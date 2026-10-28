-- Differential test for breadth-first traversal over a flat row-major
-- adjacency matrix: verified Lean forward (plus `evalFunc`
-- composition) vs the native C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffVecBfs.main [bin trials]`).
-- Every trial asserts evaluation agrees with the entry forward
-- (runtime composition check, which also validates model-fuel
-- sufficiency: under-fueled models error while native succeeds) and,
-- when the seed and drain are `.ok`, the native count AND the
-- visit-order record agree with the forward drain (the order leg is
-- what sets BFS apart from DFS: the diamond visits 0,1,2,3). The
-- driver requires `argc == 7 + nm + nv + nq + no`, prints the count
-- on line one and the order words on line two. Loud legs (seed miss,
-- short rows, short queue, short order) assert the native exit-4 path
-- against any Lean `.error` (every miss throws `std::out_of_range`
-- natively). Mismatch = P0.
import Circe.Emit
import Circe.Emit.VecBfs

namespace DiffVecBfs

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846795005 + 1442695040888963407) % 2 ^ 64

/-- Directed graphs: diamond from 0 (order 0,1,2,3, count 4), seed
    miss, empty inputs, short row (loud), short queue (loud), short
    order (loud), disconnected source (order [1], count 1), 0→1→2
    chain (order 0,1,2, count 3 from 0). -/
def vecBfsEdges : List (List (BitVec 32) × List (BitVec 32) ×
    List (BitVec 32) × List (BitVec 32) × BitVec 64 × BitVec 64) :=
  [([0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0],
     [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], 4, 0),
   ([1], [0], [0], [0], 1, 5),
   ([], [], [], [], 0, 0),
   ([1, 1], [0, 0], [0, 0], [0, 0], 2, 0),
   ([0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0],
     [0, 0, 0, 0], [0], [0, 0, 0, 0], 4, 0),
   ([0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0],
     [0, 0, 0, 0], [0, 0, 0, 0], [0], 4, 0),
   ([0, 0, 0, 0], [0, 0], [0, 0], [0, 0], 2, 1),
   ([0, 1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], 3, 0)]

def checkVecBfs (bin : String) (m vis q order : List (BitVec 32))
    (n src : BitVec 64) : IO Nat := do
  -- Entry: call-free evaluation agrees with the forward drain
  -- (runtime composition check; the fuel bound is sufficient:
  -- dequeues are bounded by the queue length and each row scan by
  -- `n`).
  let F := q.length + n.toNat + 32
  let fwd := bfsFwd F m vis q order n src
  let ev := evalFunc bfsOrderFunc
    [.stdVecVal m, .stdVecVal vis, .stdVecVal q, .stdVecVal order,
      .u64 n, .u64 src]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "bfs_order eval/fwd mismatch")
  let args := #[toString m.length]
    ++ (m.toArray.map fun x => toString x.toInt)
    ++ #[toString vis.length]
    ++ (vis.toArray.map fun x => toString x.toInt)
    ++ #[toString q.length]
    ++ (q.toArray.map fun x => toString x.toInt)
    ++ #[toString order.length]
    ++ (order.toArray.map fun x => toString x.toInt)
    ++ #[toString n.toNat, toString src.toNat]
  let runNative : IO (Nat × List Int) := do
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode != 0 then
      throw (IO.userError s!"bfs_order native failed on hit: {out.stderr}")
    let lines := (out.stdout.splitOn "\n").map (·.trimAscii.toString)
    match lines with
    | countLine :: orderLine :: _ =>
      match countLine.toNat? with
      | none =>
        throw (IO.userError s!"bfs_order native unparsable count: {out.stdout}")
      | some got =>
        let words := if orderLine == "" then [] else
          orderLine.splitOn " "
        let parsed ← words.mapM fun w =>
          match w.toInt? with
          | none => throw (IO.userError s!"bfs_order native unparsable order word: {w}")
          | some i => pure i
        pure (got, parsed)
    | _ =>
      throw (IO.userError s!"bfs_order native unparsable output: {out.stdout}")
  match bfsSeedFwd vis q src with
  | .error _ =>
    -- Loud leg: native must exit 4 (caught `std::out_of_range`).
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode == 4 then pure 1
    else throw (IO.userError s!"bfs_order native exit={out.exitCode}, expected 4 on seed miss")
  | .ok (vis1, q1) =>
    match bfsOuterFwd F m vis1 q1 order n 0 1 1 0 0 with
    | .error _ =>
      -- Loud leg: native must exit 4 (caught `std::out_of_range`).
      let out ← IO.Process.output { cmd := bin, args := args }
      if out.exitCode == 4 then pure 1
      else throw (IO.userError s!"bfs_order native exit={out.exitCode}, expected 4 on drain miss")
    | .ok (_, _, order', _, _, count', _, _) =>
      let (got, words) ← runNative
      if got != count'.toNat then
        throw (IO.userError s!"bfs_order mismatch: lean={count'.toNat} native={got}")
      if (repr fwd).pretty != (repr (.ok (.u64 count') : Result Value)).pretty then
        throw (IO.userError "bfs_order entry/drain mismatch")
      for k in List.range count'.toNat do
        match order'[k]?, words[k]? with
        | some w, some i =>
          if w.toInt != i then
            throw (IO.userError s!"bfs_order visit mismatch at {k}: lean={w.toInt} native={i}")
        | _, _ =>
          throw (IO.userError s!"bfs_order visit missing at {k}")
      pure 1

def main (args : List String) : IO Unit := do
  let asBin := args.getD 0 "/tmp/opencode/circe_vec_bfs_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (m, vis, q, order, n, src) in vecBfsEdges do
    let q ← checkVecBfs asBin m vis q order n src
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Length-bounded fuzz (0..4 per vector, driver cap 32); matrix
    -- values stay 0/1 (adjacency); visited/queue/order start zeroed;
    -- `n` stays small (0..4) while `src` sometimes runs past the end
    -- (seed-miss legs exercise the native exit-4 path).
    let nm := s % 5
    let mut m : List (BitVec 32) := []
    for _ in List.range nm do
      s := lcgNext s
      m := m ++ [BitVec.ofNat 32 (s % 2)]
    s := lcgNext s
    let nv := s % 5
    let vis : List (BitVec 32) := List.replicate nv (BitVec.ofNat 32 0)
    s := lcgNext s
    let nq := s % 5
    let q : List (BitVec 32) := List.replicate nq (BitVec.ofNat 32 0)
    s := lcgNext s
    let no := s % 5
    let order : List (BitVec 32) := List.replicate no (BitVec.ofNat 32 0)
    s := lcgNext s
    let n : BitVec 64 := BitVec.ofNat 64 (s % 5)
    s := lcgNext s
    let src : BitVec 64 :=
      if s % 3 == 2 then BitVec.ofNat 64 (nv + (s % 3))
      else BitVec.ofNat 64 (s % 5)
    let q ← checkVecBfs asBin m vis q order n src
    passed := passed + q
  IO.println s!"DIFFVECBFS-OK passed={passed} (edges + {trials} random trials)"

end DiffVecBfs
