-- Differential test for iterative DFS over a flat row-major
-- adjacency matrix: verified Lean forward (plus `evalFunc`
-- composition) vs the native C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffVecDfs.main [bin trials]`).
-- Every trial asserts evaluation agrees with the forward drain
-- (runtime composition check, which also validates model-fuel
-- sufficiency: under-fueled models error while native succeeds) and,
-- when the drain is `.ok`, the entry agrees with native (exact
-- words: the driver requires `argc == 6 + nm + nv + ns`, the N2d
-- window-shift lesson). Loud legs (seed miss, short rows, short
-- stack) assert the native exit-4 path against any Lean `.error`
-- (every miss throws `std::out_of_range` natively). Mismatch = P0.
import Circe.Emit
import Circe.Emit.VecDfs

namespace DiffVecDfs

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Directed graphs: triangle from 0 (count 3), seed miss, empty
    inputs, short row (loud), short stack (loud), disconnected
    source (count 1), 0→1→2 chain (count 3 from 0). -/
def vecDfsEdges : List (List (BitVec 32) × List (BitVec 32) ×
    List (BitVec 32) × BitVec 64 × BitVec 64) :=
  [([0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0], [0, 0, 0], 3, 0),
   ([1], [0], [0], 1, 5),
   ([], [], [], 0, 0),
   ([1, 1], [0, 0], [0, 0], 2, 0),
   ([0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0], [0], 3, 0),
   ([0, 0, 0, 0], [0, 0], [0, 0], 2, 1),
   ([0, 1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0], [0, 0, 0], 3, 0)]

def checkVecDfs (bin : String) (m vis st : List (BitVec 32))
    (n src : BitVec 64) : IO Nat := do
  -- Entry: call-free evaluation agrees with the forward drain
  -- (runtime composition check; the fuel bound is sufficient: pops
  -- are bounded by the stack length and each row scan by `n`).
  let F := st.length + n.toNat + 32
  let fwd := dfsFwd F m vis st n src
  let ev := evalFunc dfsFunc
    [.stdVecVal m, .stdVecVal vis, .stdVecVal st, .u64 n, .u64 src]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "dfs_reachable eval/fwd mismatch")
  let args := #[toString m.length]
    ++ (m.toArray.map fun x => toString x.toInt)
    ++ #[toString vis.length]
    ++ (vis.toArray.map fun x => toString x.toInt)
    ++ #[toString st.length]
    ++ (st.toArray.map fun x => toString x.toInt)
    ++ #[toString n.toNat, toString src.toNat]
  match fwd with
  | .ok (.u64 t) =>
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode != 0 then
      throw (IO.userError s!"dfs_reachable native failed on hit: {out.stderr}")
    match (out.stdout.trimAscii.toString).toNat? with
    | some got =>
      if got != t.toNat then
        throw (IO.userError s!"dfs_reachable mismatch: lean={t.toNat} native={got}")
      pure 1
    | none =>
      throw (IO.userError s!"dfs_reachable native unparsable: {out.stdout}")
  | .ok _ =>
    throw (IO.userError "dfs_reachable unexpected non-integer forward")
  | .error _ =>
    -- Loud leg: native must exit 4 (caught `out_of_range`).
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode == 4 then pure 1
    else throw (IO.userError s!"dfs_reachable native exit={out.exitCode}, expected 4 on miss")

def main (args : List String) : IO Unit := do
  let asBin := args.getD 0 "/tmp/opencode/circe_vec_dfs_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (m, vis, st, n, src) in vecDfsEdges do
    let q ← checkVecDfs asBin m vis st n src
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Length-bounded fuzz (0..4 per vector, driver cap 32); matrix
    -- values stay 0/1 (adjacency); visited/stack start zeroed; `n`
    -- stays small (0..4) while `src` sometimes runs past the end
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
    let ns := s % 5
    let st : List (BitVec 32) := List.replicate ns (BitVec.ofNat 32 0)
    s := lcgNext s
    let n : BitVec 64 := BitVec.ofNat 64 (s % 5)
    s := lcgNext s
    let src : BitVec 64 :=
      if s % 3 == 2 then BitVec.ofNat 64 (nv + (s % 3))
      else BitVec.ofNat 64 (s % 5)
    let q ← checkVecDfs asBin m vis st n src
    passed := passed + q
  IO.println s!"DIFFVECDFS-OK passed={passed} (edges + {trials} random trials)"

end DiffVecDfs
