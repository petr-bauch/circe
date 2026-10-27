-- Differential test for iterative DFS over a flat row-major
-- adjacency matrix with a caller-grown stack: verified Lean forward
-- (plus `evalFunc` composition) vs the native C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffVecDfsGrow.main [bin trials]`).
-- Every trial asserts Prog-world evaluation agrees with the forward
-- drain (runtime composition check — the entry threads `push_back`
-- composer calls, so plain `evalFunc` cannot link them; the proved
-- `evalProgFunc_dfsGrow` entry theorem says this Prog-world
-- evaluation equals the forward when the seed is fresh and fuel
-- covers `len + vis + 8 + n + 8 * unvisited`; the `F` below
-- dominates that bound on every fuzz input) and, when the drain is
-- `.ok`, the entry agrees with native (exact words: the driver
-- requires `argc == 6 + nm + nv + ns`, the N2d window-shift
-- lesson). Loud legs (seed miss, short matrix) assert the native
-- exit-4 path against any Lean `.error` (every miss throws
-- `std::out_of_range` natively). Mismatch = P0.
import Circe.Emit
import Circe.Emit.VecDfsGrow

namespace DiffVecDfsGrow

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 144269504896840367) % 2 ^ 64

/-- Directed graphs, caller-passed-empty stack: triangle from 0
    (count 3), seed miss, disconnected source (count 1), self-loop
    (count 1), line-3 from 0 (count 3, the slot-reuse regression:
    unconditional `push_back` returned 2 here), 0→1→2 chain (count
    3 from 0). -/
def vecDfsGrowEdges : List (List (BitVec 32) × List (BitVec 32) ×
    BitVec 64 × BitVec 64) :=
  [([0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0], 3, 0),
   ([0, 1, 1, 0], [0, 0], 2, 5),
   ([0, 0, 0, 0], [0, 0], 2, 1),
   ([1], [0], 1, 0),
   ([0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0], 3, 0),
   ([0, 1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0], 3, 0)]

def checkVecDfsGrow (bin : String) (m vis : List (BitVec 32))
    (n src : BitVec 64) : IO Nat := do
  -- Entry: Prog-world evaluation agrees with the forward drain
  -- (runtime composition check; the fuel bound dominates the entry
  -- theorem's `hPout`: `9 * vis + n + 16` covers every fuzz input
  -- with the caller-passed-empty stack).
  let F := 9 * vis.length + n.toNat + 64
  let fwd := dfsGrowFwd F m vis ⟨[], false⟩ 0 0 n src
  let ev := evalProgFunc vecGrowProg F dfsGrowFunc
    [.stdVecOwned ⟨m, false⟩ m.length m.length,
     .stdVecOwned ⟨vis, false⟩ vis.length vis.length,
     .stdVecOwned ⟨[], false⟩ 0 0, .u64 n, .u64 src]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "dfs_grow eval/fwd mismatch")
  let args := #[toString m.length]
    ++ (m.toArray.map fun x => toString x.toInt)
    ++ #[toString vis.length]
    ++ (vis.toArray.map fun x => toString x.toInt)
    ++ #["0"]
    ++ #[toString n.toNat, toString src.toNat]
  match fwd with
  | .ok (.u64 t) =>
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode != 0 then
      throw (IO.userError s!"dfs_grow native failed on hit: {out.stderr}")
    match (out.stdout.trimAscii.toString).toNat? with
    | some got =>
      if got != t.toNat then
        throw (IO.userError s!"dfs_grow mismatch: lean={t.toNat} native={got}")
      pure 1
    | none =>
      throw (IO.userError s!"dfs_grow native unparsable: {out.stdout}")
  | .ok _ =>
    throw (IO.userError "dfs_grow unexpected non-integer forward")
  | .error _ =>
    -- Loud leg: native must exit 4 (caught `out_of_range`).
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode == 4 then pure 1
    else throw (IO.userError s!"dfs_grow native exit={out.exitCode}, expected 4 on miss")

def main (args : List String) : IO Unit := do
  let asBin := args.getD 0 "/tmp/opencode/circe_vec_dfs_grow_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (m, vis, n, src) in vecDfsGrowEdges do
    let q ← checkVecDfsGrow asBin m vis n src
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Length-bounded fuzz (0..4 matrix/visited words; the stack
    -- stays caller-empty); matrix values stay 0/1 (adjacency);
    -- visited starts zeroed; `n` stays small (0..4) while `src`
    -- sometimes runs past the end (seed-miss legs exercise the
    -- native exit-4 path).
    let nm := s % 5
    let mut m : List (BitVec 32) := []
    for _ in List.range nm do
      s := lcgNext s
      m := m ++ [BitVec.ofNat 32 (s % 2)]
    s := lcgNext s
    let nv := s % 5
    let vis : List (BitVec 32) := List.replicate nv (BitVec.ofNat 32 0)
    s := lcgNext s
    let n : BitVec 64 := BitVec.ofNat 64 (s % 5)
    s := lcgNext s
    let src : BitVec 64 :=
      if s % 3 == 2 then BitVec.ofNat 64 (nv + (s % 3))
      else BitVec.ofNat 64 (s % 5)
    let q ← checkVecDfsGrow asBin m vis n src
    passed := passed + q
  IO.println s!"DIFFVECDFSGROW-OK passed={passed} (edges + {trials} random trials)"

end DiffVecDfsGrow
