-- Differential test for iterative selection sort over
-- `std::vector<int>`: verified Lean forwards (plus `evalProgFunc`
-- composition) vs the native C++ binary, covering both the
-- `min_index` leaf and the `vec_selection_sort` entry (second
-- calls-in-loops customer: the outer body contains a `callRet`
-- step).
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffVecSelectionSort.main [bin trials]`).
-- Every trial asserts evaluation agrees with the forward model
-- (runtime composition check); on hit the native binary must print
-- the minimum index (mode 0) or the sorted words (mode 1). Total
-- kernel: every access is guard-justified, so there are no miss
-- legs. Mismatch = P0.
import Circe.Emit
import Circe.Emit.VecSelectionSort

namespace DiffVecSelectionSort

open VecSelectionSort

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Directed `min_index` cases: (words, lo). -/
def minIndexEdges : List (List (BitVec 32) × Nat) :=
  [([5], 0),
   ([3, 1, 2], 0),
   ([7, 8], 1),
   ([3, 7, 1, 8, 2], 2)]

/-- Directed `vec_selection_sort` cases. -/
def selectionSortEdges : List (List (BitVec 32)) :=
  [[], [1], [2, 1], [1, 2, 3], [3, 1, 2], [5, 1],
   [3, 7, 1, 8, 2], [5, 5, 5], [4, 3, 2, 1]]

def checkMinIndex (bin : String) (l : List (BitVec 32))
    (lo : Nat) : IO Nat := do
  -- Entry: program evaluation agrees with the forward model
  -- (runtime composition check).
  let F := (l.length - lo) + 1
  let fwd := vecMinIndexFwd l lo
  let ev := evalProgFunc vecSelectionSortProg F minIndexFunc
    [.stdVecVal l, .u64 (BitVec.ofNat 64 lo)]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "min_index eval/fwd mismatch")
  let args := #["0", toString l.length]
    ++ (l.toArray.map fun w => toString w.toInt)
    ++ #[toString lo]
  match fwd with
  | .ok (.u64 mv) =>
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode != 0 then
      throw (IO.userError s!"min_index native failed: {out.stderr}")
    match out.stdout.trimAscii.toString.toNat? with
    | some k =>
      if k != mv.toNat then
        throw (IO.userError s!"min_index mismatch: lean={mv.toNat} native={k}")
      pure 1
    | none =>
      throw (IO.userError s!"min_index native unparsable: {out.stdout}")
  | .ok _ =>
    throw (IO.userError "min_index unexpected non-u64 forward")
  | .error _ =>
    throw (IO.userError "min_index unexpected forward error (total kernel)")

def checkSelectionSort (bin : String) (l : List (BitVec 32)) : IO Nat := do
  -- Entry: program evaluation agrees with the forward model
  -- (runtime composition check, which also validates model-fuel
  -- sufficiency: under-fueled models error while native succeeds,
  -- a loud mismatch).
  -- `callRet` re-spends the same fuel in the callee, so evaluation
  -- needs the outer iterations plus every inner scan.
  let FE := 2 * l.length + 2
  let fwd := vecSelectionSortFwd l
  let ev := evalProgFunc vecSelectionSortProg FE vecSelectionSortFunc
    [.stdVecVal l]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "vec_selection_sort eval/fwd mismatch")
  let args := #["1", toString l.length]
    ++ (l.toArray.map fun w => toString w.toInt)
  match fwd with
  | .ok (.stdVecVal l') =>
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode != 0 then
      throw (IO.userError s!"vec_selection_sort native failed: {out.stderr}")
    match out.stdout.trimAscii.toString.splitOn " " with
    | m :: ws =>
      match m.toNat? with
      | some k =>
        let got := ws.filterMap (·.toInt?)
        if k != l'.length || got.length != l'.length ||
            got != l'.map (·.toInt) then
          throw (IO.userError s!"vec_selection_sort mismatch: lean={l'.map (·.toInt)} native={got}")
        pure 1
      | none =>
        throw (IO.userError s!"vec_selection_sort native unparsable: {out.stdout}")
    | [] =>
      throw (IO.userError s!"vec_selection_sort native unparsable: {out.stdout}")
  | .ok _ =>
    throw (IO.userError "vec_selection_sort unexpected non-vector forward")
  | .error _ =>
    throw (IO.userError "vec_selection_sort unexpected forward error (total kernel)")

def main (args : List String) : IO Unit := do
  let asBin := args.getD 0 "/tmp/opencode/circe_vec_selection_sort_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (l, lo) in minIndexEdges do
    let q ← checkMinIndex asBin l lo
    passed := passed + q
  for l in selectionSortEdges do
    let q ← checkSelectionSort asBin l
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Length-bounded fuzz (0..8); words in -20..20.
    let len := s % 9
    let mut l : List (BitVec 32) := []
    for _ in List.range len do
      s := lcgNext s
      let xi : Int := ((s % 41 : Nat) : Int) - 20
      l := l ++ [BitVec.ofInt 32 xi]
    s := lcgNext s
    if len == 0 then
      let q ← checkSelectionSort asBin l
      passed := passed + q
    else if s % 2 == 0 then
      let lo := s % len
      let q ← checkMinIndex asBin l lo
      passed := passed + q
    else
      let q ← checkSelectionSort asBin l
      passed := passed + q
  IO.println s!"DIFFVECSELECTIONSORT-OK passed={passed} (edges + {trials} random trials)"

end DiffVecSelectionSort
