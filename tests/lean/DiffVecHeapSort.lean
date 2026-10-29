-- Differential test for iterative in-place heapsort over
-- `std::vector<int>`: verified Lean forward (plus `evalProgFunc`
-- composition) vs the native C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffVecHeapSort.main [bin trials]`).
-- Every trial asserts evaluation agrees with the forward model
-- (runtime composition check, which also validates model-fuel
-- sufficiency: under-fueled models error while native succeeds) and
-- the native binary prints the sorted words exactly (total kernel:
-- every access is guard-justified, so there are no miss legs).
-- Mismatch = P0.
import Circe.Emit
import Circe.Emit.VecHeapSort

namespace DiffVecHeapSort

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442690950888963407) % 2 ^ 64

/-- Directed cases: empty, singleton, sorted, reversed, duplicates,
    mixed signs, all-equal. -/
def heapSortEdges : List (List (BitVec 32)) :=
  [[],
   [1],
   [1, 2, 3, 4],
   [5, 4, 3, 2, 1],
   [2, 1, 2, 1],
   [-3, 1, -2, 0],
   [5, 5, 5],
   [3, 1, 2]]

def checkHeapSort (bin : String) (l : List (BitVec 32)) : IO Nat := do
  -- Entry: program evaluation agrees with the forward model
  -- (runtime composition check; the fuel bound is sufficient:
  -- heapify + extract scans are bounded by the length).
  let n := l.length
  let F := 8 * (n + 1) + 16
  let fwd := heapSortFwd F l (BitVec.ofNat 64 n)
  let ev := evalProgFunc heapSortProg F
    heapSortFunc
    [.stdVecVal l, .u64 (BitVec.ofNat 64 n)]
  match fwd, ev with
  | .ok (.stdVecVal l'), .ok (.stdVecVal l'') =>
    if l' != l'' then
      throw (IO.userError s!"heap_sort eval/fwd mismatch: fwd={l'.map (·.toInt)} ev={l''.map (·.toInt)}")
    let args := #[toString n]
      ++ (l.toArray.map fun w => toString w.toInt)
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode != 0 then
      throw (IO.userError s!"heap_sort native failed: {out.stderr}")
    match out.stdout.trimAscii.toString.splitOn " " with
    | m :: ws =>
      match m.toNat? with
      | some k =>
        let got := ws.filterMap (·.toInt?)
        if k != l'.length || got.length != l'.length ||
            got != l'.map (·.toInt) then
          throw (IO.userError s!"heap_sort mismatch: lean={l'.map (·.toInt)} native={got}")
        pure 1
      | none =>
        throw (IO.userError s!"heap_sort native unparsable: {out.stdout}")
    | [] =>
      throw (IO.userError s!"heap_sort native unparsable: {out.stdout}")
  | _, _ =>
    throw (IO.userError "heap_sort unexpected shape (total kernel)")

def main (args : List String) : IO Unit := do
  let asBin := args.getD 0 "/tmp/opencode/circe_vec_heap_sort_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for l in heapSortEdges do
    let q ← checkHeapSort asBin l
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
    let q ← checkHeapSort asBin l
    passed := passed + q
  IO.println s!"DIFFVECHEAPSORT-OK passed={passed} (edges + {trials} random trials)"

end DiffVecHeapSort
