-- Differential test for bottom-up merge sort over `std::vector<int>`:
-- the verified Lean forwards (plus `evalProgFunc` composition) vs
-- the native C++ binary, covering both the ranged `merge_runs`
-- callee and the `vec_merge_sort` entry (first calls-in-loops
-- customer: loop bodies contain `callProg` steps).
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffVecMergeSort.main [bin trials]`).
-- Every trial asserts evaluation agrees with the forward model
-- (runtime composition check, which also validates model-fuel
-- sufficiency: under-fueled models error while native succeeds, a
-- loud mismatch). On hit the native binary must print the words
-- exactly; on short-`tmp` miss (or overrun range) the native must
-- exit 4 (caught `std::out_of_range`) while Lean reports `.error`.
-- Sortedness is caller debt: agreement holds on unsorted runs too
-- (edges cover it — the V1 precedent). Mismatch = P0.
import Circe.Emit
import Circe.Emit.VecMergeRuns
import Circe.Emit.VecMergeSort

namespace DiffVecMergeSort

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

def bv (x : Int) : BitVec 32 := BitVec.ofInt 32 x

/-- Directed `merge_runs` cases: (a, tmp, lo, mid, hi). -/
def mergeRunsEdges : List (List (BitVec 32) × List (BitVec 32) × Nat × Nat × Nat) :=
  [([1, 3, 5, 2, 4, 6], [0, 0, 0, 0, 0, 0], 0, 3, 6),
   ([], [], 0, 0, 0),
   ([9, 7, 1, 3, 5, 2, 4, 6, 8, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 2, 5, 8),
   ([9, 2, 4, 6], [0, 0, 0, 0], 1, 1, 4),
   ([9, 1, 3, 5], [0, 0, 0, 0], 1, 4, 4),
   ([7, 5], [0, 0], 0, 1, 2),
   ([1], [], 0, 0, 1),
   ([3, -1, 2, -5], [0, 0, 0, 0], 0, 2, 4),
   ([1, 2], [0, 0], 0, 1, 5)]

def checkMergeRuns (bin : String) (la lt : List (BitVec 32))
    (lo mid hi : Nat) : IO Nat := do
  -- Entry: program evaluation agrees with the forward model
  -- (runtime composition check; the model fuel is exact).
  let F := ((mid - lo) + (hi - lo)) + 1
  let fwd := VecMergeRuns.mergeRunsFwd la lt lo mid hi
  let ev := evalProgFunc VecMergeSort.vecMergeSortProg F
    VecMergeRuns.mergeRunsFunc
    [.stdVecVal la, .stdVecVal lt, .u64 (BitVec.ofNat 64 lo),
      .u64 (BitVec.ofNat 64 mid), .u64 (BitVec.ofNat 64 hi)]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "merge_runs eval/fwd mismatch")
  let args := #["0", toString la.length]
    ++ (la.toArray.map fun w => toString w.toInt)
    ++ #[toString lt.length]
    ++ (lt.toArray.map fun w => toString w.toInt)
    ++ #[toString lo, toString mid, toString hi]
  match fwd with
  | .ok (.stdVecVal lt') =>
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode != 0 then
      throw (IO.userError s!"merge_runs native failed on hit: {out.stderr}")
    match out.stdout.trimAscii.toString.splitOn " " with
    | m :: ws =>
      match m.toNat? with
      | some k =>
        let got := ws.filterMap (·.toInt?)
        if k != lt'.length || got.length != lt'.length ||
            got != lt'.map (·.toInt) then
          throw (IO.userError s!"merge_runs mismatch: lean={lt'.map (·.toInt)} native={got}")
        pure 1
      | none =>
        throw (IO.userError s!"merge_runs native unparsable: {out.stdout}")
    | [] =>
      throw (IO.userError s!"merge_runs native unparsable: {out.stdout}")
  | .ok _ =>
    throw (IO.userError "merge_runs unexpected non-vector forward")
  | .error _ =>
    -- Miss leg: native must exit 4 (caught `out_of_range`).
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode == 4 then pure 1
    else throw (IO.userError s!"merge_runs native exit={out.exitCode}, expected 4 on miss")

/-- Directed `vec_merge_sort` cases: (a, tmp). -/
def mergeSortEdges : List (List (BitVec 32) × List (BitVec 32)) :=
  [([], []),
   ([1], [0]),
   ([3, 1, 2], [0, 0, 0]),
   ([1, 2, 3, 4], [0, 0, 0, 0]),
   ([5, 4, 3, 2, 1], [0, 0, 0, 0, 0]),
   ([2, 1, 2, 1], [0, 0, 0, 0]),
   ([-3, 1, -2, 0], [0, 0, 0, 0]),
   ([3, 1, 2], [0, 0, 0, 0, 0]),
   ([3, 1, 2], [0, 0])]

def checkMergeSort (bin : String) (la lt : List (BitVec 32)) : IO Nat := do
  -- Entry: program evaluation agrees with the forward model
  -- (runtime composition check; the fuel bound is sufficient).
  let n := la.length
  let F := 2 * (n - 1) + 2 * n + 10
  let fwd := VecMergeSort.vecMergeSortFwd la lt F
  let ev := evalProgFunc VecMergeSort.vecMergeSortProg F
    VecMergeSort.vecMergeSortFunc
    [.stdVecVal la, .stdVecVal lt]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "vec_merge_sort eval/fwd mismatch")
  let args := #["1", toString la.length]
    ++ (la.toArray.map fun w => toString w.toInt)
    ++ #[toString lt.length]
    ++ (lt.toArray.map fun w => toString w.toInt)
  match fwd with
  | .ok (.stdVecVal la') =>
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode != 0 then
      throw (IO.userError s!"vec_merge_sort native failed on hit: {out.stderr}")
    match out.stdout.trimAscii.toString.splitOn " " with
    | m :: ws =>
      match m.toNat? with
      | some k =>
        let got := ws.filterMap (·.toInt?)
        if k != la'.length || got.length != la'.length ||
            got != la'.map (·.toInt) then
          throw (IO.userError s!"vec_merge_sort mismatch: lean={la'.map (·.toInt)} native={got}")
        pure 1
      | none =>
        throw (IO.userError s!"vec_merge_sort native unparsable: {out.stdout}")
    | [] =>
      throw (IO.userError s!"vec_merge_sort native unparsable: {out.stdout}")
  | .ok _ =>
    throw (IO.userError "vec_merge_sort unexpected non-vector forward")
  | .error _ =>
    -- Miss leg: native must exit 4 (caught `out_of_range`).
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode == 4 then pure 1
    else throw (IO.userError s!"vec_merge_sort native exit={out.exitCode}, expected 4 on miss")

def main (args : List String) : IO Unit := do
  let asBin := args.getD 0 "/tmp/opencode/circe_vec_merge_sort_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (la, lt, lo, mid, hi) in mergeRunsEdges do
    let q ← checkMergeRuns asBin la lt lo mid hi
    passed := passed + q
  for (la, lt) in mergeSortEdges do
    let q ← checkMergeSort asBin la lt
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for t in List.range trials do
    s := lcgNext s
    if t % 2 == 0 then
      -- Ranged-callee fuzz: length 0..6, words in -30..30, sorted
      -- runs three trials in four (one in four stays unsorted,
      -- exercising caller-debt agreement); `tmp` covers `[lo,hi)`
      -- exactly three trials in four, short otherwise.
      let lena := s % 7
      let mut la : List (BitVec 32) := []
      for _ in List.range lena do
        s := lcgNext s
        let xi : Int := ((s % 61 : Nat) : Int) - 30
        la := la ++ [bv xi]
      s := lcgNext s
      let sortSigned (l : List (BitVec 32)) : List (BitVec 32) :=
        l.toArray.qsort (fun x y => decide (x.toInt < y.toInt)) |>.toList
      if s % 4 != 3 then
        la := sortSigned la
      s := lcgNext s
      let lo := s % (lena + 1)
      s := lcgNext s
      let mid := lo + s % (lena + 1 - lo)
      s := lcgNext s
      let hi := mid + s % (lena + 1 - mid)
      s := lcgNext s
      let nt := if s % 4 == 3 then hi - (s % 2) - 1 else hi
      let lt : List (BitVec 32) := List.replicate nt (BitVec.ofNat 32 0)
      let q ← checkMergeRuns asBin la lt lo mid hi
      passed := passed + q
    else
      -- Entry fuzz: length 0..6, words in -30..30 unsorted (the
      -- entry sorts everything); `tmp` is exact-size three trials
      -- in four, short otherwise (miss leg).
      let lena := s % 7
      let mut la : List (BitVec 32) := []
      for _ in List.range lena do
        s := lcgNext s
        let xi : Int := ((s % 61 : Nat) : Int) - 30
        la := la ++ [bv xi]
      s := lcgNext s
      let nt := if s % 4 == 3 then (lena - s % 2) - 1 else lena
      let lt : List (BitVec 32) := List.replicate nt (BitVec.ofNat 32 0)
      let q ← checkMergeSort asBin la lt
      passed := passed + q
  IO.println s!"DIFFVECMERGESORT-OK passed={passed} (edges + {trials} random trials)"

end DiffVecMergeSort
