-- Differential test for the out-of-place two-pointer merge over
-- `std::vector<int>`: verified Lean forward (plus `evalFunc`
-- composition) vs the native C++ binary.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffVecMergeInto.main [bin trials]`).
-- Every trial asserts evaluation agrees with the forward model
-- (runtime composition check). On hit the native binary must print
-- the merged `out` words exactly; on short-`out` miss the native
-- must exit 4 (caught `std::out_of_range`) while Lean reports
-- `.error .AssertFail` (the `vec_at_set` miss precedent). Sortedness
-- is caller debt: agreement holds on unsorted inputs too (one edge
-- covers it — the V1 precedent). Mismatch = P0.
import Circe.Emit
import Circe.Emit.VecMergeInto

namespace DiffVecMergeInto

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Directed cases: both-empty hit, interleave hit, drain-`a` hit,
    short-`out` miss, negatives hit, unsorted-input agreement. -/
def vecMergeIntoEdges : List (List (BitVec 32) × List (BitVec 32) × List (BitVec 32)) :=
  [([], [], [0, 0]),
   ([1, 3, 5], [2, 4, 6], [0, 0, 0, 0, 0, 0]),
   ([5], [1, 2], [0, 0, 0]),
   ([1], [2], [0]),
   ([-3, 1], [-7, 2], [0, 0, 0, 0]),
   ([2, 1], [0], [0, 0, 0])]

def checkVecMergeInto (bin : String) (la lb lo : List (BitVec 32)) : IO Nat := do
  -- Entry: call-free evaluation agrees with the forward model
  -- (runtime composition check).
  let fwd := vecMergeIntoFwd la lb lo
  let ev := evalFunc vecMergeIntoFunc
    [.stdVecVal la, .stdVecVal lb, .stdVecVal lo]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError "vec_merge_into eval/fwd mismatch")
  let args := #[toString la.length]
    ++ (la.toArray.map fun w => toString w.toInt)
    ++ #[toString lb.length]
    ++ (lb.toArray.map fun w => toString w.toInt)
    ++ #[toString lo.length]
  match fwd with
  | .ok (.stdVecVal lo') =>
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode != 0 then
      throw (IO.userError s!"vec_merge_into native failed on hit: {out.stderr}")
    match out.stdout.trimAscii.toString.splitOn " " with
    | m :: ws =>
      match m.toNat? with
      | some k =>
        let got := ws.filterMap (·.toInt?)
        if k != lo'.length || got.length != lo'.length ||
            got != lo'.map (·.toInt) then
          throw (IO.userError s!"vec_merge_into mismatch: lean={lo'.map (·.toInt)} native={got}")
        pure 1
      | none =>
        throw (IO.userError s!"vec_merge_into native unparsable: {out.stdout}")
    | [] =>
      throw (IO.userError s!"vec_merge_into native unparsable: {out.stdout}")
  | .ok _ =>
    throw (IO.userError "vec_merge_into unexpected non-vector forward")
  | .error _ =>
    -- Miss leg: native must exit 4 (caught `out_of_range`).
    let out ← IO.Process.output { cmd := bin, args := args }
    if out.exitCode == 4 then pure 1
    else throw (IO.userError s!"vec_merge_into native exit={out.exitCode}, expected 4 on miss")

def main (args : List String) : IO Unit := do
  let asBin := args.getD 0 "/tmp/opencode/circe_vec_merge_into_native"
  let trials := (args.getD 1 "1000").toNat?.getD 1000
  let mut passed := 0
  for (la, lb, lo) in vecMergeIntoEdges do
    let q ← checkVecMergeInto asBin la lb lo
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    -- Length-bounded fuzz (0..6 per side); words in -30..30, sorted
    -- three trials in four (one in four stays unsorted, exercising
    -- caller-debt agreement); `out` is exact-size three trials in
    -- four, short otherwise (miss leg exercises native exit-4).
    let lena := s % 7
    let mut la : List (BitVec 32) := []
    for _ in List.range lena do
      s := lcgNext s
      let xi : Int := ((s % 61 : Nat) : Int) - 30
      la := la ++ [BitVec.ofInt 32 xi]
    s := lcgNext s
    let lenb := s % 7
    let mut lb : List (BitVec 32) := []
    for _ in List.range lenb do
      s := lcgNext s
      let xi : Int := ((s % 61 : Nat) : Int) - 30
      lb := lb ++ [BitVec.ofInt 32 xi]
    s := lcgNext s
    -- Insertion sort by signed value (tiny lists; keeps the
    -- sorted-majority leg honest without importing a sorter).
    let sortSigned (l : List (BitVec 32)) : List (BitVec 32) :=
      l.toArray.qsort (fun x y => decide (x.toInt < y.toInt)) |>.toList
    if s % 4 != 3 then
      la := sortSigned la
      lb := sortSigned lb
    s := lcgNext s
    let nout := if s % 4 == 3 then (lena + lenb) - (s % 3) - 1
      else lena + lenb
    let lo : List (BitVec 32) := List.replicate nout (BitVec.ofNat 32 0)
    let q ← checkVecMergeInto asBin la lb lo
    passed := passed + q
  IO.println s!"DIFFVECMERGEINTO-OK passed={passed} (edges + {trials} random trials)"

end DiffVecMergeInto
