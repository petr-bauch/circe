-- Differential test for the N9 insertion sort over
-- `std::array<uint32_t, 4>`: evaluated forms (interpreter) vs the
-- verified forwards, plus an executable check of the N9-iv contract
-- (sorted + permutation) on every trial.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `DiffSort.main [trials]`). No native binary: the C++ entry prints
-- only the sum (permutation-invariant), so sortedness is pinned by
-- the spec oracle here (see `tests/cpp/array_sort_sum.cpp`).
-- Mismatch = P0.
import Circe.Emit
import Circe.Emit.ArraySort

namespace DiffSort

/-- 64-bit LCG step. -/
def lcgNext (s : Nat) : Nat :=
  (s * 6364136223846793005 + 1442695040888963407) % 2 ^ 64

/-- Executable ascending-sortedness (mirrors the `Pairwise` spec:
    no later word is strictly below its predecessor). -/
def sortedU32 : List (BitVec 32) → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (!b.ult a) && sortedU32 (b :: rest)

/-- Executable multiset equality (mirrors `List.Perm`: same length,
    same per-word counts). -/
def sameMultiset (l s : List (BitVec 32)) : Bool :=
  decide (s.length = l.length) &&
    l.all (fun x => decide (l.count x = s.count x))

/-- Directed quads: sorted, reversed, duplicates, boundaries, the
    corpus entry quad. -/
def sortEdges : List (BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32) :=
  [(0, 0, 0, 0), (1, 2, 3, 4), (4, 3, 2, 1), (2, 1, 2, 1),
   (3, 1, 2, 0), (1, 2, 4, 3),
   (0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF, 0xFFFFFFFF),
   (0, 0xFFFFFFFF, 0, 0xFFFFFFFF)]

def checkSort (a b c d : BitVec 32) : IO Nat := do
  let l : List (BitVec 32) := [a, b, c, d]
  -- Runtime composition: the interpreter agrees with the verified
  -- forward (the proof is `evalFuncFuel_insertionSort`; this checks
  -- the executable closes the same way on each input).
  let fwd := insertionSortFwd l
  let ev := evalFunc insertionSortFunc [.arr32 l]
  if (repr fwd).pretty != (repr ev).pretty then
    throw (IO.userError s!"sort eval/fwd mismatch at {[a, b, c, d]}")
  -- Executable N9-iv contract on the evaluated output.
  match ev with
  | .ok (.arr32 s) =>
    if !sortedU32 s then
      throw (IO.userError s!"sort output not sorted at {[a, b, c, d]}")
    if !sameMultiset l s then
      throw (IO.userError s!"sort output not a permutation at {[a, b, c, d]}")
    pure 1
  | _ => throw (IO.userError s!"sort eval failed at {[a, b, c, d]}")

def main (args : List String) : IO Unit := do
  let trials := (args.getD 0 "1000").toNat?.getD 1000
  -- Entry composition, once: program evaluation over the sort program
  -- agrees with the compute-to-`6` forward.
  let fwdE := arraySortSumEntryFwd
  let evE := evalProgFunc arraySortProg 7 arraySortSumEntryFunc []
  if (repr fwdE).pretty != (repr evE).pretty then
    throw (IO.userError "array_sort_sum entry eval/fwd mismatch")
  let mut passed := 0
  for (a, b, c, d) in sortEdges do
    let q ← checkSort a b c d
    passed := passed + q
  let mut s := 0x9E3779B97F4A7C15
  for _ in List.range trials do
    s := lcgNext s
    let a : BitVec 32 := BitVec.ofNat 32 (s % 2 ^ 32)
    s := lcgNext s
    let b : BitVec 32 := BitVec.ofNat 32 (s % 2 ^ 32)
    s := lcgNext s
    let c : BitVec 32 := BitVec.ofNat 32 (s % 2 ^ 32)
    s := lcgNext s
    let d : BitVec 32 := BitVec.ofNat 32 (s % 2 ^ 32)
    let q ← checkSort a b c d
    passed := passed + q
  IO.println s!"DIFFSORT-OK passed={passed} (edges + {trials} random trials)"

end DiffSort
