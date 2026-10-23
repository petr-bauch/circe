-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z13vec_quicksortRSt6vectorIiSaIiEEmm(v, lo, hi)` sorts `v[lo..hi)` in place (Lomuto, last-element pivot). Base body reference: fuel-threaded quicksort over the reified words (cf. emitted `_Z13vec_quicksortRSt6vectorIiSaIiEEmm_fwd`). -/
def _Z13vec_quicksortRSt6vectorIiSaIiEEmm_spec_fwd (l : List (BitVec 32)) : List (BitVec 32) :=
  go l (l.length * l.length + 1)
where
  go : List (BitVec 32) → Nat → List (BitVec 32)
  | _, 0 => []
  | [], _ + 1 => []
  | [x], _ + 1 => [x]
  | p :: xs, fuel + 1 =>
    go (xs.filter (fun x => x.slt p)) fuel ++ [p] ++ go (xs.filter (fun x => (x.slt p == false))) fuel

/-- Edge cases: unsorted sorts, duplicates keep multiplicity, empty/singleton are no-ops. -/
def _Z13vec_quicksortRSt6vectorIiSaIiEEmm_spec_edges : List (List (BitVec 32) × List (BitVec 32)) :=
  [([3, 1, 2], [1, 2, 3]),
   ([], []),
   ([1], [1]),
   ([5, 5, 5], [5, 5, 5]),
   ([2, 1], [1, 2])]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z13vec_quicksortRSt6vectorIiSaIiEEmm_spec_check : Bool :=
  _Z13vec_quicksortRSt6vectorIiSaIiEEmm_spec_edges.all fun t =>
    (repr (_Z13vec_quicksortRSt6vectorIiSaIiEEmm_spec_fwd t.1)).pretty == (repr t.2).pretty
