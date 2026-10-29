-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z9heap_sortRSt6vectorIiSaIiEEm(v, n)` sorts `v[0..n)` in place (iterative heapsort: down-counting heapify + extract-max). Base body reference: insertion-sort mirror over the reified words (cf. emitted `_Z9heap_sortRSt6vectorIiSaIiEEm_fwd`). -/
def _Z9heap_sortRSt6vectorIiSaIiEEm_spec_fwd (l : List (BitVec 32)) : List (BitVec 32) :=
  l.foldl ins []
where
  ins : List (BitVec 32) → BitVec 32 → List (BitVec 32)
    | [], x => [x]
    | y :: ys, x => if x.slt y then x :: y :: ys else y :: ins ys x

/-- Edge cases: unsorted sorts, duplicates keep multiplicity, empty/singleton are no-ops. -/
def _Z9heap_sortRSt6vectorIiSaIiEEm_spec_edges : List (List (BitVec 32) × List (BitVec 32)) :=
  [([3, 1, 2], [1, 2, 3]),
   ([], []),
   ([1], [1]),
   ([5, 5, 5], [5, 5, 5]),
   ([2, 1], [1, 2])]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z9heap_sortRSt6vectorIiSaIiEEm_spec_check : Bool :=
  _Z9heap_sortRSt6vectorIiSaIiEEm_spec_edges.all fun t =>
    (repr (_Z9heap_sortRSt6vectorIiSaIiEEm_spec_fwd t.1)).pretty == (repr t.2).pretty
