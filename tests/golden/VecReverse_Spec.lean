-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z11vec_reverseRSt6vectorIiSaIiEE(v)` reverses `v` in place. Base body reference: list reversal on the reified words (cf. emitted `_Z11vec_reverseRSt6vectorIiSaIiEE_fwd`, `vecReverseFwd`). -/
def _Z11vec_reverseRSt6vectorIiSaIiEE_spec_fwd (l : List (BitVec 32)) : Result (List (BitVec 32)) :=
  .ok l.reverse

/-- Edge cases: empty, singleton, even and odd lengths. -/
def _Z11vec_reverseRSt6vectorIiSaIiEE_spec_edges : List (List (BitVec 32) × Result (List (BitVec 32))) :=
  [([], .ok []), ([7], .ok [7]), ([1, 2], .ok [2, 1]),
   ([1, 2, 3], .ok [3, 2, 1]), ([1, 2, 3, 4], .ok [4, 3, 2, 1])]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z11vec_reverseRSt6vectorIiSaIiEE_spec_check : Bool :=
  _Z11vec_reverseRSt6vectorIiSaIiEE_spec_edges.all fun t =>
    (repr (_Z11vec_reverseRSt6vectorIiSaIiEE_spec_fwd t.1)).pretty == (repr t.2).pretty
