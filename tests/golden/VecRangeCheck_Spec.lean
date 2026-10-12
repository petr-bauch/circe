-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZNKSt6vectorIiSaIiEE14_M_range_checkEm(s, n)` checks `n < size(s)`.
    Base body reference: the fused guard itself (cf. emitted `_ZNKSt6vectorIiSaIiEE14_M_range_checkEm_fwd`,
    `stdVecRangeCheckFwd`). -/
def _ZNKSt6vectorIiSaIiEE14_M_range_checkEm_spec_fwd (l : List (BitVec 32)) (n : BitVec 64) : Result Unit :=
  if n.toNat < l.length then .ok () else .error .AssertFail

/-- Edge cases: hit, miss, empty. -/
def _ZNKSt6vectorIiSaIiEE14_M_range_checkEm_spec_edges : List ((List (BitVec 32) × BitVec 64) × Result Unit) :=
  [(([1], 0), .ok ()), (([1], 1), .error .AssertFail), (([], 0), .error .AssertFail)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZNKSt6vectorIiSaIiEE14_M_range_checkEm_spec_check : Bool :=
  _ZNKSt6vectorIiSaIiEE14_M_range_checkEm_spec_edges.all fun t =>
    (repr (_ZNKSt6vectorIiSaIiEE14_M_range_checkEm_spec_fwd t.1.1 t.1.2)).pretty == (repr t.2).pretty
