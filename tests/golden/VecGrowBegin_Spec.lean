-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same `Base` op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZNSt6vectorIiSaIiEE5beginEv(t)` returns the first offset.
    Base body reference: the `0` offset itself (cf. emitted `_ZNSt6vectorIiSaIiEE5beginEv_fwd`,
    `stdVecBeginFwd`). -/
def _ZNSt6vectorIiSaIiEE5beginEv_spec_fwd : BitVec 64 :=
  BitVec.ofNat 64 0

/-- Edge cases: the single offset. -/
def _ZNSt6vectorIiSaIiEE5beginEv_spec_edges : List (Unit × BitVec 64) :=
  [((), BitVec.ofNat 64 0)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZNSt6vectorIiSaIiEE5beginEv_spec_check : Bool :=
  _ZNSt6vectorIiSaIiEE5beginEv_spec_edges.all fun t =>
    (repr (_ZNSt6vectorIiSaIiEE5beginEv_spec_fwd)).pretty == (repr t.2).pretty
