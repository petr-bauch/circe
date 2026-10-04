-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same `Base` op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZNSt12_Vector_baseIiSaIiEE19_M_get_Tp_allocatorEv(t)` projects the allocator.
    Base body reference: the erased allocator `i32 0` (cf. emitted `_ZNSt12_Vector_baseIiSaIiEE19_M_get_Tp_allocatorEv_fwd`,
    `stdVecGetTpFwd`). -/
def _ZNSt12_Vector_baseIiSaIiEE19_M_get_Tp_allocatorEv_spec_fwd : BitVec 32 :=
  BitVec.ofNat 32 0

/-- Edge cases: the single erased allocator. -/
def _ZNSt12_Vector_baseIiSaIiEE19_M_get_Tp_allocatorEv_spec_edges : List (Unit × BitVec 32) :=
  [((), BitVec.ofNat 32 0)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZNSt12_Vector_baseIiSaIiEE19_M_get_Tp_allocatorEv_spec_check : Bool :=
  _ZNSt12_Vector_baseIiSaIiEE19_M_get_Tp_allocatorEv_spec_edges.all fun t =>
    (repr (_ZNSt12_Vector_baseIiSaIiEE19_M_get_Tp_allocatorEv_spec_fwd)).pretty == (repr t.2).pretty
