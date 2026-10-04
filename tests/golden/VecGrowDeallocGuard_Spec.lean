-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same `Base` op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZNSt12_Vector_baseIiSaIiEE13_M_deallocateEPim(t, n)` consumes the triple unless `n == 0`.
    Base body reference: the `n == 0` test around the consume itself (cf. emitted `_ZNSt12_Vector_baseIiSaIiEE13_M_deallocateEPim_fwd`,
    `stdVecDeallocGuardFwd`). -/
def _ZNSt12_Vector_baseIiSaIiEE13_M_deallocateEPim_spec_fwd (b : Vec32) (len cap : Nat) (n : BitVec 64) : Result (Vec32 × Nat × Nat) :=
  if (BitVec.ofNat 64 0).ult n then
    match vecFree b with
    | .error e => .error e
    | .ok b' => .ok (b', len, cap)
  else .ok (b, len, cap)

/-- Edge cases: null kept, live consume. -/
def _ZNSt12_Vector_baseIiSaIiEE13_M_deallocateEPim_spec_edges : List (((Vec32 × Nat × Nat) × BitVec 64) × Result (Vec32 × Nat × Nat)) :=
  [((((⟨[1], false⟩, 1, 1), 0)), .ok (⟨[1], false⟩, 1, 1)),
   ((((⟨[1], false⟩, 1, 1), 5)), .ok (⟨[1], true⟩, 1, 1))]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZNSt12_Vector_baseIiSaIiEE13_M_deallocateEPim_spec_check : Bool :=
  _ZNSt12_Vector_baseIiSaIiEE13_M_deallocateEPim_spec_edges.all fun t =>
    (repr (_ZNSt12_Vector_baseIiSaIiEE13_M_deallocateEPim_spec_fwd t.1.1.1 t.1.1.2.1 t.1.1.2.2 t.1.2)).pretty == (repr t.2).pretty
