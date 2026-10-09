-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZNSt16allocator_traitsISaIiEE10deallocateERS0_Pim(t)` consumes the triple.
    Base body reference: the unconditional consume itself (cf. emitted `_ZNSt16allocator_traitsISaIiEE10deallocateERS0_Pim_fwd`,
    `stdVecDeallocFwd`). -/
def _ZNSt16allocator_traitsISaIiEE10deallocateERS0_Pim_spec_fwd (b : Vec32) (len cap : Nat) : Result (Vec32 × Nat × Nat) :=
  match vecFree b with
  | .error e => .error e
  | .ok b' => .ok (b', len, cap)

/-- Edge cases: live consume, double-free. -/
def _ZNSt16allocator_traitsISaIiEE10deallocateERS0_Pim_spec_edges : List ((Vec32 × Nat × Nat) × Result (Vec32 × Nat × Nat)) :=
  [(((⟨[1, 2], false⟩, 2, 2)), .ok (⟨[1, 2], true⟩, 2, 2)),
   (((⟨[1], true⟩, 1, 1)), .error .AssertFail)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZNSt16allocator_traitsISaIiEE10deallocateERS0_Pim_spec_check : Bool :=
  _ZNSt16allocator_traitsISaIiEE10deallocateERS0_Pim_spec_edges.all fun t =>
    (repr (_ZNSt16allocator_traitsISaIiEE10deallocateERS0_Pim_spec_fwd t.1.1 t.1.2.1 t.1.2.2)).pretty == (repr t.2).pretty
