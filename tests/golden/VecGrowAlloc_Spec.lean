-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZNSt12_Vector_baseIiSaIiEE11_M_allocateEm(n)` allocates `n` words.
    Base body reference: fresh storage itself (cf. emitted `_ZNSt12_Vector_baseIiSaIiEE11_M_allocateEm_fwd`,
    `stdVecAllocFwd`). -/
def _ZNSt12_Vector_baseIiSaIiEE11_M_allocateEm_spec_fwd (n : BitVec 64) : Result (Vec32 × Nat × Nat) :=
  if (BitVec.ofNat 64 0).ult n then
    if (BitVec.ofNat 64 2305843009213693951).ult n then .error .AssertFail
    else .ok (⟨List.replicate n.toNat 0, false⟩, 0, n.toNat)
  else .ok (⟨[], false⟩, 0, 0)

/-- Edge cases: empty, fresh, loud over-max. -/
def _ZNSt12_Vector_baseIiSaIiEE11_M_allocateEm_spec_edges : List (BitVec 64 × Result (Vec32 × Nat × Nat)) :=
  [(0, .ok (⟨[], false⟩, 0, 0)),
   (1, .ok (⟨[0], false⟩, 0, 1)),
   (BitVec.ofNat 64 2305843009213693952, .error .AssertFail)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZNSt12_Vector_baseIiSaIiEE11_M_allocateEm_spec_check : Bool :=
  _ZNSt12_Vector_baseIiSaIiEE11_M_allocateEm_spec_edges.all fun t =>
    (repr (_ZNSt12_Vector_baseIiSaIiEE11_M_allocateEm_spec_fwd t.1)).pretty == (repr t.2).pretty
