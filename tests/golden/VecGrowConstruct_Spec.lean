-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZNSt16allocator_traitsISaIiEE9constructIiJiEEEvRS0_PT_DpOT0_(t, p, v)` stores the word.
    Base body reference: the placement store itself (cf. emitted `_ZNSt16allocator_traitsISaIiEE9constructIiJiEEEvRS0_PT_DpOT0__fwd`,
    `stdVecConstructFwd`). -/
def _ZNSt16allocator_traitsISaIiEE9constructIiJiEEEvRS0_PT_DpOT0__spec_fwd (b : Vec32) (len cap : Nat) (p : BitVec 64) (x : BitVec 32) : Result (Vec32 × Nat × Nat) :=
  match vecSet b p.toNat x with
  | .error e => .error e
  | .ok b' => .ok (b', len, cap)

/-- Edge cases: store, `OOB` past the storage words. -/
def _ZNSt16allocator_traitsISaIiEE9constructIiJiEEEvRS0_PT_DpOT0__spec_edges : List ((((Vec32 × Nat × Nat) × BitVec 64) × BitVec 32) × Result (Vec32 × Nat × Nat)) :=
  [(((((⟨[1, 2], false⟩, 2, 2), 0), 9)), .ok (⟨[9, 2], false⟩, 2, 2)),
   (((((⟨[1], false⟩, 1, 1), 5), 9)), .error .OOB)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZNSt16allocator_traitsISaIiEE9constructIiJiEEEvRS0_PT_DpOT0__spec_check : Bool :=
  _ZNSt16allocator_traitsISaIiEE9constructIiJiEEEvRS0_PT_DpOT0__spec_edges.all fun t =>
    (repr (_ZNSt16allocator_traitsISaIiEE9constructIiJiEEEvRS0_PT_DpOT0__spec_fwd t.1.1.1.1 t.1.1.1.2.1 t.1.1.1.2.2 t.1.1.2 t.1.2)).pretty == (repr t.2).pretty
