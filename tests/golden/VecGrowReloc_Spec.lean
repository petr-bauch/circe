-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same `Base` op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZNSt6vectorIiSaIiEE11_S_relocateEPiS2_S2_RS0_(src, dst, first, last, result)` copies the range.
    Base body reference: the copy loop itself (cf. emitted `_ZNSt6vectorIiSaIiEE11_S_relocateEPiS2_S2_RS0__fwd`,
    `stdVecRelocFwd`). -/
def _ZNSt6vectorIiSaIiEE11_S_relocateEPiS2_S2_RS0__spec_fwd (bS : Vec32) (lenS : Nat) (_capS : Nat) (bD : Vec32) (lenD capD : Nat) (first last result : BitVec 64) : Result (Vec32 × Nat × Nat) :=
  match stdVecBlitFold bS.val lenS bS.freed bD result.toNat first.toNat (last.toNat - first.toNat) with
  | .error e => .error e
  | .ok bD' => .ok (bD', lenD, capD)

/-- Edge cases: empty trip, copy, consumed source. -/
def _ZNSt6vectorIiSaIiEE11_S_relocateEPiS2_S2_RS0__spec_edges : List (((Vec32 × Nat × Nat × Vec32 × Nat × Nat × BitVec 64 × BitVec 64 × BitVec 64)) × Result (Vec32 × Nat × Nat)) :=
  [(((⟨[], false⟩, 0, 0, ⟨[9], false⟩, 1, 1, 0, 0, 0)), .ok (⟨[9], false⟩, 1, 1)),
   (((⟨[5, 6], false⟩, 2, 2, ⟨[0, 0, 0], false⟩, 0, 3, 0, 2, 1)), .ok (⟨[0, 5, 6], false⟩, 0, 3)),
   (((⟨[5], true⟩, 1, 1, ⟨[0], false⟩, 0, 1, 0, 1, 0)), .error .AssertFail)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZNSt6vectorIiSaIiEE11_S_relocateEPiS2_S2_RS0__spec_check : Bool :=
  _ZNSt6vectorIiSaIiEE11_S_relocateEPiS2_S2_RS0__spec_edges.all fun t =>
    (repr (_ZNSt6vectorIiSaIiEE11_S_relocateEPiS2_S2_RS0__spec_fwd t.1.1 t.1.2.1 t.1.2.2.1 t.1.2.2.2.1 t.1.2.2.2.2.1 t.1.2.2.2.2.2.1 t.1.2.2.2.2.2.2.1 t.1.2.2.2.2.2.2.2.1 t.1.2.2.2.2.2.2.2.2)).pretty == (repr t.2).pretty
