-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZNSt6vectorIiSaIiEEC2Ev()` builds the empty vector.
    Base body reference: the empty triple itself (cf. emitted `_ZNSt6vectorIiSaIiEEC2Ev_fwd`,
    `stdVecEmptyCtorFwd`). -/
def _ZNSt6vectorIiSaIiEEC2Ev_spec_fwd : Vec32 × Nat × Nat :=
  (⟨[], false⟩, 0, 0)

/-- Edge cases: the single empty triple. -/
def _ZNSt6vectorIiSaIiEEC2Ev_spec_edges : List (Unit × (Vec32 × Nat × Nat)) :=
  [((), (⟨[], false⟩, 0, 0))]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZNSt6vectorIiSaIiEEC2Ev_spec_check : Bool :=
  _ZNSt6vectorIiSaIiEEC2Ev_spec_edges.all fun t =>
    (repr (_ZNSt6vectorIiSaIiEEC2Ev_spec_fwd)).pretty == (repr t.2).pretty
