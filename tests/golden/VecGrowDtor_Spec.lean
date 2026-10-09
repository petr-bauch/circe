-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZNSt6vectorIiSaIiEED2Ev(t)` consumes the triple.
    Base body reference: the `0 < cap`-guarded consume itself (cf. emitted `_ZNSt6vectorIiSaIiEED2Ev_fwd`,
    `stdVecDtorFwd`). -/
def _ZNSt6vectorIiSaIiEED2Ev_spec_fwd (b : Vec32) (len cap : Nat) : Result (Vec32 × Nat × Nat) :=
  if 0 < cap then
    match vecFree b with
    | .error e => .error e
    | .ok b' => .ok (b', len, cap)
  else .ok (b, len, cap)

/-- Edge cases: empty, live consume, use-after-free. -/
def _ZNSt6vectorIiSaIiEED2Ev_spec_edges : List ((Vec32 × Nat × Nat) × Result (Vec32 × Nat × Nat)) :=
  [(((⟨[], false⟩, 0, 0)), .ok (⟨[], false⟩, 0, 0)),
   (((⟨[7], false⟩, 1, 1)), .ok (⟨[7], true⟩, 1, 1)),
   (((⟨[7], true⟩, 1, 1)), .error .AssertFail)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZNSt6vectorIiSaIiEED2Ev_spec_check : Bool :=
  _ZNSt6vectorIiSaIiEED2Ev_spec_edges.all fun t =>
    (repr (_ZNSt6vectorIiSaIiEED2Ev_spec_fwd t.1.1 t.1.2.1 t.1.2.2)).pretty == (repr t.2).pretty
