-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z15opt_val_guardedRKSt8optionalIiE(o)` calls checked `.value()` when engaged, `-1` sentinel otherwise.
    Base body reference: the guarded value call itself (cf. emitted `_Z15opt_val_guardedRKSt8optionalIiE_fwd`,
    `optValueFwd`). -/
def _Z15opt_val_guardedRKSt8optionalIiE_spec_fwd (o : Option (BitVec 32)) : Result (BitVec 32) :=
  match o with
  | some x => .ok x
  | none => .ok (-1)

/-- Edge cases: payload words, zero payload, disengaged sentinel. -/
def _Z15opt_val_guardedRKSt8optionalIiE_spec_edges : List (Option (BitVec 32) × Result (BitVec 32)) :=
  [(some 7, .ok 7), (some 0, .ok 0), (none, .ok (-1))]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z15opt_val_guardedRKSt8optionalIiE_spec_check : Bool :=
  _Z15opt_val_guardedRKSt8optionalIiE_spec_edges.all fun t =>
    (repr (_Z15opt_val_guardedRKSt8optionalIiE_spec_fwd t.1)).pretty == (repr t.2).pretty
