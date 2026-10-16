-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZNKRSt8optionalIiE5valueEv(o)` is the checked `.value()` word read.
    Base body reference: the internal engaged check itself (cf. emitted `_ZNKRSt8optionalIiE5valueEv_fwd`,
    `optValueOpFwd_is_call`). -/
def _ZNKRSt8optionalIiE5valueEv_spec_fwd (o : Option (BitVec 32)) : Result (BitVec 32) :=
  match o with
  | some x => .ok x
  | none => .error .AssertFail

/-- Edge cases: payload words, zero payload, disengaged. -/
def _ZNKRSt8optionalIiE5valueEv_spec_edges : List (Option (BitVec 32) × Result (BitVec 32)) :=
  [(some 7, .ok 7), (some 0, .ok 0), (none, .error .AssertFail)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZNKRSt8optionalIiE5valueEv_spec_check : Bool :=
  _ZNKRSt8optionalIiE5valueEv_spec_edges.all fun t =>
    (repr (_ZNKRSt8optionalIiE5valueEv_spec_fwd t.1)).pretty == (repr t.2).pretty
