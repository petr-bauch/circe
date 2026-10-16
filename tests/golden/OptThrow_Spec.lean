-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZSt27__throw_bad_optional_accessv()` aborts (the `-fno-exceptions` terminate lowering).
    Base body reference: the unconditional abort itself (cf. emitted `_ZSt27__throw_bad_optional_accessv_fwd`,
    `optThrowFwd`). -/
def _ZSt27__throw_bad_optional_accessv_spec_fwd : Result (BitVec 32) :=
  .error .AssertFail

/-- Edge cases: the only edge is the abort itself. -/
def _ZSt27__throw_bad_optional_accessv_spec_edges : List (Result (BitVec 32)) :=
  [.error .AssertFail]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZSt27__throw_bad_optional_accessv_spec_check : Bool :=
  _ZSt27__throw_bad_optional_accessv_spec_edges.all fun t =>
    (repr (_ZSt27__throw_bad_optional_accessv_spec_fwd)).pretty == (repr t).pretty
