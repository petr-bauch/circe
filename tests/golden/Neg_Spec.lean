-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same `Base` op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C signature: `int32_t neg(int32_t x)` (negation, `INT_MIN` overflows).
    Base body reference: `checkedNegI32` (cf. emitted `neg_fwd`, `emit_correct_neg`). -/
def neg_spec_fwd (x : BitVec 32) : Result (BitVec 32) :=
  checkedNegI32 x

/-- Edge cases: zero, unit, `INT32_MAX`, `INT32_MIN` (overflow). -/
def neg_spec_edges : List (BitVec 32) :=
  [0, 1, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF]

/-- Prop-test entry: the mirror agrees with the `Base` body on every edge.
    TODO (user): strengthen to the gallery equations `neg_correct_ok` /
    `neg_correct_err` (proved by hand in `Circe.Specs`). -/
def neg_spec_check : Bool :=
  neg_spec_edges.all fun p => (repr (neg_spec_fwd p)).pretty == (repr (checkedNegI32 p)).pretty
