-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C signature: `int32_t sdiv(int32_t a, int32_t b)` (truncating division).
    Base body reference: `checkedDivI32` (cf. emitted `sdiv_fwd`, `emit_correct_sdiv`). -/
def sdiv_spec_fwd (a b : BitVec 32) : Result (BitVec 32) :=
  checkedDivI32 a b

/-- Edge cases: exact, truncating, divide-by-zero, `INT_MIN / -1` (overflow). -/
def sdiv_spec_edges : List (BitVec 32 × BitVec 32) :=
  [(6, 3), (7, 3), (1, 0), (0x80000000, 0xFFFFFFFF)]

/-- Prop-test entry: the mirror agrees with the `Base` body on every edge.
    TODO (user): strengthen to the gallery equations `sdiv_correct_ok` /
    `sdiv_correct_zero` / `sdiv_correct_overflow` (proved by hand in `Circe.Specs`). -/
def sdiv_spec_check : Bool :=
  sdiv_spec_edges.all fun p =>
    (repr (sdiv_spec_fwd p.1 p.2)).pretty == (repr (checkedDivI32 p.1 p.2)).pretty
