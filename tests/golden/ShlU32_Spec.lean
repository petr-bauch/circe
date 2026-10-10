-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C signature: `uint32_t shl_u32(uint32_t a, uint32_t b)` (left shift, amounts ≥ 32 are `OOB`).
    Base body reference: `checkedShiftU32` (cf. emitted `shl_u32_fwd`, `emit_correct_shlU32`). -/
def shl_u32_spec_fwd (a b : BitVec 32) : Result (BitVec 32) :=
  checkedShiftU32 a b (· <<< ·)

/-- Edge cases: zero/unit amounts, bit 31, `OOB` amount, all-ones. -/
def shl_u32_spec_edges : List (BitVec 32 × BitVec 32) :=
  [(1, 0), (1, 1), (1, 31), (1, 32), (0xFFFFFFFF, 4)]

/-- Prop-test entry: the mirror agrees with the `Base` body on every edge.
    TODO (user): strengthen to the gallery equations `shlU32_correct_ok` /
    `shlU32_correct_err` (proved by hand in `Circe.Specs`). -/
def shl_u32_spec_check : Bool :=
  shl_u32_spec_edges.all fun p =>
    (repr (shl_u32_spec_fwd p.1 p.2)).pretty == (repr (checkedShiftU32 p.1 p.2 (· <<< ·))).pretty
