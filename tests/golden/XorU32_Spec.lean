-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C signature: `uint32_t xor_u32(uint32_t a, uint32_t b)` (bitwise xor, total).
    Base body reference: `a ^^^ b` (cf. emitted `xor_u32_fwd`, `emit_correct_xorU32`). -/
def xor_u32_spec_fwd (a b : BitVec 32) : Result (BitVec 32) :=
  .ok (a ^^^ b)

/-- Edge cases: zeros, all-ones, nibble-split, unit. -/
def xor_u32_spec_edges : List (BitVec 32 × BitVec 32) :=
  [(0, 0), (0xFFFFFFFF, 0xFFFFFFFF), (0xF0F0F0F0, 0x0F0F0F0F), (1, 0)]

/-- Prop-test entry: the mirror agrees with the `Base` body on every edge.
    TODO (user): strengthen to the gallery equation `xorU32_correct`
    (proved by hand in `Circe.Specs`). -/
def xor_u32_spec_check : Bool :=
  xor_u32_spec_edges.all fun p =>
    (repr (xor_u32_spec_fwd p.1 p.2)).pretty == (repr ((Except.ok (p.1 ^^^ p.2) : Result (BitVec 32)))).pretty
