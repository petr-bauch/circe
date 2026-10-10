-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base
import Circe.Crypto.Block

/-- C signature: `void chacha20_block(uint32_t *__restrict state)` (ten double-rounds over a 16-word copy, added back; short states are `OOB`, long states pass the tail through).
    Base body reference: the `chachaRounds`/`addBackList` fold (cf. emitted `chacha20_block_fwd`, `emit_correct_chachaBlock`). -/
def chacha20_block_spec_fwd (s : List (BitVec 32)) : Result (List (BitVec 32)) :=
  if 16 ≤ s.length then
    .ok (addBackList s (chachaRounds 10 s) 16)
  else .error .OOB

/-- Edge cases: RFC 8439 §2.3.2 KAT, all-zero state, short state (`OOB`), long state (tail passes through). -/
def chacha20_block_spec_edges : List (List (BitVec 32) × Result (List (BitVec 32))) :=
  [(([0x61707865, 0x3320646e, 0x79622d32, 0x6b206574, 0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c, 0x13121110, 0x17161514, 0x1b1a1918, 0x1f1e1d1c, 0x00000001, 0x09000000, 0x4a000000, 0x00000000]),
    .ok [0xe4e7f110, 0x15593bd1, 0x1fdd0f50, 0xc47120a3, 0xc7f4d1c7, 0x0368c033, 0x9aaa2204, 0x4e6cd4c3, 0x466482d2, 0x09aa9f07, 0x05d7c214, 0xa2028bd9, 0xd19c12b5, 0xb94e16de, 0xe883d0cb, 0x4e3c50a2]),
   (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    .ok [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
   (([0x61707865, 0x3320646e, 0x79622d32, 0x6b206574, 0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c, 0x13121110, 0x17161514, 0x1b1a1918, 0x1f1e1d1c, 0x00000001, 0x09000000, 0x4a000000]), .error .OOB),
   (([0x61707865, 0x3320646e, 0x79622d32, 0x6b206574, 0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c, 0x13121110, 0x17161514, 0x1b1a1918, 0x1f1e1d1c, 0x00000001, 0x09000000, 0x4a000000, 0x00000000, 0xdeadbeef]),
    .ok [0xe4e7f110, 0x15593bd1, 0x1fdd0f50, 0xc47120a3, 0xc7f4d1c7, 0x0368c033, 0x9aaa2204, 0x4e6cd4c3, 0x466482d2, 0x09aa9f07, 0x05d7c214, 0xa2028bd9, 0xd19c12b5, 0xb94e16de, 0xe883d0cb, 0x4e3c50a2, 0xdeadbeef])]

/-- Prop-test entry: the mirror agrees with ground truth on every edge.
    TODO (user): strengthen to a gallery equation over `chachaRounds`
    (proved by hand in `Circe.Specs`). -/
def chacha20_block_spec_check : Bool :=
  chacha20_block_spec_edges.all fun ⟨s, want⟩ =>
    (repr (chacha20_block_spec_fwd s)).pretty == (repr want).pretty
