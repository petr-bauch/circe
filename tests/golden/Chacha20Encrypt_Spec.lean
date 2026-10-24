-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base
import Circe.Crypto.Stream

/-- C signature: `void chacha20_encrypt(const uint32_t *key, uint32_t counter, const uint32_t *nonce, uint32_t *msg, uint32_t nwords)` (word-level §2.4.1; short inputs are `OOB`).
    Base body reference: the `chacha20EncryptList` fold (cf. emitted `chacha20_encrypt_fwd`, `emit_correct_chacha20Encrypt`). -/
def chacha20_encrypt_spec_fwd (key : List (BitVec 32)) (counter : BitVec 32)
  (nonce msg : List (BitVec 32)) (nwords : Nat) : Result (List (BitVec 32)) :=
  chacha20EncryptList key counter nonce msg nwords 0 0

/-- Edge cases: RFC 8439 §2.4.2 KAT (28-word prefix), empty message, short key/nonce/message (`OOB`), single-word tail. -/
def chacha20_encrypt_spec_edges : List ((List (BitVec 32)) × BitVec 32 × (List (BitVec 32)) × (List (BitVec 32)) × Nat × Result (List (BitVec 32))) :=
  [([0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c, 0x13121110, 0x17161514, 0x1b1a1918, 0x1f1e1d1c], 1,
    [0x00000000, 0x4a000000, 0x00000000],
    [0x6964614c, 0x61207365, 0x4720646e, 0x6c746e65, 0x6e656d65, 0x20666f20, 0x20656874, 0x73616c63, 0x666f2073, 0x39392720, 0x6649203a, 0x63204920, 0x646c756f, 0x66666f20, 0x79207265, 0x6f20756f, 0x20796c6e, 0x20656e6f, 0x20706974, 0x20726f66, 0x20656874, 0x75747566, 0x202c6572, 0x736e7573, 0x65657263, 0x6f77206e, 0x20646c75, 0x69206562], 28,
    .ok [0x9a352e6e, 0x80f96825, 0x2807ba41, 0x81690ddd, 0xec7a7ee9, 0xc260431d, 0xccaf270a, 0x0bae9ffd, 0xc5651bf9, 0xab334752, 0xab3d598f, 0x57b362cd, 0x24d63916, 0xab5251e6, 0x350c538f, 0xd861089f, 0xbf0dca07, 0x616a0d50, 0x088ea356, 0x5eb6228a, 0x4d51bc52, 0x06f8cc16, 0x1ae98c81, 0x363779b7, 0xbf0bf95a, 0xe65ba374, 0xed8e0bb4, 0x425e78f2]),
   ([0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c, 0x13121110, 0x17161514, 0x1b1a1918, 0x1f1e1d1c], 1,
    [0x00000000, 0x4a000000, 0x00000000], [], 0, .ok []),
   ([0x03020100], 1,
    [0x00000000, 0x4a000000, 0x00000000], [], 0, .error .OOB),
   ([0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c, 0x13121110, 0x17161514, 0x1b1a1918, 0x1f1e1d1c], 1,
    [0x00000000], [], 0, .error .OOB),
   ([0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c, 0x13121110, 0x17161514, 0x1b1a1918, 0x1f1e1d1c], 1,
    [0x00000000, 0x4a000000, 0x00000000], [0x6964614c], 2, .error .OOB),
   ([0x03020100, 0x07060504, 0x0b0a0908, 0x0f0e0d0c, 0x13121110, 0x17161514, 0x1b1a1918, 0x1f1e1d1c], 1,
    [0x00000000, 0x4a000000, 0x00000000], [0x6964614c], 1,
    .ok [0x9a352e6e])]

/-- Prop-test entry: the mirror agrees with ground truth on every edge.
    TODO (user): strengthen to the §2.4.1 fold equation. -/
def chacha20_encrypt_spec_check : Bool :=
  chacha20_encrypt_spec_edges.all fun ⟨key, counter, nonce, msg, nwords, want⟩ =>
    (repr (chacha20_encrypt_spec_fwd key counter nonce msg nwords)).pretty == (repr want).pretty
