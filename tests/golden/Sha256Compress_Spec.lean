-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base
import Circe.Crypto.Sha

/-- C signature: `void sha256_compress(uint32_t *__restrict st)` (compress the 16-word block at `st[8..24]` into the 8-word state; short states are `OOB`, long states pass the tail through).
    Base body reference: the `sha256CompressFwd` fold (cf. emitted `sha256_compress_fwd`, `emit_correct_sha256`). -/
def sha256_compress_spec_fwd (s : List (BitVec 32)) : Result (List (BitVec 32)) :=
  if 24 ≤ s.length then
    .ok (sha256CompressFwd s)
  else .error .OOB

/-- Edge cases: FIPS 180-4 §8.1.1 "abc" KAT, all-zero state, short state (`OOB`), long state (tail passes through). -/
def sha256_compress_spec_edges : List (List (BitVec 32) × Result (List (BitVec 32))) :=
  [(([0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19, 0x61626380, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000018]),
    .ok [0xba7816bf, 0x8f01cfea, 0x414140de, 0x5dae2223, 0xb00361a3, 0x96177a9c, 0xb410ff61, 0xf20015ad, 0x61626380, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000018]),
   (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
    .ok [0x7ca51614, 0x425c3ba8, 0xce54dd2f, 0xc2020ae7, 0xb6e574d1, 0x98136d0f, 0xae7e26cc, 0xbf0be7a6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]),
   (([0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19, 0x61626380, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000]), .error .OOB),
   (([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xdeadbeef]),
    .ok [0x7ca51614, 0x425c3ba8, 0xce54dd2f, 0xc2020ae7, 0xb6e574d1, 0x98136d0f, 0xae7e26cc, 0xbf0be7a6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0xdeadbeef])]

/-- Prop-test entry: the mirror agrees with ground truth on every edge.
    TODO (user): strengthen to a gallery equation over `sha256CompressFwd`
    (proved by hand in `Circe.Specs`). -/
def sha256_compress_spec_check : Bool :=
  sha256_compress_spec_edges.all fun ⟨s, want⟩ =>
    (repr (sha256_compress_spec_fwd s)).pretty == (repr want).pretty
