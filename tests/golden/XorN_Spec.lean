-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base
import Circe.Emit.XorBuf

/-- C signature: `void xor_n(uint32_t *out, const uint32_t *a, const uint32_t *b, size_t n)` (bounded xor, `n` past any buffer is `OOB`).
    Base body reference: the `xorNList` prefix fold (cf. emitted `xor_n_fwd`, `emit_correct_xorN`). -/
def xor_n_spec_fwd (o a b : List (BitVec 32)) (n : BitVec 64) : Result (List (BitVec 32)) :=
  if n.toNat ≤ o.length ∧ n.toNat ≤ a.length ∧ n.toNat ≤ b.length then
    .ok (xorNList o a b n.toNat)
  else .error .OOB

/-- Edge cases: basic xor, garbage-out overwrite, empty range (out unchanged), partial prefix, over-long `n`, short `a`. -/
def xor_n_spec_edges : List ((List (BitVec 32) × List (BitVec 32) × List (BitVec 32) × BitVec 64) × Result (List (BitVec 32))) :=
  [((([0, 0], [1, 2], [3, 4], 2)), .ok [2, 6]),
   ((([9, 9], [0xFFFFFFFF, 0], [0xFFFFFFFF, 0], 2)), .ok [0, 0]),
   ((([7, 7], [1, 1], [2, 2], 0)), .ok [7, 7]),
   ((([9, 9], [1, 2], [3, 4], 1)), .ok [2, 9]),
   ((([0, 0], [1, 2], [3, 4], 3)), .error .OOB),
   ((([0, 0], [1], [3, 4], 2)), .error .OOB)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge.
    TODO (user): strengthen to a gallery equation over `xorNList`
    (proved by hand in `Circe.Specs`). -/
def xor_n_spec_check : Bool :=
  xor_n_spec_edges.all fun ⟨⟨o, a, b, n⟩, want⟩ =>
    (repr (xor_n_spec_fwd o a b n)).pretty == (repr want).pretty
