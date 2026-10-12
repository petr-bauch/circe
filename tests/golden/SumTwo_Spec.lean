-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base
import Circe.Emit.SumTwo

/-- C signature: `uint32_t sum_two(const uint32_t *a, const uint32_t *b, size_t n)` (two length-paired readers, wrapping).
    Body reference: the `pairSum` fold (cf. emitted `sum_two_fwd`, `emit_correct_sumTwo`). -/
def sum_two_spec_fwd (a b : List (BitVec 32)) (n : BitVec 32) : Result (BitVec 32) :=
  if n.toNat ≤ a.length ∧ n.toNat ≤ b.length then
    .ok (pairSum a b n.toNat)
  else .error .OOB

/-- Edge cases: empty, disjoint readers, aliased readers (`a == b`), `OOB` past either side, wrapping. -/
def sum_two_spec_edges : List ((List (BitVec 32) × List (BitVec 32) × BitVec 32) × Result (BitVec 32)) :=
  [((([1, 2, 3], [4, 5, 6], 3)), .ok 21),
   ((([1, 2], [1, 2], 2)), .ok 6),
   ((([], [], 0)), .ok 0),
   ((([1], [1, 2], 2)), .error .OOB),
   ((([1, 2], [1], 2)), .error .OOB),
   ((([0xFFFFFFFF], [1], 1)), .ok 0)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge.
    TODO (user): strengthen to a gallery equation over `pairSum`
    (proved by hand in `Circe.Specs`). -/
def sum_two_spec_check : Bool :=
  sum_two_spec_edges.all fun ⟨⟨a, b, n⟩, want⟩ =>
    (repr (sum_two_spec_fwd a b n)).pretty == (repr want).pretty
