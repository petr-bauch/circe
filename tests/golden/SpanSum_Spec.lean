-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same `Base` op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z8span_sumSt4spanIKiLm18446744073709551615EE(s)` sums the viewed words.
    Base body reference: the checked-add fold itself (cf. emitted `_Z8span_sumSt4spanIKiLm18446744073709551615EE_fwd`,
    `spanSumFwd`). -/
def _Z8span_sumSt4spanIKiLm18446744073709551615EE_spec_fwd (l : List (BitVec 32)) : Result (BitVec 32) :=
  go l 0
where go : List (BitVec 32) → BitVec 32 → Result (BitVec 32)
  | [], acc => .ok acc
  | x :: xs, acc => do
      let a ← checkedAddI32 acc x
      go xs a

/-- Edge cases: empty sum, small sums, `nsw` overflow. -/
def _Z8span_sumSt4spanIKiLm18446744073709551615EE_spec_edges : List (List (BitVec 32) × Result (BitVec 32)) :=
  [([], .ok 0), ([1, 2, 3], .ok 6), ([0x7FFFFFFF, 1], .error .Overflow)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z8span_sumSt4spanIKiLm18446744073709551615EE_spec_check : Bool :=
  _Z8span_sumSt4spanIKiLm18446744073709551615EE_spec_edges.all fun t =>
    (repr (_Z8span_sumSt4spanIKiLm18446744073709551615EE_spec_fwd t.1)).pretty == (repr t.2).pretty
