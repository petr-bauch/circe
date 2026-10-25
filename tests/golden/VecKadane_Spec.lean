-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z12max_subarrayRKSt6vectorIiSaIiEE(v)` returns the maximum subarray sum of `v.at(i)`.
    Base body reference: Kadane's algorithm on the reified words, seeded from `l[0]`
    (cf. emitted `_Z12max_subarrayRKSt6vectorIiSaIiEE_fwd`). Empty input fails like `at()`-throw; `nsw` overflow is loud. -/
def _Z12max_subarrayRKSt6vectorIiSaIiEE_spec_fwd (l : List (BitVec 32)) : Result (BitVec 32) :=
  match l with
  | [] => .error .AssertFail
  | h :: t => (go t h h).map (fun p => p.2)
where go : List (BitVec 32) → BitVec 32 → BitVec 32 → Result (BitVec 32 × BitVec 32)
  | [], cur, best => .ok (cur, best)
  | x :: xs, cur, best => do
      let s ← checkedAddI32 cur x
      let c := if s.slt x then x else s
      go xs c (if best.slt c then c else best)

/-- Edge cases: empty seed failure, small sums, all-negative, `nsw` overflow, canonical mix. -/
def _Z12max_subarrayRKSt6vectorIiSaIiEE_spec_edges : List (List (BitVec 32) × Result (BitVec 32)) :=
  [([], .error .AssertFail), ([1, 2, 3], .ok 6),
   ([0xFFFFFFFF, 0xFFFFFFFF], .ok 0xFFFFFFFF),
   ([0x7FFFFFFF, 1], .error .Overflow), ([2, 0xFFFFFFFF, 3], .ok 4),
   ([0xFFFFFFFE, 1, 0xFFFFFFFD, 4, 0xFFFFFFFF, 2, 1, 0xFFFFFFFB, 4], .ok 6)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z12max_subarrayRKSt6vectorIiSaIiEE_spec_check : Bool :=
  _Z12max_subarrayRKSt6vectorIiSaIiEE_spec_edges.all fun t =>
    (repr (_Z12max_subarrayRKSt6vectorIiSaIiEE_spec_fwd t.1)).pretty == (repr t.2).pretty
