-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z13vec_intersectRSt6vectorIiSaIiEES2_S2_(a, b, out)` records the sorted intersection of `a` and `b` into the caller-sized `out` (`std::set_intersection` idiom). Base body reference: the same scan on the reified words (cf. emitted `_Z13vec_intersectRSt6vectorIiSaIiEES2_S2__fwd`). -/
def _Z13vec_intersectRSt6vectorIiSaIiEES2_S2__spec_fwd (la lb : List (BitVec 32)) (lo : List (BitVec 32)) : Result Nat :=
  match loop la lb lo (la.length + lb.length + 1) 0 0 0 with
  | .error e => .error e
  | .ok (_, _, w, _) => .ok w
where
  loop : List (BitVec 32) → List (BitVec 32) → List (BitVec 32) → Nat → Nat → Nat → Nat → Result (Nat × Nat × Nat × List (BitVec 32))
  | la, lb, lo, 0, i, j, w => .ok (i, j, w, lo)
  | la, lb, lo, fuel + 1, i, j, w =>
    if i < la.length then
      if j < lb.length then
        match la[i]?, lb[j]? with
        | some x, some y =>
          if x.slt y then loop la lb lo fuel (i + 1) j w
          else if y.slt x then loop la lb lo fuel i (j + 1) w
          else loop la lb (lo.set w x) fuel (i + 1) (j + 1) (w + 1)
        | _, _ => .error .AssertFail
      else .ok (i, j, w, lo)
    else .ok (i, j, w, lo)

/-- Edge cases: overlap, disjoint, empty input, duplicate min-count, negatives, singleton hit. -/
def _Z13vec_intersectRSt6vectorIiSaIiEES2_S2__spec_edges : List ((List (BitVec 32) × List (BitVec 32) × List (BitVec 32)) × Result Nat) :=
  [(([1, 2, 3, 4], [2, 4, 6], [0, 0, 0, 0]), .ok 2),
   (([1, 3, 5], [2, 4, 6], [0, 0, 0]), .ok 0),
   (([], [1, 2], [0, 0]), .ok 0),
   (([5, 5, 7], [5, 7, 7], [0, 0, 0]), .ok 2),
   (([-3, -1, 2], [-1, 2, 5], [0, 0, 0]), .ok 2),
   (([7], [7], [9]), .ok 1)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z13vec_intersectRSt6vectorIiSaIiEES2_S2__spec_check : Bool :=
  _Z13vec_intersectRSt6vectorIiSaIiEES2_S2__spec_edges.all fun t =>
    (repr (_Z13vec_intersectRSt6vectorIiSaIiEES2_S2__spec_fwd t.1.1 t.1.2.1 t.1.2.2)).pretty == (repr t.2).pretty
