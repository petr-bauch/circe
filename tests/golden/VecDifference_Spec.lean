-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z14vec_differenceRSt6vectorIiSaIiEES2_S2_(a, b, out)` records the elements of the sorted `a` absent from the sorted `b` into the caller-sized `out` (`std::set_difference` idiom with max-count multiplicity). Base body reference: the same scan plus survivor drain on the reified words (cf. emitted `_Z14vec_differenceRSt6vectorIiSaIiEES2_S2__fwd`). -/
def _Z14vec_differenceRSt6vectorIiSaIiEES2_S2__spec_fwd (la lb : List (BitVec 32)) (lo : List (BitVec 32)) : Result Nat :=
  match main la lb lo (la.length + lb.length + 1) 0 0 0 with
  | .error e => .error e
  | .ok (i, _, w, lo₁) =>
    match drain la lo₁ (la.length - i) i w with
    | .error e => .error e
    | .ok (_, w₂, _) => .ok w₂
where
  main : List (BitVec 32) → List (BitVec 32) → List (BitVec 32) → Nat → Nat → Nat → Nat → Result (Nat × Nat × Nat × List (BitVec 32))
  | la, lb, lo, 0, i, j, w => .ok (i, j, w, lo)
  | la, lb, lo, fuel + 1, i, j, w =>
    if i < la.length then
      if j < lb.length then
        match la[i]?, lb[j]? with
        | some x, some y =>
          if x.slt y then main la lb (lo.set w x) fuel (i + 1) j (w + 1)
          else if y.slt x then main la lb lo fuel i (j + 1) w
          else main la lb lo fuel (i + 1) (j + 1) w
        | _, _ => .error .AssertFail
      else .ok (i, j, w, lo)
    else .ok (i, j, w, lo)
  drain : List (BitVec 32) → List (BitVec 32) → Nat → Nat → Nat → Result (Nat × Nat × List (BitVec 32))
  | la, lo, 0, i, w => .ok (i, w, lo)
  | la, lo, fuel + 1, i, w =>
    if i < la.length then
      match la[i]? with
      | none => .error .AssertFail
      | some x =>
        match lo[w]? with
        | none => .error .AssertFail
        | some _ => drain la (lo.set w x) fuel (i + 1) (w + 1)
    else .ok (i, w, lo)

/-- Edge cases: overlap, disjoint, empty input, duplicate max-count remainder, negatives, singleton hit. -/
def _Z14vec_differenceRSt6vectorIiSaIiEES2_S2__spec_edges : List ((List (BitVec 32) × List (BitVec 32) × List (BitVec 32)) × Result Nat) :=
  [(([1, 2, 3, 4], [2, 4, 6], [0, 0, 0, 0]), .ok 2),
   (([1, 3, 5], [2, 4, 6], [0, 0, 0]), .ok 3),
   (([], [1, 2], [0, 0]), .ok 0),
   (([5, 5, 7], [5, 7, 7], [0, 0, 0]), .ok 1),
   (([-3, -1, 2], [-1, 2, 5], [0, 0, 0]), .ok 1),
   (([7], [7], [9]), .ok 0)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z14vec_differenceRSt6vectorIiSaIiEES2_S2__spec_check : Bool :=
  _Z14vec_differenceRSt6vectorIiSaIiEES2_S2__spec_edges.all fun t =>
    (repr (_Z14vec_differenceRSt6vectorIiSaIiEES2_S2__spec_fwd t.1.1 t.1.2.1 t.1.2.2)).pretty == (repr t.2).pretty
