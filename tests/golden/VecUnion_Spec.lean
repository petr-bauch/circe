-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z9vec_unionRSt6vectorIiSaIiEES2_S2_(a, b, out)` records the sorted union of `a` and `b` into the caller-sized `out` (`std::set_union` idiom with max-count multiplicity). Base body reference: the same scan plus survivor drains on the reified words (cf. emitted `_Z9vec_unionRSt6vectorIiSaIiEES2_S2__fwd`). -/
def _Z9vec_unionRSt6vectorIiSaIiEES2_S2__spec_fwd (la lb : List (BitVec 32)) (lo : List (BitVec 32)) : Result Nat :=
  match main la lb lo (la.length + lb.length + 1) 0 0 0 with
  | .error e => .error e
  | .ok (i, j, w, lo₁) =>
    match drainA la lo₁ (la.length - i) i w with
    | .error e => .error e
    | .ok (_, w₂, lo₂) =>
      match drainB lb lo₂ (lb.length - j) j w₂ with
      | .error e => .error e
      | .ok (_, w₃, _) => .ok w₃
where
  main : List (BitVec 32) → List (BitVec 32) → List (BitVec 32) → Nat → Nat → Nat → Nat → Result (Nat × Nat × Nat × List (BitVec 32))
  | la, lb, lo, 0, i, j, w => .ok (i, j, w, lo)
  | la, lb, lo, fuel + 1, i, j, w =>
    if i < la.length then
      if j < lb.length then
        match la[i]?, lb[j]? with
        | some x, some y =>
          if x.slt y then main la lb (lo.set w x) fuel (i + 1) j (w + 1)
          else if y.slt x then main la lb (lo.set w y) fuel i (j + 1) (w + 1)
          else main la lb (lo.set w x) fuel (i + 1) (j + 1) (w + 1)
        | _, _ => .error .AssertFail
      else .ok (i, j, w, lo)
    else .ok (i, j, w, lo)
  drainA : List (BitVec 32) → List (BitVec 32) → Nat → Nat → Nat → Result (Nat × Nat × List (BitVec 32))
  | la, lo, 0, i, w => .ok (i, w, lo)
  | la, lo, fuel + 1, i, w =>
    if i < la.length then
      match la[i]? with
      | none => .error .AssertFail
      | some x =>
        match lo[w]? with
        | none => .error .AssertFail
        | some _ => drainA la (lo.set w x) fuel (i + 1) (w + 1)
    else .ok (i, w, lo)
  drainB : List (BitVec 32) → List (BitVec 32) → Nat → Nat → Nat → Result (Nat × Nat × List (BitVec 32))
  | lb, lo, 0, j, w => .ok (j, w, lo)
  | lb, lo, fuel + 1, j, w =>
    if j < lb.length then
      match lb[j]? with
      | none => .error .AssertFail
      | some y =>
        match lo[w]? with
        | none => .error .AssertFail
        | some _ => drainB lb (lo.set w y) fuel (j + 1) (w + 1)
    else .ok (j, w, lo)

/-- Edge cases: overlap, disjoint, empty input, duplicate max-count, negatives, singleton hit. -/
def _Z9vec_unionRSt6vectorIiSaIiEES2_S2__spec_edges : List ((List (BitVec 32) × List (BitVec 32) × List (BitVec 32)) × Result Nat) :=
  [(([1, 2, 3, 4], [2, 4, 6], [0, 0, 0, 0, 0, 0, 0]), .ok 5),
   (([1, 3, 5], [2, 4, 6], [0, 0, 0, 0, 0, 0]), .ok 6),
   (([], [1, 2], [0, 0]), .ok 2),
   (([5, 5, 7], [5, 7, 7], [0, 0, 0, 0, 0, 0]), .ok 4),
   (([-3, -1, 2], [-1, 2, 5], [0, 0, 0, 0, 0, 0]), .ok 4),
   (([7], [7], [9]), .ok 1)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z9vec_unionRSt6vectorIiSaIiEES2_S2__spec_check : Bool :=
  _Z9vec_unionRSt6vectorIiSaIiEES2_S2__spec_edges.all fun t =>
    (repr (_Z9vec_unionRSt6vectorIiSaIiEES2_S2__spec_fwd t.1.1 t.1.2.1 t.1.2.2)).pretty == (repr t.2).pretty
