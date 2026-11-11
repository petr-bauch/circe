-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z15vec_unique_copyRKSt6vectorIiSaIiEERS1_(a, out)` squeezes adjacent duplicates of `a` into the caller-sized `out` (`std::unique_copy` idiom). Base body reference: the same seed-plus-scan on the reified words (cf. emitted `_Z15vec_unique_copyRKSt6vectorIiSaIiEERS1__fwd`). Returns the survivor count with the squeezed prefix; a short record fails loud. -/
def _Z15vec_unique_copyRKSt6vectorIiSaIiEERS1__spec_fwd (la : List (BitVec 32)) (lo : List (BitVec 32)) : Result (Nat × List (BitVec 32)) :=
  match la with
  | [] => .ok (0, lo.take 0)
  | a0 :: _ =>
    match lo[0]? with
    | none => .error .AssertFail
    | some _ =>
      match loop la (lo.set 0 a0) la.length 1 1 with
      | .error e => .error e
      | .ok (_, w, lo') => .ok (w, lo'.take w)
where
  loop : List (BitVec 32) → List (BitVec 32) → Nat → Nat → Nat → Result (Nat × Nat × List (BitVec 32))
  | la, lo, 0, r, w => .ok (r, w, lo)
  | la, lo, fuel + 1, r, w =>
    if r < la.length then
      match la[r]?, lo[w - 1]? with
      | some y, some p =>
        if (y != p) then
          match lo[w]? with
          | none => .error .AssertFail
          | some _ => loop la (lo.set w y) fuel (r + 1) (w + 1)
        else loop la lo fuel (r + 1) w
      | _, _ => .error .AssertFail
    else .ok (r, w, lo)

/-- Edge cases: runs collapse, no-dup identity, all-same, empty input, singleton, pair collapse, two-diff, short-record loud, seed-short loud. -/
def _Z15vec_unique_copyRKSt6vectorIiSaIiEERS1__spec_edges : List ((List (BitVec 32) × List (BitVec 32)) × Result (Nat × List (BitVec 32))) :=
  [(([3, 2, 2, 1, 1], [0, 0, 0, 0, 0]), .ok (3, [3, 2, 1])),
   (([3, 1, 2], [0, 0, 0]), .ok (3, [3, 1, 2])),
   (([5, 5, 5], [0, 0, 0]), .ok (1, [5])),
   (([], [0]), .ok (0, [])),
   (([7], [9]), .ok (1, [7])),
   (([9, 9], [0, 0]), .ok (1, [9])),
   (([9, 8], [0, 0]), .ok (2, [9, 8])),
   (([1, 2], [9]), .error .AssertFail),
   (([4], []), .error .AssertFail)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z15vec_unique_copyRKSt6vectorIiSaIiEERS1__spec_check : Bool :=
  _Z15vec_unique_copyRKSt6vectorIiSaIiEERS1__spec_edges.all fun t =>
    (repr (_Z15vec_unique_copyRKSt6vectorIiSaIiEERS1__spec_fwd t.1.1 t.1.2)).pretty == (repr t.2).pretty
