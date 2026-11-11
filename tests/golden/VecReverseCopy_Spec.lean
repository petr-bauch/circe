-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z16vec_reverse_copyRKSt6vectorIiSaIiEERS1_(a, out)` reverses `a` into the caller-sized `out` (countdown read `a[j - 1]`, sequential write `out[w]`). Base body reference: the same countdown scan on the reified words (cf. emitted `_Z16vec_reverse_copyRKSt6vectorIiSaIiEERS1__fwd`). Returns the copied count with the reversed prefix; a short record fails loud. -/
def _Z16vec_reverse_copyRKSt6vectorIiSaIiEERS1__spec_fwd (la : List (BitVec 32)) (lo : List (BitVec 32)) : Result (Nat × List (BitVec 32)) :=
  match la with
  | [] => .ok (0, lo.take 0)
  | _ :: _ =>
    match loop la lo la.length 0 la.length with
    | .error e => .error e
    | .ok (w, _, lo') => .ok (w, lo'.take w)
where
  loop : List (BitVec 32) → List (BitVec 32) → Nat → Nat → Nat → Result (Nat × Nat × List (BitVec 32))
  | la, lo, 0, w, j => .ok (w, j, lo)
  | la, lo, fuel + 1, w, j =>
    if 0 < j then
      match la[j - 1]?, lo[w]? with
      | some y, some _ => loop la (lo.set w y) fuel (w + 1) (j - 1)
      | _, _ => .error .AssertFail
    else .ok (w, j, lo)

/-- Edge cases: reversal, empty input, singleton, pair swap, overwrite record, dup-preserving reverse, short-record loud, empty-record loud. -/
def _Z16vec_reverse_copyRKSt6vectorIiSaIiEERS1__spec_edges : List ((List (BitVec 32) × List (BitVec 32)) × Result (Nat × List (BitVec 32))) :=
  [(([3, 1, 2], [0, 0, 0]), .ok (3, [2, 1, 3])),
   (([], [0]), .ok (0, [])),
   (([7], [9]), .ok (1, [7])),
   (([9, 8], [0, 0]), .ok (2, [8, 9])),
   (([1, 2, 3], [7, 7, 7]), .ok (3, [3, 2, 1])),
   (([5, 5], [0, 0]), .ok (2, [5, 5])),
   (([1, 2], [9]), .error .AssertFail),
   (([4], []), .error .AssertFail)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z16vec_reverse_copyRKSt6vectorIiSaIiEERS1__spec_check : Bool :=
  _Z16vec_reverse_copyRKSt6vectorIiSaIiEERS1__spec_edges.all fun t =>
    (repr (_Z16vec_reverse_copyRKSt6vectorIiSaIiEERS1__spec_fwd t.1.1 t.1.2)).pretty == (repr t.2).pretty
