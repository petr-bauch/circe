-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z11vec_copy_ifRKSt6vectorIiSaIiEERS1_i(a, out, x)` records the elements of `a` differing from `x` into the caller-sized `out` (`std::copy_if` idiom). Base body reference: the same scan on the reified words (cf. emitted `_Z11vec_copy_ifRKSt6vectorIiSaIiEERS1_i_fwd`). -/
def _Z11vec_copy_ifRKSt6vectorIiSaIiEERS1_i_spec_fwd (la : List (BitVec 32)) (lo : List (BitVec 32)) (x : BitVec 32) : Result Nat :=
  match loop la lo la.length 0 0 with
  | .error e => .error e
  | .ok (_, w, _) => .ok w
where
  loop : List (BitVec 32) → List (BitVec 32) → Nat → Nat → Nat → Result (Nat × Nat × List (BitVec 32))
  | la, lo, 0, r, w => .ok (r, w, lo)
  | la, lo, fuel + 1, r, w =>
    if r < la.length then
      match la[r]? with
      | none => .error .AssertFail
      | some y =>
        if y != x then
          match lo[w]? with
          | none => .error .AssertFail
          | some _ => loop la (lo.set w y) fuel (r + 1) (w + 1)
        else loop la lo fuel (r + 1) w
    else .ok (r, w, lo)

/-- Edge cases: keeps, all-dropped, empty input, singleton hit/miss, short-`out` loud failure. -/
def _Z11vec_copy_ifRKSt6vectorIiSaIiEERS1_i_spec_edges : List (((List (BitVec 32) × List (BitVec 32)) × BitVec 32) × Result Nat) :=
  [((([1, 2, 3], [0, 0, 0]), 2), .ok 2),
   ((([5, 5, 5], [0, 0]), 5), .ok 0),
   ((([], [0]), 1), .ok 0),
   ((([7], [9]), 7), .ok 0),
   ((([7], [9]), 0), .ok 1),
   ((([1, 2], [0]), 9), .error .AssertFail)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z11vec_copy_ifRKSt6vectorIiSaIiEERS1_i_spec_check : Bool :=
  _Z11vec_copy_ifRKSt6vectorIiSaIiEERS1_i_spec_edges.all fun t =>
    (repr (_Z11vec_copy_ifRKSt6vectorIiSaIiEERS1_i_spec_fwd t.1.1.1 t.1.1.2 t.1.2)).pretty == (repr t.2).pretty
