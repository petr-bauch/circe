-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z14vec_merge_sortRSt6vectorIiSaIiEES2_(a, tmp)` sorts `a` in place through the pre-sized `tmp`. Base body reference: width-doubling passes over the reified words (cf. emitted `_Z14vec_merge_sortRSt6vectorIiSaIiEES2__fwd`). -/
def _Z14vec_merge_sortRSt6vectorIiSaIiEES2__spec_fwd (la : List (BitVec 32)) : List (BitVec 32) :=
  go la 1 la.length
where
  go : List (BitVec 32) → Nat → Nat → List (BitVec 32)
  | la, w, 0 => la
  | la, w, fuel + 1 =>
    if la.length ≤ w then la
    else go (pass la w 0 la.length) (w + w) fuel
  pass : List (BitVec 32) → Nat → Nat → Nat → List (BitVec 32)
  | la, w, lo, 0 => la
  | la, w, lo, fuel + 1 =>
    if lo < la.length then
      pass (splice la (merge ((la.drop lo).take w) (((la.drop lo).drop w).take w) (((la.drop lo).take w).length + (((la.drop lo).drop w).take w).length)) lo) w (lo + w + w) fuel
    else la
  merge : List (BitVec 32) → List (BitVec 32) → Nat → List (BitVec 32)
  | xs, ys, 0 => xs ++ ys
  | [], ys, _ + 1 => ys
  | xs, [], _ + 1 => xs
  | x :: xs, y :: ys, fuel + 1 =>
    if x.slt y then x :: merge xs (y :: ys) fuel
    else y :: merge (x :: xs) ys fuel
  splice (la seg : List (BitVec 32)) (lo : Nat) : List (BitVec 32) :=
    (la.take lo) ++ seg ++ (la.drop (lo + seg.length))

/-- Edge cases: unsorted sorts stably, empty is a no-op. -/
def _Z14vec_merge_sortRSt6vectorIiSaIiEES2__spec_edges : List (List (BitVec 32) × List (BitVec 32)) :=
  [([3, 1, 2], [1, 2, 3]),
   ([], []),
   ([1], [1])]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z14vec_merge_sortRSt6vectorIiSaIiEES2__spec_check : Bool :=
  _Z14vec_merge_sortRSt6vectorIiSaIiEES2__spec_edges.all fun t =>
    (repr (_Z14vec_merge_sortRSt6vectorIiSaIiEES2__spec_fwd t.1)).pretty == (repr t.2).pretty
