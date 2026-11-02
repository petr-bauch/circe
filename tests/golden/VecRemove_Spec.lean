-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z10vec_removeRSt6vectorIiSaIiEEi(v, x)` compacts the `v.at(i) != x` survivors to the front (`std::remove` idiom). Base body reference: the same scan on the reified words (cf. emitted `_Z10vec_removeRSt6vectorIiSaIiEEi_fwd`). Returns the new logical length; the caller owes the `erase`/`resize` (caller-debt), the tail past the length is don't-care. Guard-justified, total. -/
def _Z10vec_removeRSt6vectorIiSaIiEEi_spec_fwd (l : List (BitVec 32)) (x : BitVec 32) : Result (Nat × List (BitVec 32)) :=
  match loop x l l.length 0 0 with
  | .error e => .error e
  | .ok (_, w, l') => .ok (w, l'.take w)
where
  loop (x : BitVec 32) : List (BitVec 32) → Nat → Nat → Nat → Result (Nat × Nat × List (BitVec 32))
  | l, 0, r, w => .ok (r, w, l)
  | l, fuel + 1, r, w =>
    if r < l.length then
      match l[r]? with
      | none => .error .AssertFail
      | some y =>
        if (y != x) then loop x (l.set w y) fuel (r + 1) (w + 1)
        else loop x l fuel (r + 1) w
    else .ok (r, w, l)

/-- Edge cases: interior drops, no-match identity, all-dropped, empty, singleton drop/keep. -/
def _Z10vec_removeRSt6vectorIiSaIiEEi_spec_edges : List ((List (BitVec 32) × BitVec 32) × Result (Nat × List (BitVec 32))) :=
  [(([1, 2, 1, 3, 1], 1), .ok (2, [2, 3])),
   (([1, 2, 3], 9), .ok (3, [1, 2, 3])),
   (([5, 5, 5], 5), .ok (0, [])),
   (([], 1), .ok (0, [])),
   (([7], 7), .ok (0, [])),
   (([7], 8), .ok (1, [7]))]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z10vec_removeRSt6vectorIiSaIiEEi_spec_check : Bool :=
  _Z10vec_removeRSt6vectorIiSaIiEEi_spec_edges.all fun t =>
    (repr (_Z10vec_removeRSt6vectorIiSaIiEEi_spec_fwd t.1.1 t.1.2)).pretty == (repr t.2).pretty
