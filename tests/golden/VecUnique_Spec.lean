-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z10vec_uniqueRSt6vectorIiSaIiEE(v)` squeezes adjacent duplicates to the front (`std::unique` idiom). Base body reference: the same scan on the reified words (cf. emitted `_Z10vec_uniqueRSt6vectorIiSaIiEE_fwd`). Returns the new logical length; the caller owes the `erase`/`resize` (caller-debt), the tail past the length is don't-care. Guard-justified, total. -/
def _Z10vec_uniqueRSt6vectorIiSaIiEE_spec_fwd (l : List (BitVec 32)) : Result (Nat × List (BitVec 32)) :=
  match l with
  | [] => .ok (0, [])
  | _ :: _ =>
    match loop l l.length 1 1 with
    | .error e => .error e
    | .ok (_, w, l') => .ok (w, l'.take w)
where
  loop : List (BitVec 32) → Nat → Nat → Nat → Result (Nat × Nat × List (BitVec 32))
  | l, 0, r, w => .ok (r, w, l)
  | l, fuel + 1, r, w =>
    if r < l.length then
      match l[r]?, l[w - 1]? with
      | some y, some p =>
        if (y != p) then loop (l.set w y) fuel (r + 1) (w + 1)
        else loop l fuel (r + 1) w
      | _, _ => .error .AssertFail
    else .ok (r, w, l)

/-- Edge cases: runs collapse, no-op identity, all-same, empty, singleton keep, pair collapse. -/
def _Z10vec_uniqueRSt6vectorIiSaIiEE_spec_edges : List (List (BitVec 32) × Result (Nat × List (BitVec 32))) :=
  [([1, 1, 2, 2, 1], .ok (3, [1, 2, 1])),
   ([1, 2, 3], .ok (3, [1, 2, 3])),
   ([5, 5, 5], .ok (1, [5])),
   ([], .ok (0, [])),
   ([7], .ok (1, [7])),
   ([7, 7], .ok (1, [7]))]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z10vec_uniqueRSt6vectorIiSaIiEE_spec_check : Bool :=
  _Z10vec_uniqueRSt6vectorIiSaIiEE_spec_edges.all fun t =>
    (repr (_Z10vec_uniqueRSt6vectorIiSaIiEE_spec_fwd t.1)).pretty == (repr t.2).pretty
