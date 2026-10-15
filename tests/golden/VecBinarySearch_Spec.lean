-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z17vec_binary_searchRKSt6vectorIiSaIiEEi(v, target)` searches `v.at(mid)` over `[lo, hi)`.
    Base body reference: the same search on the reified words (cf. emitted `_Z17vec_binary_searchRKSt6vectorIiSaIiEEi_fwd`,
    `vecBinarySearchFwd`). Miss forwards to `l.length`. -/
def _Z17vec_binary_searchRKSt6vectorIiSaIiEEi_spec_fwd (l : List (BitVec 32)) (t : BitVec 32) : Result (BitVec 64) :=
  go l t (l.length + 1) 0 l.length
where go (l : List (BitVec 32)) (t : BitVec 32) : Nat → Nat → Nat → Result (BitVec 64)
  | 0, _, _ => .ok (BitVec.ofNat 64 l.length)
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := lo + (hi - lo) / 2
      match l[mid]? with
      | some x =>
        if x == t then .ok (BitVec.ofNat 64 mid)
        else if x.slt t then go l t fuel (mid + 1) hi
        else go l t fuel lo mid
      | none => .ok (BitVec.ofNat 64 l.length)
    else .ok (BitVec.ofNat 64 l.length)

/-- Edge cases: sorted hit, miss past the end, empty miss. -/
def _Z17vec_binary_searchRKSt6vectorIiSaIiEEi_spec_edges : List ((List (BitVec 32) × BitVec 32) × Result (BitVec 64)) :=
  [(([1, 2, 3], 2), .ok 1), (([1, 2, 3], 5), .ok (BitVec.ofNat 64 3)),
   (([], 0), .ok (BitVec.ofNat 64 0))]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z17vec_binary_searchRKSt6vectorIiSaIiEEi_spec_check : Bool :=
  _Z17vec_binary_searchRKSt6vectorIiSaIiEEi_spec_edges.all fun t =>
    (repr (_Z17vec_binary_searchRKSt6vectorIiSaIiEEi_spec_fwd t.1.1 t.1.2)).pretty == (repr t.2).pretty
