-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z11vec_two_sumRKSt6vectorIiSaIiEEi(v, target)` searches `v.at(i) + v.at(j)` over `i < j`.
    Base body reference: the same pair search on the reified words (cf. emitted `_Z11vec_two_sumRKSt6vectorIiSaIiEEi_fwd`,
    `vecTwoSumFwd`). Miss forwards to `(l.length, l.length)`; overflowing sums are loud. -/
def _Z11vec_two_sumRKSt6vectorIiSaIiEEi_spec_fwd (l : List (BitVec 32)) (t : BitVec 32) : Result (BitVec 32 × BitVec 32) :=
  outer l t (l.length + 1) 0
where
  outer (l : List (BitVec 32)) (t : BitVec 32) : Nat → Nat → Result (BitVec 32 × BitVec 32)
  | 0, _ => .ok (BitVec.ofNat 32 l.length, BitVec.ofNat 32 l.length)
  | fuel + 1, i =>
    if i < l.length then
      match inner l t fuel i (i + 1) with
      | .ok (some p) => .ok p
      | .ok none => outer l t fuel (i + 1)
      | .error e => .error e
    else .ok (BitVec.ofNat 32 l.length, BitVec.ofNat 32 l.length)
  inner (l : List (BitVec 32)) (t : BitVec 32) : Nat → Nat → Nat → Result (Option (BitVec 32 × BitVec 32))
  | 0, _, _ => .ok none
  | fuel + 1, i, j =>
    if j < l.length then
      match l[i]?, l[j]? with
      | some x, some y =>
        match checkedAddI32 x y with
        | .ok s =>
          if s == t then .ok (some (BitVec.ofNat 32 i, BitVec.ofNat 32 j))
          else inner l t fuel i (j + 1)
        | .error e => .error e
      | _, _ => .ok none
    else .ok none

/-- Edge cases: early hit, miss past the end, empty miss, `nsw` overflow. -/
def _Z11vec_two_sumRKSt6vectorIiSaIiEEi_spec_edges : List ((List (BitVec 32) × BitVec 32) × Result (BitVec 32 × BitVec 32)) :=
  [(([1, 2, 3], 3), .ok (BitVec.ofNat 32 0, BitVec.ofNat 32 1)),
   (([1, 2, 3], 9), .ok (BitVec.ofNat 32 3, BitVec.ofNat 32 3)),
   (([], 0), .ok (BitVec.ofNat 32 0, BitVec.ofNat 32 0)),
   (([0x7FFFFFFF, 1], 0), .error .Overflow)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z11vec_two_sumRKSt6vectorIiSaIiEEi_spec_check : Bool :=
  _Z11vec_two_sumRKSt6vectorIiSaIiEEi_spec_edges.all fun t =>
    (repr (_Z11vec_two_sumRKSt6vectorIiSaIiEEi_spec_fwd t.1.1 t.1.2)).pretty == (repr t.2).pretty
