-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z13vec_partitionRSt6vectorIiSaIiEEi(v, pivot)` Lomuto-partitions `v.at(i) < pivot` to the front by swaps. Base body reference: the same scan on the reified words (cf. emitted `_Z13vec_partitionRSt6vectorIiSaIiEEi_fwd`). Guard-justified, total. -/
def _Z13vec_partitionRSt6vectorIiSaIiEEi_spec_fwd (l : List (BitVec 32)) (pivot : BitVec 32) : Result (List (BitVec 32)) :=
  match loop pivot l l.length 0 0 with
  | .error e => .error e
  | .ok (_, _, l') => .ok l'
where
  loop (pivot : BitVec 32) : List (BitVec 32) → Nat → Nat → Nat → Result (Nat × Nat × List (BitVec 32))
  | l, 0, i, s => .ok (i, s, l)
  | l, fuel + 1, i, s =>
    if i < l.length then
      match l[i]? with
      | none => .error .AssertFail
      | some x =>
        if x.slt pivot then
          match l[s]? with
          | none => .error .AssertFail
          | some w => loop pivot ((l.set i w).set s x) fuel (i + 1) (s + 1)
        else loop pivot l fuel (i + 1) s
    else .ok (i, s, l)

/-- Edge cases: empty is identity, all-below/all-above are fixed, mixed follows the swap trace. -/
def _Z13vec_partitionRSt6vectorIiSaIiEEi_spec_edges : List ((List (BitVec 32) × BitVec 32) × Result (List (BitVec 32))) :=
  [(([], 5), .ok []),
   (([3, 1, 2], 5), .ok [3, 1, 2]),
   (([7, 8], 5), .ok [7, 8]),
   (([3, 7, 1, 8, 2], 5), .ok [3, 1, 2, 8, 7]),
   (([5, 1], 5), .ok [1, 5])]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z13vec_partitionRSt6vectorIiSaIiEEi_spec_check : Bool :=
  _Z13vec_partitionRSt6vectorIiSaIiEEi_spec_edges.all fun t =>
    (repr (_Z13vec_partitionRSt6vectorIiSaIiEEi_spec_fwd t.1.1 t.1.2)).pretty == (repr t.2).pretty
