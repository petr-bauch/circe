-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z18vec_partition_copyRKSt6vectorIiSaIiEERS1_S4_i(a, yes, no, pivot)` records the elements of `a` below `pivot` (signed) into the caller-sized `yes` and the rest into the caller-sized `no` (`std::partition_copy` idiom). Base body reference: the same read-cursor scan on the reified words (cf. emitted `_Z18vec_partition_copyRKSt6vectorIiSaIiEERS1_S4_i_fwd`). Returns the keeper count; a short record on either side fails loud. -/
def _Z18vec_partition_copyRKSt6vectorIiSaIiEERS1_S4_i_spec_fwd (la yes no : List (BitVec 32)) (pivot : BitVec 32) : Result Nat :=
  match loop la yes no la.length 0 0 0 with
  | .error e => .error e
  | .ok (_, wYes, _, _, _) => .ok wYes
where
  loop : List (BitVec 32) → List (BitVec 32) → List (BitVec 32) → Nat → Nat → Nat → Nat → Result (Nat × Nat × Nat × List (BitVec 32) × List (BitVec 32))
  | la, yes, no, 0, r, wYes, wNo => .ok (r, wYes, wNo, yes, no)
  | la, yes, no, fuel + 1, r, wYes, wNo =>
    if r < la.length then
      match la[r]? with
      | none => .error .AssertFail
      | some y =>
        if y.slt pivot then
          match yes[wYes]? with
          | none => .error .AssertFail
          | some _ => loop la (yes.set wYes y) no fuel (r + 1) (wYes + 1) wNo
        else
          match no[wNo]? with
          | none => .error .AssertFail
          | some _ => loop la yes (no.set wNo y) fuel (r + 1) wYes (wNo + 1)
    else .ok (r, wYes, wNo, yes, no)

/-- Edge cases: mixed split, all-keep, all-drop, empty input, singleton hit/miss, short-record loud on either side. -/
def _Z18vec_partition_copyRKSt6vectorIiSaIiEERS1_S4_i_spec_edges : List ((((List (BitVec 32) × List (BitVec 32)) × List (BitVec 32)) × BitVec 32) × Result Nat) :=
  [(((([3, 1, 2], [0, 0, 0]), [0, 0, 0]), 2), .ok 1),
   (((([1, 1], [0, 0]), []), 9), .ok 2),
   (((([5, 5], []), [0, 0]), 0), .ok 0),
   (((([], [0]), [0]), 1), .ok 0),
   (((([7], [9]), [9]), 8), .ok 1),
   (((([7], [9]), [9]), 7), .ok 0),
   (((([1, 2], [0]), [0, 0]), 9), .error .AssertFail),
   (((([1, 2], [0, 0]), [0]), 0), .error .AssertFail)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z18vec_partition_copyRKSt6vectorIiSaIiEERS1_S4_i_spec_check : Bool :=
  _Z18vec_partition_copyRKSt6vectorIiSaIiEERS1_S4_i_spec_edges.all fun t =>
    (repr (_Z18vec_partition_copyRKSt6vectorIiSaIiEERS1_S4_i_spec_fwd t.1.1.1.1 t.1.1.1.2 t.1.1.2 t.1.2)).pretty == (repr t.2).pretty
