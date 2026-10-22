-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z17vec_transform_addRKSt6vectorIiSaIiEERS1_i(in, out, c)` writes `in.at(i) + c` into `out.at(i)`. Base body reference: the same transform on the reified words (cf. emitted `_Z17vec_transform_addRKSt6vectorIiSaIiEERS1_i_fwd`). Short `out` aborts loudly; overflow is loud. -/
def _Z17vec_transform_addRKSt6vectorIiSaIiEERS1_i_spec_fwd (li lo : List (BitVec 32)) (c : BitVec 32) : Result (List (BitVec 32)) :=
  match loop li c lo li.length 0 with
  | .error e => .error e
  | .ok (_, lo') => .ok lo'
where
  loop (li : List (BitVec 32)) (c : BitVec 32) : List (BitVec 32) → Nat → Nat → Result (Nat × List (BitVec 32))
  | lo, 0, i => .ok (i, lo)
  | lo, fuel + 1, i =>
    if i < li.length then
      match lo[i]? with
      | none => .error .AssertFail
      | some _ =>
        match li[i]? with
        | some x =>
          match checkedAddI32 x c with
          | .error e => .error e
          | .ok y => loop li c (lo.set i y) fuel (i + 1)
        | none => .error .AssertFail
    else .ok (i, lo)

/-- Edge cases: hit adds, empty is identity, short `out` aborts, `INT_MAX + 1` overflows. -/
def _Z17vec_transform_addRKSt6vectorIiSaIiEERS1_i_spec_edges : List (((List (BitVec 32) × List (BitVec 32)) × BitVec 32) × Result (List (BitVec 32))) :=
  [((([1, 2, 3], [0, 0, 0]), 10), .ok [11, 12, 13]),
   ((([], []), 5), .ok []),
   ((([1], []), 5), .error .AssertFail),
   ((([2147483647], [0]), 1), .error .Overflow)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z17vec_transform_addRKSt6vectorIiSaIiEERS1_i_spec_check : Bool :=
  _Z17vec_transform_addRKSt6vectorIiSaIiEERS1_i_spec_edges.all fun t =>
    (repr (_Z17vec_transform_addRKSt6vectorIiSaIiEERS1_i_spec_fwd t.1.1.1 t.1.1.2 t.1.2)).pretty == (repr t.2).pretty
