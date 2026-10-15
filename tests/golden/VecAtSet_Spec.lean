-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z10vec_at_setRSt6vectorIiSaIiEEmi(v, i, x)` stores `x` at `v.at(i)`.
    Base body reference: the same checked store on the reified words (cf. emitted `_Z10vec_at_setRSt6vectorIiSaIiEEmi_fwd`,
    `vecAtSetFwd`). Miss aborts loudly. -/
def _Z10vec_at_setRSt6vectorIiSaIiEEmi_spec_fwd (l : List (BitVec 32)) (n : BitVec 64) (x : BitVec 32) : Result (List (BitVec 32)) :=
  match l[n.toNat]? with
  | some _ => .ok (l.set n.toNat x)
  | none => .error .AssertFail

/-- Edge cases: hit stores, miss aborts, empty aborts. -/
def _Z10vec_at_setRSt6vectorIiSaIiEEmi_spec_edges : List ((List (BitVec 32) × BitVec 64 × BitVec 32) × Result (List (BitVec 32))) :=
  [(([1, 2, 3], 1, 9), .ok [1, 9, 3]),
   (([1, 2, 3], 3, 9), .error .AssertFail),
   (([], 0, 9), .error .AssertFail)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z10vec_at_setRSt6vectorIiSaIiEEmi_spec_check : Bool :=
  _Z10vec_at_setRSt6vectorIiSaIiEEmi_spec_edges.all fun t =>
    (repr (_Z10vec_at_setRSt6vectorIiSaIiEEmi_spec_fwd t.1.1 t.1.2.1 t.1.2.2)).pretty == (repr t.2).pretty
