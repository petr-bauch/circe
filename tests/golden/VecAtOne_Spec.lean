-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z10vec_at_oneRKSt6vectorIiSaIiEE(v)` reads `v.at(0)`.
    Base body reference: the `at(0)` read itself (cf. emitted `_Z10vec_at_oneRKSt6vectorIiSaIiEE_fwd`,
    `vecAtOneFwd`). -/
def _Z10vec_at_oneRKSt6vectorIiSaIiEE_spec_fwd (l : List (BitVec 32)) : Result (BitVec 32) :=
  match l[0]? with
  | some x => if 0 < l.length then .ok x else .error .AssertFail
  | none => .error .AssertFail

/-- Edge cases: singleton hit, empty abort. -/
def _Z10vec_at_oneRKSt6vectorIiSaIiEE_spec_edges : List (List (BitVec 32) × Result (BitVec 32)) :=
  [([7], .ok 7), ([], .error .AssertFail)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z10vec_at_oneRKSt6vectorIiSaIiEE_spec_check : Bool :=
  _Z10vec_at_oneRKSt6vectorIiSaIiEE_spec_edges.all fun t =>
    (repr (_Z10vec_at_oneRKSt6vectorIiSaIiEE_spec_fwd t.1)).pretty == (repr t.2).pretty
