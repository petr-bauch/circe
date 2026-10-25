-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZNKSt6vectorIcSaIcEE2atEm(s, n)` reads the word at index `n`, checked.
    Base body reference: the guarded read itself (cf. emitted `_ZNKSt6vectorIcSaIcEE2atEm_fwd`,
    `stdVecAtFwd`). -/
def _ZNKSt6vectorIcSaIcEE2atEm_spec_fwd (l : List (BitVec 32)) (n : BitVec 64) : Result (BitVec 32) :=
  match l[n.toNat]? with
  | some x => if n.toNat < l.length then .ok x else .error .AssertFail
  | none => .error .AssertFail

/-- Edge cases: first hit, miss, empty. -/
def _ZNKSt6vectorIcSaIcEE2atEm_spec_edges : List ((List (BitVec 32) × BitVec 64) × Result (BitVec 32)) :=
  [(([7], 0), .ok 7), (([7], 1), .error .AssertFail), (([], 0), .error .AssertFail)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZNKSt6vectorIcSaIcEE2atEm_spec_check : Bool :=
  _ZNKSt6vectorIcSaIcEE2atEm_spec_edges.all fun t =>
    (repr (_ZNKSt6vectorIcSaIcEE2atEm_spec_fwd t.1.1 t.1.2)).pretty == (repr t.2).pretty
