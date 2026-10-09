-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZNKSt6vectorIiSaIiEEixEm(s, n)` reads the word at index `n`.
    Base body reference: the bounded read itself (cf. emitted `_ZNKSt6vectorIiSaIiEEixEm_fwd`,
    `stdVecIndexFwd`). -/
def _ZNKSt6vectorIiSaIiEEixEm_spec_fwd (l : List (BitVec 32)) (n : BitVec 64) : Result (BitVec 32) :=
  match l[n.toNat]? with
  | some x => .ok x
  | none => .error .OOB

/-- Edge cases: first/last hits, `OOB` past the end. -/
def _ZNKSt6vectorIiSaIiEEixEm_spec_edges : List ((List (BitVec 32) × BitVec 64) × Result (BitVec 32)) :=
  [(([1, 2, 3], 0), .ok 1), (([1, 2, 3], 2), .ok 3), (([1, 2, 3], 3), .error .OOB)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZNKSt6vectorIiSaIiEEixEm_spec_check : Bool :=
  _ZNKSt6vectorIiSaIiEEixEm_spec_edges.all fun t =>
    (repr (_ZNKSt6vectorIiSaIiEEixEm_spec_fwd t.1.1 t.1.2)).pretty == (repr t.2).pretty
