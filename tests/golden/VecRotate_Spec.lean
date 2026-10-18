-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z10vec_rotateRSt6vectorIiSaIiEEm(v, k)` rotates `v` left by `k` in place. Base body reference: rotation on the reified words (cf. emitted `_Z10vec_rotateRSt6vectorIiSaIiEEm_fwd`, `vecRotateFwd`). -/
def _Z10vec_rotateRSt6vectorIiSaIiEEm_spec_fwd (l : List (BitVec 32)) (k : BitVec 64) : Result (List (BitVec 32)) :=
  if k.toNat ≤ l.length then
    .ok ((l.drop k.toNat) ++ l.take k.toNat)
  else .error .AssertFail

/-- Edge cases: empty, zero/full rotation, single steps, boundaries. -/
def _Z10vec_rotateRSt6vectorIiSaIiEEm_spec_edges : List ((List (BitVec 32) × BitVec 64) × Result (List (BitVec 32))) :=
  [(([], 0), .ok []), (([1, 2, 3], 0), .ok [1, 2, 3]),
   (([1, 2, 3], 1), .ok [2, 3, 1]), (([1, 2, 3], 2), .ok [3, 1, 2]),
   (([1, 2, 3], 3), .ok [1, 2, 3]), (([1, 2, 3, 4], 2), .ok [3, 4, 1, 2])]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z10vec_rotateRSt6vectorIiSaIiEEm_spec_check : Bool :=
  _Z10vec_rotateRSt6vectorIiSaIiEEm_spec_edges.all fun t =>
    (repr (_Z10vec_rotateRSt6vectorIiSaIiEEm_spec_fwd t.1.1 t.1.2)).pretty == (repr t.2).pretty
