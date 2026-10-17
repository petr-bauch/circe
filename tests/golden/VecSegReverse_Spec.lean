-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z15vec_seg_reverseRSt6vectorIiSaIiEEmm(v, lo, hi)` reverses `v[lo, hi)` in place. Base body reference: window reversal on the reified words (cf. emitted `_Z15vec_seg_reverseRSt6vectorIiSaIiEEmm_fwd`, `vecSegReverseFwd`). -/
def _Z15vec_seg_reverseRSt6vectorIiSaIiEEmm_spec_fwd (l : List (BitVec 32)) (lo hi : BitVec 64) : Result (List (BitVec 32)) :=
  .ok (l.take lo.toNat ++ ((l.drop lo.toNat).take (hi.toNat - lo.toNat)).reverse ++ l.drop hi.toNat)

/-- Edge cases: empty/full windows, prefix, suffix, interior, singleton. -/
def _Z15vec_seg_reverseRSt6vectorIiSaIiEEmm_spec_edges : List ((List (BitVec 32) × BitVec 64 × BitVec 64) × Result (List (BitVec 32))) :=
  [(([], 0, 0), .ok []), (([1, 2, 3], 0, 3), .ok [3, 2, 1]),
   (([1, 2, 3], 0, 2), .ok [2, 1, 3]), (([1, 2, 3], 1, 3), .ok [1, 3, 2]),
   (([1, 2, 3, 4], 1, 3), .ok [1, 3, 2, 4]), (([1, 2, 3], 1, 2), .ok [1, 2, 3])]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z15vec_seg_reverseRSt6vectorIiSaIiEEmm_spec_check : Bool :=
  _Z15vec_seg_reverseRSt6vectorIiSaIiEEmm_spec_edges.all fun t =>
    (repr (_Z15vec_seg_reverseRSt6vectorIiSaIiEEmm_spec_fwd t.1.1 t.1.2.1 t.1.2.2)).pretty == (repr t.2).pretty
