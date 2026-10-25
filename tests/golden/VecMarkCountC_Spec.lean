-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z12mark_count_cRKSt6vectorIcSaIcEERS1_m(m, vis, u)` seeds `vis.at(u) = 1`, then sums `vis.at(v)` over `v` with `m.at(v) != 0`.
    Base body reference: seed plus the gated checked-add fold on the reified words (cf. emitted `_Z12mark_count_cRKSt6vectorIcSaIcEERS1_m_fwd`,
    `markFwd`). Seed miss aborts like `at()`-throw; a short mask aborts `OOB`; `nsw` overflow is loud. -/
def _Z12mark_count_cRKSt6vectorIcSaIcEERS1_m_spec_fwd (m vis : List (BitVec 32)) (u : BitVec 64) : Result (BitVec 32) :=
  match vis[u.toNat]? with
  | none => .error .AssertFail
  | some _ => go m (vis.set u.toNat 1) 0
where go : List (BitVec 32) → List (BitVec 32) → BitVec 32 → Result (BitVec 32)
  | _, [], acc => .ok acc
  | [], _ :: _, _ => .error .OOB
  | mh :: mt, vh :: vt, acc =>
      if mh != 0 then do
        let a ← checkedAddI32 acc vh
        go mt vt a
      else go mt vt acc

/-- Edge cases: seed hit, seed miss, short mask, all-masked, `nsw` overflow. -/
def _Z12mark_count_cRKSt6vectorIcSaIcEERS1_m_spec_edges : List ((List (BitVec 32) × List (BitVec 32) × BitVec 64) × Result (BitVec 32)) :=
  [(([1, 0, 1], [0, 0, 0], 0), .ok 1),
   (([1], [0], 5), .error .AssertFail),
   (([1], [0, 0], 0), .error .OOB),
   (([0, 0], [5, 6], 1), .ok 0),
   (([1, 1], [0x7FFFFFFF, 0x7FFFFFFF], 0), .error .Overflow)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z12mark_count_cRKSt6vectorIcSaIcEERS1_m_spec_check : Bool :=
  _Z12mark_count_cRKSt6vectorIcSaIcEERS1_m_spec_edges.all fun t =>
    (repr (_Z12mark_count_cRKSt6vectorIcSaIcEERS1_m_spec_fwd t.1.1 t.1.2.1 t.1.2.2)).pretty == (repr t.2).pretty
