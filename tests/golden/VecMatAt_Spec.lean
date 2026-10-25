-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z6mat_atRKSt6vectorIiSaIiEEmmm(m, ncols, i, j)` returns `m.at(i * ncols + j)` (wrapping `u64` index).
    Base body reference: the single checked read at the wrapped index on the reified words (cf. emitted `_Z6mat_atRKSt6vectorIiSaIiEEmmm_fwd`,
    `matAtFwd`). Miss aborts like `at()`-throw (wrapping computations that land out of range included). -/
def _Z6mat_atRKSt6vectorIiSaIiEEmmm_spec_fwd (l : List (BitVec 32)) (ncols i j : BitVec 64) : Result (BitVec 32) :=
  match l[(i * ncols + j).toNat]? with
  | some w => .ok w
  | none => .error .AssertFail

/-- Edge cases: hit, miss, wrapping hit, zero-stride hit, empty miss. -/
def _Z6mat_atRKSt6vectorIiSaIiEEmmm_spec_edges : List ((List (BitVec 32) × BitVec 64 × BitVec 64 × BitVec 64) × Result (BitVec 32)) :=
  [(([1, 2, 3], 3, 0, 2), .ok 3),
   (([1, 2, 3], 3, 1, 0), .error .AssertFail),
   (([9, 8], 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF), .ok 9),
   (([5, 6], 0, 7, 1), .ok 6),
   (([], 3, 0, 0), .error .AssertFail)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z6mat_atRKSt6vectorIiSaIiEEmmm_spec_check : Bool :=
  _Z6mat_atRKSt6vectorIiSaIiEEmmm_spec_edges.all fun t =>
    (repr (_Z6mat_atRKSt6vectorIiSaIiEEmmm_spec_fwd t.1.1 t.1.2.1 t.1.2.2.1 t.1.2.2.2)).pretty == (repr t.2).pretty
