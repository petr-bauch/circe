-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z10stack_pushRSt6vectorIiSaIiEEmi(st, top, x)` stores `x` at `st.at(top)` and returns `top + 1` (wrapping `u64`).
    Base body reference: the guarded store plus the pure cursor advance on the reified words (cf. emitted `_Z10stack_pushRSt6vectorIiSaIiEEmi_fwd`,
    `stackPushFwd` for the workspace leg). Miss aborts like `at()`-throw. -/
def _Z10stack_pushRSt6vectorIiSaIiEEmi_spec_fwd (l : List (BitVec 32)) (top : BitVec 64) (x : BitVec 32) : Result (List (BitVec 32) × BitVec 64) :=
  match l[top.toNat]? with
  | some _ => .ok (l.set top.toNat x, top + 1)
  | none => .error .AssertFail

/-- Edge cases: hit, miss, singleton hit, empty miss, last-slot hit. -/
def _Z10stack_pushRSt6vectorIiSaIiEEmi_spec_edges : List ((List (BitVec 32) × BitVec 64 × BitVec 32) × Result (List (BitVec 32) × BitVec 64)) :=
  [(([1, 2, 3], 1, 9), (.ok ([1, 9, 3], 2))),
   (([1, 2, 3], 3, 9), .error .AssertFail),
   (([0], 0, 7), (.ok ([7], 1))),
   (([], 0, 7), .error .AssertFail),
   (([1, 2], 1, 5), (.ok ([1, 5], 2)))]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z10stack_pushRSt6vectorIiSaIiEEmi_spec_check : Bool :=
  _Z10stack_pushRSt6vectorIiSaIiEEmi_spec_edges.all fun t =>
    (repr (_Z10stack_pushRSt6vectorIiSaIiEEmi_spec_fwd t.1.1 t.1.2.1 t.1.2.2)).pretty == (repr t.2).pretty
