-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same `Base` op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C signature: `uint32_t cls_fall(uint32_t x)` (`switch` on 0/1 + default, empty `case 0` falls through to `case 1`).
    Base body reference: the if-chain (cf. emitted `cls_fall_fwd`, `emit_correct_clsFall`). -/
def cls_fall_spec_fwd (x : BitVec 32) : Result (BitVec 32) :=
  if x == 0 then .ok 10
  else if x == 1 then .ok 10
  else .ok 30

/-- Edge cases: both cases (fallthrough shares the arm), default, max. -/
def cls_fall_spec_edges : List (BitVec 32) :=
  [0, 1, 2, 0xFFFFFFFF]

/-- Prop-test entry: the class equation holds on every edge (this one is
    already the spec — the if-chain is the whole body). -/
def cls_fall_spec_check : Bool :=
  cls_fall_spec_edges.all fun x =>
    (repr (cls_fall_spec_fwd x)).pretty
      == (repr (((if x == (0 : BitVec 32) then (Except.ok (10 : BitVec 32)) else if x == (1 : BitVec 32) then (Except.ok (10 : BitVec 32)) else (Except.ok (30 : BitVec 32))) : Result (BitVec 32)))).pretty
