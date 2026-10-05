-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same `Base` op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C signature: `uint32_t cls_dense(uint32_t x)` (`switch` on 0..7 + default).
    Base body reference: the if-chain (cf. emitted `cls_dense_fwd`, `emit_correct_clsDense`). -/
def cls_dense_spec_fwd (x : BitVec 32) : Result (BitVec 32) :=
  if x == 0 then .ok 0
  else if x == 1 then .ok 10
  else if x == 2 then .ok 20
  else if x == 3 then .ok 30
  else if x == 4 then .ok 40
  else if x == 5 then .ok 50
  else if x == 6 then .ok 60
  else if x == 7 then .ok 70
  else .ok 80

/-- Edge cases: every case, default, max. -/
def cls_dense_spec_edges : List (BitVec 32) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 0xFFFFFFFF]

/-- Prop-test entry: the class equation holds on every edge (this one is
    already the spec — the if-chain is the whole body). -/
def cls_dense_spec_check : Bool :=
  cls_dense_spec_edges.all fun x =>
    (repr (cls_dense_spec_fwd x)).pretty
      == (repr (((if x == (0 : BitVec 32) then (Except.ok (0 : BitVec 32)) else if x == (1 : BitVec 32) then (Except.ok (10 : BitVec 32)) else if x == (2 : BitVec 32) then (Except.ok (20 : BitVec 32)) else if x == (3 : BitVec 32) then (Except.ok (30 : BitVec 32)) else if x == (4 : BitVec 32) then (Except.ok (40 : BitVec 32)) else if x == (5 : BitVec 32) then (Except.ok (50 : BitVec 32)) else if x == (6 : BitVec 32) then (Except.ok (60 : BitVec 32)) else if x == (7 : BitVec 32) then (Except.ok (70 : BitVec 32)) else (Except.ok (80 : BitVec 32))) : Result (BitVec 32)))).pretty
