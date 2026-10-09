-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C signature: `uint32_t cls_break(uint32_t x)` (`switch` on 0/1, no `default`: guarded stores + `break`, `99` initializer).
    Base body reference: the guarded assigns (cf. emitted `cls_break_fwd`, `emit_correct_clsBreak`). -/
def cls_break_spec_fwd (x : BitVec 32) : Result (BitVec 32) :=
  .ok (if x == 0 then 10 else if x == 1 then 20 else 99)

/-- Edge cases: both cases, initializer path, max. -/
def cls_break_spec_edges : List (BitVec 32) :=
  [0, 1, 2, 0xFFFFFFFF]

/-- Prop-test entry: the class equation holds on every edge (this one is
    already the spec — the guarded assigns are the whole body). -/
def cls_break_spec_check : Bool :=
  cls_break_spec_edges.all fun x =>
    (repr (cls_break_spec_fwd x)).pretty
      == (repr (((Except.ok (if x == (0 : BitVec 32) then (10 : BitVec 32) else if x == (1 : BitVec 32) then (20 : BitVec 32) else (99 : BitVec 32))) : Result (BitVec 32)))).pretty
