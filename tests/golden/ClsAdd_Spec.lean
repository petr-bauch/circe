-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C signature: `uint32_t cls_add(uint32_t x, uint32_t y)` (`switch` on 0/1 + default: `y + 1` / `y + 2` / `y`, wrapping).
    Base body reference: the `uadd` if-chain (cf. emitted `cls_add_fwd`, `emit_correct_clsAdd`). -/
def cls_add_spec_fwd (x y : BitVec 32) : Result (BitVec 32) :=
  .ok (if x == 0 then y + 1 else if x == 1 then y + 2 else y)

/-- Edge cases: both compute cases, the direct path, wrap-around, max. -/
def cls_add_spec_edges : List (BitVec 32 × BitVec 32) :=
  [(0, 0), (0, 5), (1, 5), (1, 0xFFFFFFFF), (0, 0xFFFFFFFF), (2, 7), (0xFFFFFFFF, 0xFFFFFFFF)]

/-- Prop-test entry: the class equation holds on every edge (this one is
    already the spec — the `uadd` if-chain is the whole body). -/
def cls_add_spec_check : Bool :=
  cls_add_spec_edges.all fun t =>
    (repr (cls_add_spec_fwd t.1 t.2)).pretty
      == (repr (((Except.ok (if t.1 == (0 : BitVec 32) then (t.2 + (1 : BitVec 32)) else if t.1 == (1 : BitVec 32) then (t.2 + (2 : BitVec 32)) else t.2)) : Result (BitVec 32)))).pretty
