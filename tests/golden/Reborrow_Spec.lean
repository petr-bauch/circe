-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `void _Z14alias_reborrowRi(int &x)` (`*x += 1`, then `*x += 2`).
    Base body reference: sequential checked adds (cf. emitted `_Z14alias_reborrowRi_fwd`, `reborrowFwd`). -/
def _Z14alias_reborrowRi_spec_fwd (x : BitVec 32) : Result (BitVec 32) :=
  match checkedAddI32 x 1 with
  | .error e => .error e
  | .ok t => checkedAddI32 t 2

/-- Edge cases: zero, small increments, `nsw` overflow on either add, `INT32_MIN`, `-1`. -/
def _Z14alias_reborrowRi_spec_edges : List (BitVec 32 × Result (BitVec 32)) :=
  [(0, .ok 3), (10, .ok 13), (0xFFFFFFFF, .ok 2), (0x80000000, .ok 0x80000003), (0x7FFFFFFE, .error .Overflow), (0x7FFFFFFF, .error .Overflow)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z14alias_reborrowRi_spec_check : Bool :=
  _Z14alias_reborrowRi_spec_edges.all fun t =>
    (repr (_Z14alias_reborrowRi_spec_fwd t.1)).pretty == (repr t.2).pretty
