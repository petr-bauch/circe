-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `void _Z16alias_reborrow34Ri(int &x)` (`*x += 3`, then `*x += 4`).
    Base body reference: sequential checked adds (cf. emitted `_Z16alias_reborrow34Ri_fwd`, `reborrow34Fwd`). -/
def _Z16alias_reborrow34Ri_spec_fwd (x : BitVec 32) : Result (BitVec 32) :=
  match checkedAddI32 x 3 with
  | .error e => .error e
  | .ok t => checkedAddI32 t 4

/-- Edge cases: zero, small increments, `nsw` overflow on either add. -/
def _Z16alias_reborrow34Ri_spec_edges : List (BitVec 32 × Result (BitVec 32)) :=
  [(0, .ok 7), (10, .ok 17), (0xFFFFFFFF, .ok 6), (0x7FFFFFFE, .error .Overflow), (0x7FFFFFFF, .error .Overflow)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z16alias_reborrow34Ri_spec_check : Bool :=
  _Z16alias_reborrow34Ri_spec_edges.all fun t =>
    (repr (_Z16alias_reborrow34Ri_spec_fwd t.1)).pretty == (repr t.2).pretty
