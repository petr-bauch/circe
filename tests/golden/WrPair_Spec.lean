-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C signature: `void wr_pair(int32_t *__restrict p, int32_t *__restrict q)` (`*p += 1`, `*q += 2`).
    Base body reference: independent checked adds (cf. emitted `wr_pair_fwd`, `wrPairFwd`). -/
def wr_pair_spec_fwd (p q : BitVec 32) : Result (BitVec 32 × BitVec 32) :=
  match checkedAddI32 p 1, checkedAddI32 q 2 with
  | .ok a, .ok b => .ok (a, b)
  | .error e, _ => .error e
  | _, .error e => .error e

/-- Edge cases: zero, small increments, `nsw` overflow on either add, `INT32_MIN`, `-1`. -/
def wr_pair_spec_edges : List (BitVec 32 × BitVec 32 × Result (BitVec 32 × BitVec 32)) :=
  [(0, 0, .ok (1, 2)), (10, 20, .ok (11, 22)), (0xFFFFFFFF, 0, .ok (0, 2)), (0, 0xFFFFFFFF, .ok (1, 1)), (0x7FFFFFFF, 0, .error .Overflow), (0, 0x7FFFFFFF, .error .Overflow), (0x80000000, 0x80000000, .ok (0x80000001, 0x80000002))]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def wr_pair_spec_check : Bool :=
  wr_pair_spec_edges.all fun t =>
    (repr (wr_pair_spec_fwd t.1 t.2.1)).pretty == (repr t.2.2).pretty
