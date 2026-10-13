-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C signature: `void cond_pair(int32_t *__restrict p, int32_t *__restrict q, bool c)` (`*p += 1` under `c`, `*q += 2`).
    Base body reference: branch-masked checked add plus unconditional add (cf. emitted `cond_pair_fwd`, `condPairFwd`). -/
def cond_pair_spec_fwd (p q : BitVec 32) (c : Bool) : Result (BitVec 32 × BitVec 32) :=
  match c with
  | true =>
    match checkedAddI32 p 1 with
    | .error e => .error e
    | .ok a =>
      match checkedAddI32 q 2 with
      | .error e => .error e
      | .ok b => .ok (a, b)
  | false =>
    match checkedAddI32 q 2 with
    | .error e => .error e
    | .ok b => .ok (p, b)

/-- Edge cases: both legs, masking, `nsw` overflow on either add, `INT32_MIN`, `-1`. -/
def cond_pair_spec_edges : List (BitVec 32 × BitVec 32 × Bool × Result (BitVec 32 × BitVec 32)) :=
  [(0, 0, true, .ok (1, 2)), (10, 20, false, .ok (10, 22)), (0xFFFFFFFF, 0, true, .ok (0, 2)), (0, 0xFFFFFFFF, true, .ok (1, 1)), (0x7FFFFFFF, 0, true, .error .Overflow), (0x7FFFFFFF, 0, false, .ok (0x7FFFFFFF, 2)), (0, 0x7FFFFFFF, true, .error .Overflow), (0, 0x7FFFFFFF, false, .error .Overflow), (0x80000000, 0x80000000, true, .ok (0x80000001, 0x80000002))]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def cond_pair_spec_check : Bool :=
  cond_pair_spec_edges.all fun t =>
    (repr (cond_pair_spec_fwd t.1 t.2.1 t.2.2.1)).pretty == (repr t.2.2.2).pretty
