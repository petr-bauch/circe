-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `void _Z10alias_condRiS_b(int &p, int &q, bool c)` (`if (c) *p += 1; *q += 2` over caller-aliased cells).
    Base body reference: branch-ordered checked adds with the `q` re-read (cf. emitted `_Z10alias_condRiS_b_spec`). -/
def _Z10alias_condRiS_b_spec_fwd (p q : BitVec 32) (c aliased : Bool) : Result (BitVec 32 × BitVec 32) :=
  match c with
  | true =>
    match checkedAddI32 p 1 with
    | .error e => .error e
    | .ok a =>
      let q' := if aliased then a else q
      match checkedAddI32 q' 2 with
      | .error e => .error e
      | .ok b => .ok (if aliased then (b, b) else (a, b))
  | false =>
    let q' := if aliased then p else q
    match checkedAddI32 q' 2 with
    | .error e => .error e
    | .ok b => .ok (if aliased then (b, b) else (p, b))

/-- Edge cases: both verdicts under both branches, masking, `nsw` overflow on either add. -/
def _Z10alias_condRiS_b_spec_edges : List (BitVec 32 × BitVec 32 × Bool × Bool × Result (BitVec 32 × BitVec 32)) :=
  [(10, 20, true, false, .ok (11, 22)), (10, 20, false, false, .ok (10, 22)), (10, 10, true, true, .ok (13, 13)), (10, 10, false, true, .ok (12, 12)), (0, 0, true, true, .ok (3, 3)), (0x7FFFFFFF, 0, true, false, .error .Overflow), (0x7FFFFFFF, 0, false, false, .ok (0x7FFFFFFF, 2)), (0, 0x7FFFFFFF, true, false, .error .Overflow), (0x7FFFFFFF, 0x7FFFFFFF, true, true, .error .Overflow)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z10alias_condRiS_b_spec_check : Bool :=
  _Z10alias_condRiS_b_spec_edges.all fun t =>
    (repr (_Z10alias_condRiS_b_spec_fwd t.1 t.2.1 t.2.2.1 t.2.2.2.1)).pretty == (repr t.2.2.2.2).pretty
