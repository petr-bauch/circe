-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_Z8view_sumSt17basic_string_viewIcSt11char_traitsIcEE(s)` sums the viewed bytes (sign-extended).
    Base body reference: the checked-add fold itself (cf. emitted `_Z8view_sumSt17basic_string_viewIcSt11char_traitsIcEE_fwd`,
    `viewSumFwd`). -/
def _Z8view_sumSt17basic_string_viewIcSt11char_traitsIcEE_spec_fwd (l : List (BitVec 8)) : Result (BitVec 32) :=
  go l 0
where go : List (BitVec 8) → BitVec 32 → Result (BitVec 32)
  | [], acc => .ok acc
  | x :: xs, acc => do
      let a ← checkedAddI32 acc (x.signExtend 32)
      go xs a

/-- Edge cases: empty sum, small sums, sign-extended bytes (`nsw` overflow needs more bytes than an edge can list; it is proof-covered by `evalFuncFuel_viewSum`). -/
def _Z8view_sumSt17basic_string_viewIcSt11char_traitsIcEE_spec_edges : List (List (BitVec 8) × Result (BitVec 32)) :=
  [([], .ok 0), ([1, 2, 3], .ok 6), ([0xFF], .ok (-1)), ([0x7F, 0x7F], .ok 254)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z8view_sumSt17basic_string_viewIcSt11char_traitsIcEE_spec_check : Bool :=
  _Z8view_sumSt17basic_string_viewIcSt11char_traitsIcEE_spec_edges.all fun t =>
    (repr (_Z8view_sumSt17basic_string_viewIcSt11char_traitsIcEE_spec_fwd t.1)).pretty == (repr t.2).pretty
