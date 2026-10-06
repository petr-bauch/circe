-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same `Base` op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZNKSt17basic_string_viewIcSt11char_traitsIcEE5beginEv(s)` loads the `_M_str` base pointer.
    Base body reference: the erased `0` offset (cf. emitted `_ZNKSt17basic_string_viewIcSt11char_traitsIcEE5beginEv_fwd`,
    `viewBeginFwd`). -/
def _ZNKSt17basic_string_viewIcSt11char_traitsIcEE5beginEv_spec_fwd : BitVec 64 :=
  BitVec.ofNat 64 0

/-- Edge cases: the offset is definitionally `0`. -/
def _ZNKSt17basic_string_viewIcSt11char_traitsIcEE5beginEv_spec_edges : List (BitVec 64) :=
  [0]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZNKSt17basic_string_viewIcSt11char_traitsIcEE5beginEv_spec_check : Bool :=
  _ZNKSt17basic_string_viewIcSt11char_traitsIcEE5beginEv_spec_edges.all fun t =>
    (repr _ZNKSt17basic_string_viewIcSt11char_traitsIcEE5beginEv_spec_fwd).pretty == (repr t).pretty
