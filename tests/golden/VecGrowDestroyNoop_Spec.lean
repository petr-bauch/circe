-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same `Base` op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZSt8_DestroyIPiiEvT_S1_RSaIT0_E(a, b)` destroys nothing.
    Base body reference: void as `i32 0` (cf. emitted `_ZSt8_DestroyIPiiEvT_S1_RSaIT0_E_fwd`,
    `stdVecDestroyNoopFwd`). -/
def _ZSt8_DestroyIPiiEvT_S1_RSaIT0_E_spec_fwd (_a _b : BitVec 64) : BitVec 32 :=
  BitVec.ofNat 32 0

/-- Edge cases: the single void value. -/
def _ZSt8_DestroyIPiiEvT_S1_RSaIT0_E_spec_edges : List ((BitVec 64 × BitVec 64) × BitVec 32) :=
  [((0, 0), BitVec.ofNat 32 0)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZSt8_DestroyIPiiEvT_S1_RSaIT0_E_spec_check : Bool :=
  _ZSt8_DestroyIPiiEvT_S1_RSaIT0_E_spec_edges.all fun t =>
    (repr (_ZSt8_DestroyIPiiEvT_S1_RSaIT0_E_spec_fwd t.1.1 t.1.2)).pretty == (repr t.2).pretty
