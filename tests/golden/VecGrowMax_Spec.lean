-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZSt3maxImERKT_S2_S2_(a, b)` returns the larger word.
    Base body reference: the early-return-`if` itself (cf. emitted `_ZSt3maxImERKT_S2_S2__fwd`,
    `stdVecMaxFwd`). -/
def _ZSt3maxImERKT_S2_S2__spec_fwd (a b : BitVec 64) : BitVec 64 :=
  if a.ult b then b else a

/-- Edge cases: either side wins. -/
def _ZSt3maxImERKT_S2_S2__spec_edges : List ((BitVec 64 × BitVec 64) × BitVec 64) :=
  [((3, 5), 5), ((5, 3), 5), ((4, 4), 4)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZSt3maxImERKT_S2_S2__spec_check : Bool :=
  _ZSt3maxImERKT_S2_S2__spec_edges.all fun t =>
    (repr (_ZSt3maxImERKT_S2_S2__spec_fwd t.1.1 t.1.2)).pretty == (repr t.2).pretty
