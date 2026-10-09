-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEmiEl(it, n)` steps the offset back.
    Base body reference: wrapping `usub` itself (cf. emitted `_ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEmiEl_fwd`,
    `stdVecMinusElFwd`). -/
def _ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEmiEl_spec_fwd (it n : BitVec 64) : BitVec 64 :=
  it - n

/-- Edge cases: exact, wrap. -/
def _ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEmiEl_spec_edges : List ((BitVec 64 × BitVec 64) × BitVec 64) :=
  [((10, 3), 7), ((3, 10), 18446744073709551609)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEmiEl_spec_check : Bool :=
  _ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEmiEl_spec_edges.all fun t =>
    (repr (_ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEmiEl_spec_fwd t.1.1 t.1.2)).pretty == (repr t.2).pretty
