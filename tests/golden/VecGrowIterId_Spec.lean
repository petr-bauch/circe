-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same `Base` op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZN9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEC2ERKS1_(p)` returns the offset itself.
    Base body reference: the identity itself (cf. emitted `_ZN9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEC2ERKS1__fwd`,
    `stdVecIterIdFwd`). -/
def _ZN9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEC2ERKS1__spec_fwd (x : BitVec 64) : BitVec 64 :=
  x

/-- Edge cases: zero, nonzero. -/
def _ZN9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEC2ERKS1__spec_edges : List (BitVec 64 × BitVec 64) :=
  [(0, 0), (9, 9)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZN9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEC2ERKS1__spec_check : Bool :=
  _ZN9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEC2ERKS1__spec_edges.all fun t =>
    (repr (_ZN9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEC2ERKS1__spec_fwd t.1)).pretty == (repr t.2).pretty
