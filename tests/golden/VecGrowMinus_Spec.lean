-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same `Base` op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZN9__gnu_cxxmiIPiSt6vectorIiSaIiEEEENS_17__normal_iteratorIT_T0_E15difference_typeERKS8_SB_(a, b)` differences the offsets.
    Base body reference: bit-exact `s64diff` itself (cf. emitted `_ZN9__gnu_cxxmiIPiSt6vectorIiSaIiEEEENS_17__normal_iteratorIT_T0_E15difference_typeERKS8_SB__fwd`,
    `stdVecMinusFwd`). -/
def _ZN9__gnu_cxxmiIPiSt6vectorIiSaIiEEEENS_17__normal_iteratorIT_T0_E15difference_typeERKS8_SB__spec_fwd (a b : BitVec 64) : BitVec 64 :=
  a - b

/-- Edge cases: exact, wrap. -/
def _ZN9__gnu_cxxmiIPiSt6vectorIiSaIiEEEENS_17__normal_iteratorIT_T0_E15difference_typeERKS8_SB__spec_edges : List ((BitVec 64 × BitVec 64) × BitVec 64) :=
  [((10, 3), 7), ((3, 10), 18446744073709551609)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZN9__gnu_cxxmiIPiSt6vectorIiSaIiEEEENS_17__normal_iteratorIT_T0_E15difference_typeERKS8_SB__spec_check : Bool :=
  _ZN9__gnu_cxxmiIPiSt6vectorIiSaIiEEEENS_17__normal_iteratorIT_T0_E15difference_typeERKS8_SB__spec_edges.all fun t =>
    (repr (_ZN9__gnu_cxxmiIPiSt6vectorIiSaIiEEEENS_17__normal_iteratorIT_T0_E15difference_typeERKS8_SB__spec_fwd t.1.1 t.1.2)).pretty == (repr t.2).pretty
