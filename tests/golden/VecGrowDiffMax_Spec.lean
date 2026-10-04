-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same `Base` op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZNK9__gnu_cxx13new_allocatorIiE11_M_max_sizeEv()` returns the max size.
    Base body reference: the `diffmax` const itself (cf. emitted `_ZNK9__gnu_cxx13new_allocatorIiE11_M_max_sizeEv_fwd`,
    `stdVecDiffMaxFwd`). -/
def _ZNK9__gnu_cxx13new_allocatorIiE11_M_max_sizeEv_spec_fwd : BitVec 64 :=
  BitVec.ofNat 64 2305843009213693951

/-- Edge cases: the single const. -/
def _ZNK9__gnu_cxx13new_allocatorIiE11_M_max_sizeEv_spec_edges : List (Unit × BitVec 64) :=
  [((), BitVec.ofNat 64 2305843009213693951)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZNK9__gnu_cxx13new_allocatorIiE11_M_max_sizeEv_spec_check : Bool :=
  _ZNK9__gnu_cxx13new_allocatorIiE11_M_max_sizeEv_spec_edges.all fun t =>
    (repr (_ZNK9__gnu_cxx13new_allocatorIiE11_M_max_sizeEv_spec_fwd)).pretty == (repr t.2).pretty
