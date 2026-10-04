-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same `Base` op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZN9__gnu_cxx13new_allocatorIiEC2Ev()` has no observable effect.
    Base body reference: void as `i32 0` (cf. emitted `_ZN9__gnu_cxx13new_allocatorIiEC2Ev_fwd`,
    `stdVecUnitFwd`). -/
def _ZN9__gnu_cxx13new_allocatorIiEC2Ev_spec_fwd : BitVec 32 :=
  BitVec.ofNat 32 0

/-- Edge cases: the single void value. -/
def _ZN9__gnu_cxx13new_allocatorIiEC2Ev_spec_edges : List (Unit × BitVec 32) :=
  [((), BitVec.ofNat 32 0)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZN9__gnu_cxx13new_allocatorIiEC2Ev_spec_check : Bool :=
  _ZN9__gnu_cxx13new_allocatorIiEC2Ev_spec_edges.all fun t =>
    (repr (_ZN9__gnu_cxx13new_allocatorIiEC2Ev_spec_fwd)).pretty == (repr t.2).pretty
