-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZN9__gnu_cxx13new_allocatorIiE7destroyIiEEvPT_(p)` destroys nothing.
    Base body reference: void as `i32 0` (cf. emitted `_ZN9__gnu_cxx13new_allocatorIiE7destroyIiEEvPT__fwd`,
    `stdVecDestroyPtrFwd`). -/
def _ZN9__gnu_cxx13new_allocatorIiE7destroyIiEEvPT__spec_fwd (_p : BitVec 64) : BitVec 32 :=
  BitVec.ofNat 32 0

/-- Edge cases: the single void value. -/
def _ZN9__gnu_cxx13new_allocatorIiE7destroyIiEEvPT__spec_edges : List (BitVec 64 × BitVec 32) :=
  [(0, BitVec.ofNat 32 0)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZN9__gnu_cxx13new_allocatorIiE7destroyIiEEvPT__spec_check : Bool :=
  _ZN9__gnu_cxx13new_allocatorIiE7destroyIiEEvPT__spec_edges.all fun t =>
    (repr (_ZN9__gnu_cxx13new_allocatorIiE7destroyIiEEvPT__spec_fwd t.1)).pretty == (repr t.2).pretty
