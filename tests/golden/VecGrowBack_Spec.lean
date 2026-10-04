-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same `Base` op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZNSt6vectorIiSaIiEE4backEv(t)` returns the last offset.
    Base body reference: the `len - 1` offset itself (cf. emitted `_ZNSt6vectorIiSaIiEE4backEv_fwd`,
    `stdVecBackFwd`). -/
def _ZNSt6vectorIiSaIiEE4backEv_spec_fwd (len : Nat) : BitVec 64 :=
  BitVec.ofNat 64 len - 1

/-- Edge cases: singleton, longer. -/
def _ZNSt6vectorIiSaIiEE4backEv_spec_edges : List (Nat × BitVec 64) :=
  [(1, BitVec.ofNat 64 0), (3, BitVec.ofNat 64 2)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZNSt6vectorIiSaIiEE4backEv_spec_check : Bool :=
  _ZNSt6vectorIiSaIiEE4backEv_spec_edges.all fun t =>
    (repr (_ZNSt6vectorIiSaIiEE4backEv_spec_fwd t.1)).pretty == (repr t.2).pretty
