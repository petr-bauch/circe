-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZNKSt4spanIKiLm18446744073709551615EE4sizeEv(s)` delegates to the `_M_extent` length body.
    Base body reference: the reified length itself (cf. emitted `_ZNKSt4spanIKiLm18446744073709551615EE4sizeEv_fwd`,
    `spanSizeFwd_is_call`). -/
def _ZNKSt4spanIKiLm18446744073709551615EE4sizeEv_spec_fwd (l : List (BitVec 32)) : BitVec 64 :=
  BitVec.ofNat 64 l.length

/-- Edge cases: empty, singleton, longer views. -/
def _ZNKSt4spanIKiLm18446744073709551615EE4sizeEv_spec_edges : List (List (BitVec 32) × BitVec 64) :=
  [([], 0), ([7], 1), ([1, 2, 3], 3)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZNKSt4spanIKiLm18446744073709551615EE4sizeEv_spec_check : Bool :=
  _ZNKSt4spanIKiLm18446744073709551615EE4sizeEv_spec_edges.all fun t =>
    (repr (_ZNKSt4spanIKiLm18446744073709551615EE4sizeEv_spec_fwd t.1)).pretty == (repr t.2).pretty
