-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same `Base` op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZNKSt6vectorIiSaIiEE8capacityEv(t)` returns the storage-end offset.
    Base body reference: the `cap` offset itself (cf. emitted `_ZNKSt6vectorIiSaIiEE8capacityEv_fwd`,
    `stdVecGrowCapacityFwd`). -/
def _ZNKSt6vectorIiSaIiEE8capacityEv_spec_fwd (cap : Nat) : BitVec 64 :=
  BitVec.ofNat 64 cap

/-- Edge cases: empty, longer. -/
def _ZNKSt6vectorIiSaIiEE8capacityEv_spec_edges : List (Nat × BitVec 64) :=
  [(0, BitVec.ofNat 64 0), (3, BitVec.ofNat 64 3)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZNKSt6vectorIiSaIiEE8capacityEv_spec_check : Bool :=
  _ZNKSt6vectorIiSaIiEE8capacityEv_spec_edges.all fun t =>
    (repr (_ZNKSt6vectorIiSaIiEE8capacityEv_spec_fwd t.1)).pretty == (repr t.2).pretty
