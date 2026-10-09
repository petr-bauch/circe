-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

/-- C++ signature: `_ZNKSt6vectorIiSaIiEE12_M_check_lenEmPKc(t, n)` checks the grown length.
    Base body reference: the checked length with `maxDiff` clamp itself (cf. emitted `_ZNKSt6vectorIiSaIiEE12_M_check_lenEmPKc_fwd`,
    `stdVecCheckLenFwd`). -/
def _ZNKSt6vectorIiSaIiEE12_M_check_lenEmPKc_spec_fwd (len : Nat) (n : BitVec 64) : Result (BitVec 64) :=
  if (BitVec.ofNat 64 2305843009213693951 - BitVec.ofNat 64 len).ult n then
    .error .AssertFail
  else if (BitVec.ofNat 64 len +
      (if (BitVec.ofNat 64 len).ult n then n
        else BitVec.ofNat 64 len)).ult (BitVec.ofNat 64 len) then
    .ok (BitVec.ofNat 64 2305843009213693951)
  else if (BitVec.ofNat 64 2305843009213693951).ult (BitVec.ofNat 64 len +
      (if (BitVec.ofNat 64 len).ult n then n
        else BitVec.ofNat 64 len)) then
    .ok (BitVec.ofNat 64 2305843009213693951)
  else
    .ok (BitVec.ofNat 64 len +
      (if (BitVec.ofNat 64 len).ult n then n
        else BitVec.ofNat 64 len))

/-- Edge cases: exact, clamp, loud over-max. -/
def _ZNKSt6vectorIiSaIiEE12_M_check_lenEmPKc_spec_edges : List ((Nat × BitVec 64) × Result (BitVec 64)) :=
  [((0, 0), .ok 0),
   ((0, BitVec.ofNat 64 2305843009213693951), .ok (BitVec.ofNat 64 2305843009213693951)),
   ((0, BitVec.ofNat 64 2305843009213693952), .error .AssertFail)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _ZNKSt6vectorIiSaIiEE12_M_check_lenEmPKc_spec_check : Bool :=
  _ZNKSt6vectorIiSaIiEE12_M_check_lenEmPKc_spec_edges.all fun t =>
    (repr (_ZNKSt6vectorIiSaIiEE12_M_check_lenEmPKc_spec_fwd t.1.1 t.1.2)).pretty == (repr t.2).pretty
