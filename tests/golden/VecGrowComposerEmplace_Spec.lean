-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same `Base` op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base
import Circe.Emit.VecGrow
import Circe.Emit.VecCompose

/-- C++ signature: `_ZNSt6vectorIiSaIiEE12emplace_backIJiEEERiDpOT_(t, x)` appends `x` (fast construct when
    `len ≠ cap`, slow realloc-insert at `pos = len` otherwise).
    Base body reference: the dispatch itself (cf. emitted `_ZNSt6vectorIiSaIiEE12emplace_backIJiEEERiDpOT__fwd`,
    `stdVecEmplaceBackFwd`). -/
def _ZNSt6vectorIiSaIiEE12emplace_backIJiEEERiDpOT__spec_fwd (b : Vec32) (len cap : Nat) (x : BitVec 32) : Result Value :=
  if len == cap then
    (stdVecCheckLenFwd len (BitVec.ofNat 64 1)).bind fun ckv =>
    (vecGrowU64 ckv).bind fun newlen =>
    (stdVecBeginFwd).bind fun bgv =>
    (vecGrowU64 bgv).bind fun bpos =>
    (stdVecMinusFwd (BitVec.ofNat 64 len) bpos).bind fun miv =>
    (vecGrowI64 miv).bind fun kd =>
    (stdVecAllocFwd newlen).bind fun alv =>
    (vecGrowOwned alv).bind fun (bNew, lenA, capA) =>
    (stdVecConstructFwd bNew lenA capA kd x).bind fun conv =>
    (vecGrowOwned conv).bind fun (bC, lenC, capC) =>
    (stdVecRelocFwd b len cap bC lenC capC (BitVec.ofNat 64 0) kd
      (BitVec.ofNat 64 0)).bind fun r1v =>
    (vecGrowOwned r1v).bind fun (bR1, lenR1, capR1) =>
    (stdVecRelocFwd b len cap bR1 lenR1 capR1 kd (BitVec.ofNat 64 len)
      (kd + BitVec.ofNat 64 1)).bind fun r2v =>
    (vecGrowOwned r2v).bind fun (bR2, _, capR2) =>
    (stdVecDeallocGuardFwd b len cap (BitVec.ofNat 64 cap)).bind fun _ =>
    .ok (.stdVecOwned bR2
      ((BitVec.ofNat 64 len + BitVec.ofNat 64 1).toNat) capR2)
  else (stdVecConstructFwd b len cap (BitVec.ofNat 64 len) x).bind fun conv =>
    (vecGrowOwned conv).bind fun (b', _, _) =>
    .ok (.stdVecOwned b' (len + 1) cap)

/-- Edge cases: fast append, slow realloc-insert, `check_len` failure (frozen by evaluating `stdVecEmplaceBackFwd`). -/
def _ZNSt6vectorIiSaIiEE12emplace_backIJiEEERiDpOT__spec_edges : List ((Vec32 × Nat × Nat × BitVec 32) × Result Value) :=
  [(((⟨[(0 : BitVec 32)], false⟩, 0, 1, 5)), .ok (.stdVecOwned ⟨[(5 : BitVec 32)], false⟩ 1 1)),
   (((⟨[], false⟩, 0, 0, 5)), .ok (.stdVecOwned ⟨[(5 : BitVec 32)], false⟩ 1 1)),
   (((⟨[], false⟩, stdVecMaxDiff, stdVecMaxDiff, 5)), .error .AssertFail)]

/-- Mirror-agreement entry: the stub mirror agrees with the verified forward on every edge. -/
def _ZNSt6vectorIiSaIiEE12emplace_backIJiEEERiDpOT__spec_check : Bool :=
  _ZNSt6vectorIiSaIiEE12emplace_backIJiEEERiDpOT__spec_edges.all fun t =>
    match t with
    | ((b, len, cap, x), expected) =>
      (repr (_ZNSt6vectorIiSaIiEE12emplace_backIJiEEERiDpOT__spec_fwd b len cap x)).pretty == (repr expected).pretty
