-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base
import Circe.Emit.VecGrow
import Circe.Emit.VecCompose

/-- C++ signature: `_ZNSt6vectorIiSaIiEE17_M_realloc_insertIJiEEEvN9__gnu_cxx17__normal_iteratorIPiS1_EEDpOT_(t, pos, x)` reallocating insert (growth
    composition: `check_len` → `begin` → `mi` → `allocate` →
    `construct`-at-`k` → two `_S_relocate`s → the cap-counted
    `_M_deallocate` guard).
    Base body reference: the bind chain itself (cf. emitted `_ZNSt6vectorIiSaIiEE17_M_realloc_insertIJiEEEvN9__gnu_cxx17__normal_iteratorIPiS1_EEDpOT__fwd`,
    `stdVecGrowReallocFwd`). -/
def _ZNSt6vectorIiSaIiEE17_M_realloc_insertIJiEEEvN9__gnu_cxx17__normal_iteratorIPiS1_EEDpOT__spec_fwd (b : Vec32) (len cap : Nat) (pos : BitVec 64) (x : BitVec 32) : Result Value :=
  (stdVecCheckLenFwd len (BitVec.ofNat 64 1)).bind fun ckv =>
  (vecGrowU64 ckv).bind fun newlen =>
  (stdVecBeginFwd).bind fun bgv =>
  (vecGrowU64 bgv).bind fun bpos =>
  (stdVecMinusFwd pos bpos).bind fun miv =>
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

/-- Edge cases: empty insert ok, `check_len` failure (frozen by evaluating `stdVecGrowReallocFwd`). -/
def _ZNSt6vectorIiSaIiEE17_M_realloc_insertIJiEEEvN9__gnu_cxx17__normal_iteratorIPiS1_EEDpOT__spec_edges : List ((Vec32 × Nat × Nat × BitVec 64 × BitVec 32) × Result Value) :=
  [(((⟨[], false⟩, 0, 0, 0, 5)), .ok (.stdVecOwned ⟨[(5 : BitVec 32)], false⟩ 1 1)),
   (((⟨[], false⟩, stdVecMaxDiff, 0, 0, 5)), .error .AssertFail)]

/-- Mirror-agreement entry: the stub mirror agrees with the verified forward on every edge.
    TODO (user): strengthen to the gallery equations `stdVecGrowRealloc_correct_ok` /
    `stdVecGrowRealloc_correct_err_checklen` (proved by hand in `Circe.Specs`). -/
def _ZNSt6vectorIiSaIiEE17_M_realloc_insertIJiEEEvN9__gnu_cxx17__normal_iteratorIPiS1_EEDpOT__spec_check : Bool :=
  _ZNSt6vectorIiSaIiEE17_M_realloc_insertIJiEEEvN9__gnu_cxx17__normal_iteratorIPiS1_EEDpOT__spec_edges.all fun t =>
    match t with
    | ((b, len, cap, pos, x), expected) =>
      (repr (_ZNSt6vectorIiSaIiEE17_M_realloc_insertIJiEEEvN9__gnu_cxx17__normal_iteratorIPiS1_EEDpOT__spec_fwd b len cap pos x)).pretty == (repr expected).pretty
