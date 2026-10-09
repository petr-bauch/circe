-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base
import Circe.Emit.VecGrow
import Circe.Emit.VecCompose

/-- C++ signature: `_ZNSt6vectorIiSaIiEE7reserveEm(t, n)` grows capacity to `n` (no-op when
    `capacity ≥ n`; `length_error` when `n` exceeds `max_size`).
    Base body reference: the guarded bind chain itself (cf. emitted `_ZNSt6vectorIiSaIiEE7reserveEm_fwd`,
    `stdVecReserveFwd`). -/
def _ZNSt6vectorIiSaIiEE7reserveEm_spec_fwd (b : Vec32) (len cap : Nat) (n : BitVec 64) : Result Value :=
  if stdVecMaxDiffBV.ult n then .error .AssertFail
  else if (BitVec.ofNat 64 cap).ult n then
    (stdVecAllocFwd n).bind fun alv =>
    (vecGrowOwned alv).bind fun (bNew, lenA, capA) =>
    (stdVecRelocFwd b len cap bNew lenA capA (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 len) (BitVec.ofNat 64 0)).bind fun rlv =>
    (vecGrowOwned rlv).bind fun (bR, _lenR, capR) =>
    (stdVecDeallocGuardFwd b len cap
      (BitVec.ofNat 64 cap)).bind fun _ =>
    .ok (.stdVecOwned bR ((BitVec.ofNat 64 len).toNat) capR)
  else .ok (.stdVecOwned b len cap)

/-- Edge cases: passthrough, fresh allocation, `max_size` failure (frozen by evaluating `stdVecReserveFwd`). -/
def _ZNSt6vectorIiSaIiEE7reserveEm_spec_edges : List ((Vec32 × Nat × Nat × BitVec 64) × Result Value) :=
  [(((⟨[], false⟩, 0, 10, BitVec.ofNat 64 10)), .ok (.stdVecOwned ⟨[], false⟩ 0 10)),
   (((⟨[], false⟩, 0, 0, BitVec.ofNat 64 1)), .ok (.stdVecOwned ⟨[(0 : BitVec 32)], false⟩ 0 1)),
   (((⟨[], false⟩, 0, 0, BitVec.ofNat 64 (stdVecMaxDiff + 1))), .error .AssertFail)]

/-- Mirror-agreement entry: the stub mirror agrees with the verified forward on every edge.
    TODO (user): strengthen to the gallery equations `stdVecReserve_correct_passthrough` /
    `stdVecReserve_correct_realloc` / `stdVecReserve_correct_throw` (proved by hand in `Circe.Specs`). -/
def _ZNSt6vectorIiSaIiEE7reserveEm_spec_check : Bool :=
  _ZNSt6vectorIiSaIiEE7reserveEm_spec_edges.all fun t =>
    match t with
    | ((b, len, cap, n), expected) =>
      (repr (_ZNSt6vectorIiSaIiEE7reserveEm_spec_fwd b len cap n)).pretty == (repr expected).pretty
