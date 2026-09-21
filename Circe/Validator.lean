/-
Circe.Validator — the verified gate `validate : RawIR → Option Func`.

Rejects aliasing/out-of-subset inputs loudly with actionable codes
(`alias-reject`, `escape-reject`, `oob-possible`, `out-of-subset`).
Phase 1: rejection-code vocabulary plus a stub that accepts nothing
(closed gate). Phase 4 implements §4 enforcement + the oracle `noalias`
requirement with golden rejection-message tests.
-/
import Circe.CoreIR
import Circe.Parser
import Circe.Oracle

/-- Machine-readable rejection codes (see docs/CIR_SUBSET.md). -/
inductive RejectCode : Type
  | aliasReject
  | escapeReject
  | oobPossible
  | outOfSubset
  deriving DecidableEq, Repr

/-- A rejection: which function, which code, and a human message. -/
structure Rejection : Type where
  func : String
  code : RejectCode
  message : String
  deriving DecidableEq, Repr

/-- Validation result: either a `Func` ready for `Emit`, or a rejection. -/
abbrev Validation := Except Rejection Func

/-- Phase 1 stub: the gate is closed — every input is rejected as
    `outOfSubset` until per-op admission lands (Phases 3–4). This is the
    safe default: unverified text can never reach `Emit`. -/
def validate (_raw : RawFunc) (_oracle : OracleFact) : Validation :=
  .error { func := _raw.name, code := .outOfSubset
           , message := "Phase 1 skeleton: gate closed (no ops admitted yet)" }
