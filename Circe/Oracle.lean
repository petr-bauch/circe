/-
Circe.Oracle — ownership-oracle verdict import (trusted).

Uniqueness verdicts come from Clang/CIR analysis (lifetime analysis +
CIR lifetime-checker prototype + LLVM `basicaa`), not from user proofs.
The translator trusts the oracle's `noalias` verdict per function;
`validate` rejects the function when the oracle is inconclusive.
Oracle verdict dumps are checked in under `tests/oracle/` (Phase 4;
currently a placeholder — see docs/PINS.md).
-/

/-- Per-function alias verdict from the oracle. -/
inductive Verdict : Type
  | noalias
  | mayAlias
  | unknown
  deriving DecidableEq, Repr

/-- One imported oracle fact: the verdict for a function. -/
structure OracleFact : Type where
  funcName : String
  verdict : Verdict
  deriving DecidableEq, Repr

/-- A function is translatable only on an explicit `noalias` verdict.
    Anything else is rejected loudly by `validate`. -/
def verdictAdmits (v : Verdict) : Bool :=
  match v with
  | .noalias => true
  | _ => false
