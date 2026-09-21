/-
Circe.Eval — loan-based, value-only ownership semantics (spec for
`emit_correct`).

Environments map variables to *values with loan/borrow bookkeeping*;
there is no heap and no addresses (Aeneas-style, see PLAN.md §6).
Phase 1: values, environments, and an `Eval` stub for the `add`/`incr`
fragment. Phase 2 adds the full `Eval` relation plus `docs/SEMANTICS.md`
and env/loan well-formedness lemmas.
-/
import Circe.Base
import Circe.CoreIR

/-- Runtime values: no addresses. C `int` → `BitVec 32` here (the
    `add`/`incr` fragment); Phase 2 generalizes widths and adds
    struct/array (`List`) values. -/
inductive Value : Type
  | i32 : BitVec 32 → Value
  | u32 : BitVec 32 → Value
  | b : Bool → Value
  | unit : Value
  deriving DecidableEq, Repr

/-- Evaluation environment: variables to values. Loan/borrow bookkeeping
    (region sets per Aeneas §4) is added in Phase 2. -/
abbrev Env : Type := List (String × Value)

/-- Function outcome: a returned value or fall-through. -/
inductive Outcome : Type
  | returned : Value → Outcome
  | fellThrough : Outcome
  deriving DecidableEq, Repr

/-- Loan-based evaluator stub. Phase 1 handles straight-line `add`-shaped
    bodies as `ok`; control flow and borrow tracking arrive in Phases 2–4
    with the `emit_correct` simulation proof. -/
def evalStmt : CStmt → Env → Result (Env × Outcome)
  | .skip, ρ => .ok (ρ, .fellThrough)
  | .seq _ _, ρ => .ok (ρ, .fellThrough)
  | .return_ _, ρ => .ok (ρ, .fellThrough)
  | _, ρ => .ok (ρ, .fellThrough)
