/-
Circe.Eval — loan-based, value-only ownership semantics (spec for
`emit_correct`).

Environments map variables to *values with loan/borrow bookkeeping*;
there is no heap and no addresses (Aeneas-style, see PLAN.md §6).
Phase 2: values (incl. struct/array), environments with well-formedness
lemmas, loan-state bookkeeping, and an expression evaluator over
`Circe.Base` checked ops. Statement-level `Eval` control flow and the
`emit_correct` simulation proof arrive in Phases 3–4.
-/
import Circe.Base
import Circe.CoreIR

/-- Runtime values: no addresses. C `int` → `BitVec 32`; arrays are pure
    length-paired lists of integers and structs are named field lists —
    never pointers (flat-value fragment; nested values arrive with heap
    support after v0.1). -/
inductive Value : Type
  | i32 : BitVec 32 → Value
  | u32 : BitVec 32 → Value
  | b : Bool → Value
  | unit : Value
  | arr32 : List (BitVec 32) → Value
  | structVal : String → List (String × BitVec 32) → Value
  deriving DecidableEq, Repr

/-- Evaluation environment: variables to values. Loan/borrow bookkeeping
    lives in the companion `LoanState` (Aeneas §4 regions, value-only). -/
abbrev Env : Type := List (String × Value)

/-- Function outcome: a returned value or fall-through. -/
inductive Outcome : Type
  | returned : Value → Outcome
  | fellThrough : Outcome
  deriving DecidableEq, Repr

/-! ## Environment operations + well-formedness -/

/-- Variable lookup (first binding wins). -/
def envLookup : Env → String → Option Value
  | [], _ => none
  | (k, v) :: rest, x => if x = k then some v else envLookup rest x

/-- Variable extension (shadowing allowed; well-formedness tracks it). -/
def envExtend (ρ : Env) (x : String) (v : Value) : Env := (x, v) :: ρ

/-- Keys of an environment. -/
def envKeys : Env → List String := List.map Prod.fst

/-- An environment is well-formed when no name is bound twice. -/
def EnvWF (ρ : Env) : Prop := (envKeys ρ).Nodup

theorem envLookup_empty (x : String) : envLookup [] x = none := rfl

theorem envExtend_hit (ρ : Env) (x : String) (v : Value) :
    envLookup (envExtend ρ x v) x = some v := by
  simp [envExtend, envLookup]

theorem envExtend_miss (ρ : Env) (x y : String) (v : Value) (h : x ≠ y) :
    envLookup (envExtend ρ y v) x = envLookup ρ x := by
  simp [envExtend, envLookup, h]

theorem envWF_empty : EnvWF [] := by
  simp [EnvWF, envKeys]

theorem envWF_extend_of_not_mem (ρ : Env) (x : String) (v : Value)
    (h : x ∉ envKeys ρ) (hwf : EnvWF ρ) : EnvWF (envExtend ρ x v) := by
  show List.Nodup (envKeys (envExtend ρ x v))
  have hkeys : envKeys (envExtend ρ x v) = x :: envKeys ρ := rfl
  rw [hkeys, List.nodup_cons]
  exact ⟨h, hwf⟩

theorem envWF_extend_mem_false (ρ : Env) (x : String) (v : Value)
    (hwf : EnvWF (envExtend ρ x v)) : x ∉ envKeys ρ := by
  have hkeys : envKeys (envExtend ρ x v) = x :: envKeys ρ := rfl
  have hwf' : List.Nodup (x :: envKeys ρ) := hkeys ▸ hwf
  rw [List.nodup_cons] at hwf'
  exact hwf'.1

/-! ## Loan state (region bookkeeping, value-only) -/

/-- Which variables are loaned out to which region, and which borrows are
    live. No addresses: this is pure capability bookkeeping. -/
structure LoanState : Type where
  loans : List (String × Nat)
  borrows : List (String × Nat)
  deriving DecidableEq, Repr

/-- Empty loan state (function entry: nothing borrowed). -/
def emptyLoans : LoanState := ⟨[], []⟩

/-- Loan `x` to region `r` (e.g. passing `&y` to a `mutBorrow` param). -/
def loanVar (s : LoanState) (x : String) (r : Nat) : LoanState :=
  ⟨(x, r) :: s.loans, (x, r) :: s.borrows⟩

/-- End region `r`: all its loans/borrows expire at once
    (backward-function call site, Aeneas §4.3). -/
def endRegion (s : LoanState) (r : Nat) : LoanState :=
  ⟨s.loans.filter (fun p => p.2 != r), s.borrows.filter (fun p => p.2 != r)⟩

/-- A loan state is well-formed when every loan has a matching live borrow. -/
def LoanWF (s : LoanState) : Prop :=
  ∀ x r, (x, r) ∈ s.loans → (x, r) ∈ s.borrows

theorem loanWF_empty : LoanWF emptyLoans := by
  intro x r h
  simp [emptyLoans] at h

theorem loanWF_loan (s : LoanState) (x : String) (r : Nat)
    (h : LoanWF s) : LoanWF (loanVar s x r) := by
  intro y r' hm
  simp [loanVar] at hm ⊢
  rcases hm with ⟨hx, hr⟩ | hmem
  · exact Or.inl ⟨hx, hr⟩
  · exact Or.inr (h y r' hmem)

/-- Ending a region preserves well-formedness (filtering both sides). -/
theorem loanWF_endRegion (s : LoanState) (r : Nat)
    (h : LoanWF s) : LoanWF (endRegion s r) := by
  intro x r' hm
  simp [endRegion] at hm ⊢
  obtain ⟨hmem, hne⟩ := hm
  exact ⟨h x r' hmem, hne⟩

/-! ## Expression evaluator (pure, over `Circe.Base`) -/

/-- Minimal C expressions for the Phase 2 fragment. -/
inductive CExpr : Type
  | const : Value → CExpr
  | var : String → CExpr
  | add : CExpr → CExpr → CExpr
  deriving DecidableEq, Repr

/-- Pure evaluator: `add` on `i32` goes through `checkedAddI32`
    (overflow → `.error .Overflow`); mismatched types are `AssertFail`;
    unbound variables are `Uninit`. -/
def evalExpr : CExpr → Env → Result Value
  | .const v, _ => .ok v
  | .var x, ρ =>
    match envLookup ρ x with
    | some v => .ok v
    | none => .error .Uninit
  | .add a b, ρ =>
    match evalExpr a ρ, evalExpr b ρ with
    | .ok (.i32 x), .ok (.i32 y) => (checkedAddI32 x y).map .i32
    | .ok _, .ok _ => .error .AssertFail
    | .error e, _ => .error e
    | _, .error e => .error e

theorem evalExpr_const (v : Value) (ρ : Env) :
    evalExpr (.const v) ρ = .ok v := rfl

theorem evalExpr_var_hit (ρ : Env) (x : String) (v : Value)
    (h : envLookup ρ x = some v) :
    evalExpr (.var x) ρ = .ok v := by
  simp [evalExpr, h]

theorem evalExpr_var_miss (ρ : Env) (x : String)
    (h : envLookup ρ x = none) :
    evalExpr (.var x) ρ = .error .Uninit := by
  simp [evalExpr, h]

theorem evalExpr_var_empty (x : String) :
    evalExpr (.var x) [] = .error .Uninit := by
  simp [evalExpr, envLookup]

/-- `add` on two `i32` constants forwards to `checkedAddI32`. -/
theorem evalExpr_add_const (x y : BitVec 32) (ρ : Env) :
    evalExpr (.add (.const (.i32 x)) (.const (.i32 y))) ρ =
      (checkedAddI32 x y).map .i32 := by
  simp [evalExpr]

/-- `add` type mismatches are rejected, never silently modeled. -/
theorem evalExpr_add_mismatch (ρ : Env) :
    evalExpr (.add (.const (.i32 0)) (.const (.b true))) ρ =
      .error .AssertFail := by
  simp [evalExpr]

/-! ## Statement evaluator (stub, control flow in Phases 3–4) -/

/-- Loan-based evaluator stub. Phase 2 handles values, environments, loans,
    and expressions above; statement control flow and borrow tracking arrive
    in Phases 3–4 with the `emit_correct` simulation proof. -/
def evalStmt : CStmt → Env → Result (Env × Outcome)
  | .skip, ρ => .ok (ρ, .fellThrough)
  | .seq _ _, ρ => .ok (ρ, .fellThrough)
  | .return_ _, ρ => .ok (ρ, .fellThrough)
  | _, ρ => .ok (ρ, .fellThrough)

/-- The stub never fails: failures surface via `evalExpr`, not control flow. -/
theorem evalStmt_is_ok (s : CStmt) (ρ : Env) :
    ∃ p, evalStmt s ρ = .ok p := by
  cases s <;> exact ⟨_, rfl⟩
