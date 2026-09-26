/-
Circe.Eval — loan-based, value-only ownership semantics (spec for
`emit_correct`).

Environments map variables to *values with loan/borrow bookkeeping*;
there is no heap and no addresses (Aeneas-style, see PLAN.md §6).
Phase 4: `evalExpr` covers `lit`/`var`/`add` (signed `nsw`-checked) plus
`uadd` (wrapping unsigned), `ult` (unsigned comparison), and `idx`
(bounded indexing, `OOB` on violation); `evalStmt` covers the full
loop-free fragment (`skip`/`seq`/`let_`/`assign`/`if_`/`return_`) plus
fuel-bounded `while_` (`EVAL_FUEL`; exhaustion is `AssertFail`, and
`validate` admits only bounded loops). `call` stays a stub (Phase 5+).
`bindArgs`/`evalFunc` give whole-function semantics; `evalFuncFuel`
exposes the fuel for induction (loop proofs generalize it).
-/
import Circe.Base
import Circe.CoreIR

/-- Runtime values: no addresses. C `int` → `BitVec 32`; arrays are pure
    length-paired lists of integers and structs are named field lists —
    never pointers (flat-value fragment; uniquely-owned heap blocks are
    `vecVal` values with an affine token, Phase 7). -/
inductive Value : Type
  | i32 : BitVec 32 → Value
  | u32 : BitVec 32 → Value
  | b : Bool → Value
  | unit : Value
  | arr32 : List (BitVec 32) → Value
  | vecVal : Vec32 → Value
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

/-- Point update for `assign`: replace the first binding of `x`, or `none`
    if `x` is unbound (loud `Uninit` at the statement level, never silent). -/
def envUpdate : Env → String → Value → Option Env
  | [], _, _ => none
  | (k, v) :: rest, x, v' =>
    if x = k then some ((k, v') :: rest)
    else
      match envUpdate rest x v' with
      | none => none
      | some rest' => some ((k, v) :: rest')

theorem envUpdate_empty (x : String) (v : Value) :
    envUpdate [] x v = none := rfl

theorem envUpdate_hit (k : String) (v v' : Value) (rest : Env) :
    envUpdate ((k, v) :: rest) k v' = some ((k, v') :: rest) := by
  simp [envUpdate]

theorem envUpdate_miss (k x : String) (v v' : Value) (rest : Env)
    (h : x ≠ k) :
    envUpdate ((k, v) :: rest) x v' =
      match envUpdate rest x v' with
      | none => none
      | some rest' => some ((k, v) :: rest') := by
  simp [envUpdate, h]

/-- Lookup after a hitting update sees the new value. -/
theorem envLookup_update_hit (ρ : Env) (x : String) (v : Value)
    (ρ' : Env) (h : envUpdate ρ x v = some ρ') :
    envLookup ρ' x = some v := by
  induction ρ generalizing ρ' with
  | nil => simp [envUpdate] at h
  | cons kv rest ih =>
    obtain ⟨k, w⟩ := kv
    by_cases heq : x = k
    · subst heq
      rw [envUpdate_hit] at h
      cases h
      simp [envLookup]
    · rw [envUpdate_miss _ _ _ _ _ heq] at h
      match he : envUpdate rest x v with
      | none => simp [he] at h
      | some rest' =>
        simp only [he] at h
        cases h
        by_cases hx : x = k
        · exact absurd hx heq
        · simp [envLookup, hx, ih _ he]

/-- Lookup of any *other* variable is unaffected by an update. -/
theorem envLookup_update_miss (ρ : Env) (x y : String) (v : Value)
    (ρ' : Env) (hne : x ≠ y) (h : envUpdate ρ y v = some ρ') :
    envLookup ρ' x = envLookup ρ x := by
  induction ρ generalizing ρ' with
  | nil => simp [envUpdate] at h
  | cons kv rest ih =>
    obtain ⟨k, w⟩ := kv
    by_cases heq : y = k
    · subst heq
      rw [envUpdate_hit] at h
      cases h
      simp [envLookup, hne]
    · rw [envUpdate_miss _ _ _ _ _ heq] at h
      match he : envUpdate rest y v with
      | none => simp [he] at h
      | some rest' =>
        simp only [he] at h
        cases h
        by_cases hx : x = k
        · simp [envLookup, hx]
        · simp [envLookup, hx, ih _ he]

/-- Update preserves the key set, hence well-formedness. -/
theorem envKeys_update (ρ : Env) (x : String) (v : Value) (ρ' : Env)
    (h : envUpdate ρ x v = some ρ') : envKeys ρ' = envKeys ρ := by
  induction ρ generalizing ρ' with
  | nil => simp [envUpdate] at h
  | cons kv rest ih =>
    obtain ⟨k, w⟩ := kv
    by_cases heq : x = k
    · subst heq
      rw [envUpdate_hit] at h
      cases h
      rfl
    · rw [envUpdate_miss _ _ _ _ _ heq] at h
      match he : envUpdate rest x v with
      | none => simp [he] at h
      | some rest' =>
        simp only [he] at h
        cases h
        show (k :: envKeys rest') = (k :: envKeys rest)
        rw [ih _ he]

theorem envWF_update (ρ : Env) (x : String) (v : Value) (ρ' : Env)
    (hwf : EnvWF ρ) (h : envUpdate ρ x v = some ρ') : EnvWF ρ' := by
  show List.Nodup (envKeys ρ')
  rw [envKeys_update ρ x v ρ' h]
  exact hwf

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

/-- Literal denotation: no addresses, just values. -/
def litVal : CLit → Value
  | .i32 v => .i32 v
  | .u32 v => .u32 v
  | .b v => .b v

/-- Pure evaluator:
    - `add` on `i32` goes through `checkedAddI32` (overflow → `Overflow`);
    - `uadd` on `u32` wraps (plain `cir.add`; never fails);
    - `ult` on `u32` is unsigned comparison;
    - `idx a i` looks up `arr32` array `a` at `u32` index `i`
      (`OOB` off the end, mirroring `bget`);
    mismatched types are `AssertFail`; unbound variables are `Uninit`. -/
def evalExpr : CExpr → Env → Result Value
  | .lit l, _ => .ok (litVal l)
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
  | .uadd a b, ρ =>
    match evalExpr a ρ, evalExpr b ρ with
    | .ok (.u32 x), .ok (.u32 y) => .ok (.u32 (x + y))
    | .ok _, .ok _ => .error .AssertFail
    | .error e, _ => .error e
    | _, .error e => .error e
  | .ult a b, ρ =>
    match evalExpr a ρ, evalExpr b ρ with
    | .ok (.u32 x), .ok (.u32 y) => .ok (.b (x.ult y))
    | .ok _, .ok _ => .error .AssertFail
    | .error e, _ => .error e
    | _, .error e => .error e
  | .idx arr ie, ρ =>
    match envLookup ρ arr with
    | none => .error .Uninit
    | some (.arr32 l) =>
      match evalExpr ie ρ with
      | .error e => .error e
      | .ok (.u32 i) =>
        match l[i.toNat]? with
        | some x => .ok (.u32 x)
        | none => .error .OOB
      | .ok _ => .error .AssertFail
    | some _ => .error .AssertFail
  | .vnew se, ρ =>
    match evalExpr se ρ with
    | .error e => .error e
    | .ok (.u32 n) =>
      match vecNew n.toNat with
      | .error e => .error e
      | .ok v => .ok (.vecVal v)
    | .ok _ => .error .AssertFail
  | .vget arr ie, ρ =>
    match envLookup ρ arr with
    | none => .error .Uninit
    | some (.vecVal v) =>
      match evalExpr ie ρ with
      | .error e => .error e
      | .ok (.u32 i) =>
        match vecGet v i.toNat with
        | .error e => .error e
        | .ok x => .ok (.u32 x)
      | .ok _ => .error .AssertFail
    | some _ => .error .AssertFail

theorem evalExpr_lit (l : CLit) (ρ : Env) :
    evalExpr (.lit l) ρ = .ok (litVal l) := rfl

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

/-- `add` on two `i32` literals forwards to `checkedAddI32`. -/
theorem evalExpr_add_lit (x y : BitVec 32) (ρ : Env) :
    evalExpr (.add (.lit (.i32 x)) (.lit (.i32 y))) ρ =
      (checkedAddI32 x y).map .i32 := by
  simp [evalExpr, litVal]

/-- `add` type mismatches are rejected, never silently modeled. -/
theorem evalExpr_add_mismatch (ρ : Env) :
    evalExpr (.add (.lit (.i32 0)) (.lit (.b true))) ρ =
      .error .AssertFail := by
  simp [evalExpr, litVal]

/-- `uadd` on two `u32` literals wraps. -/
theorem evalExpr_uadd_lit (x y : BitVec 32) (ρ : Env) :
    evalExpr (.uadd (.lit (.u32 x)) (.lit (.u32 y))) ρ =
      .ok (.u32 (x + y)) := by
  simp [evalExpr, litVal]

/-- `uadd` type mismatches are rejected. -/
theorem evalExpr_uadd_mismatch (ρ : Env) :
    evalExpr (.uadd (.lit (.u32 0)) (.lit (.b true))) ρ =
      .error .AssertFail := by
  simp [evalExpr, litVal]

/-- `ult` on two `u32` literals is unsigned comparison. -/
theorem evalExpr_ult_lit (x y : BitVec 32) (ρ : Env) :
    evalExpr (.ult (.lit (.u32 x)) (.lit (.u32 y))) ρ =
      .ok (.b (x.ult y)) := by
  simp [evalExpr, litVal]

/-- `ult` type mismatches are rejected. -/
theorem evalExpr_ult_mismatch (ρ : Env) :
    evalExpr (.ult (.lit (.i32 0)) (.lit (.i32 1))) ρ =
      .error .AssertFail := by
  simp [evalExpr, litVal]

/-- In-bounds indexing succeeds. -/
theorem evalExpr_idx_hit (arr : String) (l : List (BitVec 32)) (i : BitVec 32)
    (ρ : Env) (x : BitVec 32)
    (harr : envLookup ρ arr = some (.arr32 l))
    (hidx : l[i.toNat]? = some x) :
    evalExpr (.idx arr (.lit (.u32 i))) ρ = .ok (.u32 x) := by
  simp [evalExpr, litVal, harr, hidx]

/-- Out-of-bounds indexing reports `OOB`. -/
theorem evalExpr_idx_oob (arr : String) (l : List (BitVec 32)) (i : BitVec 32)
    (ρ : Env)
    (harr : envLookup ρ arr = some (.arr32 l))
    (hidx : l[i.toNat]? = none) :
    evalExpr (.idx arr (.lit (.u32 i))) ρ = .error .OOB := by
  simp [evalExpr, litVal, harr, hidx]

/-- Indexing a non-array is rejected, never silently modeled. -/
theorem evalExpr_idx_notarray (arr : String) (v : BitVec 32) (i : BitVec 32)
    (ρ : Env)
    (harr : envLookup ρ arr = some (.i32 v)) :
    evalExpr (.idx arr (.lit (.u32 i))) ρ = .error .AssertFail := by
  simp [evalExpr, harr]

/-- `vnew` on a `u32` size allocates a zeroed live block. -/
theorem evalExpr_vnew_lit (n : BitVec 32) (ρ : Env) :
    evalExpr (.vnew (.lit (.u32 n))) ρ =
      .ok (.vecVal ⟨List.replicate n.toNat 0, false⟩) := by
  simp [evalExpr, litVal, vecNew]

/-- `vnew` on a non-`u32` size is rejected. -/
theorem evalExpr_vnew_mismatch (ρ : Env) :
    evalExpr (.vnew (.lit (.i32 0))) ρ = .error .AssertFail := by
  simp [evalExpr, litVal]

/-- In-bounds heap read succeeds. -/
theorem evalExpr_vget_hit (arr : String) (v : Vec32) (i : BitVec 32)
    (ρ : Env) (x : BitVec 32)
    (harr : envLookup ρ arr = some (.vecVal v))
    (hget : vecGet v i.toNat = .ok x) :
    evalExpr (.vget arr (.lit (.u32 i))) ρ = .ok (.u32 x) := by
  simp [evalExpr, litVal, harr, hget]

/-- Heap read errors (OOB/use-after-free) propagate. -/
theorem evalExpr_vget_err (arr : String) (v : Vec32) (i : BitVec 32)
    (ρ : Env) (e : Panic)
    (harr : envLookup ρ arr = some (.vecVal v))
    (hget : vecGet v i.toNat = .error e) :
    evalExpr (.vget arr (.lit (.u32 i))) ρ = .error e := by
  simp [evalExpr, litVal, harr, hget]

/-- Reading a non-block is rejected, never silently modeled. -/
theorem evalExpr_vget_notvec (arr : String) (v : BitVec 32) (i : BitVec 32)
    (ρ : Env)
    (harr : envLookup ρ arr = some (.i32 v)) :
    evalExpr (.vget arr (.lit (.u32 i))) ρ = .error .AssertFail := by
  simp [evalExpr, harr]

/-! ## Statement evaluator (fuel-bounded `while_`) -/

/-- Default fuel: v0.1 loops must terminate within this many iterations.
    Exhaustion reports `AssertFail` (incompleteness, not unsoundness:
    `validate` admits only bounded loops; see `docs/OWNERSHIP.md`). -/
def EVAL_FUEL : Nat := 4096

/-- Loop-free statement skeleton parameterized by the `while_` handler.
    Structural on `s`, so all equation lemmas and kernel reduction work;
    fuel lives only in `evalStmtFuel` below. -/
def evalStmtWith (wh : CExpr → CStmt → Env → Result (Env × Outcome)) :
    CStmt → Env → Result (Env × Outcome)
  | .skip, ρ => .ok (ρ, .fellThrough)
  | .seq a b, ρ =>
    match evalStmtWith wh a ρ with
    | .error e => .error e
    | .ok (ρ', .returned v) => .ok (ρ', .returned v)
    | .ok (ρ', .fellThrough) => evalStmtWith wh b ρ'
  | .let_ x _ e, ρ =>
    match evalExpr e ρ with
    | .error err => .error err
    | .ok v => .ok (envExtend ρ x v, .fellThrough)
  | .assign x e, ρ =>
    match evalExpr e ρ with
    | .error err => .error err
    | .ok v =>
      match envUpdate ρ x v with
      | none => .error .Uninit
      | some ρ' => .ok (ρ', .fellThrough)
  | .vset x ie ve, ρ =>
    match evalExpr ie ρ, evalExpr ve ρ with
    | .ok (.u32 i), .ok (.u32 xv) =>
      match envLookup ρ x with
      | none => .error .Uninit
      | some (.vecVal b) =>
        match vecSet b i.toNat xv with
        | .error e => .error e
        | .ok b' =>
          match envUpdate ρ x (.vecVal b') with
          | none => .error .Uninit
          | some ρ' => .ok (ρ', .fellThrough)
      | some _ => .error .AssertFail
    | .ok _, .ok _ => .error .AssertFail
    | .error e, _ => .error e
    | _, .error e => .error e
  | .vfree x, ρ =>
    match envLookup ρ x with
    | none => .error .Uninit
    | some (.vecVal b) =>
      match vecFree b with
      | .error e => .error e
      | .ok b' =>
        match envUpdate ρ x (.vecVal b') with
        | none => .error .Uninit
        | some ρ' => .ok (ρ', .fellThrough)
    | some _ => .error .AssertFail
  | .if_ c t e, ρ =>
    match evalExpr c ρ with
    | .error err => .error err
    | .ok (.b true) => evalStmtWith wh t ρ
    | .ok (.b false) => evalStmtWith wh e ρ
    | .ok _ => .error .AssertFail
  | .while_ c b, ρ => wh c b ρ
  | .call _ _, ρ => .ok (ρ, .fellThrough)
  | .return_ e, ρ =>
    match evalExpr e ρ with
    | .error err => .error err
    | .ok v => .ok (ρ, .returned v)

/-- Zero-fuel `while_` handler, named (not inline) so that proofs can
    state rewrite rules about the unfolded loop form: every `match` gets a
    per-definition auxiliary (`*.match_1`), so copies of a handler never
    match syntactically — only the shared named head does. -/
def evalStmtZeroHandler : CExpr → CStmt → Env → Result (Env × Outcome) :=
  fun c _ ρ =>
    match evalExpr c ρ with
    | .ok (.b false) => .ok (ρ, .fellThrough)
    | .ok _ => .error .AssertFail
    | .error err => .error err

/-- Zero fuel: no further iterations allowed, but a loop whose condition
    is already false still exits cleanly (fuel counts iterations, not
    condition checks). Errors always propagate. -/
def evalStmtZero : CStmt → Env → Result (Env × Outcome) :=
  evalStmtWith evalStmtZeroHandler

/-- Positive-fuel `while_` handler, named for the same reason. Takes the
    predecessor-fuel evaluator as a parameter (no mutual recursion, so
    `evalStmtFuel` stays structural on fuel). -/
def evalStmtSuccHandler (rec : CStmt → Env → Result (Env × Outcome)) :
    CExpr → CStmt → Env → Result (Env × Outcome) :=
  fun c b ρ =>
    match evalExpr c ρ with
    | .error err => .error err
    | .ok (.b false) => .ok (ρ, .fellThrough)
    | .ok (.b true) =>
      match rec b ρ with
      | .error e => .error e
      | .ok (ρ', .returned v) => .ok (ρ', .returned v)
      | .ok (ρ', .fellThrough) => rec (.while_ c b) ρ'
    | .ok _ => .error .AssertFail

/-- Fuel-bounded statement evaluator. Only `while_` consumes fuel
    (one per iteration); all other statements thread it through.
    Structural on `fuel`, so `cases fuel` + `simp` reasoning works and
    `lake build` equation lemmas fire on concrete `EVAL_FUEL`. -/
def evalStmtFuel : Nat → CStmt → Env → Result (Env × Outcome)
  | 0, s, ρ => evalStmtZero s ρ
  | f + 1, s, ρ => evalStmtWith (evalStmtSuccHandler (evalStmtFuel f)) s ρ

/-- The top-level evaluator fixes the default fuel. -/
def evalStmt (s : CStmt) (ρ : Env) : Result (Env × Outcome) :=
  evalStmtFuel EVAL_FUEL s ρ

theorem evalStmt_skip (ρ : Env) :
    evalStmt .skip ρ = .ok (ρ, .fellThrough) := rfl

/-- `return_` at any fuel (loop proofs generalize the fuel). -/
theorem evalStmtFuel_return (f : Nat) (e : CExpr) (ρ : Env) (v : Value)
    (h : evalExpr e ρ = .ok v) :
    evalStmtFuel f (.return_ e) ρ = .ok (ρ, .returned v) := by
  cases f <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, h]

theorem evalStmt_return (e : CExpr) (ρ : Env) (v : Value)
    (h : evalExpr e ρ = .ok v) :
    evalStmt (.return_ e) ρ = .ok (ρ, .returned v) :=
  evalStmtFuel_return EVAL_FUEL e ρ v h

theorem evalStmtFuel_return_err (f : Nat) (e : CExpr) (ρ : Env) (err : Panic)
    (h : evalExpr e ρ = .error err) :
    evalStmtFuel f (.return_ e) ρ = .error err := by
  cases f <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, h]

theorem evalStmt_return_err (e : CExpr) (ρ : Env) (err : Panic)
    (h : evalExpr e ρ = .error err) :
    evalStmt (.return_ e) ρ = .error err :=
  evalStmtFuel_return_err EVAL_FUEL e ρ err h

/-- `if_` on `true` takes the branch (any fuel). -/
theorem evalStmtFuel_if_true (f : Nat) (c : CExpr) (t e : CStmt) (ρ : Env)
    (h : evalExpr c ρ = .ok (.b true)) :
    evalStmtFuel f (.if_ c t e) ρ = evalStmtFuel f t ρ := by
  cases f <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, h]

/-- `if_` on `false` takes the else-branch (any fuel). -/
theorem evalStmtFuel_if_false (f : Nat) (c : CExpr) (t e : CStmt) (ρ : Env)
    (h : evalExpr c ρ = .ok (.b false)) :
    evalStmtFuel f (.if_ c t e) ρ = evalStmtFuel f e ρ := by
  cases f <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, h]

/-- `if_` on a non-boolean is rejected. -/
theorem evalStmtFuel_if_nobool (f : Nat) (c : CExpr) (t e : CStmt) (ρ : Env)
    (v : Value) (hv : ∀ b : Bool, v ≠ .b b)
    (h : evalExpr c ρ = .ok v) :
    evalStmtFuel f (.if_ c t e) ρ = .error .AssertFail := by
  cases f <;>
    simp [evalStmtFuel, evalStmtZero, evalStmtWith, h] <;>
    (cases v <;> simp_all)

/-- `assign` updates the first binding (any fuel). -/
theorem evalStmtFuel_assign (f : Nat) (x : String) (e : CExpr) (ρ : Env)
    (v : Value) (ρ' : Env)
    (h : evalExpr e ρ = .ok v) (hu : envUpdate ρ x v = some ρ') :
    evalStmtFuel f (.assign x e) ρ = .ok (ρ', .fellThrough) := by
  cases f <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, h, hu]

/-- `assign` to an unbound variable is `Uninit`. -/
theorem evalStmtFuel_assign_unbound (f : Nat) (x : String) (e : CExpr)
    (ρ : Env) (v : Value)
    (h : evalExpr e ρ = .ok v) (hu : envUpdate ρ x v = none) :
    evalStmtFuel f (.assign x e) ρ = .error .Uninit := by
  cases f <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, h, hu]

/-- `vset` stores through a live block and updates the binding (any fuel). -/
theorem evalStmtFuel_vset (f : Nat) (x : String) (ie ve : CExpr) (ρ : Env)
    (i xv : BitVec 32) (b b' : Vec32) (ρ' : Env)
    (hi : evalExpr ie ρ = .ok (.u32 i))
    (hv : evalExpr ve ρ = .ok (.u32 xv))
    (harr : envLookup ρ x = some (.vecVal b))
    (hset : vecSet b i.toNat xv = .ok b')
    (hu : envUpdate ρ x (.vecVal b') = some ρ') :
    evalStmtFuel f (.vset x ie ve) ρ = .ok (ρ', .fellThrough) := by
  cases f <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, hi, hv, harr, hset, hu]

/-- `vset` errors (OOB/use-after-free) propagate (any fuel). -/
theorem evalStmtFuel_vset_err (f : Nat) (x : String) (ie ve : CExpr)
    (ρ : Env) (i xv : BitVec 32) (b : Vec32) (e : Panic)
    (hi : evalExpr ie ρ = .ok (.u32 i))
    (hv : evalExpr ve ρ = .ok (.u32 xv))
    (harr : envLookup ρ x = some (.vecVal b))
    (hset : vecSet b i.toNat xv = .error e) :
    evalStmtFuel f (.vset x ie ve) ρ = .error e := by
  cases f <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, hi, hv, harr, hset]

/-- `vfree` consumes the token and updates the binding (any fuel). -/
theorem evalStmtFuel_vfree (f : Nat) (x : String) (ρ : Env)
    (b b' : Vec32) (ρ' : Env)
    (harr : envLookup ρ x = some (.vecVal b))
    (hfree : vecFree b = .ok b')
    (hu : envUpdate ρ x (.vecVal b') = some ρ') :
    evalStmtFuel f (.vfree x) ρ = .ok (ρ', .fellThrough) := by
  cases f <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, harr, hfree, hu]

/-- Zero fuel exits a loop whose condition is already false. -/
theorem evalStmtFuel_zero_while_exit (c : CExpr) (b : CStmt) (ρ : Env)
    (h : evalExpr c ρ = .ok (.b false)) :
    evalStmtFuel 0 (.while_ c b) ρ = .ok (ρ, .fellThrough) := by
  simp [evalStmtFuel, evalStmtZero, evalStmtZeroHandler, evalStmtWith, h]

/-- Zero fuel exhausts a loop that wants another iteration. -/
theorem evalStmtFuel_zero_while_enter (c : CExpr) (b : CStmt) (ρ : Env)
    (h : evalExpr c ρ = .ok (.b true)) :
    evalStmtFuel 0 (.while_ c b) ρ = .error .AssertFail := by
  simp [evalStmtFuel, evalStmtZero, evalStmtZeroHandler, evalStmtWith, h]

/-! ## Function entry: argument binding + outcome -/

/-- Bind actuals to formals (names only; types/roles are `validate`'s job
    in Phase 4). Arity mismatch is `none`, and `evalFunc` rejects it. -/
def bindArgs : List Param → List Value → Option Env
  | [], [] => some []
  | p :: ps, v :: vs =>
    match bindArgs ps vs with
    | none => none
    | some ρ => some ((p.name, v) :: ρ)
  | _, _ => none

/-- Whole-function semantics at explicit fuel (loop proofs generalize it). -/
def evalFuncFuel (fuel : Nat) (f : Func) (args : List Value) : Result Value :=
  match bindArgs f.args args with
  | none => .error .AssertFail
  | some ρ =>
    match evalStmtFuel fuel f.body ρ with
    | .error e => .error e
    | .ok (_, .returned v) => .ok v
    | .ok (_, .fellThrough) => .error .AssertFail

/-- Whole-function semantics: bind, run the body, demand a `return`.
    Falling off the end without returning is `AssertFail` (the C corpus
    always returns; `validate` enforces it). -/
def evalFunc (f : Func) (args : List Value) : Result Value :=
  evalFuncFuel EVAL_FUEL f args

theorem bindArgs_nil : bindArgs [] [] = some [] := rfl

theorem bindArgs_mismatch (p : Param) (ps : List Param) :
    bindArgs (p :: ps) [] = none := rfl

theorem evalFunc_arity (f : Func) (args : List Value)
    (h : bindArgs f.args args = none) :
    evalFunc f args = .error .AssertFail := by
  simp [evalFunc, evalFuncFuel, h]

theorem evalFuncFuel_arity (fuel : Nat) (f : Func) (args : List Value)
    (h : bindArgs f.args args = none) :
    evalFuncFuel fuel f args = .error .AssertFail := by
  simp [evalFuncFuel, h]
