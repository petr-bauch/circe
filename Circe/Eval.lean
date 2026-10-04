/-
Circe.Eval — loan-based, value-only ownership semantics (spec for
`emit_correct`).

Environments map variables to *values with loan/borrow bookkeeping*;
there is no heap and no addresses (Aeneas-style, see docs/PIPELINE.md).
Phase 4: `evalExpr` covers `lit`/`var`/`add` (signed `nsw`-checked,
over `i32`/`i64` — S3b) plus
`uadd`/`umul` (wrapping unsigned, over `u32`/`u64`), `ult` (unsigned
comparison, over `u32`/`u64`), `ueq` (bit equality, over
`u32`/`u64`/`i32`/`i64` — N4b: `cir.cmp eq` is signedness-blind), and `idx`
(bounded indexing, `OOB` on violation); `evalStmt` covers the full
loop-free fragment (`skip`/`seq`/`let_`/`assign`/`if_`/`return_`) plus
fuel-bounded `while_` (`EVAL_FUEL`; exhaustion is `AssertFail`, and
`validate` admits only bounded loops) plus S3a loop-scoped
`break_`/`continue_` (`broke`/`continued` outcomes: `while_` catches
them, escape from a body is `AssertFail`). `call` stays a legacy stub;
`callRet` carries S1 program calls (see the program layer below).
`bindArgs`/`evalFunc` give whole-function semantics; `evalFuncFuel`
exposes the fuel for induction (loop proofs generalize it).
-/
import Circe.Base
import Circe.CoreIR

/-- Runtime values: no addresses. C `int` → `BitVec 32` (`i32`) or
    `BitVec 64` (`i64`, S3b); unsigned likewise (`u32`/`u64`); arrays are
    pure length-paired lists of integers and structs are named field
    lists — never pointers (flat-value fragment; uniquely-owned heap
    blocks are `vecVal` values with an affine token, Phase 7).
    64-bit arrays/loops are future work (S3b admits loop-free 64-bit
    adds only); a `u64` index into a 32-bit array is `AssertFail`.
    `std::optional<int32_t>` is `optVal` (the engaged word or
    `none`; N4d-ii). `std::span<const int32_t>` is `spanVal` (the
    reified viewed words; `sharedBorrow` pure-copy snapshot semantics,
    the S1 `sum_array` precedent bundled into one value; N4d-iii). -/
inductive Value : Type
  | i32 : BitVec 32 → Value
  | u32 : BitVec 32 → Value
  | i64 : BitVec 64 → Value
  | u64 : BitVec 64 → Value
  | b : Bool → Value
  | unit : Value
  | arr32 : List (BitVec 32) → Value
  | vecVal : Vec32 → Value
  | vecVal64 : Vec64 → Value
  | boxVal : Box32 → Value
  | structVal : String → List (String × BitVec 32) → Value
  | optVal : Option (BitVec 32) → Value
  | spanVal : List (BitVec 32) → Value
  deriving DecidableEq, Repr

/-- Evaluation environment: variables to values. Loan/borrow bookkeeping
    lives in the companion `LoanState` (Aeneas §4 regions, value-only). -/
abbrev Env : Type := List (String × Value)

/-- Function outcome: a returned value, loop-scoped `break_`/`continue_`
    signals, or fall-through. `broke`/`continued` escaping a function body
    is `AssertFail` (`evalFuncFuel`); `validate` admits them only inside
    loops, so this is incompleteness, never unsoundness. -/
inductive Outcome : Type
  | returned : Value → Outcome
  | broke : Outcome
  | continued : Outcome
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
  | .i64 v => .i64 v
  | .u64 v => .u64 v
  | .b v => .b v

/-- Field lookup in a flat struct value (fields are `BitVec 32`;
    S2 `Point` is `i32`-only). Missing field is `none` (loud
    `AssertFail` at the expression level, never silent). -/
def fieldLookup : List (String × BitVec 32) → String → Option (BitVec 32)
  | [], _ => none
  | (k, v) :: rest, f => if f = k then some v else fieldLookup rest f

theorem fieldLookup_hit (k : String) (v : BitVec 32)
    (rest : List (String × BitVec 32)) :
    fieldLookup ((k, v) :: rest) k = some v := by
  simp [fieldLookup]

theorem fieldLookup_miss (k f : String) (v : BitVec 32)
    (rest : List (String × BitVec 32)) (h : f ≠ k) :
    fieldLookup ((k, v) :: rest) f = fieldLookup rest f := by
  simp [fieldLookup, h]

/-- Pure evaluator:
    - `add` on `i32` goes through `checkedAddI32` (overflow → `Overflow`);
      on `i64` through `checkedAddI64` (S3b); mixed widths are
      `AssertFail`;
    - `uadd`/`umul` on `u32`/`u64` wrap (plain `cir.add`/`cir.mul`;
      never fail); mixed widths are `AssertFail`;
    - `ult` on `u32`/`u64` is unsigned comparison (mixed widths are
      `AssertFail`); `ueq` is width-polymorphic bit equality
      (`u32`/`u64`/`i32`/`i64` pairs; `cir.cmp eq` compares bits
      regardless of signedness, so same-width pairs are always
      defined; mixed widths are `AssertFail`);
    - `idx a i` looks up `arr32` array `a` at `u32` index `i`
      (`OOB` off the end, mirroring `bget`);
    - `idxi a i` looks up `arr32` array `a` at `u64` index `i` and
      delivers the word as `i32` (`cir.get_element` over a static
      `i32` array, N4d; `OOB` off the end, mirroring `idx`);
    - `optHas o` reads the engaged bit of `optVal` `o` (`.b`
      of `isSome`; non-`optVal` is `AssertFail`);
    - `optGet o` reads the payload word of engaged `optVal` `o`
      (disengaged is `AssertFail`: the `unreachable` assert made
      loud; non-`optVal` is `AssertFail`);
    - `fget o f` projects field `f` from `structVal` `o` (missing
      field / non-struct is `AssertFail`);
    - `pmk x y` builds the S2 `Point` `structVal` from two `i32`s;
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
    | .ok (.i64 x), .ok (.i64 y) => (checkedAddI64 x y).map .i64
    | .ok _, .ok _ => .error .AssertFail
    | .error e, _ => .error e
    | _, .error e => .error e
  | .uadd a b, ρ =>
    match evalExpr a ρ, evalExpr b ρ with
    | .ok (.u32 x), .ok (.u32 y) => .ok (.u32 (x + y))
    | .ok (.u64 x), .ok (.u64 y) => .ok (.u64 (x + y))
    | .ok _, .ok _ => .error .AssertFail
    | .error e, _ => .error e
    | _, .error e => .error e
  | .umul a b, ρ =>
    match evalExpr a ρ, evalExpr b ρ with
    | .ok (.u32 x), .ok (.u32 y) => .ok (.u32 (x * y))
    | .ok (.u64 x), .ok (.u64 y) => .ok (.u64 (x * y))
    | .ok _, .ok _ => .error .AssertFail
    | .error e, _ => .error e
    | _, .error e => .error e
  | .ult a b, ρ =>
    match evalExpr a ρ, evalExpr b ρ with
    | .ok (.u32 x), .ok (.u32 y) => .ok (.b (x.ult y))
    | .ok (.u64 x), .ok (.u64 y) => .ok (.b (x.ult y))
    | .ok _, .ok _ => .error .AssertFail
    | .error e, _ => .error e
    | _, .error e => .error e
  | .ueq a b, ρ =>
    match evalExpr a ρ, evalExpr b ρ with
    | .ok (.u32 x), .ok (.u32 y) => .ok (.b (x == y))
    | .ok (.u64 x), .ok (.u64 y) => .ok (.b (x == y))
    | .ok (.i32 x), .ok (.i32 y) => .ok (.b (x == y))
    | .ok (.i64 x), .ok (.i64 y) => .ok (.b (x == y))
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
  | .idxi arr ie, ρ =>
    match envLookup ρ arr with
    | none => .error .Uninit
    | some (.arr32 l) =>
      match evalExpr ie ρ with
      | .error e => .error e
      | .ok (.u64 i) =>
        match l[i.toNat]? with
        | some x => .ok (.i32 x)
        | none => .error .OOB
      | .ok _ => .error .AssertFail
    | some _ => .error .AssertFail
  | .optHas o, ρ =>
    match envLookup ρ o with
    | none => .error .Uninit
    | some (.optVal v) => .ok (.b v.isSome)
    | some _ => .error .AssertFail
  | .optGet o, ρ =>
    match envLookup ρ o with
    | none => .error .Uninit
    | some (.optVal v) =>
      match v with
      | some x => .ok (.i32 x)
      | none => .error .AssertFail
    | some _ => .error .AssertFail
  | .spanLen s, ρ =>
    match envLookup ρ s with
    | none => .error .Uninit
    | some (.spanVal l) => .ok (.u64 (BitVec.ofNat 64 l.length))
    | some _ => .error .AssertFail
  | .spanAt s ie, ρ =>
    match envLookup ρ s with
    | none => .error .Uninit
    | some (.spanVal l) =>
      match evalExpr ie ρ with
      | .error e => .error e
      | .ok (.u64 i) =>
        match l[i.toNat]? with
        | some x => .ok (.i32 x)
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
    | .ok (.u64 n) =>
      match vecNew64 n.toNat with
      | .error e => .error e
      | .ok v => .ok (.vecVal64 v)
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
    | some (.vecVal64 v) =>
      match evalExpr ie ρ with
      | .error e => .error e
      | .ok (.u64 i) =>
        match vecGet64 v i.toNat with
        | .error e => .error e
        | .ok x => .ok (.u64 x)
      | .ok _ => .error .AssertFail
    | some _ => .error .AssertFail
  | .boxNew se, ρ =>
    match evalExpr se ρ with
    | .error e => .error e
    | .ok (.i32 x) =>
      match boxNew x with
      | .error e => .error e
      | .ok b => .ok (.boxVal b)
    | .ok _ => .error .AssertFail
  | .boxGet b, ρ =>
    match envLookup ρ b with
    | none => .error .Uninit
    | some (.boxVal v) =>
      match boxGet v with
      | .error e => .error e
      | .ok x => .ok (.i32 x)
    | some _ => .error .AssertFail
  | .fget obj field, ρ =>
    match envLookup ρ obj with
    | none => .error .Uninit
    | some (.structVal _ fields) =>
      match fieldLookup fields field with
      | some x => .ok (.i32 x)
      | none => .error .AssertFail
    | some _ => .error .AssertFail
  | .pmk x y, ρ =>
    match evalExpr x ρ, evalExpr y ρ with
    | .ok (.i32 xv), .ok (.i32 yv) =>
      .ok (.structVal "Point" [("x", xv), ("y", yv)])
    | .ok _, .ok _ => .error .AssertFail
    | .error e, _ => .error e
    | _, .error e => .error e

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

/-- `add` on two `i64` literals forwards to `checkedAddI64`. -/
theorem evalExpr_add64_lit (x y : BitVec 64) (ρ : Env) :
    evalExpr (.add (.lit (.i64 x)) (.lit (.i64 y))) ρ =
      (checkedAddI64 x y).map .i64 := by
  simp [evalExpr, litVal]

/-- `add` across widths is rejected, never silently modeled. -/
theorem evalExpr_add_width_mismatch (ρ : Env) :
    evalExpr (.add (.lit (.i32 0)) (.lit (.i64 0))) ρ =
      .error .AssertFail := by
  simp [evalExpr, litVal]

/-- `uadd` on two `u64` literals wraps. -/
theorem evalExpr_uadd64_lit (x y : BitVec 64) (ρ : Env) :
    evalExpr (.uadd (.lit (.u64 x)) (.lit (.u64 y))) ρ =
      .ok (.u64 (x + y)) := by
  simp [evalExpr, litVal]

/-- `uadd` across widths is rejected. -/
theorem evalExpr_uadd_width_mismatch (ρ : Env) :
    evalExpr (.uadd (.lit (.u32 0)) (.lit (.u64 0))) ρ =
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

/-- `umul` on two `u32` literals wraps. -/
theorem evalExpr_umul_lit (x y : BitVec 32) (ρ : Env) :
    evalExpr (.umul (.lit (.u32 x)) (.lit (.u32 y))) ρ =
      .ok (.u32 (x * y)) := by
  simp [evalExpr, litVal]

/-- `umul` type mismatches are rejected. -/
theorem evalExpr_umul_mismatch (ρ : Env) :
    evalExpr (.umul (.lit (.u32 0)) (.lit (.b true))) ρ =
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

/-- `ueq` on two `u32` literals is unsigned equality. -/
theorem evalExpr_ueq_lit (x y : BitVec 32) (ρ : Env) :
    evalExpr (.ueq (.lit (.u32 x)) (.lit (.u32 y))) ρ =
      .ok (.b (x == y)) := by
  simp [evalExpr, litVal]

/-- `ueq` on two `i32` literals is bit equality (N4b: `cir.cmp eq`
    on signed words; signedness never affects `==` on bits). -/
theorem evalExpr_ueq_i32_lit (x y : BitVec 32) (ρ : Env) :
    evalExpr (.ueq (.lit (.i32 x)) (.lit (.i32 y))) ρ =
      .ok (.b (x == y)) := by
  simp [evalExpr, litVal]

/-- `ueq` mixed-width pairs are still rejected. -/
theorem evalExpr_ueq_mismatch (ρ : Env) :
    evalExpr (.ueq (.lit (.u32 0)) (.lit (.i32 1))) ρ =
      .error .AssertFail := by
  simp [evalExpr, litVal]

/-- `umul` on two `u64` literals wraps. -/
theorem evalExpr_umul64_lit (x y : BitVec 64) (ρ : Env) :
    evalExpr (.umul (.lit (.u64 x)) (.lit (.u64 y))) ρ =
      .ok (.u64 (x * y)) := by
  simp [evalExpr, litVal]

/-- `ult` on two `u64` literals is unsigned comparison. -/
theorem evalExpr_ult64_lit (x y : BitVec 64) (ρ : Env) :
    evalExpr (.ult (.lit (.u64 x)) (.lit (.u64 y))) ρ =
      .ok (.b (x.ult y)) := by
  simp [evalExpr, litVal]

/-- `ueq` on two `u64` literals is unsigned equality. -/
theorem evalExpr_ueq64_lit (x y : BitVec 64) (ρ : Env) :
    evalExpr (.ueq (.lit (.u64 x)) (.lit (.u64 y))) ρ =
      .ok (.b (x == y)) := by
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

/-- In-bounds `i32`-flavored indexing succeeds. -/
theorem evalExpr_idxi_hit (arr : String) (l : List (BitVec 32)) (i : BitVec 64)
    (ρ : Env) (x : BitVec 32)
    (harr : envLookup ρ arr = some (.arr32 l))
    (hidx : l[i.toNat]? = some x) :
    evalExpr (.idxi arr (.lit (.u64 i))) ρ = .ok (.i32 x) := by
  simp [evalExpr, litVal, harr, hidx]

/-- Out-of-bounds `i32`-flavored indexing reports `OOB`. -/
theorem evalExpr_idxi_oob (arr : String) (l : List (BitVec 32)) (i : BitVec 64)
    (ρ : Env)
    (harr : envLookup ρ arr = some (.arr32 l))
    (hidx : l[i.toNat]? = none) :
    evalExpr (.idxi arr (.lit (.u64 i))) ρ = .error .OOB := by
  simp [evalExpr, litVal, harr, hidx]

/-- `i32`-flavored indexing of a non-array is rejected, never silently
    modeled. -/
theorem evalExpr_idxi_notarray (arr : String) (v : BitVec 32) (i : BitVec 64)
    (ρ : Env)
    (harr : envLookup ρ arr = some (.i32 v)) :
    evalExpr (.idxi arr (.lit (.u64 i))) ρ = .error .AssertFail := by
  simp [evalExpr, harr]

/-- Engaged `optVal` reports `true`. -/
theorem evalExpr_optHas_some (o : String) (ρ : Env) (x : BitVec 32)
    (ho : envLookup ρ o = some (.optVal (some x))) :
    evalExpr (.optHas o) ρ = .ok (.b true) := by
  simp [evalExpr, ho]

/-- Disengaged `optVal` reports `false`. -/
theorem evalExpr_optHas_none (o : String) (ρ : Env)
    (ho : envLookup ρ o = some (.optVal none)) :
    evalExpr (.optHas o) ρ = .ok (.b false) := by
  simp [evalExpr, ho]

/-- `optHas` of a non-optional is rejected, never silently modeled. -/
theorem evalExpr_optHas_notval (o : String) (v : BitVec 32) (ρ : Env)
    (ho : envLookup ρ o = some (.i32 v)) :
    evalExpr (.optHas o) ρ = .error .AssertFail := by
  simp [evalExpr, ho]

/-- Engaged `optVal` delivers the payload word. -/
theorem evalExpr_optGet_some (o : String) (ρ : Env) (x : BitVec 32)
    (ho : envLookup ρ o = some (.optVal (some x))) :
    evalExpr (.optGet o) ρ = .ok (.i32 x) := by
  simp [evalExpr, ho]

/-- Disengaged `optVal` is `AssertFail` (the `unreachable` assert
    made loud). -/
theorem evalExpr_optGet_none (o : String) (ρ : Env)
    (ho : envLookup ρ o = some (.optVal none)) :
    evalExpr (.optGet o) ρ = .error .AssertFail := by
  simp [evalExpr, ho]

/-- `optGet` of a non-optional is rejected, never silently modeled. -/
theorem evalExpr_optGet_notval (o : String) (v : BitVec 32) (ρ : Env)
    (ho : envLookup ρ o = some (.i32 v)) :
    evalExpr (.optGet o) ρ = .error .AssertFail := by
  simp [evalExpr, ho]

/-- `spanLen` of a span delivers its length as a `u64` word. -/
theorem evalExpr_spanLen_some (s : String) (ρ : Env)
    (l : List (BitVec 32))
    (hs : envLookup ρ s = some (.spanVal l)) :
    evalExpr (.spanLen s) ρ = .ok (.u64 (BitVec.ofNat 64 l.length)) := by
  simp [evalExpr, hs]

/-- `spanLen` of a non-span is rejected, never silently modeled. -/
theorem evalExpr_spanLen_notval (s : String) (v : BitVec 32) (ρ : Env)
    (hs : envLookup ρ s = some (.i32 v)) :
    evalExpr (.spanLen s) ρ = .error .AssertFail := by
  simp [evalExpr, hs]

/-- `spanAt` in bounds delivers the word. -/
theorem evalExpr_spanAt_some (s : String) (ie : CExpr) (ρ : Env)
    (l : List (BitVec 32)) (i : BitVec 64) (x : BitVec 32)
    (hs : envLookup ρ s = some (.spanVal l))
    (hi : evalExpr ie ρ = .ok (.u64 i))
    (hget : l[i.toNat]? = some x) :
    evalExpr (.spanAt s ie) ρ = .ok (.i32 x) := by
  simp [evalExpr, hs, hi, hget]

/-- `spanAt` off the end is `OOB` (mirrors `idx`). -/
theorem evalExpr_spanAt_oob (s : String) (ie : CExpr) (ρ : Env)
    (l : List (BitVec 32)) (i : BitVec 64)
    (hs : envLookup ρ s = some (.spanVal l))
    (hi : evalExpr ie ρ = .ok (.u64 i))
    (hget : l[i.toNat]? = none) :
    evalExpr (.spanAt s ie) ρ = .error .OOB := by
  simp [evalExpr, hs, hi, hget]

/-- `spanAt` with a non-`u64` index is rejected. -/
theorem evalExpr_spanAt_nonu64 (s : String) (ie : CExpr) (ρ : Env)
    (l : List (BitVec 32)) (v : BitVec 32)
    (hs : envLookup ρ s = some (.spanVal l))
    (hi : evalExpr ie ρ = .ok (.i32 v)) :
    evalExpr (.spanAt s ie) ρ = .error .AssertFail := by
  simp [evalExpr, hs, hi]

/-- `spanAt` of a non-span is rejected, never silently modeled. -/
theorem evalExpr_spanAt_notval (s : String) (ie : CExpr) (v : BitVec 32)
    (ρ : Env)
    (hs : envLookup ρ s = some (.i32 v)) :
    evalExpr (.spanAt s ie) ρ = .error .AssertFail := by
  simp [evalExpr, hs]

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

/-- `add` of a projected field and a variable forwards to `checkedAddI32`. -/
theorem evalExpr_add_fget_var (ρ : Env) (obj f xv : String)
    (tag : String) (fields : List (String × BitVec 32))
    (px dx : BitVec 32)
    (hobj : envLookup ρ obj = some (.structVal tag fields))
    (hfield : fieldLookup fields f = some px)
    (hvar : envLookup ρ xv = some (.i32 dx)) :
    evalExpr (.add (.fget obj f) (.var xv)) ρ =
      (checkedAddI32 px dx).map .i32 := by
  simp [evalExpr, hobj, hfield, hvar]

/-- Reading a non-block is rejected, never silently modeled. -/
theorem evalExpr_vget_notvec (arr : String) (v : BitVec 32) (i : BitVec 32)
    (ρ : Env)
    (harr : envLookup ρ arr = some (.i32 v)) :
    evalExpr (.vget arr (.lit (.u32 i))) ρ = .error .AssertFail := by
  simp [evalExpr, harr]

/-- `vnew` on a `u64` size allocates a zeroed live `u64` block (M1b). -/
theorem evalExpr_vnew_lit64 (n : BitVec 64) (ρ : Env) :
    evalExpr (.vnew (.lit (.u64 n))) ρ =
      .ok (.vecVal64 ⟨List.replicate n.toNat 0, false⟩) := by
  simp [evalExpr, litVal, vecNew64]

/-- In-bounds `u64` heap read succeeds (M1b). -/
theorem evalExpr_vget_hit64 (arr : String) (v : Vec64) (i : BitVec 64)
    (ρ : Env) (x : BitVec 64)
    (harr : envLookup ρ arr = some (.vecVal64 v))
    (hget : vecGet64 v i.toNat = .ok x) :
    evalExpr (.vget arr (.lit (.u64 i))) ρ = .ok (.u64 x) := by
  simp [evalExpr, litVal, harr, hget]

/-- `u64` heap read errors (OOB/use-after-free) propagate (M1b). -/
theorem evalExpr_vget_err64 (arr : String) (v : Vec64) (i : BitVec 64)
    (ρ : Env) (e : Panic)
    (harr : envLookup ρ arr = some (.vecVal64 v))
    (hget : vecGet64 v i.toNat = .error e) :
    evalExpr (.vget arr (.lit (.u64 i))) ρ = .error e := by
  simp [evalExpr, litVal, harr, hget]

/-- Mixed-width heap read is rejected (M1b S3b policy): a `u32` block
    read with a `u64` index is `AssertFail`, never silently modeled. -/
theorem evalExpr_vget_mix (arr : String) (v : Vec32) (i : BitVec 64)
    (ρ : Env)
    (harr : envLookup ρ arr = some (.vecVal v)) :
    evalExpr (.vget arr (.lit (.u64 i))) ρ = .error .AssertFail := by
  simp [evalExpr, litVal, harr]

/-- Mixed-width heap read is rejected (M1b S3b policy): a `u64` block
    read with a `u32` index is `AssertFail`, never silently modeled. -/
theorem evalExpr_vget_mix64 (arr : String) (v : Vec64) (i : BitVec 32)
    (ρ : Env)
    (harr : envLookup ρ arr = some (.vecVal64 v)) :
    evalExpr (.vget arr (.lit (.u32 i))) ρ = .error .AssertFail := by
  simp [evalExpr, litVal, harr]

/-- `boxNew` on an `i32` init allocates a live box (M2c). -/
theorem evalExpr_boxNew_ok (e : CExpr) (ρ : Env) (x : BitVec 32)
    (h : evalExpr e ρ = .ok (.i32 x)) :
    evalExpr (.boxNew e) ρ = .ok (.boxVal ⟨x, false⟩) := by
  simp [evalExpr, h, boxNew]

/-- `boxNew` propagates init errors. -/
theorem evalExpr_boxNew_err (e : CExpr) (ρ : Env) (err : Panic)
    (h : evalExpr e ρ = .error err) :
    evalExpr (.boxNew e) ρ = .error err := by
  simp [evalExpr, h]

/-- `boxNew` on a non-`i32` init is rejected. -/
theorem evalExpr_boxNew_mismatch (e : CExpr) (ρ : Env) (v : Value)
    (hv : ∀ x : BitVec 32, v ≠ .i32 x)
    (h : evalExpr e ρ = .ok v) :
    evalExpr (.boxNew e) ρ = .error .AssertFail := by
  simp [evalExpr, h]

/-- Live box read succeeds (M2c). -/
theorem evalExpr_boxGet_hit (b : String) (v : Box32) (ρ : Env) (x : BitVec 32)
    (harr : envLookup ρ b = some (.boxVal v))
    (hget : boxGet v = .ok x) :
    evalExpr (.boxGet b) ρ = .ok (.i32 x) := by
  simp [evalExpr, harr, hget]

/-- Box read errors (use-after-`delete`) propagate (M2c). -/
theorem evalExpr_boxGet_err (b : String) (v : Box32) (ρ : Env) (e : Panic)
    (harr : envLookup ρ b = some (.boxVal v))
    (hget : boxGet v = .error e) :
    evalExpr (.boxGet b) ρ = .error e := by
  simp [evalExpr, harr, hget]

/-- Reading a non-box is rejected, never silently modeled (M2c). -/
theorem evalExpr_boxGet_notbox (b : String) (v : BitVec 32)
    (ρ : Env)
    (harr : envLookup ρ b = some (.i32 v)) :
    evalExpr (.boxGet b) ρ = .error .AssertFail := by
  simp [evalExpr, harr]

/-- Field projection hits. -/
theorem evalExpr_fget_hit (obj : String) (tag : String)
    (fields : List (String × BitVec 32)) (f : String) (x : BitVec 32)
    (ρ : Env)
    (harr : envLookup ρ obj = some (.structVal tag fields))
    (hget : fieldLookup fields f = some x) :
    evalExpr (.fget obj f) ρ = .ok (.i32 x) := by
  simp [evalExpr, harr, hget]

/-- Missing field is rejected, never silently modeled. -/
theorem evalExpr_fget_miss (obj : String) (tag : String)
    (fields : List (String × BitVec 32)) (f : String)
    (ρ : Env)
    (harr : envLookup ρ obj = some (.structVal tag fields))
    (hget : fieldLookup fields f = none) :
    evalExpr (.fget obj f) ρ = .error .AssertFail := by
  simp [evalExpr, harr, hget]

/-- Projecting from a non-struct is rejected. -/
theorem evalExpr_fget_notstruct (obj : String) (v : BitVec 32) (f : String)
    (ρ : Env)
    (harr : envLookup ρ obj = some (.i32 v)) :
    evalExpr (.fget obj f) ρ = .error .AssertFail := by
  simp [evalExpr, harr]

/-- Projecting from an unbound variable is `Uninit`. -/
theorem evalExpr_fget_unbound (obj f : String) (ρ : Env)
    (harr : envLookup ρ obj = none) :
    evalExpr (.fget obj f) ρ = .error .Uninit := by
  simp [evalExpr, harr]

/-- `pmk` on two `i32`s builds the `Point` struct value. -/
theorem evalExpr_pmk_ok (x y : CExpr) (ρ : Env)
    (xv yv : BitVec 32)
    (hx : evalExpr x ρ = .ok (.i32 xv))
    (hy : evalExpr y ρ = .ok (.i32 yv)) :
    evalExpr (.pmk x y) ρ =
      .ok (.structVal "Point" [("x", xv), ("y", yv)]) := by
  simp [evalExpr, hx, hy]

/-- `pmk` type mismatches are rejected. -/
theorem evalExpr_pmk_mismatch (ρ : Env) :
    evalExpr (.pmk (.lit (.i32 0)) (.lit (.b true))) ρ =
      .error .AssertFail := by
  simp [evalExpr, litVal]

/-- `pmk` propagates left errors. -/
theorem evalExpr_pmk_err_l (x y : CExpr) (ρ : Env) (e : Panic)
    (hx : evalExpr x ρ = .error e) :
    evalExpr (.pmk x y) ρ = .error e := by
  simp [evalExpr, hx]

/-! ## Statement evaluator (fuel-bounded `while_`) -/

/-- Default fuel: loops must terminate within this many iterations.
    Exhaustion reports `AssertFail` (incompleteness, not unsoundness:
    `validate` admits only bounded loops; see `docs/SUBSET.md`). -/
def EVAL_FUEL : Nat := 4096

/-! ## S5 fuel automation (Tactics stage 2; documented in `Circe.Tactics`).

No new subset: these discharge proof obligations the existing
fuel-generalized loop proofs already carry. -/

/-- Fuel fits in a word: anything within `EVAL_FUEL` is below `2 ^ 32`.
    Collapses the `h32eq` / `hle4096` / `omega` block repeated in every
    `emit_correct_*` wrapper into one `have`. -/
theorem word32_lt_two32_of_fuel (n : BitVec 32)
    (h : n.toNat ≤ EVAL_FUEL) : n.toNat < 2 ^ 32 := by
  have h4096 : n.toNat ≤ 4096 := by simpa [EVAL_FUEL] using h
  omega

/-- Fuel fits in a `u64` word (M1b): anything within `EVAL_FUEL` is below
    `2 ^ 64` (mirror of `word32_lt_two32_of_fuel` for `vec_alloc_u64`). -/
theorem word64_lt_two64_of_fuel (n : BitVec 64)
    (h : n.toNat ≤ EVAL_FUEL) : n.toNat < 2 ^ 64 := by
  have h4096 : n.toNat ≤ 4096 := by simpa [EVAL_FUEL] using h
  omega

/-- Fuel automation: normalize `EVAL_FUEL` wherever it appears, then
    discharge fuel arithmetic — `≤ EVAL_FUEL` / `≤ 4096` bounds and the
    `remaining ≤ F` side conditions of fuel-generalized loop facts
    (the `(by omega)` arguments to `sumWhile_correct`,
    `vecFillWhile_correct`, and friends). Written with explicit
    `first`-branching (not `try ... ; omega`: `try` would swallow the
    whole sequence when `simp` makes no progress). -/
macro "cir_fuel" : tactic =>
  `(tactic| (first | (simp only [EVAL_FUEL] at *; omega) | omega))

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
    | .ok (ρ', .broke) => .ok (ρ', .broke)
    | .ok (ρ', .continued) => .ok (ρ', .continued)
    | .ok (ρ', .fellThrough) => evalStmtWith wh b ρ'
  | .cleanup body, ρ => evalStmtWith wh body ρ
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
    | .ok (.u64 i), .ok (.u64 xv) =>
      match envLookup ρ x with
      | none => .error .Uninit
      | some (.vecVal64 b) =>
        match vecSet64 b i.toNat xv with
        | .error e => .error e
        | .ok b' =>
          match envUpdate ρ x (.vecVal64 b') with
          | none => .error .Uninit
          | some ρ' => .ok (ρ', .fellThrough)
      | some _ => .error .AssertFail
    | .ok _, .ok _ => .error .AssertFail
    | .error e, _ => .error e
    | _, .error e => .error e
  | .vrealloc x se, ρ =>
    match evalExpr se ρ with
    | .error e => .error e
    | .ok (.u32 m) =>
      match envLookup ρ x with
      | none => .error .Uninit
      | some (.vecVal b) =>
        match vecRealloc b m.toNat with
        | .error e => .error e
        | .ok b' =>
          match envUpdate ρ x (.vecVal b') with
          | none => .error .Uninit
          | some ρ' => .ok (ρ', .fellThrough)
      | some _ => .error .AssertFail
    | .ok _ => .error .AssertFail
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
    | some (.vecVal64 b) =>
      match vecFree64 b with
      | .error e => .error e
      | .ok b' =>
        match envUpdate ρ x (.vecVal64 b') with
        | none => .error .Uninit
        | some ρ' => .ok (ρ', .fellThrough)
    | some _ => .error .AssertFail
  | .boxFree x, ρ =>
    match envLookup ρ x with
    | none => .error .Uninit
    | some (.boxVal b) =>
      match boxFree b with
      | .error e => .error e
      | .ok b' =>
        match envUpdate ρ x (.boxVal b') with
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
  | .break_, ρ => .ok (ρ, .broke)
  | .continue_, ρ => .ok (ρ, .continued)
  | .call _ _, ρ => .ok (ρ, .fellThrough)
  | .callRet _ _ _, _ =>
    -- Calls need program context (which function `f` resolves to); outside
    -- `evalProgStmt` they are rejected loudly, never silently modeled.
    .error .AssertFail
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
      | .ok (ρ', .broke) => .ok (ρ', .fellThrough)
      | .ok (ρ', .continued) => rec (.while_ c b) ρ'
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

/-- `vset` stores through a live `u64` block (M1b mirror, any fuel). -/
theorem evalStmtFuel_vset64 (f : Nat) (x : String) (ie ve : CExpr) (ρ : Env)
    (i xv : BitVec 64) (b b' : Vec64) (ρ' : Env)
    (hi : evalExpr ie ρ = .ok (.u64 i))
    (hv : evalExpr ve ρ = .ok (.u64 xv))
    (harr : envLookup ρ x = some (.vecVal64 b))
    (hset : vecSet64 b i.toNat xv = .ok b')
    (hu : envUpdate ρ x (.vecVal64 b') = some ρ') :
    evalStmtFuel f (.vset x ie ve) ρ = .ok (ρ', .fellThrough) := by
  cases f <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, hi, hv, harr, hset, hu]

/-- `u64` `vset` errors propagate (M1b mirror, any fuel). -/
theorem evalStmtFuel_vset_err64 (f : Nat) (x : String) (ie ve : CExpr)
    (ρ : Env) (i xv : BitVec 64) (b : Vec64) (e : Panic)
    (hi : evalExpr ie ρ = .ok (.u64 i))
    (hv : evalExpr ve ρ = .ok (.u64 xv))
    (harr : envLookup ρ x = some (.vecVal64 b))
    (hset : vecSet64 b i.toNat xv = .error e) :
    evalStmtFuel f (.vset x ie ve) ρ = .error e := by
  cases f <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, hi, hv, harr, hset]

/-- `u64` `vfree` consumes the token (M1b mirror, any fuel). -/
theorem evalStmtFuel_vfree64 (f : Nat) (x : String) (ρ : Env)
    (b b' : Vec64) (ρ' : Env)
    (harr : envLookup ρ x = some (.vecVal64 b))
    (hfree : vecFree64 b = .ok b')
    (hu : envUpdate ρ x (.vecVal64 b') = some ρ') :
    evalStmtFuel f (.vfree x) ρ = .ok (ρ', .fellThrough) := by
  cases f <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, harr, hfree, hu]

/-- `boxFree` consumes the token and updates the binding (M2c, any fuel). -/
theorem evalStmtFuel_boxFree (f : Nat) (x : String) (ρ : Env)
    (b b' : Box32) (ρ' : Env)
    (harr : envLookup ρ x = some (.boxVal b))
    (hfree : boxFree b = .ok b')
    (hu : envUpdate ρ x (.boxVal b') = some ρ') :
    evalStmtFuel f (.boxFree x) ρ = .ok (ρ', .fellThrough) := by
  cases f <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, harr, hfree, hu]

/-- `boxFree` errors (double-`delete`) propagate (M2c, any fuel). -/
theorem evalStmtFuel_boxFree_err (f : Nat) (x : String) (ρ : Env)
    (b : Box32) (e : Panic)
    (harr : envLookup ρ x = some (.boxVal b))
    (hfree : boxFree b = .error e) :
    evalStmtFuel f (.boxFree x) ρ = .error e := by
  cases f <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, harr, hfree]

/-- `let_` binds the value and extends the environment (any fuel). -/
theorem evalStmtFuel_let_ (f : Nat) (x : String) (ty : CType) (e : CExpr)
    (ρ : Env) (v : Value)
    (h : evalExpr e ρ = .ok v) :
    evalStmtFuel f (.let_ x ty e) ρ =
      .ok (envExtend ρ x v, .fellThrough) := by
  cases f <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, h]

/-- `let_` propagates expression errors (any fuel). -/
theorem evalStmtFuel_let_err (f : Nat) (x : String) (ty : CType) (e : CExpr)
    (ρ : Env) (err : Panic)
    (h : evalExpr e ρ = .error err) :
    evalStmtFuel f (.let_ x ty e) ρ = .error err := by
  cases f <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, h]

/-- `vrealloc` resizes a live block and updates the binding (M1c, any fuel). -/
theorem evalStmtFuel_vrealloc (f : Nat) (x : String) (se : CExpr) (ρ : Env)
    (m : BitVec 32) (b b' : Vec32) (ρ' : Env)
    (hsize : evalExpr se ρ = .ok (.u32 m))
    (harr : envLookup ρ x = some (.vecVal b))
    (hre : vecRealloc b m.toNat = .ok b')
    (hu : envUpdate ρ x (.vecVal b') = some ρ') :
    evalStmtFuel f (.vrealloc x se) ρ = .ok (ρ', .fellThrough) := by
  cases f <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, hsize, harr, hre, hu]

/-- `vrealloc` errors (use-after-free) propagate (M1c, any fuel). -/
theorem evalStmtFuel_vrealloc_err (f : Nat) (x : String) (se : CExpr)
    (ρ : Env) (m : BitVec 32) (b : Vec32) (e : Panic)
    (hsize : evalExpr se ρ = .ok (.u32 m))
    (harr : envLookup ρ x = some (.vecVal b))
    (hre : vecRealloc b m.toNat = .error e) :
    evalStmtFuel f (.vrealloc x se) ρ = .error e := by
  cases f <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, hsize, harr, hre]

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

/-- Bind actuals to formals (names only; types/roles are `validate`'s job).
    Arity mismatch is `none`, and `evalFunc` rejects it. -/
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
    | .ok (_, .broke) => .error .AssertFail
    | .ok (_, .continued) => .error .AssertFail
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

/-! ## Program evaluation: DAG calls (S1) -/

/-- S1: a program is a list of validated `Func`s. DAG by validator
    construction: leaves (`add`/`sum_array`/…) are call-free (leaf shapes
    exclude `cir.call`), callers only target admitted leaves, and
    self-calls are rejected — so no cycle is expressible. -/
abbrev Prog := List Func

/-- Resolve a callee by name (first match wins). -/
def findFunc (p : Prog) (name : String) : Option Func :=
  p.find? (fun f => f.name == name)

theorem findFunc_hit (f : Func) (p : Prog) :
    findFunc (f :: p) f.name = some f := by
  unfold findFunc
  simp

theorem findFunc_miss (f : Func) (p : Prog) (name : String)
    (h : (f.name == name) = false) :
    findFunc (f :: p) name = findFunc p name := by
  simp [findFunc, h]

/-- Look up actuals in the environment (all-or-nothing; missing is loud). -/
def lookupArgs : Env → List String → Option (List Value)
  | _, [] => some []
  | ρ, x :: xs =>
    match envLookup ρ x, lookupArgs ρ xs with
    | some v, some vs => some (v :: vs)
    | _, _ => none

theorem lookupArgs_nil (ρ : Env) : lookupArgs ρ [] = some [] := rfl

theorem lookupArgs_cons_hit (ρ : Env) (x : String) (v : Value)
    (xs : List String) (vs : List Value)
    (h : envLookup ρ x = some v) (t : lookupArgs ρ xs = some vs) :
    lookupArgs ρ (x :: xs) = some (v :: vs) := by
  simp [lookupArgs, h, t]

/-- Depth-1 program statement evaluation. `callRet dst f xs` looks up the
    actuals, dispatches to the call-free callee via the old `evalFuncFuel`
    at the same fuel, and extends the environment with the result;
    `seq` recurses; everything else delegates to the old `evalStmtFuel`.
    Callee errors propagate; unknown callees / unbound actuals are loud. -/
def evalProgStmt (prog : Prog) (fuel : Nat) : CStmt → Env → Result (Env × Outcome)
  | .callRet dst f xs, ρ =>
    match lookupArgs ρ xs with
    | none => .error .Uninit
    | some vs =>
      match findFunc prog f with
      | none => .error .AssertFail
      | some callee =>
        match evalFuncFuel fuel callee vs with
        | .error e => .error e
        | .ok ret => .ok (envExtend ρ dst ret, .fellThrough)
  | .seq a b, ρ =>
    match evalProgStmt prog fuel a ρ with
    | .error e => .error e
    | .ok (ρ', .returned v) => .ok (ρ', .returned v)
    | .ok (ρ', .broke) => .ok (ρ', .broke)
    | .ok (ρ', .continued) => .ok (ρ', .continued)
    | .ok (ρ', .fellThrough) => evalProgStmt prog fuel b ρ'
  | .cleanup body, ρ => evalProgStmt prog fuel body ρ
  | .if_ c t e, ρ =>
    match evalExpr c ρ with
    | .ok (.b true) => evalProgStmt prog fuel t ρ
    | .ok (.b false) => evalProgStmt prog fuel e ρ
    | _ => .error .AssertFail
  | s, ρ => evalStmtFuel fuel s ρ

/-- `callRet` with resolved actuals + callee runs the callee. -/
theorem evalProgStmt_callRet_ok (prog : Prog) (fuel : Nat)
    (dst f : String) (xs : List String) (ρ : Env)
    (vs : List Value) (callee : Func) (ret : Value)
    (hargs : lookupArgs ρ xs = some vs)
    (hfind : findFunc prog f = some callee)
    (hcall : evalFuncFuel fuel callee vs = .ok ret) :
    evalProgStmt prog fuel (.callRet dst f xs) ρ =
      .ok (envExtend ρ dst ret, .fellThrough) := by
  simp [evalProgStmt, hargs, hfind, hcall]

/-- `callRet` propagates callee errors. -/
theorem evalProgStmt_callRet_err (prog : Prog) (fuel : Nat)
    (dst f : String) (xs : List String) (ρ : Env)
    (vs : List Value) (callee : Func) (e : Panic)
    (hargs : lookupArgs ρ xs = some vs)
    (hfind : findFunc prog f = some callee)
    (hcall : evalFuncFuel fuel callee vs = .error e) :
    evalProgStmt prog fuel (.callRet dst f xs) ρ = .error e := by
  simp [evalProgStmt, hargs, hfind, hcall]

/-- `callRet` to an unknown callee is rejected, never silently modeled. -/
theorem evalProgStmt_callRet_unknown (prog : Prog) (fuel : Nat)
    (dst f : String) (xs : List String) (ρ : Env) (vs : List Value)
    (hargs : lookupArgs ρ xs = some vs)
    (hfind : findFunc prog f = none) :
    evalProgStmt prog fuel (.callRet dst f xs) ρ =
      .error .AssertFail := by
  simp [evalProgStmt, hargs, hfind]

/-- `callRet` with unbound actuals is `Uninit`. -/
theorem evalProgStmt_callRet_unbound (prog : Prog) (fuel : Nat)
    (dst f : String) (xs : List String) (ρ : Env)
    (hargs : lookupArgs ρ xs = none) :
    evalProgStmt prog fuel (.callRet dst f xs) ρ = .error .Uninit := by
  simp [evalProgStmt, hargs]

/-- Whole-program function semantics: bind, run the body under the program,
    demand a `return` (falling off the end is `AssertFail`, as before). -/
def evalProgFunc (prog : Prog) (fuel : Nat) (f : Func)
    (args : List Value) : Result Value :=
  match bindArgs f.args args with
  | none => .error .AssertFail
  | some ρ =>
    match evalProgStmt prog fuel f.body ρ with
    | .error e => .error e
    | .ok (_, .returned v) => .ok v
    | .ok (_, .broke) => .error .AssertFail
    | .ok (_, .continued) => .error .AssertFail
    | .ok (_, .fellThrough) => .error .AssertFail

theorem evalProgFunc_arity (prog : Prog) (fuel : Nat) (f : Func)
    (args : List Value) (h : bindArgs f.args args = none) :
    evalProgFunc prog fuel f args = .error .AssertFail := by
  simp [evalProgFunc, h]

/-- `seq` short-circuits on error in the first component (any fuel). -/
theorem evalStmtFuel_seq_err (f : Nat) (a b : CStmt)
    (ρ : Env) (e : Panic)
    (h : evalStmtFuel f a ρ = .error e) :
    evalStmtFuel f (.seq a b) ρ = .error e := by
  cases f with
  | zero =>
    simp only [evalStmtFuel, evalStmtZero] at h ⊢
    simp only [evalStmtWith, h]
  | succ g =>
    simp only [evalStmtFuel] at h ⊢
    simp only [evalStmtWith, h]

/-- `seq` threads the environment on fall-through (any fuel). -/
theorem evalStmtFuel_seq_fallthrough (f : Nat) (a b : CStmt)
    (ρ ρ' : Env)
    (h : evalStmtFuel f a ρ = .ok (ρ', .fellThrough)) :
    evalStmtFuel f (.seq a b) ρ = evalStmtFuel f b ρ' := by
  cases f with
  | zero =>
    simp only [evalStmtFuel, evalStmtZero] at h ⊢
    simp only [evalStmtWith, h]
  | succ g =>
    simp only [evalStmtFuel] at h ⊢
    simp only [evalStmtWith, h]

/-! ## `break_` / `continue_` composition (S3a) -/

/-- `break_` signals at any fuel. -/
theorem evalStmtFuel_break (f : Nat) (ρ : Env) :
    evalStmtFuel f .break_ ρ = .ok (ρ, .broke) := by
  cases f <;> rfl

/-- `continue_` signals at any fuel. -/
theorem evalStmtFuel_continue (f : Nat) (ρ : Env) :
    evalStmtFuel f .continue_ ρ = .ok (ρ, .continued) := by
  cases f <;> rfl

/-- `seq` propagates `broke` (the second component never runs). -/
theorem evalStmtFuel_seq_broke (f : Nat) (a b : CStmt)
    (ρ ρ' : Env)
    (h : evalStmtFuel f a ρ = .ok (ρ', .broke)) :
    evalStmtFuel f (.seq a b) ρ = .ok (ρ', .broke) := by
  cases f with
  | zero =>
    simp only [evalStmtFuel, evalStmtZero] at h ⊢
    simp only [evalStmtWith, h]
  | succ g =>
    simp only [evalStmtFuel] at h ⊢
    simp only [evalStmtWith, h]

/-- `seq` propagates `continued` (the second component never runs). -/
theorem evalStmtFuel_seq_continued (f : Nat) (a b : CStmt)
    (ρ ρ' : Env)
    (h : evalStmtFuel f a ρ = .ok (ρ', .continued)) :
    evalStmtFuel f (.seq a b) ρ = .ok (ρ', .continued) := by
  cases f with
  | zero =>
    simp only [evalStmtFuel, evalStmtZero] at h ⊢
    simp only [evalStmtWith, h]
  | succ g =>
    simp only [evalStmtFuel] at h ⊢
    simp only [evalStmtWith, h]

/-- A `break_` escaping the function body is `AssertFail`. -/
theorem evalFuncFuel_broke (fuel : Nat) (f : Func) (ρ : Env)
    (hbind : bindArgs f.args [] = some ρ)
    (hbody : evalStmtFuel fuel f.body ρ = .ok (ρ, .broke)) :
    evalFuncFuel fuel f [] = .error .AssertFail := by
  simp [evalFuncFuel, hbind, hbody]

/-- A `continue_` escaping the function body is `AssertFail`. -/
theorem evalFuncFuel_continued (fuel : Nat) (f : Func) (ρ : Env)
    (hbind : bindArgs f.args [] = some ρ)
    (hbody : evalStmtFuel fuel f.body ρ = .ok (ρ, .continued)) :
    evalFuncFuel fuel f [] = .error .AssertFail := by
  simp [evalFuncFuel, hbind, hbody]

/-- `seq` short-circuits on error in the first component. -/
theorem evalProgStmt_seq_err (prog : Prog) (fuel : Nat) (a b : CStmt)
    (ρ : Env) (e : Panic)
    (h : evalProgStmt prog fuel a ρ = .error e) :
    evalProgStmt prog fuel (.seq a b) ρ = .error e := by
  simp only [evalProgStmt, h]

/-- `seq` threads the environment on fall-through. -/
theorem evalProgStmt_seq_fallthrough (prog : Prog) (fuel : Nat) (a b : CStmt)
    (ρ ρ' : Env)
    (h : evalProgStmt prog fuel a ρ = .ok (ρ', .fellThrough)) :
    evalProgStmt prog fuel (.seq a b) ρ =
      evalProgStmt prog fuel b ρ' := by
  simp only [evalProgStmt, h]

/-- `seq` short-circuits on `returned` in the first component (N4b: the
    early-return branch of `scope_early`; the trailing statements never
    run, exactly like the C++ early `return`). -/
theorem evalProgStmt_seq_returned (prog : Prog) (fuel : Nat) (a b : CStmt)
    (ρ ρ' : Env) (v : Value)
    (h : evalProgStmt prog fuel a ρ = .ok (ρ', .returned v)) :
    evalProgStmt prog fuel (.seq a b) ρ = .ok (ρ', .returned v) := by
  simp only [evalProgStmt, h]

/-- `if_` on `true` runs the branch at program level (N4b: the
    `scope_early` early-return branch contains a `callRet`, so the
    branch must evaluate with `evalProgStmt` — the statement-level
    `call` stub would be unsound here). -/
theorem evalProgStmt_if_true (prog : Prog) (fuel : Nat)
    (c : CExpr) (t e : CStmt) (ρ : Env)
    (h : evalExpr c ρ = .ok (.b true)) :
    evalProgStmt prog fuel (.if_ c t e) ρ =
      evalProgStmt prog fuel t ρ := by
  simp only [evalProgStmt, h]

/-- `if_` on `false` runs the else-branch at program level. -/
theorem evalProgStmt_if_false (prog : Prog) (fuel : Nat)
    (c : CExpr) (t e : CStmt) (ρ : Env)
    (h : evalExpr c ρ = .ok (.b false)) :
    evalProgStmt prog fuel (.if_ c t e) ρ =
      evalProgStmt prog fuel e ρ := by
  simp only [evalProgStmt, h]

/-- `return_` under a program delegates to the old evaluator. -/
theorem evalProgStmt_return (prog : Prog) (fuel : Nat) (e : CExpr)
    (ρ : Env) (v : Value)
    (h : evalExpr e ρ = .ok v) :
    evalProgStmt prog fuel (.return_ e) ρ = .ok (ρ, .returned v) := by
  have hfuel := evalStmtFuel_return fuel e ρ v h
  simp only [evalProgStmt, hfuel]

/-- `cleanup` evaluates exactly its body (M2b: the `cleanup normal`
    region is a trivial-dtor call, a no-op, so normal exit just runs the
    scope; the trailing `cir.trap` is unreachable and unmodeled). -/
theorem evalStmtFuel_cleanup (f : Nat) (body : CStmt) (ρ : Env) :
    evalStmtFuel f (.cleanup body) ρ = evalStmtFuel f body ρ := by
  cases f <;> rfl

/-- `cleanup` under a program evaluates exactly its body (M2b: the scope
    holds `callRet`s, so the program evaluator must recurse, not
    delegate to the call-free `evalStmtFuel`). -/
theorem evalProgStmt_cleanup (prog : Prog) (fuel : Nat) (body : CStmt)
    (ρ : Env) :
    evalProgStmt prog fuel (.cleanup body) ρ =
      evalProgStmt prog fuel body ρ := rfl
