/-
Circe.Eval.Core — values, environments, loan state, and the pure
expression evaluator (`evalExpr`); the statement + program layers live
in `Circe.Eval.Stmt`.
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
    the S1 `sum_array` precedent bundled into one value; N4d-iii).
    `std::vector<int32_t>` reads are `stdVecVal` (the reified element
    words; same `sharedBorrow` snapshot story over the heap triple —
    the `_M_start` load path fuses into the read, so the triple
    itself never materializes; N4d-iv-a, reads only).
    `std::vector<int32_t>` growth leaves are `stdVecOwned` (the
    uniquely-owned heap triple: `buf` is the `Vec32` storage block
    with its affine token, `len` / `cap` are the reified
    `_M_finish - _M_start` / `_M_end_of_storage - _M_start` element
    counts; N4d-iv-b1). Iterators over the triple erase to `u64`
    offsets into `buf` (`_M_start` is `0`, `_M_finish` is `len`,
    `_M_end_of_storage` is `cap`); a null buffer is the
    `len = cap = 0` triple (empty storage — the `_M_allocate(0)`
    null and the default-ctor null coincide, so the `n == 0` branch
    builds the same value as fresh storage). -/
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
  | stdVecVal : List (BitVec 32) → Value
  | stdVecOwned : Vec32 → Nat → Nat → Value
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
  | .usub a b, ρ =>
    match evalExpr a ρ, evalExpr b ρ with
    | .ok (.u32 x), .ok (.u32 y) => .ok (.u32 (x - y))
    | .ok (.u64 x), .ok (.u64 y) => .ok (.u64 (x - y))
    | .ok _, .ok _ => .error .AssertFail
    | .error e, _ => .error e
    | _, .error e => .error e
  | .s64diff a b, ρ =>
    match evalExpr a ρ, evalExpr b ρ with
    | .ok (.u64 x), .ok (.u64 y) => .ok (.i64 (x - y))
    | .ok _, .ok _ => .error .AssertFail
    | .error e, _ => .error e
    | _, .error e => .error e
  | .tif c t e, ρ =>
    match evalExpr c ρ with
    | .error err => .error err
    | .ok (.b true) => evalExpr t ρ
    | .ok (.b false) => evalExpr e ρ
    | .ok _ => .error .AssertFail
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
  | .une a b, ρ =>
    match evalExpr a ρ, evalExpr b ρ with
    | .ok (.u32 x), .ok (.u32 y) => .ok (.b (x != y))
    | .ok (.u64 x), .ok (.u64 y) => .ok (.b (x != y))
    | .ok (.i32 x), .ok (.i32 y) => .ok (.b (x != y))
    | .ok (.i64 x), .ok (.i64 y) => .ok (.b (x != y))
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
  | .stdVecLen s, ρ =>
    match envLookup ρ s with
    | none => .error .Uninit
    | some (.stdVecVal l) => .ok (.u64 (BitVec.ofNat 64 l.length))
    | some _ => .error .AssertFail
  | .stdVecAt s ie, ρ =>
    match envLookup ρ s with
    | none => .error .Uninit
    | some (.stdVecVal l) =>
      match evalExpr ie ρ with
      | .error e => .error e
      | .ok (.u64 i) =>
        match l[i.toNat]? with
        | some x => .ok (.i32 x)
        | none => .error .OOB
      | .ok _ => .error .AssertFail
    | some _ => .error .AssertFail
  | .vgrowLen s, ρ =>
    match envLookup ρ s with
    | none => .error .Uninit
    | some (.stdVecOwned _ len _) => .ok (.u64 (BitVec.ofNat 64 len))
    | some _ => .error .AssertFail
  | .vgrowCap s, ρ =>
    match envLookup ρ s with
    | none => .error .Uninit
    | some (.stdVecOwned _ _ cap) => .ok (.u64 (BitVec.ofNat 64 cap))
    | some _ => .error .AssertFail
  | .vgrowAt s ie, ρ =>
    match envLookup ρ s with
    | none => .error .Uninit
    | some (.stdVecOwned b len _) =>
      match evalExpr ie ρ with
      | .error e => .error e
      | .ok (.u64 i) =>
        if b.freed then .error .AssertFail
        else match b.val[i.toNat]? with
        | some x => if i.toNat < len then .ok (.i32 x) else .error .OOB
        | none => .error .OOB
      | .ok _ => .error .AssertFail
    | some _ => .error .AssertFail
  | .vgrowNew ce, ρ =>
    match evalExpr ce ρ with
    | .error e => .error e
    | .ok (.u64 n) =>
      match vecNew n.toNat with
      | .error e => .error e
      | .ok v => .ok (.stdVecOwned v 0 n.toNat)
    | .ok _ => .error .AssertFail
  | .vgrowSetLen s e, ρ =>
    match envLookup ρ s with
    | none => .error .Uninit
    | some (.stdVecOwned b _ cap) =>
      match evalExpr e ρ with
      | .error err => .error err
      | .ok (.u64 n) => .ok (.stdVecOwned b n.toNat cap)
      | .ok _ => .error .AssertFail
    | some _ => .error .AssertFail
  | .u64ofI64 e, ρ =>
    match evalExpr e ρ with
    | .error err => .error err
    | .ok (.i64 d) => .ok (.u64 d)
    | .ok _ => .error .AssertFail
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

/-- `uadd` on two `u64`-valued expressions (N4d-iv-b1: `_M_check_len`
    `__len + max(__len, __n)` shape). -/
theorem evalExpr_uadd_u64 (e₁ e₂ : CExpr) (ρ : Env) (x y : BitVec 64)
    (h₁ : evalExpr e₁ ρ = .ok (.u64 x))
    (h₂ : evalExpr e₂ ρ = .ok (.u64 y)) :
    evalExpr (.uadd e₁ e₂) ρ = .ok (.u64 (x + y)) := by
  simp [evalExpr, h₁, h₂]

/-- `uadd` type mismatches are rejected. -/
theorem evalExpr_uadd_mismatch (ρ : Env) :
    evalExpr (.uadd (.lit (.u32 0)) (.lit (.b true))) ρ =
      .error .AssertFail := by
  simp [evalExpr, litVal]

/-- `usub` on two `u64` literals wraps (N4d-iv-b1). -/
theorem evalExpr_usub64_lit (x y : BitVec 64) (ρ : Env) :
    evalExpr (.usub (.lit (.u64 x)) (.lit (.u64 y))) ρ =
      .ok (.u64 (x - y)) := by
  simp [evalExpr, litVal]

/-- `usub` with a `u64` literal LHS and a `u64`-valued RHS expression
    (N4d-iv-b1: `_M_check_len` / `_M_allocate` shapes). -/
theorem evalExpr_usub_u64 (x y : BitVec 64) (e : CExpr) (ρ : Env)
    (h : evalExpr e ρ = .ok (.u64 y)) :
    evalExpr (.usub (.lit (.u64 x)) e) ρ = .ok (.u64 (x - y)) := by
  simp [evalExpr, litVal, h]

/-- `usub` on two `u64`-valued expressions (N4d-iv-b1: `miEl` fused
    `cir.minus` + `ptr_stride` over erased element indices). -/
theorem evalExpr_usub_u64u64 (e₁ e₂ : CExpr) (ρ : Env) (x y : BitVec 64)
    (h₁ : evalExpr e₁ ρ = .ok (.u64 x))
    (h₂ : evalExpr e₂ ρ = .ok (.u64 y)) :
    evalExpr (.usub e₁ e₂) ρ = .ok (.u64 (x - y)) := by
  simp [evalExpr, h₁, h₂]

/-- `usub` with a `u64`-valued LHS and a `u64` literal RHS
    (N4d-iv-b1: `back` fused `len - 1`, wrapping on empty). -/
theorem evalExpr_u64_usub (x y : BitVec 64) (e : CExpr) (ρ : Env)
    (h : evalExpr e ρ = .ok (.u64 x)) :
    evalExpr (.usub e (.lit (.u64 y))) ρ = .ok (.u64 (x - y)) := by
  simp [evalExpr, litVal, h]

/-- `usub` on two `u32` literals wraps (N4d-iv-b1). -/
theorem evalExpr_usub_lit (x y : BitVec 32) (ρ : Env) :
    evalExpr (.usub (.lit (.u32 x)) (.lit (.u32 y))) ρ =
      .ok (.u32 (x - y)) := by
  simp [evalExpr, litVal]

/-- `usub` type mismatches are rejected. -/
theorem evalExpr_usub_mismatch (ρ : Env) :
    evalExpr (.usub (.lit (.u32 0)) (.lit (.b true))) ρ =
      .error .AssertFail := by
  simp [evalExpr, litVal]

/-- `s64diff` on two `u64` offsets delivers the bit-exact difference
    as `s64` (N4d-iv-b1: fused `cir.ptr_diff`). -/
theorem evalExpr_s64diff_lit (x y : BitVec 64) (ρ : Env) :
    evalExpr (.s64diff (.lit (.u64 x)) (.lit (.u64 y))) ρ =
      .ok (.i64 (x - y)) := by
  simp [evalExpr, litVal]

/-- `s64diff` on two `u64`-valued expressions (N4d-iv-b1: `mi` fused
    double-`base` + `ptr_diff` over erased element indices). -/
theorem evalExpr_s64diff_u64u64 (e₁ e₂ : CExpr) (ρ : Env)
    (x y : BitVec 64)
    (h₁ : evalExpr e₁ ρ = .ok (.u64 x))
    (h₂ : evalExpr e₂ ρ = .ok (.u64 y)) :
    evalExpr (.s64diff e₁ e₂) ρ = .ok (.i64 (x - y)) := by
  simp [evalExpr, h₁, h₂]

/-- `s64diff` type mismatches are rejected. -/
theorem evalExpr_s64diff_mismatch (ρ : Env) :
    evalExpr (.s64diff (.lit (.u64 0)) (.lit (.b true))) ρ =
      .error .AssertFail := by
  simp [evalExpr, litVal]

/-- `tif` on a true condition evaluates the then-branch. -/
theorem evalExpr_tif_true (c t e : CExpr) (ρ : Env)
    (hc : evalExpr c ρ = .ok (.b true)) :
    evalExpr (.tif c t e) ρ = evalExpr t ρ := by
  simp [evalExpr, hc]

/-- `tif` on a false condition evaluates the else-branch. -/
theorem evalExpr_tif_false (c t e : CExpr) (ρ : Env)
    (hc : evalExpr c ρ = .ok (.b false)) :
    evalExpr (.tif c t e) ρ = evalExpr e ρ := by
  simp [evalExpr, hc]

/-- `tif` on a non-boolean condition is rejected. -/
theorem evalExpr_tif_nonbool (c t e : CExpr) (ρ : Env) (x : BitVec 32)
    (hc : evalExpr c ρ = .ok (.i32 x)) :
    evalExpr (.tif c t e) ρ = .error .AssertFail := by
  simp [evalExpr, hc]

/-- `tif` propagates condition errors. -/
theorem evalExpr_tif_err (c t e : CExpr) (ρ : Env) (err : Panic)
    (hc : evalExpr c ρ = .error err) :
    evalExpr (.tif c t e) ρ = .error err := by
  simp [evalExpr, hc]

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

/-- `ult` on two `u64`-valued expressions (N4d-iv-b1: `_M_check_len` /
    `_M_allocate` shapes). -/
theorem evalExpr_ult_u64 (e₁ e₂ : CExpr) (ρ : Env) (x y : BitVec 64)
    (h₁ : evalExpr e₁ ρ = .ok (.u64 x))
    (h₂ : evalExpr e₂ ρ = .ok (.u64 y)) :
    evalExpr (.ult e₁ e₂) ρ = .ok (.b (x.ult y)) := by
  simp [evalExpr, h₁, h₂]

/-- `ult` with a `u64` literal LHS and a `u64`-valued RHS expression
    (N4d-iv-b1: `_M_check_len` second-guard shape). -/
theorem evalExpr_ult_u64lit (x y : BitVec 64) (e : CExpr) (ρ : Env)
    (h : evalExpr e ρ = .ok (.u64 y)) :
    evalExpr (.ult (.lit (.u64 x)) e) ρ = .ok (.b (x.ult y)) := by
  simp [evalExpr, litVal, h]

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

/-- `stdVecLen` of a vector delivers its length as a `u64` word. -/
theorem evalExpr_stdVecLen_some (s : String) (ρ : Env)
    (l : List (BitVec 32))
    (hs : envLookup ρ s = some (.stdVecVal l)) :
    evalExpr (.stdVecLen s) ρ = .ok (.u64 (BitVec.ofNat 64 l.length)) := by
  simp [evalExpr, hs]

/-- `stdVecLen` of a non-vector is rejected, never silently modeled. -/
theorem evalExpr_stdVecLen_notval (s : String) (v : BitVec 32) (ρ : Env)
    (hs : envLookup ρ s = some (.i32 v)) :
    evalExpr (.stdVecLen s) ρ = .error .AssertFail := by
  simp [evalExpr, hs]

/-- `stdVecAt` in bounds delivers the word. -/
theorem evalExpr_stdVecAt_some (s : String) (ie : CExpr) (ρ : Env)
    (l : List (BitVec 32)) (i : BitVec 64) (x : BitVec 32)
    (hs : envLookup ρ s = some (.stdVecVal l))
    (hi : evalExpr ie ρ = .ok (.u64 i))
    (hget : l[i.toNat]? = some x) :
    evalExpr (.stdVecAt s ie) ρ = .ok (.i32 x) := by
  simp [evalExpr, hs, hi, hget]

/-- `stdVecAt` off the end is `OOB` (mirrors `spanAt`). -/
theorem evalExpr_stdVecAt_oob (s : String) (ie : CExpr) (ρ : Env)
    (l : List (BitVec 32)) (i : BitVec 64)
    (hs : envLookup ρ s = some (.stdVecVal l))
    (hi : evalExpr ie ρ = .ok (.u64 i))
    (hget : l[i.toNat]? = none) :
    evalExpr (.stdVecAt s ie) ρ = .error .OOB := by
  simp [evalExpr, hs, hi, hget]

/-- `stdVecAt` with a non-`u64` index is rejected. -/
theorem evalExpr_stdVecAt_nonu64 (s : String) (ie : CExpr) (ρ : Env)
    (l : List (BitVec 32)) (v : BitVec 32)
    (hs : envLookup ρ s = some (.stdVecVal l))
    (hi : evalExpr ie ρ = .ok (.i32 v)) :
    evalExpr (.stdVecAt s ie) ρ = .error .AssertFail := by
  simp [evalExpr, hs, hi]

/-- `stdVecAt` of a non-vector is rejected, never silently modeled. -/
theorem evalExpr_stdVecAt_notval (s : String) (ie : CExpr) (v : BitVec 32)
    (ρ : Env)
    (hs : envLookup ρ s = some (.i32 v)) :
    evalExpr (.stdVecAt s ie) ρ = .error .AssertFail := by
  simp [evalExpr, hs]

/-- `vgrowLen` of an owned triple delivers its length as a `u64` word
    (N4d-iv-b1). -/
theorem evalExpr_vgrowLen_some (s : String) (ρ : Env)
    (b : Vec32) (len cap : Nat)
    (hs : envLookup ρ s = some (.stdVecOwned b len cap)) :
    evalExpr (.vgrowLen s) ρ = .ok (.u64 (BitVec.ofNat 64 len)) := by
  simp [evalExpr, hs]

/-- `vgrowLen` of a non-triple is rejected, never silently modeled. -/
theorem evalExpr_vgrowLen_notval (s : String) (v : BitVec 32) (ρ : Env)
    (hs : envLookup ρ s = some (.i32 v)) :
    evalExpr (.vgrowLen s) ρ = .error .AssertFail := by
  simp [evalExpr, hs]

/-- `vgrowCap` of an owned triple delivers its capacity as a `u64` word
    (N4d-iv-b1). -/
theorem evalExpr_vgrowCap_some (s : String) (ρ : Env)
    (b : Vec32) (len cap : Nat)
    (hs : envLookup ρ s = some (.stdVecOwned b len cap)) :
    evalExpr (.vgrowCap s) ρ = .ok (.u64 (BitVec.ofNat 64 cap)) := by
  simp [evalExpr, hs]

/-- `vgrowCap` of a non-triple is rejected, never silently modeled. -/
theorem evalExpr_vgrowCap_notval (s : String) (v : BitVec 32) (ρ : Env)
    (hs : envLookup ρ s = some (.i32 v)) :
    evalExpr (.vgrowCap s) ρ = .error .AssertFail := by
  simp [evalExpr, hs]

/-- `vgrowAt` in bounds delivers the word (N4d-iv-b1). -/
theorem evalExpr_vgrowAt_some (s : String) (ie : CExpr) (ρ : Env)
    (b : Vec32) (len cap : Nat) (i : BitVec 64) (x : BitVec 32)
    (hs : envLookup ρ s = some (.stdVecOwned b len cap))
    (hi : evalExpr ie ρ = .ok (.u64 i))
    (hlive : b.freed = false)
    (hget : b.val[i.toNat]? = some x)
    (hlt : i.toNat < len) :
    evalExpr (.vgrowAt s ie) ρ = .ok (.i32 x) := by
  simp [evalExpr, hs, hi, hlive, hget, hlt]

/-- `vgrowAt` at or past the length is `OOB` (uninitialized slots are
    not readable, even when the storage is live). -/
theorem evalExpr_vgrowAt_oob_len (s : String) (ie : CExpr) (ρ : Env)
    (b : Vec32) (len cap : Nat) (i : BitVec 64) (x : BitVec 32)
    (hs : envLookup ρ s = some (.stdVecOwned b len cap))
    (hi : evalExpr ie ρ = .ok (.u64 i))
    (hlive : b.freed = false)
    (hget : b.val[i.toNat]? = some x)
    (hlt : ¬ i.toNat < len) :
    evalExpr (.vgrowAt s ie) ρ = .error .OOB := by
  simp [evalExpr, hs, hi, hlive, hget, hlt]

/-- `vgrowAt` past the storage words is `OOB`. -/
theorem evalExpr_vgrowAt_oob_miss (s : String) (ie : CExpr) (ρ : Env)
    (b : Vec32) (len cap : Nat) (i : BitVec 64)
    (hs : envLookup ρ s = some (.stdVecOwned b len cap))
    (hi : evalExpr ie ρ = .ok (.u64 i))
    (hlive : b.freed = false)
    (hget : b.val[i.toNat]? = none) :
    evalExpr (.vgrowAt s ie) ρ = .error .OOB := by
  simp [evalExpr, hs, hi, hlive, hget]

/-- `vgrowAt` on a consumed buffer is `AssertFail` (use-after-free is
    never a silent read). -/
theorem evalExpr_vgrowAt_freed (s : String) (ie : CExpr) (ρ : Env)
    (b : Vec32) (len cap : Nat) (i : BitVec 64)
    (hs : envLookup ρ s = some (.stdVecOwned b len cap))
    (hi : evalExpr ie ρ = .ok (.u64 i))
    (hfree : b.freed = true) :
    evalExpr (.vgrowAt s ie) ρ = .error .AssertFail := by
  simp [evalExpr, hs, hi, hfree]

/-- `vgrowAt` with a non-`u64` index is rejected. -/
theorem evalExpr_vgrowAt_nonu64 (s : String) (ie : CExpr) (ρ : Env)
    (b : Vec32) (len cap : Nat) (v : BitVec 32)
    (hs : envLookup ρ s = some (.stdVecOwned b len cap))
    (hi : evalExpr ie ρ = .ok (.i32 v)) :
    evalExpr (.vgrowAt s ie) ρ = .error .AssertFail := by
  simp [evalExpr, hs, hi]

/-- `vgrowAt` of a non-triple is rejected, never silently modeled. -/
theorem evalExpr_vgrowAt_notval (s : String) (ie : CExpr) (v : BitVec 32)
    (ρ : Env)
    (hs : envLookup ρ s = some (.i32 v)) :
    evalExpr (.vgrowAt s ie) ρ = .error .AssertFail := by
  simp [evalExpr, hs]

/-- `vgrowNew` on a `u64` capacity allocates a zeroed live buffer with
    length `0` (N4d-iv-b1: `_M_allocate` fused). -/
theorem evalExpr_vgrowNew_lit (n : BitVec 64) (ρ : Env) :
    evalExpr (.vgrowNew (.lit (.u64 n))) ρ =
      .ok (.stdVecOwned ⟨List.replicate n.toNat 0, false⟩ 0 n.toNat) := by
  simp [evalExpr, litVal, vecNew]

/-- `vgrowNew` on a `u64`-valued capacity expression (`vecNew` is total,
    so no side conditions; N4d-iv-b1: `_M_allocate` fused). -/
theorem evalExpr_vgrowNew_u64 (e : CExpr) (ρ : Env) (n : BitVec 64)
    (h : evalExpr e ρ = .ok (.u64 n)) :
    evalExpr (.vgrowNew e) ρ =
      .ok (.stdVecOwned ⟨List.replicate n.toNat 0, false⟩ 0 n.toNat) := by
  simp [evalExpr, h, vecNew]

/-- `vgrowSetLen` on an owned triple rebuilds it with the new length
    (N4d-iv-b2: the realloc header stores fused). -/
theorem evalExpr_vgrowSetLen_hit (s : String) (e : CExpr) (ρ : Env)
    (b : Vec32) (len cap : Nat) (n : BitVec 64)
    (hs : envLookup ρ s = some (.stdVecOwned b len cap))
    (he : evalExpr e ρ = .ok (.u64 n)) :
    evalExpr (.vgrowSetLen s e) ρ =
      .ok (.stdVecOwned b n.toNat cap) := by
  simp [evalExpr, hs, he]

/-- `vgrowSetLen` of a non-triple is rejected, never silently modeled. -/
theorem evalExpr_vgrowSetLen_notval (s : String) (e : CExpr)
    (v : BitVec 32) (ρ : Env)
    (hs : envLookup ρ s = some (.i32 v)) :
    evalExpr (.vgrowSetLen s e) ρ = .error .AssertFail := by
  simp [evalExpr, hs]

/-- `vgrowSetLen` on a non-`u64` length is rejected. -/
theorem evalExpr_vgrowSetLen_nonu64 (s : String) (e : CExpr) (ρ : Env)
    (b : Vec32) (len cap : Nat) (v : BitVec 32)
    (hs : envLookup ρ s = some (.stdVecOwned b len cap))
    (he : evalExpr e ρ = .ok (.i32 v)) :
    evalExpr (.vgrowSetLen s e) ρ = .error .AssertFail := by
  simp [evalExpr, hs, he]

/-- `u64ofI64` on an `i64` word retags the same bits as `u64`
    (N4d-iv-b2: the `mi`-difference `s64 -> u64` cast fused). -/
theorem evalExpr_u64ofI64_hit (e : CExpr) (ρ : Env) (d : BitVec 64)
    (h : evalExpr e ρ = .ok (.i64 d)) :
    evalExpr (.u64ofI64 e) ρ = .ok (.u64 d) := by
  simp [evalExpr, h]

/-- `u64ofI64` on a non-`i64` word is rejected. -/
theorem evalExpr_u64ofI64_mismatch (e : CExpr) (ρ : Env)
    (n : BitVec 64)
    (h : evalExpr e ρ = .ok (.u64 n)) :
    evalExpr (.u64ofI64 e) ρ = .error .AssertFail := by
  simp [evalExpr, h]

/-- `vgrowNew` on a non-`u64` capacity is rejected. -/
theorem evalExpr_vgrowNew_mismatch (ρ : Env) :
    evalExpr (.vgrowNew (.lit (.i32 0))) ρ = .error .AssertFail := by
  simp [evalExpr, litVal]

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

