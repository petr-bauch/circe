/-
Circe.Eval.Stmt — statement + program evaluation over `Circe.Eval.Core`
(fuel-bounded `while_`, S1 DAG calls, S3a loop-scoped `break_` /
`continue_`, whole-function `evalFunc` / `evalProgFunc`).
-/
import Circe.Base
import Circe.CoreIR
import Circe.Eval.Core
import Lean.Elab.Tactic
import Lean.Parser.Extension

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

/-- Composer fuel split (N5a): from a closed/composer bound `k + 1 ≤ F`,
    split `F = F' + 1` with the stepped-down bound `k ≤ F'` — one
    `obtain` replacing the `obtain ⟨F', rfl⟩ ... + have ... := by omega`
    pair at the six b2 composer sites (`evalProgFunc`/`memEvalProgFunc`
    for emplace/push_back/entry). The arithmetic lives here; call sites
    name only `F'`, `hF'`, and `k`. -/
theorem fuel_step_down {F : Nat} (k : Nat) (h : k + 1 ≤ F) :
    ∃ F', F = F' + 1 ∧ k ≤ F' := by
  obtain ⟨F', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : F ≠ 0)
  exact ⟨F', rfl, by omega⟩

/-- Program-step cascade (N5b): the registered cascade core — evaluator
    unfolding + `Except.map` normalization (the `Span.lean` precedent) —
    with per-step hypotheses as arguments. Replaces the bespoke
    `simp only [evalExpr, <hyps>, Except.map]` lines at the span/read/
    entry steps; new composers close steps with this (+ N5a) instead of
    re-listing the set. The evaluator is an argument so mem-side steps
    (`memEvalExpr`) share the core. -/
elab "cir_step " ev:ident " [" hs:ident,* "]" : tactic => do
  -- Reparse (not splice): `simp only` arg kinds reject spliced idents,
  -- so elaborate the exact surface string at the use site instead.
  let names := ev :: hs.getElems.toList
  let code := "simp only [" ++
    String.intercalate ", "
      ((names.map fun s => (Lean.Syntax.getId s.raw).toString) ++
        ["Except.map"]) ++ "]"
  let .ok stx := Lean.Parser.runParserCategory (← Lean.MonadEnv.getEnv) `tactic code
    | throwError "cir_step: could not parse {code}"
  Lean.Elab.Tactic.evalTactic stx

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
  | .vgrowSet x ie ve, ρ =>
    match evalExpr ie ρ, evalExpr ve ρ with
    | .ok (.u64 i), .ok (.i32 xv) =>
      match envLookup ρ x with
      | none => .error .Uninit
      | some (.stdVecOwned b len cap) =>
        match vecSet b i.toNat xv with
        | .error e => .error e
        | .ok b' =>
          match envUpdate ρ x (.stdVecOwned b' len cap) with
          | none => .error .Uninit
          | some ρ' => .ok (ρ', .fellThrough)
      | some _ => .error .AssertFail
    | .ok _, .ok _ => .error .AssertFail
    | .error e, _ => .error e
    | _, .error e => .error e
  | .arrSet x ie ve, ρ =>
    match evalExpr ie ρ, evalExpr ve ρ with
    | .ok (.u64 i), .ok (.u32 xv) =>
      match envLookup ρ x with
      | none => .error .Uninit
      | some (.arr32 l) =>
        match l[i.toNat]? with
        | none => .error .OOB
        | some _ =>
          match envUpdate ρ x (.arr32 (l.set i.toNat xv)) with
          | none => .error .Uninit
          | some ρ' => .ok (ρ', .fellThrough)
      | some _ => .error .AssertFail
    | .ok _, .ok _ => .error .AssertFail
    | .error e, _ => .error e
    | _, .error e => .error e
  | .vgrowFree x, ρ =>
    match envLookup ρ x with
    | none => .error .Uninit
    | some (.stdVecOwned b len cap) =>
      match vecFree b with
      | .error e => .error e
      | .ok b' =>
        match envUpdate ρ x (.stdVecOwned b' len cap) with
        | none => .error .Uninit
        | some ρ' => .ok (ρ', .fellThrough)
    | some _ => .error .AssertFail
  | .fail, _ => .error .AssertFail
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
  | .callProg _ _ _, _ =>
    -- Composer calls need program context too (`evalProgStmt` runs them
    -- via `evalProgFunc`); at leaf level they are loud like `callRet`.
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

/-- `vgrowSet` stores through a live owned triple and updates the
    binding, keeping `len`/`cap` (any fuel; N4d-iv-b1: `construct`
    fused). -/
theorem evalStmtFuel_vgrowSet (f : Nat) (x : String) (ie ve : CExpr)
    (ρ : Env) (i : BitVec 64) (xv : BitVec 32)
    (b b' : Vec32) (len cap : Nat) (ρ' : Env)
    (hi : evalExpr ie ρ = .ok (.u64 i))
    (hv : evalExpr ve ρ = .ok (.i32 xv))
    (harr : envLookup ρ x = some (.stdVecOwned b len cap))
    (hset : vecSet b i.toNat xv = .ok b')
    (hu : envUpdate ρ x (.stdVecOwned b' len cap) = some ρ') :
    evalStmtFuel f (.vgrowSet x ie ve) ρ = .ok (ρ', .fellThrough) := by
  cases f <;>
    simp [evalStmtFuel, evalStmtZero, evalStmtWith, hi, hv, harr, hset, hu]

/-- `vgrowSet` errors (OOB/use-after-free) propagate (any fuel). -/
theorem evalStmtFuel_vgrowSet_err (f : Nat) (x : String) (ie ve : CExpr)
    (ρ : Env) (i : BitVec 64) (xv : BitVec 32)
    (b : Vec32) (len cap : Nat) (e : Panic)
    (hi : evalExpr ie ρ = .ok (.u64 i))
    (hv : evalExpr ve ρ = .ok (.i32 xv))
    (harr : envLookup ρ x = some (.stdVecOwned b len cap))
    (hset : vecSet b i.toNat xv = .error e) :
    evalStmtFuel f (.vgrowSet x ie ve) ρ = .error e := by
  cases f <;>
    simp [evalStmtFuel, evalStmtZero, evalStmtWith, hi, hv, harr, hset]

/-- `arrSet` writes the word and threads the env (any fuel; N9: the
    fused subscript-call + `cir.store` for the insertion-sort swap). -/
theorem evalStmtFuel_arrSet (f : Nat) (x : String) (ie ve : CExpr)
    (ρ : Env) (i : BitVec 64) (xv : BitVec 32)
    (l : List (BitVec 32)) (w : BitVec 32) (ρ' : Env)
    (hi : evalExpr ie ρ = .ok (.u64 i))
    (hv : evalExpr ve ρ = .ok (.u32 xv))
    (harr : envLookup ρ x = some (.arr32 l))
    (hget : l[i.toNat]? = some w)
    (hu : envUpdate ρ x (.arr32 (l.set i.toNat xv)) = some ρ') :
    evalStmtFuel f (.arrSet x ie ve) ρ = .ok (ρ', .fellThrough) := by
  cases f <;>
    simp [evalStmtFuel, evalStmtZero, evalStmtWith, hi, hv, harr, hget, hu]

/-- `arrSet` out-of-bounds reports `OOB` (any fuel). -/
theorem evalStmtFuel_arrSet_oob (f : Nat) (x : String) (ie ve : CExpr)
    (ρ : Env) (i : BitVec 64) (xv : BitVec 32)
    (l : List (BitVec 32))
    (hi : evalExpr ie ρ = .ok (.u64 i))
    (hv : evalExpr ve ρ = .ok (.u32 xv))
    (harr : envLookup ρ x = some (.arr32 l))
    (hget : l[i.toNat]? = none) :
    evalStmtFuel f (.arrSet x ie ve) ρ = .error .OOB := by
  cases f <;>
    simp [evalStmtFuel, evalStmtZero, evalStmtWith, hi, hv, harr, hget]

/-- `vgrowFree` consumes the triple's buffer token and updates the
    binding, keeping `len`/`cap` (any fuel; N4d-iv-b1:
    `_M_deallocate` / dtor fused). -/
theorem evalStmtFuel_vgrowFree (f : Nat) (x : String) (ρ : Env)
    (b b' : Vec32) (len cap : Nat) (ρ' : Env)
    (harr : envLookup ρ x = some (.stdVecOwned b len cap))
    (hfree : vecFree b = .ok b')
    (hu : envUpdate ρ x (.stdVecOwned b' len cap) = some ρ') :
    evalStmtFuel f (.vgrowFree x) ρ = .ok (ρ', .fellThrough) := by
  cases f <;>
    simp [evalStmtFuel, evalStmtZero, evalStmtWith, harr, hfree, hu]

/-- `vgrowFree` errors (double-free) propagate (any fuel). -/
theorem evalStmtFuel_vgrowFree_err (f : Nat) (x : String) (ρ : Env)
    (b : Vec32) (len cap : Nat) (e : Panic)
    (harr : envLookup ρ x = some (.stdVecOwned b len cap))
    (hfree : vecFree b = .error e) :
    evalStmtFuel f (.vgrowFree x) ρ = .error e := by
  cases f <;>
    simp [evalStmtFuel, evalStmtZero, evalStmtWith, harr, hfree]

/-- `fail` aborts loudly at any fuel (noreturn-throw fusion). -/
theorem evalStmtFuel_fail (f : Nat) (ρ : Env) :
    evalStmtFuel f .fail ρ = .error .AssertFail := by
  cases f <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith]

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

mutual
/-- Program statement evaluation. `callRet dst f xs` looks up the
    actuals, dispatches to the call-free callee via the old `evalFuncFuel`
    at the same fuel, and extends the environment with the result;
    `callProg dst f xs` is the depth-n twin (N4d-iv-b2: composer calls
    composer): the callee runs under `evalProgFunc` at one less fuel
    (fuel is the call-depth budget as well as the loop budget; zero fuel
    is loud), so arbitrarily deep `Prog` call DAGs evaluate;
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
  | .callProg dst f xs, ρ =>
    match lookupArgs ρ xs with
    | none => .error .Uninit
    | some vs =>
      match findFunc prog f with
      | none => .error .AssertFail
      | some callee =>
        match fuel with
        | 0 => .error .AssertFail
        | fuel + 1 =>
          match evalProgFunc prog fuel callee vs with
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
  termination_by s _ => (fuel, 0, s)

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
  termination_by (fuel, 1, f.body)
end

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

/-- `callProg` with resolved actuals + callee runs the callee under the
    program evaluator (one fuel less; N4d-iv-b2 composer calls). -/
theorem evalProgStmt_callProg_ok (prog : Prog) (fuel : Nat)
    (dst f : String) (xs : List String) (ρ : Env)
    (vs : List Value) (callee : Func) (ret : Value)
    (hargs : lookupArgs ρ xs = some vs)
    (hfind : findFunc prog f = some callee)
    (hcall : evalProgFunc prog fuel callee vs = .ok ret) :
    evalProgStmt prog (fuel + 1) (.callProg dst f xs) ρ =
      .ok (envExtend ρ dst ret, .fellThrough) := by
  simp [evalProgStmt, hargs, hfind, hcall]

/-- `callProg` propagates callee errors. -/
theorem evalProgStmt_callProg_err (prog : Prog) (fuel : Nat)
    (dst f : String) (xs : List String) (ρ : Env)
    (vs : List Value) (callee : Func) (e : Panic)
    (hargs : lookupArgs ρ xs = some vs)
    (hfind : findFunc prog f = some callee)
    (hcall : evalProgFunc prog fuel callee vs = .error e) :
    evalProgStmt prog (fuel + 1) (.callProg dst f xs) ρ = .error e := by
  simp [evalProgStmt, hargs, hfind, hcall]

/-- `callProg` to an unknown callee is rejected, never silently modeled. -/
theorem evalProgStmt_callProg_unknown (prog : Prog) (fuel : Nat)
    (dst f : String) (xs : List String) (ρ : Env) (vs : List Value)
    (hargs : lookupArgs ρ xs = some vs)
    (hfind : findFunc prog f = none) :
    evalProgStmt prog fuel (.callProg dst f xs) ρ =
      .error .AssertFail := by
  simp [evalProgStmt, hargs, hfind]

/-- `callProg` with unbound actuals is `Uninit`. -/
theorem evalProgStmt_callProg_unbound (prog : Prog) (fuel : Nat)
    (dst f : String) (xs : List String) (ρ : Env)
    (hargs : lookupArgs ρ xs = none) :
    evalProgStmt prog fuel (.callProg dst f xs) ρ = .error .Uninit := by
  simp [evalProgStmt, hargs]

/-- `callProg` at zero fuel is loud (the call-depth budget is spent). -/
theorem evalProgStmt_callProg_nofuel (prog : Prog)
    (dst f : String) (xs : List String) (ρ : Env) (vs : List Value)
    (callee : Func)
    (hargs : lookupArgs ρ xs = some vs)
    (hfind : findFunc prog f = some callee) :
    evalProgStmt prog 0 (.callProg dst f xs) ρ =
      .error .AssertFail := by
  simp [evalProgStmt, hargs, hfind]

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
      evalProgStmt prog fuel body ρ := by
  simp only [evalProgStmt]
