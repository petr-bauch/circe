/-
Circe.Emit.VecMarkCount — G1 visited-mark idiom: the `mark_count`
entry over the N4d-iv-c `at()` reads.

The corpus (`tests/cpp/mark_count.cpp`: const-matrix `m`,
mut-visited `vis`, `u64` vertex `u`, `i32` out) captures the entry +
`size` + const-`at()` + mut-`at()` + `_M_range_check` + both
`operator[]` leaves. The entry functionalizes to a fused seed (the
mut-`at()` write behind its `ult` guard, the `at()`-throw
precedent) plus a call-free fused `while_` loop: per iteration the
gate `m[i] != 0` selects the checked-add accumulation of the `vis`
read, and the index advances. A `callRet`-per-iteration composer
was considered and rejected: `while_` bodies delegate to the
call-free evaluator (`evalStmtFuel`), so calls cannot appear
inside loop bodies — fusion is structural, not a shortcut.

Error precedence: the seed `fail` is the `at()`-throw precedent
(`AssertFail`); the loop bound `i < vis.size` subsumes the `vis`
guard, so the `vis` leg is dead-but-propagated; the `m` leg is
live — `m` shorter than `vis` throws in C++, modeled as the
evaluator's own `OOB` (the `Array`/`find` precedent, not a fused
guard); the live arithmetic failure is the `nsw` overflow. The
forward is therefore the gated dual-list fold.
-/
import Circe.Emit.VecRead
import Circe.Emit.VecAt

/-! ## G1b: `vector<char>` instantiation names -/

/-- Mangled callee names in `tests/cpp/mark_count_c.cpp` (the
    char-width instantiation: `std::vector<char>`; element loads are
    `!s8i`, and integer promotion to `i32` happens in the entry via
    `cir.cast integral %x : !s8i -> !s32i`, never as native
    small-width arithmetic — the S3b promotion precedent). The leaf
    CoreIR is the width-agnostic int family (`stdVecLen` /
    `stdVecAt` fuse over the reified words; the struct layout is
    never projected), so these names only route Gate dispatch; the
    entry CoreIR is `vecMarkCountFunc` under its own mangled name
    (the sext is fused into the `stdVecAt` read, the `viewAt`
    precedent). Reification contract: chars reify by sign-extension
    (`c : Int` with `-128 ≤ c ≤ 127` maps to `BitVec.ofInt 32 c`);
    the seed stores `1`, exactly representable, so the store/read
    round-trip is the identity on the reified range. -/
def charVecSizeName : String :=
  "_ZNKSt6vectorIcSaIcEE4sizeEv"
def charVecIndexName : String :=
  "_ZNKSt6vectorIcSaIcEEixEm"
def charVecIndexMutName : String :=
  "_ZNSt6vectorIcSaIcEEixEm"
def charVecRangeCheckName : String :=
  "_ZNKSt6vectorIcSaIcEE14_M_range_checkEm"
def charVecAtName : String :=
  "_ZNKSt6vectorIcSaIcEE2atEm"
def charVecAtMutName : String :=
  "_ZNSt6vectorIcSaIcEE2atEm"
def markCountCName : String :=
  "_Z12mark_count_cRKSt6vectorIcSaIcEERS1_m"

/-! ## G1: `mark_count` entry -/

/-- Mangled name of the visited-mark entry. -/
def vecMarkCountName : String :=
  "_Z10mark_countRKSt6vectorIiSaIiEERS1_m"

/-- Seed: `vis[u] = 1`, guarded (OOB seed takes `fail`, the
    `at()`-throw precedent). -/
def vecMarkCountSeed : CStmt :=
  .if_ (.ult (.var "u") (.stdVecLen "vis"))
    (.vecSet "vis" (.var "u") (.lit (.i32 (BitVec.ofNat 32 1))))
    .fail

/-- Loop body: gate `m[i] != 0` selects the checked accumulation of
    the `vis` read; the index always advances. -/
def vecMarkCountBody : CStmt :=
  .seq (.if_ (.une (.stdVecAt "m" (.var "i"))
              (.lit (.i32 (BitVec.ofNat 32 0))))
          (.assign "t" (.add (.var "t")
            (.stdVecAt "vis" (.var "i"))))
          .skip)
    (.assign "i" (.uadd (.var "i")
      (.lit (.u64 (BitVec.ofNat 64 1)))))

/-- Loop: `while (i < vis.size()) { gate; accumulate; advance }`. -/
def vecMarkCountWhile : CStmt :=
  .while_ (.ult (.var "i") (.stdVecLen "vis")) vecMarkCountBody

/-- Canonical CoreIR for `mark_count`. -/
def vecMarkCountFunc : Func :=
  ⟨vecMarkCountName,
   [{ name := "m", ty := stdVecObjTy, role := .sharedBorrow },
    { name := "vis", ty := stdVecObjTy, role := .mutBorrow 0 },
    { name := "u", ty := .u 64, role := .owned }],
   .i 32,
   .seq vecMarkCountSeed
   (.seq (.let_ "t" (.i 32) (.lit (.i32 (BitVec.ofNat 32 0))))
   (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
   (.seq vecMarkCountWhile
         (.return_ (.var "t")))))⟩

/-- Loop environments: `u64` vertex + `u64` index + `i32`
    accumulator, both word lists, view fixed (the prelude order
    `i, t, m, vis, u` is pinned here). -/
def mkMarkEnv (mL visL : List (BitVec 32)) (u : BitVec 64)
    (k : Nat) (t : BitVec 32) : Env :=
  [("i", .u64 (BitVec.ofNat 64 k)), ("t", .i32 t),
   ("m", .stdVecVal mL), ("vis", .stdVecVal visL), ("u", .u64 u)]

theorem mkMarkEnv_i (mL visL : List (BitVec 32)) (u : BitVec 64)
    (k : Nat) (t : BitVec 32) :
    envLookup (mkMarkEnv mL visL u k t) "i" =
      some (.u64 (BitVec.ofNat 64 k)) := by
  simp [mkMarkEnv, envLookup]

theorem mkMarkEnv_t (mL visL : List (BitVec 32)) (u : BitVec 64)
    (k : Nat) (t : BitVec 32) :
    envLookup (mkMarkEnv mL visL u k t) "t" =
      some (.i32 t) := by
  simp [mkMarkEnv, envLookup, show ("t" : String) ≠ "i" by decide]

theorem mkMarkEnv_m (mL visL : List (BitVec 32)) (u : BitVec 64)
    (k : Nat) (t : BitVec 32) :
    envLookup (mkMarkEnv mL visL u k t) "m" =
      some (.stdVecVal mL) := by
  simp [mkMarkEnv, envLookup, show ("m" : String) ≠ "i" by decide,
    show ("m" : String) ≠ "t" by decide]

theorem mkMarkEnv_vis (mL visL : List (BitVec 32)) (u : BitVec 64)
    (k : Nat) (t : BitVec 32) :
    envLookup (mkMarkEnv mL visL u k t) "vis" =
      some (.stdVecVal visL) := by
  simp [mkMarkEnv, envLookup, show ("vis" : String) ≠ "i" by decide,
    show ("vis" : String) ≠ "t" by decide,
    show ("vis" : String) ≠ "m" by decide]

theorem mkMarkEnv_u (mL visL : List (BitVec 32)) (u : BitVec 64)
    (k : Nat) (t : BitVec 32) :
    envLookup (mkMarkEnv mL visL u k t) "u" =
      some (.u64 u) := by
  simp [mkMarkEnv, envLookup, show ("u" : String) ≠ "i" by decide,
    show ("u" : String) ≠ "t" by decide,
    show ("u" : String) ≠ "m" by decide,
    show ("u" : String) ≠ "vis" by decide]

/-! ## Forward model -/

/-- Gated dual-list fold over the suffixes: the gate word comes from
    the matrix head, the accumulator word from the visited head
    (both advance in lockstep, so the fold is structural and the
    loop invariant bridges via `markFold_step` — no well-founded
    fixpoint is ever unfolded). `m` exhausted first is the
    evaluator's own `OOB` (the C++ `at()` throw, `Array`/`find`
    precedent). -/
def markFold : List (BitVec 32) → List (BitVec 32) → BitVec 32 →
    Result (BitVec 32)
  | [], _ :: _, _ => .error .OOB
  | _, [], t => .ok t
  | g :: gs, w :: ws, t =>
    if g != 0 then
      match checkedAddI32 t w with
      | .error e => .error e
      | .ok a => markFold gs ws a
    else markFold gs ws t

/-- Value-level forward for `mark_count`: the `vis[u] = 1` seed
    (OOB seed is `AssertFail`, the `at()`-throw precedent), then the
    gated fold from zero. -/
def markFwd (mL visL : List (BitVec 32)) (u : BitVec 64) :
    Result Value :=
  match visL[u.toNat]? with
  | none => .error .AssertFail
  | some _ =>
    (markFold mL (visL.set u.toNat (BitVec.ofNat 32 1)) (BitVec.ofNat 32 0)).map
      fun w => .i32 w

/-- `(<$>)` on the word-valued fold computes on both constructors. -/
theorem markMap_error (e : Panic) :
    Except.map (fun w : BitVec 32 => Value.i32 w)
      (.error e : Result (BitVec 32)) = .error e := rfl

theorem markMap_ok (w : BitVec 32) :
    Except.map (fun w : BitVec 32 => Value.i32 w)
      (.ok w : Result (BitVec 32)) = .ok (.i32 w) := rfl

/-- The forward on a failed seed lookup is the seed `AssertFail`. -/
theorem markFwd_seed_err (mL visL : List (BitVec 32)) (u : BitVec 64)
    (hseed : visL[u.toNat]? = none) :
    markFwd mL visL u = .error .AssertFail := by
  simp [markFwd, hseed]

/-- The forward on a successful seed is the mapped fold. -/
theorem markFwd_seed_ok (mL visL : List (BitVec 32)) (u : BitVec 64)
    (w : BitVec 32) (hseed : visL[u.toNat]? = some w)
    (r : Result (BitVec 32))
    (hfold : markFold mL (visL.set u.toNat (BitVec.ofNat 32 1)) (BitVec.ofNat 32 0) = r) :
    markFwd mL visL u = r.map fun w => .i32 w := by
  simp only [markFwd, hseed, hfold]

/-! ## Fold unfolding -/

/-- One-step unfold at a live index pair (proved by induction on the
    index with the lists case-split inside each case, so the loop
    proof never unfolds a well-founded fixpoint). -/
theorem markFold_step (mL visL : List (BitVec 32)) (k : Nat)
    (t : BitVec 32) (w g : BitVec 32)
    (hgetW : visL[k]? = some w) (hgetG : mL[k]? = some g) :
    markFold (mL.drop k) (visL.drop k) t =
      if g != 0 then
        match checkedAddI32 t w with
        | .error e => .error e
        | .ok a => markFold (mL.drop (k + 1)) (visL.drop (k + 1)) a
      else markFold (mL.drop (k + 1)) (visL.drop (k + 1)) t := by
  induction k generalizing mL visL t with
  | zero =>
    cases mL with
    | nil => simp at hgetG
    | cons g0 gs =>
      cases visL with
      | nil => simp at hgetW
      | cons w0 ws =>
        have hw0 : w0 = w := Option.some_inj.mp hgetW
        have hg0 : g0 = g := Option.some_inj.mp hgetG
        subst hw0; subst hg0
        simp [markFold]
  | succ k ih =>
    cases mL with
    | nil => simp at hgetG
    | cons g0 gs =>
      cases visL with
      | nil => simp at hgetW
      | cons w0 ws =>
        simp only [List.drop_succ_cons, List.getElem?_cons_succ]
          at hgetW hgetG ⊢
        exact ih _ _ _ hgetW hgetG

/-- Exit: past the visited end the fold is done (the matrix suffix
    is irrelevant — the loop bound is `vis.size`). -/
theorem markFold_exit (mL visL : List (BitVec 32)) (t : BitVec 32) :
    markFold (mL.drop visL.length) (visL.drop visL.length) t =
      .ok t := by
  rw [List.drop_length]
  cases h : mL.drop visL.length with
  | nil => rfl
  | cons _ _ => rfl

/-! ## Guard evaluation -/

/-- Seed guard: `u < vis.size` as a `decide` (the `vecAtSetGuard_eval`
    shape on the visited vector). -/
theorem markSeedGuard_eval (mL visL : List (BitVec 32)) (u : BitVec 64)
    (hlen64 : visL.length < 2 ^ 64) :
    evalExpr (.ult (.var "u") (.stdVecLen "vis"))
      [("m", .stdVecVal mL), ("vis", .stdVecVal visL), ("u", .u64 u)] =
      .ok (.b (decide (u.toNat < visL.length))) := by
  have hsize : evalExpr (.stdVecLen "vis")
      [("m", .stdVecVal mL), ("vis", .stdVecVal visL), ("u", .u64 u)] =
      .ok (.u64 (BitVec.ofNat 64 visL.length)) :=
    evalExpr_stdVecLen_some "vis" _ visL (by simp [envLookup])
  have hnv : evalExpr (.var "u")
      [("m", .stdVecVal mL), ("vis", .stdVecVal visL), ("u", .u64 u)] =
      .ok (.u64 u) :=
    evalExpr_var_hit _ _ _ (by simp [envLookup])
  have hult := evalExpr_ult_u64 _ _ _ _ _ hnv hsize
  rw [ult_ofNat64_len u visL.length hlen64] at hult
  exact hult

/-- Loop guard: `k < vis.size` as a `decide`. -/
theorem markLoopGuard_eval (mL visL : List (BitVec 32)) (u : BitVec 64)
    (k : Nat) (t : BitVec 32)
    (hk64 : k < 2 ^ 64) (hl64 : visL.length < 2 ^ 64) :
    evalExpr (.ult (.var "i") (.stdVecLen "vis"))
      (mkMarkEnv mL visL u k t) =
      .ok (.b (decide (k < visL.length))) := by
  have hi := mkMarkEnv_i mL visL u k t
  have hs := mkMarkEnv_vis mL visL u k t
  have hlen : (BitVec.ofNat 64 visL.length).toNat = visL.length :=
    ofNat64_toNat _ hl64
  simp [evalExpr, hi, hs, ofNat64_ult k _ hk64, hlen]

/-- Gate: `m[i] != 0` as the model boolean. -/
theorem markGate_eval (mL visL : List (BitVec 32)) (u : BitVec 64)
    (k : Nat) (t : BitVec 32) (g : BitVec 32)
    (hget : mL[k]? = some g)
    (hk64 : k < 2 ^ 64) :
    evalExpr (.une (.stdVecAt "m" (.var "i"))
        (.lit (.i32 (BitVec.ofNat 32 0))))
      (mkMarkEnv mL visL u k t) =
      .ok (.b (g != (BitVec.ofNat 32 0))) := by
  have hm := mkMarkEnv_m mL visL u k t
  have hi := mkMarkEnv_i mL visL u k t
  have hgetB : mL[(BitVec.ofNat 64 k).toNat]? = some g := by
    rw [ofNat64_toNat _ hk64]; exact hget
  have hread : evalExpr (.stdVecAt "m" (.var "i"))
      (mkMarkEnv mL visL u k t) = .ok (.i32 g) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hm
      (evalExpr_var_hit _ _ _ hi) hgetB
  have hlit : evalExpr (.lit (.i32 (BitVec.ofNat 32 0)))
      (mkMarkEnv mL visL u k t) = .ok (.i32 (BitVec.ofNat 32 0)) := by
    simp [evalExpr, litVal]
  have hunfold : evalExpr (.une (.stdVecAt "m" (.var "i"))
      (.lit (.i32 (BitVec.ofNat 32 0))))
      (mkMarkEnv mL visL u k t) =
      match evalExpr (.stdVecAt "m" (.var "i")) (mkMarkEnv mL visL u k t),
        evalExpr (.lit (.i32 (BitVec.ofNat 32 0)))
          (mkMarkEnv mL visL u k t) with
      | .ok (.u32 x), .ok (.u32 y) => .ok (.b (x != y))
      | .ok (.u64 x), .ok (.u64 y) => .ok (.b (x != y))
      | .ok (.i32 x), .ok (.i32 y) => .ok (.b (x != y))
      | .ok (.i64 x), .ok (.i64 y) => .ok (.b (x != y))
      | .ok _, .ok _ => .error .AssertFail
      | .error e, _ => .error e
      | _, .error e => .error e := rfl
  simp only [hunfold, hread, hlit]

/-! ## Seed steps -/

/-- Seed hit: guard holds, the store marks `vis[u]`, the
    environment carries the marked words. -/
theorem markSeed_hit (F : Nat) (mL visL : List (BitVec 32))
    (u : BitVec 64) (w : BitVec 32)
    (hlt : u.toNat < visL.length) (hlen64 : visL.length < 2 ^ 64)
    (hget : visL[u.toNat]? = some w) :
    evalStmtFuel F vecMarkCountSeed
      [("m", .stdVecVal mL), ("vis", .stdVecVal visL), ("u", .u64 u)] =
      .ok ([("m", .stdVecVal mL),
        ("vis", .stdVecVal (visL.set u.toNat (BitVec.ofNat 32 1))), ("u", .u64 u)],
        .fellThrough) := by
  have hc : evalExpr (.ult (.var "u") (.stdVecLen "vis"))
      [("m", .stdVecVal mL), ("vis", .stdVecVal visL), ("u", .u64 u)] =
      .ok (.b true) := by
    have h := markSeedGuard_eval mL visL u hlen64
    simpa [hlt] using h
  have hi : evalExpr (.var "u")
      [("m", .stdVecVal mL), ("vis", .stdVecVal visL), ("u", .u64 u)] =
      .ok (.u64 u) :=
    evalExpr_var_hit _ _ _ (by simp [envLookup])
  have hx : evalExpr (.lit (.i32 (BitVec.ofNat 32 1)))
      [("m", .stdVecVal mL), ("vis", .stdVecVal visL), ("u", .u64 u)] =
      .ok (.i32 (BitVec.ofNat 32 1)) := by
    simp [evalExpr, litVal]
  have hu : envUpdate [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
      ("u", .u64 u)] "vis" (.stdVecVal (visL.set u.toNat (BitVec.ofNat 32 1))) =
      some [("m", .stdVecVal mL),
        ("vis", .stdVecVal (visL.set u.toNat (BitVec.ofNat 32 1))), ("u", .u64 u)] := rfl
  have hset := evalStmtFuel_vecSet F "vis" (.var "u")
    (.lit (.i32 (BitVec.ofNat 32 1)))
    [("m", .stdVecVal mL), ("vis", .stdVecVal visL), ("u", .u64 u)]
    u (BitVec.ofNat 32 1) visL w _ hi hx
    (by simp [envLookup]) hget hu
  simp only [vecMarkCountSeed]
  rw [evalStmtFuel_if_true _ _ _ _ _ hc]
  exact hset

/-- Seed miss: past the end aborts loudly (the `at()`-throw
    precedent, any fuel). -/
theorem markSeed_empty (F : Nat) (mL visL : List (BitVec 32))
    (u : BitVec 64) (hlen64 : visL.length < 2 ^ 64)
    (hle : visL.length ≤ u.toNat) :
    evalStmtFuel F vecMarkCountSeed
      [("m", .stdVecVal mL), ("vis", .stdVecVal visL), ("u", .u64 u)] =
      .error .AssertFail := by
  have hc : evalExpr (.ult (.var "u") (.stdVecLen "vis"))
      [("m", .stdVecVal mL), ("vis", .stdVecVal visL), ("u", .u64 u)] =
      .ok (.b false) := by
    have h := markSeedGuard_eval mL visL u hlen64
    simpa [Nat.not_lt.mpr hle] using h
  simp only [vecMarkCountSeed]
  exact (evalStmtFuel_if_false _ _ _ _ _ hc).trans
    (evalStmtFuel_fail _ _)

/-! ## Body steps -/

/-- `if_` on an erroring condition aborts loudly (the `TwoSum`
    local-helper shape). -/
theorem markIf_err (f : Nat) (c : CExpr) (t e : CStmt)
    (ρ : Env) (err : Panic)
    (h : evalExpr c ρ = .error err) :
    evalStmtFuel f (.if_ c t e) ρ = .error err := by
  cases f with
  | zero =>
    simp only [evalStmtFuel, evalStmtZero] at h ⊢
    simp only [evalStmtWith, h]
  | succ g =>
    simp only [evalStmtFuel] at h ⊢
    simp only [evalStmtWith, h]

/-- One-step unfold when the matrix is exhausted but visited is
    not: the C++ `at()` throw, the evaluator's own `OOB`. -/
theorem markFold_step_miss (mL visL : List (BitVec 32)) (k : Nat)
    (t : BitVec 32) (w : BitVec 32)
    (hgetW : visL[k]? = some w) (hmiss : mL[k]? = none) :
    markFold (mL.drop k) (visL.drop k) t = .error .OOB := by
  induction k generalizing mL visL t with
  | zero =>
    cases mL with
    | nil =>
      cases visL with
      | nil => simp at hgetW
      | cons w0 ws => simp [markFold]
    | cons g0 gs => simp at hmiss
  | succ k ih =>
    cases mL with
    | nil =>
      cases visL with
      | nil => simp at hgetW
      | cons w0 ws =>
        cases hdrop : (w0 :: ws).drop (k + 1) with
        | nil =>
          obtain ⟨hltW, _⟩ := List.getElem?_eq_some_iff.mp hgetW
          have hL : ((w0 :: ws).drop (k + 1)).length = 0 := by
            rw [hdrop]; rfl
          rw [List.length_drop] at hL
          omega
        | cons x xs =>
          show markFold [] (x :: xs) t = .error .OOB
          rfl
    | cons g0 gs =>
      cases visL with
      | nil => simp at hgetW
      | cons w0 ws =>
        simp only [List.drop_succ_cons, List.getElem?_cons_succ]
          at hmiss hgetW ⊢
        exact ih _ _ _ hgetW hmiss

/-- Body with the gate off: skip the accumulation, advance the
    index (any fuel). -/
theorem markBody_gateOff (F : Nat) (mL visL : List (BitVec 32))
    (u : BitVec 64) (k : Nat) (t : BitVec 32) (g : BitVec 32)
    (hgetG : mL[k]? = some g) (hk64 : k < 2 ^ 64)
    (hoff : (g != (BitVec.ofNat 32 0)) = false) :
    evalStmtFuel F vecMarkCountBody (mkMarkEnv mL visL u k t) =
      .ok (mkMarkEnv mL visL u (k + 1) t, .fellThrough) := by
  have hgate : evalExpr (.une (.stdVecAt "m" (.var "i"))
      (.lit (.i32 (BitVec.ofNat 32 0))))
      (mkMarkEnv mL visL u k t) = .ok (.b false) := by
    have h := markGate_eval mL visL u k t g hgetG hk64
    rw [hoff] at h; exact h
  have hskip : evalStmtFuel F
      (.if_ (.une (.stdVecAt "m" (.var "i"))
        (.lit (.i32 (BitVec.ofNat 32 0))))
        (.assign "t" (.add (.var "t")
          (.stdVecAt "vis" (.var "i")))) .skip)
      (mkMarkEnv mL visL u k t) =
      .ok (mkMarkEnv mL visL u k t, .fellThrough) := by
    rw [evalStmtFuel_if_false _ _ _ _ _ hgate]
    cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith]
  have hi := mkMarkEnv_i mL visL u k t
  have haddI : evalExpr
      (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1))))
      (mkMarkEnv mL visL u k t) =
      .ok (.u64 (BitVec.ofNat 64 k + BitVec.ofNat 64 1)) := by
    simp only [evalExpr, litVal, hi]
  have huI : envUpdate (mkMarkEnv mL visL u k t) "i"
      (.u64 (BitVec.ofNat 64 k + BitVec.ofNat 64 1)) =
      some (mkMarkEnv mL visL u (k + 1) t) := by
    simp [mkMarkEnv, envUpdate, ofNat64_add_one]
  have hadv := evalStmtFuel_assign F _ _ _ _ _ haddI huI
  simp only [vecMarkCountBody]
  rw [evalStmtFuel_seq_fallthrough _ _ _ _ _ hskip]
  exact hadv

/-- Body with the gate on and a successful add: accumulate and
    advance (any fuel). -/
theorem markBody_ok (F : Nat) (mL visL : List (BitVec 32))
    (u : BitVec 64) (k : Nat) (t : BitVec 32) (w g : BitVec 32)
    (hgetW : visL[k]? = some w) (hgetG : mL[k]? = some g)
    (hk64 : k < 2 ^ 64)
    (hon : (g != (BitVec.ofNat 32 0)) = true)
    (a : BitVec 32) (hc : checkedAddI32 t w = .ok a) :
    evalStmtFuel F vecMarkCountBody (mkMarkEnv mL visL u k t) =
      .ok (mkMarkEnv mL visL u (k + 1) a, .fellThrough) := by
  have hgate : evalExpr (.une (.stdVecAt "m" (.var "i"))
      (.lit (.i32 (BitVec.ofNat 32 0))))
      (mkMarkEnv mL visL u k t) = .ok (.b true) := by
    have h := markGate_eval mL visL u k t g hgetG hk64
    rw [hon] at h; exact h
  have hvis := mkMarkEnv_vis mL visL u k t
  have hi := mkMarkEnv_i mL visL u k t
  have ht := mkMarkEnv_t mL visL u k t
  have hgetWB : visL[(BitVec.ofNat 64 k).toNat]? = some w := by
    rw [ofNat64_toNat _ hk64]; exact hgetW
  have hreadV : evalExpr (.stdVecAt "vis" (.var "i"))
      (mkMarkEnv mL visL u k t) = .ok (.i32 w) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hvis
      (evalExpr_var_hit _ _ _ hi) hgetWB
  have hevalT : evalExpr (.var "t") (mkMarkEnv mL visL u k t) =
      .ok (.i32 t) :=
    evalExpr_var_hit _ _ _ ht
  have hunfold : evalExpr (.add (.var "t") (.stdVecAt "vis" (.var "i")))
      (mkMarkEnv mL visL u k t) =
      match evalExpr (.var "t") (mkMarkEnv mL visL u k t),
        evalExpr (.stdVecAt "vis" (.var "i"))
          (mkMarkEnv mL visL u k t) with
      | .ok (.i32 x), .ok (.i32 y) => (checkedAddI32 x y).map .i32
      | .ok (.i64 x), .ok (.i64 y) => (checkedAddI64 x y).map .i64
      | .ok _, .ok _ => .error .AssertFail
      | .error e, _ => .error e
      | _, .error e => .error e := rfl
  have hadd : evalExpr (.add (.var "t") (.stdVecAt "vis" (.var "i")))
      (mkMarkEnv mL visL u k t) = .ok (.i32 a) := by
    simp only [hunfold, hevalT, hreadV, hc, Except.map]
  have huT : envUpdate (mkMarkEnv mL visL u k t) "t" (.i32 a) =
      some (mkMarkEnv mL visL u k a) := rfl
  have h1 := evalStmtFuel_assign F _ _ _ _ _ hadd huT
  have hifT : evalStmtFuel F
      (.if_ (.une (.stdVecAt "m" (.var "i"))
        (.lit (.i32 (BitVec.ofNat 32 0))))
        (.assign "t" (.add (.var "t")
          (.stdVecAt "vis" (.var "i")))) .skip)
      (mkMarkEnv mL visL u k t) =
      .ok (mkMarkEnv mL visL u k a, .fellThrough) := by
    rw [evalStmtFuel_if_true _ _ _ _ _ hgate]
    exact h1
  have hi' := mkMarkEnv_i mL visL u k a
  have haddI : evalExpr
      (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1))))
      (mkMarkEnv mL visL u k a) =
      .ok (.u64 (BitVec.ofNat 64 k + BitVec.ofNat 64 1)) := by
    simp only [evalExpr, litVal, hi']
  have huI : envUpdate (mkMarkEnv mL visL u k a) "i"
      (.u64 (BitVec.ofNat 64 k + BitVec.ofNat 64 1)) =
      some (mkMarkEnv mL visL u (k + 1) a) := by
    simp [mkMarkEnv, envUpdate, ofNat64_add_one]
  have h2 := evalStmtFuel_assign F _ _ _ _ _ haddI huI
  simp only [vecMarkCountBody]
  rw [evalStmtFuel_seq_fallthrough _ _ _ _ _ hifT]
  exact h2

/-- Body with an overflowing add: the `nsw` error is loud, the
    index never advances (any fuel). -/
theorem markBody_add_err (F : Nat) (mL visL : List (BitVec 32))
    (u : BitVec 64) (k : Nat) (t : BitVec 32) (w g : BitVec 32)
    (e : Panic)
    (hgetW : visL[k]? = some w) (hgetG : mL[k]? = some g)
    (hk64 : k < 2 ^ 64)
    (hon : (g != (BitVec.ofNat 32 0)) = true)
    (hc : checkedAddI32 t w = .error e) :
    evalStmtFuel F vecMarkCountBody (mkMarkEnv mL visL u k t) =
      .error e := by
  have hgate : evalExpr (.une (.stdVecAt "m" (.var "i"))
      (.lit (.i32 (BitVec.ofNat 32 0))))
      (mkMarkEnv mL visL u k t) = .ok (.b true) := by
    have h := markGate_eval mL visL u k t g hgetG hk64
    rw [hon] at h; exact h
  have hvis := mkMarkEnv_vis mL visL u k t
  have hi := mkMarkEnv_i mL visL u k t
  have ht := mkMarkEnv_t mL visL u k t
  have hgetWB : visL[(BitVec.ofNat 64 k).toNat]? = some w := by
    rw [ofNat64_toNat _ hk64]; exact hgetW
  have hreadV : evalExpr (.stdVecAt "vis" (.var "i"))
      (mkMarkEnv mL visL u k t) = .ok (.i32 w) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hvis
      (evalExpr_var_hit _ _ _ hi) hgetWB
  have hevalT : evalExpr (.var "t") (mkMarkEnv mL visL u k t) =
      .ok (.i32 t) :=
    evalExpr_var_hit _ _ _ ht
  have hunfold : evalExpr (.add (.var "t") (.stdVecAt "vis" (.var "i")))
      (mkMarkEnv mL visL u k t) =
      match evalExpr (.var "t") (mkMarkEnv mL visL u k t),
        evalExpr (.stdVecAt "vis" (.var "i"))
          (mkMarkEnv mL visL u k t) with
      | .ok (.i32 x), .ok (.i32 y) => (checkedAddI32 x y).map .i32
      | .ok (.i64 x), .ok (.i64 y) => (checkedAddI64 x y).map .i64
      | .ok _, .ok _ => .error .AssertFail
      | .error e, _ => .error e
      | _, .error e => .error e := rfl
  have haddE : evalExpr (.add (.var "t") (.stdVecAt "vis" (.var "i")))
      (mkMarkEnv mL visL u k t) = .error e := by
    simp only [hunfold, hevalT, hreadV, hc, Except.map]
  have h1 : evalStmtFuel F
      (.assign "t" (.add (.var "t") (.stdVecAt "vis" (.var "i"))))
      (mkMarkEnv mL visL u k t) = .error e := by
    cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, haddE]
  have hifT : evalStmtFuel F
      (.if_ (.une (.stdVecAt "m" (.var "i"))
        (.lit (.i32 (BitVec.ofNat 32 0))))
        (.assign "t" (.add (.var "t")
          (.stdVecAt "vis" (.var "i")))) .skip)
      (mkMarkEnv mL visL u k t) = .error e := by
    rw [evalStmtFuel_if_true _ _ _ _ _ hgate]
    exact h1
  simp only [vecMarkCountBody]
  -- The advance never runs: the seq errors on its first leg.
  exact evalStmtFuel_seq_err _ _ _ _ _ hifT

/-- Body when the matrix is exhausted: the `at()` throw is loud
    (any fuel; the visited value is never read on this leg). -/
theorem markBody_mOob (F : Nat) (mL visL : List (BitVec 32))
    (u : BitVec 64) (k : Nat) (t : BitVec 32)
    (hmiss : mL[k]? = none)
    (hk64 : k < 2 ^ 64) :
    evalStmtFuel F vecMarkCountBody (mkMarkEnv mL visL u k t) =
      .error .OOB := by
  have hm := mkMarkEnv_m mL visL u k t
  have hi := mkMarkEnv_i mL visL u k t
  have hmissB : mL[(BitVec.ofNat 64 k).toNat]? = none := by
    rw [ofNat64_toNat _ hk64]; exact hmiss
  have hreadOOB : evalExpr (.stdVecAt "m" (.var "i"))
      (mkMarkEnv mL visL u k t) = .error .OOB :=
    evalExpr_stdVecAt_oob _ _ _ _ _ hm
      (evalExpr_var_hit _ _ _ hi) hmissB
  have hlit : evalExpr (.lit (.i32 (BitVec.ofNat 32 0)))
      (mkMarkEnv mL visL u k t) = .ok (.i32 (BitVec.ofNat 32 0)) := by
    simp [evalExpr, litVal]
  have hunfold : evalExpr (.une (.stdVecAt "m" (.var "i"))
      (.lit (.i32 (BitVec.ofNat 32 0))))
      (mkMarkEnv mL visL u k t) =
      match evalExpr (.stdVecAt "m" (.var "i")) (mkMarkEnv mL visL u k t),
        evalExpr (.lit (.i32 (BitVec.ofNat 32 0)))
          (mkMarkEnv mL visL u k t) with
      | .ok (.u32 x), .ok (.u32 y) => .ok (.b (x != y))
      | .ok (.u64 x), .ok (.u64 y) => .ok (.b (x != y))
      | .ok (.i32 x), .ok (.i32 y) => .ok (.b (x != y))
      | .ok (.i64 x), .ok (.i64 y) => .ok (.b (x != y))
      | .ok _, .ok _ => .error .AssertFail
      | .error e, _ => .error e
      | _, .error e => .error e := rfl
  have hcond : evalExpr (.une (.stdVecAt "m" (.var "i"))
      (.lit (.i32 (BitVec.ofNat 32 0))))
      (mkMarkEnv mL visL u k t) = .error .OOB := by
    simp only [hunfold, hreadOOB, hlit]
  simp only [vecMarkCountBody]
  exact evalStmtFuel_seq_err _ _ _ _ _ (markIf_err _ _ _ _ _ _ hcond)

/-! ## Loop correctness -/

/-- Loop correctness, by fuel induction. The visited list is never
    written by the loop, so the post-environment is exact (no
    scratch existentials): the loop preserves both word lists and
    stops at `vis.length`. -/
theorem markWhile_correct (mL visL : List (BitVec 32)) (u : BitVec 64)
    (F k : Nat) (t : BitVec 32)
    (hk : k ≤ visL.length) (hl64 : visL.length < 2 ^ 64)
    (hF : visL.length - k + 1 ≤ F) :
    match markFold (mL.drop k) (visL.drop k) t with
    | .error e => evalStmtFuel F vecMarkCountWhile
        (mkMarkEnv mL visL u k t) = .error e
    | .ok t' => evalStmtFuel F vecMarkCountWhile
        (mkMarkEnv mL visL u k t) =
        .ok (mkMarkEnv mL visL u visL.length t', .fellThrough) := by
  induction F generalizing k t with
  | zero => omega
  | succ F ih =>
    by_cases hlt : k < visL.length
    · have hk64 : k < 2 ^ 64 := by omega
      have hgetW : visL[k]? = some visL[k] := List.getElem?_eq_getElem hlt
      have hcond : evalExpr (.ult (.var "i") (.stdVecLen "vis"))
            (mkMarkEnv mL visL u k t) = .ok (.b true) := by
        simpa [hlt] using (markLoopGuard_eval mL visL u k t hk64 hl64)
      cases hmget : mL[k]? with
      | none =>
        have hunfold := markFold_step_miss mL visL k t visL[k]
          hgetW hmget
        have hbody := markBody_mOob F mL visL u k t hmget hk64
        have hstep : evalStmtFuel (F + 1) vecMarkCountWhile
            (mkMarkEnv mL visL u k t) = .error .OOB := by
          cir_unfold_leaf (vecMarkCountWhile, hcond, hbody)
        simp only [hstep, hunfold]
      | some g =>
        have hunfold := markFold_step mL visL k t visL[k] g
          hgetW hmget
        by_cases hon : (g != (BitVec.ofNat 32 0)) = true
        · have hon0 : (g != 0) = true := hon
          cases hc : checkedAddI32 t visL[k] with
          | error e =>
            have hbody := markBody_add_err F mL visL u k t visL[k] g e
              hgetW hmget hk64 hon hc
            have hstep : evalStmtFuel (F + 1) vecMarkCountWhile
                (mkMarkEnv mL visL u k t) = .error e := by
              cir_unfold_leaf (vecMarkCountWhile, hcond, hbody)
            simp only [hstep, hunfold, hon0, hc, ite_true]
          | ok a =>
            have hbody := markBody_ok F mL visL u k t visL[k] g
              hgetW hmget hk64 hon a hc
            have hon0 : (g != 0) = true := hon
            have hstep : evalStmtFuel (F + 1) vecMarkCountWhile
                (mkMarkEnv mL visL u k t) =
                evalStmtFuel F vecMarkCountWhile
                  (mkMarkEnv mL visL u (k + 1) a) := by
              cir_unfold_leaf (vecMarkCountWhile, hcond, hbody)
            simp only [hstep, hunfold, hon0, hc, ite_true]
            exact ih (k + 1) a (by omega) (by omega)
        · have hoff : (g != (BitVec.ofNat 32 0)) = false := by
            cases hX : (g != (BitVec.ofNat 32 0)) with
            | true => exact absurd hX hon
            | false => rfl
          have hoff0 : (g != 0) = false := hoff
          have hbody := markBody_gateOff F mL visL u k t g
            hmget hk64 hoff
          have hstep : evalStmtFuel (F + 1) vecMarkCountWhile
              (mkMarkEnv mL visL u k t) =
              evalStmtFuel F vecMarkCountWhile
                (mkMarkEnv mL visL u (k + 1) t) := by
            cir_unfold_leaf (vecMarkCountWhile, hcond, hbody)
          simp only [hstep, hunfold, hoff0]
          exact ih (k + 1) t (by omega) (by omega)
    · have hkk : k = visL.length := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "i") (.stdVecLen "vis"))
            (mkMarkEnv mL visL u visL.length t) = .ok (.b false) := by
        have h := markLoopGuard_eval mL visL u visL.length t
          (by omega) hl64
        simpa using h
      have hexit : evalStmtFuel (F + 1) vecMarkCountWhile
          (mkMarkEnv mL visL u visL.length t) =
          .ok (mkMarkEnv mL visL u visL.length t, .fellThrough) := by
        simp only [vecMarkCountWhile]
        simp [evalStmtFuel, evalStmtSuccHandler, evalStmtWith, hcond]
      have hdone : markFold (mL.drop visL.length)
          (visL.drop visL.length) t = .ok t :=
        markFold_exit _ _ _
      rw [hdone]
      exact hexit

/-! ## Whole-function forward -/

/-- Whole-function forward at explicit fuel (the `vecAtSum` entry
    shape: bind, seed, two lets, loop, return). -/
theorem evalFuncFuel_vecMarkCount (mL visL : List (BitVec 32))
    (u : BitVec 64) (F : Nat) (hl64 : visL.length < 2 ^ 64)
    (hF : visL.length + 1 ≤ F) :
    evalFuncFuel F vecMarkCountFunc
      [.stdVecVal mL, .stdVecVal visL, .u64 u] =
      markFwd mL visL u := by
  have hbind : bindArgs vecMarkCountFunc.args
      [.stdVecVal mL, .stdVecVal visL, .u64 u] =
      some [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
        ("u", .u64 u)] := rfl
  have hbody : vecMarkCountFunc.body =
      .seq vecMarkCountSeed
      (.seq (.let_ "t" (.i 32) (.lit (.i32 (BitVec.ofNat 32 0))))
      (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.seq vecMarkCountWhile
            (.return_ (.var "t"))))) := rfl
  cases hseed : visL[u.toNat]? with
  | none =>
    have hsum0 : markFwd mL visL u = .error .AssertFail :=
      markFwd_seed_err _ _ _ hseed
    cases F with
    | zero =>
      have hseedW : evalStmtWith evalStmtZeroHandler vecMarkCountSeed
          [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
            ("u", .u64 u)] = .error .AssertFail :=
        markSeed_empty 0 mL visL u hl64
          (Nat.le_of_not_lt (fun hlt => by
            have hsome := List.getElem?_eq_getElem hlt
            rw [hsome] at hseed
            simp at hseed))
      simp [evalFuncFuel, vecMarkCountFunc, bindArgs,
        evalStmtFuel, evalStmtZero, evalStmtWith, hseedW, hsum0]
    | succ F =>
      have hseedW : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          vecMarkCountSeed
          [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
            ("u", .u64 u)] = .error .AssertFail :=
        markSeed_empty (F + 1) mL visL u hl64
          (Nat.le_of_not_lt (fun hlt => by
            have hsome := List.getElem?_eq_getElem hlt
            rw [hsome] at hseed
            simp at hseed))
      simp [evalFuncFuel, vecMarkCountFunc, bindArgs,
        evalStmtFuel, evalStmtWith, hseedW, hsum0]
  | some w =>
    obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hseed
    have hseedW0 : evalStmtWith evalStmtZeroHandler vecMarkCountSeed
        [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
          ("u", .u64 u)] =
        .ok ([("m", .stdVecVal mL),
          ("vis", .stdVecVal (visL.set u.toNat (BitVec.ofNat 32 1))), ("u", .u64 u)],
          .fellThrough) :=
      markSeed_hit 0 mL visL u w hlt hl64 hseed
    have hseedWS : ∀ F : Nat, evalStmtWith
        (evalStmtSuccHandler (evalStmtFuel F)) vecMarkCountSeed
        [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
          ("u", .u64 u)] =
        .ok ([("m", .stdVecVal mL),
          ("vis", .stdVecVal (visL.set u.toNat (BitVec.ofNat 32 1))), ("u", .u64 u)],
          .fellThrough) :=
      fun F => markSeed_hit (F + 1) mL visL u w hlt hl64 hseed
    have henv : [("i", .u64 (BitVec.ofNat 64 0)),
        ("t", .i32 (BitVec.ofNat 32 0)),
        ("m", .stdVecVal mL),
        ("vis", .stdVecVal (visL.set u.toNat (BitVec.ofNat 32 1))), ("u", .u64 u)]
        = mkMarkEnv mL (visL.set u.toNat (BitVec.ofNat 32 1)) u 0
          (BitVec.ofNat 32 0) := rfl
    cases hfold : markFold mL (visL.set u.toNat (BitVec.ofNat 32 1))
      (BitVec.ofNat 32 0) with
    | error e =>
      have hsum0 : markFwd mL visL u = .error e :=
        markFwd_seed_ok _ _ _ _ hseed _ hfold
      cases F with
      | zero =>
        have hloopH0 : evalStmtWith evalStmtZeroHandler
            vecMarkCountWhile
            (mkMarkEnv mL (visL.set u.toNat (BitVec.ofNat 32 1)) u 0
              (BitVec.ofNat 32 0)) = .error e := by
          have hlen0 : (visL.set u.toNat (BitVec.ofNat 32 1)).length = visL.length :=
            List.length_set
          have h := markWhile_correct mL (visL.set u.toNat (BitVec.ofNat 32 1)) u 0 0
            (BitVec.ofNat 32 0) (Nat.zero_le _) (by omega) (by omega)
          rw [hlen0] at h
          have hdrop0m : mL.drop 0 = mL := by simp
          have hdrop0v : (visL.set u.toNat (BitVec.ofNat 32 1)).drop 0 =
              visL.set u.toNat (BitVec.ofNat 32 1) := by simp
          rw [hdrop0m, hdrop0v, hfold] at h
          exact h
        simp [evalFuncFuel, vecMarkCountFunc, bindArgs,
          evalStmtFuel, evalStmtZero, evalStmtWith, evalExpr, litVal,
          envExtend, henv, hseedW0, hloopH0, hsum0]
      | succ F =>
        have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
            vecMarkCountWhile
            (mkMarkEnv mL (visL.set u.toNat (BitVec.ofNat 32 1)) u 0
              (BitVec.ofNat 32 0)) = .error e := by
          have hlen0 : (visL.set u.toNat (BitVec.ofNat 32 1)).length = visL.length :=
            List.length_set
          have h := markWhile_correct mL (visL.set u.toNat (BitVec.ofNat 32 1)) u (F + 1) 0
            (BitVec.ofNat 32 0) (Nat.zero_le _) (by omega) (by omega)
          rw [hlen0] at h
          have hdrop0m : mL.drop 0 = mL := by simp
          have hdrop0v : (visL.set u.toNat (BitVec.ofNat 32 1)).drop 0 =
              visL.set u.toNat (BitVec.ofNat 32 1) := by simp
          rw [hdrop0m, hdrop0v, hfold] at h
          exact h
        have hseedW : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
            vecMarkCountSeed
            [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
              ("u", .u64 u)] =
            .ok ([("m", .stdVecVal mL),
              ("vis", .stdVecVal (visL.set u.toNat (BitVec.ofNat 32 1))), ("u", .u64 u)],
              .fellThrough) :=
          hseedWS F
        simp [evalFuncFuel, vecMarkCountFunc, bindArgs,
          evalStmtFuel, evalStmtWith, evalExpr, litVal, envExtend,
          henv, hseedW, hloopS, hsum0]
    | ok t' =>
      have hsum0 : markFwd mL visL u = .ok (.i32 t') :=
        markFwd_seed_ok _ _ _ _ hseed _ hfold
      cases F with
      | zero =>
        have hlen0 : (visL.set u.toNat (BitVec.ofNat 32 1)).length = visL.length :=
          List.length_set
        have h := markWhile_correct mL (visL.set u.toNat (BitVec.ofNat 32 1)) u 0 0
          (BitVec.ofNat 32 0) (Nat.zero_le _) (by omega) (by omega)
        rw [hlen0] at h
        have hdrop0m : mL.drop 0 = mL := by simp
        have hdrop0v : (visL.set u.toNat (BitVec.ofNat 32 1)).drop 0 =
            visL.set u.toNat (BitVec.ofNat 32 1) := by simp
        rw [hdrop0m, hdrop0v, hfold] at h
        have hloopH0w : evalStmtWith evalStmtZeroHandler
            vecMarkCountWhile
            (mkMarkEnv mL (visL.set u.toNat (BitVec.ofNat 32 1)) u 0
              (BitVec.ofNat 32 0)) =
            .ok (mkMarkEnv mL (visL.set u.toNat (BitVec.ofNat 32 1)) u visL.length t',
              .fellThrough) :=
          h
        have hsret : envLookup
            (mkMarkEnv mL (visL.set u.toNat (BitVec.ofNat 32 1)) u visL.length t') "t" =
            some (.i32 t') :=
          mkMarkEnv_t _ _ _ _ _
        simp [evalFuncFuel, vecMarkCountFunc, bindArgs,
          evalStmtFuel, evalStmtZero, evalStmtWith, evalExpr, litVal,
          envExtend, henv, hseedW0, hloopH0w, hsret, hsum0]
      | succ F =>
        have hlen0 : (visL.set u.toNat (BitVec.ofNat 32 1)).length = visL.length :=
          List.length_set
        have h := markWhile_correct mL (visL.set u.toNat (BitVec.ofNat 32 1)) u (F + 1) 0
          (BitVec.ofNat 32 0) (Nat.zero_le _) (by omega) (by omega)
        rw [hlen0] at h
        have hdrop0m : mL.drop 0 = mL := by simp
        have hdrop0v : (visL.set u.toNat (BitVec.ofNat 32 1)).drop 0 =
            visL.set u.toNat (BitVec.ofNat 32 1) := by simp
        rw [hdrop0m, hdrop0v, hfold] at h
        have hloopSw : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
            vecMarkCountWhile
            (mkMarkEnv mL (visL.set u.toNat (BitVec.ofNat 32 1)) u 0
              (BitVec.ofNat 32 0)) =
            .ok (mkMarkEnv mL (visL.set u.toNat (BitVec.ofNat 32 1)) u visL.length t',
              .fellThrough) :=
          h
        have hsret : envLookup
            (mkMarkEnv mL (visL.set u.toNat (BitVec.ofNat 32 1)) u visL.length t') "t" =
            some (.i32 t') :=
          mkMarkEnv_t _ _ _ _ _
        have hseedW : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
            vecMarkCountSeed
            [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
              ("u", .u64 u)] =
            .ok ([("m", .stdVecVal mL),
              ("vis", .stdVecVal (visL.set u.toNat (BitVec.ofNat 32 1))), ("u", .u64 u)],
              .fellThrough) :=
          hseedWS F
        simp [evalFuncFuel, vecMarkCountFunc, bindArgs,
          evalStmtFuel, evalStmtWith, evalExpr, litVal, envExtend,
          henv, hseedW, hsret, hloopSw, hsum0]


/-- G1b transport: the char-width entry is `vecMarkCountFunc` under
    its own mangled name (the sext is fused into the `stdVecAt`
    read, so the CoreIR body is width-agnostic); `evalFuncFuel`
    never consults the name, so the G1 entry theorem applies
    definitionally. -/
theorem evalFuncFuel_vecMarkCountC (mL visL : List (BitVec 32))
    (u : BitVec 64) (F : Nat) (hl64 : visL.length < 2 ^ 64)
    (hF : visL.length + 1 ≤ F) :
    evalFuncFuel F { vecMarkCountFunc with name := markCountCName }
      [.stdVecVal mL, .stdVecVal visL, .u64 u] =
      markFwd mL visL u :=
  evalFuncFuel_vecMarkCount mL visL u F hl64 hF
