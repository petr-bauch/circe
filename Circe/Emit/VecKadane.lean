/-
Circe.Emit.VecKadane — Kadane maximum-subarray over `const vector<int>&`.

The corpus (`tests/cpp/max_subarray.cpp`: `cur = best = v.at(0)`,
loop from `i = 1`, explicit-comparison max updates, `nsw` add)
functionalizes to one fused entry `Func`: the two `at(0)` seeds
fuse to one `0 < size` guard around two `stdVecAt`-`let`s (empty
input takes the `fail` arm — the `at()`-throw precedent), the
loop is the call-free `while_` over a dual-accumulator env
(`callRet` cannot live inside loop bodies).

Error precedence: the loop bound `i < len` subsumes the per-read
guard, so the in-loop `OOB` leg is dead-but-propagated; the live
failures are the `nsw` overflow (aborts the fold mid-loop) and
the empty-input seed (fused `fail`). The max updates are
`if_`-on-`slt` statements (the source `if`s, one per update);
the value-level `imax` shares the `slt` boolean, so the
eval bridge is rewriting, never arithmetic.

The loop induction is first-order fuel threading in the
`vecAtSumWhile_correct` shape (induction on fuel, `by_cases`
on the guard, `cir_unfold_leaf` steps). The `LoopOob` bricks
are deliberately NOT reused: `Circe.Crypto` imports `Emit`,
so `Emit` importing `LoopOob` would be an import cycle; each
unfold is a one-line `cir_unfold_leaf` step anyway.
-/
import Circe.Emit.VecRead

/-- Mangled name of the entry. -/
def vecKadaneName : String :=
  "_Z12max_subarrayRKSt6vectorIiSaIiEE"

/-- Signed max of two `i32` words, value-level: the branch both
    `if_` updates compute (stated with `slt` so the eval bridge
    is rewriting, never arithmetic). -/
def imax (a b : BitVec 32) : BitVec 32 :=
  if a.slt b then b else a

/-- Loop body: `x = s[i]; sum = cur+x;` max-update into `sum`;
    `cur = sum;` max-update into `best`; `i++`. All targets are
    pre-bound (the prelude binds `x`/`sum`), so the env shape is
    fixed across iterations. -/
def vecKadaneBody : CStmt :=
  .seq (.assign "x" (.stdVecAt "s" (.var "i")))
  (.seq (.assign "sum" (.add (.var "cur") (.var "x")))
  (.seq (.if_ (.slt (.var "sum") (.var "x"))
            (.assign "sum" (.var "x")) .skip)
  (.seq (.assign "cur" (.var "sum"))
  (.seq (.if_ (.slt (.var "best") (.var "cur"))
            (.assign "best" (.var "cur")) .skip)
    (.assign "i" (.uadd (.var "i")
      (.lit (.u64 (BitVec.ofNat 64 1)))))))))

/-- Loop: `while (i < s.size()) { ... }`. -/
def vecKadaneWhile : CStmt :=
  .while_ (.ult (.var "i") (.stdVecLen "s")) vecKadaneBody

/-- Seed guard: `0 < s.size()` (the fused `at(0)` range check). -/
def vecKadaneSeedGuard : CExpr :=
  .ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "s")

/-- Seed: `cur = best = s[0]`, guarded (empty input takes `fail`,
    the `at()`-throw precedent). -/
def vecKadaneSeed : CStmt :=
  .if_ vecKadaneSeedGuard
    (.seq (.let_ "cur" (.i 32)
              (.stdVecAt "s" (.lit (.u64 (BitVec.ofNat 64 0)))))
          (.let_ "best" (.i 32)
              (.stdVecAt "s" (.lit (.u64 (BitVec.ofNat 64 0))))))
    .fail

/-- Canonical CoreIR for `max_subarray`. -/
def vecKadaneFunc : Func :=
  ⟨vecKadaneName,
   [{ name := "s", ty := stdVecObjTy, role := .sharedBorrow }],
   .i 32,
   .seq vecKadaneSeed
   (.seq (.let_ "x" (.i 32) (.lit (.i32 (BitVec.ofNat 32 0))))
   (.seq (.let_ "sum" (.i 32) (.lit (.i32 (BitVec.ofNat 32 0))))
   (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
   (.seq vecKadaneWhile
         (.return_ (.var "best"))))))⟩

/-- Loop environments: `u64` index `k` plus the two accumulators
    and the two pre-bound scratch words, view fixed (the prelude
    order `i, sum, x, best, cur, s` is pinned here). -/
def mkKadaneEnv (l : List (BitVec 32)) (k : Nat)
    (cur best x sum : BitVec 32) : Env :=
  [("i", .u64 (BitVec.ofNat 64 k)), ("sum", .i32 sum),
   ("x", .i32 x), ("best", .i32 best), ("cur", .i32 cur),
   ("s", .stdVecVal l)]

theorem mkKadaneEnv_i (l : List (BitVec 32)) (k : Nat)
    (cur best x sum : BitVec 32) :
    envLookup (mkKadaneEnv l k cur best x sum) "i" =
      some (.u64 (BitVec.ofNat 64 k)) := by
  simp [mkKadaneEnv, envLookup]

theorem mkKadaneEnv_sum (l : List (BitVec 32)) (k : Nat)
    (cur best x sum : BitVec 32) :
    envLookup (mkKadaneEnv l k cur best x sum) "sum" =
      some (.i32 sum) := by
  simp [mkKadaneEnv, envLookup, show ("sum" : String) ≠ "i" by decide]

theorem mkKadaneEnv_x (l : List (BitVec 32)) (k : Nat)
    (cur best x sum : BitVec 32) :
    envLookup (mkKadaneEnv l k cur best x sum) "x" =
      some (.i32 x) := by
  simp [mkKadaneEnv, envLookup, show ("x" : String) ≠ "i" by decide,
    show ("x" : String) ≠ "sum" by decide]

theorem mkKadaneEnv_best (l : List (BitVec 32)) (k : Nat)
    (cur best x sum : BitVec 32) :
    envLookup (mkKadaneEnv l k cur best x sum) "best" =
      some (.i32 best) := by
  simp [mkKadaneEnv, envLookup, show ("best" : String) ≠ "i" by decide,
    show ("best" : String) ≠ "sum" by decide,
    show ("best" : String) ≠ "x" by decide]

theorem mkKadaneEnv_cur (l : List (BitVec 32)) (k : Nat)
    (cur best x sum : BitVec 32) :
    envLookup (mkKadaneEnv l k cur best x sum) "cur" =
      some (.i32 cur) := by
  simp [mkKadaneEnv, envLookup, show ("cur" : String) ≠ "i" by decide,
    show ("cur" : String) ≠ "sum" by decide,
    show ("cur" : String) ≠ "x" by decide,
    show ("cur" : String) ≠ "best" by decide]

theorem mkKadaneEnv_s (l : List (BitVec 32)) (k : Nat)
    (cur best x sum : BitVec 32) :
    envLookup (mkKadaneEnv l k cur best x sum) "s" =
      some (.stdVecVal l) := by
  simp [mkKadaneEnv, envLookup, show ("s" : String) ≠ "i" by decide,
    show ("s" : String) ≠ "sum" by decide,
    show ("s" : String) ≠ "x" by decide,
    show ("s" : String) ≠ "best" by decide,
    show ("s" : String) ≠ "cur" by decide]

/-! ## Forward model -/

/-- Dual-accumulator fold over the suffix: the `nsw` accumulation
    with loud err-propagation, threading both maxima (the
    `stdVecFold` shape doubled — structural recursion, so the
    loop invariant bridges via `kadaneFold_drop`). -/
def kadaneFold : List (BitVec 32) → BitVec 32 → BitVec 32 →
    Result (BitVec 32 × BitVec 32)
  | [], cur, best => .ok (cur, best)
  | x :: xs, cur, best =>
    match checkedAddI32 cur x with
    | .error e => .error e
    | .ok s => kadaneFold xs (imax s x) (imax best (imax s x))

/-- Value-level forward for `max_subarray`: the fold from the
    `at(0)` seed; empty input is the fused `fail`
    (`AssertFail`, the `at()`-throw precedent). -/
def kadaneFwd : List (BitVec 32) → Result Value
  | [] => .error .AssertFail
  | h :: t => (kadaneFold t h h).map (fun p => .i32 p.2)

/-- `(<$>)` on the pair-valued fold computes on both constructors
    (the `i32_map_error`/`i32_map_ok` shape for pairs). -/
theorem kadaneMap_error (e : Panic) :
    Except.map (fun p : BitVec 32 × BitVec 32 => Value.i32 p.2)
      (Except.error e : Result (BitVec 32 × BitVec 32)) =
      .error e := rfl

theorem kadaneMap_ok (c b : BitVec 32) :
    Except.map (fun p : BitVec 32 × BitVec 32 => Value.i32 p.2)
      (Except.ok (c, b) : Result (BitVec 32 × BitVec 32)) =
      .ok (.i32 b) := rfl

/-- The forward on a failed fold is the error. -/
theorem kadaneFwd_err (h : BitVec 32) (t : List (BitVec 32))
    (e : Panic) (hfold : kadaneFold t h h = .error e) :
    kadaneFwd (h :: t) = .error e := by
  simp [kadaneFwd, hfold, kadaneMap_error]

/-- The forward on a successful fold is the best word. -/
theorem kadaneFwd_ok (h : BitVec 32) (t : List (BitVec 32))
    (c b : BitVec 32) (hfold : kadaneFold t h h = .ok (c, b)) :
    kadaneFwd (h :: t) = .ok (.i32 b) := by
  simp [kadaneFwd, hfold, kadaneMap_ok]

/-! ## Fold unfolding -/

/-- The fold over a dropped suffix unfolds at the live head
    (proved once by list induction, so the loop proof never
    unfolds a well-founded fixpoint — the `stdVecFold_drop`
    shape). Note the `imax` argument order: `imax best cur`
    shares the `best.slt cur` boolean with the second `if_`
    condition (and `imax s x` shares `s.slt x` with the
    first), so every bridge is rewriting. -/
theorem kadaneFold_drop (l : List (BitVec 32)) (k : Nat)
    (cur best : BitVec 32) :
    kadaneFold (l.drop k) cur best =
      match l[k]? with
      | none => .ok (cur, best)
      | some x =>
        match checkedAddI32 cur x with
        | .error e => .error e
        | .ok s =>
          kadaneFold (l.drop (k + 1)) (imax s x)
            (imax best (imax s x)) := by
  induction l generalizing k with
  | nil => simp [kadaneFold]
  | cons y ys ih =>
    cases k with
    | zero => simp [kadaneFold]
    | succ k =>
      simp only [List.drop_succ_cons]
      exact ih k

/-- Unfolding the suffix fold at a live index with a
    successful add. -/
theorem kadaneFold_step (l : List (BitVec 32)) (k : Nat)
    (cur best : BitVec 32) (w s : BitVec 32)
    (hget : l[k]? = some w)
    (hc : checkedAddI32 cur w = .ok s) :
    kadaneFold (l.drop k) cur best =
      kadaneFold (l.drop (k + 1)) (imax s w)
        (imax best (imax s w)) := by
  rw [kadaneFold_drop]; simp only [hget, hc]

/-- Unfolding the suffix fold past the end. -/
theorem kadaneFold_nil (l : List (BitVec 32)) (k : Nat)
    (cur best : BitVec 32)
    (hget : l[k]? = none) :
    kadaneFold (l.drop k) cur best = .ok (cur, best) := by
  rw [kadaneFold_drop]; simp only [hget]

/-- Unfolding the suffix fold at a live index, keeping the
    checked-add match (the error arm stays open for the
    loud-overflow leg). -/
theorem kadaneFold_step_err (l : List (BitVec 32)) (k : Nat)
    (cur best : BitVec 32) (w : BitVec 32)
    (hget : l[k]? = some w) :
    kadaneFold (l.drop k) cur best =
      match checkedAddI32 cur w with
      | .error e => .error e
      | .ok s => kadaneFold (l.drop (k + 1)) (imax s w)
        (imax best (imax s w)) := by
  rw [kadaneFold_drop]; simp only [hget]

/-! ## Seed -/

/-- Seed-guard evaluation: `0 < len` on the reified length. -/
theorem kadaneSeedGuard_eval (l : List (BitVec 32))
    (hl64 : l.length < 2 ^ 64) :
    evalExpr vecKadaneSeedGuard [("s", .stdVecVal l)] =
      .ok (.b (decide (0 < l.length))) := by
  have hs : envLookup [("s", .stdVecVal l)] "s" =
      some (.stdVecVal l) := by
    simp [envLookup]
  have hlen := evalExpr_stdVecLen_some "s" _ l hs
  have h := evalExpr_ult_u64lit (BitVec.ofNat 64 0) _ _ _ hlen
  have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length :=
    ofNat64_toNat _ hl64
  have hz : (0 : Nat) < 2 ^ 64 := by decide
  simpa [vecKadaneSeedGuard, hlenN, ofNat64_ult 0 _ hz] using h

/-- Empty input: the seed guard is false and the fused `fail`
    aborts (any fuel — the `at(0)`-throw precedent). -/
theorem kadaneSeed_empty (F : Nat) :
    evalStmtFuel F vecKadaneSeed [("s", .stdVecVal [])] =
      .error .AssertFail := by
  have hg : evalExpr vecKadaneSeedGuard [("s", .stdVecVal [])] =
      .ok (.b false) := by
    have h := kadaneSeedGuard_eval [] (by decide)
    simpa using h
  simp only [vecKadaneSeed]
  rw [evalStmtFuel_if_false _ _ _ _ _ hg]
  cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith]

/-- Nonempty input: the seed binds `cur = best = head`
    (any fuel). -/
theorem kadaneSeed_hit (F : Nat) (h : BitVec 32)
    (t : List (BitVec 32)) (hl64 : (h :: t).length < 2 ^ 64) :
    evalStmtFuel F vecKadaneSeed [("s", .stdVecVal (h :: t))] =
      .ok ([("best", .i32 h), ("cur", .i32 h),
        ("s", .stdVecVal (h :: t))], .fellThrough) := by
  have hs : envLookup [("s", .stdVecVal (h :: t))] "s" =
      some (.stdVecVal (h :: t)) := by
    simp [envLookup]
  have hg : evalExpr vecKadaneSeedGuard
      [("s", .stdVecVal (h :: t))] = .ok (.b true) := by
    have h0 := kadaneSeedGuard_eval (h :: t) hl64
    simpa using h0
  have hr : evalExpr
      (.stdVecAt "s" (.lit (.u64 (BitVec.ofNat 64 0))))
      [("s", .stdVecVal (h :: t))] = .ok (.i32 h) := by
    have hget : (h :: t)[(BitVec.ofNat 64 0).toNat]? = some h := by
      have h0 : (BitVec.ofNat 64 0).toNat = 0 := by decide
      rw [h0]
      rfl
    exact evalExpr_stdVecAt_some _ _ _ _ _ _ hs
      (evalExpr_lit _ _) hget
  have hrMid : evalExpr
      (.stdVecAt "s" (.lit (.u64 (BitVec.ofNat 64 0))))
      [("cur", .i32 h), ("s", .stdVecVal (h :: t))] =
      .ok (.i32 h) := by
    have hsMid : envLookup
        [("cur", .i32 h), ("s", .stdVecVal (h :: t))] "s" =
        some (.stdVecVal (h :: t)) := by
      simp [envLookup, show ("s" : String) ≠ "cur" by decide]
    have hget : (h :: t)[(BitVec.ofNat 64 0).toNat]? = some h := by
      have h0 : (BitVec.ofNat 64 0).toNat = 0 := by decide
      rw [h0]
      rfl
    exact evalExpr_stdVecAt_some _ _ _ _ _ _ hsMid
      (evalExpr_lit _ _) hget
  simp only [vecKadaneSeed]
  rw [evalStmtFuel_if_true _ _ _ _ _ hg,
    evalStmtFuel_seq_fallthrough _ _ _ _ _
      (evalStmtFuel_let_ _ _ _ _ _ _ hr)]
  exact evalStmtFuel_let_ _ _ _ _ _ _ hrMid


/-! ## Loop -/

/-- Loop-guard evaluation: `k < len` on the reified length. -/
theorem kadaneLoopGuard_eval (l : List (BitVec 32)) (k : Nat)
    (cur best x sum : BitVec 32)
    (hk64 : k < 2 ^ 64) (hl64 : l.length < 2 ^ 64) :
    evalExpr (.ult (.var "i") (.stdVecLen "s"))
      (mkKadaneEnv l k cur best x sum) =
      .ok (.b (decide (k < l.length))) := by
  have hi := mkKadaneEnv_i l k cur best x sum
  have hs := mkKadaneEnv_s l k cur best x sum
  have hlen : (BitVec.ofNat 64 l.length).toNat = l.length :=
    ofNat64_toNat _ hl64
  simp [evalExpr, hi, hs, ofNat64_ult k _ hk64, hlen]

/-- Body with a successful add: both max updates and the advance
    (any fuel). The post-env names the updated accumulators and
    scratch words; the `imax` bridges are rewriting. -/
theorem kadaneBody_ok (F : Nat) (l : List (BitVec 32))
    (k : Nat) (cur best x sum : BitVec 32)
    (w s : BitVec 32)
    (hk64 : k < 2 ^ 64)
    (hget : l[k]? = some w)
    (hc : checkedAddI32 cur w = .ok s) :
    evalStmtFuel F vecKadaneBody (mkKadaneEnv l k cur best x sum) =
      .ok (mkKadaneEnv l (k + 1) (imax s w) (imax best (imax s w))
        w (imax s w), .fellThrough) := by
  have hi := mkKadaneEnv_i l k cur best x sum
  have hs := mkKadaneEnv_s l k cur best x sum
  have hgetB : l[(BitVec.ofNat 64 k).toNat]? = some w := by
    rw [ofNat64_toNat _ hk64]; exact hget
  have hread : evalExpr (.stdVecAt "s" (.var "i"))
      (mkKadaneEnv l k cur best x sum) = .ok (.i32 w) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hs
      (evalExpr_var_hit _ _ _ hi) hgetB
  have huX : envUpdate (mkKadaneEnv l k cur best x sum) "x" (.i32 w) =
      some (mkKadaneEnv l k cur best w sum) := by rfl
  have h1 := evalStmtFuel_assign F _ _ _ _ _ hread huX
  have hcur1 := mkKadaneEnv_cur l k cur best w sum
  have hx1 := mkKadaneEnv_x l k cur best w sum
  have hadd : evalExpr (.add (.var "cur") (.var "x"))
      (mkKadaneEnv l k cur best w sum) = .ok (.i32 s) := by
    cir_step evalExpr [hcur1, hx1, hc]
  have huS : envUpdate (mkKadaneEnv l k cur best w sum) "sum" (.i32 s) =
      some (mkKadaneEnv l k cur best w s) := by rfl
  have h2 := evalStmtFuel_assign F _ _ _ _ _ hadd huS
  have hsum2 := mkKadaneEnv_sum l k cur best w s
  have hx2 := mkKadaneEnv_x l k cur best w s
  have hcond1 : evalExpr (.slt (.var "sum") (.var "x"))
      (mkKadaneEnv l k cur best w s) = .ok (.b (s.slt w)) :=
    evalExpr_slt_i32 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hsum2) (evalExpr_var_hit _ _ _ hx2)
  have hlit1 : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      (mkKadaneEnv l k cur best x sum) =
      .ok (.u64 (BitVec.ofNat 64 1)) :=
    evalExpr_lit _ _
  cases hslt1 : s.slt w with
  | true =>
    have himax1 : imax s w = w := by simp [imax, hslt1]
    have hcondT : evalExpr (.slt (.var "sum") (.var "x"))
        (mkKadaneEnv l k cur best w s) = .ok (.b true) := by
      rwa [hslt1] at hcond1
    have huS1 : envUpdate (mkKadaneEnv l k cur best w s) "sum" (.i32 w) =
        some (mkKadaneEnv l k cur best w w) := by rfl
    have h3a := evalStmtFuel_assign F _ _ _ _ _
      (evalExpr_var_hit _ _ _ hx2) huS1
    have h3 : evalStmtFuel F
        (.if_ (.slt (.var "sum") (.var "x"))
          (.assign "sum" (.var "x")) .skip)
        (mkKadaneEnv l k cur best w s) =
        .ok (mkKadaneEnv l k cur best w w, .fellThrough) := by
      rw [evalStmtFuel_if_true _ _ _ _ _ hcondT]
      exact h3a
    have hsum3 := mkKadaneEnv_sum l k cur best w w
    have hcur3 := mkKadaneEnv_cur l k cur best w w
    have hbest3 := mkKadaneEnv_best l k cur best w w
    have h4v : evalExpr (.var "sum")
        (mkKadaneEnv l k cur best w w) = .ok (.i32 w) :=
      evalExpr_var_hit _ _ _ hsum3
    have huC : envUpdate (mkKadaneEnv l k cur best w w) "cur" (.i32 w) =
        some (mkKadaneEnv l k w best w w) := by rfl
    have h4 := evalStmtFuel_assign F _ _ _ _ _ h4v huC
    have hbest4 := mkKadaneEnv_best l k w best w w
    have hcur4 := mkKadaneEnv_cur l k w best w w
    have hcond2 : evalExpr (.slt (.var "best") (.var "cur"))
        (mkKadaneEnv l k w best w w) =
        .ok (.b (best.slt (imax s w))) := by
      have hcurV : evalExpr (.var "cur")
          (mkKadaneEnv l k w best w w) = .ok (.i32 (imax s w)) := by
        rw [himax1]; exact evalExpr_var_hit _ _ _ hcur4
      exact evalExpr_slt_i32 _ _ _ _ _
        (evalExpr_var_hit _ _ _ hbest4) hcurV
    cases hslt2 : best.slt (imax s w) with
    | true =>
      have h2w : best.slt w = true := by
        rw [himax1] at hslt2; exact hslt2
      have himax2 : imax best (imax s w) = imax s w := by
        simp [imax, hslt1, h2w]
      have hcondT2 : evalExpr (.slt (.var "best") (.var "cur"))
          (mkKadaneEnv l k w best w w) = .ok (.b true) := by
        rwa [hslt2] at hcond2
      have hcurV : evalExpr (.var "cur")
          (mkKadaneEnv l k w best w w) = .ok (.i32 w) :=
        evalExpr_var_hit _ _ _ hcur4
      have huB : envUpdate (mkKadaneEnv l k w best w w) "best" (.i32 w) =
          some (mkKadaneEnv l k w w w w) := by rfl
      have h5a := evalStmtFuel_assign F _ _ _ _ _ hcurV huB
      have h5 : evalStmtFuel F
          (.if_ (.slt (.var "best") (.var "cur"))
            (.assign "best" (.var "cur")) .skip)
          (mkKadaneEnv l k w best w w) =
          .ok (mkKadaneEnv l k w w w w, .fellThrough) := by
        rw [evalStmtFuel_if_true _ _ _ _ _ hcondT2]
        exact h5a
      have hi5 := mkKadaneEnv_i l k w w w w
      have haddI : evalExpr
          (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1))))
          (mkKadaneEnv l k w w w w) =
          .ok (.u64 (BitVec.ofNat 64 k + BitVec.ofNat 64 1)) := by
        simp only [evalExpr, litVal, hi5]
      have huI : envUpdate (mkKadaneEnv l k w w w w) "i"
          (.u64 (BitVec.ofNat 64 k + BitVec.ofNat 64 1)) =
          some (mkKadaneEnv l (k + 1) w w w w) := by
        simp [mkKadaneEnv, envUpdate, ofNat64_add_one]
      have h6 := evalStmtFuel_assign F _ _ _ _ _ haddI huI
      rw [himax2, himax1]
      simp only [vecKadaneBody]
      rw [evalStmtFuel_seq_fallthrough _ _ _ _ _ h1,
        evalStmtFuel_seq_fallthrough _ _ _ _ _ h2,
        evalStmtFuel_seq_fallthrough _ _ _ _ _ h3,
        evalStmtFuel_seq_fallthrough _ _ _ _ _ h4,
        evalStmtFuel_seq_fallthrough _ _ _ _ _ h5]
      exact h6
    | false =>
      have h2w : best.slt w = false := by
        rw [himax1] at hslt2; exact hslt2
      have himax2 : imax best (imax s w) = best := by
        simp [imax, hslt1, h2w]
      have hcondF2 : evalExpr (.slt (.var "best") (.var "cur"))
          (mkKadaneEnv l k w best w w) = .ok (.b false) := by
        rwa [hslt2] at hcond2
      have h5skip : evalStmtFuel F .skip
          (mkKadaneEnv l k w best w w) =
          .ok (mkKadaneEnv l k w best w w, .fellThrough) := by
        cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith]
      have h5 : evalStmtFuel F
          (.if_ (.slt (.var "best") (.var "cur"))
            (.assign "best" (.var "cur")) .skip)
          (mkKadaneEnv l k w best w w) =
          .ok (mkKadaneEnv l k w best w w, .fellThrough) := by
        rw [evalStmtFuel_if_false _ _ _ _ _ hcondF2]
        exact h5skip
      have hi5 := mkKadaneEnv_i l k w best w w
      have haddI : evalExpr
          (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1))))
          (mkKadaneEnv l k w best w w) =
          .ok (.u64 (BitVec.ofNat 64 k + BitVec.ofNat 64 1)) := by
        simp only [evalExpr, litVal, hi5]
      have huI : envUpdate (mkKadaneEnv l k w best w w) "i"
          (.u64 (BitVec.ofNat 64 k + BitVec.ofNat 64 1)) =
          some (mkKadaneEnv l (k + 1) w best w w) := by
        simp [mkKadaneEnv, envUpdate, ofNat64_add_one]
      have h6 := evalStmtFuel_assign F _ _ _ _ _ haddI huI
      rw [himax2, himax1]
      simp only [vecKadaneBody]
      rw [evalStmtFuel_seq_fallthrough _ _ _ _ _ h1,
        evalStmtFuel_seq_fallthrough _ _ _ _ _ h2,
        evalStmtFuel_seq_fallthrough _ _ _ _ _ h3,
        evalStmtFuel_seq_fallthrough _ _ _ _ _ h4,
        evalStmtFuel_seq_fallthrough _ _ _ _ _ h5]
      exact h6
  | false =>
    have himax1 : imax s w = s := by simp [imax, hslt1]
    have hcondF : evalExpr (.slt (.var "sum") (.var "x"))
        (mkKadaneEnv l k cur best w s) = .ok (.b false) := by
      rwa [hslt1] at hcond1
    have h3skip : evalStmtFuel F .skip
        (mkKadaneEnv l k cur best w s) =
        .ok (mkKadaneEnv l k cur best w s, .fellThrough) := by
      cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith]
    have h3 : evalStmtFuel F
        (.if_ (.slt (.var "sum") (.var "x"))
          (.assign "sum" (.var "x")) .skip)
        (mkKadaneEnv l k cur best w s) =
        .ok (mkKadaneEnv l k cur best w s, .fellThrough) := by
      rw [evalStmtFuel_if_false _ _ _ _ _ hcondF]
      exact h3skip
    have hcur3 := mkKadaneEnv_cur l k cur best w s
    have hsum3 := mkKadaneEnv_sum l k cur best w s
    have hbest3 := mkKadaneEnv_best l k cur best w s
    have h4v : evalExpr (.var "sum")
        (mkKadaneEnv l k cur best w s) = .ok (.i32 s) :=
      evalExpr_var_hit _ _ _ hsum3
    have huC : envUpdate (mkKadaneEnv l k cur best w s) "cur" (.i32 s) =
        some (mkKadaneEnv l k s best w s) := by rfl
    have h4 := evalStmtFuel_assign F _ _ _ _ _ h4v huC
    have hbest4 := mkKadaneEnv_best l k s best w s
    have hcur4 := mkKadaneEnv_cur l k s best w s
    have hcond2 : evalExpr (.slt (.var "best") (.var "cur"))
        (mkKadaneEnv l k s best w s) =
        .ok (.b (best.slt (imax s w))) := by
      have hcurV : evalExpr (.var "cur")
          (mkKadaneEnv l k s best w s) = .ok (.i32 (imax s w)) := by
        rw [himax1]; exact evalExpr_var_hit _ _ _ hcur4
      exact evalExpr_slt_i32 _ _ _ _ _
        (evalExpr_var_hit _ _ _ hbest4) hcurV
    cases hslt2 : best.slt (imax s w) with
    | true =>
      have h2w : best.slt s = true := by
        rw [himax1] at hslt2; exact hslt2
      have himax2 : imax best (imax s w) = imax s w := by
        simp [imax, hslt1, h2w]
      have hcondT2 : evalExpr (.slt (.var "best") (.var "cur"))
          (mkKadaneEnv l k s best w s) = .ok (.b true) := by
        rwa [hslt2] at hcond2
      have hcurV : evalExpr (.var "cur")
          (mkKadaneEnv l k s best w s) = .ok (.i32 s) :=
        evalExpr_var_hit _ _ _ hcur4
      have huB : envUpdate (mkKadaneEnv l k s best w s) "best" (.i32 s) =
          some (mkKadaneEnv l k s s w s) := by rfl
      have h5a := evalStmtFuel_assign F _ _ _ _ _ hcurV huB
      have h5 : evalStmtFuel F
          (.if_ (.slt (.var "best") (.var "cur"))
            (.assign "best" (.var "cur")) .skip)
          (mkKadaneEnv l k s best w s) =
          .ok (mkKadaneEnv l k s s w s, .fellThrough) := by
        rw [evalStmtFuel_if_true _ _ _ _ _ hcondT2]
        exact h5a
      have hi5 := mkKadaneEnv_i l k s s w s
      have haddI : evalExpr
          (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1))))
          (mkKadaneEnv l k s s w s) =
          .ok (.u64 (BitVec.ofNat 64 k + BitVec.ofNat 64 1)) := by
        simp only [evalExpr, litVal, hi5]
      have huI : envUpdate (mkKadaneEnv l k s s w s) "i"
          (.u64 (BitVec.ofNat 64 k + BitVec.ofNat 64 1)) =
          some (mkKadaneEnv l (k + 1) s s w s) := by
        simp [mkKadaneEnv, envUpdate, ofNat64_add_one]
      have h6 := evalStmtFuel_assign F _ _ _ _ _ haddI huI
      rw [himax2, himax1]
      simp only [vecKadaneBody]
      rw [evalStmtFuel_seq_fallthrough _ _ _ _ _ h1,
        evalStmtFuel_seq_fallthrough _ _ _ _ _ h2,
        evalStmtFuel_seq_fallthrough _ _ _ _ _ h3,
        evalStmtFuel_seq_fallthrough _ _ _ _ _ h4,
        evalStmtFuel_seq_fallthrough _ _ _ _ _ h5]
      exact h6
    | false =>
      have h2w : best.slt s = false := by
        rw [himax1] at hslt2; exact hslt2
      have himax2 : imax best (imax s w) = best := by
        simp [imax, hslt1, h2w]
      have hcondF2 : evalExpr (.slt (.var "best") (.var "cur"))
          (mkKadaneEnv l k s best w s) = .ok (.b false) := by
        rwa [hslt2] at hcond2
      have h5skip : evalStmtFuel F .skip
          (mkKadaneEnv l k s best w s) =
          .ok (mkKadaneEnv l k s best w s, .fellThrough) := by
        cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith]
      have h5 : evalStmtFuel F
          (.if_ (.slt (.var "best") (.var "cur"))
            (.assign "best" (.var "cur")) .skip)
          (mkKadaneEnv l k s best w s) =
          .ok (mkKadaneEnv l k s best w s, .fellThrough) := by
        rw [evalStmtFuel_if_false _ _ _ _ _ hcondF2]
        exact h5skip
      have hi5 := mkKadaneEnv_i l k s best w s
      have haddI : evalExpr
          (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1))))
          (mkKadaneEnv l k s best w s) =
          .ok (.u64 (BitVec.ofNat 64 k + BitVec.ofNat 64 1)) := by
        simp only [evalExpr, litVal, hi5]
      have huI : envUpdate (mkKadaneEnv l k s best w s) "i"
          (.u64 (BitVec.ofNat 64 k + BitVec.ofNat 64 1)) =
          some (mkKadaneEnv l (k + 1) s best w s) := by
        simp [mkKadaneEnv, envUpdate, ofNat64_add_one]
      have h6 := evalStmtFuel_assign F _ _ _ _ _ haddI huI
      rw [himax2, himax1]
      simp only [vecKadaneBody]
      rw [evalStmtFuel_seq_fallthrough _ _ _ _ _ h1,
        evalStmtFuel_seq_fallthrough _ _ _ _ _ h2,
        evalStmtFuel_seq_fallthrough _ _ _ _ _ h3,
        evalStmtFuel_seq_fallthrough _ _ _ _ _ h4,
        evalStmtFuel_seq_fallthrough _ _ _ _ _ h5]
      exact h6


/-- Body with an overflowing add: the `nsw` error is loud, the
    index never advances (any fuel). -/
theorem kadaneBody_add_err (F : Nat) (l : List (BitVec 32))
    (k : Nat) (cur best x sum : BitVec 32)
    (w : BitVec 32) (e : Panic)
    (hk64 : k < 2 ^ 64)
    (hget : l[k]? = some w)
    (hc : checkedAddI32 cur w = .error e) :
    evalStmtFuel F vecKadaneBody (mkKadaneEnv l k cur best x sum) =
      .error e := by
  have hi := mkKadaneEnv_i l k cur best x sum
  have hs := mkKadaneEnv_s l k cur best x sum
  have hcur := mkKadaneEnv_cur l k cur best x sum
  have hx := mkKadaneEnv_x l k cur best x sum
  have hgetB : l[(BitVec.ofNat 64 k).toNat]? = some w := by
    rw [ofNat64_toNat _ hk64]; exact hget
  have hread : evalExpr (.stdVecAt "s" (.var "i"))
      (mkKadaneEnv l k cur best x sum) = .ok (.i32 w) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hs
      (evalExpr_var_hit _ _ _ hi) hgetB
  have huX : envUpdate (mkKadaneEnv l k cur best x sum) "x" (.i32 w) =
      some (mkKadaneEnv l k cur best w sum) := by rfl
  have h1 := evalStmtFuel_assign F _ _ _ _ _ hread huX
  have hcur1 := mkKadaneEnv_cur l k cur best w sum
  have hx1 := mkKadaneEnv_x l k cur best w sum
  have haddE : evalExpr (.add (.var "cur") (.var "x"))
      (mkKadaneEnv l k cur best w sum) = .error e := by
    cir_step evalExpr [hcur1, hx1, hc]
  have h2 : evalStmtFuel F
      (.assign "sum" (.add (.var "cur") (.var "x")))
      (mkKadaneEnv l k cur best w sum) = .error e := by
    cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith, haddE]
  simp only [vecKadaneBody]
  rw [evalStmtFuel_seq_fallthrough _ _ _ _ _ h1,
    evalStmtFuel_seq_err _ _ _ _ _ h2]

/-- Loop correctness: folds the checked-add suffix, exits with
    `i = length` (fuel-generalized induction in the
    `vecAtSumWhile_correct` shape; the ok post-env carries the
    final accumulators with existentially-bound scratch words —
    the prelude seeds them, the body overwrites before reading). -/
theorem kadaneWhile_correct (l : List (BitVec 32))
    (F : Nat) (k : Nat) (cur best x sum : BitVec 32)
    (hk : k ≤ l.length) (hl64 : l.length < 2 ^ 64)
    (hF : l.length - k + 1 ≤ F) :
    match kadaneFold (l.drop k) cur best with
    | .error e =>
      evalStmtFuel F vecKadaneWhile (mkKadaneEnv l k cur best x sum) =
        .error e
    | .ok (c, b) =>
      ∃ x' s', evalStmtFuel F vecKadaneWhile
        (mkKadaneEnv l k cur best x sum) =
        .ok (mkKadaneEnv l l.length c b x' s', .fellThrough) := by
  induction F generalizing k cur best x sum with
  | zero => omega
  | succ F ih =>
    by_cases hlt : k < l.length
    · have hk64 : k < 2 ^ 64 := by omega
      have hget : l[k]? = some l[k] := List.getElem?_eq_getElem hlt
      have hcond : evalExpr (.ult (.var "i") (.stdVecLen "s"))
            (mkKadaneEnv l k cur best x sum) = .ok (.b true) := by
        simpa [hlt] using
          (kadaneLoopGuard_eval l k cur best x sum hk64 hl64)
      have hunfold := kadaneFold_step_err l k cur best l[k] hget
      cases hc : checkedAddI32 cur l[k] with
      | error e =>
        have hbody := kadaneBody_add_err F l k cur best x sum l[k] e
          hk64 hget hc
        have hstep : evalStmtFuel (F + 1) vecKadaneWhile
            (mkKadaneEnv l k cur best x sum) = .error e := by
          cir_unfold_leaf (vecKadaneWhile, hcond, hbody)
        rw [hstep, hunfold, hc]
      | ok s =>
        have hbody := kadaneBody_ok F l k cur best x sum l[k] s
          hk64 hget hc
        have hstep : evalStmtFuel (F + 1) vecKadaneWhile
            (mkKadaneEnv l k cur best x sum) =
            evalStmtFuel F vecKadaneWhile
              (mkKadaneEnv l (k + 1) (imax s l[k])
                (imax best (imax s l[k])) l[k] (imax s l[k])) := by
          cir_unfold_leaf (vecKadaneWhile, hcond, hbody)
        have hunfoldOk := kadaneFold_step l k cur best l[k] s hget hc
        rw [hstep, hunfoldOk]
        exact ih (k + 1) (imax s l[k]) (imax best (imax s l[k]))
          l[k] (imax s l[k]) (by omega) (by omega)
    · have hkk : k = l.length := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "i") (.stdVecLen "s"))
            (mkKadaneEnv l l.length cur best x sum) =
            .ok (.b false) := by
        have hfalse : (decide (l.length < l.length)) = false := by
          simp
        have hk64 : l.length < 2 ^ 64 := hl64
        have h := kadaneLoopGuard_eval l l.length cur best x sum
          hk64 hl64
        rwa [hfalse] at h
      have hexit : evalStmtFuel (F + 1) vecKadaneWhile
            (mkKadaneEnv l l.length cur best x sum) =
            .ok (mkKadaneEnv l l.length cur best x sum,
              .fellThrough) := by
        simp only [vecKadaneWhile]
        simp [evalStmtFuel, evalStmtSuccHandler, evalStmtWith, hcond]
      have hdropLen : l.drop l.length = [] := by simp
      rw [hdropLen]
      exact ⟨x, sum, hexit⟩

/-- `emit_correct` for `max_subarray`, fuel-generalized (the S3a
    shape; the fuel hypothesis is the slice's dynamic-length side
    condition). -/
theorem evalFuncFuel_vecKadane (F : Nat) (l : List (BitVec 32))
    (hl64 : l.length < 2 ^ 64) (hF : l.length + 1 ≤ F) :
    evalFuncFuel F vecKadaneFunc [.stdVecVal l] = kadaneFwd l := by
  have hbind : bindArgs vecKadaneFunc.args [.stdVecVal l] =
      some [("s", .stdVecVal l)] := rfl
  have hbody : vecKadaneFunc.body =
      .seq vecKadaneSeed
      (.seq (.let_ "x" (.i 32) (.lit (.i32 (BitVec.ofNat 32 0))))
      (.seq (.let_ "sum" (.i 32) (.lit (.i32 (BitVec.ofNat 32 0))))
      (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      (.seq vecKadaneWhile
            (.return_ (.var "best")))))) := rfl
  cases l with
  | nil =>
    have hfwd : kadaneFwd [] = .error .AssertFail := rfl
    cases F with
    | zero =>
      have hseedW : evalStmtWith evalStmtZeroHandler vecKadaneSeed
          [("s", .stdVecVal [])] = .error .AssertFail :=
        kadaneSeed_empty 0
      simp [evalFuncFuel, vecKadaneFunc, hbind, hbody, bindArgs, evalStmtFuel,
        evalStmtZero, evalStmtWith, hseedW, hfwd]
    | succ F =>
      have hseedW : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          vecKadaneSeed [("s", .stdVecVal [])] = .error .AssertFail :=
        kadaneSeed_empty (F + 1)
      simp [evalFuncFuel, vecKadaneFunc, hbind, hbody, bindArgs, evalStmtFuel,
        evalStmtWith, hseedW, hfwd]
  | cons h t =>
    have hlen : (h :: t).length < 2 ^ 64 := hl64
    have henv : [("i", .u64 (BitVec.ofNat 64 1)),
        ("sum", .i32 (BitVec.ofNat 32 0)),
        ("x", .i32 (BitVec.ofNat 32 0)),
        ("best", .i32 h), ("cur", .i32 h),
        ("s", .stdVecVal (h :: t))]
        = mkKadaneEnv (h :: t) 1 h h (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) := rfl
    have hdrop : (h :: t).drop 1 = t := rfl
    cases hfold : kadaneFold t h h with
    | error e =>
      have hsum0 : kadaneFwd (h :: t) = .error e :=
        kadaneFwd_err h t e hfold
      cases F with
      | zero =>
        have hloopH0 : evalStmtWith evalStmtZeroHandler
              vecKadaneWhile (mkKadaneEnv (h :: t) 1 h h (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)) =
              .error e := by
          have h := kadaneWhile_correct (h :: t) 0 1 h h (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)
            (Nat.succ_le_succ (Nat.zero_le _)) hlen (by omega)
          rwa [hdrop, hfold] at h
        have hseedW : evalStmtWith evalStmtZeroHandler vecKadaneSeed
            [("s", .stdVecVal (h :: t))] =
            .ok ([("best", .i32 h), ("cur", .i32 h),
              ("s", .stdVecVal (h :: t))], .fellThrough) :=
          kadaneSeed_hit 0 h t hlen
        simp [evalFuncFuel, vecKadaneFunc, hbind, hbody, bindArgs, evalStmtFuel,
          evalStmtZero, evalStmtWith, evalExpr, litVal, envExtend,
          henv, hseedW, hloopH0, hsum0]
      | succ F =>
        have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
              vecKadaneWhile (mkKadaneEnv (h :: t) 1 h h (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)) =
              .error e := by
          have h := kadaneWhile_correct (h :: t) (F + 1) 1 h h 0 0
            (Nat.succ_le_succ (Nat.zero_le _)) hlen (by omega)
          rwa [hdrop, hfold] at h
        have hseedW : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
            vecKadaneSeed [("s", .stdVecVal (h :: t))] =
            .ok ([("best", .i32 h), ("cur", .i32 h),
              ("s", .stdVecVal (h :: t))], .fellThrough) :=
          kadaneSeed_hit (F + 1) h t hlen
        simp [evalFuncFuel, vecKadaneFunc, hbind, hbody, bindArgs, evalStmtFuel,
          evalStmtWith, evalExpr, litVal, envExtend,
          henv, hseedW, hloopS, hsum0]
    | ok p =>
      obtain ⟨c, b⟩ := p
      have hsum0 : kadaneFwd (h :: t) = .ok (.i32 b) :=
        kadaneFwd_ok h t c b hfold
      cases F with
      | zero =>
        have h := kadaneWhile_correct (h :: t) 0 1 h h (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)
          (Nat.succ_le_succ (Nat.zero_le _)) hlen (by omega)
        simp only [hdrop, hfold] at h
        obtain ⟨x', s', hloopH0⟩ := h
        have hloopH0w : evalStmtWith evalStmtZeroHandler vecKadaneWhile
            (mkKadaneEnv (h :: t) 1 h h (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)) =
            .ok (mkKadaneEnv (h :: t) (h :: t).length c b x' s', .fellThrough) :=
          hloopH0
        have hsret : envLookup
            (mkKadaneEnv (h :: t) (t.length + 1) c b x' s') "best" =
            some (.i32 b) :=
          mkKadaneEnv_best _ _ _ _ _ _
        have hseedW : evalStmtWith evalStmtZeroHandler vecKadaneSeed
            [("s", .stdVecVal (h :: t))] =
            .ok ([("best", .i32 h), ("cur", .i32 h),
              ("s", .stdVecVal (h :: t))], .fellThrough) :=
          kadaneSeed_hit 0 h t hlen
        simp [evalFuncFuel, vecKadaneFunc, hbind, hbody, bindArgs, evalStmtFuel,
          evalStmtZero, evalStmtWith, evalExpr, litVal, envExtend,
          henv, hseedW, hloopH0w, hsret, hsum0]
      | succ F =>
        have h := kadaneWhile_correct (h :: t) (F + 1) 1 h h 0 0
          (Nat.succ_le_succ (Nat.zero_le _)) hlen (by omega)
        simp only [hdrop, hfold] at h
        obtain ⟨x', s', hloopS⟩ := h
        have hloopSw : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
            vecKadaneWhile
            (mkKadaneEnv (h :: t) 1 h h (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)) =
            .ok (mkKadaneEnv (h :: t) (h :: t).length c b x' s', .fellThrough) :=
          hloopS
        have hsret : envLookup
            (mkKadaneEnv (h :: t) (t.length + 1) c b x' s') "best" =
            some (.i32 b) :=
          mkKadaneEnv_best _ _ _ _ _ _
        have hseedW : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
            vecKadaneSeed [("s", .stdVecVal (h :: t))] =
            .ok ([("best", .i32 h), ("cur", .i32 h),
              ("s", .stdVecVal (h :: t))], .fellThrough) :=
          kadaneSeed_hit (F + 1) h t hlen
        simp [evalFuncFuel, vecKadaneFunc, hbind, hbody, bindArgs, evalStmtFuel,
          evalStmtWith, evalExpr, litVal, envExtend,
          henv, hseedW, hsret, hloopSw, hsum0]