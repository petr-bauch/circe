/-
Circe.Emit.Flow — S3a control flow: `nested_sum`, `skip_sum`
(break/continue), `find_eq` (early return), `cls` (switch-as-if-chain).
-/
import Circe.Emit.Fragment

/-! ## S3a: control-flow hardening (nested loops, break/continue,
early return, switch-as-if-chain) -/

/-! ### Word bridges for the new ops -/

/-- `umul` on `ofNat` words is `ofNat` of the product (wrapping
    unsigned multiplication; cf. `ofNat32_add_one`). -/
theorem ofNat32_mul (k j : Nat) :
    BitVec.ofNat 32 k * BitVec.ofNat 32 j = BitVec.ofNat 32 (k * j) :=
  (BitVec.ofNat_mul (n := 32) k j).symm

/-- `ofNat` is injective below `2^32` (for `ueq` condition reasoning). -/
theorem ofNat32_inj (k c : Nat) (hk : k < 2 ^ 32) (hc : c < 2 ^ 32)
    (h : BitVec.ofNat 32 k = BitVec.ofNat 32 c) : k = c := by
  have hcongr := congrArg BitVec.toNat h
  rw [ofNat32_toNat k hk, ofNat32_toNat c hc] at hcongr
  exact hcongr

/-- Word `==` on `ofNat` values decides `Nat` equality (below `2^32`). -/
theorem ofNat32_beq (k c : Nat) (hk : k < 2 ^ 32) (hc : c < 2 ^ 32) :
    (BitVec.ofNat 32 k == BitVec.ofNat 32 c) = decide (k = c) := by
  by_cases h : k = c
  · subst h; simp
  · have hne : BitVec.ofNat 32 k ≠ BitVec.ofNat 32 c :=
      fun heq => h (ofNat32_inj k c hk hc heq)
    simp [h, hne]

/-! ### `nested_sum`: nested bounded `u32` loops -/

/-- Suffix row sum: `Σ_{j∈[t,m)} ofNat (i*j)` (inner-loop invariant). -/
def rowSuffixU32 (i t m : Nat) : BitVec 32 :=
  (((List.range' t (m - t)).map (fun j => BitVec.ofNat 32 (i * j)))).sum

/-- Suffix nest sum: `Σ_{i∈[k,n)} rowU32 i m` (outer-loop invariant). -/
def nestSuffixU32 (k n m : Nat) : BitVec 32 :=
  (((List.range' k (n - k)).map (fun i => rowU32 i m))).sum

/-- Inner step: peeling `t < m` exposes the head product. -/
theorem rowSuffix_step (i t m : Nat) (h : t < m) :
    rowSuffixU32 i t m =
      BitVec.ofNat 32 (i * t) + rowSuffixU32 i (t + 1) m := by
  have hsub : m - t = (m - (t + 1)) + 1 := by omega
  simp [rowSuffixU32, hsub, List.range'_succ, List.map_cons, List.sum_cons,
    BitVec.add_comm (BitVec.ofNat 32 (i * t)) _]

/-- Inner exit: empty suffix sums to zero. -/
theorem rowSuffix_nil (i t : Nat) :
    rowSuffixU32 i t t = 0 := by
  simp [rowSuffixU32]

/-- Full row is the suffix from zero. -/
theorem rowSuffix_full (i m : Nat) :
    rowSuffixU32 i 0 m = rowU32 i m := by
  simp [rowSuffixU32, rowU32, List.range_eq_range']

/-- Outer step: peeling `k < n` exposes the head row. -/
theorem nestSuffix_step (k n m : Nat) (h : k < n) :
    nestSuffixU32 k n m = rowU32 k m + nestSuffixU32 (k + 1) n m := by
  have hsub : n - k = (n - (k + 1)) + 1 := by omega
  simp [nestSuffixU32, hsub, List.range'_succ, List.map_cons, List.sum_cons,
    BitVec.add_comm (rowU32 k m) _]

/-- Outer exit: empty suffix sums to zero. -/
theorem nestSuffix_nil (k n m : Nat) (h : n ≤ k) :
    nestSuffixU32 k n m = 0 := by
  have hsub : n - k = 0 := by omega
  simp [nestSuffixU32, hsub]

/-- Full nest is the suffix from zero. -/
theorem nestSuffix_full (n m : Nat) :
    nestSuffixU32 0 n m = nestedSumU32 n m := by
  simp [nestSuffixU32, nestedSumU32, List.range_eq_range']

/-- Inner body: `s = s + i*j; j = j+1` (wrapping `u32`). -/
def nestedBodyInner : CStmt :=
  .seq (.assign "s" (.uadd (.var "s") (.umul (.var "i") (.var "j"))))
       (.assign "j" (.uadd (.var "j") (.lit (.u32 (BitVec.ofNat 32 1)))))

/-- Inner loop: `while (j < m) { ... }`. -/
def nestedInner : CStmt :=
  .while_ (.ult (.var "j") (.var "m")) nestedBodyInner

/-- Outer body: run the inner loop, step `i`, reset `j` to `0`.
    The reset comes last so the outer-loop-head invariant (`j = 0`)
    holds every iteration (first iteration from the initial `let`). -/
def nestedBodyOuter : CStmt :=
  .seq nestedInner (.seq (.assign "i" (.uadd (.var "i") (.lit (.u32 (BitVec.ofNat 32 1))))) (.assign "j" (.lit (.u32 (BitVec.ofNat 32 0)))))

/-- Outer loop: `while (i < n) { ... }`. -/
def nestedOuter : CStmt :=
  .while_ (.ult (.var "i") (.var "n")) nestedBodyOuter

/-- Canonical CoreIR for `tests/c/nested_sum.c`. Both bounds are plain
    `u32` values (no array: no `OOB`; fuel exhaustion past `EVAL_FUEL`
    is `AssertFail`, discharged by the `hF` side condition). -/
def nestedFunc : Func :=
  ⟨"nested_sum",
   [{ name := "n", ty := .u 32, role := .owned },
    { name := "m", ty := .u 32, role := .owned }],
   .u 32,
   .seq (.let_ "s" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
   (.seq (.let_ "i" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
   (.seq (.let_ "j" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
   (.seq nestedOuter
         (.return_ (.var "s")))))⟩

/-- Value-level forward for `nested_sum` (cf. rendered `nested_sum_fwd`,
    which references `Base.nestedSumU32`). -/
def nestedFwd (n m : BitVec 32) : Result Value :=
  .ok (.u32 (nestedSumU32 n.toNat m.toNat))

/-- Loop environments: outer index `k`, accumulator, inner index `t`,
    bounds fixed. -/
def mkNestedEnv (nv mv : BitVec 32) (k : Nat) (acc : BitVec 32)
    (t : Nat) : Env :=
  [("j", .u32 (BitVec.ofNat 32 t)), ("i", .u32 (BitVec.ofNat 32 k)),
   ("s", .u32 acc), ("n", .u32 nv), ("m", .u32 mv)]

theorem mkNestedEnv_j (nv mv : BitVec 32) (k : Nat) (acc : BitVec 32)
    (t : Nat) :
    envLookup (mkNestedEnv nv mv k acc t) "j" =
      some (.u32 (BitVec.ofNat 32 t)) := by
  simp [mkNestedEnv, envLookup]

theorem mkNestedEnv_i (nv mv : BitVec 32) (k : Nat) (acc : BitVec 32)
    (t : Nat) :
    envLookup (mkNestedEnv nv mv k acc t) "i" =
      some (.u32 (BitVec.ofNat 32 k)) := by
  simp [mkNestedEnv, envLookup, show ("i" : String) ≠ "j" by decide]

theorem mkNestedEnv_s (nv mv : BitVec 32) (k : Nat) (acc : BitVec 32)
    (t : Nat) :
    envLookup (mkNestedEnv nv mv k acc t) "s" = some (.u32 acc) := by
  simp [mkNestedEnv, envLookup, show ("s" : String) ≠ "j" by decide,
    show ("s" : String) ≠ "i" by decide]

theorem mkNestedEnv_n (nv mv : BitVec 32) (k : Nat) (acc : BitVec 32)
    (t : Nat) :
    envLookup (mkNestedEnv nv mv k acc t) "n" = some (.u32 nv) := by
  simp [mkNestedEnv, envLookup, show ("n" : String) ≠ "j" by decide,
    show ("n" : String) ≠ "i" by decide,
    show ("n" : String) ≠ "s" by decide]

theorem mkNestedEnv_m (nv mv : BitVec 32) (k : Nat) (acc : BitVec 32)
    (t : Nat) :
    envLookup (mkNestedEnv nv mv k acc t) "m" = some (.u32 mv) := by
  simp [mkNestedEnv, envLookup, show ("m" : String) ≠ "j" by decide,
    show ("m" : String) ≠ "i" by decide,
    show ("m" : String) ≠ "s" by decide,
    show ("m" : String) ≠ "n" by decide]

/-- Updating `s` stays in the env family. -/
theorem nestedEnv_update_s (nv mv : BitVec 32) (k t : Nat)
    (acc v : BitVec 32) :
    envUpdate (mkNestedEnv nv mv k acc t) "s" (.u32 v) =
      some (mkNestedEnv nv mv k v t) := by
  simp [mkNestedEnv, envUpdate, show ("s" : String) ≠ "j" by decide,
    show ("s" : String) ≠ "i" by decide]

/-- Updating `j` stays in the env family. -/
theorem nestedEnv_update_j (nv mv : BitVec 32) (k t t' : Nat)
    (acc : BitVec 32) :
    envUpdate (mkNestedEnv nv mv k acc t) "j"
        (.u32 (BitVec.ofNat 32 t')) =
      some (mkNestedEnv nv mv k acc t') := by
  simp [mkNestedEnv, envUpdate]

/-- Updating `i` stays in the env family. -/
theorem nestedEnv_update_i (nv mv : BitVec 32) (k k' t : Nat)
    (acc : BitVec 32) :
    envUpdate (mkNestedEnv nv mv k acc t) "i"
        (.u32 (BitVec.ofNat 32 k')) =
      some (mkNestedEnv nv mv k' acc t) := by
  simp [mkNestedEnv, envUpdate, show ("i" : String) ≠ "j" by decide]

/-- Inner condition reads `j` against `m`. -/
theorem nestedCondInner_eval (nv mv : BitVec 32) (k t : Nat)
    (acc : BitVec 32) (h : t < 2 ^ 32) :
    evalExpr (.ult (.var "j") (.var "m")) (mkNestedEnv nv mv k acc t) =
      .ok (.b (decide (t < mv.toNat))) := by
  have hj := mkNestedEnv_j nv mv k acc t
  have hm := mkNestedEnv_m nv mv k acc t
  simp [evalExpr, hj, hm, ofNat32_ult t mv h]

/-- Outer condition reads `i` against `n`. -/
theorem nestedCondOuter_eval (nv mv : BitVec 32) (k t : Nat)
    (acc : BitVec 32) (h : k < 2 ^ 32) :
    evalExpr (.ult (.var "i") (.var "n")) (mkNestedEnv nv mv k acc t) =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkNestedEnv_i nv mv k acc t
  have hn := mkNestedEnv_n nv mv k acc t
  simp [evalExpr, hi, hn, ofNat32_ult k nv h]

/-- One inner step advances `j` and accumulates `ofNat (k*t)` (any fuel:
    loop-free). -/
theorem nestedBodyInner_eval (F : Nat) (nv mv : BitVec 32)
    (k t : Nat) (acc : BitVec 32) :
    evalStmtFuel F nestedBodyInner (mkNestedEnv nv mv k acc t) =
      .ok (mkNestedEnv nv mv k
        (acc + BitVec.ofNat 32 (k * t)) (t + 1), .fellThrough) := by
  have hs : evalExpr (.uadd (.var "s") (.umul (.var "i") (.var "j")))
        (mkNestedEnv nv mv k acc t) =
        .ok (.u32 (acc + BitVec.ofNat 32 (k * t))) := by
    have h1 := mkNestedEnv_s nv mv k acc t
    have hii := mkNestedEnv_i nv mv k acc t
    have hj := mkNestedEnv_j nv mv k acc t
    simp only [evalExpr, h1, hii, hj, ofNat32_mul]
  have hj2 : evalExpr (.uadd (.var "j") (.lit (.u32 (BitVec.ofNat 32 1))))
        (mkNestedEnv nv mv k (acc + BitVec.ofNat 32 (k * t)) t) =
        .ok (.u32 (BitVec.ofNat 32 (t + 1))) := by
    have hj := mkNestedEnv_j nv mv k (acc + BitVec.ofNat 32 (k * t)) t
    simp only [evalExpr, litVal, hj, ofNat32_add_one]
  have up1 := nestedEnv_update_s nv mv k t acc
    (acc + BitVec.ofNat 32 (k * t))
  have up2 := nestedEnv_update_j nv mv k t (t + 1)
    (acc + BitVec.ofNat 32 (k * t))
  cases F <;>
    simp [nestedBodyInner, evalStmtFuel, evalStmtZero, evalStmtWith,
      hs, hj2, up1, up2]

/-- Inner loop correctness: folds the row suffix (fuel-generalized). -/
theorem nestedInner_correct (nv mv : BitVec 32)
    (F k t : Nat) (acc : BitVec 32)
    (ht32 : t ≤ mv.toNat) (ht2 : t < 2 ^ 32) (hm : mv.toNat < 2 ^ 32)
    (hF : mv.toNat - t ≤ F) :
    evalStmtFuel F nestedInner (mkNestedEnv nv mv k acc t) =
      .ok (mkNestedEnv nv mv k
        (acc + rowSuffixU32 k t mv.toNat) mv.toNat, .fellThrough) := by
  induction F generalizing t acc with
  | zero =>
    have htt : t = mv.toNat := by omega
    subst htt
    have hcond : evalExpr (.ult (.var "j") (.var "m"))
          (mkNestedEnv nv mv k acc mv.toNat) = .ok (.b false) := by
      simpa using
        (nestedCondInner_eval nv mv k mv.toNat acc (by omega : mv.toNat < 2 ^ 32))
    have hnil := rowSuffix_nil k mv.toNat
    simp [nestedInner, evalStmtFuel, evalStmtZero, evalStmtZeroHandler,
      evalStmtWith, hcond, hnil, BitVec.add_zero]
  | succ F ih =>
    by_cases hlt : t < mv.toNat
    · have hcond : evalExpr (.ult (.var "j") (.var "m"))
          (mkNestedEnv nv mv k acc t) = .ok (.b true) := by
        simpa [hlt] using (nestedCondInner_eval nv mv k t acc ht2)
      have hbody := nestedBodyInner_eval F nv mv k t acc
      have hstep : evalStmtFuel (F + 1) nestedInner
            (mkNestedEnv nv mv k acc t)
          = evalStmtFuel F nestedInner
            (mkNestedEnv nv mv k (acc + BitVec.ofNat 32 (k * t)) (t + 1)) := by
        simp [nestedInner, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond, hbody]
      rw [hstep]
      have hrec := ih (t + 1) (acc + BitVec.ofNat 32 (k * t))
        (by omega) (by omega) (by omega)
      rw [hrec]
      have hrow := rowSuffix_step k t mv.toNat hlt
      have hacc : (acc + BitVec.ofNat 32 (k * t)) +
            rowSuffixU32 k (t + 1) mv.toNat
          = acc + rowSuffixU32 k t mv.toNat := by
        rw [hrow]; exact BitVec.add_assoc _ _ _
      rw [hacc]
    · have htt : t = mv.toNat := by omega
      subst htt
      have hcond : evalExpr (.ult (.var "j") (.var "m"))
            (mkNestedEnv nv mv k acc mv.toNat) = .ok (.b false) := by
        simpa using
          (nestedCondInner_eval nv mv k mv.toNat acc (by omega : mv.toNat < 2 ^ 32))
      have hnil := rowSuffix_nil k mv.toNat
      simp [nestedInner, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
        hcond, hnil, BitVec.add_zero]

/-- Outer body evaluation: run the inner loop, step `i`, reset `j`.
    Needs `m ≤ F` so the inner loop has fuel (the three steps are
    handler-independent, so one inner fact covers all fuels via
    `cases`, ascribed to the unfolded handler form in the `succ`
    branch). -/
theorem nestedBodyOuter_eval (F : Nat) (nv mv : BitVec 32)
    (k : Nat) (acc : BitVec 32)
    (hmF : mv.toNat ≤ F)
    (hm32 : mv.toNat < 2 ^ 32) :
    evalStmtFuel F nestedBodyOuter (mkNestedEnv nv mv k acc 0) =
      .ok (mkNestedEnv nv mv (k + 1) (acc + rowU32 k mv.toNat) 0,
        .fellThrough) := by
  have hinner : evalStmtFuel F nestedInner (mkNestedEnv nv mv k acc 0) =
        .ok (mkNestedEnv nv mv k (acc + rowU32 k mv.toNat) mv.toNat,
          .fellThrough) := by
    have h := nestedInner_correct nv mv F k 0 acc
      (Nat.zero_le _) (by omega) hm32 (by omega)
    rwa [rowSuffix_full] at h
  have hincr : evalExpr (.uadd (.var "i") (.lit (.u32 (BitVec.ofNat 32 1))))
        (mkNestedEnv nv mv k (acc + rowU32 k mv.toNat) mv.toNat) =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have hii := mkNestedEnv_i nv mv k (acc + rowU32 k mv.toNat) mv.toNat
    simp only [evalExpr, litVal, hii, ofNat32_add_one]
  have up1 := nestedEnv_update_i nv mv k (k + 1) mv.toNat
    (acc + rowU32 k mv.toNat)
  have hreset : evalExpr (.lit (.u32 (BitVec.ofNat 32 0)))
        (mkNestedEnv nv mv (k + 1) (acc + rowU32 k mv.toNat) mv.toNat) =
        .ok (.u32 (BitVec.ofNat 32 0)) := rfl
  have up0 := nestedEnv_update_j nv mv (k + 1) mv.toNat 0
    (acc + rowU32 k mv.toNat)
  cases F with
  | zero =>
    have hinner0 : evalStmtWith evalStmtZeroHandler
          nestedInner (mkNestedEnv nv mv k acc 0) =
          .ok (mkNestedEnv nv mv k (acc + rowU32 k mv.toNat) mv.toNat,
            .fellThrough) := hinner
    simp [nestedBodyOuter, evalStmtFuel, evalStmtZero, evalStmtWith,
      hinner0, hincr, up1, hreset, up0]
  | succ F =>
    have hinnerS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          nestedInner (mkNestedEnv nv mv k acc 0) =
          .ok (mkNestedEnv nv mv k (acc + rowU32 k mv.toNat) mv.toNat,
            .fellThrough) := hinner
    simp [nestedBodyOuter, evalStmtFuel, evalStmtWith,
      hinnerS, hincr, up1, hreset, up0]

/-- Outer loop correctness: folds the nest suffix (fuel-generalized;
    one outer iteration costs `m+1` fuel units). -/
theorem nestedOuter_correct (nv mv : BitVec 32)
    (F k : Nat) (acc : BitVec 32)
    (hk : k ≤ nv.toNat) (hn : nv.toNat < 2 ^ 32) (hm : mv.toNat < 2 ^ 32)
    (hF : (nv.toNat - k) * (mv.toNat + 1) ≤ F) :
    evalStmtFuel F nestedOuter (mkNestedEnv nv mv k acc 0) =
      .ok (mkNestedEnv nv mv nv.toNat
        (acc + nestSuffixU32 k nv.toNat mv.toNat) 0, .fellThrough) := by
  induction F generalizing k acc with
  | zero =>
    have hkk : k = nv.toNat := by
      have hpos : 0 < nv.toNat - k ∨ k = nv.toNat := by omega
      rcases hpos with hpos | hkk
      · have hge := Nat.le_mul_of_pos_left (mv.toNat + 1) hpos
        omega
      · exact hkk
    subst hkk
    have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkNestedEnv nv mv nv.toNat acc 0) = .ok (.b false) := by
      simpa using (nestedCondOuter_eval nv mv nv.toNat 0 acc hn)
    have hnil := nestSuffix_nil nv.toNat nv.toNat mv.toNat (Nat.le_refl _)
    simp [nestedOuter, evalStmtFuel, evalStmtZero, evalStmtZeroHandler,
      evalStmtWith, hcond, hnil, BitVec.add_zero]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
            (mkNestedEnv nv mv k acc 0) = .ok (.b true) := by
        simpa [hlt] using (nestedCondOuter_eval nv mv k 0 acc hk32)
      have hbody := nestedBodyOuter_eval F nv mv k acc
        (by have hge := Nat.le_mul_of_pos_left (mv.toNat + 1)
              (show 0 < nv.toNat - k by omega)
            omega)
        hm
      have hstep : evalStmtFuel (F + 1) nestedOuter
            (mkNestedEnv nv mv k acc 0)
          = evalStmtFuel F nestedOuter
            (mkNestedEnv nv mv (k + 1) (acc + rowU32 k mv.toNat) 0) := by
        simp [nestedOuter, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond, hbody]
      rw [hstep]
      have hsplit : (nv.toNat - k) * (mv.toNat + 1)
          = (nv.toNat - (k + 1)) * (mv.toNat + 1) + (mv.toNat + 1) := by
        have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
        rw [hkk1, Nat.add_mul, Nat.one_mul]
      have hrec := ih (k + 1) (acc + rowU32 k mv.toNat)
        (by omega)
        (show (nv.toNat - (k + 1)) * (mv.toNat + 1) ≤ F by omega)
      rw [hrec]
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      have hnest := nestSuffix_step k nv.toNat mv.toNat hlt
      have hacc : (acc + rowU32 k mv.toNat) +
            nestSuffixU32 (k + 1) nv.toNat mv.toNat
          = acc + nestSuffixU32 k nv.toNat mv.toNat := by
        rw [hnest]; exact BitVec.add_assoc _ _ _
      rw [hacc]
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
            (mkNestedEnv nv mv nv.toNat acc 0) = .ok (.b false) := by
        simpa using (nestedCondOuter_eval nv mv nv.toNat 0 acc hn)
      have hnil := nestSuffix_nil nv.toNat nv.toNat mv.toNat (Nat.le_refl _)
      simp [nestedOuter, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
        hcond, hnil, BitVec.add_zero]

/-- `emit_correct` for `nested_sum`, fuel-generalized. -/
theorem evalFuncFuel_nested (F : Nat) (nv mv : BitVec 32)
    (hn : nv.toNat < 2 ^ 32) (hm : mv.toNat < 2 ^ 32)
    (hF : nv.toNat * (mv.toNat + 1) ≤ F) :
    evalFuncFuel F nestedFunc [.u32 nv, .u32 mv] = nestedFwd nv mv := by
  have hbind : bindArgs nestedFunc.args [.u32 nv, .u32 mv] =
      some [("n", .u32 nv), ("m", .u32 mv)] := rfl
  have hbody : nestedFunc.body =
      .seq (.let_ "s" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
      (.seq (.let_ "i" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
      (.seq (.let_ "j" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
      (.seq nestedOuter
            (.return_ (.var "s"))))) := rfl
  -- Stated with `ofNat`-headed zeros (simp's simprocs normalize `0` to
  -- `0#32`, so `OfNat`-headed forms would not match after normalization).
  have henv : [("j", .u32 (BitVec.ofNat 32 0)),
        ("i", .u32 (BitVec.ofNat 32 0)),
        ("s", .u32 (BitVec.ofNat 32 0)),
        ("n", .u32 nv), ("m", .u32 mv)]
      = mkNestedEnv nv mv 0 (BitVec.ofNat 32 0) 0 := rfl
  have hfull := nestSuffix_full nv.toNat mv.toNat
  have hsret : envLookup
        (mkNestedEnv nv mv nv.toNat (nestedSumU32 nv.toNat mv.toNat) 0)
        "s" = some (.u32 (nestedSumU32 nv.toNat mv.toNat)) :=
    mkNestedEnv_s nv mv nv.toNat (nestedSumU32 nv.toNat mv.toNat) 0
  cases F with
  | zero =>
    have hloopH0 : evalStmtWith evalStmtZeroHandler
          nestedOuter (mkNestedEnv nv mv 0 (BitVec.ofNat 32 0) 0)
        = .ok (mkNestedEnv nv mv nv.toNat
            (BitVec.ofNat 32 0 + nestSuffixU32 0 nv.toNat mv.toNat) 0,
            .fellThrough) :=
      nestedOuter_correct nv mv 0 0 (BitVec.ofNat 32 0) (Nat.zero_le _)
        hn hm (by omega)
    simp [evalFuncFuel, nestedFunc, bindArgs, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, litVal, envExtend, nestedFwd, henv, hloopH0,
      hsret, hfull, BitVec.zero_add]
  | succ F =>
    have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          nestedOuter (mkNestedEnv nv mv 0 (BitVec.ofNat 32 0) 0)
        = .ok (mkNestedEnv nv mv nv.toNat
            (BitVec.ofNat 32 0 + nestSuffixU32 0 nv.toNat mv.toNat) 0,
            .fellThrough) :=
      nestedOuter_correct nv mv (F + 1) 0 (BitVec.ofNat 32 0)
        (Nat.zero_le _) hn hm (by omega)
    simp [evalFuncFuel, nestedFunc, bindArgs, evalStmtFuel, evalStmtWith,
      evalExpr, litVal, envExtend, nestedFwd, henv, hloopS, hsret, hfull,
      BitVec.zero_add]

/-- `emit_correct` for `nested_sum` at the default fuel. -/
theorem emit_correct_nested (nv mv : BitVec 32)
    (hn : nv.toNat < 2 ^ 32) (hm : mv.toNat < 2 ^ 32)
    (hfuel : nv.toNat * (mv.toNat + 1) ≤ EVAL_FUEL) :
    evalFunc nestedFunc [.u32 nv, .u32 mv] = nestedFwd nv mv :=
  evalFuncFuel_nested EVAL_FUEL nv mv hn hm hfuel


/-! ### `skip_sum`: break/continue in a bounded `u32` loop -/

/-- Suffix sum: `Σ` of `i ∈ [t,e)`, skipping `2` (loop invariant;
    `e` is always `min n 8`: `break` at `8` caps the range,
    `continue` filters `2`). -/
def skipSuffixU32 (t e : Nat) : BitVec 32 :=
  ((((List.range' t (e - t)).filter (fun i => i != 2)).map
    (fun i => BitVec.ofNat 32 i))).sum

/-- Step: peeling `t < e`, `t ≠ 2` exposes the head summand. -/
theorem skipSuffix_step (t e : Nat) (hlt : t < e) (hne : t ≠ 2) :
    skipSuffixU32 t e =
      BitVec.ofNat 32 t + skipSuffixU32 (t + 1) e := by
  have hsub : e - t = (e - (t + 1)) + 1 := by omega
  have hkeep : (t != 2) = true := by simp [hne]
  simp [skipSuffixU32, hsub, List.range'_succ, hkeep,
    BitVec.add_comm (BitVec.ofNat 32 t) _]

/-- `continue` at `2` drops it: suffixes from `2` and `3` agree. -/
theorem skipSuffix_skip2 (e : Nat) (h : 2 < e) :
    skipSuffixU32 2 e = skipSuffixU32 3 e := by
  have hsub : e - 2 = (e - 3) + 1 := by omega
  have hdrop : ((2 != 2)) = false := by simp
  simp [skipSuffixU32, hsub, List.range'_succ]

/-- Empty suffix sums to zero. -/
theorem skipSuffix_nil (t e : Nat) (h : e ≤ t) :
    skipSuffixU32 t e = 0 := by
  have hsub : e - t = 0 := by omega
  simp [skipSuffixU32, hsub]

/-- Full suffix is the rendered forward reference. -/
theorem skipSuffix_full (n : Nat) :
    skipSuffixU32 0 (min n 8) = skipSumU32 n := by
  simp [skipSuffixU32, skipSumU32, List.range_eq_range']

/-- `continue` branch: `i = i+1` then signal (mirrors the `cir.for`
    step region, which runs on `continue`). -/
def skipContBranch : CStmt :=
  .seq (.assign "i" (.uadd (.var "i") (.lit (.u32 (BitVec.ofNat 32 1)))))
    .continue_

/-- Fall-through tail: `s = s+i; i = i+1`. -/
def skipTail : CStmt :=
  .seq (.assign "s" (.uadd (.var "s") (.var "i")))
    (.assign "i" (.uadd (.var "i") (.lit (.u32 (BitVec.ofNat 32 1)))))

/-- Loop body: skip `2`, break at `8`, else accumulate. -/
def skipBody : CStmt :=
  .seq (.if_ (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 2))))
        skipContBranch .skip)
    (.seq (.if_ (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 8))))
            .break_ .skip)
          skipTail)

/-- Loop: `while (i < n) { ... }`. -/
def skipWhile : CStmt :=
  .while_ (.ult (.var "i") (.var "n")) skipBody

/-- Canonical CoreIR for `tests/c/skip_sum.c`. `break` caps iterations
    at `9`, so the default-fuel correctness is unconditional (the
    fuel side condition discharges by `omega` over `min n 8`). -/
def skipFunc : Func :=
  ⟨"skip_sum",
   [{ name := "n", ty := .u 32, role := .owned }],
   .u 32,
   .seq (.let_ "s" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
   (.seq (.let_ "i" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
   (.seq skipWhile
         (.return_ (.var "s"))))⟩

/-- Value-level forward for `skip_sum` (cf. rendered `skip_sum_fwd`,
    which references `Base.skipSumU32`). -/
def skipFwd (n : BitVec 32) : Result Value :=
  .ok (.u32 (skipSumU32 n.toNat))

/-- Loop environments: index `k` and accumulator, bound fixed. -/
def mkSkipEnv (nv : BitVec 32) (k : Nat) (acc : BitVec 32) : Env :=
  [("i", .u32 (BitVec.ofNat 32 k)), ("s", .u32 acc), ("n", .u32 nv)]

theorem mkSkipEnv_i (nv : BitVec 32) (k : Nat) (acc : BitVec 32) :
    envLookup (mkSkipEnv nv k acc) "i" =
      some (.u32 (BitVec.ofNat 32 k)) := by
  simp [mkSkipEnv, envLookup]

theorem mkSkipEnv_s (nv : BitVec 32) (k : Nat) (acc : BitVec 32) :
    envLookup (mkSkipEnv nv k acc) "s" = some (.u32 acc) := by
  simp [mkSkipEnv, envLookup, show ("s" : String) ≠ "i" by decide]

theorem mkSkipEnv_n (nv : BitVec 32) (k : Nat) (acc : BitVec 32) :
    envLookup (mkSkipEnv nv k acc) "n" = some (.u32 nv) := by
  simp [mkSkipEnv, envLookup, show ("n" : String) ≠ "i" by decide,
    show ("n" : String) ≠ "s" by decide]

/-- Updating `s` stays in the env family. -/
theorem skipEnv_update_s (nv : BitVec 32) (k : Nat) (acc v : BitVec 32) :
    envUpdate (mkSkipEnv nv k acc) "s" (.u32 v) =
      some (mkSkipEnv nv k v) := by
  simp [mkSkipEnv, envUpdate, show ("s" : String) ≠ "i" by decide]

/-- Updating `i` stays in the env family. -/
theorem skipEnv_update_i (nv : BitVec 32) (k k' : Nat) (acc : BitVec 32) :
    envUpdate (mkSkipEnv nv k acc) "i" (.u32 (BitVec.ofNat 32 k')) =
      some (mkSkipEnv nv k' acc) := by
  simp [mkSkipEnv, envUpdate]

/-- The loop condition reads the index against the bound. -/
theorem skipCond_eval (nv : BitVec 32) (k : Nat) (acc : BitVec 32)
    (h : k < 2 ^ 32) :
    evalExpr (.ult (.var "i") (.var "n")) (mkSkipEnv nv k acc) =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkSkipEnv_i nv k acc
  have hn := mkSkipEnv_n nv k acc
  simp [evalExpr, hi, hn, ofNat32_ult k nv h]

/-- `ueq` against a const decides `Nat` equality (index below `2^32`). -/
theorem skipCond_eq (nv : BitVec 32) (k c : Nat) (acc : BitVec 32)
    (hk : k < 2 ^ 32) (hc : c < 2 ^ 32) :
    evalExpr (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 c))))
      (mkSkipEnv nv k acc) = .ok (.b (decide (k = c))) := by
  have hi := mkSkipEnv_i nv k acc
  simp [evalExpr, hi, litVal, ofNat32_beq k c hk hc]

/-- Body at `k = 2`: increment, signal `continued` (any fuel). -/
theorem skipBody_continue (F : Nat) (nv : BitVec 32) (acc : BitVec 32) :
    evalStmtFuel F skipBody (mkSkipEnv nv 2 acc) =
      .ok (mkSkipEnv nv 3 acc, .continued) := by
  have hcond1 : evalExpr (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 2))))
        (mkSkipEnv nv 2 acc) = .ok (.b true) := by
    simpa using (skipCond_eq nv 2 2 acc (by decide) (by decide))
  have hincr : evalExpr (.uadd (.var "i") (.lit (.u32 (BitVec.ofNat 32 1))))
        (mkSkipEnv nv 2 acc) = .ok (.u32 (BitVec.ofNat 32 3)) := by
    have hi := mkSkipEnv_i nv 2 acc
    have h3 : BitVec.ofNat 32 2 + BitVec.ofNat 32 1
        = BitVec.ofNat 32 3 :=
      ofNat32_add_one 2
    simp only [evalExpr, litVal, hi, h3]
  have upi := skipEnv_update_i nv 2 3 acc
  cases F <;>
    simp [skipBody, skipContBranch, evalStmtFuel, evalStmtZero, evalStmtWith,
      hcond1, hincr, upi]

/-- Body at `k = 8`: signal `broke`, env untouched (any fuel). -/
theorem skipBody_break (F : Nat) (nv : BitVec 32) (acc : BitVec 32) :
    evalStmtFuel F skipBody (mkSkipEnv nv 8 acc) =
      .ok (mkSkipEnv nv 8 acc, .broke) := by
  have hcond1 : evalExpr (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 2))))
        (mkSkipEnv nv 8 acc) = .ok (.b false) := by
    have h := skipCond_eq nv 8 2 acc (by decide) (by decide)
    simpa using h
  have hcond2 : evalExpr (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 8))))
        (mkSkipEnv nv 8 acc) = .ok (.b true) := by
    simpa using (skipCond_eq nv 8 8 acc (by decide) (by decide))
  cases F <;>
    simp [skipBody, evalStmtFuel, evalStmtZero, evalStmtWith, hcond1, hcond2]

/-- Body elsewhere: accumulate and step (any fuel). -/
theorem skipBody_step (F : Nat) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32)
    (hne2 : k ≠ 2) (hne8 : k ≠ 8) (hk32 : k < 2 ^ 32) :
    evalStmtFuel F skipBody (mkSkipEnv nv k acc) =
      .ok (mkSkipEnv nv (k + 1) (acc + BitVec.ofNat 32 k),
        .fellThrough) := by
  have hcond1 : evalExpr (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 2))))
        (mkSkipEnv nv k acc) = .ok (.b false) := by
    have h := skipCond_eq nv k 2 acc hk32 (by decide)
    simpa [hne2] using h
  have hcond2 : evalExpr (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 8))))
        (mkSkipEnv nv k acc) = .ok (.b false) := by
    have h := skipCond_eq nv k 8 acc hk32 (by decide)
    simpa [hne8] using h
  have hs : evalExpr (.uadd (.var "s") (.var "i"))
        (mkSkipEnv nv k acc) = .ok (.u32 (acc + BitVec.ofNat 32 k)) := by
    have h1 := mkSkipEnv_s nv k acc
    have hii := mkSkipEnv_i nv k acc
    simp only [evalExpr, h1, hii]
  have hi2 : evalExpr (.uadd (.var "i") (.lit (.u32 (BitVec.ofNat 32 1))))
        (mkSkipEnv nv k (acc + BitVec.ofNat 32 k)) =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkSkipEnv_i nv k (acc + BitVec.ofNat 32 k)
    simp only [evalExpr, litVal, h1, ofNat32_add_one]
  have up1 := skipEnv_update_s nv k acc (acc + BitVec.ofNat 32 k)
  have up2 := skipEnv_update_i nv k (k + 1) (acc + BitVec.ofNat 32 k)
  cases F <;>
    simp [skipBody, skipTail, evalStmtFuel, evalStmtZero, evalStmtWith,
      hcond1, hcond2, hs, hi2, up1, up2]

/-- Loop correctness: folds the skip suffix, exits with `i = min n 8`
    (fuel-generalized; the `+1` absorbs the final exit iteration, so
    the zero-fuel case is vacuous). -/
theorem skipWhile_correct (nv : BitVec 32)
    (F k : Nat) (acc : BitVec 32)
    (hk : k ≤ min nv.toNat 8)
    (hF : min nv.toNat 8 - k + 1 ≤ F) :
    evalStmtFuel F skipWhile (mkSkipEnv nv k acc) =
      .ok (mkSkipEnv nv (min nv.toNat 8)
        (acc + skipSuffixU32 k (min nv.toNat 8)), .fellThrough) := by
  induction F generalizing k acc with
  | zero => omega
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · by_cases h2 : k = 2
      · subst h2
        have hcond : evalExpr (.ult (.var "i") (.var "n"))
              (mkSkipEnv nv 2 acc) = .ok (.b true) := by
          have hk32 : (2 : Nat) < 2 ^ 32 := by decide
          simpa [hlt] using (skipCond_eval nv 2 acc hk32)
        have hbody := skipBody_continue F nv acc
        have hstep : evalStmtFuel (F + 1) skipWhile (mkSkipEnv nv 2 acc)
            = evalStmtFuel F skipWhile (mkSkipEnv nv 3 acc) := by
          simp [skipWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
            hcond, hbody]
        rw [hstep]
        have hrec := ih 3 acc (by omega) (by omega)
        rw [hrec]
        have hskip := skipSuffix_skip2 (min nv.toNat 8) (by omega)
        have hacc : acc + skipSuffixU32 3 (min nv.toNat 8)
            = acc + skipSuffixU32 2 (min nv.toNat 8) := by
          rw [hskip]
        rw [hacc]
      · by_cases h8 : k = 8
        · subst h8
          have he : min nv.toNat 8 = 8 := by omega
          have hcond : evalExpr (.ult (.var "i") (.var "n"))
                (mkSkipEnv nv 8 acc) = .ok (.b true) := by
            have hk32 : (8 : Nat) < 2 ^ 32 := by decide
            simpa [hlt] using (skipCond_eval nv 8 acc hk32)
          have hbody := skipBody_break F nv acc
          have hnil8 := skipSuffix_nil 8 8 (Nat.le_refl 8)
          simp [skipWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
            hcond, hbody, he, hnil8, BitVec.add_zero]
        · have hk32 : k < 2 ^ 32 := by omega
          have hcond : evalExpr (.ult (.var "i") (.var "n"))
                (mkSkipEnv nv k acc) = .ok (.b true) := by
            simpa [hlt] using (skipCond_eval nv k acc hk32)
          have hbody := skipBody_step F nv k acc h2 h8 hk32
          have hstep : evalStmtFuel (F + 1) skipWhile (mkSkipEnv nv k acc)
              = evalStmtFuel F skipWhile
                (mkSkipEnv nv (k + 1) (acc + BitVec.ofNat 32 k)) := by
            simp [skipWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
              hcond, hbody]
          rw [hstep]
          have hrec := ih (k + 1) (acc + BitVec.ofNat 32 k)
            (by omega) (by omega)
          rw [hrec]
          have hlt' : k < min nv.toNat 8 := by omega
          have hstep' := skipSuffix_step k (min nv.toNat 8) hlt' h2
          have hacc : (acc + BitVec.ofNat 32 k) +
                skipSuffixU32 (k + 1) (min nv.toNat 8)
              = acc + skipSuffixU32 k (min nv.toNat 8) := by
            rw [hstep']; exact BitVec.add_assoc _ _ _
          rw [hacc]
    · have hkk : k = min nv.toNat 8 := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
            (mkSkipEnv nv (min nv.toNat 8) acc) = .ok (.b false) := by
        have hfalse : (decide (min nv.toNat 8 < nv.toNat)) = false := by
          have : ¬ min nv.toNat 8 < nv.toNat := by omega
          simp [this]
        have hk32 : min nv.toNat 8 < 2 ^ 32 := by omega
        have h := skipCond_eval nv (min nv.toNat 8) acc hk32
        rwa [hfalse] at h
      have hnil := skipSuffix_nil (min nv.toNat 8) (min nv.toNat 8)
        (Nat.le_refl _)
      simp [skipWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
        hcond, hnil, BitVec.add_zero]

/-- `emit_correct` for `skip_sum`, fuel-generalized. -/
theorem evalFuncFuel_skip (F : Nat) (nv : BitVec 32)
    (hF : min nv.toNat 8 + 1 ≤ F) :
    evalFuncFuel F skipFunc [.u32 nv] = skipFwd nv := by
  have hbind : bindArgs skipFunc.args [.u32 nv] =
      some [("n", .u32 nv)] := rfl
  have hbody : skipFunc.body =
      .seq (.let_ "s" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
      (.seq (.let_ "i" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
      (.seq skipWhile
            (.return_ (.var "s")))) := rfl
  have henv : [("i", .u32 (BitVec.ofNat 32 0)),
        ("s", .u32 (BitVec.ofNat 32 0)),
        ("n", .u32 nv)]
      = mkSkipEnv nv 0 (BitVec.ofNat 32 0) := rfl
  have hfull := skipSuffix_full nv.toNat
  have hsret : envLookup
        (mkSkipEnv nv (min nv.toNat 8) (skipSumU32 nv.toNat)) "s" =
        some (.u32 (skipSumU32 nv.toNat)) :=
    mkSkipEnv_s nv (min nv.toNat 8) (skipSumU32 nv.toNat)
  cases F with
  | zero =>
    have hloopH0 : evalStmtWith evalStmtZeroHandler
          skipWhile (mkSkipEnv nv 0 (BitVec.ofNat 32 0))
        = .ok (mkSkipEnv nv (min nv.toNat 8)
            (BitVec.ofNat 32 0 + skipSuffixU32 0 (min nv.toNat 8)),
            .fellThrough) :=
      skipWhile_correct nv 0 0 (BitVec.ofNat 32 0) (Nat.zero_le _) (by omega)
    simp [evalFuncFuel, skipFunc, bindArgs, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, litVal, envExtend, skipFwd, henv, hloopH0,
      hsret, hfull, BitVec.zero_add]
  | succ F =>
    have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          skipWhile (mkSkipEnv nv 0 (BitVec.ofNat 32 0))
        = .ok (mkSkipEnv nv (min nv.toNat 8)
            (BitVec.ofNat 32 0 + skipSuffixU32 0 (min nv.toNat 8)),
            .fellThrough) :=
      skipWhile_correct nv (F + 1) 0 (BitVec.ofNat 32 0) (Nat.zero_le _)
        (by omega)
    simp [evalFuncFuel, skipFunc, bindArgs, evalStmtFuel, evalStmtWith,
      evalExpr, litVal, envExtend, skipFwd, henv, hloopS, hsret, hfull,
      BitVec.zero_add]

/-- `emit_correct` for `skip_sum` at the default fuel — unconditional:
    `break` caps iterations at `9 ≤ EVAL_FUEL`. -/
theorem emit_correct_skip (nv : BitVec 32) :
    evalFunc skipFunc [.u32 nv] = skipFwd nv := by
  apply evalFuncFuel_skip
  have h8 := Nat.min_le_right nv.toNat 8
  simp only [EVAL_FUEL] at h8 ⊢
  omega



/-! ### `find_eq`: early return inside a bounded loop -/

/-- `ofNat` round-trips `toNat` (for narrowing the found index back). -/
theorem ofNat32_toNat_inv (v : BitVec 32) :
    BitVec.ofNat 32 v.toNat = v := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt v.isLt

/-- First match of `k` in `l[j]?` over `j ∈ [t,e)` (loop invariant;
    `decide` predicate keeps `find?` simp-friendly). -/
def findSuffixU32 (l : List (BitVec 32)) (t e : Nat)
    (k : BitVec 32) : Option Nat :=
  ((List.range' t (e - t)).find? (fun j => decide (l[j]? = some k)))

/-- Hit at the head: the suffix finds `t` itself. -/
theorem findSuffix_hit (l : List (BitVec 32)) (t e : Nat)
    (k : BitVec 32) (x : BitVec 32)
    (hget : l[t]? = some x) (heq : x = k) (hlt : t < e) :
    findSuffixU32 l t e k = some t := by
  have hsub : e - t = (e - (t + 1)) + 1 := by omega
  have hpt : (fun j => decide (l[j]? = some k)) t = true := by
    simp [hget, heq]
  simp [findSuffixU32, hsub, List.range'_succ, hpt]

/-- Miss at the head: the suffix agrees with the tail. -/
theorem findSuffix_miss (l : List (BitVec 32)) (t e : Nat)
    (k : BitVec 32)
    (hmiss : ∀ x, l[t]? = some x → x ≠ k) (hlt : t < e) :
    findSuffixU32 l t e k = findSuffixU32 l (t + 1) e k := by
  have hsub : e - t = (e - (t + 1)) + 1 := by omega
  have hpt : (fun j => decide (l[j]? = some k)) t = false := by
    match ht : l[t]? with
    | some x =>
      have hne := hmiss x ht
      simp [ht, hne]
    | none => simp [ht]
  simp [findSuffixU32, hsub, List.range'_succ, hpt]

/-- Empty suffix finds nothing. -/
theorem findSuffix_nil (l : List (BitVec 32)) (t : Nat) (k : BitVec 32) :
    findSuffixU32 l t t k = none := by
  have hsub : t - t = 0 := Nat.sub_self _
  simp [findSuffixU32, hsub]

/-- Suffix from zero is the whole-prefix find (bridge to `findEqOut`). -/
theorem findSuffix_zero_idx (l : List (BitVec 32)) (n : Nat)
    (k : BitVec 32) :
    findSuffixU32 l 0 (min n l.length) k = findIdxU32 l n k := by
  simp [findSuffixU32, findIdxU32, Nat.sub_zero, List.range_eq_range']

/-- Loop body: return the index on match, else step. -/
def findBody : CStmt :=
  .seq (.if_ (.ueq (.idx "a" (.var "i")) (.var "k"))
        (.return_ (.var "i")) .skip)
       (.assign "i" (.uadd (.var "i") (.lit (.u32 (BitVec.ofNat 32 1)))))

/-- Loop: `while (i < n) { ... }`. -/
def findWhile : CStmt :=
  .while_ (.ult (.var "i") (.var "n")) findBody

/-- Canonical CoreIR for `tests/c/find_eq.c`. `a` is a `sharedBorrow`
    (pure list value); `n` is the 32-bit length (C `size_t` lengths must
    fit 32 bits — `validate` narrows them, runtime excess is `OOB`,
    exactly as in `sum`). -/
def findEqFunc : Func :=
  ⟨"find_eq",
   [{ name := "a", ty := .array (.u 32) 4096, role := .sharedBorrow },
    { name := "n", ty := .u 32, role := .owned },
    { name := "k", ty := .u 32, role := .owned }],
   .u 32,
   .seq (.let_ "i" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
   (.seq findWhile
         (.return_ (.var "n")))⟩

/-- Value-level forward for `find_eq` (cf. rendered `find_eq_fwd`,
    which references `Base.findEqOut`). Stated by matching (not
    `Functor.map`) so `simp` closes goal sides syntactically. -/
def findEqFwd (l : List (BitVec 32)) (n k : BitVec 32) : Result Value :=
  match findEqOut l n.toNat k with
  | .ok w => .ok (.u32 w)
  | .error e => .error e

/-- Loop environments: index `t`, array and bound/needle fixed. -/
def mkFindEnv (l : List (BitVec 32)) (nv kv : BitVec 32)
    (t : Nat) : Env :=
  [("i", .u32 (BitVec.ofNat 32 t)), ("a", .arr32 l),
   ("n", .u32 nv), ("k", .u32 kv)]

theorem mkFindEnv_i (l : List (BitVec 32)) (nv kv : BitVec 32)
    (t : Nat) :
    envLookup (mkFindEnv l nv kv t) "i" =
      some (.u32 (BitVec.ofNat 32 t)) := by
  simp [mkFindEnv, envLookup]

theorem mkFindEnv_a (l : List (BitVec 32)) (nv kv : BitVec 32)
    (t : Nat) :
    envLookup (mkFindEnv l nv kv t) "a" = some (.arr32 l) := by
  simp [mkFindEnv, envLookup, show ("a" : String) ≠ "i" by decide]

theorem mkFindEnv_n (l : List (BitVec 32)) (nv kv : BitVec 32)
    (t : Nat) :
    envLookup (mkFindEnv l nv kv t) "n" = some (.u32 nv) := by
  simp [mkFindEnv, envLookup, show ("n" : String) ≠ "i" by decide,
    show ("n" : String) ≠ "a" by decide]

theorem mkFindEnv_k (l : List (BitVec 32)) (nv kv : BitVec 32)
    (t : Nat) :
    envLookup (mkFindEnv l nv kv t) "k" = some (.u32 kv) := by
  simp [mkFindEnv, envLookup, show ("k" : String) ≠ "i" by decide,
    show ("k" : String) ≠ "a" by decide,
    show ("k" : String) ≠ "n" by decide]

/-- Updating `i` stays in the env family. -/
theorem findEnv_update_i (l : List (BitVec 32)) (nv kv : BitVec 32)
    (t t' : Nat) :
    envUpdate (mkFindEnv l nv kv t) "i"
        (.u32 (BitVec.ofNat 32 t')) =
      some (mkFindEnv l nv kv t') := by
  simp [mkFindEnv, envUpdate]

/-- The loop condition reads the index against the bound. -/
theorem findCond_eval (l : List (BitVec 32)) (nv kv : BitVec 32)
    (t : Nat) (h : t < 2 ^ 32) :
    evalExpr (.ult (.var "i") (.var "n")) (mkFindEnv l nv kv t) =
      .ok (.b (decide (t < nv.toNat))) := by
  have hi := mkFindEnv_i l nv kv t
  have hn := mkFindEnv_n l nv kv t
  simp [evalExpr, hi, hn, ofNat32_ult t nv h]

/-- Body on match: return the index (any fuel). -/
theorem findBody_hit (F : Nat) (l : List (BitVec 32)) (nv kv : BitVec 32)
    (t : Nat) (x : BitVec 32)
    (hget : l[t]? = some x) (heq : x = kv) (ht32 : t < 2 ^ 32) :
    evalStmtFuel F findBody (mkFindEnv l nv kv t) =
      .ok (mkFindEnv l nv kv t,
        .returned (.u32 (BitVec.ofNat 32 t))) := by
  have hkk : (BitVec.ofNat 32 t).toNat = t := ofNat32_toNat t ht32
  have ha := mkFindEnv_a l nv kv t
  have hii := mkFindEnv_i l nv kv t
  have hidx : evalExpr (.idx "a" (.var "i")) (mkFindEnv l nv kv t) =
        .ok (.u32 x) := by
    simp only [evalExpr, ha, hii, hkk, hget]
  have hk := mkFindEnv_k l nv kv t
  have hcond : evalExpr (.ueq (.idx "a" (.var "i")) (.var "k"))
        (mkFindEnv l nv kv t) = .ok (.b true) := by
    simp [evalExpr, ha, hii, hkk, hget, hk, heq]
  have hret : evalExpr (.var "i") (mkFindEnv l nv kv t) =
        .ok (.u32 (BitVec.ofNat 32 t)) :=
    evalExpr_var_hit _ _ _ (mkFindEnv_i l nv kv t)
  cases F <;>
    simp [findBody, evalStmtFuel, evalStmtZero, evalStmtWith, hcond, hret]

/-- Body on miss: step the index (any fuel). -/
theorem findBody_miss (F : Nat) (l : List (BitVec 32)) (nv kv : BitVec 32)
    (t : Nat)
    (hmiss : ∀ x, l[t]? = some x → x ≠ kv)
    (htlen : t < l.length) (ht32 : t < 2 ^ 32) :
    evalStmtFuel F findBody (mkFindEnv l nv kv t) =
      .ok (mkFindEnv l nv kv (t + 1), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 t).toNat = t := ofNat32_toNat t ht32
  have hget : l[t]? = some l[t] := List.getElem?_eq_getElem htlen
  have hne : l[t] ≠ kv := hmiss _ hget
  have ha := mkFindEnv_a l nv kv t
  have hii := mkFindEnv_i l nv kv t
  have hidx : evalExpr (.idx "a" (.var "i")) (mkFindEnv l nv kv t) =
        .ok (.u32 l[t]) := by
    simp only [evalExpr, ha, hii, hkk, hget]
  have hk := mkFindEnv_k l nv kv t
  have hcond : evalExpr (.ueq (.idx "a" (.var "i")) (.var "k"))
        (mkFindEnv l nv kv t) = .ok (.b false) := by
    simp only [evalExpr, ha, hii, hkk, hget, hk]
    simp [hne]
  have hi2 : evalExpr (.uadd (.var "i") (.lit (.u32 (BitVec.ofNat 32 1))))
        (mkFindEnv l nv kv t) =
        .ok (.u32 (BitVec.ofNat 32 (t + 1))) := by
    have hii := mkFindEnv_i l nv kv t
    simp only [evalExpr, litVal, hii, ofNat32_add_one]
  have up := findEnv_update_i l nv kv t (t + 1)
  cases F <;>
    simp [findBody, evalStmtFuel, evalStmtZero, evalStmtWith, hcond, hi2, up]

/-- Body past the end: the index read fails `OOB` (any fuel). -/
theorem findBody_oob (F : Nat) (l : List (BitVec 32)) (nv kv : BitVec 32)
    (hlen32 : l.length < 2 ^ 32) :
    evalStmtFuel F findBody (mkFindEnv l nv kv l.length) =
      .error .OOB := by
  have hkk : (BitVec.ofNat 32 l.length).toNat = l.length :=
    ofNat32_toNat _ hlen32
  have hget : l[l.length]? = none :=
    List.getElem?_eq_none (Nat.le_refl _)
  have ha := mkFindEnv_a l nv kv l.length
  have hii := mkFindEnv_i l nv kv l.length
  have herr : evalExpr (.ueq (.idx "a" (.var "i")) (.var "k"))
        (mkFindEnv l nv kv l.length) = .error .OOB := by
    simp only [evalExpr, ha, hii, hkk, hget]
  cases F <;>
    simp [findBody, evalStmtFuel, evalStmtZero, evalStmtWith, herr]

/-- Loop correctness, hit: when the suffix finds `j`, the loop returns
    it (fuel-generalized; the `+1` absorbs the final exit iteration, so
    the zero-fuel case is vacuous). -/
theorem findWhile_some (l : List (BitVec 32)) (nv kv : BitVec 32)
    (F t j : Nat)
    (htm : t ≤ min nv.toNat l.length)
    (h32n : nv.toNat < 2 ^ 32)
    (hF : min nv.toNat l.length - t + 1 ≤ F)
    (hfind : findSuffixU32 l t (min nv.toNat l.length) kv = some j) :
    evalStmtFuel F findWhile (mkFindEnv l nv kv t) =
      .ok (mkFindEnv l nv kv j,
        .returned (.u32 (BitVec.ofNat 32 j))) := by
  induction F generalizing t j with
  | zero => omega
  | succ F ih =>
    by_cases hlt : t < min nv.toNat l.length
    · have htn : t < nv.toNat := by omega
      have htl : t < l.length := by omega
      have ht32 : t < 2 ^ 32 := by omega
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
            (mkFindEnv l nv kv t) = .ok (.b true) := by
        simpa [htn] using (findCond_eval l nv kv t ht32)
      match hget : l[t]? with
      | some x =>
        by_cases heq : x = kv
        · have hbody := findBody_hit F l nv kv t x hget heq ht32
          have hfound := findSuffix_hit l t (min nv.toNat l.length) kv x
            hget heq hlt
          have hjt : t = j := by
            rw [hfound] at hfind
            exact Option.some_inj.mp hfind
          have hstep : evalStmtFuel (F + 1) findWhile
                (mkFindEnv l nv kv t)
              = .ok (mkFindEnv l nv kv t,
                .returned (.u32 (BitVec.ofNat 32 t))) := by
            simp [findWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
              hcond, hbody]
          rw [← hjt]
          exact hstep
        · have hmiss : ∀ y, l[t]? = some y → y ≠ kv := by
            intro y hy
            rw [hget] at hy
            cases hy
            exact heq
          have hbody := findBody_miss F l nv kv t hmiss htl ht32
          have htail := findSuffix_miss l t (min nv.toNat l.length) kv
            hmiss hlt
          have hstep : evalStmtFuel (F + 1) findWhile
                (mkFindEnv l nv kv t)
              = evalStmtFuel F findWhile (mkFindEnv l nv kv (t + 1)) := by
            simp [findWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
              hcond, hbody]
          rw [hstep]
          rw [htail] at hfind
          exact ih (t + 1) j (by omega) (by omega) hfind
      | none =>
        have hsome : l[t]? = some l[t] := List.getElem?_eq_getElem htl
        rw [hsome] at hget
        simp at hget
    · have htt : t = min nv.toNat l.length := by omega
      subst htt
      have hnil := findSuffix_nil l (min nv.toNat l.length) kv
      rw [hnil] at hfind
      simp at hfind

/-- Loop correctness, miss: when the suffix finds nothing, the loop
    falls through with `i = n` (exact length) or reports `OOB`
    (over-long length) — mirroring `sumWhile_correct`/`sumWhile_oob`
    in one induction. -/
theorem findWhile_none (l : List (BitVec 32)) (nv kv : BitVec 32)
    (F t : Nat)
    (htm : t ≤ min nv.toNat l.length)
    (h32n : nv.toNat < 2 ^ 32) (h32l : l.length < 2 ^ 32)
    (hF : min nv.toNat l.length - t + 1 ≤ F)
    (hfind : findSuffixU32 l t (min nv.toNat l.length) kv = none) :
    evalStmtFuel F findWhile (mkFindEnv l nv kv t) =
      if decide (nv.toNat ≤ l.length) then
        .ok (mkFindEnv l nv kv nv.toNat, .fellThrough)
      else .error .OOB := by
  induction F generalizing t with
  | zero => omega
  | succ F ih =>
    by_cases hlt : t < min nv.toNat l.length
    · have htn : t < nv.toNat := by omega
      have htl : t < l.length := by omega
      have ht32 : t < 2 ^ 32 := by omega
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
            (mkFindEnv l nv kv t) = .ok (.b true) := by
        simpa [htn] using (findCond_eval l nv kv t ht32)
      have hget : l[t]? = some l[t] := List.getElem?_eq_getElem htl
      by_cases heq : l[t] = kv
      · exfalso
        have hfound := findSuffix_hit l t (min nv.toNat l.length) kv l[t]
          hget heq hlt
        rw [hfound] at hfind
        simp at hfind
      · have hmiss : ∀ y, l[t]? = some y → y ≠ kv := by
          intro y hy
          rw [hget] at hy
          cases hy
          exact heq
        have hbody := findBody_miss F l nv kv t hmiss htl ht32
        have htail := findSuffix_miss l t (min nv.toNat l.length) kv
          hmiss hlt
        have hstep : evalStmtFuel (F + 1) findWhile
              (mkFindEnv l nv kv t)
            = evalStmtFuel F findWhile (mkFindEnv l nv kv (t + 1)) := by
          simp [findWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
            hcond, hbody]
        rw [hstep]
        rw [htail] at hfind
        exact ih (t + 1) (by omega) (by omega) hfind
    · have htt : t = min nv.toNat l.length := by omega
      by_cases hnlen : nv.toNat ≤ l.length
      · have htn : t = nv.toNat := by omega
        subst htn
        have hcond : evalExpr (.ult (.var "i") (.var "n"))
              (mkFindEnv l nv kv nv.toNat) = .ok (.b false) := by
          simpa using (findCond_eval l nv kv nv.toNat h32n)
        have htrue : (decide (nv.toNat ≤ l.length)) = true := by
          simp [hnlen]
        simp [findWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond, htrue]
      · have htl2 : t = l.length := by omega
        subst htl2
        have hlt' : l.length < nv.toNat := by omega
        have hcond : evalExpr (.ult (.var "i") (.var "n"))
              (mkFindEnv l nv kv l.length) = .ok (.b true) := by
          simpa [hlt'] using (findCond_eval l nv kv l.length h32l)
        have hbody := findBody_oob F l nv kv h32l
        have hfalse : (decide (nv.toNat ≤ l.length)) = false := by
          simp [hnlen]
        simp [findWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond, hbody, hfalse]

/-- `emit_correct` for `find_eq`, fuel-generalized (split on the
    whole-prefix find, then on length exactness). -/
theorem evalFuncFuel_find (F : Nat) (l : List (BitVec 32))
    (nv kv : BitVec 32)
    (h32n : nv.toNat < 2 ^ 32) (h32l : l.length < 2 ^ 32)
    (hF : min nv.toNat l.length + 1 ≤ F) :
    evalFuncFuel F findEqFunc [.arr32 l, .u32 nv, .u32 kv] =
      findEqFwd l nv kv := by
  have hbind : bindArgs findEqFunc.args [.arr32 l, .u32 nv, .u32 kv] =
      some [("a", .arr32 l), ("n", .u32 nv), ("k", .u32 kv)] := rfl
  have hbody : findEqFunc.body =
      .seq (.let_ "i" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
      (.seq findWhile
            (.return_ (.var "n"))) := rfl
  have henv : [("i", .u32 (BitVec.ofNat 32 0)), ("a", .arr32 l),
        ("n", .u32 nv), ("k", .u32 kv)]
      = mkFindEnv l nv kv 0 := rfl
  have hbridge := findSuffix_zero_idx l nv.toNat kv
  match hfi : findIdxU32 l nv.toNat kv with
  | some j =>
    have hloop : ∀ (G : Nat),
        min nv.toNat l.length + 1 ≤ G →
        evalStmtFuel G findWhile (mkFindEnv l nv kv 0) =
          .ok (mkFindEnv l nv kv j,
            .returned (.u32 (BitVec.ofNat 32 j))) := by
      intro G hG
      exact findWhile_some l nv kv G 0 j (Nat.zero_le _) h32n
        (by omega) (by rw [hbridge, hfi])
    cases F with
    | zero =>
      have hloopH0 : evalStmtWith evalStmtZeroHandler
            findWhile (mkFindEnv l nv kv 0) =
          .ok (mkFindEnv l nv kv j,
            .returned (.u32 (BitVec.ofNat 32 j))) :=
        hloop 0 (by omega)
      simp [evalFuncFuel, findEqFunc, bindArgs, evalStmtFuel, evalStmtZero,
        evalStmtWith, evalExpr, litVal, envExtend, findEqFwd, findEqOut,
        henv, hloopH0, hfi]
    | succ F =>
      have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
            findWhile (mkFindEnv l nv kv 0) =
          .ok (mkFindEnv l nv kv j,
            .returned (.u32 (BitVec.ofNat 32 j))) :=
        hloop (F + 1) (by omega)
      simp [evalFuncFuel, findEqFunc, bindArgs, evalStmtFuel, evalStmtWith,
        evalExpr, litVal, envExtend, findEqFwd, findEqOut, henv, hloopS, hfi]
  | none =>
    have hloop : ∀ (G : Nat),
        min nv.toNat l.length + 1 ≤ G →
        evalStmtFuel G findWhile (mkFindEnv l nv kv 0) =
          if decide (nv.toNat ≤ l.length) then
            .ok (mkFindEnv l nv kv nv.toNat, .fellThrough)
          else .error .OOB := by
      intro G hG
      exact findWhile_none l nv kv G 0 (Nat.zero_le _) h32n h32l
        (by omega) (by rw [hbridge, hfi])
    by_cases hle : nv.toNat ≤ l.length
    · have htrue : (decide (nv.toNat ≤ l.length)) = true := by simp [hle]
      have hsnret : envLookup (mkFindEnv l nv kv nv.toNat) "n" =
            some (.u32 nv) :=
        mkFindEnv_n l nv kv nv.toNat
      have hinv : BitVec.ofNat 32 nv.toNat = nv := ofNat32_toNat_inv nv
      cases F with
      | zero =>
        have hloopH0 : evalStmtWith evalStmtZeroHandler
              findWhile (mkFindEnv l nv kv 0) =
            .ok (mkFindEnv l nv kv nv.toNat, .fellThrough) := by
          have h := hloop 0 (by omega)
          rwa [htrue] at h
        simp [evalFuncFuel, findEqFunc, bindArgs, evalStmtFuel, evalStmtZero,
          evalStmtWith, evalExpr, litVal, envExtend, findEqFwd, findEqOut,
          henv, hloopH0, hsnret, hfi, htrue, hinv]
      | succ F =>
        have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
              findWhile (mkFindEnv l nv kv 0) =
            .ok (mkFindEnv l nv kv nv.toNat, .fellThrough) := by
          have h := hloop (F + 1) (by omega)
          rwa [htrue] at h
        simp [evalFuncFuel, findEqFunc, bindArgs, evalStmtFuel, evalStmtWith,
          evalExpr, litVal, envExtend, findEqFwd, findEqOut, henv, hloopS,
          hsnret, hfi, htrue, hinv]
    · have hfalse : (decide (nv.toNat ≤ l.length)) = false := by
        simp [hle]
      cases F with
      | zero =>
        have hloopH0 : evalStmtWith evalStmtZeroHandler
              findWhile (mkFindEnv l nv kv 0) = .error .OOB := by
          have h := hloop 0 (by omega)
          rwa [hfalse] at h
        simp [evalFuncFuel, findEqFunc, bindArgs, evalStmtFuel, evalStmtZero,
          evalStmtWith, evalExpr, litVal, envExtend, findEqFwd, findEqOut,
          henv, hloopH0, hfi, hfalse]
      | succ F =>
        have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
              findWhile (mkFindEnv l nv kv 0) = .error .OOB := by
          have h := hloop (F + 1) (by omega)
          rwa [hfalse] at h
        simp [evalFuncFuel, findEqFunc, bindArgs, evalStmtFuel, evalStmtWith,
          evalExpr, litVal, envExtend, findEqFwd, findEqOut, henv, hloopS,
          hfi, hfalse]

/-- `emit_correct` for `find_eq` at the default fuel. -/
theorem emit_correct_find (l : List (BitVec 32)) (nv kv : BitVec 32)
    (h32n : nv.toNat < 2 ^ 32) (h32l : l.length < 2 ^ 32)
    (hfuel : min nv.toNat l.length + 1 ≤ EVAL_FUEL) :
    evalFunc findEqFunc [.arr32 l, .u32 nv, .u32 kv] = findEqFwd l nv kv :=
  evalFuncFuel_find EVAL_FUEL l nv kv h32n h32l hfuel
/-! ### `cls`: switch-as-if-chain (loop-free) -/

/-- Canonical CoreIR for `tests/c/cls.c`: the `cir.switch` (equality
    cases on `0`/`1` + `default`, every case a bare const `return`)
    lowered to a nested `if_` chain. The validator admits exactly this
    lowered shape (`isClsShape` pins the scrutinee type, case consts,
    and result consts); any other `cir.switch` is rejected loudly. -/
def clsFunc : Func :=
  ⟨"cls",
   [{ name := "x", ty := .u 32, role := .owned }],
   .u 32,
   .if_ (.ueq (.var "x") (.lit (.u32 0)))
     (.return_ (.lit (.u32 10)))
     (.if_ (.ueq (.var "x") (.lit (.u32 1)))
       (.return_ (.lit (.u32 20)))
       (.return_ (.lit (.u32 30))))⟩

/-- Value-level forward for `cls` (cf. rendered `cls_fwd`). -/
def clsFwd (x : BitVec 32) : Result Value :=
  if x == 0 then .ok (.u32 10)
  else if x == 1 then .ok (.u32 20)
  else .ok (.u32 30)

/-- `emit_correct` for `cls` (loop-free: any fuel). -/
theorem evalFuncFuel_cls (F : Nat) (x : BitVec 32) :
    evalFuncFuel F clsFunc [.u32 x] = clsFwd x := by
  have hbind : bindArgs clsFunc.args [.u32 x] =
      some [("x", .u32 x)] := rfl
  have hbody : clsFunc.body =
      .if_ (.ueq (.var "x") (.lit (.u32 0)))
        (.return_ (.lit (.u32 10)))
        (.if_ (.ueq (.var "x") (.lit (.u32 1)))
          (.return_ (.lit (.u32 20)))
          (.return_ (.lit (.u32 30)))) := rfl
  have hx : envLookup [("x", .u32 x)] "x" = some (.u32 x) :=
    envExtend_hit _ _ _
  by_cases h0 : x = 0
  · subst h0
    cases F <;>
      simp [evalFuncFuel, clsFunc, bindArgs, evalStmtFuel, evalStmtZero,
        evalStmtWith, evalExpr, litVal, envLookup, clsFwd]
  · have h0' : x ≠ 0#32 := h0
    by_cases h1 : x = 1
    · subst h1
      cases F <;>
        simp [evalFuncFuel, clsFunc, bindArgs, evalStmtFuel, evalStmtZero,
          evalStmtWith, evalExpr, litVal, envLookup, clsFwd]
    · have h1' : x ≠ 1#32 := h1
      have e0 : (x == 0#32) = false := by simp [h0']
      have e1 : (x == 1#32) = false := by simp [h1']
      cases F <;>
        simp [evalFuncFuel, clsFunc, bindArgs, evalStmtFuel, evalStmtZero,
          evalStmtWith, evalExpr, litVal, envLookup, clsFwd, e0, e1]

/-- `emit_correct` for `cls` at the default fuel. -/
theorem emit_correct_cls (x : BitVec 32) :
    evalFunc clsFunc [.u32 x] = clsFwd x :=
  evalFuncFuel_cls EVAL_FUEL x
/-! ### `cls_fall`: switch with fallthrough (N6b-i) -/

/-- Canonical CoreIR for `tests/c/cls_fall.c`: the empty `case 0`
    falls through to `case 1`, so both map to the `10` arm of the
    nested `if_` chain. The validator admits exactly this lowered shape
    (`isClsFallShape`: empty `case 0` region, `case 1` → `10`,
    `default` → `30`, no arithmetic). -/
def clsFallFunc : Func :=
  ⟨"cls_fall",
   [{ name := "x", ty := .u 32, role := .owned }],
   .u 32,
   .if_ (.ueq (.var "x") (.lit (.u32 0)))
     (.return_ (.lit (.u32 10)))
     (.if_ (.ueq (.var "x") (.lit (.u32 1)))
       (.return_ (.lit (.u32 10)))
       (.return_ (.lit (.u32 30))))⟩

/-- Value-level forward for `cls_fall` (cf. rendered `cls_fall_fwd`). -/
def clsFallFwd (x : BitVec 32) : Result Value :=
  if x == 0 then .ok (.u32 10)
  else if x == 1 then .ok (.u32 10)
  else .ok (.u32 30)

/-- `emit_correct` for `cls_fall` (loop-free: any fuel). -/
theorem evalFuncFuel_clsFall (F : Nat) (x : BitVec 32) :
    evalFuncFuel F clsFallFunc [.u32 x] = clsFallFwd x := by
  have hbind : bindArgs clsFallFunc.args [.u32 x] =
      some [("x", .u32 x)] := rfl
  have hbody : clsFallFunc.body =
      .if_ (.ueq (.var "x") (.lit (.u32 0)))
        (.return_ (.lit (.u32 10)))
        (.if_ (.ueq (.var "x") (.lit (.u32 1)))
          (.return_ (.lit (.u32 10)))
          (.return_ (.lit (.u32 30)))) := rfl
  have hx : envLookup [("x", .u32 x)] "x" = some (.u32 x) :=
    envExtend_hit _ _ _
  by_cases h0 : x = 0
  · subst h0
    cases F <;>
      simp [evalFuncFuel, clsFallFunc, bindArgs, evalStmtFuel, evalStmtZero,
        evalStmtWith, evalExpr, litVal, envLookup, clsFallFwd]
  · have h0' : x ≠ 0#32 := h0
    by_cases h1 : x = 1
    · subst h1
      cases F <;>
        simp [evalFuncFuel, clsFallFunc, bindArgs, evalStmtFuel, evalStmtZero,
          evalStmtWith, evalExpr, litVal, envLookup, clsFallFwd]
    · have h1' : x ≠ 1#32 := h1
      have e0 : (x == 0#32) = false := by simp [h0']
      have e1 : (x == 1#32) = false := by simp [h1']
      cases F <;>
        simp [evalFuncFuel, clsFallFunc, bindArgs, evalStmtFuel, evalStmtZero,
          evalStmtWith, evalExpr, litVal, envLookup, clsFallFwd, e0, e1]

/-- `emit_correct` for `cls_fall` at the default fuel. -/
theorem emit_correct_clsFall (x : BitVec 32) :
    evalFunc clsFallFunc [.u32 x] = clsFallFwd x :=
  evalFuncFuel_clsFall EVAL_FUEL x
/-! ### `cls_dense`: eight-case switch (N6b-i) -/

/-- Canonical CoreIR for `tests/c/cls_dense.c`: equality cases on
    `0`..`7` plus `default`, every case a bare const `return`, lowered
    to an 8-deep `if_` chain (dense switches stay `cir.switch` at CIR
    level — jump tables only appear at LLVM lowering). The validator
    admits exactly this lowered shape (`isClsDenseShape`). -/
def clsDenseFunc : Func :=
  ⟨"cls_dense",
   [{ name := "x", ty := .u 32, role := .owned }],
   .u 32,
   .if_ (.ueq (.var "x") (.lit (.u32 0)))
     (.return_ (.lit (.u32 0)))
     (.if_ (.ueq (.var "x") (.lit (.u32 1)))
       (.return_ (.lit (.u32 10)))
       (.if_ (.ueq (.var "x") (.lit (.u32 2)))
         (.return_ (.lit (.u32 20)))
         (.if_ (.ueq (.var "x") (.lit (.u32 3)))
           (.return_ (.lit (.u32 30)))
           (.if_ (.ueq (.var "x") (.lit (.u32 4)))
             (.return_ (.lit (.u32 40)))
             (.if_ (.ueq (.var "x") (.lit (.u32 5)))
               (.return_ (.lit (.u32 50)))
               (.if_ (.ueq (.var "x") (.lit (.u32 6)))
                 (.return_ (.lit (.u32 60)))
                 (.if_ (.ueq (.var "x") (.lit (.u32 7)))
                   (.return_ (.lit (.u32 70)))
                   (.return_ (.lit (.u32 80))))))))))⟩

/-- Value-level forward for `cls_dense` (cf. rendered `cls_dense_fwd`). -/
def clsDenseFwd (x : BitVec 32) : Result Value :=
  if x == 0 then .ok (.u32 0)
  else if x == 1 then .ok (.u32 10)
  else if x == 2 then .ok (.u32 20)
  else if x == 3 then .ok (.u32 30)
  else if x == 4 then .ok (.u32 40)
  else if x == 5 then .ok (.u32 50)
  else if x == 6 then .ok (.u32 60)
  else if x == 7 then .ok (.u32 70)
  else .ok (.u32 80)

/-- `emit_correct` for `cls_dense` (loop-free: any fuel). -/
theorem evalFuncFuel_clsDense (F : Nat) (x : BitVec 32) :
    evalFuncFuel F clsDenseFunc [.u32 x] = clsDenseFwd x := by
  have hbind : bindArgs clsDenseFunc.args [.u32 x] =
      some [("x", .u32 x)] := rfl
  have hx : envLookup [("x", .u32 x)] "x" = some (.u32 x) :=
    envExtend_hit _ _ _
  by_cases h0 : x = 0
  · subst h0
    cases F <;>
      simp [evalFuncFuel, clsDenseFunc, bindArgs, evalStmtFuel, evalStmtZero,
        evalStmtWith, evalExpr, litVal, envLookup, clsDenseFwd]
  · have h0' : x ≠ 0#32 := h0
    have e0 : (x == 0#32) = false := by simp [h0']
    by_cases h1 : x = 1
    · subst h1
      cases F <;>
        simp [evalFuncFuel, clsDenseFunc, bindArgs, evalStmtFuel, evalStmtZero,
          evalStmtWith, evalExpr, litVal, envLookup, clsDenseFwd, e0]
    · have h1' : x ≠ 1#32 := h1
      have e1 : (x == 1#32) = false := by simp [h1']
      by_cases h2 : x = 2
      · subst h2
        cases F <;>
          simp [evalFuncFuel, clsDenseFunc, bindArgs, evalStmtFuel, evalStmtZero,
            evalStmtWith, evalExpr, litVal, envLookup, clsDenseFwd, e0, e1]
      · have h2' : x ≠ 2#32 := h2
        have e2 : (x == 2#32) = false := by simp [h2']
        by_cases h3 : x = 3
        · subst h3
          cases F <;>
            simp [evalFuncFuel, clsDenseFunc, bindArgs, evalStmtFuel, evalStmtZero,
              evalStmtWith, evalExpr, litVal, envLookup, clsDenseFwd, e0, e1, e2]
        · have h3' : x ≠ 3#32 := h3
          have e3 : (x == 3#32) = false := by simp [h3']
          by_cases h4 : x = 4
          · subst h4
            cases F <;>
              simp [evalFuncFuel, clsDenseFunc, bindArgs, evalStmtFuel, evalStmtZero,
                evalStmtWith, evalExpr, litVal, envLookup, clsDenseFwd, e0, e1, e2, e3]
          · have h4' : x ≠ 4#32 := h4
            have e4 : (x == 4#32) = false := by simp [h4']
            by_cases h5 : x = 5
            · subst h5
              cases F <;>
                simp [evalFuncFuel, clsDenseFunc, bindArgs, evalStmtFuel, evalStmtZero,
                  evalStmtWith, evalExpr, litVal, envLookup, clsDenseFwd, e0, e1, e2, e3, e4]
            · have h5' : x ≠ 5#32 := h5
              have e5 : (x == 5#32) = false := by simp [h5']
              by_cases h6 : x = 6
              · subst h6
                cases F <;>
                  simp [evalFuncFuel, clsDenseFunc, bindArgs, evalStmtFuel, evalStmtZero,
                    evalStmtWith, evalExpr, litVal, envLookup, clsDenseFwd, e0, e1, e2, e3, e4, e5]
              · have h6' : x ≠ 6#32 := h6
                have e6 : (x == 6#32) = false := by simp [h6']
                by_cases h7 : x = 7
                · subst h7
                  cases F <;>
                    simp [evalFuncFuel, clsDenseFunc, bindArgs, evalStmtFuel, evalStmtZero,
                      evalStmtWith, evalExpr, litVal, envLookup, clsDenseFwd, e0, e1, e2, e3, e4, e5, e6]
                · have h7' : x ≠ 7#32 := h7
                  have e7 : (x == 7#32) = false := by simp [h7']
                  cases F <;>
                    simp [evalFuncFuel, clsDenseFunc, bindArgs, evalStmtFuel, evalStmtZero,
                      evalStmtWith, evalExpr, litVal, envLookup, clsDenseFwd, e0, e1, e2, e3, e4, e5, e6, e7]

/-- `emit_correct` for `cls_dense` at the default fuel. -/
theorem emit_correct_clsDense (x : BitVec 32) :
    evalFunc clsDenseFunc [.u32 x] = clsDenseFwd x :=
  evalFuncFuel_clsDense EVAL_FUEL x
/-! ### `cls_break`: break-switch without default (N6b-ii) -/

/-- Canonical CoreIR for `tests/c/cls_break.c`: the result local `r`
    starts at `99`; each case is a guarded assign (the `cir.break`s
    erase — disjoint guards make the sequential assigns exact);
    unmatched scrutinees keep `99`. The validator admits exactly this
    lowered shape (`isClsBreakShape`). -/
def clsBreakFunc : Func :=
  ⟨"cls_break",
   [{ name := "x", ty := .u 32, role := .owned }],
   .u 32,
   .seq (.let_ "r" (.u 32) (.lit (.u32 99)))
   (.seq (.if_ (.ueq (.var "x") (.lit (.u32 0)))
            (.assign "r" (.lit (.u32 10)))
            .skip)
   (.seq (.if_ (.ueq (.var "x") (.lit (.u32 1)))
            (.assign "r" (.lit (.u32 20)))
            .skip)
         (.return_ (.var "r"))))⟩

/-- Value-level forward for `cls_break` (cf. rendered `cls_break_fwd`). -/
def clsBreakFwd (x : BitVec 32) : Result Value :=
  .ok (.u32 (if x == 0 then 10 else if x == 1 then 20 else 99))

/-- `emit_correct` for `cls_break` (loop-free: any fuel). -/
theorem evalFuncFuel_clsBreak (F : Nat) (x : BitVec 32) :
    evalFuncFuel F clsBreakFunc [.u32 x] = clsBreakFwd x := by
  have hbind : bindArgs clsBreakFunc.args [.u32 x] =
      some [("x", .u32 x)] := rfl
  have hbody : clsBreakFunc.body =
      .seq (.let_ "r" (.u 32) (.lit (.u32 99)))
      (.seq (.if_ (.ueq (.var "x") (.lit (.u32 0)))
               (.assign "r" (.lit (.u32 10)))
               .skip)
      (.seq (.if_ (.ueq (.var "x") (.lit (.u32 1)))
               (.assign "r" (.lit (.u32 20)))
               .skip)
            (.return_ (.var "r")))) := rfl
  have hx : envLookup [("x", .u32 x)] "x" = some (.u32 x) :=
    envExtend_hit _ _ _
  have hxr : ("x" : String) ≠ "r" := by decide
  by_cases h0 : x = 0
  · subst h0
    have hupd : envUpdate [("r", .u32 99#32), ("x", .u32 0#32)]
        "r" (.u32 10#32) =
        some [(("r", .u32 10#32)), ("x", .u32 0#32)] :=
      envUpdate_hit _ _ _ _
    have hlk : envLookup [(("r", .u32 10#32)), ("x", .u32 0#32)] "x" =
        some (.u32 0#32) := by simp [envLookup, hxr]
    have g01 : (0#32 == 1#32) = false := by decide
    cases F <;>
      simp [evalFuncFuel, clsBreakFunc, bindArgs, evalStmtFuel, evalStmtZero,
        evalStmtWith, evalExpr, litVal, envLookup, envExtend, clsBreakFwd,
        hupd, hlk, g01]
  · have h0' : x ≠ 0#32 := h0
    have e0 : (x == 0#32) = false := by simp [h0']
    by_cases h1 : x = 1
    · subst h1
      have hupd : envUpdate [("r", .u32 99#32), ("x", .u32 1#32)]
          "r" (.u32 20#32) =
          some [(("r", .u32 20#32)), ("x", .u32 1#32)] :=
        envUpdate_hit _ _ _ _
      have hlk : envLookup [(("r", .u32 20#32)), ("x", .u32 1#32)] "x" =
          some (.u32 1#32) := by simp [envLookup, hxr]
      cases F <;>
        simp [evalFuncFuel, clsBreakFunc, bindArgs, evalStmtFuel, evalStmtZero,
          evalStmtWith, evalExpr, litVal, envLookup, envExtend, clsBreakFwd, e0,
          hupd, hlk]
    · have h1' : x ≠ 1#32 := h1
      have e1 : (x == 1#32) = false := by simp [h1']
      have hlk : envLookup [(("r", .u32 99#32)), ("x", .u32 x)] "x" =
          some (.u32 x) := by simp [envLookup, hxr]
      cases F <;>
        simp [evalFuncFuel, clsBreakFunc, bindArgs, evalStmtFuel, evalStmtZero,
          evalStmtWith, evalExpr, litVal, envLookup, envExtend, clsBreakFwd, e0, e1,
          hlk]

/-- `emit_correct` for `cls_break` at the default fuel. -/
theorem emit_correct_clsBreak (x : BitVec 32) :
    evalFunc clsBreakFunc [.u32 x] = clsBreakFwd x :=
  evalFuncFuel_clsBreak EVAL_FUEL x
