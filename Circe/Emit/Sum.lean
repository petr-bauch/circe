/-
Circe.Emit.Sum — `sum_array`: bounded loop over a length-paired array
(canonical `Func`, forward, loop invariant, fuel-generalized correctness).
-/
import Circe.Emit.Fragment
import Circe.Emit.SumFwd

/-! ## `sum_array`: bounded loop over a length-paired array -/


/-- Splitting a drop at a valid index exposes head and tail. -/
theorem drop_cons_getElem (l : List (BitVec 32)) (k : Nat)
    (h : k < l.length) :
    l.drop k = l[k] :: l.drop (k + 1) := by
  induction l generalizing k with
  | nil => simp at h
  | cons x xs ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hk : k < xs.length := by
        simp only [List.length_cons] at h
        omega
      simp only [List.drop_succ_cons, List.getElem_cons_succ]
      exact ih k hk

/-! ### Canonical CoreIR + verified forward function -/

/-- Loop body: `s = s + a[i]; i = i + 1` (wrapping `u32`, plain `cir.add`;
    `cir.for` step region). The `1` is written `1#32` (`ofNat`-headed):
    simp's simprocs normalize `1` to `1#32`, so rewrite rules must use the
    normal form to match. -/
def sumBody : CStmt :=
  .seq (.assign "s" (.uadd (.var "s") (.idx "a" (.var "i"))))
       (.assign "i" (.uadd (.var "i") (.lit (.u32 1#32))))

/-- Loop: `while (i < n) { ... }` (`cir.for` cond region). -/
def sumWhile : CStmt :=
  .while_ (.ult (.var "i") (.var "n")) sumBody

/-- Canonical CoreIR for `tests/c/sum_array.c`. `a` is a `sharedBorrow`
    (pure list value, copy semantics); `n` is the 32-bit length
    (C `size_t` lengths must fit 32 bits — `validate` narrows
    them, runtime excess is `OOB`). The static array bound (4096) equals
    `EVAL_FUEL`: capacity and fuel coincide by construction. -/
def sumFunc : Func :=
  ⟨"sum_array",
   [{ name := "a", ty := .array (.u 32) 4096, role := .sharedBorrow },
    { name := "n", ty := .u 32, role := .owned }],
   .u 32,
   .seq (.let_ "s" (.u 32) (.lit (.u32 0)))
   (.seq (.let_ "i" (.u 32) (.lit (.u32 0)))
   (.seq sumWhile
         (.return_ (.var "s"))))⟩

/-- Value-level forward function for `sum_array` (cf. rendered `sum_fwd`):
    wrapping prefix sum of the first `n` elements; `OOB` when `n` exceeds
    the array (C would read out of bounds there — UB made loud). -/
def sumFwd (l : List (BitVec 32)) (n : BitVec 32) : Result Value :=
  if n.toNat ≤ l.length then .ok (.u32 (prefixSumU32 l n.toNat))
  else .error .OOB

/-- OOB corollary helper: `sumFwd` reports `OOB` exactly off-range. -/
theorem sumFwd_oob (l : List (BitVec 32)) (n : BitVec 32)
    (h : ¬ n.toNat ≤ l.length) : sumFwd l n = .error .OOB := by
  simp [sumFwd, h]

theorem sumFwd_ok (l : List (BitVec 32)) (n : BitVec 32)
    (h : n.toNat ≤ l.length) :
    sumFwd l n = .ok (.u32 (prefixSumU32 l n.toNat)) := by
  simp [sumFwd, h]


/-! ### Loop invariant -/

/-- Loop environments: index `k` and accumulator, array and bound fixed. -/
def mkSumEnv (l : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) : Env :=
  [("i", .u32 (BitVec.ofNat 32 k)), ("s", .u32 acc),
   ("a", .arr32 l), ("n", .u32 nv)]

theorem mkSumEnv_i (l : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) :
    envLookup (mkSumEnv l nv k acc) "i" =
      some (.u32 (BitVec.ofNat 32 k)) := by
  simp [mkSumEnv, envLookup]

theorem mkSumEnv_s (l : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) :
    envLookup (mkSumEnv l nv k acc) "s" = some (.u32 acc) := by
  simp [mkSumEnv, envLookup, show ("s" : String) ≠ "i" by decide]

theorem mkSumEnv_a (l : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) :
    envLookup (mkSumEnv l nv k acc) "a" = some (.arr32 l) := by
  simp [mkSumEnv, envLookup, show ("a" : String) ≠ "i" by decide,
    show ("a" : String) ≠ "s" by decide]

theorem mkSumEnv_n (l : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) :
    envLookup (mkSumEnv l nv k acc) "n" = some (.u32 nv) := by
  simp [mkSumEnv, envLookup, show ("n" : String) ≠ "i" by decide,
    show ("n" : String) ≠ "s" by decide,
    show ("n" : String) ≠ "a" by decide]

/-- Updating `s` in a loop env stays a loop env. -/
theorem sumEnv_update_s (l : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc v : BitVec 32) :
    envUpdate (mkSumEnv l nv k acc) "s" (.u32 v) =
      some (mkSumEnv l nv k v) := by
  simp [mkSumEnv, envUpdate, show ("s" : String) ≠ "i" by decide]

/-- Updating `i` in a loop env stays a loop env. -/
theorem sumEnv_update_i (l : List (BitVec 32)) (nv : BitVec 32) (k k' : Nat)
    (acc : BitVec 32) :
    envUpdate (mkSumEnv l nv k acc) "i" (.u32 (BitVec.ofNat 32 k')) =
      some (mkSumEnv l nv k' acc) := by
  simp [mkSumEnv, envUpdate]

/-- The loop condition reads the index against the bound. -/
theorem sumCond_eval (l : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) (h : k < 2 ^ 32) :
    evalExpr (.ult (.var "i") (.var "n")) (mkSumEnv l nv k acc) =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkSumEnv_i l nv k acc
  have hn := mkSumEnv_n l nv k acc
  simp [evalExpr, hi, hn, ofNat32_ult k nv h]

/-- One body step advances index and accumulator (any fuel: loop-free). -/
theorem sumBody_eval (F : Nat) (l : List (BitVec 32)) (nv : BitVec 32)
    (k : Nat) (acc : BitVec 32)
    (hklen : k < l.length) (hk32 : k < 2 ^ 32) :
    evalStmtFuel F sumBody (mkSumEnv l nv k acc) =
      .ok (mkSumEnv l nv (k + 1) (acc + l[k]), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hget : l[k]? = some l[k] := List.getElem?_eq_getElem hklen
  have hs : evalExpr (.uadd (.var "s") (.idx "a" (.var "i")))
        (mkSumEnv l nv k acc) = .ok (.u32 (acc + l[k])) := by
    have h1 := mkSumEnv_s l nv k acc
    have ha := mkSumEnv_a l nv k acc
    have hii := mkSumEnv_i l nv k acc
    simp only [evalExpr, h1, ha, hii, hkk, hget]
  have hi2 : evalExpr (.uadd (.var "i") (.lit (.u32 1#32)))
        (mkSumEnv l nv k (acc + l[k])) =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkSumEnv_i l nv k (acc + l[k])
    simp only [evalExpr, litVal, h1, ofNat32_add_one]
  have up1 := sumEnv_update_s l nv k acc (acc + l[k])
  have up2 := sumEnv_update_i l nv k (k + 1) (acc + l[k])
  cases F <;>
    simp [sumBody, evalStmtFuel, evalStmtZero, evalStmtWith, hs, hi2, up1, up2]

/-- The OOB step: at `k = length` the index read fails loudly
    (independent of the bound `n`). -/
theorem sumBody_oob (F : Nat) (l : List (BitVec 32)) (nv : BitVec 32)
    (acc : BitVec 32) (h32 : l.length < 2 ^ 32) :
    evalStmtFuel F sumBody
        (mkSumEnv l nv l.length acc) = .error .OOB := by
  have hkk : (BitVec.ofNat 32 l.length).toNat = l.length :=
    ofNat32_toNat _ h32
  have hget : l[l.length]? = none :=
    List.getElem?_eq_none (Nat.le_refl _)
  have ha := mkSumEnv_a l nv l.length acc
  have hii := mkSumEnv_i l nv l.length acc
  have hs : evalExpr (.uadd (.var "s") (.idx "a" (.var "i")))
        (mkSumEnv l nv l.length acc) = .error .OOB := by
    have h1 := mkSumEnv_s l nv l.length acc
    simp only [evalExpr, h1, ha, hii, hkk, hget]
  cases F <;>
    simp [sumBody, evalStmtFuel, evalStmtZero, evalStmtWith, hs]

/-- Loop correctness, in-range: the loop folds the remaining suffix. -/
theorem sumWhile_correct (l : List (BitVec 32)) (nv : BitVec 32)
    (F k : Nat) (acc : BitVec 32)
    (hk : k ≤ nv.toNat)
    (hlen : nv.toNat ≤ l.length)
    (h32 : nv.toNat < 2 ^ 32)
    (hF : nv.toNat - k ≤ F) :
    evalStmtFuel F sumWhile (mkSumEnv l nv k acc) =
      .ok (mkSumEnv l nv nv.toNat
        (acc + prefixSumU32 (l.drop k) (nv.toNat - k)), .fellThrough) := by
  induction F generalizing k acc with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : evalExpr (.ult (.var "i") (.var "n"))
        (mkSumEnv l nv nv.toNat acc) = .ok (.b false) := by
      simpa using (sumCond_eval l nv nv.toNat acc h32)
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    have hpre : prefixSumU32 (l.drop nv.toNat) 0 = 0 := prefixSumU32_zero _
    simp [sumWhile, evalStmtFuel, evalStmtZero, evalStmtZeroHandler, evalStmtWith,
      hcond, hsub, hpre]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hklen : k < l.length := by omega
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkSumEnv l nv k acc) = .ok (.b true) := by
        simpa [hlt] using (sumCond_eval l nv k acc hk32)
      have hbody := sumBody_eval F l nv k acc hklen hk32
      have hstep : evalStmtFuel (F + 1) sumWhile (mkSumEnv l nv k acc)
          = evalStmtFuel F sumWhile (mkSumEnv l nv (k + 1) (acc + l[k])) := by
        simp [sumWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith, hcond,
          hbody]
      rw [hstep]
      have hrec := ih (k + 1) (acc + l[k]) (by omega) (by omega)
      rw [hrec]
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      have hdrop : l.drop k = l[k] :: l.drop (k + 1) :=
        drop_cons_getElem l k hklen
      have hacc : (acc + l[k]) +
            prefixSumU32 (l.drop (k + 1)) (nv.toNat - (k + 1))
          = acc + prefixSumU32 (l.drop k) (nv.toNat - k) := by
        rw [hkk1, hdrop, prefixSumU32_cons]
        exact BitVec.add_assoc _ _ _
      rw [hacc]
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkSumEnv l nv nv.toNat acc) = .ok (.b false) := by
        simpa using (sumCond_eval l nv nv.toNat acc h32)
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      have hpre : prefixSumU32 (l.drop nv.toNat) 0 = 0 := prefixSumU32_zero _
      simp [sumWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith, hcond,
        hsub, hpre]

/-- Loop correctness, out-of-range: the loop reports `OOB` at the end.
    Note the bound is on the *length* (`hlen32`): `n` itself may exceed
    32 bits here (that is the OOB case); indices never pass `length`. -/
theorem sumWhile_oob (l : List (BitVec 32)) (nv : BitVec 32)
    (F k : Nat) (acc : BitVec 32)
    (hk : k ≤ l.length)
    (hlt : l.length < nv.toNat)
    (hlen32 : l.length < 2 ^ 32)
    (hF : l.length - k + 1 ≤ F) :
    evalStmtFuel F sumWhile (mkSumEnv l nv k acc) = .error .OOB := by
  induction F generalizing k acc with
  | zero => omega
  | succ F ih =>
    by_cases hlt2 : k < l.length
    · have hk32 : k < 2 ^ 32 := by omega
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkSumEnv l nv k acc) = .ok (.b true) := by
        have hkn : k < nv.toNat := by omega
        simpa [hkn] using (sumCond_eval l nv k acc hk32)
      have hbody := sumBody_eval F l nv k acc hlt2 hk32
      have hstep : evalStmtFuel (F + 1) sumWhile (mkSumEnv l nv k acc)
          = evalStmtFuel F sumWhile (mkSumEnv l nv (k + 1) (acc + l[k])) := by
        simp [sumWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith, hcond,
          hbody]
      rw [hstep]
      exact ih (k + 1) (acc + l[k]) (by omega) (by omega)
    · have hkk : k = l.length := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkSumEnv l nv l.length acc) = .ok (.b true) := by
        simpa [hlt] using
          (sumCond_eval l nv l.length acc hlen32)
      have hbody := sumBody_oob F l nv acc hlen32
      simp [sumWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith, hcond,
        hbody]

/-! ### Whole-function correctness (fuel-generalized, then instantiated) -/

/-- `emit_correct` for `sum`, at any fuel covering `n`. -/
theorem evalFuncFuel_sum (F : Nat) (l : List (BitVec 32)) (nv : BitVec 32)
    (hle : nv.toNat ≤ l.length) (h32 : nv.toNat < 2 ^ 32)
    (hF : nv.toNat ≤ F) :
    evalFuncFuel F sumFunc [.arr32 l, .u32 nv] = sumFwd l nv := by
  -- Stated with `ofNat`-headed zeros (simp's simprocs normalize `0` to
  -- `0#32`, so `OfNat`-headed forms would not match after normalization).
  have henv : [("i", .u32 (BitVec.ofNat 32 0)),
        ("s", .u32 (BitVec.ofNat 32 0)),
        ("a", .arr32 l), ("n", .u32 nv)]
      = mkSumEnv l nv 0 (BitVec.ofNat 32 0) := rfl
  have hret := mkSumEnv_s l nv nv.toNat (prefixSumU32 l nv.toNat)
  -- The loop `have`s match simp's *unfolded* handler forms (the fuel
  -- equations necessarily unfold the loop while evaluating the lets, so a
  -- folded `evalStmtFuel` statement could never match). Handlers are named
  -- definitions (`evalStmtZeroHandler` / `evalStmtSuccHandler`), so the
  -- rules match syntactically; each is proved from the corresponding loop
  -- theorem by definitional unfolding (`exact` checks up to defeq).
  cases F with
  | zero =>
    -- Inside the zero branch `hF` forces `nv.toNat = 0`.
    have hloopH0 : evalStmtWith evalStmtZeroHandler
          sumWhile (mkSumEnv l nv 0 (BitVec.ofNat 32 0))
        = .ok (mkSumEnv l nv nv.toNat
            (BitVec.ofNat 32 0 + prefixSumU32 (l.drop 0) (nv.toNat - 0)),
            .fellThrough) :=
      sumWhile_correct l nv 0 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hle h32
        (by cir_fuel)
    simp [evalFuncFuel, sumFunc, bindArgs, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, litVal, envExtend, sumFwd, henv, hloopH0, hret,
      hle]
  | succ F =>
    have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          sumWhile (mkSumEnv l nv 0 (BitVec.ofNat 32 0))
        = .ok (mkSumEnv l nv nv.toNat
            (BitVec.ofNat 32 0 + prefixSumU32 (l.drop 0) (nv.toNat - 0)),
            .fellThrough) :=
      sumWhile_correct l nv (F + 1) 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hle
        h32 (by cir_fuel)
    simp [evalFuncFuel, sumFunc, bindArgs, evalStmtFuel, evalStmtWith,
      evalExpr, litVal, envExtend, sumFwd, henv, hloopS, hret, hle]

/-- `emit_correct` for `sum` at the default fuel. -/
theorem emit_correct_sum (l : List (BitVec 32)) (nv : BitVec 32)
    (hle : nv.toNat ≤ l.length) (hfuel : nv.toNat ≤ EVAL_FUEL) :
    evalFunc sumFunc [.arr32 l, .u32 nv] = sumFwd l nv := by
  have h32 : nv.toNat < 2 ^ 32 := word32_lt_two32_of_fuel _ hfuel
  exact evalFuncFuel_sum EVAL_FUEL l nv hle h32 hfuel

/-- OOB corollary: over-long lengths fail loudly on both sides. -/
theorem evalFuncFuel_sum_oob (F : Nat) (l : List (BitVec 32))
    (nv : BitVec 32)
    (hlt : l.length < nv.toNat) (hlen32 : l.length < 2 ^ 32)
    (hF : l.length + 1 ≤ F) :
    evalFuncFuel F sumFunc [.arr32 l, .u32 nv] = .error .OOB := by
  -- `ofNat`-headed zeros (see `evalFuncFuel_sum`).
  have henv : [("i", .u32 (BitVec.ofNat 32 0)),
        ("s", .u32 (BitVec.ofNat 32 0)),
        ("a", .arr32 l), ("n", .u32 nv)]
      = mkSumEnv l nv 0 (BitVec.ofNat 32 0) := rfl
  cases F with
  | zero =>
    have hloopH0 : evalStmtWith evalStmtZeroHandler
          sumWhile (mkSumEnv l nv 0 (BitVec.ofNat 32 0)) = .error .OOB :=
      sumWhile_oob l nv 0 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hlt hlen32
        (by cir_fuel)
    simp [evalFuncFuel, sumFunc, bindArgs, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, litVal, envExtend, henv, hloopH0]
  | succ F =>
    have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          sumWhile (mkSumEnv l nv 0 (BitVec.ofNat 32 0)) = .error .OOB :=
      sumWhile_oob l nv (F + 1) 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hlt
        hlen32 (by cir_fuel)
    simp [evalFuncFuel, sumFunc, bindArgs, evalStmtFuel, evalStmtWith,
      evalExpr, litVal, envExtend, henv, hloopS]

/-- OOB corollary at the default fuel. -/
theorem emit_correct_sum_oob (l : List (BitVec 32)) (nv : BitVec 32)
    (hlt : l.length < nv.toNat) (hfuel : l.length + 1 ≤ EVAL_FUEL) :
    evalFunc sumFunc [.arr32 l, .u32 nv] = .error .OOB := by
  have hlen32 : l.length < 2 ^ 32 := by cir_fuel
  exact evalFuncFuel_sum_oob EVAL_FUEL l nv hlt hlen32 hfuel
