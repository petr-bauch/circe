/-
Circe.Crypto.ShaLoops — fuel-induction loop evaluations for the K5
SHA-256 block function (split from `Circe.Crypto.ShaBlock` under the
~2k-line discipline): the init, work-init, schedule and add-back
`while_` loops evaluate to their `Circe.Crypto.Sha` loop functions.
(Transfer/compress/OOB/func-dispatch follow in K5c slices B–D.)
-/
import Circe.Crypto.ShaBlock

/-! ### Loop evaluation (fuel induction, K4 `roundWhile_correct` precedent) -/

/-- The block-copy loop evaluates to `initLoop 16 0` (fuel
    induction mirroring `roundWhile_correct`; the invariant phrases
    the remaining copy suffix-style since `initLoop` composes
    inside-out: `initLoop (16 - t) t w = initLoop 16 0 w0`). -/
theorem initWhile_correct (F : Nat) (s : List (BitVec 32)) (t : Nat)
    (w w0 : List (BitVec 32))
    (ht : t ≤ 16) (hs : 24 ≤ s.length) (hw : w.length = 64)
    (hinv : initLoop (16 - t) t w s = initLoop 16 0 w0 s)
    (hF : 16 - t ≤ F) :
    evalStmtFuel F initWhile (mkInitEnv s t w) =
      .ok (mkInitEnv s 16 (initLoop 16 0 w0 s), .fellThrough) := by
  induction F generalizing t w with
  | zero =>
    have ht16 : t = 16 := by omega
    subst ht16
    have hcond := initCond_eval s 16 w (by decide)
    have hcondF : evalExpr (.ult (.var "t")
          (.lit (.u64 (BitVec.ofNat 64 16)))) (mkInitEnv s 16 w) =
        .ok (.b false) := by
      simpa using hcond
    have hdone : w = initLoop 16 0 w0 s := hinv
    rw [hdone] at hcondF ⊢
    simp [initWhile, evalStmtFuel, evalStmtZero, evalStmtZeroHandler,
      evalStmtWith, hcondF]
  | succ F ih =>
    by_cases hlt : t < 16
    · have ht64 : t < 2 ^ 64 := by omega
      have hcond := initCond_eval s t w ht64
      have hcondT : evalExpr (.ult (.var "t")
            (.lit (.u64 (BitVec.ofNat 64 16)))) (mkInitEnv s t w) =
          .ok (.b true) := by
        simpa [hlt] using hcond
      have hbody := initBody_eval F s t w hlt hs hw ht64
      have hstep : evalStmtFuel (F + 1) initWhile (mkInitEnv s t w)
          = evalStmtFuel F initWhile
            (mkInitEnv s (t + 1) (w.set t s[8 + t])) := by
        simp [initWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcondT, hbody]
      rw [hstep]
      have ht' : t + 1 ≤ 16 := by omega
      have hw' : (w.set t s[8 + t]).length = 64 := by
        rw [List.length_set]; exact hw
      have hget : s[8 + t]? = some s[8 + t] :=
        List.getElem?_eq_getElem (by omega)
      have hset : w.set t s[8 + t] = initStep w s t := by
        simp [initStep, hget]
      have e1 : 16 - (t + 1) = 16 - t - 1 := by omega
      have e2 : 16 - t = (16 - t - 1) + 1 := by omega
      have hinv' : initLoop (16 - (t + 1)) (t + 1) (w.set t s[8 + t]) s =
          initLoop 16 0 w0 s := by
        rw [hset, e1, ← initLoop_succ, ← e2]
        exact hinv
      exact ih (t + 1) (w.set t s[8 + t]) ht' hw' hinv' (by omega)
    · have ht16 : t = 16 := by omega
      subst ht16
      have hcond := initCond_eval s 16 w (by decide)
      have hcondF : evalExpr (.ult (.var "t")
            (.lit (.u64 (BitVec.ofNat 64 16)))) (mkInitEnv s 16 w) =
          .ok (.b false) := by
        simpa using hcond
      have hdone : w = initLoop 16 0 w0 s := hinv
      rw [hdone] at hcondF ⊢
      simp [initWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
        hcondF]

/-- The work-init loop evaluates to `vinitLoop 8 0` (same
    suffix-style induction over the digest head). -/
theorem vinitWhile_correct (F : Nat) (s : List (BitVec 32)) (i : Nat)
    (v v0 : List (BitVec 32)) (w : List (BitVec 32))
    (hi : i ≤ 8) (hs : 24 ≤ s.length) (hvlen : v.length = 8)
    (hinv : vinitLoop (8 - i) i v s = vinitLoop 8 0 v0 s)
    (hF : 8 - i ≤ F) :
    evalStmtFuel F vinitWhile (mkVinitEnv s i v w) =
      .ok (mkVinitEnv s 8 (vinitLoop 8 0 v0 s) w, .fellThrough) := by
  induction F generalizing i v with
  | zero =>
    have hi8 : i = 8 := by omega
    subst hi8
    have hcond := vinitCond_eval s 8 v w (by decide)
    have hcondF : evalExpr (.ult (.var "i")
          (.lit (.u64 (BitVec.ofNat 64 8)))) (mkVinitEnv s 8 v w) =
        .ok (.b false) := by
      simpa using hcond
    have hdone : v = vinitLoop 8 0 v0 s := hinv
    rw [hdone] at hcondF ⊢
    simp [vinitWhile, evalStmtFuel, evalStmtZero, evalStmtZeroHandler,
      evalStmtWith, hcondF]
  | succ F ih =>
    by_cases hlt : i < 8
    · have hi64 : i < 2 ^ 64 := by omega
      have hcond := vinitCond_eval s i v w hi64
      have hcondT : evalExpr (.ult (.var "i")
            (.lit (.u64 (BitVec.ofNat 64 8)))) (mkVinitEnv s i v w) =
          .ok (.b true) := by
        simpa [hlt] using hcond
      have hbody := vinitBody_eval F s i v w hlt hs hvlen hi64
      have hstep : evalStmtFuel (F + 1) vinitWhile (mkVinitEnv s i v w)
          = evalStmtFuel F vinitWhile
            (mkVinitEnv s (i + 1) (v.set i s[i]) w) := by
        simp [vinitWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcondT, hbody]
      rw [hstep]
      have hi' : i + 1 ≤ 8 := by omega
      have hvlen' : (v.set i s[i]).length = 8 := by
        rw [List.length_set]; exact hvlen
      have hget : s[i]? = some s[i] := List.getElem?_eq_getElem (by omega)
      have hset : v.set i s[i] = vinitStep v s i := by
        simp [vinitStep, hget]
      have e1 : 8 - (i + 1) = 8 - i - 1 := by omega
      have e2 : 8 - i = (8 - i - 1) + 1 := by omega
      have hinv' : vinitLoop (8 - (i + 1)) (i + 1) (v.set i s[i]) s =
          vinitLoop 8 0 v0 s := by
        rw [hset, e1, ← vinitLoop_succ, ← e2]
        exact hinv
      exact ih (i + 1) (v.set i s[i]) hi' hvlen' hinv' (by omega)
    · have hi8 : i = 8 := by omega
      subst hi8
      have hcond := vinitCond_eval s 8 v w (by decide)
      have hcondF : evalExpr (.ult (.var "i")
            (.lit (.u64 (BitVec.ofNat 64 8)))) (mkVinitEnv s 8 v w) =
          .ok (.b false) := by
        simpa using hcond
      have hdone : v = vinitLoop 8 0 v0 s := hinv
      rw [hdone] at hcondF ⊢
      simp [vinitWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
        hcondF]

/-- The schedule loop evaluates to `schedLoop 48 16` (fuel induction
    mirroring `initWhile_correct`; the counter runs `16 → 64` and the
    invariant phrases the remaining fill suffix-style). -/
theorem schedWhile_correct (F : Nat) (s : List (BitVec 32)) (u : Nat)
    (w w0 : List (BitVec 32))
    (hu : u ≤ 64) (hu16 : 16 ≤ u) (hw : w.length = 64)
    (hinv : schedLoop (64 - u) u w = schedLoop 48 16 w0)
    (hF : 64 - u ≤ F) :
    evalStmtFuel F schedWhile (mkSchedEnv s u w) =
      .ok (mkSchedEnv s 64 (schedLoop 48 16 w0), .fellThrough) := by
  induction F generalizing u w with
  | zero =>
    have hu64 : u = 64 := by omega
    subst hu64
    have hcond := schedCond_eval s 64 w (by decide)
    have hcondF : evalExpr (.ult (.var "u")
          (.lit (.u64 (BitVec.ofNat 64 64)))) (mkSchedEnv s 64 w) =
        .ok (.b false) := by
      simpa using hcond
    have hdone : w = schedLoop 48 16 w0 := hinv
    rw [hdone] at hcondF ⊢
    simp [schedWhile, evalStmtFuel, evalStmtZero, evalStmtZeroHandler,
      evalStmtWith, hcondF]
  | succ F ih =>
    by_cases hlt : u < 64
    · have hu642 : u < 2 ^ 64 := by omega
      have hcond := schedCond_eval s u w hu642
      have hcondT : evalExpr (.ult (.var "u")
            (.lit (.u64 (BitVec.ofNat 64 64)))) (mkSchedEnv s u w) =
          .ok (.b true) := by
        simpa [hlt] using hcond
      have hbody := schedBody_eval F s u w (by omega) hlt hw hu642
      have hstep : evalStmtFuel (F + 1) schedWhile (mkSchedEnv s u w)
          = evalStmtFuel F schedWhile
            (mkSchedEnv s (u + 1)
              (w.set u (sV11 w[u - 16] w[u - 15] w[u - 7] w[u - 2]))) := by
        simp [schedWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcondT, hbody]
      rw [hstep]
      have hu' : u + 1 ≤ 64 := by omega
      have hu16' : 16 ≤ u + 1 := by omega
      have hw' : (w.set u
          (sV11 w[u - 16] w[u - 15] w[u - 7] w[u - 2])).length = 64 := by
        rw [List.length_set]; exact hw
      have hgu : w[u]? = some w[u] := List.getElem?_eq_getElem (by omega)
      have hgA : w[u - 16]? = some w[u - 16] :=
        List.getElem?_eq_getElem (by omega)
      have hgB : w[u - 15]? = some w[u - 15] :=
        List.getElem?_eq_getElem (by omega)
      have hgC : w[u - 7]? = some w[u - 7] :=
        List.getElem?_eq_getElem (by omega)
      have hgD : w[u - 2]? = some w[u - 2] :=
        List.getElem?_eq_getElem (by omega)
      -- One body step is one `schedStep`: the mirror values unfold
      -- to the sigma bodies (`sV4 = shas0`, `sV8 = shas1`).
      have hset : w.set u (sV11 w[u - 16] w[u - 15] w[u - 7] w[u - 2]) =
          schedStep w u := by
        simp [schedStep, sV11, sV10, sV9, sV8, sV7, sV5, sV6, sV4, sV3,
          sV1, sV2, shas0, shas1, hgu, hgA, hgB, hgC, hgD]
      have e1 : 64 - (u + 1) = 64 - u - 1 := by omega
      have e2 : 64 - u = (64 - u - 1) + 1 := by omega
      have hinv' : schedLoop (64 - (u + 1)) (u + 1)
          (w.set u (sV11 w[u - 16] w[u - 15] w[u - 7] w[u - 2])) =
          schedLoop 48 16 w0 := by
        rw [hset, e1, ← schedLoop_succ, ← e2]
        exact hinv
      exact ih (u + 1)
        (w.set u (sV11 w[u - 16] w[u - 15] w[u - 7] w[u - 2]))
        hu' hu16' hw' hinv' (by omega)
    · have hu64 : u = 64 := by omega
      subst hu64
      have hcond := schedCond_eval s 64 w (by decide)
      have hcondF : evalExpr (.ult (.var "u")
            (.lit (.u64 (BitVec.ofNat 64 64)))) (mkSchedEnv s 64 w) =
          .ok (.b false) := by
        simpa using hcond
      have hdone : w = schedLoop 48 16 w0 := hinv
      rw [hdone] at hcondF ⊢
      simp [schedWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
        hcondF]

/-- The add-back loop evaluates to `shaAddBackN st0 v 8` (fuel
    induction mirroring `initWhile_correct`; the counter runs `0 → 8`
    and the invariant counts completed add-backs:
    `shaAddBackN st0 v j = st`). -/
theorem shaAddWhile_correct (F : Nat) (v w : List (BitVec 32)) (j : Nat)
    (st st0 : List (BitVec 32))
    (hj : j ≤ 8) (hst : 8 ≤ st.length) (hvlen : v.length = 8)
    (hinv : shaAddBackN st0 v j = st)
    (hF : 8 - j ≤ F) :
    evalStmtFuel F shaAddWhile (mkShaAddEnv v w j st) =
      .ok (mkShaAddEnv v w 8 (shaAddBackN st0 v 8), .fellThrough) := by
  induction F generalizing j st with
  | zero =>
    have hj8 : j = 8 := by omega
    subst hj8
    have hcond := shaAddCond_eval v w 8 st (by decide)
    have hcondF : evalExpr (.ult (.var "j")
          (.lit (.u64 (BitVec.ofNat 64 8)))) (mkShaAddEnv v w 8 st) =
        .ok (.b false) := by
      simpa using hcond
    have hdone : st = shaAddBackN st0 v 8 := hinv.symm
    rw [hdone] at hcondF ⊢
    simp [shaAddWhile, evalStmtFuel, evalStmtZero, evalStmtZeroHandler,
      evalStmtWith, hcondF]
  | succ F ih =>
    by_cases hlt : j < 8
    · have hj642 : j < 2 ^ 64 := by omega
      have hcond := shaAddCond_eval v w j st hj642
      have hcondT : evalExpr (.ult (.var "j")
            (.lit (.u64 (BitVec.ofNat 64 8)))) (mkShaAddEnv v w j st) =
          .ok (.b true) := by
        simpa [hlt] using hcond
      have hbody := shaAddBody_eval F v w j st hlt hst hvlen hj642
      have hstep : evalStmtFuel (F + 1) shaAddWhile (mkShaAddEnv v w j st)
          = evalStmtFuel F shaAddWhile
            (mkShaAddEnv v w (j + 1) (st.set j (st[j] + v[j]))) := by
        simp [shaAddWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcondT, hbody]
      rw [hstep]
      have hj' : j + 1 ≤ 8 := by omega
      have hst' : 8 ≤ (st.set j (st[j] + v[j])).length := by
        rw [List.length_set]; exact hst
      have hgs : st[j]? = some st[j] := List.getElem?_eq_getElem (by omega)
      have hgv : v[j]? = some v[j] := List.getElem?_eq_getElem (by omega)
      -- The frontier cell is untouched by the completed steps, so the
      -- twin's original-state read is the current-state read.
      have hsame : (shaAddBackN st0 v j)[j]? = st0[j]? :=
        shaAddBackN_get_untouched st0 v j j (by omega)
      rw [hinv] at hsame
      -- One body step is one twin step: the `set` values agree once
      -- the in-range reads resolve (`getD` of `some`).
      have hinv' : shaAddBackN st0 v (j + 1) = st.set j (st[j] + v[j]) := by
        rw [shaAddBackN_succ, hinv, ← hsame, hgs, hgv, Option.getD_some,
          Option.getD_some]
      exact ih (j + 1) (st.set j (st[j] + v[j])) hj' hst' hinv' (by omega)
    · have hj8 : j = 8 := by omega
      subst hj8
      have hcond := shaAddCond_eval v w 8 st (by decide)
      have hcondF : evalExpr (.ult (.var "j")
            (.lit (.u64 (BitVec.ofNat 64 8)))) (mkShaAddEnv v w 8 st) =
          .ok (.b false) := by
        simpa using hcond
      have hdone : st = shaAddBackN st0 v 8 := hinv.symm
      rw [hdone] at hcondF ⊢
      simp [shaAddWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
        hcondF]
