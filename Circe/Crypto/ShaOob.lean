/-
Circe.Crypto.ShaOob — out-of-bounds legs for the K5 SHA-256 block
function (split from `Circe.Crypto.ShaBlock` under the ~2k-line
discipline).

Mirror discipline (K4 `roundFrag_oob` precedent): every loop body
that reads a short list fails loudly with `.error .OOB`, and each
loop errors when run over a short list. The per-value error
propagation reuses K4's generic `evalStmtFuel_arrSet_err` (value
errors abort the store at any fuel); only the missing-read facts
and the single-error `simp only [evalExpr, ...]` closures are
per-path.

Only the init loop needs a general induction (`initWhile_oob`):
a short input (`s.length < 24`) may survive the first iterations
(the body at `t` reads `st[8+t]`, so entry succeeds when
`8 < s.length < 24`) and fail mid-loop. The other loops error on
entry over short lists, since their bodies touch a fixed cell
(`sched`: `w[u-2]` at `u = 16`; `compress`: `v[7]`; `add-back`:
`st[0]`; `vinit`: `st[0]`).
-/
import Circe.Crypto.ShaBlock

/-! ### Block-copy OOB legs -/

/-- One block-copy iteration over a short input errors: the
    `st[8+t]` read misses, so the value errors and the store
    propagates it (the trailing `t++` never runs). -/
theorem initBody_oob (F : Nat) (s : List (BitVec 32)) (t : Nat)
    (w : List (BitVec 32))
    (ht16 : t < 16) (hle : s.length ≤ 8 + t) :
    evalStmtFuel F initBody (mkInitEnv s t w) = .error .OOB := by
  -- The store index is the plain counter; the `8 + t` arithmetic
  -- lives only in the value read.
  have hiv : evalExpr (.var "t") (mkInitEnv s t w) =
      .ok (.u64 (BitVec.ofNat 64 t)) := by
    simp [evalExpr, mkInitEnv_t]
  have htoNat : (BitVec.ofNat 64 (8 + t)).toNat = 8 + t :=
    ofNat64_toNat _ (by omega)
  have hget : s[8 + t]? = none := List.getElem?_eq_none (by omega)
  have hv : evalExpr
      (.idxu "st" (.uadd (.lit (.u64 (BitVec.ofNat 64 8))) (.var "t")))
      (mkInitEnv s t w) = .error .OOB := by
    simp only [evalExpr, mkInitEnv_st, mkInitEnv_t, litVal,
      ofNat64_add 8 t (by omega), htoNat, hget]
  have harr := evalStmtFuel_arrSet_err F "w" _ _ _ _ _ hiv hv
  rw [initBody, evalStmtFuel_seq_err F _ _ _ _ harr]

/-- The block-copy loop over a short input errors (fuel induction
    mirroring `initWhile_correct`: iterations with `8 + t`
    in-bounds step through `initArrSet`, the first iteration with
    `8 + t` out-of-bounds errors via `initBody_oob`; the `t < 16`
    hypothesis rules out the vacuous zero-fuel exit). -/
theorem initWhile_oob (F : Nat) (s : List (BitVec 32)) (t : Nat)
    (w : List (BitVec 32))
    (ht : t < 16) (hshort : s.length < 24) (hw : w.length = 64)
    (hF : 16 - t ≤ F) :
    evalStmtFuel F initWhile (mkInitEnv s t w) = .error .OOB := by
  induction F generalizing t w with
  | zero => exact False.elim (by omega)
  | succ F ih =>
    have ht64 : t < 2 ^ 64 := by omega
    have hcond := initCond_eval s t w ht64
    have hcondT : evalExpr (.ult (.var "t")
          (.lit (.u64 (BitVec.ofNat 64 16)))) (mkInitEnv s t w) =
          .ok (.b true) := by
      simpa [ht] using hcond
    by_cases hle : s.length ≤ 8 + t
    · have hbody := initBody_oob F s t w (by omega) hle
      simp [initWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
        hcondT, hbody]
    · have hlt : 8 + t < s.length := by omega
      have hget : s[8 + t]? = some s[8 + t] :=
        List.getElem?_eq_getElem hlt
      -- In-bounds iteration: assembled manually since
      -- `initBody_eval` needs `24 ≤ s.length`.
      have htoNat : (BitVec.ofNat 64 (8 + t)).toNat = 8 + t :=
        ofNat64_toNat _ (by omega)
      have hv : evalExpr
          (.idxu "st" (.uadd (.lit (.u64 (BitVec.ofNat 64 8))) (.var "t")))
          (mkInitEnv s t w) = .ok (.u32 s[8 + t]) := by
        simp only [evalExpr, mkInitEnv_st, mkInitEnv_t, litVal,
          ofNat64_add 8 t (by omega), htoNat, hget]
      have harr := initArrSet F s t w _ _ (by omega) ht64 hv
      have huaddt : evalExpr
          (.uadd (.var "t") (.lit (.u64 (BitVec.ofNat 64 1))))
          (mkInitEnv s t (w.set t s[8 + t])) =
          .ok (.u64 (BitVec.ofNat 64 (t + 1))) := by
        simp only [evalExpr, mkInitEnv_t, litVal, ofNat64_add_one]
      have hupdt : envUpdate (mkInitEnv s t (w.set t s[8 + t])) "t"
          (.u64 (BitVec.ofNat 64 (t + 1))) =
          some (mkInitEnv s (t + 1) (w.set t s[8 + t])) :=
        initEnv_update_t s t (t + 1) (w.set t s[8 + t])
      have hassign := evalStmtFuel_assign F "t" _ _ _ _ huaddt hupdt
      have hbodyOk : evalStmtFuel F initBody (mkInitEnv s t w) =
          .ok (mkInitEnv s (t + 1) (w.set t s[8 + t]), .fellThrough) := by
        rw [initBody, evalStmtFuel_seq_fallthrough F _ _ _ _ harr, hassign]
      have hstep : evalStmtFuel (F + 1) initWhile (mkInitEnv s t w)
          = evalStmtFuel F initWhile
            (mkInitEnv s (t + 1) (w.set t s[8 + t])) := by
        simp [initWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcondT, hbodyOk]
      rw [hstep]
      have hw' : (w.set t s[8 + t]).length = 64 := by
        rw [List.length_set]; exact hw
      exact ih (t + 1) (w.set t s[8 + t]) (by omega) hw' (by omega)

/-! ### Work-init OOB legs -/

/-- One work-init iteration over an empty input errors: the `st[i]`
    read misses, so the value errors and the store propagates it. -/
theorem vinitBody_oob (F : Nat) (s : List (BitVec 32)) (i : Nat)
    (v w : List (BitVec 32))
    (hi64 : i < 2 ^ 64) (hle : s.length ≤ i) :
    evalStmtFuel F vinitBody (mkVinitEnv s i v w) = .error .OOB := by
  have htoNat : (BitVec.ofNat 64 i).toNat = i := ofNat64_toNat i hi64
  have hiv : evalExpr (.var "i") (mkVinitEnv s i v w) =
      .ok (.u64 (BitVec.ofNat 64 i)) := by
    simp [evalExpr, mkVinitEnv_i]
  have hget : s[i]? = none := List.getElem?_eq_none (by omega)
  have hv : evalExpr (.idxu "st" (.var "i")) (mkVinitEnv s i v w) =
      .error .OOB := by
    simp only [evalExpr, mkVinitEnv_st, mkVinitEnv_i, htoNat, hget]
  have harr := evalStmtFuel_arrSet_err F "v" _ _ _ _ _ hiv hv
  rw [vinitBody, evalStmtFuel_seq_err F _ _ _ _ harr]

/-- The work-init loop over an empty input errors on entry (`i = 0`,
    so the condition holds and the first body runs at fuel `F`). -/
theorem vinitWhile_oob (F : Nat) (s : List (BitVec 32))
    (v w : List (BitVec 32)) (hshort : s.length ≤ 0) :
    evalStmtFuel (F + 1) vinitWhile (mkVinitEnv s 0 v w) =
      .error .OOB := by
  have hcond := vinitCond_eval s 0 v w (by decide)
  have hcondT : evalExpr (.ult (.var "i")
        (.lit (.u64 (BitVec.ofNat 64 8)))) (mkVinitEnv s 0 v w) =
        .ok (.b true) := by
    simpa using hcond
  have hbodyErr := vinitBody_oob F s 0 v w (by decide) hshort
  simp [vinitWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
    hcondT, hbodyErr]

/-! ### Schedule OOB legs -/

/-- Strictness helpers: `uadd`/`bxor`/`bshr`/`rotrE` propagate an
    erroring operand. Stated at variable level on purpose: the
    error fact is about a variable-headed `evalExpr` term, which no
    `evalExpr` equation matches, so `simp only [evalExpr, h]` meets
    no competing unfolding — the same reason K4's `xAt`-leaf error
    propagation goes through, and why chaining error facts about
    explicit constructor-headed subterms does not. -/
theorem uadd_err_left (a b : CExpr) (ρ : Env) (e : Panic)
    (h : evalExpr a ρ = .error e) :
    evalExpr (.uadd a b) ρ = .error e := by
  simp [evalExpr, h]

/-- `uadd` over `u32` oks is the wrapping sum (variable-level,
    hence no competing unfolding). -/
theorem uadd_u32_ok (a b : CExpr) (ρ : Env) (x y : BitVec 32)
    (h1 : evalExpr a ρ = .ok (.u32 x))
    (h2 : evalExpr b ρ = .ok (.u32 y)) :
    evalExpr (.uadd a b) ρ = .ok (.u32 (x + y)) := by
  simp [evalExpr, h1, h2]

/-- `bxor` over `u32` oks is `^^^` (variable-level). -/
theorem bxor_u32_ok (a b : CExpr) (ρ : Env) (x y : BitVec 32)
    (h1 : evalExpr a ρ = .ok (.u32 x))
    (h2 : evalExpr b ρ = .ok (.u32 y)) :
    evalExpr (.bxor a b) ρ = .ok (.u32 (x ^^^ y)) := by
  simp [evalExpr, h1, h2]

/-- `uadd` with an ok `u32` left and an erroring right reports the
    right error (variable-level; this is the sound right-side
    form — a bare error-right fact would be false, since a
    differing left error wins the match). -/
theorem uadd_ok_err_right (a b : CExpr) (ρ : Env) (m : BitVec 32)
    (e : Panic)
    (h1 : evalExpr a ρ = .ok (.u32 m))
    (h2 : evalExpr b ρ = .error e) :
    evalExpr (.uadd a b) ρ = .error e := by
  simp [evalExpr, h1, h2]

theorem bxor_err_left (a b : CExpr) (ρ : Env) (e : Panic)
    (h : evalExpr a ρ = .error e) :
    evalExpr (.bxor a b) ρ = .error e := by
  simp [evalExpr, h]

/-- A `rotrE` over an erroring read errors (the `bor`/`bshr`/`bshl`
    leaves are strict, so the single error propagates without any
    in-bounds facts). -/
theorem rotrE_err (ρ : Env) (X : CExpr) (n : Nat) (e : Panic)
    (h : evalExpr X ρ = .error e) :
    evalExpr (rotrE X n) ρ = .error e := by
  simp [rotrE, evalExpr, h]

/-- One schedule iteration over a short schedule errors: with
    `u - 6 ≤ w.length ≤ u - 2` the `w[u-2]` read misses (so the
    `s1` half errors) while the `s0`-half reads (`u-16`, `u-15`,
    `u-7`) all hit (so the left half of the top `uadd` is ok and
    the `s1` error determines the outcome — an erroring right side
    alone would not suffice, since a differing left error wins the
    match). The store propagates the value error; the trailing
    `u++` never runs. -/
theorem schedBody_oob (F : Nat) (s : List (BitVec 32)) (u : Nat)
    (w : List (BitVec 32))
    (hu16 : 16 ≤ u) (hu64 : u < 2 ^ 64)
    (hlo : u - 6 ≤ w.length) (hhi : w.length ≤ u - 2) :
    evalStmtFuel F schedBody (mkSchedEnv s u w) = .error .OOB := by
  have hiu2 : evalExpr (.usub (.var "u") (.lit (.u64 (BitVec.ofNat 64 2))))
      (mkSchedEnv s u w) = .ok (.u64 (BitVec.ofNat 64 (u - 2))) := by
    simp only [evalExpr, mkSchedEnv_u, litVal, ofNat64_sub u 2 (by omega) hu64]
  have ht2 : (BitVec.ofNat 64 (u - 2)).toNat = u - 2 :=
    ofNat64_toNat _ (by omega)
  have hgD : w[u - 2]? = none := List.getElem?_eq_none (by omega)
  have hD : evalExpr (.idxu "w" (.usub (.var "u")
      (.lit (.u64 (BitVec.ofNat 64 2))))) (mkSchedEnv s u w) =
      .error .OOB := by
    simp only [evalExpr, mkSchedEnv_w, mkSchedEnv_u, litVal,
      ofNat64_sub u 2 (by omega) hu64, ht2, hgD]
  -- The `s0`-half reads all hit under the lower band bound.
  have ht16 : (BitVec.ofNat 64 (u - 16)).toNat = u - 16 :=
    ofNat64_toNat _ (by omega)
  have ht15 : (BitVec.ofNat 64 (u - 15)).toNat = u - 15 :=
    ofNat64_toNat _ (by omega)
  have ht7 : (BitVec.ofNat 64 (u - 7)).toNat = u - 7 :=
    ofNat64_toNat _ (by omega)
  have hgA : w[u - 16]? = some w[u - 16] :=
    List.getElem?_eq_getElem (by omega)
  have hgB : w[u - 15]? = some w[u - 15] :=
    List.getElem?_eq_getElem (by omega)
  have hgC : w[u - 7]? = some w[u - 7] :=
    List.getElem?_eq_getElem (by omega)
  have hA : evalExpr (.idxu "w" (.usub (.var "u")
      (.lit (.u64 (BitVec.ofNat 64 16))))) (mkSchedEnv s u w) =
      .ok (.u32 w[u - 16]) := by
    simp only [evalExpr, mkSchedEnv_w, mkSchedEnv_u, litVal, ofNat64_sub u 16 (by omega) hu64, ht16, hgA]
  have hB : evalExpr (.idxu "w" (.usub (.var "u")
      (.lit (.u64 (BitVec.ofNat 64 15))))) (mkSchedEnv s u w) =
      .ok (.u32 w[u - 15]) := by
    simp only [evalExpr, mkSchedEnv_w, mkSchedEnv_u, litVal, ofNat64_sub u 15 (by omega) hu64, ht15, hgB]
  have hC : evalExpr (.idxu "w" (.usub (.var "u")
      (.lit (.u64 (BitVec.ofNat 64 7))))) (mkSchedEnv s u w) =
      .ok (.u32 w[u - 7]) := by
    simp only [evalExpr, mkSchedEnv_w, mkSchedEnv_u, litVal, ofNat64_sub u 7 (by omega) hu64, ht7, hgC]
  have hr7 : evalExpr (rotrE (.idxu "w" (.usub (.var "u")
      (.lit (.u64 (BitVec.ofNat 64 15))))) 7) (mkSchedEnv s u w) =
      .ok (.u32 (rotrU32 w[u - 15] 7)) :=
    rotrE_eval _ _ _ 7 hB (ofNat32_toNat 7 (by decide))
      (ofNat32_toNat (32 - 7) (by decide)) (by decide) (by decide)
  have hr18 : evalExpr (rotrE (.idxu "w" (.usub (.var "u")
      (.lit (.u64 (BitVec.ofNat 64 15))))) 18) (mkSchedEnv s u w) =
      .ok (.u32 (rotrU32 w[u - 15] 18)) :=
    rotrE_eval _ _ _ 18 hB (ofNat32_toNat 18 (by decide))
      (ofNat32_toNat (32 - 18) (by decide)) (by decide) (by decide)
  have hs3 : evalExpr (.bshr (.idxu "w" (.usub (.var "u")
      (.lit (.u64 (BitVec.ofNat 64 15)))))
      (.lit (.u32 (BitVec.ofNat 32 3)))) (mkSchedEnv s u w) =
      .ok (.u32 (w[u - 15] >>> 3)) := by
    have h := checkedShiftU32_ok w[u - 15] (BitVec.ofNat 32 3) (· >>> ·)
      (by rw [ofNat32_toNat 3 (by decide)]; decide)
    simp only [evalExpr, mkSchedEnv_w, mkSchedEnv_u, litVal, ofNat64_sub u 15 (by omega) hu64, ht15, hgB]
    rw [h]
    exact u32_map_ok _
  have hs0 : evalExpr
      (.bxor
        (.bxor (rotrE (.idxu "w" (.usub (.var "u")
            (.lit (.u64 (BitVec.ofNat 64 15))))) 7)
          (rotrE (.idxu "w" (.usub (.var "u")
            (.lit (.u64 (BitVec.ofNat 64 15))))) 18))
        (.bshr (.idxu "w" (.usub (.var "u")
            (.lit (.u64 (BitVec.ofNat 64 15)))))
          (.lit (.u32 (BitVec.ofNat 32 3)))))
      (mkSchedEnv s u w) = .ok (.u32 _) :=
    bxor_u32_ok _ _ _ _ _ (bxor_u32_ok _ _ _ _ _ hr7 hr18) hs3
  have hMIDok : evalExpr
      (.uadd
        (.uadd (.idxu "w" (.usub (.var "u")
            (.lit (.u64 (BitVec.ofNat 64 16)))))
          (.bxor
            (.bxor (rotrE (.idxu "w" (.usub (.var "u")
                (.lit (.u64 (BitVec.ofNat 64 15))))) 7)
              (rotrE (.idxu "w" (.usub (.var "u")
                (.lit (.u64 (BitVec.ofNat 64 15))))) 18))
            (.bshr (.idxu "w" (.usub (.var "u")
                (.lit (.u64 (BitVec.ofNat 64 15)))))
              (.lit (.u32 (BitVec.ofNat 32 3))))))
        (.idxu "w" (.usub (.var "u")
          (.lit (.u64 (BitVec.ofNat 64 7))))))
      (mkSchedEnv s u w) = .ok (.u32 _) :=
    uadd_u32_ok _ _ _ _ _ (uadd_u32_ok _ _ _ _ _ hA hs0) hC
  -- The `s1` half errors down its left spine (`rotrE` over the
  -- missing read); the `19`-rotate and the shift stay stuck but
  -- harmless, exactly K4's single-error propagation.
  have hS1 : evalExpr
      (.bxor
        (.bxor (rotrE (.idxu "w" (.usub (.var "u")
            (.lit (.u64 (BitVec.ofNat 64 2))))) 17)
          (rotrE (.idxu "w" (.usub (.var "u")
            (.lit (.u64 (BitVec.ofNat 64 2))))) 19))
        (.bshr (.idxu "w" (.usub (.var "u")
            (.lit (.u64 (BitVec.ofNat 64 2)))))
          (.lit (.u32 (BitVec.ofNat 32 10)))))
      (mkSchedEnv s u w) = .error .OOB :=
    bxor_err_left _ _ _ _
      (bxor_err_left _ _ _ _ (rotrE_err _ _ 17 _ hD))
  have hv : evalExpr
      (.uadd
        (.uadd
          (.uadd (.idxu "w" (.usub (.var "u")
              (.lit (.u64 (BitVec.ofNat 64 16)))))
            (.bxor
              (.bxor (rotrE (.idxu "w" (.usub (.var "u")
                  (.lit (.u64 (BitVec.ofNat 64 15))))) 7)
                (rotrE (.idxu "w" (.usub (.var "u")
                  (.lit (.u64 (BitVec.ofNat 64 15))))) 18))
              (.bshr (.idxu "w" (.usub (.var "u")
                  (.lit (.u64 (BitVec.ofNat 64 15)))))
                (.lit (.u32 (BitVec.ofNat 32 3))))))
          (.idxu "w" (.usub (.var "u")
            (.lit (.u64 (BitVec.ofNat 64 7))))))
        (.bxor
          (.bxor (rotrE (.idxu "w" (.usub (.var "u")
              (.lit (.u64 (BitVec.ofNat 64 2))))) 17)
            (rotrE (.idxu "w" (.usub (.var "u")
              (.lit (.u64 (BitVec.ofNat 64 2))))) 19))
          (.bshr (.idxu "w" (.usub (.var "u")
              (.lit (.u64 (BitVec.ofNat 64 2)))))
            (.lit (.u32 (BitVec.ofNat 32 10))))))
      (mkSchedEnv s u w) = .error .OOB :=
    uadd_ok_err_right _ _ _ _ _ hMIDok hS1
  have hiv : evalExpr (.var "u") (mkSchedEnv s u w) =
      .ok (.u64 (BitVec.ofNat 64 u)) := by
    simp [evalExpr, mkSchedEnv_u]
  have harr := evalStmtFuel_arrSet_err F "w" _ _ _ _ _ hiv hv
  rw [schedBody, evalStmtFuel_seq_err F _ _ _ _ harr]

/-- The schedule loop over a short schedule errors on entry
    (`u = 16 < 64`, so the condition holds and the first body runs
    at fuel `F`; `16 - 2 = 14` is the deepest read and `16 - 6 = 10`
    the shallowest hit the band needs). -/
theorem schedWhile_oob (F : Nat) (s : List (BitVec 32))
    (w : List (BitVec 32)) (hlo : 10 ≤ w.length) (hhi : w.length ≤ 14) :
    evalStmtFuel (F + 1) schedWhile (mkSchedEnv s 16 w) =
      .error .OOB := by
  have hcond := schedCond_eval s 16 w (by decide)
  have hcondT : evalExpr (.ult (.var "u")
        (.lit (.u64 (BitVec.ofNat 64 64)))) (mkSchedEnv s 16 w) =
        .ok (.b true) := by
    simpa using hcond
  have hbodyErr := schedBody_oob F s 16 w (by decide) (by decide) hlo hhi
  simp [schedWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
    hcondT, hbodyErr]

/-! ### Compression OOB legs -/

/-- One compression round over short working vars errors: with
    `vv.length < 8` the leftmost `v[7]` read of `t1Expr` misses, so
    the `t1` bind errors and the fragment aborts before any store
    (the single error propagates up the left-nested `uadd` chain;
    the `K`/`w` reads stay stuck but harmless). -/
theorem compressFrag_oob (F : Nat) (s : List (BitVec 32))
    (vv : List (BitVec 32)) (r : Nat) (w : List (BitVec 32))
    (t1 t2 : BitVec 32) (hlt8 : vv.length < 8) :
    evalStmtFuel F compressFrag (mkCompressEnv s vv r w t1 t2) =
      .error .OOB := by
  have htoNat7 : (BitVec.ofNat 64 7).toNat = 7 :=
    ofNat64_toNat 7 (by decide)
  have hget7 : vv[7]? = none := List.getElem?_eq_none (by omega)
  have harr := mkCompressEnv_v s vv r w t1 t2
  have herr7 : evalExpr (.idxu "v" (atU64 7))
      (mkCompressEnv s vv r w t1 t2) = .error .OOB := by
    simp only [atU64, evalExpr, litVal, harr, htoNat7, hget7]
  -- Unfold the temp def (no competing equation matches the bare
  -- constant), then climb the left-nested `uadd` spine by term
  -- application: the missing `v[7]` read sits at the left of the
  -- innermost `uadd`.
  have ht1 : evalExpr t1Expr (mkCompressEnv s vv r w t1 t2) =
      .error .OOB := by
    simp only [t1Expr]
    exact uadd_err_left _ _ _ _ (uadd_err_left _ _ _ _
      (uadd_err_left _ _ _ _ (uadd_err_left _ _ _ _ herr7)))
  have hlet := evalStmtFuel_let_err F "t1" (.u 32) _ _ _ ht1
  rw [compressFrag, evalStmtFuel_seq_err F _ _ _ _ hlet]

/-- One round-loop iteration over short working vars errors in the
    fragment (the trailing `r++` never runs). -/
theorem shaRoundBody_oob (F : Nat) (s : List (BitVec 32))
    (vv : List (BitVec 32)) (r : Nat) (w : List (BitVec 32))
    (t1 t2 : BitVec 32) (hlt8 : vv.length < 8) :
    evalStmtFuel F shaRoundBody (mkCompressEnv s vv r w t1 t2) =
      .error .OOB := by
  have herr := compressFrag_oob F s vv r w t1 t2 hlt8
  rw [shaRoundBody, evalStmtFuel_seq_err F _ _ _ _ herr]

/-- The 64-round loop over short working vars errors on entry
    (`r = 0 < 64`, so the condition holds and the first body runs
    at fuel `F`). -/
theorem compressWhile_oob (F : Nat) (s : List (BitVec 32))
    (vv : List (BitVec 32)) (w : List (BitVec 32)) (t1 t2 : BitVec 32)
    (hlt8 : vv.length < 8) :
    evalStmtFuel (F + 1) compressWhile
      (mkCompressEnv s vv 0 w t1 t2) = .error .OOB := by
  have hcond := compressCond_eval s vv 0 w t1 t2 (by decide)
  have hcondT : evalExpr (.ult (.var "r")
        (.lit (.u64 (BitVec.ofNat 64 64)))) (mkCompressEnv s vv 0 w t1 t2) =
        .ok (.b true) := by
    simpa using hcond
  have hbodyErr := shaRoundBody_oob F s vv 0 w t1 t2 hlt8
  simp [compressWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
    hcondT, hbodyErr]

/-! ### Add-back OOB legs -/

/-- One add-back iteration over a short state errors: the `st[j]`
    read misses, so the value errors and the store propagates it
    (the trailing `j++` never runs). -/
theorem shaAddBody_oob (F : Nat) (v w : List (BitVec 32)) (j : Nat)
    (st : List (BitVec 32))
    (hj64 : j < 2 ^ 64) (hle : st.length ≤ j) :
    evalStmtFuel F shaAddBody (mkShaAddEnv v w j st) = .error .OOB := by
  have htoNat : (BitVec.ofNat 64 j).toNat = j := ofNat64_toNat j hj64
  have hij : evalExpr (.var "j") (mkShaAddEnv v w j st) =
      .ok (.u64 (BitVec.ofNat 64 j)) := by
    simp [evalExpr, mkShaAddEnv_j]
  have hget : st[j]? = none := List.getElem?_eq_none (by omega)
  have herrSt : evalExpr (.idxu "st" (.var "j")) (mkShaAddEnv v w j st) =
      .error .OOB := by
    simp only [evalExpr, mkShaAddEnv_st, mkShaAddEnv_j, htoNat, hget]
  have hv : evalExpr (.uadd (.idxu "st" (.var "j")) (.idxu "v" (.var "j")))
      (mkShaAddEnv v w j st) = .error .OOB :=
    uadd_err_left _ _ _ _ herrSt
  have harr := evalStmtFuel_arrSet_err F "st" _ _ _ _ _ hij hv
  rw [shaAddBody, evalStmtFuel_seq_err F _ _ _ _ harr]

/-- The add-back loop over an empty state errors on entry (`j = 0`,
    so the condition holds and the first body runs at fuel `F`). -/
theorem shaAddWhile_oob (F : Nat) (v w : List (BitVec 32))
    (st : List (BitVec 32)) (hshort : st.length ≤ 0) :
    evalStmtFuel (F + 1) shaAddWhile (mkShaAddEnv v w 0 st) =
      .error .OOB := by
  have hcond := shaAddCond_eval v w 0 st (by decide)
  have hcondT : evalExpr (.ult (.var "j")
        (.lit (.u64 (BitVec.ofNat 64 8)))) (mkShaAddEnv v w 0 st) =
        .ok (.b true) := by
    simpa using hcond
  have hbodyErr := shaAddBody_oob F v w 0 st (by decide) hshort
  simp [shaAddWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
    hcondT, hbodyErr]
