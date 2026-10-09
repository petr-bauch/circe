/-
Circe.Emit.Vec — `vec_alloc`: uniquely-owned heap block (fill + sum loops,
whole-function correctness).
-/
import Circe.Emit.Fragment
import Circe.Emit.VecFwd

/-! ## `vec_alloc`: uniquely-owned heap block (Phase 7, u32-only) -/

/-- Fill body: `v[i] = i; i = i + 1` (the value written is the index).
    The `1` is `1#32` (`ofNat`-headed, cf. `sumBody`). -/
def vecFillBody : CStmt :=
  .seq (.vset "v" (.var "i") (.var "i"))
       (.assign "i" (.uadd (.var "i") (.lit (.u32 1#32))))

/-- Fill loop: `while (i < n) { ... }`. -/
def vecFillWhile : CStmt :=
  .while_ (.ult (.var "i") (.var "n")) vecFillBody

/-- Sum body: `s = s + v[j]; j = j + 1`. -/
def vecSumBody : CStmt :=
  .seq (.assign "s" (.uadd (.var "s") (.vget "v" (.var "j"))))
       (.assign "j" (.uadd (.var "j") (.lit (.u32 1#32))))

/-- Sum loop: `while (j < n) { ... }`. -/
def vecSumWhile : CStmt :=
  .while_ (.ult (.var "j") (.var "n")) vecSumBody

/-- Canonical CoreIR for `tests/c/vec_alloc.c`: allocate a zeroed `u32`
    block of `n` words (`malloc`), fill it with indices, sum it, `free`
    it, return the sum. `n` is the length (`u32`: C `size_t` must fit
    32 bits, like `sum_array`); the block lives in `v` as a `vecVal`. -/
def vecFunc : Func :=
  ⟨"vec_alloc",
   [{ name := "n", ty := .u 32, role := .owned }],
   .u 32,
   .seq (.let_ "v" .vecBlock (.vnew (.var "n")))
   (.seq (.let_ "i" (.u 32) (.lit (.u32 0)))
   (.seq (.let_ "s" (.u 32) (.lit (.u32 0)))
   (.seq (.let_ "j" (.u 32) (.lit (.u32 0)))
   (.seq vecFillWhile
   (.seq vecSumWhile
   (.seq (.vfree "v")
         (.return_ (.var "s"))))))))⟩


/-- Value-level forward function for `vec_alloc` (cf. rendered
    `vec_alloc_fwd`): the pure heap program from `Circe.Base`. -/
def vecFwd (n : BitVec 32) : Result Value :=
  .u32 <$> vecFillSumU32 n.toNat



/-! ### Heap loop environments -/

/-- Heap environments: block plus bound, both indices, accumulator.
    All four lets are bound before the fill loop, so one shape threads
    through both loops (`s`/`j` sit unused during fill). -/
def mkVecEnv (blk : Vec32) (nv iv sv jv : BitVec 32) : Env :=
  [("j", .u32 jv), ("s", .u32 sv), ("i", .u32 iv),
   ("v", .vecVal blk), ("n", .u32 nv)]

theorem mkVecEnv_j (blk : Vec32) (nv iv sv jv : BitVec 32) :
    envLookup (mkVecEnv blk nv iv sv jv) "j" = some (.u32 jv) := by
  simp [mkVecEnv, envLookup]

theorem mkVecEnv_s (blk : Vec32) (nv iv sv jv : BitVec 32) :
    envLookup (mkVecEnv blk nv iv sv jv) "s" = some (.u32 sv) := by
  simp [mkVecEnv, envLookup, show ("s" : String) ≠ "j" by decide]

theorem mkVecEnv_i (blk : Vec32) (nv iv sv jv : BitVec 32) :
    envLookup (mkVecEnv blk nv iv sv jv) "i" = some (.u32 iv) := by
  simp [mkVecEnv, envLookup, show ("i" : String) ≠ "j" by decide,
    show ("i" : String) ≠ "s" by decide]

theorem mkVecEnv_v (blk : Vec32) (nv iv sv jv : BitVec 32) :
    envLookup (mkVecEnv blk nv iv sv jv) "v" = some (.vecVal blk) := by
  simp [mkVecEnv, envLookup, show ("v" : String) ≠ "j" by decide,
    show ("v" : String) ≠ "s" by decide,
    show ("v" : String) ≠ "i" by decide]

theorem mkVecEnv_n (blk : Vec32) (nv iv sv jv : BitVec 32) :
    envLookup (mkVecEnv blk nv iv sv jv) "n" = some (.u32 nv) := by
  simp [mkVecEnv, envLookup, show ("n" : String) ≠ "j" by decide,
    show ("n" : String) ≠ "s" by decide,
    show ("n" : String) ≠ "i" by decide,
    show ("n" : String) ≠ "v" by decide]

/-- Updating `v` in a heap env stays a heap env. -/
theorem vecEnv_update_v (blk : Vec32) (nv iv sv jv : BitVec 32)
    (blk' : Vec32) :
    envUpdate (mkVecEnv blk nv iv sv jv) "v" (.vecVal blk') =
      some (mkVecEnv blk' nv iv sv jv) := by
  simp [mkVecEnv, envUpdate, show ("v" : String) ≠ "j" by decide,
    show ("v" : String) ≠ "s" by decide,
    show ("v" : String) ≠ "i" by decide]

/-- Updating `i` in a heap env stays a heap env. -/
theorem vecEnv_update_i (blk : Vec32) (nv iv iv' sv jv : BitVec 32) :
    envUpdate (mkVecEnv blk nv iv sv jv) "i" (.u32 iv') =
      some (mkVecEnv blk nv iv' sv jv) := by
  simp [mkVecEnv, envUpdate, show ("i" : String) ≠ "j" by decide,
    show ("i" : String) ≠ "s" by decide]

/-- Updating `s` in a heap env stays a heap env. -/
theorem vecEnv_update_s (blk : Vec32) (nv iv sv sv' jv : BitVec 32) :
    envUpdate (mkVecEnv blk nv iv sv jv) "s" (.u32 sv') =
      some (mkVecEnv blk nv iv sv' jv) := by
  simp [mkVecEnv, envUpdate, show ("s" : String) ≠ "j" by decide]

/-- Updating `j` in a heap env stays a heap env. -/
theorem vecEnv_update_j (blk : Vec32) (nv iv sv jv jv' : BitVec 32) :
    envUpdate (mkVecEnv blk nv iv sv jv) "j" (.u32 jv') =
      some (mkVecEnv blk nv iv sv jv') := by
  simp [mkVecEnv, envUpdate]

/-- The fill-loop condition reads the index against the bound. -/
theorem vecFillCond_eval (blk : Vec32) (nv : BitVec 32) (k : Nat)
    (sv jv : BitVec 32) (h : k < 2 ^ 32) :
    evalExpr (.ult (.var "i") (.var "n"))
        (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkVecEnv_i blk nv (BitVec.ofNat 32 k) sv jv
  have hn := mkVecEnv_n blk nv (BitVec.ofNat 32 k) sv jv
  simp [evalExpr, hi, hn, ofNat32_ult k nv h]

/-- The sum-loop condition reads the index against the bound. -/
theorem vecSumCond_eval (blk : Vec32) (nv iv sv : BitVec 32) (k : Nat)
    (h : k < 2 ^ 32) :
    evalExpr (.ult (.var "j") (.var "n"))
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) =
      .ok (.b (decide (k < nv.toNat))) := by
  have hj := mkVecEnv_j blk nv iv sv (BitVec.ofNat 32 k)
  have hn := mkVecEnv_n blk nv iv sv (BitVec.ofNat 32 k)
  simp [evalExpr, hj, hn, ofNat32_ult k nv h]

/-- One fill step stores the index and advances (any fuel: loop-free). -/
theorem vecFillBody_eval (F : Nat) (blk : Vec32) (nv : BitVec 32)
    (k : Nat) (sv jv : BitVec 32) (blkMid : Vec32)
    (_hklen : k < blk.val.length) (hk32 : k < 2 ^ 32)
    (_hlive : blk.freed = false)
    (hset : vecSet blk k (BitVec.ofNat 32 k) = .ok blkMid) :
    evalStmtFuel F vecFillBody
        (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) =
      .ok (mkVecEnv blkMid nv (BitVec.ofNat 32 (k + 1)) sv jv,
        .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hi : evalExpr (.var "i")
        (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) =
        .ok (.u32 (BitVec.ofNat 32 k)) :=
    evalExpr_var_hit _ _ _
      (mkVecEnv_i blk nv (BitVec.ofNat 32 k) sv jv)
  have harr := mkVecEnv_v blk nv (BitVec.ofNat 32 k) sv jv
  have hset' : vecSet blk (BitVec.ofNat 32 k).toNat (BitVec.ofNat 32 k) =
      .ok blkMid := by rw [hkk]; exact hset
  have up1 := vecEnv_update_v blk nv (BitVec.ofNat 32 k) sv jv blkMid
  have hi2 : evalExpr (.uadd (.var "i") (.lit (.u32 1#32)))
        (mkVecEnv blkMid nv (BitVec.ofNat 32 k) sv jv) =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVecEnv_i blkMid nv (BitVec.ofNat 32 k) sv jv
    simp only [evalExpr, litVal, h1, ofNat32_add_one]
  have up2 := vecEnv_update_i blkMid nv (BitVec.ofNat 32 k)
    (BitVec.ofNat 32 (k + 1)) sv jv
  -- Feed primitive facts (never intermediate `evalStmtFuel` facts: after
  -- unfolding, only syntactically-matching rules fire). `simp only`
  -- (unlike full `simp`) leaves `(ofNat 32 k).toNat` alone, so `hset'`
  -- fires as-is.
  cases F <;>
    simp only [vecFillBody, evalStmtFuel, evalStmtZero, evalStmtWith, hi, harr,
      hset', up1, hi2, up2]

/-- One sum step accumulates the block element and advances (any fuel). -/
theorem vecSumBody_eval (F : Nat) (blk : Vec32) (nv iv sv : BitVec 32)
    (k : Nat) (hk32 : k < 2 ^ 32)
    (hget : vecGet blk k = .ok (BitVec.ofNat 32 k)) :
    evalStmtFuel F vecSumBody
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) =
      .ok (mkVecEnv blk nv iv (sv + BitVec.ofNat 32 k)
        (BitVec.ofNat 32 (k + 1)), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hj := mkVecEnv_j blk nv iv sv (BitVec.ofNat 32 k)
  have hs0 := mkVecEnv_s blk nv iv sv (BitVec.ofNat 32 k)
  have harr := mkVecEnv_v blk nv iv sv (BitVec.ofNat 32 k)
  have hget' : vecGet blk (BitVec.ofNat 32 k).toNat =
      .ok (BitVec.ofNat 32 k) := by rw [hkk]; exact hget
  have hg : evalExpr (.vget "v" (.var "j"))
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) =
        .ok (.u32 (BitVec.ofNat 32 k)) := by
    simp only [evalExpr, hj, harr, hget']
  have hs : evalExpr (.uadd (.var "s") (.vget "v" (.var "j")))
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) =
        .ok (.u32 (sv + BitVec.ofNat 32 k)) := by
    simp only [evalExpr, hs0, hj, harr, hget']
  have hj2 : evalExpr (.uadd (.var "j") (.lit (.u32 1#32)))
        (mkVecEnv blk nv iv (sv + BitVec.ofNat 32 k) (BitVec.ofNat 32 k)) =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVecEnv_j blk nv iv (sv + BitVec.ofNat 32 k)
      (BitVec.ofNat 32 k)
    simp only [evalExpr, litVal, h1, ofNat32_add_one]
  have up1 := vecEnv_update_s blk nv iv sv (sv + BitVec.ofNat 32 k)
    (BitVec.ofNat 32 k)
  have up2 := vecEnv_update_j blk nv iv (sv + BitVec.ofNat 32 k)
    (BitVec.ofNat 32 k) (BitVec.ofNat 32 (k + 1))
  -- Feed primitive facts (never intermediate `evalStmtFuel` facts: after
  -- unfolding, only syntactically-matching rules fire). `hs`/`hg` are
  -- `evalExpr`-headed (no `evalExpr` unfolding in the set), so they fire
  -- as-is; `hj`/`harr`/`hget'` discharge the inner `vget` matches.
  cases F <;>
    simp only [vecSumBody, evalStmtFuel, evalStmtZero, evalStmtWith, hs, hj2,
      up1, up2]

/-! ### Heap loop correctness (fuel-generalized) -/

/-- Fill-loop correctness: the eval loop runs the `Base` fill to completion.
    The `Base` program (`hfill`) is both spec and witness: induction follows
    its unfolding, like `sumWhile_correct`. -/
theorem vecFillWhile_correct (blk : Vec32) (nv : BitVec 32)
    (F k : Nat) (sv jv : BitVec 32) (blkOut : Vec32)
    (hk : k ≤ nv.toNat)
    (hlen : blk.val.length = nv.toNat)
    (hlive : blk.freed = false)
    (hn32 : nv.toNat < 2 ^ 32)
    (hfill : vecFillLoopAux blk k (nv.toNat - k) = .ok blkOut)
    (hF : nv.toNat - k ≤ F) :
    evalStmtFuel F vecFillWhile
        (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) =
      .ok (mkVecEnv blkOut nv (BitVec.ofNat 32 nv.toNat) sv jv,
        .fellThrough) := by
  induction F generalizing k blk blkOut with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    -- `subst` creates `ofNat 32 nv.toNat`; `simp only` (unlike full `simp`)
    -- leaves it alone, so the cond fact stays in `ofNat` form and `rw`
    -- fires syntactically (cf. probe6).
    have hcond : evalExpr (.ult (.var "i") (.var "n"))
        (mkVecEnv blk nv (BitVec.ofNat 32 nv.toNat) sv jv) =
        .ok (.b false) := by
      have hc := vecFillCond_eval blk nv nv.toNat sv jv hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hfill
    simp only [vecFillLoopAux] at hfill
    cases hfill
    simp only [vecFillWhile, evalStmtFuel, evalStmtZero, evalStmtZeroHandler,
      evalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hklen : k < blk.val.length := by omega
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) =
          .ok (.b true) := by
        simpa [hlt] using (vecFillCond_eval blk nv k sv jv hk32)
      have hset : vecSet blk k (BitVec.ofNat 32 k) =
          .ok ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ :=
        vecSet_ok blk k _ hlive hklen
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hfill
      simp only [vecFillLoopAux, hset] at hfill
      -- hfill : Aux ⟨set ..⟩ (k+1) (n-(k+1)) = ok blkOut
      have hbody := vecFillBody_eval F blk nv k sv jv
        ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩
        hklen hk32 hlive hset
      have hstep : evalStmtFuel (F + 1) vecFillWhile
            (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv)
          = evalStmtFuel F vecFillWhile
            (mkVecEnv ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ nv
              (BitVec.ofNat 32 (k + 1)) sv jv) := by
        simp [vecFillWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond, hbody]
      rw [hstep]
      have hlenMid : (⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).val.length
          = nv.toNat := by
        show (blk.val.set k (BitVec.ofNat 32 k)).length = nv.toNat
        rw [List.length_set]
        omega
      have hliveMid : (⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).freed
          = false := rfl
      exact ih ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ (k + 1) blkOut
        (by omega) hlenMid hliveMid hfill (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkVecEnv blk nv (BitVec.ofNat 32 nv.toNat) sv jv) =
          .ok (.b false) := by
        have hc := vecFillCond_eval blk nv nv.toNat sv jv hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hfill
      simp only [vecFillLoopAux] at hfill
      cases hfill
      simp only [vecFillWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith]
      rw [hcond]

/-- Sum-loop correctness: the eval loop runs the `Base` sum to completion. -/
theorem vecSumWhile_correct (blk : Vec32) (nv : BitVec 32)
    (F k : Nat) (iv sv : BitVec 32) (sout : BitVec 32)
    (hk : k ≤ nv.toNat)
    (hget : ∀ j, k ≤ j → j < nv.toNat →
      vecGet blk j = .ok (BitVec.ofNat 32 j))
    (hn32 : nv.toNat < 2 ^ 32)
    (hsum : vecSumLoopAux blk k (nv.toNat - k) sv = .ok sout)
    (hF : nv.toNat - k ≤ F) :
    evalStmtFuel F vecSumWhile
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) =
      .ok (mkVecEnv blk nv iv sout (BitVec.ofNat 32 nv.toNat),
        .fellThrough) := by
  induction F generalizing k sv sout with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : evalExpr (.ult (.var "j") (.var "n"))
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 nv.toNat)) =
        .ok (.b false) := by
      have hc := vecSumCond_eval blk nv iv sv nv.toNat hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hsum
    simp only [vecSumLoopAux] at hsum
    cases hsum
    simp only [vecSumWhile, evalStmtFuel, evalStmtZero, evalStmtZeroHandler,
      evalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hcond : evalExpr (.ult (.var "j") (.var "n"))
          (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) =
          .ok (.b true) := by
        simpa [hlt] using (vecSumCond_eval blk nv iv sv k hk32)
      have hgetk : vecGet blk k = .ok (BitVec.ofNat 32 k) :=
        hget k (Nat.le_refl _) hlt
      have hbody := vecSumBody_eval F blk nv iv sv k hk32 hgetk
      have hstep : evalStmtFuel (F + 1) vecSumWhile
            (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k))
          = evalStmtFuel F vecSumWhile
            (mkVecEnv blk nv iv (sv + BitVec.ofNat 32 k)
              (BitVec.ofNat 32 (k + 1))) := by
        simp [vecSumWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond, hbody]
      rw [hstep]
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hsum
      simp only [vecSumLoopAux, hgetk] at hsum
      exact ih (k + 1) (sv + BitVec.ofNat 32 k) sout (by omega)
        (by intro j hjlo hjhi; exact hget j (by omega) hjhi) hsum (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "j") (.var "n"))
          (mkVecEnv blk nv iv sv (BitVec.ofNat 32 nv.toNat)) =
          .ok (.b false) := by
        have hc := vecSumCond_eval blk nv iv sv nv.toNat hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hsum
      simp only [vecSumLoopAux] at hsum
      cases hsum
      simp only [vecSumWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith]
      rw [hcond]

/-! ### Whole-function correctness (fuel-generalized, then instantiated) -/

/-- `emit_correct` for `vec_alloc`, at any fuel covering `n`. -/
theorem evalFuncFuel_vec (F : Nat) (nv : BitVec 32)
    (hn : nv.toNat ≤ F) (hn32 : nv.toNat < 2 ^ 32) :
    evalFuncFuel F vecFunc [.u32 nv] =
      .ok (.u32 (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
        nv.toNat)) := by
  have hfresh : (⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ : Vec32).val.length =
      0 + nv.toNat := by simp
  obtain ⟨blkOut, hfill0⟩ := vecFillLoopAux_fresh_ok
    (List.replicate nv.toNat (BitVec.ofNat 32 0)) 0 nv.toNat (by simp)
  have hliveOut : blkOut.freed = false :=
    vecFillLoopAux_live _ _ _ _ rfl hfill0
  have hgetOut : ∀ j, 0 ≤ j → j < nv.toNat →
      vecGet blkOut j = .ok (BitVec.ofNat 32 j) := by
    intro j hjlo hjhi
    have hjhi' : j < 0 + nv.toNat := by omega
    exact vecFillLoopAux_get _ 0 nv.toNat _ rfl hfresh hfill0 j hjlo hjhi'
  have hsum0 := vecSumLoopAux_correct blkOut 0 nv.toNat 0 (by
    intro j hjlo hjhi
    exact hgetOut j hjlo (by omega))
  have hrange : List.range' 0 nv.toNat = List.range nv.toNat := by
    simp [List.range_eq_range']
  rw [hrange] at hsum0
  have h0 : (0 : BitVec 32) + prefixSumU32 ((List.range nv.toNat).map
      (BitVec.ofNat 32)) nv.toNat
      = prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat :=
    BitVec.zero_add _
  rw [h0] at hsum0
  have hfree0 : vecFree blkOut = .ok ⟨blkOut.val, true⟩ :=
    vecFree_ok blkOut hliveOut
  -- The four lets build the heap env (stated `ofNat`-headed: simp's
  -- simprocs normalize `0` to `0#32`).
  have henv : [("j", .u32 (BitVec.ofNat 32 0)),
        ("s", .u32 (BitVec.ofNat 32 0)),
        ("i", .u32 (BitVec.ofNat 32 0)),
        ("v", .vecVal ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩),
        ("n", .u32 nv)]
      = mkVecEnv ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
        (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) := rfl
  have hn0 : envLookup [("n", .u32 nv)] "n" = some (.u32 nv) := rfl
  -- Loop haves match simp's unfolded handler forms (cf. `evalFuncFuel_sum`).
  cases F with
  | zero =>
    have hF0 : nv.toNat - 0 ≤ 0 := by cir_fuel
    have hloopF0 : evalStmtWith evalStmtZeroHandler
          vecFillWhile
          (mkVecEnv ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
        = .ok (mkVecEnv blkOut nv (BitVec.ofNat 32 nv.toNat)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0), .fellThrough) :=
      vecFillWhile_correct _ _ 0 0 _ _ blkOut (Nat.zero_le _)
        (by simp) rfl hn32 hfill0 hF0
    have hloopS0 : evalStmtWith evalStmtZeroHandler
          vecSumWhile
          (mkVecEnv blkOut nv nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
        = .ok (mkVecEnv blkOut nv nv
            (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
              nv.toNat)
            (BitVec.ofNat 32 nv.toNat), .fellThrough) :=
      vecSumWhile_correct blkOut nv 0 0 nv _ _ (Nat.zero_le _)
        (by intro j hjlo hjhi; exact hgetOut j hjlo hjhi) hn32 hsum0 hF0
    have huv := vecEnv_update_v blkOut nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      nv ⟨blkOut.val, true⟩
    have harv := mkVecEnv_v blkOut nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      nv
    have hars := mkVecEnv_s ⟨blkOut.val, true⟩ nv
      nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      nv
    simp [evalFuncFuel, vecFunc, bindArgs, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, litVal, envExtend, hn0, vecNew, henv,
      hloopF0, hloopS0, hfree0, huv, harv, hars]
  | succ F =>
    have hFS : nv.toNat - 0 ≤ F + 1 := by cir_fuel
    have hloopFS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          vecFillWhile
          (mkVecEnv ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
        = .ok (mkVecEnv blkOut nv (BitVec.ofNat 32 nv.toNat)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0), .fellThrough) :=
      vecFillWhile_correct _ _ (F + 1) 0 _ _ blkOut (Nat.zero_le _)
        (by simp) rfl hn32 hfill0 hFS
    have hloopSS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          vecSumWhile
          (mkVecEnv blkOut nv nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
        = .ok (mkVecEnv blkOut nv nv
            (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
              nv.toNat)
            (BitVec.ofNat 32 nv.toNat), .fellThrough) :=
      vecSumWhile_correct blkOut nv (F + 1) 0 nv _ _ (Nat.zero_le _)
        (by intro j hjlo hjhi; exact hgetOut j hjlo hjhi) hn32 hsum0 hFS
    have huv := vecEnv_update_v blkOut nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      nv ⟨blkOut.val, true⟩
    have harv := mkVecEnv_v blkOut nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      nv
    have hars := mkVecEnv_s ⟨blkOut.val, true⟩ nv
      nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      nv
    simp [evalFuncFuel, vecFunc, bindArgs, evalStmtFuel, evalStmtWith,
      evalExpr, litVal, envExtend, hn0, vecNew, henv, hloopFS,
      hloopSS, hfree0, huv, harv, hars]

/-- `emit_correct` for `vec_alloc` at the default fuel. -/
theorem emit_correct_vec (nv : BitVec 32)
    (hfuel : nv.toNat ≤ EVAL_FUEL) :
    evalFunc vecFunc [.u32 nv] = vecFwd nv := by
  have h32 : nv.toNat < 2 ^ 32 := word32_lt_two32_of_fuel _ hfuel
  have h := evalFuncFuel_vec EVAL_FUEL nv hfuel h32
  have hc := vecFillSumU32_correct nv.toNat
  simp only [evalFunc, vecFwd, h, hc, u32_map_ok]
