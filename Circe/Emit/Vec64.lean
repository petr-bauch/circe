/-
Circe.Emit.Vec64 — `vec_alloc_u64`: uniquely-owned `u64` heap block
(monomorphized mirror of `Vec.lean`: fill + sum loops, whole-function
correctness).
-/
import Circe.Emit.Fragment

/-! ## `vec_alloc_u64`: uniquely-owned heap block (M1b, u64-only) -/

/-- Fill body: `v[i] = i; i = i + 1` (the value written is the index).
    The `1` is `1#64` (`ofNat`-headed, cf. `sumBody`). -/
def vec64FillBody : CStmt :=
  .seq (.vset "v" (.var "i") (.var "i"))
       (.assign "i" (.uadd (.var "i") (.lit (.u64 1#64))))

/-- Fill loop: `while (i < n) { ... }`. -/
def vec64FillWhile : CStmt :=
  .while_ (.ult (.var "i") (.var "n")) vec64FillBody

/-- Sum body: `s = s + v[j]; j = j + 1`. -/
def vec64SumBody : CStmt :=
  .seq (.assign "s" (.uadd (.var "s") (.vget "v" (.var "j"))))
       (.assign "j" (.uadd (.var "j") (.lit (.u64 1#64))))

/-- Sum loop: `while (j < n) { ... }`. -/
def vec64SumWhile : CStmt :=
  .while_ (.ult (.var "j") (.var "n")) vec64SumBody

/-- Canonical CoreIR for `tests/c/vec_alloc_u64.c`: allocate a zeroed `u64`
    block of `n` words (`malloc`), fill it with indices, sum it, `free`
    it, return the sum. `n` is the length (`u64`: C `size_t` is 64 bits);
    the block lives in `v` as a `vecVal64`. -/
def vec64Func : Func :=
  ⟨"vec_alloc_u64",
   [{ name := "n", ty := .u 64, role := .owned }],
   .u 64,
   .seq (.let_ "v" .vecBlock (.vnew (.var "n")))
   (.seq (.let_ "i" (.u 64) (.lit (.u64 0)))
   (.seq (.let_ "s" (.u 64) (.lit (.u64 0)))
   (.seq (.let_ "j" (.u 64) (.lit (.u64 0)))
   (.seq vec64FillWhile
   (.seq vec64SumWhile
   (.seq (.vfree "v")
         (.return_ (.var "s"))))))))⟩


/-- Value-level forward function for `vec_alloc_u64` (cf. rendered
    `vec_alloc_u64_fwd`): the pure heap program from `Circe.Base`. -/
def vec64Fwd (n : BitVec 64) : Result Value :=
  .u64 <$> vecFillSumU64 n.toNat



/-! ### Heap loop environments -/

/-- Heap environments: block plus bound, both indices, accumulator.
    All four lets are bound before the fill loop, so one shape threads
    through both loops (`s`/`j` sit unused during fill). -/
def mkVec64Env (blk : Vec64) (nv iv sv jv : BitVec 64) : Env :=
  [("j", .u64 jv), ("s", .u64 sv), ("i", .u64 iv),
   ("v", .vecVal64 blk), ("n", .u64 nv)]

theorem mkVec64Env_j (blk : Vec64) (nv iv sv jv : BitVec 64) :
    envLookup (mkVec64Env blk nv iv sv jv) "j" = some (.u64 jv) := by
  simp [mkVec64Env, envLookup]

theorem mkVec64Env_s (blk : Vec64) (nv iv sv jv : BitVec 64) :
    envLookup (mkVec64Env blk nv iv sv jv) "s" = some (.u64 sv) := by
  simp [mkVec64Env, envLookup, show ("s" : String) ≠ "j" by decide]

theorem mkVec64Env_i (blk : Vec64) (nv iv sv jv : BitVec 64) :
    envLookup (mkVec64Env blk nv iv sv jv) "i" = some (.u64 iv) := by
  simp [mkVec64Env, envLookup, show ("i" : String) ≠ "j" by decide,
    show ("i" : String) ≠ "s" by decide]

theorem mkVec64Env_v (blk : Vec64) (nv iv sv jv : BitVec 64) :
    envLookup (mkVec64Env blk nv iv sv jv) "v" = some (.vecVal64 blk) := by
  simp [mkVec64Env, envLookup, show ("v" : String) ≠ "j" by decide,
    show ("v" : String) ≠ "s" by decide,
    show ("v" : String) ≠ "i" by decide]

theorem mkVec64Env_n (blk : Vec64) (nv iv sv jv : BitVec 64) :
    envLookup (mkVec64Env blk nv iv sv jv) "n" = some (.u64 nv) := by
  simp [mkVec64Env, envLookup, show ("n" : String) ≠ "j" by decide,
    show ("n" : String) ≠ "s" by decide,
    show ("n" : String) ≠ "i" by decide,
    show ("n" : String) ≠ "v" by decide]

/-- Updating `v` in a heap env stays a heap env. -/
theorem vec64Env_update_v (blk : Vec64) (nv iv sv jv : BitVec 64)
    (blk' : Vec64) :
    envUpdate (mkVec64Env blk nv iv sv jv) "v" (.vecVal64 blk') =
      some (mkVec64Env blk' nv iv sv jv) := by
  simp [mkVec64Env, envUpdate, show ("v" : String) ≠ "j" by decide,
    show ("v" : String) ≠ "s" by decide,
    show ("v" : String) ≠ "i" by decide]

/-- Updating `i` in a heap env stays a heap env. -/
theorem vec64Env_update_i (blk : Vec64) (nv iv iv' sv jv : BitVec 64) :
    envUpdate (mkVec64Env blk nv iv sv jv) "i" (.u64 iv') =
      some (mkVec64Env blk nv iv' sv jv) := by
  simp [mkVec64Env, envUpdate, show ("i" : String) ≠ "j" by decide,
    show ("i" : String) ≠ "s" by decide]

/-- Updating `s` in a heap env stays a heap env. -/
theorem vec64Env_update_s (blk : Vec64) (nv iv sv sv' jv : BitVec 64) :
    envUpdate (mkVec64Env blk nv iv sv jv) "s" (.u64 sv') =
      some (mkVec64Env blk nv iv sv' jv) := by
  simp [mkVec64Env, envUpdate, show ("s" : String) ≠ "j" by decide]

/-- Updating `j` in a heap env stays a heap env. -/
theorem vec64Env_update_j (blk : Vec64) (nv iv sv jv jv' : BitVec 64) :
    envUpdate (mkVec64Env blk nv iv sv jv) "j" (.u64 jv') =
      some (mkVec64Env blk nv iv sv jv') := by
  simp [mkVec64Env, envUpdate]

/-- The fill-loop condition reads the index against the bound. -/
theorem vec64FillCond_eval (blk : Vec64) (nv : BitVec 64) (k : Nat)
    (sv jv : BitVec 64) (h : k < 2 ^ 64) :
    evalExpr (.ult (.var "i") (.var "n"))
        (mkVec64Env blk nv (BitVec.ofNat 64 k) sv jv) =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkVec64Env_i blk nv (BitVec.ofNat 64 k) sv jv
  have hn := mkVec64Env_n blk nv (BitVec.ofNat 64 k) sv jv
  simp [evalExpr, hi, hn, ofNat64_ult k nv h]

/-- The sum-loop condition reads the index against the bound. -/
theorem vec64SumCond_eval (blk : Vec64) (nv iv sv : BitVec 64) (k : Nat)
    (h : k < 2 ^ 64) :
    evalExpr (.ult (.var "j") (.var "n"))
        (mkVec64Env blk nv iv sv (BitVec.ofNat 64 k)) =
      .ok (.b (decide (k < nv.toNat))) := by
  have hj := mkVec64Env_j blk nv iv sv (BitVec.ofNat 64 k)
  have hn := mkVec64Env_n blk nv iv sv (BitVec.ofNat 64 k)
  simp [evalExpr, hj, hn, ofNat64_ult k nv h]

/-- One fill step stores the index and advances (any fuel: loop-free). -/
theorem vec64FillBody_eval (F : Nat) (blk : Vec64) (nv : BitVec 64)
    (k : Nat) (sv jv : BitVec 64) (blkMid : Vec64)
    (_hklen : k < blk.val.length) (hk32 : k < 2 ^ 64)
    (_hlive : blk.freed = false)
    (hset : vecSet64 blk k (BitVec.ofNat 64 k) = .ok blkMid) :
    evalStmtFuel F vec64FillBody
        (mkVec64Env blk nv (BitVec.ofNat 64 k) sv jv) =
      .ok (mkVec64Env blkMid nv (BitVec.ofNat 64 (k + 1)) sv jv,
        .fellThrough) := by
  have hkk : (BitVec.ofNat 64 k).toNat = k := ofNat64_toNat k hk32
  have hi : evalExpr (.var "i")
        (mkVec64Env blk nv (BitVec.ofNat 64 k) sv jv) =
        .ok (.u64 (BitVec.ofNat 64 k)) :=
    evalExpr_var_hit _ _ _
      (mkVec64Env_i blk nv (BitVec.ofNat 64 k) sv jv)
  have harr := mkVec64Env_v blk nv (BitVec.ofNat 64 k) sv jv
  have hset' : vecSet64 blk (BitVec.ofNat 64 k).toNat (BitVec.ofNat 64 k) =
      .ok blkMid := by rw [hkk]; exact hset
  have up1 := vec64Env_update_v blk nv (BitVec.ofNat 64 k) sv jv blkMid
  have hi2 : evalExpr (.uadd (.var "i") (.lit (.u64 1#64)))
        (mkVec64Env blkMid nv (BitVec.ofNat 64 k) sv jv) =
        .ok (.u64 (BitVec.ofNat 64 (k + 1))) := by
    have h1 := mkVec64Env_i blkMid nv (BitVec.ofNat 64 k) sv jv
    simp only [evalExpr, litVal, h1, ofNat64_add_one]
  have up2 := vec64Env_update_i blkMid nv (BitVec.ofNat 64 k)
    (BitVec.ofNat 64 (k + 1)) sv jv
  -- Feed primitive facts (never intermediate `evalStmtFuel` facts: after
  -- unfolding, only syntactically-matching rules fire). `simp only`
  -- (unlike full `simp`) leaves `(ofNat 64 k).toNat` alone, so `hset'`
  -- fires as-is.
  cases F <;>
    simp only [vec64FillBody, evalStmtFuel, evalStmtZero, evalStmtWith, hi, harr,
      hset', up1, hi2, up2]

/-- One sum step accumulates the block element and advances (any fuel). -/
theorem vec64SumBody_eval (F : Nat) (blk : Vec64) (nv iv sv : BitVec 64)
    (k : Nat) (hk32 : k < 2 ^ 64)
    (hget : vecGet64 blk k = .ok (BitVec.ofNat 64 k)) :
    evalStmtFuel F vec64SumBody
        (mkVec64Env blk nv iv sv (BitVec.ofNat 64 k)) =
      .ok (mkVec64Env blk nv iv (sv + BitVec.ofNat 64 k)
        (BitVec.ofNat 64 (k + 1)), .fellThrough) := by
  have hkk : (BitVec.ofNat 64 k).toNat = k := ofNat64_toNat k hk32
  have hj := mkVec64Env_j blk nv iv sv (BitVec.ofNat 64 k)
  have hs0 := mkVec64Env_s blk nv iv sv (BitVec.ofNat 64 k)
  have harr := mkVec64Env_v blk nv iv sv (BitVec.ofNat 64 k)
  have hget' : vecGet64 blk (BitVec.ofNat 64 k).toNat =
      .ok (BitVec.ofNat 64 k) := by rw [hkk]; exact hget
  have hg : evalExpr (.vget "v" (.var "j"))
        (mkVec64Env blk nv iv sv (BitVec.ofNat 64 k)) =
        .ok (.u64 (BitVec.ofNat 64 k)) := by
    simp only [evalExpr, hj, harr, hget']
  have hs : evalExpr (.uadd (.var "s") (.vget "v" (.var "j")))
        (mkVec64Env blk nv iv sv (BitVec.ofNat 64 k)) =
        .ok (.u64 (sv + BitVec.ofNat 64 k)) := by
    simp only [evalExpr, hs0, hj, harr, hget']
  have hj2 : evalExpr (.uadd (.var "j") (.lit (.u64 1#64)))
        (mkVec64Env blk nv iv (sv + BitVec.ofNat 64 k) (BitVec.ofNat 64 k)) =
        .ok (.u64 (BitVec.ofNat 64 (k + 1))) := by
    have h1 := mkVec64Env_j blk nv iv (sv + BitVec.ofNat 64 k)
      (BitVec.ofNat 64 k)
    simp only [evalExpr, litVal, h1, ofNat64_add_one]
  have up1 := vec64Env_update_s blk nv iv sv (sv + BitVec.ofNat 64 k)
    (BitVec.ofNat 64 k)
  have up2 := vec64Env_update_j blk nv iv (sv + BitVec.ofNat 64 k)
    (BitVec.ofNat 64 k) (BitVec.ofNat 64 (k + 1))
  -- Feed primitive facts (never intermediate `evalStmtFuel` facts: after
  -- unfolding, only syntactically-matching rules fire). `hs`/`hg` are
  -- `evalExpr`-headed (no `evalExpr` unfolding in the set), so they fire
  -- as-is; `hj`/`harr`/`hget'` discharge the inner `vget` matches.
  cases F <;>
    simp only [vec64SumBody, evalStmtFuel, evalStmtZero, evalStmtWith, hs, hj2,
      up1, up2]

/-! ### Heap loop correctness (fuel-generalized) -/

/-- Fill-loop correctness: the eval loop runs the `Base` fill to completion.
    The `Base` program (`hfill`) is both spec and witness: induction follows
    its unfolding, like `sumWhile_correct`. -/
theorem vec64FillWhile_correct (blk : Vec64) (nv : BitVec 64)
    (F k : Nat) (sv jv : BitVec 64) (blkOut : Vec64)
    (hk : k ≤ nv.toNat)
    (hlen : blk.val.length = nv.toNat)
    (hlive : blk.freed = false)
    (hn32 : nv.toNat < 2 ^ 64)
    (hfill : vecFillLoopAux64 blk k (nv.toNat - k) = .ok blkOut)
    (hF : nv.toNat - k ≤ F) :
    evalStmtFuel F vec64FillWhile
        (mkVec64Env blk nv (BitVec.ofNat 64 k) sv jv) =
      .ok (mkVec64Env blkOut nv (BitVec.ofNat 64 nv.toNat) sv jv,
        .fellThrough) := by
  induction F generalizing k blk blkOut with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    -- `subst` creates `ofNat 64 nv.toNat`; `simp only` (unlike full `simp`)
    -- leaves it alone, so the cond fact stays in `ofNat` form and `rw`
    -- fires syntactically (cf. probe6).
    have hcond : evalExpr (.ult (.var "i") (.var "n"))
        (mkVec64Env blk nv (BitVec.ofNat 64 nv.toNat) sv jv) =
        .ok (.b false) := by
      have hc := vec64FillCond_eval blk nv nv.toNat sv jv hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hfill
    simp only [vecFillLoopAux64] at hfill
    cases hfill
    simp only [vec64FillWhile, evalStmtFuel, evalStmtZero, evalStmtZeroHandler,
      evalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 64 := by omega
      have hklen : k < blk.val.length := by omega
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkVec64Env blk nv (BitVec.ofNat 64 k) sv jv) =
          .ok (.b true) := by
        simpa [hlt] using (vec64FillCond_eval blk nv k sv jv hk32)
      have hset : vecSet64 blk k (BitVec.ofNat 64 k) =
          .ok ⟨blk.val.set k (BitVec.ofNat 64 k), false⟩ :=
        vecSet64_ok blk k _ hlive hklen
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hfill
      simp only [vecFillLoopAux64, hset] at hfill
      -- hfill : Aux ⟨set ..⟩ (k+1) (n-(k+1)) = ok blkOut
      have hbody := vec64FillBody_eval F blk nv k sv jv
        ⟨blk.val.set k (BitVec.ofNat 64 k), false⟩
        hklen hk32 hlive hset
      have hstep : evalStmtFuel (F + 1) vec64FillWhile
            (mkVec64Env blk nv (BitVec.ofNat 64 k) sv jv)
          = evalStmtFuel F vec64FillWhile
            (mkVec64Env ⟨blk.val.set k (BitVec.ofNat 64 k), false⟩ nv
              (BitVec.ofNat 64 (k + 1)) sv jv) := by
        simp [vec64FillWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond, hbody]
      rw [hstep]
      have hlenMid : (⟨blk.val.set k (BitVec.ofNat 64 k), false⟩ : Vec64).val.length
          = nv.toNat := by
        show (blk.val.set k (BitVec.ofNat 64 k)).length = nv.toNat
        rw [List.length_set]
        omega
      have hliveMid : (⟨blk.val.set k (BitVec.ofNat 64 k), false⟩ : Vec64).freed
          = false := rfl
      exact ih ⟨blk.val.set k (BitVec.ofNat 64 k), false⟩ (k + 1) blkOut
        (by omega) hlenMid hliveMid hfill (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkVec64Env blk nv (BitVec.ofNat 64 nv.toNat) sv jv) =
          .ok (.b false) := by
        have hc := vec64FillCond_eval blk nv nv.toNat sv jv hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hfill
      simp only [vecFillLoopAux64] at hfill
      cases hfill
      simp only [vec64FillWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith]
      rw [hcond]

/-- Sum-loop correctness: the eval loop runs the `Base` sum to completion. -/
theorem vec64SumWhile_correct (blk : Vec64) (nv : BitVec 64)
    (F k : Nat) (iv sv : BitVec 64) (sout : BitVec 64)
    (hk : k ≤ nv.toNat)
    (hget : ∀ j, k ≤ j → j < nv.toNat →
      vecGet64 blk j = .ok (BitVec.ofNat 64 j))
    (hn32 : nv.toNat < 2 ^ 64)
    (hsum : vecSumLoopAux64 blk k (nv.toNat - k) sv = .ok sout)
    (hF : nv.toNat - k ≤ F) :
    evalStmtFuel F vec64SumWhile
        (mkVec64Env blk nv iv sv (BitVec.ofNat 64 k)) =
      .ok (mkVec64Env blk nv iv sout (BitVec.ofNat 64 nv.toNat),
        .fellThrough) := by
  induction F generalizing k sv sout with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : evalExpr (.ult (.var "j") (.var "n"))
        (mkVec64Env blk nv iv sv (BitVec.ofNat 64 nv.toNat)) =
        .ok (.b false) := by
      have hc := vec64SumCond_eval blk nv iv sv nv.toNat hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hsum
    simp only [vecSumLoopAux64] at hsum
    cases hsum
    simp only [vec64SumWhile, evalStmtFuel, evalStmtZero, evalStmtZeroHandler,
      evalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 64 := by omega
      have hcond : evalExpr (.ult (.var "j") (.var "n"))
          (mkVec64Env blk nv iv sv (BitVec.ofNat 64 k)) =
          .ok (.b true) := by
        simpa [hlt] using (vec64SumCond_eval blk nv iv sv k hk32)
      have hgetk : vecGet64 blk k = .ok (BitVec.ofNat 64 k) :=
        hget k (Nat.le_refl _) hlt
      have hbody := vec64SumBody_eval F blk nv iv sv k hk32 hgetk
      have hstep : evalStmtFuel (F + 1) vec64SumWhile
            (mkVec64Env blk nv iv sv (BitVec.ofNat 64 k))
          = evalStmtFuel F vec64SumWhile
            (mkVec64Env blk nv iv (sv + BitVec.ofNat 64 k)
              (BitVec.ofNat 64 (k + 1))) := by
        simp [vec64SumWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond, hbody]
      rw [hstep]
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hsum
      simp only [vecSumLoopAux64, hgetk] at hsum
      exact ih (k + 1) (sv + BitVec.ofNat 64 k) sout (by omega)
        (by intro j hjlo hjhi; exact hget j (by omega) hjhi) hsum (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "j") (.var "n"))
          (mkVec64Env blk nv iv sv (BitVec.ofNat 64 nv.toNat)) =
          .ok (.b false) := by
        have hc := vec64SumCond_eval blk nv iv sv nv.toNat hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hsum
      simp only [vecSumLoopAux64] at hsum
      cases hsum
      simp only [vec64SumWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith]
      rw [hcond]

/-! ### Whole-function correctness (fuel-generalized, then instantiated) -/

/-- `emit_correct` for `vec_alloc_u64`, at any fuel covering `n`. -/
theorem evalFuncFuel_vec64 (F : Nat) (nv : BitVec 64)
    (hn : nv.toNat ≤ F) (hn32 : nv.toNat < 2 ^ 64) :
    evalFuncFuel F vec64Func [.u64 nv] =
      .ok (.u64 (prefixSumU64 ((List.range nv.toNat).map (BitVec.ofNat 64))
        nv.toNat)) := by
  have hfresh : (⟨List.replicate nv.toNat (BitVec.ofNat 64 0), false⟩ : Vec64).val.length =
      0 + nv.toNat := by simp
  obtain ⟨blkOut, hfill0⟩ := vecFillLoopAux64_fresh_ok
    (List.replicate nv.toNat (BitVec.ofNat 64 0)) 0 nv.toNat (by simp)
  have hliveOut : blkOut.freed = false :=
    vecFillLoopAux64_live _ _ _ _ rfl hfill0
  have hgetOut : ∀ j, 0 ≤ j → j < nv.toNat →
      vecGet64 blkOut j = .ok (BitVec.ofNat 64 j) := by
    intro j hjlo hjhi
    have hjhi' : j < 0 + nv.toNat := by omega
    exact vecFillLoopAux64_get _ 0 nv.toNat _ rfl hfresh hfill0 j hjlo hjhi'
  have hsum0 := vecSumLoopAux64_correct blkOut 0 nv.toNat 0 (by
    intro j hjlo hjhi
    exact hgetOut j hjlo (by omega))
  have hrange : List.range' 0 nv.toNat = List.range nv.toNat := by
    simp [List.range_eq_range']
  rw [hrange] at hsum0
  have h0 : (0 : BitVec 64) + prefixSumU64 ((List.range nv.toNat).map
      (BitVec.ofNat 64)) nv.toNat
      = prefixSumU64 ((List.range nv.toNat).map (BitVec.ofNat 64)) nv.toNat :=
    BitVec.zero_add _
  rw [h0] at hsum0
  have hfree0 : vecFree64 blkOut = .ok ⟨blkOut.val, true⟩ :=
    vecFree64_ok blkOut hliveOut
  -- The four lets build the heap env (stated `ofNat`-headed: simp's
  -- simprocs normalize `0` to `0#32`).
  have henv : [("j", .u64 (BitVec.ofNat 64 0)),
        ("s", .u64 (BitVec.ofNat 64 0)),
        ("i", .u64 (BitVec.ofNat 64 0)),
        ("v", .vecVal64 ⟨List.replicate nv.toNat (BitVec.ofNat 64 0), false⟩),
        ("n", .u64 nv)]
      = mkVec64Env ⟨List.replicate nv.toNat (BitVec.ofNat 64 0), false⟩ nv
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) := rfl
  have hn0 : envLookup [("n", .u64 nv)] "n" = some (.u64 nv) := rfl
  -- Loop haves match simp's unfolded handler forms (cf. `evalFuncFuel_sum`).
  cases F with
  | zero =>
    have hF0 : nv.toNat - 0 ≤ 0 := by cir_fuel
    have hloopF0 : evalStmtWith evalStmtZeroHandler
          vec64FillWhile
          (mkVec64Env ⟨List.replicate nv.toNat (BitVec.ofNat 64 0), false⟩ nv
            (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) (BitVec.ofNat 64 0))
        = .ok (mkVec64Env blkOut nv (BitVec.ofNat 64 nv.toNat)
            (BitVec.ofNat 64 0) (BitVec.ofNat 64 0), .fellThrough) :=
      vec64FillWhile_correct _ _ 0 0 _ _ blkOut (Nat.zero_le _)
        (by simp) rfl hn32 hfill0 hF0
    have hloopS0 : evalStmtWith evalStmtZeroHandler
          vec64SumWhile
          (mkVec64Env blkOut nv nv
            (BitVec.ofNat 64 0) (BitVec.ofNat 64 0))
        = .ok (mkVec64Env blkOut nv nv
            (prefixSumU64 ((List.range nv.toNat).map (BitVec.ofNat 64))
              nv.toNat)
            (BitVec.ofNat 64 nv.toNat), .fellThrough) :=
      vec64SumWhile_correct blkOut nv 0 0 nv _ _ (Nat.zero_le _)
        (by intro j hjlo hjhi; exact hgetOut j hjlo hjhi) hn32 hsum0 hF0
    have huv := vec64Env_update_v blkOut nv nv
      (prefixSumU64 ((List.range nv.toNat).map (BitVec.ofNat 64)) nv.toNat)
      nv ⟨blkOut.val, true⟩
    have harv := mkVec64Env_v blkOut nv nv
      (prefixSumU64 ((List.range nv.toNat).map (BitVec.ofNat 64)) nv.toNat)
      nv
    have hars := mkVec64Env_s ⟨blkOut.val, true⟩ nv
      nv
      (prefixSumU64 ((List.range nv.toNat).map (BitVec.ofNat 64)) nv.toNat)
      nv
    simp [evalFuncFuel, vec64Func, bindArgs, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, litVal, envExtend, hn0, vecNew64, henv,
      hloopF0, hloopS0, hfree0, huv, harv, hars]
  | succ F =>
    have hFS : nv.toNat - 0 ≤ F + 1 := by cir_fuel
    have hloopFS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          vec64FillWhile
          (mkVec64Env ⟨List.replicate nv.toNat (BitVec.ofNat 64 0), false⟩ nv
            (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) (BitVec.ofNat 64 0))
        = .ok (mkVec64Env blkOut nv (BitVec.ofNat 64 nv.toNat)
            (BitVec.ofNat 64 0) (BitVec.ofNat 64 0), .fellThrough) :=
      vec64FillWhile_correct _ _ (F + 1) 0 _ _ blkOut (Nat.zero_le _)
        (by simp) rfl hn32 hfill0 hFS
    have hloopSS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          vec64SumWhile
          (mkVec64Env blkOut nv nv
            (BitVec.ofNat 64 0) (BitVec.ofNat 64 0))
        = .ok (mkVec64Env blkOut nv nv
            (prefixSumU64 ((List.range nv.toNat).map (BitVec.ofNat 64))
              nv.toNat)
            (BitVec.ofNat 64 nv.toNat), .fellThrough) :=
      vec64SumWhile_correct blkOut nv (F + 1) 0 nv _ _ (Nat.zero_le _)
        (by intro j hjlo hjhi; exact hgetOut j hjlo hjhi) hn32 hsum0 hFS
    have huv := vec64Env_update_v blkOut nv nv
      (prefixSumU64 ((List.range nv.toNat).map (BitVec.ofNat 64)) nv.toNat)
      nv ⟨blkOut.val, true⟩
    have harv := mkVec64Env_v blkOut nv nv
      (prefixSumU64 ((List.range nv.toNat).map (BitVec.ofNat 64)) nv.toNat)
      nv
    have hars := mkVec64Env_s ⟨blkOut.val, true⟩ nv
      nv
      (prefixSumU64 ((List.range nv.toNat).map (BitVec.ofNat 64)) nv.toNat)
      nv
    simp [evalFuncFuel, vec64Func, bindArgs, evalStmtFuel, evalStmtWith,
      evalExpr, litVal, envExtend, hn0, vecNew64, henv, hloopFS,
      hloopSS, hfree0, huv, harv, hars]

/-- `emit_correct` for `vec_alloc_u64` at the default fuel. -/
theorem emit_correct_vec64 (nv : BitVec 64)
    (hfuel : nv.toNat ≤ EVAL_FUEL) :
    evalFunc vec64Func [.u64 nv] = vec64Fwd nv := by
  have h32 : nv.toNat < 2 ^ 64 := word64_lt_two64_of_fuel _ hfuel
  have h := evalFuncFuel_vec64 EVAL_FUEL nv hfuel h32
  have hc := vecFillSumU64_correct nv.toNat
  simp only [evalFunc, vec64Fwd, h, hc, u64_map_ok]
