/-
Circe.Emit.Vec2 — M1a `vec_copy_sum`: two live blocks (fill `a` / copy `a` into
`b` / sum `b`). The copy is value-invisible (`vec2Fwd_eq_vecFwd`).
-/
import Circe.Emit.Fragment
import Circe.Emit.Vec

/-! ## M1a: two live blocks (`vec_copy_sum`) -/

/-- Fill body over `a`: `a[i] = i; i = i + 1`. -/
def vec2FillBody : CStmt :=
  .seq (.vset "a" (.var "i") (.var "i"))
       (.assign "i" (.uadd (.var "i") (.lit (.u32 1#32))))

/-- Fill loop over `a`: `while (i < n) { ... }`. -/
def vec2FillWhile : CStmt :=
  .while_ (.ult (.var "i") (.var "n")) vec2FillBody

/-- Copy body: `b[j] = a[j]; j = j + 1` (cross-block read: both blocks
    live simultaneously — the M1a shape). -/
def vec2CopyBody : CStmt :=
  .seq (.vset "b" (.var "j") (.vget "a" (.var "j")))
       (.assign "j" (.uadd (.var "j") (.lit (.u32 1#32))))

/-- Copy loop: `while (j < n) { ... }`. -/
def vec2CopyWhile : CStmt :=
  .while_ (.ult (.var "j") (.var "n")) vec2CopyBody

/-- Sum body over `b`: `s = s + b[k]; k = k + 1`. -/
def vec2SumBody : CStmt :=
  .seq (.assign "s" (.uadd (.var "s") (.vget "b" (.var "k"))))
       (.assign "k" (.uadd (.var "k") (.lit (.u32 1#32))))

/-- Sum loop over `b`: `while (k < n) { ... }`. -/
def vec2SumWhile : CStmt :=
  .while_ (.ult (.var "k") (.var "n")) vec2SumBody

/-- Canonical CoreIR for `tests/c/vec_copy_sum.c`: allocate two `u32`
    blocks, fill `a` with indices, copy `a` into `b`, sum `b`, free
    both, return the sum. The two blocks are disjoint by construction
    (two `malloc` results); the model captures this as two separate
    values. -/
def vec2Func : Func :=
  ⟨"vec_copy_sum",
   [{ name := "n", ty := .u 32, role := .owned }],
   .u 32,
   .seq (.let_ "a" .vecBlock (.vnew (.var "n")))
   (.seq (.let_ "b" .vecBlock (.vnew (.var "n")))
   (.seq (.let_ "i" (.u 32) (.lit (.u32 0)))
   (.seq (.let_ "j" (.u 32) (.lit (.u32 0)))
   (.seq (.let_ "k" (.u 32) (.lit (.u32 0)))
   (.seq (.let_ "s" (.u 32) (.lit (.u32 0)))
   (.seq vec2FillWhile
   (.seq vec2CopyWhile
   (.seq vec2SumWhile
   (.seq (.vfree "a")
   (.seq (.vfree "b")
         (.return_ (.var "s"))))))))))))⟩


/-- Value-level forward for `vec_copy_sum`: the copy is value-invisible,
    so the forward is the same index-sum as `vec_alloc`
    (cf. rendered `vec_copy_sum_fwd`). -/
def vec2Fwd (n : BitVec 32) : Result Value :=
  .u32 <$> vecFillSumU32 n.toNat

/-- The two-block forward agrees with the single-block forward. -/
theorem vec2Fwd_eq_vecFwd (n : BitVec 32) : vec2Fwd n = vecFwd n := rfl

/-! ### Two-block heap environments -/

/-- Two-block environments: both blocks plus bound, all three indices,
    accumulator. All six lets are bound before the fill loop, so one
    shape threads through all three loops. -/
def mkVec2Env (blkA blkB : Vec32) (nv iv jv kv sv : BitVec 32) : Env :=
  [("s", .u32 sv), ("k", .u32 kv), ("j", .u32 jv), ("i", .u32 iv),
   ("b", .vecVal blkB), ("a", .vecVal blkA), ("n", .u32 nv)]

theorem mkVec2Env_s (blkA blkB : Vec32) (nv iv jv kv sv : BitVec 32) :
    envLookup (mkVec2Env blkA blkB nv iv jv kv sv) "s" = some (.u32 sv) := by
  simp [mkVec2Env, envLookup]

theorem mkVec2Env_k (blkA blkB : Vec32) (nv iv jv kv sv : BitVec 32) :
    envLookup (mkVec2Env blkA blkB nv iv jv kv sv) "k" = some (.u32 kv) := by
  simp [mkVec2Env, envLookup, show ("k" : String) ≠ "s" by decide]

theorem mkVec2Env_j (blkA blkB : Vec32) (nv iv jv kv sv : BitVec 32) :
    envLookup (mkVec2Env blkA blkB nv iv jv kv sv) "j" = some (.u32 jv) := by
  simp [mkVec2Env, envLookup, show ("j" : String) ≠ "s" by decide,
    show ("j" : String) ≠ "k" by decide]

theorem mkVec2Env_i (blkA blkB : Vec32) (nv iv jv kv sv : BitVec 32) :
    envLookup (mkVec2Env blkA blkB nv iv jv kv sv) "i" = some (.u32 iv) := by
  simp [mkVec2Env, envLookup, show ("i" : String) ≠ "s" by decide,
    show ("i" : String) ≠ "k" by decide,
    show ("i" : String) ≠ "j" by decide]

theorem mkVec2Env_b (blkA blkB : Vec32) (nv iv jv kv sv : BitVec 32) :
    envLookup (mkVec2Env blkA blkB nv iv jv kv sv) "b" =
      some (.vecVal blkB) := by
  simp [mkVec2Env, envLookup, show ("b" : String) ≠ "s" by decide,
    show ("b" : String) ≠ "k" by decide,
    show ("b" : String) ≠ "j" by decide,
    show ("b" : String) ≠ "i" by decide]

theorem mkVec2Env_a (blkA blkB : Vec32) (nv iv jv kv sv : BitVec 32) :
    envLookup (mkVec2Env blkA blkB nv iv jv kv sv) "a" =
      some (.vecVal blkA) := by
  simp [mkVec2Env, envLookup, show ("a" : String) ≠ "s" by decide,
    show ("a" : String) ≠ "k" by decide,
    show ("a" : String) ≠ "j" by decide,
    show ("a" : String) ≠ "i" by decide,
    show ("a" : String) ≠ "b" by decide]

theorem mkVec2Env_n (blkA blkB : Vec32) (nv iv jv kv sv : BitVec 32) :
    envLookup (mkVec2Env blkA blkB nv iv jv kv sv) "n" = some (.u32 nv) := by
  simp [mkVec2Env, envLookup, show ("n" : String) ≠ "s" by decide,
    show ("n" : String) ≠ "k" by decide,
    show ("n" : String) ≠ "j" by decide,
    show ("n" : String) ≠ "i" by decide,
    show ("n" : String) ≠ "b" by decide,
    show ("n" : String) ≠ "a" by decide]

/-- Updating `a` in a two-block env stays a two-block env. -/
theorem vec2Env_update_a (blkA blkB : Vec32) (nv iv jv kv sv : BitVec 32)
    (blkA' : Vec32) :
    envUpdate (mkVec2Env blkA blkB nv iv jv kv sv) "a" (.vecVal blkA') =
      some (mkVec2Env blkA' blkB nv iv jv kv sv) := by
  simp [mkVec2Env, envUpdate, show ("a" : String) ≠ "s" by decide,
    show ("a" : String) ≠ "k" by decide,
    show ("a" : String) ≠ "j" by decide,
    show ("a" : String) ≠ "i" by decide,
    show ("a" : String) ≠ "b" by decide]

/-- Updating `b` in a two-block env stays a two-block env. -/
theorem vec2Env_update_b (blkA blkB : Vec32) (nv iv jv kv sv : BitVec 32)
    (blkB' : Vec32) :
    envUpdate (mkVec2Env blkA blkB nv iv jv kv sv) "b" (.vecVal blkB') =
      some (mkVec2Env blkA blkB' nv iv jv kv sv) := by
  simp [mkVec2Env, envUpdate, show ("b" : String) ≠ "s" by decide,
    show ("b" : String) ≠ "k" by decide,
    show ("b" : String) ≠ "j" by decide,
    show ("b" : String) ≠ "i" by decide]

/-- Updating `i` in a two-block env stays a two-block env. -/
theorem vec2Env_update_i (blkA blkB : Vec32) (nv iv iv' jv kv sv : BitVec 32) :
    envUpdate (mkVec2Env blkA blkB nv iv jv kv sv) "i" (.u32 iv') =
      some (mkVec2Env blkA blkB nv iv' jv kv sv) := by
  simp [mkVec2Env, envUpdate, show ("i" : String) ≠ "s" by decide,
    show ("i" : String) ≠ "k" by decide,
    show ("i" : String) ≠ "j" by decide]

/-- Updating `j` in a two-block env stays a two-block env. -/
theorem vec2Env_update_j (blkA blkB : Vec32) (nv iv jv jv' kv sv : BitVec 32) :
    envUpdate (mkVec2Env blkA blkB nv iv jv kv sv) "j" (.u32 jv') =
      some (mkVec2Env blkA blkB nv iv jv' kv sv) := by
  simp [mkVec2Env, envUpdate, show ("j" : String) ≠ "s" by decide,
    show ("j" : String) ≠ "k" by decide]

/-- Updating `k` in a two-block env stays a two-block env. -/
theorem vec2Env_update_k (blkA blkB : Vec32) (nv iv jv kv kv' sv : BitVec 32) :
    envUpdate (mkVec2Env blkA blkB nv iv jv kv sv) "k" (.u32 kv') =
      some (mkVec2Env blkA blkB nv iv jv kv' sv) := by
  simp [mkVec2Env, envUpdate, show ("k" : String) ≠ "s" by decide]

/-- Updating `s` in a two-block env stays a two-block env. -/
theorem vec2Env_update_s (blkA blkB : Vec32) (nv iv jv kv sv sv' : BitVec 32) :
    envUpdate (mkVec2Env blkA blkB nv iv jv kv sv) "s" (.u32 sv') =
      some (mkVec2Env blkA blkB nv iv jv kv sv') := by
  simp [mkVec2Env, envUpdate]

/-! ### Two-block loop steps -/

/-- The fill-loop condition reads `i` against the bound. -/
theorem vec2FillCond_eval (blkA blkB : Vec32) (nv : BitVec 32) (k : Nat)
    (jv kv sv : BitVec 32) (h : k < 2 ^ 32) :
    evalExpr (.ult (.var "i") (.var "n"))
        (mkVec2Env blkA blkB nv (BitVec.ofNat 32 k) jv kv sv) =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkVec2Env_i blkA blkB nv (BitVec.ofNat 32 k) jv kv sv
  have hn := mkVec2Env_n blkA blkB nv (BitVec.ofNat 32 k) jv kv sv
  simp [evalExpr, hi, hn, ofNat32_ult k nv h]

/-- The copy-loop condition reads `j` against the bound. -/
theorem vec2CopyCond_eval (blkA blkB : Vec32) (nv : BitVec 32) (k : Nat)
    (iv sv kv : BitVec 32) (h : k < 2 ^ 32) :
    evalExpr (.ult (.var "j") (.var "n"))
        (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) =
      .ok (.b (decide (k < nv.toNat))) := by
  have hj := mkVec2Env_j blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
  have hn := mkVec2Env_n blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
  simp [evalExpr, hj, hn, ofNat32_ult k nv h]

/-- The sum-loop condition reads `k` against the bound. -/
theorem vec2SumCond_eval (blkA blkB : Vec32) (nv : BitVec 32) (k : Nat)
    (iv jv sv : BitVec 32) (h : k < 2 ^ 32) :
    evalExpr (.ult (.var "k") (.var "n"))
        (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv) =
      .ok (.b (decide (k < nv.toNat))) := by
  have hk := mkVec2Env_k blkA blkB nv iv jv (BitVec.ofNat 32 k) sv
  have hn := mkVec2Env_n blkA blkB nv iv jv (BitVec.ofNat 32 k) sv
  simp [evalExpr, hk, hn, ofNat32_ult k nv h]

/-- One fill step stores the index into `a` and advances (any fuel). -/
theorem vec2FillBody_eval (F : Nat) (blkA blkB : Vec32) (nv : BitVec 32)
    (k : Nat) (jv kv sv : BitVec 32) (blkMid : Vec32)
    (_hklen : k < blkA.val.length) (hk32 : k < 2 ^ 32)
    (_hlive : blkA.freed = false)
    (hset : vecSet blkA k (BitVec.ofNat 32 k) = .ok blkMid) :
    evalStmtFuel F vec2FillBody
        (mkVec2Env blkA blkB nv (BitVec.ofNat 32 k) jv kv sv) =
      .ok (mkVec2Env blkMid blkB nv (BitVec.ofNat 32 (k + 1)) jv kv sv,
        .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hi : evalExpr (.var "i")
        (mkVec2Env blkA blkB nv (BitVec.ofNat 32 k) jv kv sv) =
        .ok (.u32 (BitVec.ofNat 32 k)) :=
    evalExpr_var_hit _ _ _
      (mkVec2Env_i blkA blkB nv (BitVec.ofNat 32 k) jv kv sv)
  have harr := mkVec2Env_a blkA blkB nv (BitVec.ofNat 32 k) jv kv sv
  have hset' : vecSet blkA (BitVec.ofNat 32 k).toNat (BitVec.ofNat 32 k) =
      .ok blkMid := by rw [hkk]; exact hset
  have up1 := vec2Env_update_a blkA blkB nv (BitVec.ofNat 32 k) jv kv sv
    blkMid
  have hi2 : evalExpr (.uadd (.var "i") (.lit (.u32 1#32)))
        (mkVec2Env blkMid blkB nv (BitVec.ofNat 32 k) jv kv sv) =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVec2Env_i blkMid blkB nv (BitVec.ofNat 32 k) jv kv sv
    simp only [evalExpr, litVal, h1, ofNat32_add_one]
  have up2 := vec2Env_update_i blkMid blkB nv (BitVec.ofNat 32 k)
    (BitVec.ofNat 32 (k + 1)) jv kv sv
  cases F <;>
    simp only [vec2FillBody, evalStmtFuel, evalStmtZero, evalStmtWith, hi,
      harr, hset', up1, hi2, up2]

/-- One copy step reads `a[j]`, stores into `b[j]`, advances (any fuel). -/
theorem vec2CopyBody_eval (F : Nat) (blkA blkB : Vec32) (nv : BitVec 32)
    (k : Nat) (iv sv kv : BitVec 32) (x : BitVec 32) (blkMid : Vec32)
    (hk32 : k < 2 ^ 32)
    (hget : vecGet blkA k = .ok x)
    (hset : vecSet blkB k x = .ok blkMid) :
    evalStmtFuel F vec2CopyBody
        (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) =
      .ok (mkVec2Env blkA blkMid nv iv (BitVec.ofNat 32 (k + 1)) kv sv,
        .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hj : evalExpr (.var "j")
        (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) =
        .ok (.u32 (BitVec.ofNat 32 k)) :=
    evalExpr_var_hit _ _ _
      (mkVec2Env_j blkA blkB nv iv (BitVec.ofNat 32 k) kv sv)
  have ha := mkVec2Env_a blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
  have hb := mkVec2Env_b blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
  have hget' : vecGet blkA (BitVec.ofNat 32 k).toNat = .ok x := by
    rw [hkk]; exact hget
  have hg : evalExpr (.vget "a" (.var "j"))
        (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) =
        .ok (.u32 x) := by
    -- `hj` (eval`Expr`-headed) would compete with `evalExpr` unfolding and
    -- lose, so discharge the index lookup with the `envLookup`-headed
    -- `hjl` instead (no competing rule).
    have hjl := mkVec2Env_j blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
    simp only [evalExpr, hjl, ha, hget']
  have hset' : vecSet blkB (BitVec.ofNat 32 k).toNat x = .ok blkMid := by
    rw [hkk]; exact hset
  have up1 := vec2Env_update_b blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
    blkMid
  have hj2 : evalExpr (.uadd (.var "j") (.lit (.u32 1#32)))
        (mkVec2Env blkA blkMid nv iv (BitVec.ofNat 32 k) kv sv) =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVec2Env_j blkA blkMid nv iv (BitVec.ofNat 32 k) kv sv
    simp only [evalExpr, litVal, h1, ofNat32_add_one]
  have up2 := vec2Env_update_j blkA blkMid nv iv (BitVec.ofNat 32 k)
    (BitVec.ofNat 32 (k + 1)) kv sv
  cases F <;>
    simp only [vec2CopyBody, evalStmtFuel, evalStmtZero, evalStmtWith, hj,
      hb, hg, hset', up1, hj2, up2]

/-- One sum step accumulates `b[k]` and advances (any fuel). -/
theorem vec2SumBody_eval (F : Nat) (blkA blkB : Vec32) (nv : BitVec 32)
    (k : Nat) (iv jv sv : BitVec 32)
    (hk32 : k < 2 ^ 32)
    (hget : vecGet blkB k = .ok (BitVec.ofNat 32 k)) :
    evalStmtFuel F vec2SumBody
        (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv) =
      .ok (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 (k + 1))
        (sv + BitVec.ofNat 32 k), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hk := mkVec2Env_k blkA blkB nv iv jv (BitVec.ofNat 32 k) sv
  have hs0 := mkVec2Env_s blkA blkB nv iv jv (BitVec.ofNat 32 k) sv
  have harr := mkVec2Env_b blkA blkB nv iv jv (BitVec.ofNat 32 k) sv
  have hget' : vecGet blkB (BitVec.ofNat 32 k).toNat =
      .ok (BitVec.ofNat 32 k) := by rw [hkk]; exact hget
  have hg : evalExpr (.vget "b" (.var "k"))
        (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv) =
        .ok (.u32 (BitVec.ofNat 32 k)) := by
    simp only [evalExpr, hk, harr, hget']
  have hs : evalExpr (.uadd (.var "s") (.vget "b" (.var "k")))
        (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv) =
        .ok (.u32 (sv + BitVec.ofNat 32 k)) := by
    simp only [evalExpr, hs0, hk, harr, hget']
  have hk2 : evalExpr (.uadd (.var "k") (.lit (.u32 1#32)))
        (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k)
          (sv + BitVec.ofNat 32 k)) =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVec2Env_k blkA blkB nv iv jv (BitVec.ofNat 32 k)
      (sv + BitVec.ofNat 32 k)
    simp only [evalExpr, litVal, h1, ofNat32_add_one]
  have up1 := vec2Env_update_s blkA blkB nv iv jv (BitVec.ofNat 32 k) sv
    (sv + BitVec.ofNat 32 k)
  have up2 := vec2Env_update_k blkA blkB nv iv jv (BitVec.ofNat 32 k)
    (BitVec.ofNat 32 (k + 1)) (sv + BitVec.ofNat 32 k)
  cases F <;>
    simp only [vec2SumBody, evalStmtFuel, evalStmtZero, evalStmtWith, hs,
      hk2, up1, up2]

/-! ### Two-block loop correctness (fuel-generalized) -/

/-- Fill-loop correctness over `a`: the eval loop runs the `Base` fill
    to completion (mirror of `vecFillWhile_correct`). -/
theorem vec2FillWhile_correct (blkA blkB : Vec32) (nv : BitVec 32)
    (F k : Nat) (jv kv sv : BitVec 32) (blkOut : Vec32)
    (hk : k ≤ nv.toNat)
    (hlen : blkA.val.length = nv.toNat)
    (hlive : blkA.freed = false)
    (hn32 : nv.toNat < 2 ^ 32)
    (hfill : vecFillLoopAux blkA k (nv.toNat - k) = .ok blkOut)
    (hF : nv.toNat - k ≤ F) :
    evalStmtFuel F vec2FillWhile
        (mkVec2Env blkA blkB nv (BitVec.ofNat 32 k) jv kv sv) =
      .ok (mkVec2Env blkOut blkB nv (BitVec.ofNat 32 nv.toNat) jv kv sv,
        .fellThrough) := by
  induction F generalizing k blkA blkOut with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : evalExpr (.ult (.var "i") (.var "n"))
        (mkVec2Env blkA blkB nv (BitVec.ofNat 32 nv.toNat) jv kv sv) =
        .ok (.b false) := by
      have hc := vec2FillCond_eval blkA blkB nv nv.toNat jv kv sv hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hfill
    simp only [vecFillLoopAux] at hfill
    cases hfill
    simp only [vec2FillWhile, evalStmtFuel, evalStmtZero,
      evalStmtZeroHandler, evalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hklen : k < blkA.val.length := by omega
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
            (mkVec2Env blkA blkB nv (BitVec.ofNat 32 k) jv kv sv) =
            .ok (.b true) := by
        simpa [hlt] using (vec2FillCond_eval blkA blkB nv k jv kv sv hk32)
      have hset : vecSet blkA k (BitVec.ofNat 32 k) =
          .ok ⟨blkA.val.set k (BitVec.ofNat 32 k), false⟩ :=
        vecSet_ok blkA k _ hlive hklen
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hfill
      simp only [vecFillLoopAux, hset] at hfill
      have hbody := vec2FillBody_eval F blkA blkB nv k jv kv sv
        ⟨blkA.val.set k (BitVec.ofNat 32 k), false⟩
        hklen hk32 hlive hset
      have hstep : evalStmtFuel (F + 1) vec2FillWhile
            (mkVec2Env blkA blkB nv (BitVec.ofNat 32 k) jv kv sv)
          = evalStmtFuel F vec2FillWhile
            (mkVec2Env ⟨blkA.val.set k (BitVec.ofNat 32 k), false⟩ blkB nv
              (BitVec.ofNat 32 (k + 1)) jv kv sv) := by
        simp [vec2FillWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond, hbody]
      rw [hstep]
      have hlenMid : (⟨blkA.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).val.length
          = nv.toNat := by
        show (blkA.val.set k (BitVec.ofNat 32 k)).length = nv.toNat
        rw [List.length_set]
        omega
      have hliveMid : (⟨blkA.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).freed
          = false := rfl
      exact ih ⟨blkA.val.set k (BitVec.ofNat 32 k), false⟩ (k + 1) blkOut
        (by omega) hlenMid hliveMid hfill (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkVec2Env blkA blkB nv (BitVec.ofNat 32 nv.toNat) jv kv sv) =
          .ok (.b false) := by
        have hc := vec2FillCond_eval blkA blkB nv nv.toNat jv kv sv hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hfill
      simp only [vecFillLoopAux] at hfill
      cases hfill
      simp only [vec2FillWhile, evalStmtFuel, evalStmtSuccHandler,
        evalStmtWith]
      rw [hcond]

/-- Copy-loop correctness: the eval loop runs the `Base` copy to
    completion. `blkA` is fixed (read-only source); `blkB` accumulates
    the copy. -/
theorem vec2CopyWhile_correct (blkA blkB : Vec32) (nv : BitVec 32)
    (F k : Nat) (iv sv kv : BitVec 32) (blkOut : Vec32)
    (hk : k ≤ nv.toNat)
    (hlenA : blkA.val.length = nv.toNat)
    (hlenB : blkB.val.length = nv.toNat)
    (_hliveA : blkA.freed = false) (hliveB : blkB.freed = false)
    (hn32 : nv.toNat < 2 ^ 32)
    (hpre : ∀ t, t < k → vecGet blkB t = .ok (BitVec.ofNat 32 t))
    (hsrc : ∀ t, t < nv.toNat → vecGet blkA t = .ok (BitVec.ofNat 32 t))
    (hcopy : vecCopyLoopAux blkA blkB k (nv.toNat - k) = .ok blkOut)
    (hF : nv.toNat - k ≤ F) :
    evalStmtFuel F vec2CopyWhile
        (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) =
      .ok (mkVec2Env blkA blkOut nv iv (BitVec.ofNat 32 nv.toNat) kv sv,
        .fellThrough) := by
  -- `hliveA`: the copy loop never touches `a`'s token (reads go through
  -- `hsrc`, which already says they succeed), so liveness is implied.
  -- Kept as a premise to mirror the fill/sum shapes.
  induction F generalizing k blkB blkOut with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : evalExpr (.ult (.var "j") (.var "n"))
        (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 nv.toNat) kv sv) =
        .ok (.b false) := by
      have hc := vec2CopyCond_eval blkA blkB nv nv.toNat iv sv kv hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hcopy
    simp only [vecCopyLoopAux] at hcopy
    cases hcopy
    simp only [vec2CopyWhile, evalStmtFuel, evalStmtZero,
      evalStmtZeroHandler, evalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hklenB : k < blkB.val.length := by omega
      have hcond : evalExpr (.ult (.var "j") (.var "n"))
            (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) =
            .ok (.b true) := by
        simpa [hlt] using (vec2CopyCond_eval blkA blkB nv k iv sv kv hk32)
      have hgetk : vecGet blkA k = .ok (BitVec.ofNat 32 k) :=
        hsrc k (by omega)
      have hset : vecSet blkB k (BitVec.ofNat 32 k) =
          .ok ⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩ :=
        vecSet_ok blkB k _ hliveB hklenB
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hcopy
      simp only [vecCopyLoopAux, hgetk, hset] at hcopy
      have hbody := vec2CopyBody_eval F blkA blkB nv k iv sv kv
        (BitVec.ofNat 32 k)
        ⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩
        hk32 hgetk hset
      have hstep : evalStmtFuel (F + 1) vec2CopyWhile
            (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv)
          = evalStmtFuel F vec2CopyWhile
            (mkVec2Env blkA
              ⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩ nv iv
              (BitVec.ofNat 32 (k + 1)) kv sv) := by
        simp [vec2CopyWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond, hbody]
      rw [hstep]
      have hlenMid : (⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).val.length
          = nv.toNat := by
        show (blkB.val.set k (BitVec.ofNat 32 k)).length = nv.toNat
        rw [List.length_set]
        omega
      have hliveMid : (⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).freed
          = false := rfl
      have hpre' : ∀ t, t < k + 1 →
          vecGet ⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩ t =
            .ok (BitVec.ofNat 32 t) := by
        intro t ht
        by_cases htk : t = k
        · subst t
          rw [vecGet_ok _ _ _ rfl]
          exact getElem?_set_self blkB.val k _ hklenB
        · exact vecSet_get_other blkB k t _ _ _ (by omega) hset
            (hpre t (by omega))
      exact ih ⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩ (k + 1) blkOut
        (by omega) hlenMid hliveMid hpre' hcopy (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "j") (.var "n"))
          (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 nv.toNat) kv sv) =
          .ok (.b false) := by
        have hc := vec2CopyCond_eval blkA blkB nv nv.toNat iv sv kv hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hcopy
      simp only [vecCopyLoopAux] at hcopy
      cases hcopy
      simp only [vec2CopyWhile, evalStmtFuel, evalStmtSuccHandler,
        evalStmtWith]
      rw [hcond]

/-- Sum-loop correctness over `b`: the eval loop runs the `Base` sum to
    completion (mirror of `vecSumWhile_correct`). -/
theorem vec2SumWhile_correct (blkA blkB : Vec32) (nv : BitVec 32)
    (F k : Nat) (iv jv sv : BitVec 32) (sout : BitVec 32)
    (hk : k ≤ nv.toNat)
    (hget : ∀ j, k ≤ j → j < nv.toNat →
      vecGet blkB j = .ok (BitVec.ofNat 32 j))
    (hn32 : nv.toNat < 2 ^ 32)
    (hsum : vecSumLoopAux blkB k (nv.toNat - k) sv = .ok sout)
    (hF : nv.toNat - k ≤ F) :
    evalStmtFuel F vec2SumWhile
        (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv) =
      .ok (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 nv.toNat) sout,
        .fellThrough) := by
  induction F generalizing k sv sout with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : evalExpr (.ult (.var "k") (.var "n"))
        (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 nv.toNat) sv) =
        .ok (.b false) := by
      have hc := vec2SumCond_eval blkA blkB nv nv.toNat iv jv sv hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hsum
    simp only [vecSumLoopAux] at hsum
    cases hsum
    simp only [vec2SumWhile, evalStmtFuel, evalStmtZero, evalStmtZeroHandler,
      evalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hcond : evalExpr (.ult (.var "k") (.var "n"))
            (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv) =
            .ok (.b true) := by
        simpa [hlt] using (vec2SumCond_eval blkA blkB nv k iv jv sv hk32)
      have hgetk : vecGet blkB k = .ok (BitVec.ofNat 32 k) :=
        hget k (Nat.le_refl _) hlt
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hsum
      simp only [vecSumLoopAux, hgetk] at hsum
      have hbody := vec2SumBody_eval F blkA blkB nv k iv jv sv hk32 hgetk
      have hstep : evalStmtFuel (F + 1) vec2SumWhile
            (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv)
          = evalStmtFuel F vec2SumWhile
            (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 (k + 1))
              (sv + BitVec.ofNat 32 k)) := by
        simp [vec2SumWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond, hbody]
      rw [hstep]
      exact ih (k + 1) (sv + BitVec.ofNat 32 k) sout (by omega)
        (fun j hjlo hjhi => hget j (by omega) hjhi) hsum (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "k") (.var "n"))
          (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 nv.toNat) sv) =
          .ok (.b false) := by
        have hc := vec2SumCond_eval blkA blkB nv nv.toNat iv jv sv hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hsum
      simp only [vecSumLoopAux] at hsum
      cases hsum
      simp only [vec2SumWhile, evalStmtFuel, evalStmtSuccHandler,
        evalStmtWith]
      rw [hcond]

/-! ### Whole-function correctness (fuel-generalized, then instantiated) -/

/-- `emit_correct` for `vec_copy_sum`, at any fuel covering `n`. The
    fill produces indices in `a` (existing `Base` facts), the copy
    carries them into `b` (`vecCopyLoopAux_all`), the sum folds `b`
    (existing `vecSumLoopAux_correct`). -/
theorem evalFuncFuel_vec2 (F : Nat) (nv : BitVec 32)
    (hn : nv.toNat ≤ F) (hn32 : nv.toNat < 2 ^ 32) :
    evalFuncFuel F vec2Func [.u32 nv] =
      .ok (.u32 (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
        nv.toNat)) := by
  have hfresh : (⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ : Vec32).val.length =
      0 + nv.toNat := by simp
  obtain ⟨blkAOut, hfill0⟩ := vecFillLoopAux_fresh_ok
    (List.replicate nv.toNat (BitVec.ofNat 32 0)) 0 nv.toNat (by simp)
  have hliveAOut : blkAOut.freed = false :=
    vecFillLoopAux_live _ _ _ _ rfl hfill0
  have hlenAOut : blkAOut.val.length = nv.toNat := by
    have h := vecFillLoopAux_length _ _ _ _ hfill0
    simp at h
    exact h
  have hgetA : ∀ j, 0 ≤ j → j < nv.toNat →
      vecGet blkAOut j = .ok (BitVec.ofNat 32 j) := by
    intro j hjlo hjhi
    have hjhi' : j < 0 + nv.toNat := by omega
    exact vecFillLoopAux_get _ 0 nv.toNat _ rfl hfresh hfill0 j hjlo hjhi'
  obtain ⟨blkBOut, hcopy0⟩ := vecCopyLoopAux_fresh_ok blkAOut
    ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ 0 nv.toNat
    hliveAOut rfl (by rw [hlenAOut]; simp) (by omega)
    (fun t ht => hgetA t (by omega) (by omega))
  have hliveBOut : blkBOut.freed = false :=
    vecCopyLoopAux_live _ _ _ _ _ rfl hcopy0
  have hlenBOut : blkBOut.val.length = nv.toNat := by
    have h := vecCopyLoopAux_length _ _ _ _ _ hcopy0
    simp at h
    exact h
  have hgetB : ∀ j, 0 ≤ j → j < nv.toNat →
      vecGet blkBOut j = .ok (BitVec.ofNat 32 j) := by
    intro j hjlo hjhi
    have hjhi' : j < 0 + (nv.toNat - 0) := by omega
    exact vecCopyLoopAux_all blkAOut
      ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ 0
      (nv.toNat - 0) blkBOut rfl (by rw [hlenAOut]; simp) (by omega)
      (fun t ht => absurd ht (by omega))
      (fun t ht => hgetA t (by omega) (by omega)) hcopy0 j hjhi'
  have hsum0 := vecSumLoopAux_correct blkBOut 0 nv.toNat 0 (by
    intro j hjlo hjhi
    exact hgetB j hjlo (by omega))
  have hrange : List.range' 0 nv.toNat = List.range nv.toNat := by
    simp [List.range_eq_range']
  rw [hrange] at hsum0
  have h0 : (0 : BitVec 32) + prefixSumU32 ((List.range nv.toNat).map
      (BitVec.ofNat 32)) nv.toNat
      = prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat :=
    BitVec.zero_add _
  rw [h0] at hsum0
  have hfreeA : vecFree blkAOut = .ok ⟨blkAOut.val, true⟩ :=
    vecFree_ok blkAOut hliveAOut
  have hfreeB : vecFree blkBOut = .ok ⟨blkBOut.val, true⟩ :=
    vecFree_ok blkBOut hliveBOut
  -- The second `vnew` reads `n` past the `a` binding: no `hn0`-shaped
  -- fact covers it (contrast `vec`, whose single `vnew` is the first
  -- let), so state it exactly. `simp` never unfolds `envLookup` on its
  -- own (probed) — every lookup redex needs a rewrite fact.
  have hna : envLookup [("a", .vecVal
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩),
      ("n", .u32 nv)] "n" = some (.u32 nv) := by
    simp [envLookup, show ("n" : String) ≠ "a" by decide]
  -- The six lets build the two-block env (stated `ofNat`-headed: simp's
  -- simprocs normalize `0` to `0#32`).
  have henv : [("s", .u32 (BitVec.ofNat 32 0)),
        ("k", .u32 (BitVec.ofNat 32 0)),
        ("j", .u32 (BitVec.ofNat 32 0)),
        ("i", .u32 (BitVec.ofNat 32 0)),
        ("b", .vecVal ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩),
        ("a", .vecVal ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩),
        ("n", .u32 nv)]
      = mkVec2Env ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
        (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)
        (BitVec.ofNat 32 0) := rfl
  have hn0 : envLookup [("n", .u32 nv)] "n" = some (.u32 nv) := rfl
  -- Loop haves match simp's unfolded handler forms (cf. `evalFuncFuel_sum`).
  cases F with
  | zero =>
    have hF0 : nv.toNat - 0 ≤ 0 := by cir_fuel
    have hloopF0 : evalStmtWith evalStmtZeroHandler
          vec2FillWhile
          (mkVec2Env ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0))
        = .ok (mkVec2Env blkAOut
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
            (BitVec.ofNat 32 nv.toNat) (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0), .fellThrough) :=
      vec2FillWhile_correct _ _ _ 0 0 _ _ _ blkAOut (Nat.zero_le _)
        (by simp) rfl hn32 hfill0 hF0
    have hloopC0 : evalStmtWith evalStmtZeroHandler
          vec2CopyWhile
          (mkVec2Env blkAOut
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
        = .ok (mkVec2Env blkAOut blkBOut nv nv
            (BitVec.ofNat 32 nv.toNat) (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0), .fellThrough) :=
      vec2CopyWhile_correct blkAOut
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv 0 0 nv
        (BitVec.ofNat 32 0)
        (BitVec.ofNat 32 0) blkBOut (Nat.zero_le _) hlenAOut (by simp)
        hliveAOut rfl hn32
        (fun t ht => absurd ht (by omega))
        (fun t ht => hgetA t (by omega) (by omega)) hcopy0 hF0
    have hloopS0 : evalStmtWith evalStmtZeroHandler
          vec2SumWhile
          (mkVec2Env blkAOut blkBOut nv nv nv (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0))
        = .ok (mkVec2Env blkAOut blkBOut nv nv nv
            (BitVec.ofNat 32 nv.toNat)
            (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
              nv.toNat), .fellThrough) :=
      vec2SumWhile_correct blkAOut blkBOut nv 0 0 nv nv
        (BitVec.ofNat 32 0)
        (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
        (Nat.zero_le _)
        (by intro j hjlo hjhi; exact hgetB j hjlo hjhi) hn32 hsum0 hF0
    have hfreeA' := vec2Env_update_a blkAOut blkBOut nv nv nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      ⟨blkAOut.val, true⟩
    have hfreeB' := vec2Env_update_b ⟨blkAOut.val, true⟩ blkBOut nv nv nv
      nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      ⟨blkBOut.val, true⟩
    have hrets := mkVec2Env_s ⟨blkAOut.val, true⟩ ⟨blkBOut.val, true⟩ nv
      nv nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
    simp [evalFuncFuel, vec2Func, bindArgs, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, litVal, envExtend, hn0, hna, vecNew, henv,
      mkVec2Env_a, mkVec2Env_b, hloopF0, hloopC0, hloopS0, hfreeA, hfreeB,
      hfreeA', hfreeB', hrets]
  | succ F =>
    have hFS : nv.toNat - 0 ≤ F + 1 := by cir_fuel
    have hloopFS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          vec2FillWhile
          (mkVec2Env ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0))
        = .ok (mkVec2Env blkAOut
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
            (BitVec.ofNat 32 nv.toNat) (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0), .fellThrough) :=
      vec2FillWhile_correct _ _ _ (F + 1) 0 _ _ _ blkAOut (Nat.zero_le _)
        (by simp) rfl hn32 hfill0 hFS
    have hloopCS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          vec2CopyWhile
          (mkVec2Env blkAOut
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
        = .ok (mkVec2Env blkAOut blkBOut nv nv
            (BitVec.ofNat 32 nv.toNat) (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0), .fellThrough) :=
      vec2CopyWhile_correct blkAOut
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv (F + 1) 0
        nv (BitVec.ofNat 32 0)
        (BitVec.ofNat 32 0) blkBOut (Nat.zero_le _) hlenAOut (by simp)
        hliveAOut rfl hn32
        (fun t ht => absurd ht (by omega))
        (fun t ht => hgetA t (by omega) (by omega)) hcopy0 hFS
    have hloopSS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          vec2SumWhile
          (mkVec2Env blkAOut blkBOut nv nv nv (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0))
        = .ok (mkVec2Env blkAOut blkBOut nv nv nv
            (BitVec.ofNat 32 nv.toNat)
            (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
              nv.toNat), .fellThrough) :=
      vec2SumWhile_correct blkAOut blkBOut nv (F + 1) 0 nv nv
        (BitVec.ofNat 32 0)
        (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
        (Nat.zero_le _)
        (by intro j hjlo hjhi; exact hgetB j hjlo hjhi) hn32 hsum0 hFS
    have hfreeA' := vec2Env_update_a blkAOut blkBOut nv nv nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      ⟨blkAOut.val, true⟩
    have hfreeB' := vec2Env_update_b ⟨blkAOut.val, true⟩ blkBOut nv nv nv
      nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      ⟨blkBOut.val, true⟩
    have hrets := mkVec2Env_s ⟨blkAOut.val, true⟩ ⟨blkBOut.val, true⟩ nv
      nv nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
    simp [evalFuncFuel, vec2Func, bindArgs, evalStmtFuel, evalStmtWith,
      evalExpr, litVal, envExtend, hn0, hna, vecNew, henv, mkVec2Env_a,
      mkVec2Env_b, hloopFS,
      hloopCS, hloopSS, hfreeA, hfreeB, hfreeA', hfreeB', hrets]

/-- `emit_correct` for `vec_copy_sum` at the default fuel. -/
theorem emit_correct_vec2 (nv : BitVec 32)
    (hfuel : nv.toNat ≤ EVAL_FUEL) :
    evalFunc vec2Func [.u32 nv] = vec2Fwd nv := by
  have h32 : nv.toNat < 2 ^ 32 := word32_lt_two32_of_fuel _ hfuel
  have h := evalFuncFuel_vec2 EVAL_FUEL nv hfuel h32
  have hc := vecFillSumU32_correct nv.toNat
  simp only [evalFunc, vec2Fwd, h, hc, u32_map_ok]

/-- Corollary: `vec_copy_sum` delivers the `range` prefix sum on success. -/
theorem emit_correct_vec2_ok (nv : BitVec 32) (r : BitVec 32)
    (hfuel : nv.toNat ≤ EVAL_FUEL)
    (h : vecFillSumU32 nv.toNat = .ok r) :
    evalFunc vec2Func [.u32 nv] = .ok (.u32 r) := by
  rw [emit_correct_vec2 nv hfuel]
  unfold vec2Fwd
  rw [h]
  exact u32_map_ok r
