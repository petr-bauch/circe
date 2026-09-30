/-
Circe.Emit.VecRealloc — M1c `vec_realloc`: grow a uniquely-owned `u32`
block via `realloc` (fill `[0,n)`, resize to `2*n` preserving the prefix,
fill the extension `[n,2*n)`, sum, free).
-/
import Circe.Emit.Fragment
import Circe.Emit.Vec

/-! ## M1c: grown block (`vec_realloc`) -/

/-- Fill body over `v`: `v[i] = i; i = i + 1`. -/
def vecReallocFillBody : CStmt :=
  .seq (.vset "v" (.var "i") (.var "i"))
       (.assign "i" (.uadd (.var "i") (.lit (.u32 1#32))))

/-- Fill loop over `v`: `while (i < n) { ... }`. -/
def vecReallocFillWhile : CStmt :=
  .while_ (.ult (.var "i") (.var "n")) vecReallocFillBody

/-- Extension-fill body: `v[j] = j; j = j + 1` (runs after the `realloc`,
    over the grown capacity). -/
def vecReallocExtBody : CStmt :=
  .seq (.vset "v" (.var "j") (.var "j"))
       (.assign "j" (.uadd (.var "j") (.lit (.u32 1#32))))

/-- Extension-fill loop: `while (j < m) { ... }`. -/
def vecReallocExtWhile : CStmt :=
  .while_ (.ult (.var "j") (.var "m")) vecReallocExtBody

/-- Sum body over `v`: `s = s + v[k]; k = k + 1`. -/
def vecReallocSumBody : CStmt :=
  .seq (.assign "s" (.uadd (.var "s") (.vget "v" (.var "k"))))
       (.assign "k" (.uadd (.var "k") (.lit (.u32 1#32))))

/-- Sum loop over `v`: `while (k < m) { ... }`. -/
def vecReallocSumWhile : CStmt :=
  .while_ (.ult (.var "k") (.var "m")) vecReallocSumBody

/-- Canonical CoreIR for `tests/c/vec_realloc.c`: allocate a zeroed `u32`
    block of `n` words (`malloc`), fill it with indices, grow it to `m =
    n + n` words (`realloc`, prefix preserved), fill the extension with
    indices, sum the whole grown block, `free` it, return the sum. `n` is
    the length (`u32`: C `size_t` must fit 32 bits, like `sum_array`);
    the block lives in `v` as a `vecVal`. -/
def vecReallocFunc : Func :=
  ⟨"vec_realloc",
   [{ name := "n", ty := .u 32, role := .owned }],
   .u 32,
   .seq (.let_ "v" .vecBlock (.vnew (.var "n")))
   (.seq (.let_ "i" (.u 32) (.lit (.u32 0)))
   (.seq (.let_ "m" (.u 32) (.uadd (.var "n") (.var "n")))
   (.seq (.let_ "s" (.u 32) (.lit (.u32 0)))
   (.seq (.let_ "j" (.u 32) (.var "n"))
   (.seq (.let_ "k" (.u 32) (.lit (.u32 0)))
   (.seq vecReallocFillWhile
   (.seq (.vrealloc "v" (.var "m"))
   (.seq vecReallocExtWhile
   (.seq vecReallocSumWhile
   (.seq (.vfree "v")
         (.return_ (.var "s"))))))))))))⟩

/-- Value-level forward for `vec_realloc` (cf. rendered
    `vec_realloc_fwd`): the pure grown-heap program from `Circe.Base`. -/
def vecReallocFwd (n : BitVec 32) : Result Value :=
  .u32 <$> vecReallocFillSumU32 n.toNat

/-! ### Grown-block heap environments -/

/-- Grown-block environments: block plus both bounds, all three indices,
    accumulator. All six lets are bound before the fill loop, so one
    shape threads through all three loops (`m` is `n + n`; `j` starts at
    `n`, like the C `for (j = n; j < m; …)`). -/
def mkVecReallocEnv (blk : Vec32) (nv mv iv jv kv sv : BitVec 32) : Env :=
  [("k", .u32 kv), ("j", .u32 jv), ("s", .u32 sv), ("m", .u32 mv),
   ("i", .u32 iv), ("v", .vecVal blk), ("n", .u32 nv)]

theorem mkVecReallocEnv_k (blk : Vec32) (nv mv iv jv kv sv : BitVec 32) :
    envLookup (mkVecReallocEnv blk nv mv iv jv kv sv) "k" =
      some (.u32 kv) := by
  simp [mkVecReallocEnv, envLookup]

theorem mkVecReallocEnv_j (blk : Vec32) (nv mv iv jv kv sv : BitVec 32) :
    envLookup (mkVecReallocEnv blk nv mv iv jv kv sv) "j" =
      some (.u32 jv) := by
  simp [mkVecReallocEnv, envLookup, show ("j" : String) ≠ "k" by decide]

theorem mkVecReallocEnv_s (blk : Vec32) (nv mv iv jv kv sv : BitVec 32) :
    envLookup (mkVecReallocEnv blk nv mv iv jv kv sv) "s" =
      some (.u32 sv) := by
  simp [mkVecReallocEnv, envLookup, show ("s" : String) ≠ "k" by decide,
    show ("s" : String) ≠ "j" by decide]

theorem mkVecReallocEnv_m (blk : Vec32) (nv mv iv jv kv sv : BitVec 32) :
    envLookup (mkVecReallocEnv blk nv mv iv jv kv sv) "m" =
      some (.u32 mv) := by
  simp [mkVecReallocEnv, envLookup, show ("m" : String) ≠ "k" by decide,
    show ("m" : String) ≠ "j" by decide,
    show ("m" : String) ≠ "s" by decide]

theorem mkVecReallocEnv_i (blk : Vec32) (nv mv iv jv kv sv : BitVec 32) :
    envLookup (mkVecReallocEnv blk nv mv iv jv kv sv) "i" =
      some (.u32 iv) := by
  simp [mkVecReallocEnv, envLookup, show ("i" : String) ≠ "k" by decide,
    show ("i" : String) ≠ "j" by decide,
    show ("i" : String) ≠ "s" by decide,
    show ("i" : String) ≠ "m" by decide]

theorem mkVecReallocEnv_v (blk : Vec32) (nv mv iv jv kv sv : BitVec 32) :
    envLookup (mkVecReallocEnv blk nv mv iv jv kv sv) "v" =
      some (.vecVal blk) := by
  simp [mkVecReallocEnv, envLookup, show ("v" : String) ≠ "k" by decide,
    show ("v" : String) ≠ "j" by decide,
    show ("v" : String) ≠ "s" by decide,
    show ("v" : String) ≠ "m" by decide,
    show ("v" : String) ≠ "i" by decide]

theorem mkVecReallocEnv_n (blk : Vec32) (nv mv iv jv kv sv : BitVec 32) :
    envLookup (mkVecReallocEnv blk nv mv iv jv kv sv) "n" =
      some (.u32 nv) := by
  simp [mkVecReallocEnv, envLookup, show ("n" : String) ≠ "k" by decide,
    show ("n" : String) ≠ "j" by decide,
    show ("n" : String) ≠ "s" by decide,
    show ("n" : String) ≠ "m" by decide,
    show ("n" : String) ≠ "i" by decide,
    show ("n" : String) ≠ "v" by decide]

/-- Updating `v` in a grown-block env stays a grown-block env. -/
theorem vecReallocEnv_update_v (blk : Vec32) (nv mv iv jv kv sv : BitVec 32)
    (blk' : Vec32) :
    envUpdate (mkVecReallocEnv blk nv mv iv jv kv sv) "v" (.vecVal blk') =
      some (mkVecReallocEnv blk' nv mv iv jv kv sv) := by
  simp [mkVecReallocEnv, envUpdate, show ("v" : String) ≠ "k" by decide,
    show ("v" : String) ≠ "j" by decide,
    show ("v" : String) ≠ "s" by decide,
    show ("v" : String) ≠ "m" by decide,
    show ("v" : String) ≠ "i" by decide]

/-- Updating `i` in a grown-block env stays a grown-block env. -/
theorem vecReallocEnv_update_i (blk : Vec32) (nv mv iv iv' jv kv sv : BitVec 32) :
    envUpdate (mkVecReallocEnv blk nv mv iv jv kv sv) "i" (.u32 iv') =
      some (mkVecReallocEnv blk nv mv iv' jv kv sv) := by
  simp [mkVecReallocEnv, envUpdate, show ("i" : String) ≠ "k" by decide,
    show ("i" : String) ≠ "j" by decide,
    show ("i" : String) ≠ "s" by decide,
    show ("i" : String) ≠ "m" by decide]

/-- Updating `m` in a grown-block env stays a grown-block env. -/
theorem vecReallocEnv_update_m (blk : Vec32) (nv mv mv' iv jv kv sv : BitVec 32) :
    envUpdate (mkVecReallocEnv blk nv mv iv jv kv sv) "m" (.u32 mv') =
      some (mkVecReallocEnv blk nv mv' iv jv kv sv) := by
  simp [mkVecReallocEnv, envUpdate, show ("m" : String) ≠ "k" by decide,
    show ("m" : String) ≠ "j" by decide,
    show ("m" : String) ≠ "s" by decide]

/-- Updating `s` in a grown-block env stays a grown-block env. -/
theorem vecReallocEnv_update_s (blk : Vec32) (nv mv iv jv kv sv sv' : BitVec 32) :
    envUpdate (mkVecReallocEnv blk nv mv iv jv kv sv) "s" (.u32 sv') =
      some (mkVecReallocEnv blk nv mv iv jv kv sv') := by
  simp [mkVecReallocEnv, envUpdate, show ("s" : String) ≠ "k" by decide,
    show ("s" : String) ≠ "j" by decide]

/-- Updating `j` in a grown-block env stays a grown-block env. -/
theorem vecReallocEnv_update_j (blk : Vec32) (nv mv iv jv jv' kv sv : BitVec 32) :
    envUpdate (mkVecReallocEnv blk nv mv iv jv kv sv) "j" (.u32 jv') =
      some (mkVecReallocEnv blk nv mv iv jv' kv sv) := by
  simp [mkVecReallocEnv, envUpdate, show ("j" : String) ≠ "k" by decide]

/-- Updating `k` in a grown-block env stays a grown-block env. -/
theorem vecReallocEnv_update_k (blk : Vec32) (nv mv iv jv kv kv' sv : BitVec 32) :
    envUpdate (mkVecReallocEnv blk nv mv iv jv kv sv) "k" (.u32 kv') =
      some (mkVecReallocEnv blk nv mv iv jv kv' sv) := by
  simp [mkVecReallocEnv, envUpdate]

/-! ### Grown-block loop steps -/

/-- The fill-loop condition reads `i` against `n`. -/
theorem vecReallocFillCond_eval (blk : Vec32) (nv mv : BitVec 32) (k : Nat)
    (jv kv sv : BitVec 32) (h : k < 2 ^ 32) :
    evalExpr (.ult (.var "i") (.var "n"))
        (mkVecReallocEnv blk nv mv (BitVec.ofNat 32 k) jv kv sv) =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkVecReallocEnv_i blk nv mv (BitVec.ofNat 32 k) jv kv sv
  have hn := mkVecReallocEnv_n blk nv mv (BitVec.ofNat 32 k) jv kv sv
  simp [evalExpr, hi, hn, ofNat32_ult k nv h]

/-- The extension-loop condition reads `j` against `m`. -/
theorem vecReallocExtCond_eval (blk : Vec32) (nv mv : BitVec 32) (k : Nat)
    (iv kv sv : BitVec 32) (h : k < 2 ^ 32) :
    evalExpr (.ult (.var "j") (.var "m"))
        (mkVecReallocEnv blk nv mv iv (BitVec.ofNat 32 k) kv sv) =
      .ok (.b (decide (k < mv.toNat))) := by
  have hj := mkVecReallocEnv_j blk nv mv iv (BitVec.ofNat 32 k) kv sv
  have hm := mkVecReallocEnv_m blk nv mv iv (BitVec.ofNat 32 k) kv sv
  simp [evalExpr, hj, hm, ofNat32_ult k mv h]

/-- The sum-loop condition reads `k` against `m`. -/
theorem vecReallocSumCond_eval (blk : Vec32) (nv mv : BitVec 32) (k : Nat)
    (iv jv sv : BitVec 32) (h : k < 2 ^ 32) :
    evalExpr (.ult (.var "k") (.var "m"))
        (mkVecReallocEnv blk nv mv iv jv (BitVec.ofNat 32 k) sv) =
      .ok (.b (decide (k < mv.toNat))) := by
  have hk := mkVecReallocEnv_k blk nv mv iv jv (BitVec.ofNat 32 k) sv
  have hm := mkVecReallocEnv_m blk nv mv iv jv (BitVec.ofNat 32 k) sv
  simp [evalExpr, hk, hm, ofNat32_ult k mv h]

/-- One fill step stores the index and advances (any fuel: loop-free). -/
theorem vecReallocFillBody_eval (F : Nat) (blk : Vec32) (nv mv : BitVec 32)
    (k : Nat) (jv kv sv : BitVec 32) (blkMid : Vec32)
    (_hklen : k < blk.val.length) (hk32 : k < 2 ^ 32)
    (_hlive : blk.freed = false)
    (hset : vecSet blk k (BitVec.ofNat 32 k) = .ok blkMid) :
    evalStmtFuel F vecReallocFillBody
        (mkVecReallocEnv blk nv mv (BitVec.ofNat 32 k) jv kv sv) =
      .ok (mkVecReallocEnv blkMid nv mv (BitVec.ofNat 32 (k + 1)) jv kv sv,
        .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hi : evalExpr (.var "i")
        (mkVecReallocEnv blk nv mv (BitVec.ofNat 32 k) jv kv sv) =
        .ok (.u32 (BitVec.ofNat 32 k)) :=
    evalExpr_var_hit _ _ _
      (mkVecReallocEnv_i blk nv mv (BitVec.ofNat 32 k) jv kv sv)
  have harr := mkVecReallocEnv_v blk nv mv (BitVec.ofNat 32 k) jv kv sv
  have hset' : vecSet blk (BitVec.ofNat 32 k).toNat (BitVec.ofNat 32 k) =
      .ok blkMid := by rw [hkk]; exact hset
  have up1 := vecReallocEnv_update_v blk nv mv (BitVec.ofNat 32 k) jv kv sv
    blkMid
  have hi2 : evalExpr (.uadd (.var "i") (.lit (.u32 1#32)))
        (mkVecReallocEnv blkMid nv mv (BitVec.ofNat 32 k) jv kv sv) =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVecReallocEnv_i blkMid nv mv (BitVec.ofNat 32 k) jv kv sv
    simp only [evalExpr, litVal, h1, ofNat32_add_one]
  have up2 := vecReallocEnv_update_i blkMid nv mv (BitVec.ofNat 32 k)
    (BitVec.ofNat 32 (k + 1)) jv kv sv
  cases F <;>
    simp only [vecReallocFillBody, evalStmtFuel, evalStmtZero, evalStmtWith,
      hi, harr, hset', up1, hi2, up2]

/-- The `realloc` step resizes the block in place (any fuel: loop-free,
    via the shared `evalStmtFuel_vrealloc` fact). -/
theorem vecReallocStep_eval (F : Nat) (blk : Vec32) (nv mv : BitVec 32)
    (iv jv kv sv : BitVec 32) (blkMid : Vec32)
    (hre : vecRealloc blk mv.toNat = .ok blkMid) :
    evalStmtFuel F (.vrealloc "v" (.var "m"))
        (mkVecReallocEnv blk nv mv iv jv kv sv) =
      .ok (mkVecReallocEnv blkMid nv mv iv jv kv sv, .fellThrough) := by
  have hm : evalExpr (.var "m")
        (mkVecReallocEnv blk nv mv iv jv kv sv) = .ok (.u32 mv) :=
    evalExpr_var_hit _ _ _ (mkVecReallocEnv_m blk nv mv iv jv kv sv)
  have harr := mkVecReallocEnv_v blk nv mv iv jv kv sv
  have up := vecReallocEnv_update_v blk nv mv iv jv kv sv blkMid
  exact evalStmtFuel_vrealloc F "v" (.var "m") _ mv blk blkMid _ hm harr hre up

/-- One extension step stores the index and advances (any fuel). -/
theorem vecReallocExtBody_eval (F : Nat) (blk : Vec32) (nv mv : BitVec 32)
    (k : Nat) (iv kv sv : BitVec 32) (blkMid : Vec32)
    (_hklen : k < blk.val.length) (hk32 : k < 2 ^ 32)
    (_hlive : blk.freed = false)
    (hset : vecSet blk k (BitVec.ofNat 32 k) = .ok blkMid) :
    evalStmtFuel F vecReallocExtBody
        (mkVecReallocEnv blk nv mv iv (BitVec.ofNat 32 k) kv sv) =
      .ok (mkVecReallocEnv blkMid nv mv iv (BitVec.ofNat 32 (k + 1)) kv sv,
        .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hj : evalExpr (.var "j")
        (mkVecReallocEnv blk nv mv iv (BitVec.ofNat 32 k) kv sv) =
        .ok (.u32 (BitVec.ofNat 32 k)) :=
    evalExpr_var_hit _ _ _
      (mkVecReallocEnv_j blk nv mv iv (BitVec.ofNat 32 k) kv sv)
  have harr := mkVecReallocEnv_v blk nv mv iv (BitVec.ofNat 32 k) kv sv
  have hset' : vecSet blk (BitVec.ofNat 32 k).toNat (BitVec.ofNat 32 k) =
      .ok blkMid := by rw [hkk]; exact hset
  have up1 := vecReallocEnv_update_v blk nv mv iv (BitVec.ofNat 32 k) kv sv
    blkMid
  have hj2 : evalExpr (.uadd (.var "j") (.lit (.u32 1#32)))
        (mkVecReallocEnv blkMid nv mv iv (BitVec.ofNat 32 k) kv sv) =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVecReallocEnv_j blkMid nv mv iv (BitVec.ofNat 32 k) kv sv
    simp only [evalExpr, litVal, h1, ofNat32_add_one]
  have up2 := vecReallocEnv_update_j blkMid nv mv iv (BitVec.ofNat 32 k)
    (BitVec.ofNat 32 (k + 1)) kv sv
  cases F <;>
    simp only [vecReallocExtBody, evalStmtFuel, evalStmtZero, evalStmtWith,
      hj, harr, hset', up1, hj2, up2]

/-- One sum step accumulates the block element and advances (any fuel). -/
theorem vecReallocSumBody_eval (F : Nat) (blk : Vec32) (nv mv : BitVec 32)
    (k : Nat) (iv jv sv : BitVec 32)
    (hk32 : k < 2 ^ 32)
    (hget : vecGet blk k = .ok (BitVec.ofNat 32 k)) :
    evalStmtFuel F vecReallocSumBody
        (mkVecReallocEnv blk nv mv iv jv (BitVec.ofNat 32 k) sv) =
      .ok (mkVecReallocEnv blk nv mv iv jv (BitVec.ofNat 32 (k + 1))
        (sv + BitVec.ofNat 32 k), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hk := mkVecReallocEnv_k blk nv mv iv jv (BitVec.ofNat 32 k) sv
  have hs0 := mkVecReallocEnv_s blk nv mv iv jv (BitVec.ofNat 32 k) sv
  have harr := mkVecReallocEnv_v blk nv mv iv jv (BitVec.ofNat 32 k) sv
  have hget' : vecGet blk (BitVec.ofNat 32 k).toNat =
      .ok (BitVec.ofNat 32 k) := by rw [hkk]; exact hget
  have hg : evalExpr (.vget "v" (.var "k"))
        (mkVecReallocEnv blk nv mv iv jv (BitVec.ofNat 32 k) sv) =
        .ok (.u32 (BitVec.ofNat 32 k)) := by
    simp only [evalExpr, hk, harr, hget']
  have hs : evalExpr (.uadd (.var "s") (.vget "v" (.var "k")))
        (mkVecReallocEnv blk nv mv iv jv (BitVec.ofNat 32 k) sv) =
        .ok (.u32 (sv + BitVec.ofNat 32 k)) := by
    simp only [evalExpr, hs0, hk, harr, hget']
  have hk2 : evalExpr (.uadd (.var "k") (.lit (.u32 1#32)))
        (mkVecReallocEnv blk nv mv iv jv (BitVec.ofNat 32 k)
          (sv + BitVec.ofNat 32 k)) =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVecReallocEnv_k blk nv mv iv jv (BitVec.ofNat 32 k)
      (sv + BitVec.ofNat 32 k)
    simp only [evalExpr, litVal, h1, ofNat32_add_one]
  have up1 := vecReallocEnv_update_s blk nv mv iv jv (BitVec.ofNat 32 k) sv
    (sv + BitVec.ofNat 32 k)
  have up2 := vecReallocEnv_update_k blk nv mv iv jv (BitVec.ofNat 32 k)
    (BitVec.ofNat 32 (k + 1)) (sv + BitVec.ofNat 32 k)
  cases F <;>
    simp only [vecReallocSumBody, evalStmtFuel, evalStmtZero, evalStmtWith,
      hs, hk2, up1, up2]

/-! ### Grown-block loop correctness (fuel-generalized) -/

/-- Fill-loop correctness: the eval loop runs the `Base` fill `[0, n)` to
    completion (mirror of `vecFillWhile_correct`; `m`/`j`/`k`/`s` thread
    through untouched). -/
theorem vecReallocFillWhile_correct (blk : Vec32) (nv mv : BitVec 32)
    (F k : Nat) (jv kv sv : BitVec 32) (blkOut : Vec32)
    (hk : k ≤ nv.toNat)
    (hlen : blk.val.length = nv.toNat)
    (hlive : blk.freed = false)
    (hn32 : nv.toNat < 2 ^ 32)
    (hfill : vecFillLoopAux blk k (nv.toNat - k) = .ok blkOut)
    (hF : nv.toNat - k ≤ F) :
    evalStmtFuel F vecReallocFillWhile
        (mkVecReallocEnv blk nv mv (BitVec.ofNat 32 k) jv kv sv) =
      .ok (mkVecReallocEnv blkOut nv mv (BitVec.ofNat 32 nv.toNat) jv kv sv,
        .fellThrough) := by
  induction F generalizing k blk blkOut with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : evalExpr (.ult (.var "i") (.var "n"))
        (mkVecReallocEnv blk nv mv (BitVec.ofNat 32 nv.toNat) jv kv sv) =
        .ok (.b false) := by
      have hc := vecReallocFillCond_eval blk nv mv nv.toNat jv kv sv hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hfill
    simp only [vecFillLoopAux] at hfill
    cases hfill
    simp only [vecReallocFillWhile, evalStmtFuel, evalStmtZero,
      evalStmtZeroHandler, evalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hklen : k < blk.val.length := by omega
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
            (mkVecReallocEnv blk nv mv (BitVec.ofNat 32 k) jv kv sv) =
            .ok (.b true) := by
        simpa [hlt] using (vecReallocFillCond_eval blk nv mv k jv kv sv hk32)
      have hset : vecSet blk k (BitVec.ofNat 32 k) =
          .ok ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ :=
        vecSet_ok blk k _ hlive hklen
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hfill
      simp only [vecFillLoopAux, hset] at hfill
      have hbody := vecReallocFillBody_eval F blk nv mv k jv kv sv
        ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩
        hklen hk32 hlive hset
      have hstep : evalStmtFuel (F + 1) vecReallocFillWhile
            (mkVecReallocEnv blk nv mv (BitVec.ofNat 32 k) jv kv sv)
          = evalStmtFuel F vecReallocFillWhile
            (mkVecReallocEnv ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ nv mv
              (BitVec.ofNat 32 (k + 1)) jv kv sv) := by
        simp [vecReallocFillWhile, evalStmtFuel, evalStmtSuccHandler,
          evalStmtWith, hcond, hbody]
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
          (mkVecReallocEnv blk nv mv (BitVec.ofNat 32 nv.toNat) jv kv sv) =
          .ok (.b false) := by
        have hc := vecReallocFillCond_eval blk nv mv nv.toNat jv kv sv hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hfill
      simp only [vecFillLoopAux] at hfill
      cases hfill
      simp only [vecReallocFillWhile, evalStmtFuel, evalStmtSuccHandler,
        evalStmtWith]
      rw [hcond]

/-- Extension-loop correctness: the eval loop runs the `Base`
    extension fill `[k, m)` to completion (same shape as the fill proof,
    over the grown bound `m`). -/
theorem vecReallocExtWhile_correct (blk : Vec32) (nv mv : BitVec 32)
    (F k : Nat) (iv kv sv : BitVec 32) (blkOut : Vec32)
    (hk : k ≤ mv.toNat)
    (hlen : blk.val.length = mv.toNat)
    (hlive : blk.freed = false)
    (hm32 : mv.toNat < 2 ^ 32)
    (hfill : vecFillLoopAux blk k (mv.toNat - k) = .ok blkOut)
    (hF : mv.toNat - k ≤ F) :
    evalStmtFuel F vecReallocExtWhile
        (mkVecReallocEnv blk nv mv iv (BitVec.ofNat 32 k) kv sv) =
      .ok (mkVecReallocEnv blkOut nv mv iv (BitVec.ofNat 32 mv.toNat) kv sv,
        .fellThrough) := by
  induction F generalizing k blk blkOut with
  | zero =>
    have hkk : k = mv.toNat := by omega
    subst hkk
    have hcond : evalExpr (.ult (.var "j") (.var "m"))
        (mkVecReallocEnv blk nv mv iv (BitVec.ofNat 32 mv.toNat) kv sv) =
        .ok (.b false) := by
      have hc := vecReallocExtCond_eval blk nv mv mv.toNat iv kv sv hm32
      rw [show decide (mv.toNat < mv.toNat) = false from by simp] at hc
      exact hc
    have hsub : mv.toNat - mv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hfill
    simp only [vecFillLoopAux] at hfill
    cases hfill
    simp only [vecReallocExtWhile, evalStmtFuel, evalStmtZero,
      evalStmtZeroHandler, evalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < mv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hklen : k < blk.val.length := by omega
      have hcond : evalExpr (.ult (.var "j") (.var "m"))
            (mkVecReallocEnv blk nv mv iv (BitVec.ofNat 32 k) kv sv) =
            .ok (.b true) := by
        simpa [hlt] using (vecReallocExtCond_eval blk nv mv k iv kv sv hk32)
      have hset : vecSet blk k (BitVec.ofNat 32 k) =
          .ok ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ :=
        vecSet_ok blk k _ hlive hklen
      have hkk1 : mv.toNat - k = (mv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hfill
      simp only [vecFillLoopAux, hset] at hfill
      have hbody := vecReallocExtBody_eval F blk nv mv k iv kv sv
        ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩
        hklen hk32 hlive hset
      have hstep : evalStmtFuel (F + 1) vecReallocExtWhile
            (mkVecReallocEnv blk nv mv iv (BitVec.ofNat 32 k) kv sv)
          = evalStmtFuel F vecReallocExtWhile
            (mkVecReallocEnv ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ nv mv iv
              (BitVec.ofNat 32 (k + 1)) kv sv) := by
        simp [vecReallocExtWhile, evalStmtFuel, evalStmtSuccHandler,
          evalStmtWith, hcond, hbody]
      rw [hstep]
      have hlenMid : (⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).val.length
          = mv.toNat := by
        show (blk.val.set k (BitVec.ofNat 32 k)).length = mv.toNat
        rw [List.length_set]
        omega
      have hliveMid : (⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).freed
          = false := rfl
      exact ih ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ (k + 1) blkOut
        (by omega) hlenMid hliveMid hfill (by omega)
    · have hkk : k = mv.toNat := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "j") (.var "m"))
          (mkVecReallocEnv blk nv mv iv (BitVec.ofNat 32 mv.toNat) kv sv) =
          .ok (.b false) := by
        have hc := vecReallocExtCond_eval blk nv mv mv.toNat iv kv sv hm32
        rw [show decide (mv.toNat < mv.toNat) = false from by simp] at hc
        exact hc
      have hsub : mv.toNat - mv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hfill
      simp only [vecFillLoopAux] at hfill
      cases hfill
      simp only [vecReallocExtWhile, evalStmtFuel, evalStmtSuccHandler,
        evalStmtWith]
      rw [hcond]

/-- Sum-loop correctness over the grown block: the eval loop runs the
    `Base` sum `[k, m)` to completion (mirror of `vecSumWhile_correct`,
    over the grown bound `m`). -/
theorem vecReallocSumWhile_correct (blk : Vec32) (nv mv : BitVec 32)
    (F k : Nat) (iv jv sv : BitVec 32) (sout : BitVec 32)
    (hk : k ≤ mv.toNat)
    (hget : ∀ j, k ≤ j → j < mv.toNat →
      vecGet blk j = .ok (BitVec.ofNat 32 j))
    (hm32 : mv.toNat < 2 ^ 32)
    (hsum : vecSumLoopAux blk k (mv.toNat - k) sv = .ok sout)
    (hF : mv.toNat - k ≤ F) :
    evalStmtFuel F vecReallocSumWhile
        (mkVecReallocEnv blk nv mv iv jv (BitVec.ofNat 32 k) sv) =
      .ok (mkVecReallocEnv blk nv mv iv jv (BitVec.ofNat 32 mv.toNat) sout,
        .fellThrough) := by
  induction F generalizing k sv sout with
  | zero =>
    have hkk : k = mv.toNat := by omega
    subst hkk
    have hcond : evalExpr (.ult (.var "k") (.var "m"))
        (mkVecReallocEnv blk nv mv iv jv (BitVec.ofNat 32 mv.toNat) sv) =
        .ok (.b false) := by
      have hc := vecReallocSumCond_eval blk nv mv mv.toNat iv jv sv hm32
      rw [show decide (mv.toNat < mv.toNat) = false from by simp] at hc
      exact hc
    have hsub : mv.toNat - mv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hsum
    simp only [vecSumLoopAux] at hsum
    cases hsum
    simp only [vecReallocSumWhile, evalStmtFuel, evalStmtZero,
      evalStmtZeroHandler, evalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < mv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hcond : evalExpr (.ult (.var "k") (.var "m"))
            (mkVecReallocEnv blk nv mv iv jv (BitVec.ofNat 32 k) sv) =
            .ok (.b true) := by
        simpa [hlt] using (vecReallocSumCond_eval blk nv mv k iv jv sv hk32)
      have hgetk : vecGet blk k = .ok (BitVec.ofNat 32 k) :=
        hget k (Nat.le_refl _) hlt
      have hbody := vecReallocSumBody_eval F blk nv mv k iv jv sv hk32 hgetk
      have hstep : evalStmtFuel (F + 1) vecReallocSumWhile
            (mkVecReallocEnv blk nv mv iv jv (BitVec.ofNat 32 k) sv)
          = evalStmtFuel F vecReallocSumWhile
            (mkVecReallocEnv blk nv mv iv jv (BitVec.ofNat 32 (k + 1))
              (sv + BitVec.ofNat 32 k)) := by
        simp [vecReallocSumWhile, evalStmtFuel, evalStmtSuccHandler,
          evalStmtWith, hcond, hbody]
      rw [hstep]
      have hkk1 : mv.toNat - k = (mv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hsum
      simp only [vecSumLoopAux, hgetk] at hsum
      exact ih (k + 1) (sv + BitVec.ofNat 32 k) sout (by omega)
        (fun j hjlo hjhi => hget j (by omega) hjhi) hsum (by omega)
    · have hkk : k = mv.toNat := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "k") (.var "m"))
          (mkVecReallocEnv blk nv mv iv jv (BitVec.ofNat 32 mv.toNat) sv) =
          .ok (.b false) := by
        have hc := vecReallocSumCond_eval blk nv mv mv.toNat iv jv sv hm32
        rw [show decide (mv.toNat < mv.toNat) = false from by simp] at hc
        exact hc
      have hsub : mv.toNat - mv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hsum
      simp only [vecSumLoopAux] at hsum
      cases hsum
      simp only [vecReallocSumWhile, evalStmtFuel, evalStmtSuccHandler,
        evalStmtWith]
      rw [hcond]

/-! ### Whole-function correctness (fuel-generalized, then instantiated) -/

/-- `emit_correct` for `vec_realloc`, at any fuel covering `2 * n`. The
    fill produces indices in the fresh block (existing `Base` facts), the
    `realloc` carries the prefix into the grown block
    (`vecRealloc_preserve`), the extension fill completes the indices
    (`vecFillLoopAux_get` + `vecFillLoopAux_preserve`), the sum folds the
    grown block (`vecSumLoopAux_correct`). The `m = n + n` word addition
    is exact on small inputs (`hnowrap`: no wrap, so `(nv + nv).toNat =
    nv.toNat + nv.toNat`). -/
theorem evalFuncFuel_vecRealloc (F : Nat) (nv : BitVec 32)
    (hm2 : nv.toNat + nv.toNat ≤ F)
    (hnowrap : nv.toNat + nv.toNat < 2 ^ 32) :
    evalFuncFuel F vecReallocFunc [.u32 nv] =
      .ok (.u32 (prefixSumU32
        ((List.range (nv.toNat + nv.toNat)).map (BitVec.ofNat 32))
        (nv.toNat + nv.toNat))) := by
  have hn32 : nv.toNat < 2 ^ 32 := by omega
  have hm32 : (nv + nv).toNat < 2 ^ 32 := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hnowrap]
    exact hnowrap
  have hmvNat : (nv + nv).toNat = nv.toNat + nv.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt hnowrap]
  have nv_eq : nv = BitVec.ofNat 32 nv.toNat :=
    BitVec.eq_of_toNat_eq (by rw [ofNat32_toNat _ hn32])
  have mv_eq : nv + nv = BitVec.ofNat 32 (nv + nv).toNat :=
    BitVec.eq_of_toNat_eq (by rw [ofNat32_toNat _ hm32])
  -- `Base` witness chain (over `Nat`, mirroring `vecReallocFillSumU32_correct`).
  have hfill := vecFillLoopAux_fresh_ok (List.replicate nv.toNat 0) 0
    nv.toNat (by simp)
  obtain ⟨blkA, hfill0⟩ := hfill
  have hliveA : blkA.freed = false :=
    vecFillLoopAux_live _ _ _ _ rfl hfill0
  have hlenFresh : (⟨List.replicate nv.toNat 0, false⟩ : Vec32).val.length
      = 0 + nv.toNat := by simp
  have hgetA : ∀ j, 0 ≤ j → j < nv.toNat →
      vecGet blkA j = .ok (BitVec.ofNat 32 j) := by
    intro j hjlo hjhi
    have hjhi' : j < 0 + nv.toNat := by omega
    exact vecFillLoopAux_get _ 0 nv.toNat _ rfl hlenFresh
      hfill0 j hjlo hjhi'
  have hlenA : blkA.val.length = nv.toNat := by
    have h := vecFillLoopAux_length _ _ _ _ hfill0
    simp at h
    exact h
  obtain ⟨blkB, hcopy0⟩ : ∃ w, vecRealloc blkA (nv.toNat + nv.toNat) = .ok w :=
    ⟨_, vecRealloc_ok blkA (nv.toNat + nv.toNat) hliveA⟩
  have hliveB : blkB.freed = false :=
    vecRealloc_live blkA (nv.toNat + nv.toNat) blkB hcopy0
  have hlenB : blkB.val.length = nv.toNat + nv.toNat :=
    vecRealloc_length blkA (nv.toNat + nv.toNat) blkB hcopy0
  have hgetB : ∀ j, j < nv.toNat →
      vecGet blkB j = .ok (BitVec.ofNat 32 j) := by
    intro j hj
    exact vecRealloc_preserve blkA (nv.toNat + nv.toNat) j _ blkB (by omega)
      (hgetA j (Nat.zero_le _) hj) hcopy0
  obtain ⟨blkC, hext0⟩ := vecFillLoopAux_live_ok blkB nv.toNat nv.toNat
    hliveB (by omega)
  have hliveC : blkC.freed = false :=
    vecFillLoopAux_live _ _ _ _ hliveB hext0
  have hgetC : ∀ j, 0 ≤ j → j < nv.toNat + nv.toNat →
      vecGet blkC j = .ok (BitVec.ofNat 32 j) := by
    intro j hjlo hjhi
    rcases Nat.lt_or_ge j nv.toNat with hj | hj
    · have hhere := hgetB j hj
      exact vecFillLoopAux_preserve _ nv.toNat nv.toNat j _ blkC hj hhere hext0
    · exact vecFillLoopAux_get _ nv.toNat nv.toNat _ hliveB (by omega)
        hext0 j hj (by omega)
  have hsum0 := vecSumLoopAux_correct blkC 0 (nv.toNat + nv.toNat) 0 (by
    intro j hjlo hjhi
    exact hgetC j hjlo (by omega))
  have hrange : List.range' 0 (nv.toNat + nv.toNat) =
      List.range (nv.toNat + nv.toNat) := by
    simp [List.range_eq_range']
  rw [hrange] at hsum0
  have h0 : (0 : BitVec 32) + prefixSumU32
      ((List.range (nv.toNat + nv.toNat)).map (BitVec.ofNat 32))
      (nv.toNat + nv.toNat)
      = prefixSumU32 ((List.range (nv.toNat + nv.toNat)).map
        (BitVec.ofNat 32)) (nv.toNat + nv.toNat) :=
    BitVec.zero_add _
  rw [h0] at hsum0
  have hfree0 : vecFree blkC = .ok ⟨blkC.val, true⟩ :=
    vecFree_ok blkC hliveC
  -- The `m` let evaluates `n + n` (as a lookup fact: simp unfolds
  -- `evalExpr` first, so the folded `evalExpr` equation never fires —
  -- cf. `hn0`/`hjL` below).
  have hmn : envLookup
      [("i", .u32 (BitVec.ofNat 32 0)),
       ("v", .vecVal ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩),
       ("n", .u32 nv)] "n" = some (.u32 nv) := by
    simp [envLookup, show ("n" : String) ≠ "i" by decide,
      show ("n" : String) ≠ "v" by decide]
  -- … and the `j` let reads `n` past the `s`/`m` bindings.
  have hjL : envLookup
      [("s", .u32 (BitVec.ofNat 32 0)), ("m", .u32 (nv + nv)),
       ("i", .u32 (BitVec.ofNat 32 0)),
       ("v", .vecVal ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩),
       ("n", .u32 nv)] "n" = some (.u32 nv) := by
    simp [envLookup, show ("n" : String) ≠ "s" by decide,
      show ("n" : String) ≠ "m" by decide,
      show ("n" : String) ≠ "i" by decide,
      show ("n" : String) ≠ "v" by decide]
  -- The six lets build the grown-block env, `ofNat`-headed throughout
  -- (simp's simprocs normalize `0` to `0#32`); `j` holds the `n` word,
  -- rewritten once to `ofNat` form for the extension-loop invariant.
  have henv : [("k", .u32 (BitVec.ofNat 32 0)),
        ("j", .u32 nv),
        ("s", .u32 (BitVec.ofNat 32 0)),
        ("m", .u32 (nv + nv)),
        ("i", .u32 (BitVec.ofNat 32 0)),
        ("v", .vecVal ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩),
        ("n", .u32 nv)]
      = mkVecReallocEnv ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩
        nv (nv + nv) (BitVec.ofNat 32 0) nv (BitVec.ofNat 32 0)
        (BitVec.ofNat 32 0) := rfl
  have hn0 : envLookup [("n", .u32 nv)] "n" = some (.u32 nv) := rfl
  -- The `realloc` primitive in simp's `%`-normalized form: simp's
  -- `BitVec.toNat_add` simproc rewrites `(nv + nv).toNat` to
  -- `(nv.toNat + nv.toNat) % 2 ^ 32` when the `vrealloc` step unfolds,
  -- so state the fact in that form (via `hnowrap`).
  have hreW : vecRealloc blkA ((nv.toNat + nv.toNat) % 2 ^ 32) = .ok blkB := by
    rw [Nat.mod_eq_of_lt hnowrap]; exact hcopy0
  -- Loop haves match simp's unfolded handler forms (cf. `evalFuncFuel_vec2`).
  cases F with
  | zero =>
    have hF0 : nv.toNat - 0 ≤ 0 := by cir_fuel
    have hE0 : (nv + nv).toNat - nv.toNat ≤ 0 := by
      rw [hmvNat]; cir_fuel
    have hS0 : (nv + nv).toNat - 0 ≤ 0 := by
      rw [hmvNat]; cir_fuel
    -- Word-form loop facts: simp normalizes `BitVec.ofNat 32 nv.toNat`
    -- to `nv` (`BitVec.ofNat_toNat` + `setWidth_eq`, probed), so state
    -- outputs/inputs with `nv` / `nv + nv` and bridge inside via
    -- `← nv_eq` / `← mv_eq`. No `hbridge` needed: `realloc` preserves
    -- `j = nv`, which is already the extension loop's start.
    have hloopF0 : evalStmtWith evalStmtZeroHandler
          vecReallocFillWhile
          (mkVecReallocEnv
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩
            nv (nv + nv) (BitVec.ofNat 32 0) nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
        = .ok (mkVecReallocEnv blkA nv (nv + nv)
            nv nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0), .fellThrough) := by
      have h := vecReallocFillWhile_correct
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv (nv + nv) 0 0 nv
        (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) blkA (Nat.zero_le _)
        (by simp) rfl hn32 hfill0 hF0
      rw [← nv_eq] at h
      exact h
    have hloopE0 : evalStmtWith evalStmtZeroHandler
          vecReallocExtWhile
          (mkVecReallocEnv blkB nv (nv + nv)
            nv nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
        = .ok (mkVecReallocEnv blkC nv (nv + nv)
            nv (nv + nv)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0), .fellThrough) := by
      have hext0' : vecFillLoopAux blkB nv.toNat ((nv + nv).toNat - nv.toNat)
          = .ok blkC := by
        rw [hmvNat, Nat.add_sub_cancel]; exact hext0
      have h := vecReallocExtWhile_correct blkB nv (nv + nv) 0 nv.toNat
        (BitVec.ofNat 32 nv.toNat) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) blkC
        (by rw [hmvNat]; omega)
        (by rw [hlenB, hmvNat]) hliveB hm32 hext0' hE0
      rw [← nv_eq, ← mv_eq] at h
      exact h
    have hloopS0 : evalStmtWith evalStmtZeroHandler
          vecReallocSumWhile
          (mkVecReallocEnv blkC nv (nv + nv)
            nv (nv + nv)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
        = .ok (mkVecReallocEnv blkC nv (nv + nv)
            nv (nv + nv)
            (nv + nv)
            (prefixSumU32 ((List.range (nv.toNat + nv.toNat)).map
              (BitVec.ofNat 32)) (nv.toNat + nv.toNat)), .fellThrough) := by
      have hsum0' : vecSumLoopAux blkC 0 ((nv + nv).toNat - 0) 0 =
          .ok (prefixSumU32 ((List.range (nv.toNat + nv.toNat)).map
            (BitVec.ofNat 32)) (nv.toNat + nv.toNat)) := by
        rw [Nat.sub_zero, hmvNat]; exact hsum0
      have h := vecReallocSumWhile_correct blkC nv (nv + nv) 0 0
        (BitVec.ofNat 32 nv.toNat) (BitVec.ofNat 32 (nv + nv).toNat)
        (BitVec.ofNat 32 0)
        (prefixSumU32 ((List.range (nv.toNat + nv.toNat)).map
          (BitVec.ofNat 32)) (nv.toNat + nv.toNat)) (Nat.zero_le _)
        (by intro j hjlo hjhi; rw [hmvNat] at hjhi; exact hgetC j hjlo hjhi)
        hm32 hsum0' hS0
      rw [← nv_eq, ← mv_eq] at h
      exact h
    have hfreeB := vecReallocEnv_update_v blkC nv (nv + nv)
      nv (nv + nv)
      (nv + nv)
      (prefixSumU32 ((List.range (nv.toNat + nv.toNat)).map
        (BitVec.ofNat 32)) (nv.toNat + nv.toNat)) ⟨blkC.val, true⟩
    have hrets := mkVecReallocEnv_s ⟨blkC.val, true⟩ nv (nv + nv)
      nv (nv + nv)
      (nv + nv)
      (prefixSumU32 ((List.range (nv.toNat + nv.toNat)).map
        (BitVec.ofNat 32)) (nv.toNat + nv.toNat))
    simp [evalFuncFuel, vecReallocFunc, bindArgs, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, litVal, envExtend, hn0, hmn, hjL, vecNew,
      henv, mkVecReallocEnv_m, mkVecReallocEnv_v, vecReallocEnv_update_v,
      hreW, hloopF0, hloopE0, hloopS0, hfree0,
      hfreeB, hrets]
  | succ F =>
    have hFS : nv.toNat - 0 ≤ F + 1 := by cir_fuel
    have hES : (nv + nv).toNat - nv.toNat ≤ F + 1 := by
      rw [hmvNat]; cir_fuel
    have hSS : (nv + nv).toNat - 0 ≤ F + 1 := by
      rw [hmvNat]; cir_fuel
    have hloopFS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          vecReallocFillWhile
          (mkVecReallocEnv
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩
            nv (nv + nv) (BitVec.ofNat 32 0) nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
        = .ok (mkVecReallocEnv blkA nv (nv + nv)
            nv nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0), .fellThrough) := by
      have h := vecReallocFillWhile_correct
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv (nv + nv) (F + 1) 0 nv
        (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) blkA (Nat.zero_le _)
        (by simp) rfl hn32 hfill0 hFS
      rw [← nv_eq] at h
      exact h
    have hloopES : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          vecReallocExtWhile
          (mkVecReallocEnv blkB nv (nv + nv)
            nv nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
        = .ok (mkVecReallocEnv blkC nv (nv + nv)
            nv (nv + nv)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0), .fellThrough) := by
      have hext0' : vecFillLoopAux blkB nv.toNat ((nv + nv).toNat - nv.toNat)
          = .ok blkC := by
        rw [hmvNat, Nat.add_sub_cancel]; exact hext0
      have h := vecReallocExtWhile_correct blkB nv (nv + nv) (F + 1) nv.toNat
        (BitVec.ofNat 32 nv.toNat) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) blkC
        (by rw [hmvNat]; omega)
        (by rw [hlenB, hmvNat]) hliveB hm32 hext0' hES
      rw [← nv_eq, ← mv_eq] at h
      exact h
    have hloopSS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          vecReallocSumWhile
          (mkVecReallocEnv blkC nv (nv + nv)
            nv (nv + nv)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
        = .ok (mkVecReallocEnv blkC nv (nv + nv)
            nv (nv + nv)
            (nv + nv)
            (prefixSumU32 ((List.range (nv.toNat + nv.toNat)).map
              (BitVec.ofNat 32)) (nv.toNat + nv.toNat)), .fellThrough) := by
      have hsum0' : vecSumLoopAux blkC 0 ((nv + nv).toNat - 0) 0 =
          .ok (prefixSumU32 ((List.range (nv.toNat + nv.toNat)).map
            (BitVec.ofNat 32)) (nv.toNat + nv.toNat)) := by
        rw [Nat.sub_zero, hmvNat]; exact hsum0
      have h := vecReallocSumWhile_correct blkC nv (nv + nv) (F + 1) 0
        (BitVec.ofNat 32 nv.toNat) (BitVec.ofNat 32 (nv + nv).toNat)
        (BitVec.ofNat 32 0)
        (prefixSumU32 ((List.range (nv.toNat + nv.toNat)).map
          (BitVec.ofNat 32)) (nv.toNat + nv.toNat)) (Nat.zero_le _)
        (by intro j hjlo hjhi; rw [hmvNat] at hjhi; exact hgetC j hjlo hjhi)
        hm32 hsum0' hSS
      rw [← nv_eq, ← mv_eq] at h
      exact h
    have hfreeB := vecReallocEnv_update_v blkC nv (nv + nv)
      nv (nv + nv)
      (nv + nv)
      (prefixSumU32 ((List.range (nv.toNat + nv.toNat)).map
        (BitVec.ofNat 32)) (nv.toNat + nv.toNat)) ⟨blkC.val, true⟩
    have hrets := mkVecReallocEnv_s ⟨blkC.val, true⟩ nv (nv + nv)
      nv (nv + nv)
      (nv + nv)
      (prefixSumU32 ((List.range (nv.toNat + nv.toNat)).map
        (BitVec.ofNat 32)) (nv.toNat + nv.toNat))
    simp [evalFuncFuel, vecReallocFunc, bindArgs, evalStmtFuel, evalStmtWith,
      evalExpr, litVal, envExtend, hn0, hmn, hjL, vecNew, henv,
      mkVecReallocEnv_m, mkVecReallocEnv_v, vecReallocEnv_update_v,
      hreW, hloopFS, hloopES, hloopSS, hfree0, hfreeB,
      hrets]

/-- `emit_correct` for `vec_realloc` at the default fuel. -/
theorem emit_correct_vecRealloc (nv : BitVec 32)
    (hm : nv.toNat + nv.toNat ≤ EVAL_FUEL)
    (hnowrap : nv.toNat + nv.toNat < 2 ^ 32) :
    evalFunc vecReallocFunc [.u32 nv] = vecReallocFwd nv := by
  have h := evalFuncFuel_vecRealloc EVAL_FUEL nv hm hnowrap
  have hc := vecReallocFillSumU32_correct nv.toNat
  simp only [evalFunc, vecReallocFwd, h, hc, u32_map_ok]

/-- Corollary: `vec_realloc` delivers the `range (n + n)` prefix sum. -/
theorem emit_correct_vecRealloc_ok (nv : BitVec 32) (r : BitVec 32)
    (hm : nv.toNat + nv.toNat ≤ EVAL_FUEL)
    (hnowrap : nv.toNat + nv.toNat < 2 ^ 32)
    (h : vecReallocFillSumU32 nv.toNat = .ok r) :
    evalFunc vecReallocFunc [.u32 nv] = .ok (.u32 r) := by
  rw [emit_correct_vecRealloc nv hm hnowrap]
  unfold vecReallocFwd
  rw [h]
  exact u32_map_ok r
