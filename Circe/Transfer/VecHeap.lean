/-
Circe.Transfer.VecHeap — M3c heap transfers: `vec_realloc` and `vec_alloc_u64`.
Over `Circe.Transfer.VecLeaves`.
-/
import Circe.Transfer.VecLeaves

/-! ## M3c heap transfer: `vec_realloc` (grown block, in-place resize) -/

/-- Memory fill-loop condition reads `i` against `n`. -/
theorem memVecReallocFillCond_eval (blk : Vec32) (nv mv : BitVec 32) (k : Nat)
    (jv kv sv : BitVec 32) (m : Mem) (π : Layout) (h : k < 2 ^ 32) :
    memEvalExpr (.ult (.var "i") (.var "n"))
      (mkVecReallocEnv blk nv mv (BitVec.ofNat 32 k) jv kv sv) m π =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkVecReallocEnv_i blk nv mv (BitVec.ofNat 32 k) jv kv sv
  have hn := mkVecReallocEnv_n blk nv mv (BitVec.ofNat 32 k) jv kv sv
  simp only [memEvalExpr, hi, hn, ofNat32_ult k nv h]

/-- Memory extension-loop condition reads `j` against `m`. -/
theorem memVecReallocExtCond_eval (blk : Vec32) (nv mv : BitVec 32) (k : Nat)
    (iv kv sv : BitVec 32) (m : Mem) (π : Layout) (h : k < 2 ^ 32) :
    memEvalExpr (.ult (.var "j") (.var "m"))
      (mkVecReallocEnv blk nv mv iv (BitVec.ofNat 32 k) kv sv) m π =
      .ok (.b (decide (k < mv.toNat))) := by
  have hj := mkVecReallocEnv_j blk nv mv iv (BitVec.ofNat 32 k) kv sv
  have hm := mkVecReallocEnv_m blk nv mv iv (BitVec.ofNat 32 k) kv sv
  simp only [memEvalExpr, hj, hm, ofNat32_ult k mv h]

/-- Memory sum-loop condition reads `k` against `m`. -/
theorem memVecReallocSumCond_eval (blk : Vec32) (nv mv : BitVec 32) (k : Nat)
    (iv jv sv : BitVec 32) (m : Mem) (π : Layout) (h : k < 2 ^ 32) :
    memEvalExpr (.ult (.var "k") (.var "m"))
      (mkVecReallocEnv blk nv mv iv jv (BitVec.ofNat 32 k) sv) m π =
      .ok (.b (decide (k < mv.toNat))) := by
  have hk := mkVecReallocEnv_k blk nv mv iv jv (BitVec.ofNat 32 k) sv
  have hm := mkVecReallocEnv_m blk nv mv iv jv (BitVec.ofNat 32 k) sv
  simp only [memEvalExpr, hk, hm, ofNat32_ult k mv h]

/-- One memory fill step stores the index and advances (any fuel), with
    `Mem`/`Layout` lockstepped on `v`. -/
theorem memVecReallocFillBody_eval (F : Nat) (blk : Vec32) (nv mv : BitVec 32)
    (k : Nat) (jv kv sv : BitVec 32) (blkMid : Vec32)
    (m : Mem) (a : Addr) (π : Layout) (mMid : Mem)
    (hk32 : k < 2 ^ 32)
    (hset : vecSet blk k (BitVec.ofNat 32 k) = .ok blkMid)
    (hstore : memStore m a a k (BitVec.ofNat 32 k) = .ok mMid)
    (hlay : layoutLookup π "v" = some (a, a)) :
    memEvalStmtFuel F vecReallocFillBody
      (mkVecReallocEnv blk nv mv (BitVec.ofNat 32 k) jv kv sv) m π =
      .ok (((mkVecReallocEnv blkMid nv mv (BitVec.ofNat 32 (k + 1)) jv kv sv,
        mMid, π)), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hi : memEvalExpr (.var "i")
      (mkVecReallocEnv blk nv mv (BitVec.ofNat 32 k) jv kv sv) m π =
      .ok (.u32 (BitVec.ofNat 32 k)) := by
    have h1 := mkVecReallocEnv_i blk nv mv (BitVec.ofNat 32 k) jv kv sv
    simp [memEvalExpr, h1]
  have harr := mkVecReallocEnv_v blk nv mv (BitVec.ofNat 32 k) jv kv sv
  have hset' : vecSet blk (BitVec.ofNat 32 k).toNat (BitVec.ofNat 32 k) =
      .ok blkMid := by rw [hkk]; exact hset
  have hstore' : memStore m a a (BitVec.ofNat 32 k).toNat
      (BitVec.ofNat 32 k) = .ok mMid := by rw [hkk]; exact hstore
  have up1 := vecReallocEnv_update_v blk nv mv (BitVec.ofNat 32 k) jv kv sv
    blkMid
  have hi2 : memEvalExpr (.uadd (.var "i") (.lit (.u32 1#32)))
      (mkVecReallocEnv blkMid nv mv (BitVec.ofNat 32 k) jv kv sv) mMid π =
      .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVecReallocEnv_i blkMid nv mv (BitVec.ofNat 32 k) jv kv sv
    simp only [memEvalExpr, litVal, h1, ofNat32_add_one]
  have up2 := vecReallocEnv_update_i blkMid nv mv (BitVec.ofNat 32 k)
    (BitVec.ofNat 32 (k + 1)) jv kv sv
  cases F <;>
    simp only [vecReallocFillBody, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtWith, hi, harr, hlay, hset', hstore', up1, hi2, up2]

/-- The memory `realloc` step resizes value and block in lockstep (any
    fuel): the size expression runs on memory, `vecRealloc` /
    `memRealloc` agree, the layout pin survives (in-place resize). -/
theorem memVecReallocStep_eval (F : Nat) (blk : Vec32) (nv mv : BitVec 32)
    (iv jv kv sv : BitVec 32) (blkMid : Vec32)
    (m : Mem) (a : Addr) (π : Layout)
    (hlay : layoutLookup π "v" = some (a, a))
    (hfind : memFind m a = some ⟨a, true, blk.val⟩)
    (hlive : blk.freed = false)
    (hre : vecRealloc blk mv.toNat = .ok blkMid) :
    ∃ mMid, memEvalStmtFuel F (.vrealloc "v" (.var "m"))
      (mkVecReallocEnv blk nv mv iv jv kv sv) m π =
      .ok (((mkVecReallocEnv blkMid nv mv iv jv kv sv, mMid, π)),
        .fellThrough) ∧
      memFind mMid a = some ⟨a, true, blkMid.val⟩ := by
  have hm : memEvalExpr (.var "m")
      (mkVecReallocEnv blk nv mv iv jv kv sv) m π = .ok (.u32 mv) := by
    have h1 := mkVecReallocEnv_m blk nv mv iv jv kv sv
    simp [memEvalExpr, h1]
  have harr := mkVecReallocEnv_v blk nv mv iv jv kv sv
  obtain ⟨mMid, hmre, hfindMid⟩ := vrealloc_lockstep m a a blk mv.toNat
    ⟨a, true, blk.val⟩ blkMid hfind rfl rfl rfl hlive hre
  have up := vecReallocEnv_update_v blk nv mv iv jv kv sv blkMid
  have hstep := memEvalStmtFuel_vrealloc F "v" (.var "m")
    (mkVecReallocEnv blk nv mv iv jv kv sv) m π mv a a blk blkMid mMid
    (mkVecReallocEnv blkMid nv mv iv jv kv sv)
    hm harr hlay hre hmre up
  exact ⟨mMid, hstep, hfindMid⟩

/-- One memory extension step stores the index and advances (any fuel). -/
theorem memVecReallocExtBody_eval (F : Nat) (blk : Vec32) (nv mv : BitVec 32)
    (k : Nat) (iv kv sv : BitVec 32) (blkMid : Vec32)
    (m : Mem) (a : Addr) (π : Layout) (mMid : Mem)
    (hk32 : k < 2 ^ 32)
    (hset : vecSet blk k (BitVec.ofNat 32 k) = .ok blkMid)
    (hstore : memStore m a a k (BitVec.ofNat 32 k) = .ok mMid)
    (hlay : layoutLookup π "v" = some (a, a)) :
    memEvalStmtFuel F vecReallocExtBody
      (mkVecReallocEnv blk nv mv iv (BitVec.ofNat 32 k) kv sv) m π =
      .ok (((mkVecReallocEnv blkMid nv mv iv (BitVec.ofNat 32 (k + 1)) kv sv,
        mMid, π)), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hj : memEvalExpr (.var "j")
      (mkVecReallocEnv blk nv mv iv (BitVec.ofNat 32 k) kv sv) m π =
      .ok (.u32 (BitVec.ofNat 32 k)) := by
    have h1 := mkVecReallocEnv_j blk nv mv iv (BitVec.ofNat 32 k) kv sv
    simp [memEvalExpr, h1]
  have harr := mkVecReallocEnv_v blk nv mv iv (BitVec.ofNat 32 k) kv sv
  have hset' : vecSet blk (BitVec.ofNat 32 k).toNat (BitVec.ofNat 32 k) =
      .ok blkMid := by rw [hkk]; exact hset
  have hstore' : memStore m a a (BitVec.ofNat 32 k).toNat
      (BitVec.ofNat 32 k) = .ok mMid := by rw [hkk]; exact hstore
  have up1 := vecReallocEnv_update_v blk nv mv iv (BitVec.ofNat 32 k) kv sv
    blkMid
  have hj2 : memEvalExpr (.uadd (.var "j") (.lit (.u32 1#32)))
      (mkVecReallocEnv blkMid nv mv iv (BitVec.ofNat 32 k) kv sv) mMid π =
      .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVecReallocEnv_j blkMid nv mv iv (BitVec.ofNat 32 k) kv sv
    simp only [memEvalExpr, litVal, h1, ofNat32_add_one]
  have up2 := vecReallocEnv_update_j blkMid nv mv iv (BitVec.ofNat 32 k)
    (BitVec.ofNat 32 (k + 1)) kv sv
  cases F <;>
    simp only [vecReallocExtBody, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtWith, hj, harr, hlay, hset', hstore', up1, hj2, up2]

/-- One memory sum step accumulates `v[k]` and advances (any fuel),
    with `Mem`/`Layout` untouched (reads only). -/
theorem memVecReallocSumBody_eval (F : Nat) (blk : Vec32) (nv mv : BitVec 32)
    (k : Nat) (iv jv sv : BitVec 32)
    (m : Mem) (a : Addr) (π : Layout)
    (hk32 : k < 2 ^ 32)
    (hlay : layoutLookup π "v" = some (a, a))
    (hfind : memFind m a = some ⟨a, true, blk.val⟩)
    (hget : vecGet blk k = .ok (BitVec.ofNat 32 k)) :
    memEvalStmtFuel F vecReallocSumBody
      (mkVecReallocEnv blk nv mv iv jv (BitVec.ofNat 32 k) sv) m π =
      .ok (((mkVecReallocEnv blk nv mv iv jv (BitVec.ofNat 32 (k + 1))
        (sv + BitVec.ofNat 32 k), m, π)), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hload : memLoad m a a (BitVec.ofNat 32 k).toNat =
      .ok (BitVec.ofNat 32 k) := by
    rw [hkk]
    exact memLoad_of_vecGet m a blk k hfind hget
  have hget' : vecGet blk (BitVec.ofNat 32 k).toNat =
      .ok (BitVec.ofNat 32 k) := by rw [hkk]; exact hget
  have hk := mkVecReallocEnv_k blk nv mv iv jv (BitVec.ofNat 32 k) sv
  have hs0 := mkVecReallocEnv_s blk nv mv iv jv (BitVec.ofNat 32 k) sv
  have harr := mkVecReallocEnv_v blk nv mv iv jv (BitVec.ofNat 32 k) sv
  have hs : memEvalExpr (.uadd (.var "s") (.vget "v" (.var "k")))
      (mkVecReallocEnv blk nv mv iv jv (BitVec.ofNat 32 k) sv) m π =
      .ok (.u32 (sv + BitVec.ofNat 32 k)) := by
    -- `hk` (envLookup-headed) avoids the equation-lemma race that a
    -- folded `memEvalExpr` index fact would lose (cf. copy-body `hjl`).
    simp only [memEvalExpr, hs0, hlay, harr, hk, hload, hget',
      beq_self_eq_true, ↓reduceIte]
  have hk2 : memEvalExpr (.uadd (.var "k") (.lit (.u32 1#32)))
      (mkVecReallocEnv blk nv mv iv jv (BitVec.ofNat 32 k)
        (sv + BitVec.ofNat 32 k)) m π =
      .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVecReallocEnv_k blk nv mv iv jv (BitVec.ofNat 32 k)
      (sv + BitVec.ofNat 32 k)
    simp only [memEvalExpr, litVal, h1, ofNat32_add_one]
  have up1 := vecReallocEnv_update_s blk nv mv iv jv (BitVec.ofNat 32 k) sv
    (sv + BitVec.ofNat 32 k)
  have up2 := vecReallocEnv_update_k blk nv mv iv jv (BitVec.ofNat 32 k)
    (BitVec.ofNat 32 (k + 1)) (sv + BitVec.ofNat 32 k)
  cases F <;>
    simp only [vecReallocSumBody, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtWith, hs, hk2, up1, up2]

/-- Fill-loop correctness on memory `[0, n)`: the memory loop runs the
    `Base` fill to completion, lockstepping value and memory. -/
theorem memVecReallocFillWhile_correct (blk : Vec32) (nv mv : BitVec 32)
    (F k : Nat) (jv kv sv : BitVec 32) (blkOut : Vec32)
    (m : Mem) (a : Addr) (π : Layout)
    (hk : k ≤ nv.toNat)
    (hlen : blk.val.length = nv.toNat)
    (hlive : blk.freed = false)
    (hn32 : nv.toNat < 2 ^ 32)
    (hlay : layoutLookup π "v" = some (a, a))
    (hfind : memFind m a = some ⟨a, true, blk.val⟩)
    (hfill : vecFillLoopAux blk k (nv.toNat - k) = .ok blkOut)
    (hF : nv.toNat - k ≤ F) :
    ∃ mOut, memEvalStmtFuel F vecReallocFillWhile
        (mkVecReallocEnv blk nv mv (BitVec.ofNat 32 k) jv kv sv) m π =
      .ok (((mkVecReallocEnv blkOut nv mv (BitVec.ofNat 32 nv.toNat) jv kv sv,
        mOut, π)), .fellThrough) ∧
      memFind mOut a = some ⟨a, true, blkOut.val⟩ ∧
      blkOut.freed = false := by
  induction F generalizing k blk m with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
        (mkVecReallocEnv blk nv mv (BitVec.ofNat 32 nv.toNat) jv kv sv) m π =
        .ok (.b false) := by
      have hc := memVecReallocFillCond_eval blk nv mv nv.toNat jv kv sv m π
        hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hfill
    simp only [vecFillLoopAux] at hfill
    cases hfill
    refine ⟨m, ?_, hfind, hlive⟩
    simp only [vecReallocFillWhile, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtZeroHandler, memEvalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hklen : k < blk.val.length := by omega
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
          (mkVecReallocEnv blk nv mv (BitVec.ofNat 32 k) jv kv sv) m π =
          .ok (.b true) := by
        simpa [hlt] using
          (memVecReallocFillCond_eval blk nv mv k jv kv sv m π hk32)
      have hset : vecSet blk k (BitVec.ofNat 32 k) =
          .ok ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ :=
        vecSet_ok blk k _ hlive hklen
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hfill
      simp only [vecFillLoopAux, hset] at hfill
      obtain ⟨mMid, hstore, hfindMid⟩ := vset_lockstep m a a blk k
        (BitVec.ofNat 32 k) ⟨a, true, blk.val⟩
        ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩
        hfind rfl rfl rfl hlive hset
      have hbody := memVecReallocFillBody_eval F blk nv mv k jv kv sv
        ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ m a π mMid
        hk32 hset hstore hlay
      have hstep : memEvalStmtFuel (F + 1) vecReallocFillWhile
            (mkVecReallocEnv blk nv mv (BitVec.ofNat 32 k) jv kv sv) m π
          = memEvalStmtFuel F vecReallocFillWhile
            (mkVecReallocEnv ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ nv mv
              (BitVec.ofNat 32 (k + 1)) jv kv sv) mMid π := by
        simp [vecReallocFillWhile, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond, hbody]
      rw [hstep]
      have hlenMid : (⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).val.length
          = nv.toNat := by
        show (blk.val.set k (BitVec.ofNat 32 k)).length = nv.toNat
        rw [List.length_set]
        omega
      exact ih ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ (k + 1) mMid
        (by omega) hlenMid rfl hfindMid hfill (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
          (mkVecReallocEnv blk nv mv (BitVec.ofNat 32 nv.toNat) jv kv sv) m π =
          .ok (.b false) := by
        have hc := memVecReallocFillCond_eval blk nv mv nv.toNat jv kv sv m π
          hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hfill
      simp only [vecFillLoopAux] at hfill
      cases hfill
      refine ⟨m, ?_, hfind, hlive⟩
      simp only [vecReallocFillWhile, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith]
      rw [hcond]

/-- Extension-loop correctness on memory `[k, m)`: same shape as the
    fill proof, over the grown bound. -/
theorem memVecReallocExtWhile_correct (blk : Vec32) (nv mv : BitVec 32)
    (F k : Nat) (iv kv sv : BitVec 32) (blkOut : Vec32)
    (m : Mem) (a : Addr) (π : Layout)
    (hk : k ≤ mv.toNat)
    (hlen : blk.val.length = mv.toNat)
    (hlive : blk.freed = false)
    (hm32 : mv.toNat < 2 ^ 32)
    (hlay : layoutLookup π "v" = some (a, a))
    (hfind : memFind m a = some ⟨a, true, blk.val⟩)
    (hfill : vecFillLoopAux blk k (mv.toNat - k) = .ok blkOut)
    (hF : mv.toNat - k ≤ F) :
    ∃ mOut, memEvalStmtFuel F vecReallocExtWhile
        (mkVecReallocEnv blk nv mv iv (BitVec.ofNat 32 k) kv sv) m π =
      .ok (((mkVecReallocEnv blkOut nv mv iv (BitVec.ofNat 32 mv.toNat) kv sv,
        mOut, π)), .fellThrough) ∧
      memFind mOut a = some ⟨a, true, blkOut.val⟩ ∧
      blkOut.freed = false := by
  induction F generalizing k blk m with
  | zero =>
    have hkk : k = mv.toNat := by omega
    subst hkk
    have hcond : memEvalExpr (.ult (.var "j") (.var "m"))
        (mkVecReallocEnv blk nv mv iv (BitVec.ofNat 32 mv.toNat) kv sv) m π =
        .ok (.b false) := by
      have hc := memVecReallocExtCond_eval blk nv mv mv.toNat iv kv sv m π
        hm32
      rw [show decide (mv.toNat < mv.toNat) = false from by simp] at hc
      exact hc
    have hsub : mv.toNat - mv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hfill
    simp only [vecFillLoopAux] at hfill
    cases hfill
    refine ⟨m, ?_, hfind, hlive⟩
    simp only [vecReallocExtWhile, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtZeroHandler, memEvalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < mv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hklen : k < blk.val.length := by omega
      have hcond : memEvalExpr (.ult (.var "j") (.var "m"))
          (mkVecReallocEnv blk nv mv iv (BitVec.ofNat 32 k) kv sv) m π =
          .ok (.b true) := by
        simpa [hlt] using
          (memVecReallocExtCond_eval blk nv mv k iv kv sv m π hk32)
      have hset : vecSet blk k (BitVec.ofNat 32 k) =
          .ok ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ :=
        vecSet_ok blk k _ hlive hklen
      have hkk1 : mv.toNat - k = (mv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hfill
      simp only [vecFillLoopAux, hset] at hfill
      obtain ⟨mMid, hstore, hfindMid⟩ := vset_lockstep m a a blk k
        (BitVec.ofNat 32 k) ⟨a, true, blk.val⟩
        ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩
        hfind rfl rfl rfl hlive hset
      have hbody := memVecReallocExtBody_eval F blk nv mv k iv kv sv
        ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ m a π mMid
        hk32 hset hstore hlay
      have hstep : memEvalStmtFuel (F + 1) vecReallocExtWhile
            (mkVecReallocEnv blk nv mv iv (BitVec.ofNat 32 k) kv sv) m π
          = memEvalStmtFuel F vecReallocExtWhile
            (mkVecReallocEnv ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ nv mv iv
              (BitVec.ofNat 32 (k + 1)) kv sv) mMid π := by
        simp [vecReallocExtWhile, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond, hbody]
      rw [hstep]
      have hlenMid : (⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).val.length
          = mv.toNat := by
        show (blk.val.set k (BitVec.ofNat 32 k)).length = mv.toNat
        rw [List.length_set]
        omega
      exact ih ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ (k + 1) mMid
        (by omega) hlenMid rfl hfindMid hfill (by omega)
    · have hkk : k = mv.toNat := by omega
      subst hkk
      have hcond : memEvalExpr (.ult (.var "j") (.var "m"))
          (mkVecReallocEnv blk nv mv iv (BitVec.ofNat 32 mv.toNat) kv sv) m π =
          .ok (.b false) := by
        have hc := memVecReallocExtCond_eval blk nv mv mv.toNat iv kv sv m π
          hm32
        rw [show decide (mv.toNat < mv.toNat) = false from by simp] at hc
        exact hc
      have hsub : mv.toNat - mv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hfill
      simp only [vecFillLoopAux] at hfill
      cases hfill
      refine ⟨m, ?_, hfind, hlive⟩
      simp only [vecReallocExtWhile, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith]
      rw [hcond]

/-- Sum-loop correctness on memory over the grown block `[k, m)`: runs
    the `Base` sum to completion, leaving `Mem`/`Layout` untouched. -/
theorem memVecReallocSumWhile_correct (blk : Vec32) (nv mv : BitVec 32)
    (F k : Nat) (iv jv sv : BitVec 32) (sout : BitVec 32)
    (m : Mem) (a : Addr) (π : Layout)
    (hk : k ≤ mv.toNat)
    (hget : ∀ j, k ≤ j → j < mv.toNat →
      vecGet blk j = .ok (BitVec.ofNat 32 j))
    (hm32 : mv.toNat < 2 ^ 32)
    (hlay : layoutLookup π "v" = some (a, a))
    (hfind : memFind m a = some ⟨a, true, blk.val⟩)
    (hsum : vecSumLoopAux blk k (mv.toNat - k) sv = .ok sout)
    (hF : mv.toNat - k ≤ F) :
    memEvalStmtFuel F vecReallocSumWhile
      (mkVecReallocEnv blk nv mv iv jv (BitVec.ofNat 32 k) sv) m π =
      .ok (((mkVecReallocEnv blk nv mv iv jv (BitVec.ofNat 32 mv.toNat) sout,
        m, π)), .fellThrough) := by
  induction F generalizing k sv sout with
  | zero =>
    have hkk : k = mv.toNat := by omega
    subst hkk
    have hcond : memEvalExpr (.ult (.var "k") (.var "m"))
        (mkVecReallocEnv blk nv mv iv jv (BitVec.ofNat 32 mv.toNat) sv) m π =
        .ok (.b false) := by
      have hc := memVecReallocSumCond_eval blk nv mv mv.toNat iv jv sv m π
        hm32
      rw [show decide (mv.toNat < mv.toNat) = false from by simp] at hc
      exact hc
    have hsub : mv.toNat - mv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hsum
    simp only [vecSumLoopAux] at hsum
    cases hsum
    simp only [vecReallocSumWhile, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtZeroHandler, memEvalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < mv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hcond : memEvalExpr (.ult (.var "k") (.var "m"))
          (mkVecReallocEnv blk nv mv iv jv (BitVec.ofNat 32 k) sv) m π =
          .ok (.b true) := by
        simpa [hlt] using
          (memVecReallocSumCond_eval blk nv mv k iv jv sv m π hk32)
      have hgetk : vecGet blk k = .ok (BitVec.ofNat 32 k) :=
        hget k (Nat.le_refl _) hlt
      have hbody := memVecReallocSumBody_eval F blk nv mv k iv jv sv
        m a π hk32 hlay hfind hgetk
      have hstep : memEvalStmtFuel (F + 1) vecReallocSumWhile
            (mkVecReallocEnv blk nv mv iv jv (BitVec.ofNat 32 k) sv) m π
          = memEvalStmtFuel F vecReallocSumWhile
            (mkVecReallocEnv blk nv mv iv jv (BitVec.ofNat 32 (k + 1))
              (sv + BitVec.ofNat 32 k)) m π := by
        simp [vecReallocSumWhile, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond, hbody]
      rw [hstep]
      have hkk1 : mv.toNat - k = (mv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hsum
      simp only [vecSumLoopAux, hgetk] at hsum
      exact ih (k + 1) (sv + BitVec.ofNat 32 k) sout (by omega)
        (by intro j hjlo hjhi; exact hget j (by omega) hjhi) hsum (by omega)
    · have hkk : k = mv.toNat := by omega
      subst hkk
      have hcond : memEvalExpr (.ult (.var "k") (.var "m"))
          (mkVecReallocEnv blk nv mv iv jv (BitVec.ofNat 32 mv.toNat) sv) m π =
          .ok (.b false) := by
        have hc := memVecReallocSumCond_eval blk nv mv mv.toNat iv jv sv m π
          hm32
        rw [show decide (mv.toNat < mv.toNat) = false from by simp] at hc
        exact hc
      have hsub : mv.toNat - mv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hsum
      simp only [vecSumLoopAux] at hsum
      cases hsum
      simp only [vecReallocSumWhile, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith]
      rw [hcond]

/-- `memEval` for `vec_realloc` at any fuel covering `2 * n` (mirrors
    `evalFuncFuel_vecRealloc`; the grown block rides alongside in
    lockstep, resized in place by `memRealloc`). -/
theorem memEvalFuncFuel_vecRealloc (F : Nat) (nv : BitVec 32)
    (hm2 : nv.toNat + nv.toNat ≤ F)
    (hnowrap : nv.toNat + nv.toNat < 2 ^ 32) :
    memEvalFuncFuel F vecReallocFunc [.u32 nv] =
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
  -- Simp normalizes `BitVec.ofNat 32 0` to `0#32` in the closing goal;
  -- bridge the loop-rule zeros to match (defeq, proved by `rfl`).
  -- (The fill rule keeps plain-`0` zeros: its goal positions never reach
  -- the `0#32` normal form before the rule fires.)
  have z0 : (BitVec.ofNat 32 0) = (0 : BitVec 32) := rfl
  have z032 : (BitVec.ofNat 32 0) = 0#32 := rfl
  -- `Base` witness chain (memory-independent: verbatim from
  -- `evalFuncFuel_vecRealloc`).
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
  -- Stated unfolded (`⟨0, [], []⟩`): if `emptyMem` unfolds first, the
  -- `bindMemArgs_vecRealloc` match is destroyed and the closing stalls.
  have hb : bindMemArgs [{ name := "n", ty := .u 32, role := .owned }]
      [.u32 nv] (⟨0, [], []⟩ : Mem) =
      some ([("n", .u32 nv)], (⟨0, [], []⟩ : Mem), []) :=
    bindMemArgs_vecRealloc nv
  have hmn : envLookup
      [("i", .u32 (BitVec.ofNat 32 0)),
       ("v", .vecVal ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩),
       ("n", .u32 nv)] "n" = some (.u32 nv) := by
    simp [envLookup, show ("n" : String) ≠ "i" by decide,
      show ("n" : String) ≠ "v" by decide]
  have hjL : envLookup
      [("s", .u32 (BitVec.ofNat 32 0)), ("m", .u32 (nv + nv)),
       ("i", .u32 (BitVec.ofNat 32 0)),
       ("v", .vecVal ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩),
       ("n", .u32 nv)] "n" = some (.u32 nv) := by
    simp [envLookup, show ("n" : String) ≠ "s" by decide,
      show ("n" : String) ≠ "m" by decide,
      show ("n" : String) ≠ "i" by decide,
      show ("n" : String) ≠ "v" by decide]
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
  -- The `realloc` primitive in simp's `%`-normalized form (cf.
  -- `evalFuncFuel_vecRealloc`).
  have hreW : vecRealloc blkA ((nv.toNat + nv.toNat) % 2 ^ 32) = .ok blkB := by
    rw [Nat.mod_eq_of_lt hnowrap]; exact hcopy0
  have hlayV : layoutLookup [("v", 0, 0)] "v" = some (0, 0) :=
    layoutLookup_hit "v" 0 0 []
  have hfindV0 : memFind
      (⟨1, [(0, ⟨0, true,
        List.replicate nv.toNat (BitVec.ofNat 32 0)⟩)], []⟩ : Mem) 0 =
      some ⟨0, true, List.replicate nv.toNat (BitVec.ofNat 32 0)⟩ := by
    simp [memFind]
  cases F with
  | zero =>
    have hF0 : nv.toNat - 0 ≤ 0 := by cir_fuel
    have hE0 : (nv + nv).toNat - nv.toNat ≤ 0 := by
      rw [hmvNat]; cir_fuel
    have hS0 : (nv + nv).toNat - 0 ≤ 0 := by
      rw [hmvNat]; cir_fuel
    obtain ⟨mFill, hfillLoop, hfindFill, hliveFill⟩ :=
      memVecReallocFillWhile_correct
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv (nv + nv) 0 0
        nv (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) blkA
        ⟨1, [(0, ⟨0, true,
          List.replicate nv.toNat (BitVec.ofNat 32 0)⟩)], []⟩ 0 [("v", 0, 0)]
        (Nat.zero_le _) (by simp) rfl hn32 hlayV hfindV0 hfill0 hF0
    have hloopF0 : memEvalStmtWith memEvalStmtZeroHandler
          vecReallocFillWhile
          (mkVecReallocEnv
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩
            nv (nv + nv) (BitVec.ofNat 32 0) nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
          ⟨1, [(0, ⟨0, true,
            List.replicate nv.toNat (BitVec.ofNat 32 0)⟩)], []⟩ [("v", 0, 0)]
        = .ok ((mkVecReallocEnv blkA nv (nv + nv)
            nv nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0), mFill, [("v", 0, 0)]),
          .fellThrough) := by
      have h := hfillLoop
      rw [← nv_eq, z0] at h
      exact h
    obtain ⟨mRe, hmreW, hfindRe⟩ := vrealloc_lockstep mFill 0 0 blkA
      ((nv.toNat + nv.toNat) % 2 ^ 32) ⟨0, true, blkA.val⟩ blkB
      hfindFill rfl rfl rfl hliveFill hreW
    have hext0' : vecFillLoopAux blkB nv.toNat ((nv + nv).toNat - nv.toNat)
        = .ok blkC := by
      rw [hmvNat, Nat.add_sub_cancel]; exact hext0
    obtain ⟨mExt, hloopE_raw, hfindExt, hliveExt⟩ := by
      have h := memVecReallocExtWhile_correct blkB nv (nv + nv) 0 nv.toNat
        (BitVec.ofNat 32 nv.toNat) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) blkC
        mRe 0 [("v", 0, 0)]
        (by rw [hmvNat]; omega)
        (by rw [hlenB, hmvNat]) hliveB hm32 hlayV hfindRe hext0' hE0
      rw [← nv_eq, ← mv_eq, z032] at h
      exact h
    -- Restate in `With`-handler form: the closing simp sees the unfolded
    -- `memEvalStmtWith memEvalStmtZeroHandler` redex (defeq, not
    -- syntactic, so the raw `Fuel`-form equation never fires).
    have hloopE0 : memEvalStmtWith memEvalStmtZeroHandler
          vecReallocExtWhile
          (mkVecReallocEnv blkB nv (nv + nv) nv nv 0#32 0#32)
          mRe [("v", 0, 0)]
        = .ok ((mkVecReallocEnv blkC nv (nv + nv) nv (nv + nv)
            0#32 0#32, mExt, [("v", 0, 0)]),
          .fellThrough) :=
      hloopE_raw
    have hsum0' : vecSumLoopAux blkC 0 ((nv + nv).toNat - 0) 0 =
        .ok (prefixSumU32 ((List.range (nv.toNat + nv.toNat)).map
          (BitVec.ofNat 32)) (nv.toNat + nv.toNat)) := by
      rw [Nat.sub_zero, hmvNat]; exact hsum0
    have hloopS0 : memEvalStmtWith memEvalStmtZeroHandler
          vecReallocSumWhile
          (mkVecReallocEnv blkC nv (nv + nv)
            nv (nv + nv)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
          mExt [("v", 0, 0)]
        = .ok ((mkVecReallocEnv blkC nv (nv + nv)
            nv (nv + nv)
            (nv + nv)
            (prefixSumU32 ((List.range (nv.toNat + nv.toNat)).map
              (BitVec.ofNat 32)) (nv.toNat + nv.toNat)), mExt, [("v", 0, 0)]),
          .fellThrough) := by
      have h := memVecReallocSumWhile_correct blkC nv (nv + nv) 0 0
        (BitVec.ofNat 32 nv.toNat) (BitVec.ofNat 32 (nv + nv).toNat)
        (BitVec.ofNat 32 0)
        (prefixSumU32 ((List.range (nv.toNat + nv.toNat)).map
          (BitVec.ofNat 32)) (nv.toNat + nv.toNat)) mExt 0 [("v", 0, 0)]
        (Nat.zero_le _)
        (by intro j hjlo hjhi; rw [hmvNat] at hjhi; exact hgetC j hjlo hjhi)
        hm32 hlayV hfindExt hsum0' hS0
      rw [← nv_eq, ← mv_eq, z032] at h
      exact h
    obtain ⟨mFree, hmfree, _hfindFree⟩ := vfree_lockstep mExt 0 0 blkC
      ⟨0, true, blkC.val⟩ ⟨blkC.val, true⟩ hfindExt rfl rfl rfl
      hliveExt hfree0
    have huv := vecReallocEnv_update_v blkC nv (nv + nv)
      nv (nv + nv)
      (nv + nv)
      (prefixSumU32 ((List.range (nv.toNat + nv.toNat)).map
        (BitVec.ofNat 32)) (nv.toNat + nv.toNat)) ⟨blkC.val, true⟩
    have hars := mkVecReallocEnv_s ⟨blkC.val, true⟩ nv (nv + nv)
      nv (nv + nv)
      (nv + nv)
      (prefixSumU32 ((List.range (nv.toNat + nv.toNat)).map
        (BitVec.ofNat 32)) (nv.toNat + nv.toNat))
    -- Phased closing: the monolithic simp exposes the loops but its
    -- `memEvalStmtWith` equations race the loop rules, so apply the
    -- extension/sum rules as standalone steps once their redexes exist.
    simp [memEvalFuncFuel, vecReallocFunc, emptyMem, hb, memEvalStmtFuel,
      memEvalStmtZero, memEvalStmtWith, memEvalExpr, litVal, hn0, hmn, hjL,
      vecNew, memAllocData, henv, mkVecReallocEnv_m,
      mkVecReallocEnv_v, vecReallocEnv_update_v,
      hloopF0, hreW, hmreW, hlayV]
    simp only [hloopE0]
    simp only [hloopS0]
    simp [hfree0, hmfree, huv, hars, hlayV, mkVecReallocEnv_v]
  | succ F =>
    have hFS : nv.toNat - 0 ≤ F + 1 := by cir_fuel
    have hES : (nv + nv).toNat - nv.toNat ≤ F + 1 := by
      rw [hmvNat]; cir_fuel
    have hSS : (nv + nv).toNat - 0 ≤ F + 1 := by
      rw [hmvNat]; cir_fuel
    obtain ⟨mFill, hfillLoop, hfindFill, hliveFill⟩ :=
      memVecReallocFillWhile_correct
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv (nv + nv)
        (F + 1) 0
        nv (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) blkA
        ⟨1, [(0, ⟨0, true,
          List.replicate nv.toNat (BitVec.ofNat 32 0)⟩)], []⟩ 0 [("v", 0, 0)]
        (Nat.zero_le _) (by simp) rfl hn32 hlayV hfindV0 hfill0 hFS
    have hloopFS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          vecReallocFillWhile
          (mkVecReallocEnv
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩
            nv (nv + nv) (BitVec.ofNat 32 0) nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
          ⟨1, [(0, ⟨0, true,
            List.replicate nv.toNat (BitVec.ofNat 32 0)⟩)], []⟩ [("v", 0, 0)]
        = .ok ((mkVecReallocEnv blkA nv (nv + nv)
            nv nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0), mFill, [("v", 0, 0)]),
          .fellThrough) := by
      have h := hfillLoop
      rw [← nv_eq, z0] at h
      exact h
    obtain ⟨mRe, hmreW, hfindRe⟩ := vrealloc_lockstep mFill 0 0 blkA
      ((nv.toNat + nv.toNat) % 2 ^ 32) ⟨0, true, blkA.val⟩ blkB
      hfindFill rfl rfl rfl hliveFill hreW
    have hextS' : vecFillLoopAux blkB nv.toNat ((nv + nv).toNat - nv.toNat)
        = .ok blkC := by
      rw [hmvNat, Nat.add_sub_cancel]; exact hext0
    obtain ⟨mExt, hloopE_raw, hfindExt, hliveExt⟩ := by
      have h := memVecReallocExtWhile_correct blkB nv (nv + nv) (F + 1) nv.toNat
        (BitVec.ofNat 32 nv.toNat) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) blkC
        mRe 0 [("v", 0, 0)]
        (by rw [hmvNat]; omega)
        (by rw [hlenB, hmvNat]) hliveB hm32 hlayV hfindRe hextS' hES
      rw [← nv_eq, ← mv_eq, z032] at h
      exact h
    have hloopES : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          vecReallocExtWhile
          (mkVecReallocEnv blkB nv (nv + nv) nv nv 0#32 0#32)
          mRe [("v", 0, 0)]
        = .ok ((mkVecReallocEnv blkC nv (nv + nv) nv (nv + nv)
            0#32 0#32, mExt, [("v", 0, 0)]),
          .fellThrough) :=
      hloopE_raw
    have hsumS' : vecSumLoopAux blkC 0 ((nv + nv).toNat - 0) 0 =
        .ok (prefixSumU32 ((List.range (nv.toNat + nv.toNat)).map
          (BitVec.ofNat 32)) (nv.toNat + nv.toNat)) := by
      rw [Nat.sub_zero, hmvNat]; exact hsum0
    have hloopSS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          vecReallocSumWhile
          (mkVecReallocEnv blkC nv (nv + nv)
            nv (nv + nv)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
          mExt [("v", 0, 0)]
        = .ok ((mkVecReallocEnv blkC nv (nv + nv)
            nv (nv + nv)
            (nv + nv)
            (prefixSumU32 ((List.range (nv.toNat + nv.toNat)).map
              (BitVec.ofNat 32)) (nv.toNat + nv.toNat)), mExt, [("v", 0, 0)]),
          .fellThrough) := by
      have h := memVecReallocSumWhile_correct blkC nv (nv + nv) (F + 1) 0
        (BitVec.ofNat 32 nv.toNat) (BitVec.ofNat 32 (nv + nv).toNat)
        (BitVec.ofNat 32 0)
        (prefixSumU32 ((List.range (nv.toNat + nv.toNat)).map
          (BitVec.ofNat 32)) (nv.toNat + nv.toNat)) mExt 0 [("v", 0, 0)]
        (Nat.zero_le _)
        (by intro j hjlo hjhi; rw [hmvNat] at hjhi; exact hgetC j hjlo hjhi)
        hm32 hlayV hfindExt hsumS' hSS
      rw [← nv_eq, ← mv_eq, z032] at h
      exact h
    obtain ⟨mFree, hmfree, _hfindFree⟩ := vfree_lockstep mExt 0 0 blkC
      ⟨0, true, blkC.val⟩ ⟨blkC.val, true⟩ hfindExt rfl rfl rfl
      hliveExt hfree0
    have huv := vecReallocEnv_update_v blkC nv (nv + nv)
      nv (nv + nv)
      (nv + nv)
      (prefixSumU32 ((List.range (nv.toNat + nv.toNat)).map
        (BitVec.ofNat 32)) (nv.toNat + nv.toNat)) ⟨blkC.val, true⟩
    have hars := mkVecReallocEnv_s ⟨blkC.val, true⟩ nv (nv + nv)
      nv (nv + nv)
      (nv + nv)
      (prefixSumU32 ((List.range (nv.toNat + nv.toNat)).map
        (BitVec.ofNat 32)) (nv.toNat + nv.toNat))
    simp [memEvalFuncFuel, vecReallocFunc, emptyMem, hb, memEvalStmtFuel,
      memEvalStmtWith, memEvalExpr, litVal, hn0, hmn, hjL,
      vecNew, memAllocData, henv, mkVecReallocEnv_m,
      mkVecReallocEnv_v, vecReallocEnv_update_v,
      hloopFS, hreW, hmreW, hlayV]
    simp only [hloopES]
    simp only [hloopSS]
    simp [hfree0, hmfree, huv, hars, hlayV, mkVecReallocEnv_v]

/-- Transfer for `vec_realloc`: both sides equal the grown prefix sum. -/
theorem memTransfer_vecRealloc (F : Nat) (nv : BitVec 32)
    (hm2 : nv.toNat + nv.toNat ≤ F)
    (hnowrap : nv.toNat + nv.toNat < 2 ^ 32)
    (_h : oracleNoalias vecReallocFunc [.u32 nv]) :
    memEvalFuncFuel F vecReallocFunc [.u32 nv] =
      evalFuncFuel F vecReallocFunc [.u32 nv] := by
  rw [memEvalFuncFuel_vecRealloc F nv hm2 hnowrap,
    evalFuncFuel_vecRealloc F nv hm2 hnowrap]

/-! ## M3c heap transfer: `vec_alloc_u64` (single 64-bit block) -/

/-- One memory fill step stores the index and advances (any fuel),
    lockstepping value and 64-bit memory. -/
theorem memVec64FillBody_eval (F : Nat) (blk : Vec64) (nv : BitVec 64)
    (k : Nat) (sv jv : BitVec 64) (blkMid : Vec64)
    (m : Mem) (a : Addr) (π : Layout) (mMid : Mem)
    (_hklen : k < blk.val.length) (hk32 : k < 2 ^ 64)
    (_hlive : blk.freed = false)
    (hset : vecSet64 blk k (BitVec.ofNat 64 k) = .ok blkMid)
    (hstore : memStore64 m a a k (BitVec.ofNat 64 k) = .ok mMid)
    (hlay : layoutLookup π "v" = some (a, a))
    (_hfind : memFind64 m a = some ⟨a, true, blk.val⟩) :
    memEvalStmtFuel F vec64FillBody
        (mkVec64Env blk nv (BitVec.ofNat 64 k) sv jv) m π =
      .ok (((mkVec64Env blkMid nv (BitVec.ofNat 64 (k + 1)) sv jv,
        mMid, π)), .fellThrough) := by
  have hkk : (BitVec.ofNat 64 k).toNat = k := ofNat64_toNat k hk32
  have hi : memEvalExpr (.var "i")
        (mkVec64Env blk nv (BitVec.ofNat 64 k) sv jv) m π =
        .ok (.u64 (BitVec.ofNat 64 k)) := by
    have h1 := mkVec64Env_i blk nv (BitVec.ofNat 64 k) sv jv
    simp [memEvalExpr, h1]
  have harr := mkVec64Env_v blk nv (BitVec.ofNat 64 k) sv jv
  have hset' : vecSet64 blk (BitVec.ofNat 64 k).toNat (BitVec.ofNat 64 k) =
      .ok blkMid := by rw [hkk]; exact hset
  have hstore' : memStore64 m a a (BitVec.ofNat 64 k).toNat
      (BitVec.ofNat 64 k) = .ok mMid := by rw [hkk]; exact hstore
  have up1 := vec64Env_update_v blk nv (BitVec.ofNat 64 k) sv jv blkMid
  have hi2 : memEvalExpr (.uadd (.var "i") (.lit (.u64 1#64)))
        (mkVec64Env blkMid nv (BitVec.ofNat 64 k) sv jv) mMid π =
        .ok (.u64 (BitVec.ofNat 64 (k + 1))) := by
    have h1 := mkVec64Env_i blkMid nv (BitVec.ofNat 64 k) sv jv
    simp only [memEvalExpr, litVal, h1, ofNat64_add_one]
  have up2 := vec64Env_update_i blkMid nv (BitVec.ofNat 64 k)
    (BitVec.ofNat 64 (k + 1)) sv jv
  cases F <;>
    simp only [vec64FillBody, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtWith, hi, harr, hlay, hset', hstore', up1, hi2, up2]

/-- The memory fill-loop condition reads the index against the bound. -/
theorem memVec64FillCond_eval (blk : Vec64) (nv : BitVec 64) (k : Nat)
    (sv jv : BitVec 64) (m : Mem) (π : Layout) (h : k < 2 ^ 64) :
    memEvalExpr (.ult (.var "i") (.var "n"))
        (mkVec64Env blk nv (BitVec.ofNat 64 k) sv jv) m π =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkVec64Env_i blk nv (BitVec.ofNat 64 k) sv jv
  have hn := mkVec64Env_n blk nv (BitVec.ofNat 64 k) sv jv
  simp only [memEvalExpr, hi, hn, ofNat64_ult k nv h]

/-- Fill-loop correctness on 64-bit memory: the memory loop runs the
    `Base` fill to completion, lockstepping value and memory. -/
theorem memVec64FillWhile_correct (blk : Vec64) (nv : BitVec 64)
    (F k : Nat) (sv jv : BitVec 64) (blkOut : Vec64)
    (m : Mem) (a : Addr) (π : Layout)
    (hk : k ≤ nv.toNat)
    (hlen : blk.val.length = nv.toNat)
    (hlive : blk.freed = false)
    (hn32 : nv.toNat < 2 ^ 64)
    (hlay : layoutLookup π "v" = some (a, a))
    (hfind : memFind64 m a = some ⟨a, true, blk.val⟩)
    (hfill : vecFillLoopAux64 blk k (nv.toNat - k) = .ok blkOut)
    (hF : nv.toNat - k ≤ F) :
    ∃ mOut, memEvalStmtFuel F vec64FillWhile
        (mkVec64Env blk nv (BitVec.ofNat 64 k) sv jv) m π =
      .ok (((mkVec64Env blkOut nv (BitVec.ofNat 64 nv.toNat) sv jv,
        mOut, π)), .fellThrough) ∧
      memFind64 mOut a = some ⟨a, true, blkOut.val⟩ ∧
      blkOut.freed = false := by
  induction F generalizing k blk m with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
        (mkVec64Env blk nv (BitVec.ofNat 64 nv.toNat) sv jv) m π =
        .ok (.b false) := by
      have hc := memVec64FillCond_eval blk nv nv.toNat sv jv m π hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hfill
    simp only [vecFillLoopAux64] at hfill
    cases hfill
    refine ⟨m, ?_, hfind, hlive⟩
    simp only [vec64FillWhile, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtZeroHandler, memEvalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 64 := by omega
      have hklen : k < blk.val.length := by omega
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
          (mkVec64Env blk nv (BitVec.ofNat 64 k) sv jv) m π =
          .ok (.b true) := by
        simpa [hlt] using (memVec64FillCond_eval blk nv k sv jv m π hk32)
      have hset : vecSet64 blk k (BitVec.ofNat 64 k) =
          .ok ⟨blk.val.set k (BitVec.ofNat 64 k), false⟩ :=
        vecSet64_ok blk k _ hlive hklen
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hfill
      simp only [vecFillLoopAux64, hset] at hfill
      obtain ⟨mMid, hstore, hfindMid⟩ := vset64_lockstep m a a blk k
        (BitVec.ofNat 64 k) ⟨a, true, blk.val⟩
        ⟨blk.val.set k (BitVec.ofNat 64 k), false⟩
        hfind rfl rfl rfl hlive hset
      have hbody := memVec64FillBody_eval F blk nv k sv jv
        ⟨blk.val.set k (BitVec.ofNat 64 k), false⟩ m a π mMid
        hklen hk32 hlive hset hstore hlay hfind
      have hstep : memEvalStmtFuel (F + 1) vec64FillWhile
            (mkVec64Env blk nv (BitVec.ofNat 64 k) sv jv) m π
          = memEvalStmtFuel F vec64FillWhile
            (mkVec64Env ⟨blk.val.set k (BitVec.ofNat 64 k), false⟩ nv
              (BitVec.ofNat 64 (k + 1)) sv jv) mMid π := by
        simp [vec64FillWhile, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond, hbody]
      rw [hstep]
      have hlenMid : (⟨blk.val.set k (BitVec.ofNat 64 k), false⟩ : Vec64).val.length
          = nv.toNat := by
        show (blk.val.set k (BitVec.ofNat 64 k)).length = nv.toNat
        rw [List.length_set]
        omega
      exact ih ⟨blk.val.set k (BitVec.ofNat 64 k), false⟩ (k + 1) mMid
        (by omega) hlenMid rfl hfindMid hfill (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
          (mkVec64Env blk nv (BitVec.ofNat 64 nv.toNat) sv jv) m π =
          .ok (.b false) := by
        have hc := memVec64FillCond_eval blk nv nv.toNat sv jv m π hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hfill
      simp only [vecFillLoopAux64] at hfill
      cases hfill
      refine ⟨m, ?_, hfind, hlive⟩
      simp only [vec64FillWhile, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith]
      rw [hcond]

/-- One memory sum step accumulates the 64-bit block element and
    advances (any fuel), with `Mem`/`Layout` untouched (reads only). -/
theorem memVec64SumBody_eval (F : Nat) (blk : Vec64) (nv iv sv : BitVec 64)
    (k : Nat) (m : Mem) (a : Addr) (π : Layout)
    (hk32 : k < 2 ^ 64)
    (hlay : layoutLookup π "v" = some (a, a))
    (hfind : memFind64 m a = some ⟨a, true, blk.val⟩)
    (hget : vecGet64 blk k = .ok (BitVec.ofNat 64 k)) :
    memEvalStmtFuel F vec64SumBody
        (mkVec64Env blk nv iv sv (BitVec.ofNat 64 k)) m π =
      .ok (((mkVec64Env blk nv iv (sv + BitVec.ofNat 64 k)
        (BitVec.ofNat 64 (k + 1)), m, π)), .fellThrough) := by
  have hkk : (BitVec.ofNat 64 k).toNat = k := ofNat64_toNat k hk32
  have hload : memLoad64 m a a (BitVec.ofNat 64 k).toNat =
      .ok (BitVec.ofNat 64 k) := by
    rw [hkk]
    exact memLoad64_of_vecGet64 m a blk k hfind hget
  have hget' : vecGet64 blk (BitVec.ofNat 64 k).toNat =
      .ok (BitVec.ofNat 64 k) := by rw [hkk]; exact hget
  have hj := mkVec64Env_j blk nv iv sv (BitVec.ofNat 64 k)
  have hs0 := mkVec64Env_s blk nv iv sv (BitVec.ofNat 64 k)
  have harr := mkVec64Env_v blk nv iv sv (BitVec.ofNat 64 k)
  have hs : memEvalExpr (.uadd (.var "s") (.vget "v" (.var "j")))
        (mkVec64Env blk nv iv sv (BitVec.ofNat 64 k)) m π =
        .ok (.u64 (sv + BitVec.ofNat 64 k)) := by
    simp only [memEvalExpr, hs0, hlay, harr, hj, hload, hget',
      beq_self_eq_true, ↓reduceIte]
  have hj2 : memEvalExpr (.uadd (.var "j") (.lit (.u64 1#64)))
        (mkVec64Env blk nv iv (sv + BitVec.ofNat 64 k)
          (BitVec.ofNat 64 k)) m π =
        .ok (.u64 (BitVec.ofNat 64 (k + 1))) := by
    have h1 := mkVec64Env_j blk nv iv (sv + BitVec.ofNat 64 k)
      (BitVec.ofNat 64 k)
    simp only [memEvalExpr, litVal, h1, ofNat64_add_one]
  have up1 := vec64Env_update_s blk nv iv sv (sv + BitVec.ofNat 64 k)
    (BitVec.ofNat 64 k)
  have up2 := vec64Env_update_j blk nv iv (sv + BitVec.ofNat 64 k)
    (BitVec.ofNat 64 k) (BitVec.ofNat 64 (k + 1))
  cases F <;>
    simp only [vec64SumBody, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtWith, hs, hj2, up1, up2]

/-- The memory sum-loop condition reads the index against the bound. -/
theorem memVec64SumCond_eval (blk : Vec64) (nv iv sv : BitVec 64) (k : Nat)
    (m : Mem) (π : Layout) (h : k < 2 ^ 64) :
    memEvalExpr (.ult (.var "j") (.var "n"))
        (mkVec64Env blk nv iv sv (BitVec.ofNat 64 k)) m π =
      .ok (.b (decide (k < nv.toNat))) := by
  have hj := mkVec64Env_j blk nv iv sv (BitVec.ofNat 64 k)
  have hn := mkVec64Env_n blk nv iv sv (BitVec.ofNat 64 k)
  simp only [memEvalExpr, hj, hn, ofNat64_ult k nv h]

/-- Sum-loop correctness on 64-bit memory: the memory loop runs the
    `Base` sum to completion, leaving `Mem`/`Layout` untouched. -/
theorem memVec64SumWhile_correct (blk : Vec64) (nv : BitVec 64)
    (F k : Nat) (iv sv : BitVec 64) (sout : BitVec 64)
    (m : Mem) (a : Addr) (π : Layout)
    (hk : k ≤ nv.toNat)
    (hget : ∀ j, k ≤ j → j < nv.toNat →
      vecGet64 blk j = .ok (BitVec.ofNat 64 j))
    (hn32 : nv.toNat < 2 ^ 64)
    (hlay : layoutLookup π "v" = some (a, a))
    (hfind : memFind64 m a = some ⟨a, true, blk.val⟩)
    (hsum : vecSumLoopAux64 blk k (nv.toNat - k) sv = .ok sout)
    (hF : nv.toNat - k ≤ F) :
    memEvalStmtFuel F vec64SumWhile
        (mkVec64Env blk nv iv sv (BitVec.ofNat 64 k)) m π =
      .ok (((mkVec64Env blk nv iv sout (BitVec.ofNat 64 nv.toNat), m, π)),
        .fellThrough) := by
  induction F generalizing k sv sout with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : memEvalExpr (.ult (.var "j") (.var "n"))
        (mkVec64Env blk nv iv sv (BitVec.ofNat 64 nv.toNat)) m π =
        .ok (.b false) := by
      have hc := memVec64SumCond_eval blk nv iv sv nv.toNat m π hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hsum
    simp only [vecSumLoopAux64] at hsum
    cases hsum
    simp only [vec64SumWhile, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtZeroHandler, memEvalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 64 := by omega
      have hcond : memEvalExpr (.ult (.var "j") (.var "n"))
          (mkVec64Env blk nv iv sv (BitVec.ofNat 64 k)) m π =
          .ok (.b true) := by
        simpa [hlt] using (memVec64SumCond_eval blk nv iv sv k m π hk32)
      have hgetk : vecGet64 blk k = .ok (BitVec.ofNat 64 k) :=
        hget k (Nat.le_refl _) hlt
      have hbody := memVec64SumBody_eval F blk nv iv sv k m a π hk32
        hlay hfind hgetk
      have hstep : memEvalStmtFuel (F + 1) vec64SumWhile
            (mkVec64Env blk nv iv sv (BitVec.ofNat 64 k)) m π
          = memEvalStmtFuel F vec64SumWhile
            (mkVec64Env blk nv iv (sv + BitVec.ofNat 64 k)
              (BitVec.ofNat 64 (k + 1))) m π := by
        simp [vec64SumWhile, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond, hbody]
      rw [hstep]
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hsum
      have hgetk' : vecGet64 blk k = .ok (BitVec.ofNat 64 k) :=
        hget k (Nat.le_refl _) hlt
      simp only [vecSumLoopAux64, hgetk'] at hsum
      exact ih (k + 1) (sv + BitVec.ofNat 64 k) sout (by omega)
        (by intro j hjlo hjhi; exact hget j (by omega) hjhi) hsum (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : memEvalExpr (.ult (.var "j") (.var "n"))
          (mkVec64Env blk nv iv sv (BitVec.ofNat 64 nv.toNat)) m π =
          .ok (.b false) := by
        have hc := memVec64SumCond_eval blk nv iv sv nv.toNat m π hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hsum
      simp only [vecSumLoopAux64] at hsum
      cases hsum
      simp only [vec64SumWhile, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith]
      rw [hcond]


/-- `memEval` for `vec_alloc_u64` at any fuel covering `n` (mirrors
    `evalFuncFuel_vec64`; the single 64-bit block rides alongside in
    lockstep). -/
theorem memEvalFuncFuel_vec64 (F : Nat) (nv : BitVec 64)
    (hn : nv.toNat ≤ F) (hn32 : nv.toNat < 2 ^ 64) :
    memEvalFuncFuel F vec64Func [.u64 nv] =
      .ok (.u64 (prefixSumU64 ((List.range nv.toNat).map (BitVec.ofNat 64))
        nv.toNat)) := by
  -- Stated unfolded (`⟨0, [], []⟩`): if `emptyMem` unfolds first, the
  -- `bindMemArgs_vec64` match is destroyed and the closing stalls.
  have hb : bindMemArgs [{ name := "n", ty := .u 64, role := .owned }]
      [.u64 nv] (⟨0, [], []⟩ : Mem) =
      some ([("n", .u64 nv)], (⟨0, [], []⟩ : Mem), []) :=
    bindMemArgs_vec64 nv
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
  have hlayV : layoutLookup [("v", 0, 0)] "v" = some (0, 0) := by
    simp [layoutLookup]
  have hfindV : memFind64 ⟨1, [], [(0, ⟨0, true,
      List.replicate nv.toNat (BitVec.ofNat 64 0)⟩)]⟩ 0 =
      some ⟨0, true,
        List.replicate nv.toNat (BitVec.ofNat 64 0)⟩ := by
    simp [memFind64]
  have hn0 : envLookup [("n", .u64 nv)] "n" = some (.u64 nv) := rfl
  have hfree0 : vecFree64 blkOut = .ok ⟨blkOut.val, true⟩ :=
    vecFree64_ok blkOut hliveOut
  cases F with
  | zero =>
    obtain ⟨mFill, hfillLoop, hfindFill, _hliveFill⟩ :=
      memVec64FillWhile_correct
        ⟨List.replicate nv.toNat (BitVec.ofNat 64 0), false⟩ nv 0 0
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) blkOut
        ⟨1, [], [(0, ⟨0, true,
          List.replicate nv.toNat (BitVec.ofNat 64 0)⟩)]⟩ 0 [("v", 0, 0)]
        (Nat.zero_le _) (by simp) rfl hn32 hlayV hfindV hfill0 (by cir_fuel)
    have hloopF0 : memEvalStmtWith memEvalStmtZeroHandler
          vec64FillWhile
          [("j", .u64 0), ("s", .u64 0), ("i", .u64 0),
           ("v", .vecVal64 ⟨List.replicate nv.toNat 0, false⟩),
           ("n", .u64 nv)]
          ⟨1, [], [(0, ⟨0, true, List.replicate nv.toNat 0⟩)]⟩
          [("v", 0, 0)]
        = .ok ((mkVec64Env blkOut nv (BitVec.ofNat 64 nv.toNat)
            (BitVec.ofNat 64 0) (BitVec.ofNat 64 0), mFill, [("v", 0, 0)]),
          .fellThrough) :=
      hfillLoop
    have hloopS0 : memEvalStmtWith memEvalStmtZeroHandler
          vec64SumWhile
          (mkVec64Env blkOut nv (BitVec.ofNat 64 nv.toNat)
            (BitVec.ofNat 64 0) (BitVec.ofNat 64 0))
          mFill [("v", 0, 0)]
        = .ok ((mkVec64Env blkOut nv (BitVec.ofNat 64 nv.toNat)
            (prefixSumU64 ((List.range nv.toNat).map (BitVec.ofNat 64))
              nv.toNat)
            (BitVec.ofNat 64 nv.toNat), mFill, [("v", 0, 0)]),
          .fellThrough) :=
      memVec64SumWhile_correct blkOut nv 0 0 (BitVec.ofNat 64 nv.toNat) _ _
        mFill 0 [("v", 0, 0)]
        (Nat.zero_le _)
        (by intro j hjlo hjhi; exact hgetOut j hjlo hjhi) hn32 hlayV
        hfindFill hsum0 (by cir_fuel)
    obtain ⟨mFree, hmfree, _hfindFree⟩ := vfree64_lockstep mFill 0 0 blkOut
      ⟨0, true, blkOut.val⟩ ⟨blkOut.val, true⟩ hfindFill rfl rfl rfl
      hliveOut hfree0
    have huv := vec64Env_update_v blkOut nv (BitVec.ofNat 64 nv.toNat)
      (prefixSumU64 ((List.range nv.toNat).map (BitVec.ofNat 64)) nv.toNat)
      (BitVec.ofNat 64 nv.toNat) ⟨blkOut.val, true⟩
    have harv := mkVec64Env_v blkOut nv (BitVec.ofNat 64 nv.toNat)
      (prefixSumU64 ((List.range nv.toNat).map (BitVec.ofNat 64)) nv.toNat)
      (BitVec.ofNat 64 nv.toNat)
    have hars := mkVec64Env_s ⟨blkOut.val, true⟩ nv
      (BitVec.ofNat 64 nv.toNat)
      (prefixSumU64 ((List.range nv.toNat).map (BitVec.ofNat 64)) nv.toNat)
      (BitVec.ofNat 64 nv.toNat)
    simp only [memEvalFuncFuel, vec64Func, emptyMem, hb, memEvalStmtFuel,
      memEvalStmtZero, memEvalStmtWith, memEvalExpr, litVal, hn0, vecNew64,
      memAllocData64, Nat.reduceAdd]
    simp only [hloopF0, hloopS0, hfree0,
      hmfree, huv, harv, hars, hlayV]
  | succ F =>
    obtain ⟨mFill, hfillLoop, hfindFill, _hliveFill⟩ :=
      memVec64FillWhile_correct
        ⟨List.replicate nv.toNat (BitVec.ofNat 64 0), false⟩ nv (F + 1) 0
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) blkOut
        ⟨1, [], [(0, ⟨0, true,
          List.replicate nv.toNat (BitVec.ofNat 64 0)⟩)]⟩ 0 [("v", 0, 0)]
        (Nat.zero_le _) (by simp) rfl hn32 hlayV hfindV hfill0 (by cir_fuel)
    have hloopFS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          vec64FillWhile
          [("j", .u64 0), ("s", .u64 0), ("i", .u64 0),
           ("v", .vecVal64 ⟨List.replicate nv.toNat 0, false⟩),
           ("n", .u64 nv)]
          ⟨1, [], [(0, ⟨0, true, List.replicate nv.toNat 0⟩)]⟩
          [("v", 0, 0)]
        = .ok ((mkVec64Env blkOut nv (BitVec.ofNat 64 nv.toNat)
            (BitVec.ofNat 64 0) (BitVec.ofNat 64 0), mFill, [("v", 0, 0)]),
          .fellThrough) :=
      hfillLoop
    have hloopSS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          vec64SumWhile
          (mkVec64Env blkOut nv (BitVec.ofNat 64 nv.toNat)
            (BitVec.ofNat 64 0) (BitVec.ofNat 64 0))
          mFill [("v", 0, 0)]
        = .ok ((mkVec64Env blkOut nv (BitVec.ofNat 64 nv.toNat)
            (prefixSumU64 ((List.range nv.toNat).map (BitVec.ofNat 64))
              nv.toNat)
            (BitVec.ofNat 64 nv.toNat), mFill, [("v", 0, 0)]),
          .fellThrough) :=
      memVec64SumWhile_correct blkOut nv (F + 1) 0 (BitVec.ofNat 64 nv.toNat)
        _ _ mFill 0 [("v", 0, 0)] (Nat.zero_le _)
        (by intro j hjlo hjhi; exact hgetOut j hjlo hjhi) hn32 hlayV
        hfindFill hsum0 (by cir_fuel)
    obtain ⟨mFree, hmfree, _hfindFree⟩ := vfree64_lockstep mFill 0 0 blkOut
      ⟨0, true, blkOut.val⟩ ⟨blkOut.val, true⟩ hfindFill rfl rfl rfl
      hliveOut hfree0
    have huv := vec64Env_update_v blkOut nv (BitVec.ofNat 64 nv.toNat)
      (prefixSumU64 ((List.range nv.toNat).map (BitVec.ofNat 64)) nv.toNat)
      (BitVec.ofNat 64 nv.toNat) ⟨blkOut.val, true⟩
    have harv := mkVec64Env_v blkOut nv (BitVec.ofNat 64 nv.toNat)
      (prefixSumU64 ((List.range nv.toNat).map (BitVec.ofNat 64)) nv.toNat)
      (BitVec.ofNat 64 nv.toNat)
    have hars := mkVec64Env_s ⟨blkOut.val, true⟩ nv
      (BitVec.ofNat 64 nv.toNat)
      (prefixSumU64 ((List.range nv.toNat).map (BitVec.ofNat 64)) nv.toNat)
      (BitVec.ofNat 64 nv.toNat)
    simp only [memEvalFuncFuel, vec64Func, emptyMem, hb, memEvalStmtFuel,
      memEvalStmtWith, memEvalExpr, litVal, hn0, vecNew64,
      memAllocData64, Nat.reduceAdd]
    simp only [hloopFS, hloopSS, hfree0,
      hmfree, huv, harv, hars, hlayV]

/-- Transfer for `vec_alloc_u64`: both sides equal the prefix sum. -/
theorem memTransfer_vec64 (F : Nat) (nv : BitVec 64)
    (hn : nv.toNat ≤ F) (hn32 : nv.toNat < 2 ^ 64)
    (_h : oracleNoalias vec64Func [.u64 nv]) :
    memEvalFuncFuel F vec64Func [.u64 nv] =
      evalFuncFuel F vec64Func [.u64 nv] := by
  rw [memEvalFuncFuel_vec64 F nv hn hn32, evalFuncFuel_vec64 F nv hn hn32]

