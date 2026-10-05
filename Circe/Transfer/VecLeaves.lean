/-
Circe.Transfer.VecLeaves — `vec_alloc` and `vec_copy_sum` transfers.
Over `Circe.Transfer.Core`.
-/
import Circe.Transfer.Core

/-! ## `vec_alloc` transfer -/

/-- `vec_alloc` binding: the bound is owned scalar, empty layout. -/
theorem bindMemArgs_vec (nv : BitVec 32) :
    bindMemArgs [{ name := "n", ty := .u 32, role := .owned }]
      [.u32 nv] ⟨0, [], []⟩ =
      some ([("n", .u32 nv)], ⟨0, [], []⟩, []) := by
  rfl

/-- `vec_alloc` entry footprints are empty (trivially disjoint). -/
theorem oracleNoalias_vec (nv : BitVec 32) :
    oracleNoalias vecFunc [.u32 nv] := by
  have hb : bindMemArgs vecFunc.args [.u32 nv] emptyMem =
      some ([("n", .u32 nv)], emptyMem, []) := by
    show bindMemArgs [{ name := "n", ty := .u 32, role := .owned }]
      [.u32 nv] ⟨0, [], []⟩ = some ([("n", .u32 nv)], ⟨0, [], []⟩, [])
    exact bindMemArgs_vec nv
  have hn : LayoutNoAlias ([] : Layout) := layoutNoAlias_nil
  exact ⟨_, _, _, hb, hn⟩

/-- One memory fill step stores the index and advances (any fuel:
    loop-free), lockstepping value and memory. -/
theorem memVecFillBody_eval (F : Nat) (blk : Vec32) (nv : BitVec 32)
    (k : Nat) (sv jv : BitVec 32) (blkMid : Vec32)
    (m : Mem) (a : Addr) (π : Layout) (mMid : Mem)
    (_hklen : k < blk.val.length) (hk32 : k < 2 ^ 32)
    (_hlive : blk.freed = false)
    (hset : vecSet blk k (BitVec.ofNat 32 k) = .ok blkMid)
    (hstore : memStore m a a k (BitVec.ofNat 32 k) = .ok mMid)
    (hlay : layoutLookup π "v" = some (a, a))
    (_hfind : memFind m a = some ⟨a, true, blk.val⟩) :
    memEvalStmtFuel F vecFillBody
        (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) m π =
      .ok (((mkVecEnv blkMid nv (BitVec.ofNat 32 (k + 1)) sv jv,
        mMid, π)), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hi : memEvalExpr (.var "i")
        (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) m π =
        .ok (.u32 (BitVec.ofNat 32 k)) := by
    have h1 := mkVecEnv_i blk nv (BitVec.ofNat 32 k) sv jv
    simp [memEvalExpr, h1]
  have harr := mkVecEnv_v blk nv (BitVec.ofNat 32 k) sv jv
  have hset' : vecSet blk (BitVec.ofNat 32 k).toNat (BitVec.ofNat 32 k) =
      .ok blkMid := by rw [hkk]; exact hset
  have hstore' : memStore m a a (BitVec.ofNat 32 k).toNat
      (BitVec.ofNat 32 k) = .ok mMid := by rw [hkk]; exact hstore
  have up1 : envUpdate (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) "v"
      (.vecVal blkMid) =
      some (mkVecEnv blkMid nv (BitVec.ofNat 32 k) sv jv) :=
    vecEnv_update_v blk nv (BitVec.ofNat 32 k) sv jv blkMid
  have hi2 : memEvalExpr (.uadd (.var "i") (.lit (.u32 1#32)))
        (mkVecEnv blkMid nv (BitVec.ofNat 32 k) sv jv) mMid π =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVecEnv_i blkMid nv (BitVec.ofNat 32 k) sv jv
    simp only [memEvalExpr, litVal, h1, ofNat32_add_one]
  have up2 := vecEnv_update_i blkMid nv (BitVec.ofNat 32 k)
    (BitVec.ofNat 32 (k + 1)) sv jv
  cases F <;>
    simp only [vecFillBody, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtWith, hi, harr, hlay, hset', hstore', up1, hi2, up2]

/-- The memory fill-loop condition reads the index against the bound. -/
theorem memVecFillCond_eval (blk : Vec32) (nv : BitVec 32) (k : Nat)
    (sv jv : BitVec 32) (m : Mem) (π : Layout) (h : k < 2 ^ 32) :
    memEvalExpr (.ult (.var "i") (.var "n"))
        (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) m π =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkVecEnv_i blk nv (BitVec.ofNat 32 k) sv jv
  have hn := mkVecEnv_n blk nv (BitVec.ofNat 32 k) sv jv
  simp only [memEvalExpr, hi, hn, ofNat32_ult k nv h]

/-- Fill-loop correctness on memory: the memory loop runs the `Base`
    fill to completion, lockstepping value and memory (the block always
    mirrors the value). -/
theorem memVecFillWhile_correct (blk : Vec32) (nv : BitVec 32)
    (F k : Nat) (sv jv : BitVec 32) (blkOut : Vec32)
    (m : Mem) (a : Addr) (π : Layout)
    (hk : k ≤ nv.toNat)
    (hlen : blk.val.length = nv.toNat)
    (hlive : blk.freed = false)
    (hn32 : nv.toNat < 2 ^ 32)
    (hlay : layoutLookup π "v" = some (a, a))
    (hfind : memFind m a = some ⟨a, true, blk.val⟩)
    (hfill : vecFillLoopAux blk k (nv.toNat - k) = .ok blkOut)
    (hF : nv.toNat - k ≤ F) :
    ∃ mOut, memEvalStmtFuel F vecFillWhile
        (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) m π =
      .ok (((mkVecEnv blkOut nv (BitVec.ofNat 32 nv.toNat) sv jv,
        mOut, π)), .fellThrough) ∧
      memFind mOut a = some ⟨a, true, blkOut.val⟩ ∧
      blkOut.freed = false := by
  induction F generalizing k blk m with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
        (mkVecEnv blk nv (BitVec.ofNat 32 nv.toNat) sv jv) m π =
        .ok (.b false) := by
      have hc := memVecFillCond_eval blk nv nv.toNat sv jv m π hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hfill
    simp only [vecFillLoopAux] at hfill
    cases hfill
    refine ⟨m, ?_, hfind, hlive⟩
    simp only [vecFillWhile, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtZeroHandler, memEvalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hklen : k < blk.val.length := by omega
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
          (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) m π =
          .ok (.b true) := by
        simpa [hlt] using (memVecFillCond_eval blk nv k sv jv m π hk32)
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
      have hbody := memVecFillBody_eval F blk nv k sv jv
        ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ m a π mMid
        hklen hk32 hlive hset hstore hlay hfind
      have hstep : memEvalStmtFuel (F + 1) vecFillWhile
            (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) m π
          = memEvalStmtFuel F vecFillWhile
            (mkVecEnv ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ nv
              (BitVec.ofNat 32 (k + 1)) sv jv) mMid π := by
        simp [vecFillWhile, memEvalStmtFuel, memEvalSuccHandler,
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
          (mkVecEnv blk nv (BitVec.ofNat 32 nv.toNat) sv jv) m π =
          .ok (.b false) := by
        have hc := memVecFillCond_eval blk nv nv.toNat sv jv m π hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hfill
      simp only [vecFillLoopAux] at hfill
      cases hfill
      refine ⟨m, ?_, hfind, hlive⟩
      simp only [vecFillWhile, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith]
      rw [hcond]

/-- One memory sum step accumulates the block element and advances
    (any fuel), with `Mem`/`Layout` untouched (reads only). -/
theorem memVecSumBody_eval (F : Nat) (blk : Vec32) (nv iv sv : BitVec 32)
    (k : Nat) (m : Mem) (a : Addr) (π : Layout)
    (hk32 : k < 2 ^ 32)
    (hlay : layoutLookup π "v" = some (a, a))
    (hfind : memFind m a = some ⟨a, true, blk.val⟩)
    (hget : vecGet blk k = .ok (BitVec.ofNat 32 k)) :
    memEvalStmtFuel F vecSumBody
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) m π =
      .ok (((mkVecEnv blk nv iv (sv + BitVec.ofNat 32 k)
        (BitVec.ofNat 32 (k + 1)), m, π)), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hload : memLoad m a a (BitVec.ofNat 32 k).toNat =
      .ok (BitVec.ofNat 32 k) := by
    rw [hkk]
    exact memLoad_of_vecGet m a blk k hfind hget
  have hget' : vecGet blk (BitVec.ofNat 32 k).toNat =
      .ok (BitVec.ofNat 32 k) := by rw [hkk]; exact hget
  have hj := mkVecEnv_j blk nv iv sv (BitVec.ofNat 32 k)
  have hs0 := mkVecEnv_s blk nv iv sv (BitVec.ofNat 32 k)
  have harr := mkVecEnv_v blk nv iv sv (BitVec.ofNat 32 k)
  have hs : memEvalExpr (.uadd (.var "s") (.vget "v" (.var "j")))
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) m π =
        .ok (.u32 (sv + BitVec.ofNat 32 k)) := by
    simp only [memEvalExpr, hs0, hlay, harr, hj, hload, hget',
      beq_self_eq_true, ↓reduceIte]
  have hj2 : memEvalExpr (.uadd (.var "j") (.lit (.u32 1#32)))
        (mkVecEnv blk nv iv (sv + BitVec.ofNat 32 k)
          (BitVec.ofNat 32 k)) m π =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVecEnv_j blk nv iv (sv + BitVec.ofNat 32 k)
      (BitVec.ofNat 32 k)
    simp only [memEvalExpr, litVal, h1, ofNat32_add_one]
  have up1 := vecEnv_update_s blk nv iv sv (sv + BitVec.ofNat 32 k)
    (BitVec.ofNat 32 k)
  have up2 := vecEnv_update_j blk nv iv (sv + BitVec.ofNat 32 k)
    (BitVec.ofNat 32 k) (BitVec.ofNat 32 (k + 1))
  cases F <;>
    simp only [vecSumBody, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtWith, hs, hj2, up1, up2]

/-- The memory sum-loop condition reads the index against the bound. -/
theorem memVecSumCond_eval (blk : Vec32) (nv iv sv : BitVec 32) (k : Nat)
    (m : Mem) (π : Layout) (h : k < 2 ^ 32) :
    memEvalExpr (.ult (.var "j") (.var "n"))
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) m π =
      .ok (.b (decide (k < nv.toNat))) := by
  have hj := mkVecEnv_j blk nv iv sv (BitVec.ofNat 32 k)
  have hn := mkVecEnv_n blk nv iv sv (BitVec.ofNat 32 k)
  simp only [memEvalExpr, hj, hn, ofNat32_ult k nv h]

/-- Sum-loop correctness on memory: the memory loop runs the `Base`
    sum to completion, leaving `Mem`/`Layout` untouched. -/
theorem memVecSumWhile_correct (blk : Vec32) (nv : BitVec 32)
    (F k : Nat) (iv sv : BitVec 32) (sout : BitVec 32)
    (m : Mem) (a : Addr) (π : Layout)
    (hk : k ≤ nv.toNat)
    (hget : ∀ j, k ≤ j → j < nv.toNat →
      vecGet blk j = .ok (BitVec.ofNat 32 j))
    (hn32 : nv.toNat < 2 ^ 32)
    (hlay : layoutLookup π "v" = some (a, a))
    (hfind : memFind m a = some ⟨a, true, blk.val⟩)
    (hsum : vecSumLoopAux blk k (nv.toNat - k) sv = .ok sout)
    (hF : nv.toNat - k ≤ F) :
    memEvalStmtFuel F vecSumWhile
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) m π =
      .ok (((mkVecEnv blk nv iv sout (BitVec.ofNat 32 nv.toNat), m, π)),
        .fellThrough) := by
  induction F generalizing k sv sout with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : memEvalExpr (.ult (.var "j") (.var "n"))
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 nv.toNat)) m π =
        .ok (.b false) := by
      have hc := memVecSumCond_eval blk nv iv sv nv.toNat m π hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hsum
    simp only [vecSumLoopAux] at hsum
    cases hsum
    simp only [vecSumWhile, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtZeroHandler, memEvalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hcond : memEvalExpr (.ult (.var "j") (.var "n"))
          (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) m π =
          .ok (.b true) := by
        simpa [hlt] using (memVecSumCond_eval blk nv iv sv k m π hk32)
      have hgetk : vecGet blk k = .ok (BitVec.ofNat 32 k) :=
        hget k (Nat.le_refl _) hlt
      have hbody := memVecSumBody_eval F blk nv iv sv k m a π hk32
        hlay hfind hgetk
      have hstep : memEvalStmtFuel (F + 1) vecSumWhile
            (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) m π
          = memEvalStmtFuel F vecSumWhile
            (mkVecEnv blk nv iv (sv + BitVec.ofNat 32 k)
              (BitVec.ofNat 32 (k + 1))) m π := by
        simp [vecSumWhile, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond, hbody]
      rw [hstep]
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hsum
      have hgetk' : vecGet blk k = .ok (BitVec.ofNat 32 k) :=
        hget k (Nat.le_refl _) hlt
      simp only [vecSumLoopAux, hgetk'] at hsum
      exact ih (k + 1) (sv + BitVec.ofNat 32 k) sout (by omega)
        (by intro j hjlo hjhi; exact hget j (by omega) hjhi) hsum (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : memEvalExpr (.ult (.var "j") (.var "n"))
          (mkVecEnv blk nv iv sv (BitVec.ofNat 32 nv.toNat)) m π =
          .ok (.b false) := by
        have hc := memVecSumCond_eval blk nv iv sv nv.toNat m π hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hsum
      simp only [vecSumLoopAux] at hsum
      cases hsum
      simp only [vecSumWhile, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith]
      rw [hcond]

/-- `memEval` for `vec_alloc` at any fuel covering `n` (mirrors
    `evalFuncFuel_vec`; memory locksteps the value). -/
theorem memEvalFuncFuel_vec (F : Nat) (nv : BitVec 32)
    (hn : nv.toNat ≤ F) (hn32 : nv.toNat < 2 ^ 32) :
    memEvalFuncFuel F vecFunc [.u32 nv] =
      .ok (.u32 (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
        nv.toNat)) := by
  have hb := bindMemArgs_vec nv
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
  have hlayV : layoutLookup [("v", 0, 0)] "v" = some (0, 0) := by
    simp [layoutLookup]
  have hfindV : memFind ⟨1, [(0, ⟨0, true,
      List.replicate nv.toNat (BitVec.ofNat 32 0)⟩)], []⟩ 0 =
      some ⟨0, true,
        List.replicate nv.toNat (BitVec.ofNat 32 0)⟩ := by
    simp [memFind]
  have hn0 : envLookup [("n", .u32 nv)] "n" = some (.u32 nv) := rfl
  have hfree0 : vecFree blkOut = .ok ⟨blkOut.val, true⟩ :=
    vecFree_ok blkOut hliveOut
  cases F with
  | zero =>
    obtain ⟨mFill, hfillLoop, hfindFill, _hliveFill⟩ :=
      memVecFillWhile_correct
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv 0 0
        (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) blkOut
        ⟨1, [(0, ⟨0, true,
          List.replicate nv.toNat (BitVec.ofNat 32 0)⟩)], []⟩ 0 [("v", 0, 0)]
        (Nat.zero_le _) (by simp) rfl hn32 hlayV hfindV hfill0 (by cir_fuel)
    have hloopF0 : memEvalStmtWith memEvalStmtZeroHandler
          vecFillWhile
          [("j", .u32 0), ("s", .u32 0), ("i", .u32 0),
           ("v", .vecVal ⟨List.replicate nv.toNat 0, false⟩),
           ("n", .u32 nv)]
          ⟨1, [(0, ⟨0, true, List.replicate nv.toNat 0⟩)], []⟩
          [("v", 0, 0)]
        = .ok ((mkVecEnv blkOut nv (BitVec.ofNat 32 nv.toNat)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0), mFill, [("v", 0, 0)]),
          .fellThrough) :=
      hfillLoop
    have hloopS0 : memEvalStmtWith memEvalStmtZeroHandler
          vecSumWhile
          (mkVecEnv blkOut nv (BitVec.ofNat 32 nv.toNat)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
          mFill [("v", 0, 0)]
        = .ok ((mkVecEnv blkOut nv (BitVec.ofNat 32 nv.toNat)
            (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
              nv.toNat)
            (BitVec.ofNat 32 nv.toNat), mFill, [("v", 0, 0)]),
          .fellThrough) :=
      memVecSumWhile_correct blkOut nv 0 0 (BitVec.ofNat 32 nv.toNat) _ _
        mFill 0 [("v", 0, 0)]
        (Nat.zero_le _)
        (by intro j hjlo hjhi; exact hgetOut j hjlo hjhi) hn32 hlayV
        hfindFill hsum0 (by cir_fuel)
    obtain ⟨mFree, hmfree, _hfindFree⟩ := vfree_lockstep mFill 0 0 blkOut
      ⟨0, true, blkOut.val⟩ ⟨blkOut.val, true⟩ hfindFill rfl rfl rfl
      hliveOut hfree0
    have huv := vecEnv_update_v blkOut nv (BitVec.ofNat 32 nv.toNat)
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      (BitVec.ofNat 32 nv.toNat) ⟨blkOut.val, true⟩
    have harv := mkVecEnv_v blkOut nv (BitVec.ofNat 32 nv.toNat)
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      (BitVec.ofNat 32 nv.toNat)
    have hars := mkVecEnv_s ⟨blkOut.val, true⟩ nv
      (BitVec.ofNat 32 nv.toNat)
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      (BitVec.ofNat 32 nv.toNat)
    simp only [memEvalFuncFuel, vecFunc, emptyMem, hb, memEvalStmtFuel,
      memEvalStmtZero, memEvalStmtWith, memEvalExpr, litVal, hn0, vecNew,
      memAllocData, Nat.reduceAdd]
    simp only [hloopF0, hloopS0, hfree0,
      hmfree, huv, harv, hars, hlayV]
  | succ F =>
    obtain ⟨mFill, hfillLoop, hfindFill, _hliveFill⟩ :=
      memVecFillWhile_correct
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv (F + 1) 0
        (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) blkOut
        ⟨1, [(0, ⟨0, true,
          List.replicate nv.toNat (BitVec.ofNat 32 0)⟩)], []⟩ 0 [("v", 0, 0)]
        (Nat.zero_le _) (by simp) rfl hn32 hlayV hfindV hfill0 (by cir_fuel)
    have hloopFS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          vecFillWhile
          [("j", .u32 0), ("s", .u32 0), ("i", .u32 0),
           ("v", .vecVal ⟨List.replicate nv.toNat 0, false⟩),
           ("n", .u32 nv)]
          ⟨1, [(0, ⟨0, true, List.replicate nv.toNat 0⟩)], []⟩
          [("v", 0, 0)]
        = .ok ((mkVecEnv blkOut nv (BitVec.ofNat 32 nv.toNat)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0), mFill, [("v", 0, 0)]),
          .fellThrough) :=
      hfillLoop
    have hloopSS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          vecSumWhile
          (mkVecEnv blkOut nv (BitVec.ofNat 32 nv.toNat)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
          mFill [("v", 0, 0)]
        = .ok ((mkVecEnv blkOut nv (BitVec.ofNat 32 nv.toNat)
            (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
              nv.toNat)
            (BitVec.ofNat 32 nv.toNat), mFill, [("v", 0, 0)]),
          .fellThrough) :=
      memVecSumWhile_correct blkOut nv (F + 1) 0 (BitVec.ofNat 32 nv.toNat)
        _ _ mFill 0 [("v", 0, 0)] (Nat.zero_le _)
        (by intro j hjlo hjhi; exact hgetOut j hjlo hjhi) hn32 hlayV
        hfindFill hsum0 (by cir_fuel)
    obtain ⟨mFree, hmfree, _hfindFree⟩ := vfree_lockstep mFill 0 0 blkOut
      ⟨0, true, blkOut.val⟩ ⟨blkOut.val, true⟩ hfindFill rfl rfl rfl
      hliveOut hfree0
    have huv := vecEnv_update_v blkOut nv (BitVec.ofNat 32 nv.toNat)
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      (BitVec.ofNat 32 nv.toNat) ⟨blkOut.val, true⟩
    have harv := mkVecEnv_v blkOut nv (BitVec.ofNat 32 nv.toNat)
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      (BitVec.ofNat 32 nv.toNat)
    have hars := mkVecEnv_s ⟨blkOut.val, true⟩ nv
      (BitVec.ofNat 32 nv.toNat)
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      (BitVec.ofNat 32 nv.toNat)
    simp only [memEvalFuncFuel, vecFunc, emptyMem, hb, memEvalStmtFuel,
      memEvalStmtWith, memEvalExpr, litVal, hn0, vecNew,
      memAllocData, Nat.reduceAdd]
    simp only [hloopFS, hloopSS, hfree0,
      hmfree, huv, harv, hars, hlayV]

/-- Transfer for `vec_alloc`: both sides equal the prefix sum. -/
theorem memTransfer_vec (F : Nat) (nv : BitVec 32)
    (hn : nv.toNat ≤ F) (hn32 : nv.toNat < 2 ^ 32)
    (_h : oracleNoalias vecFunc [.u32 nv]) :
    memEvalFuncFuel F vecFunc [.u32 nv] =
      evalFuncFuel F vecFunc [.u32 nv] := by
  rw [memEvalFuncFuel_vec F nv hn hn32, evalFuncFuel_vec F nv hn hn32]

/-! ## M3c heap transfer: `vec_copy_sum` (two live blocks) -/

/-- Memory fill-loop condition reads `i` against the bound. -/
theorem memVec2FillCond_eval (blkA blkB : Vec32) (nv : BitVec 32) (k : Nat)
    (jv kv sv : BitVec 32) (m : Mem) (π : Layout) (h : k < 2 ^ 32) :
    memEvalExpr (.ult (.var "i") (.var "n"))
      (mkVec2Env blkA blkB nv (BitVec.ofNat 32 k) jv kv sv) m π =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkVec2Env_i blkA blkB nv (BitVec.ofNat 32 k) jv kv sv
  have hn := mkVec2Env_n blkA blkB nv (BitVec.ofNat 32 k) jv kv sv
  simp only [memEvalExpr, hi, hn, ofNat32_ult k nv h]

/-- Memory copy-loop condition reads `j` against the bound. -/
theorem memVec2CopyCond_eval (blkA blkB : Vec32) (nv : BitVec 32) (k : Nat)
    (iv sv kv : BitVec 32) (m : Mem) (π : Layout) (h : k < 2 ^ 32) :
    memEvalExpr (.ult (.var "j") (.var "n"))
      (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) m π =
      .ok (.b (decide (k < nv.toNat))) := by
  have hj := mkVec2Env_j blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
  have hn := mkVec2Env_n blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
  simp only [memEvalExpr, hj, hn, ofNat32_ult k nv h]

/-- Memory sum-loop condition reads `k` against the bound. -/
theorem memVec2SumCond_eval (blkA blkB : Vec32) (nv : BitVec 32) (k : Nat)
    (iv jv sv : BitVec 32) (m : Mem) (π : Layout) (h : k < 2 ^ 32) :
    memEvalExpr (.ult (.var "k") (.var "n"))
      (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv) m π =
      .ok (.b (decide (k < nv.toNat))) := by
  have hk := mkVec2Env_k blkA blkB nv iv jv (BitVec.ofNat 32 k) sv
  have hn := mkVec2Env_n blkA blkB nv iv jv (BitVec.ofNat 32 k) sv
  simp only [memEvalExpr, hk, hn, ofNat32_ult k nv h]

/-- One memory fill step stores the index into `a` and advances (any
    fuel), with `Mem`/`Layout` lockstepped on `a` (the `b` pin is
    untouched — preservation is the loop's job). -/
theorem memVec2FillBody_eval (F : Nat) (blkA blkB : Vec32) (nv : BitVec 32)
    (k : Nat) (jv kv sv : BitVec 32) (blkMid : Vec32)
    (m : Mem) (aA : Addr) (π : Layout) (mMid : Mem)
    (hk32 : k < 2 ^ 32)
    (hset : vecSet blkA k (BitVec.ofNat 32 k) = .ok blkMid)
    (hstore : memStore m aA aA k (BitVec.ofNat 32 k) = .ok mMid)
    (hlay : layoutLookup π "a" = some (aA, aA)) :
    memEvalStmtFuel F vec2FillBody
      (mkVec2Env blkA blkB nv (BitVec.ofNat 32 k) jv kv sv) m π =
      .ok (((mkVec2Env blkMid blkB nv (BitVec.ofNat 32 (k + 1)) jv kv sv,
        mMid, π)), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hi : memEvalExpr (.var "i")
      (mkVec2Env blkA blkB nv (BitVec.ofNat 32 k) jv kv sv) m π =
      .ok (.u32 (BitVec.ofNat 32 k)) := by
    have h1 := mkVec2Env_i blkA blkB nv (BitVec.ofNat 32 k) jv kv sv
    simp [memEvalExpr, h1]
  have harr := mkVec2Env_a blkA blkB nv (BitVec.ofNat 32 k) jv kv sv
  have hset' : vecSet blkA (BitVec.ofNat 32 k).toNat (BitVec.ofNat 32 k) =
      .ok blkMid := by rw [hkk]; exact hset
  have hstore' : memStore m aA aA (BitVec.ofNat 32 k).toNat
      (BitVec.ofNat 32 k) = .ok mMid := by rw [hkk]; exact hstore
  have up1 := vec2Env_update_a blkA blkB nv (BitVec.ofNat 32 k) jv kv sv
    blkMid
  have hi2 : memEvalExpr (.uadd (.var "i") (.lit (.u32 1#32)))
      (mkVec2Env blkMid blkB nv (BitVec.ofNat 32 k) jv kv sv) mMid π =
      .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVec2Env_i blkMid blkB nv (BitVec.ofNat 32 k) jv kv sv
    simp only [memEvalExpr, litVal, h1, ofNat32_add_one]
  have up2 := vec2Env_update_i blkMid blkB nv (BitVec.ofNat 32 k)
    (BitVec.ofNat 32 (k + 1)) jv kv sv
  cases F <;>
    simp only [vec2FillBody, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtWith, hi, harr, hlay, hset', hstore', up1, hi2, up2]

/-- One memory copy step reads `a[j]`, stores into `b[j]`, advances (any
    fuel): the source block is read through the cross-checked `vget`,
    the target block locksteps value and memory. -/
theorem memVec2CopyBody_eval (F : Nat) (blkA blkB : Vec32) (nv : BitVec 32)
    (k : Nat) (iv sv kv : BitVec 32) (blkMid : Vec32)
    (m : Mem) (aA aB : Addr) (π : Layout) (mMid : Mem)
    (hk32 : k < 2 ^ 32)
    (hgetA : vecGet blkA k = .ok (BitVec.ofNat 32 k))
    (hsetB : vecSet blkB k (BitVec.ofNat 32 k) = .ok blkMid)
    (hstoreB : memStore m aB aB k (BitVec.ofNat 32 k) = .ok mMid)
    (hlayA : layoutLookup π "a" = some (aA, aA))
    (hlayB : layoutLookup π "b" = some (aB, aB))
    (hfindA : memFind m aA = some ⟨aA, true, blkA.val⟩) :
    memEvalStmtFuel F vec2CopyBody
      (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) m π =
      .ok (((mkVec2Env blkA blkMid nv iv (BitVec.ofNat 32 (k + 1)) kv sv,
        mMid, π)), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hj : memEvalExpr (.var "j")
      (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) m π =
      .ok (.u32 (BitVec.ofNat 32 k)) := by
    have h1 := mkVec2Env_j blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
    simp [memEvalExpr, h1]
  have ha := mkVec2Env_a blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
  have hb := mkVec2Env_b blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
  have hloadA : memLoad m aA aA k = .ok (BitVec.ofNat 32 k) :=
    memLoad_of_vecGet m aA blkA k hfindA hgetA
  have hloadA' : memLoad m aA aA (BitVec.ofNat 32 k).toNat =
      .ok (BitVec.ofNat 32 k) := by rw [hkk]; exact hloadA
  have hgetA' : vecGet blkA (BitVec.ofNat 32 k).toNat =
      .ok (BitVec.ofNat 32 k) := by rw [hkk]; exact hgetA
  have hg : memEvalExpr (.vget "a" (.var "j"))
      (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) m π =
      .ok (.u32 (BitVec.ofNat 32 k)) := by
    -- `hj` (memEvalExpr-headed) would compete with `memEvalExpr`
    -- unfolding and lose, so discharge the index lookup with the
    -- `envLookup`-headed `hjl` instead (no competing rule).
    have hjl := mkVec2Env_j blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
    simp only [memEvalExpr, hlayA, ha, hjl, hloadA', hgetA',
      beq_self_eq_true, ↓reduceIte]
  have hsetB' : vecSet blkB (BitVec.ofNat 32 k).toNat (BitVec.ofNat 32 k) =
      .ok blkMid := by rw [hkk]; exact hsetB
  have hstoreB' : memStore m aB aB (BitVec.ofNat 32 k).toNat
      (BitVec.ofNat 32 k) = .ok mMid := by rw [hkk]; exact hstoreB
  have up1 := vec2Env_update_b blkA blkB nv iv (BitVec.ofNat 32 k) kv sv
    blkMid
  have hj2 : memEvalExpr (.uadd (.var "j") (.lit (.u32 1#32)))
      (mkVec2Env blkA blkMid nv iv (BitVec.ofNat 32 k) kv sv) mMid π =
      .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVec2Env_j blkA blkMid nv iv (BitVec.ofNat 32 k) kv sv
    simp only [memEvalExpr, litVal, h1, ofNat32_add_one]
  have up2 := vec2Env_update_j blkA blkMid nv iv (BitVec.ofNat 32 k)
    (BitVec.ofNat 32 (k + 1)) kv sv
  cases F <;>
    simp only [vec2CopyBody, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtWith, hj, hb, hlayB, hg, hsetB', hstoreB', up1, hj2, up2]

/-- One memory sum step accumulates `b[k]` and advances (any fuel),
    with `Mem`/`Layout` untouched (reads only). -/
theorem memVec2SumBody_eval (F : Nat) (blkA blkB : Vec32) (nv : BitVec 32)
    (k : Nat) (iv jv sv : BitVec 32)
    (m : Mem) (aB : Addr) (π : Layout)
    (hk32 : k < 2 ^ 32)
    (hlayB : layoutLookup π "b" = some (aB, aB))
    (hfindB : memFind m aB = some ⟨aB, true, blkB.val⟩)
    (hget : vecGet blkB k = .ok (BitVec.ofNat 32 k)) :
    memEvalStmtFuel F vec2SumBody
      (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv) m π =
      .ok (((mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 (k + 1))
        (sv + BitVec.ofNat 32 k), m, π)), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hload : memLoad m aB aB (BitVec.ofNat 32 k).toNat =
      .ok (BitVec.ofNat 32 k) := by
    rw [hkk]
    exact memLoad_of_vecGet m aB blkB k hfindB hget
  have hget' : vecGet blkB (BitVec.ofNat 32 k).toNat =
      .ok (BitVec.ofNat 32 k) := by rw [hkk]; exact hget
  have hk := mkVec2Env_k blkA blkB nv iv jv (BitVec.ofNat 32 k) sv
  have hs0 := mkVec2Env_s blkA blkB nv iv jv (BitVec.ofNat 32 k) sv
  have harr := mkVec2Env_b blkA blkB nv iv jv (BitVec.ofNat 32 k) sv
  have hs : memEvalExpr (.uadd (.var "s") (.vget "b" (.var "k")))
      (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv) m π =
      .ok (.u32 (sv + BitVec.ofNat 32 k)) := by
    simp only [memEvalExpr, hs0, hlayB, harr, hk, hload, hget',
      beq_self_eq_true, ↓reduceIte]
  have hk2 : memEvalExpr (.uadd (.var "k") (.lit (.u32 1#32)))
      (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k)
        (sv + BitVec.ofNat 32 k)) m π =
      .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVec2Env_k blkA blkB nv iv jv (BitVec.ofNat 32 k)
      (sv + BitVec.ofNat 32 k)
    simp only [memEvalExpr, litVal, h1, ofNat32_add_one]
  have up1 := vec2Env_update_s blkA blkB nv iv jv (BitVec.ofNat 32 k) sv
    (sv + BitVec.ofNat 32 k)
  have up2 := vec2Env_update_k blkA blkB nv iv jv (BitVec.ofNat 32 k)
    (BitVec.ofNat 32 (k + 1)) (sv + BitVec.ofNat 32 k)
  cases F <;>
    simp only [vec2SumBody, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtWith, hs, hk2, up1, up2]

/-- Fill-loop correctness on memory: the memory loop runs the `Base`
    fill to completion on `a`, lockstepping value and memory, while the
    `b` pin fact rides alongside untouched (writes cons-shadow, so the
    other address is preserved by `memFind_memStore_other`). -/
theorem memVec2FillWhile_correct (blkA blkB : Vec32) (nv : BitVec 32)
    (F k : Nat) (jv kv sv : BitVec 32) (blkOut : Vec32)
    (m : Mem) (aA aB : Addr) (π : Layout)
    (hk : k ≤ nv.toNat)
    (hlenA : blkA.val.length = nv.toNat)
    (hliveA : blkA.freed = false)
    (hn32 : nv.toNat < 2 ^ 32)
    (hlayA : layoutLookup π "a" = some (aA, aA))
    (hfindA : memFind m aA = some ⟨aA, true, blkA.val⟩)
    (hfindB : memFind m aB = some ⟨aB, true, blkB.val⟩)
    (hne : aA ≠ aB)
    (hfill : vecFillLoopAux blkA k (nv.toNat - k) = .ok blkOut)
    (hF : nv.toNat - k ≤ F) :
    ∃ mOut, memEvalStmtFuel F vec2FillWhile
        (mkVec2Env blkA blkB nv (BitVec.ofNat 32 k) jv kv sv) m π =
      .ok (((mkVec2Env blkOut blkB nv (BitVec.ofNat 32 nv.toNat) jv kv sv,
        mOut, π)), .fellThrough) ∧
      memFind mOut aA = some ⟨aA, true, blkOut.val⟩ ∧
      blkOut.freed = false ∧
      memFind mOut aB = some ⟨aB, true, blkB.val⟩ := by
  induction F generalizing k blkA m with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
        (mkVec2Env blkA blkB nv (BitVec.ofNat 32 nv.toNat) jv kv sv) m π =
        .ok (.b false) := by
      have hc := memVec2FillCond_eval blkA blkB nv nv.toNat jv kv sv m π hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hfill
    simp only [vecFillLoopAux] at hfill
    cases hfill
    refine ⟨m, ?_, hfindA, hliveA, hfindB⟩
    simp only [vec2FillWhile, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtZeroHandler, memEvalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hklen : k < blkA.val.length := by omega
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
          (mkVec2Env blkA blkB nv (BitVec.ofNat 32 k) jv kv sv) m π =
          .ok (.b true) := by
        simpa [hlt] using
          (memVec2FillCond_eval blkA blkB nv k jv kv sv m π hk32)
      have hset : vecSet blkA k (BitVec.ofNat 32 k) =
          .ok ⟨blkA.val.set k (BitVec.ofNat 32 k), false⟩ :=
        vecSet_ok blkA k _ hliveA hklen
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hfill
      simp only [vecFillLoopAux, hset] at hfill
      obtain ⟨mMid, hstore, hfindMid⟩ := vset_lockstep m aA aA blkA k
        (BitVec.ofNat 32 k) ⟨aA, true, blkA.val⟩
        ⟨blkA.val.set k (BitVec.ofNat 32 k), false⟩
        hfindA rfl rfl rfl hliveA hset
      have hfindMidB : memFind mMid aB = some ⟨aB, true, blkB.val⟩ := by
        rw [memFind_memStore_other m mMid aA aB aA k _ hstore
          (Ne.symm hne)]
        exact hfindB
      have hbody := memVec2FillBody_eval F blkA blkB nv k jv kv sv
        ⟨blkA.val.set k (BitVec.ofNat 32 k), false⟩ m aA π mMid
        hk32 hset hstore hlayA
      have hstep : memEvalStmtFuel (F + 1) vec2FillWhile
            (mkVec2Env blkA blkB nv (BitVec.ofNat 32 k) jv kv sv) m π
          = memEvalStmtFuel F vec2FillWhile
            (mkVec2Env ⟨blkA.val.set k (BitVec.ofNat 32 k), false⟩ blkB nv
              (BitVec.ofNat 32 (k + 1)) jv kv sv) mMid π := by
        simp [vec2FillWhile, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond, hbody]
      rw [hstep]
      have hlenMid : (⟨blkA.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).val.length
          = nv.toNat := by
        show (blkA.val.set k (BitVec.ofNat 32 k)).length = nv.toNat
        rw [List.length_set]
        omega
      exact ih ⟨blkA.val.set k (BitVec.ofNat 32 k), false⟩ (k + 1) mMid
        (by omega) hlenMid rfl hfindMid hfindMidB hfill (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
          (mkVec2Env blkA blkB nv (BitVec.ofNat 32 nv.toNat) jv kv sv) m π =
          .ok (.b false) := by
        have hc := memVec2FillCond_eval blkA blkB nv nv.toNat jv kv sv m π
          hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hfill
      simp only [vecFillLoopAux] at hfill
      cases hfill
      refine ⟨m, ?_, hfindA, hliveA, hfindB⟩
      simp only [vec2FillWhile, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith]
      rw [hcond]

/-- Copy-loop correctness on memory: `blkA` is the fixed read-only
    source (its pin fact is preserved over writes to `b`); `blkB`
    accumulates the copy in lockstep. -/
theorem memVec2CopyWhile_correct (blkA blkB : Vec32) (nv : BitVec 32)
    (F k : Nat) (iv sv kv : BitVec 32) (blkOut : Vec32)
    (m : Mem) (aA aB : Addr) (π : Layout)
    (hk : k ≤ nv.toNat)
    (hlenB : blkB.val.length = nv.toNat)
    (hliveB : blkB.freed = false)
    (hn32 : nv.toNat < 2 ^ 32)
    (hlayA : layoutLookup π "a" = some (aA, aA))
    (hlayB : layoutLookup π "b" = some (aB, aB))
    (hfindA : memFind m aA = some ⟨aA, true, blkA.val⟩)
    (hfindB : memFind m aB = some ⟨aB, true, blkB.val⟩)
    (hne : aA ≠ aB)
    (hpre : ∀ t, t < k → vecGet blkB t = .ok (BitVec.ofNat 32 t))
    (hsrc : ∀ t, t < nv.toNat → vecGet blkA t = .ok (BitVec.ofNat 32 t))
    (hcopy : vecCopyLoopAux blkA blkB k (nv.toNat - k) = .ok blkOut)
    (hF : nv.toNat - k ≤ F) :
    ∃ mOut, memEvalStmtFuel F vec2CopyWhile
        (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) m π =
      .ok (((mkVec2Env blkA blkOut nv iv (BitVec.ofNat 32 nv.toNat) kv sv,
        mOut, π)), .fellThrough) ∧
      memFind mOut aA = some ⟨aA, true, blkA.val⟩ ∧
      memFind mOut aB = some ⟨aB, true, blkOut.val⟩ ∧
      blkOut.freed = false := by
  induction F generalizing k blkB m with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : memEvalExpr (.ult (.var "j") (.var "n"))
        (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 nv.toNat) kv sv) m π =
        .ok (.b false) := by
      have hc := memVec2CopyCond_eval blkA blkB nv nv.toNat iv sv kv m π
        hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hcopy
    simp only [vecCopyLoopAux] at hcopy
    cases hcopy
    refine ⟨m, ?_, hfindA, hfindB, hliveB⟩
    simp only [vec2CopyWhile, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtZeroHandler, memEvalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hklenB : k < blkB.val.length := by omega
      have hcond : memEvalExpr (.ult (.var "j") (.var "n"))
            (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) m π =
            .ok (.b true) := by
        simpa [hlt] using
          (memVec2CopyCond_eval blkA blkB nv k iv sv kv m π hk32)
      have hgetk : vecGet blkA k = .ok (BitVec.ofNat 32 k) :=
        hsrc k (by omega)
      have hset : vecSet blkB k (BitVec.ofNat 32 k) =
          .ok ⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩ :=
        vecSet_ok blkB k _ hliveB hklenB
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hcopy
      simp only [vecCopyLoopAux, hgetk, hset] at hcopy
      obtain ⟨mMid, hstore, hfindMid⟩ := vset_lockstep m aB aB blkB k
        (BitVec.ofNat 32 k) ⟨aB, true, blkB.val⟩
        ⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩
        hfindB rfl rfl rfl hliveB hset
      have hfindMidA : memFind mMid aA = some ⟨aA, true, blkA.val⟩ := by
        rw [memFind_memStore_other m mMid aB aA aB k _ hstore hne]
        exact hfindA
      have hbody := memVec2CopyBody_eval F blkA blkB nv k iv sv kv
        ⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩ m aA aB π mMid
        hk32 hgetk hset hstore hlayA hlayB hfindA
      have hstep : memEvalStmtFuel (F + 1) vec2CopyWhile
            (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 k) kv sv) m π
          = memEvalStmtFuel F vec2CopyWhile
            (mkVec2Env blkA
              ⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩ nv iv
              (BitVec.ofNat 32 (k + 1)) kv sv) mMid π := by
        simp [vec2CopyWhile, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond, hbody]
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
      exact ih ⟨blkB.val.set k (BitVec.ofNat 32 k), false⟩ (k + 1) mMid
        (by omega) hlenMid hliveMid hfindMidA hfindMid hpre' hcopy (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : memEvalExpr (.ult (.var "j") (.var "n"))
          (mkVec2Env blkA blkB nv iv (BitVec.ofNat 32 nv.toNat) kv sv) m π =
          .ok (.b false) := by
        have hc := memVec2CopyCond_eval blkA blkB nv nv.toNat iv sv kv m π
          hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hcopy
      simp only [vecCopyLoopAux] at hcopy
      cases hcopy
      refine ⟨m, ?_, hfindA, hfindB, hliveB⟩
      simp only [vec2CopyWhile, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith]
      rw [hcond]

/-- Sum-loop correctness on memory over `b`: the memory loop runs the
    `Base` sum to completion, leaving `Mem`/`Layout` untouched. -/
theorem memVec2SumWhile_correct (blkA blkB : Vec32) (nv : BitVec 32)
    (F k : Nat) (iv jv sv : BitVec 32) (sout : BitVec 32)
    (m : Mem) (aA aB : Addr) (π : Layout)
    (hk : k ≤ nv.toNat)
    (hget : ∀ j, k ≤ j → j < nv.toNat →
      vecGet blkB j = .ok (BitVec.ofNat 32 j))
    (hn32 : nv.toNat < 2 ^ 32)
    (hlayB : layoutLookup π "b" = some (aB, aB))
    (_hfindA : memFind m aA = some ⟨aA, true, blkA.val⟩)
    (hfindB : memFind m aB = some ⟨aB, true, blkB.val⟩)
    (hsum : vecSumLoopAux blkB k (nv.toNat - k) sv = .ok sout)
    (hF : nv.toNat - k ≤ F) :
    memEvalStmtFuel F vec2SumWhile
      (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv) m π =
      .ok (((mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 nv.toNat) sout,
        m, π)), .fellThrough) := by
  induction F generalizing k sv sout with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : memEvalExpr (.ult (.var "k") (.var "n"))
        (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 nv.toNat) sv) m π =
        .ok (.b false) := by
      have hc := memVec2SumCond_eval blkA blkB nv nv.toNat iv jv sv m π hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hsum
    simp only [vecSumLoopAux] at hsum
    cases hsum
    simp only [vec2SumWhile, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtZeroHandler, memEvalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hcond : memEvalExpr (.ult (.var "k") (.var "n"))
          (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv) m π =
          .ok (.b true) := by
        simpa [hlt] using
          (memVec2SumCond_eval blkA blkB nv k iv jv sv m π hk32)
      have hgetk : vecGet blkB k = .ok (BitVec.ofNat 32 k) :=
        hget k (Nat.le_refl _) hlt
      have hbody := memVec2SumBody_eval F blkA blkB nv k iv jv sv
        m aB π hk32 hlayB hfindB hgetk
      have hstep : memEvalStmtFuel (F + 1) vec2SumWhile
            (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 k) sv) m π
          = memEvalStmtFuel F vec2SumWhile
            (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 (k + 1))
              (sv + BitVec.ofNat 32 k)) m π := by
        simp [vec2SumWhile, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond, hbody]
      rw [hstep]
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hsum
      have hgetk' : vecGet blkB k = .ok (BitVec.ofNat 32 k) :=
        hget k (Nat.le_refl _) hlt
      simp only [vecSumLoopAux, hgetk'] at hsum
      exact ih (k + 1) (sv + BitVec.ofNat 32 k) sout (by omega)
        (by intro j hjlo hjhi; exact hget j (by omega) hjhi) hsum (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : memEvalExpr (.ult (.var "k") (.var "n"))
          (mkVec2Env blkA blkB nv iv jv (BitVec.ofNat 32 nv.toNat) sv) m π =
          .ok (.b false) := by
        have hc := memVec2SumCond_eval blkA blkB nv nv.toNat iv jv sv m π
          hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hsum
      simp only [vecSumLoopAux] at hsum
      cases hsum
      simp only [vec2SumWhile, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith]
      rw [hcond]

/-- `memEval` for `vec_copy_sum` at any fuel covering `n` (mirrors
    `evalFuncFuel_vec2`; both blocks ride alongside in lockstep). -/
theorem memEvalFuncFuel_vec2 (F : Nat) (nv : BitVec 32)
    (hn : nv.toNat ≤ F) (hn32 : nv.toNat < 2 ^ 32) :
    memEvalFuncFuel F vec2Func [.u32 nv] =
      .ok (.u32 (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
        nv.toNat)) := by
  -- Stated unfolded (`⟨0, [], []⟩`): if `emptyMem` unfolds first, the
  -- `bindMemArgs_vec2` match is destroyed and the closing `simp` stalls.
  have hb : bindMemArgs [{ name := "n", ty := .u 32, role := .owned }]
      [.u32 nv] (⟨0, [], []⟩ : Mem) =
      some ([("n", .u32 nv)], (⟨0, [], []⟩ : Mem), []) :=
    bindMemArgs_vec2 nv
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
  -- The second `vnew` reads `n` past the `a` binding (cf. `evalFuncFuel_vec2`).
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
  have hlayA : layoutLookup [("b", 1, 1), ("a", 0, 0)] "a" =
      some (0, 0) := by
    simp [layoutLookup, show ("a" : String) ≠ "b" by decide]
  have hlayB : layoutLookup [("b", 1, 1), ("a", 0, 0)] "b" =
      some (1, 1) := by
    simp [layoutLookup]
  have hfindA0 : memFind ⟨2, [(1, ⟨1, true,
        List.replicate nv.toNat (BitVec.ofNat 32 0)⟩),
        (0, ⟨0, true,
        List.replicate nv.toNat (BitVec.ofNat 32 0)⟩)], []⟩ 0 =
      some ⟨0, true,
        List.replicate nv.toNat (BitVec.ofNat 32 0)⟩ := by
    simp [memFind]
  have hfindB0 : memFind ⟨2, [(1, ⟨1, true,
        List.replicate nv.toNat (BitVec.ofNat 32 0)⟩),
        (0, ⟨0, true,
        List.replicate nv.toNat (BitVec.ofNat 32 0)⟩)], []⟩ 1 =
      some ⟨1, true,
        List.replicate nv.toNat (BitVec.ofNat 32 0)⟩ := by
    simp [memFind]
  cases F with
  | zero =>
    obtain ⟨mFill, hfillLoop, hfindFillA, _hliveFill, hfindFillB⟩ :=
      memVec2FillWhile_correct
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv 0 0
        (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)
        blkAOut
        ⟨2, [(1, ⟨1, true, List.replicate nv.toNat (BitVec.ofNat 32 0)⟩),
          (0, ⟨0, true, List.replicate nv.toNat (BitVec.ofNat 32 0)⟩)], []⟩
        0 1 [("b", 1, 1), ("a", 0, 0)]
        (Nat.zero_le _) (by simp) rfl hn32 hlayA hfindA0 hfindB0
        (by decide) hfill0 (by cir_fuel)
    have hloopF0 : memEvalStmtWith memEvalStmtZeroHandler
          vec2FillWhile
          (mkVec2Env ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0))
          ⟨2, [(1, ⟨1, true, List.replicate nv.toNat (BitVec.ofNat 32 0)⟩),
            (0, ⟨0, true, List.replicate nv.toNat (BitVec.ofNat 32 0)⟩)], []⟩
          [("b", 1, 1), ("a", 0, 0)]
        = .ok ((mkVec2Env blkAOut
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
            (BitVec.ofNat 32 nv.toNat) (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0), mFill,
            [("b", 1, 1), ("a", 0, 0)]),
          .fellThrough) :=
      hfillLoop
    obtain ⟨mCopy, hcopyLoop, hfindCopyA, hfindCopyB, _hliveCopy⟩ :=
      memVec2CopyWhile_correct blkAOut
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv 0 0 nv
        (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)
        blkBOut mFill 0 1 [("b", 1, 1), ("a", 0, 0)]
        (Nat.zero_le _) (by simp) rfl hn32 hlayA hlayB
        hfindFillA hfindFillB (by decide)
        (fun t ht => absurd ht (by omega))
        (fun t ht => hgetA t (by omega) (by omega)) hcopy0 (by cir_fuel)
    have hloopC0 : memEvalStmtWith memEvalStmtZeroHandler
          vec2CopyWhile
          (mkVec2Env blkAOut
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
          mFill [("b", 1, 1), ("a", 0, 0)]
        = .ok ((mkVec2Env blkAOut blkBOut nv nv
            (BitVec.ofNat 32 nv.toNat) (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0), mCopy, [("b", 1, 1), ("a", 0, 0)]),
          .fellThrough) :=
      hcopyLoop
    have hloopS0 : memEvalStmtWith memEvalStmtZeroHandler
          vec2SumWhile
          (mkVec2Env blkAOut blkBOut nv nv nv (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0))
          mCopy [("b", 1, 1), ("a", 0, 0)]
        = .ok ((mkVec2Env blkAOut blkBOut nv nv nv
            (BitVec.ofNat 32 nv.toNat)
            (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
              nv.toNat), mCopy, [("b", 1, 1), ("a", 0, 0)]),
          .fellThrough) :=
      memVec2SumWhile_correct blkAOut blkBOut nv 0 0 nv nv
        (BitVec.ofNat 32 0)
        (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
        mCopy 0 1 [("b", 1, 1), ("a", 0, 0)]
        (Nat.zero_le _)
        (by intro j hjlo hjhi; exact hgetB j hjlo hjhi) hn32 hlayB
        hfindCopyA hfindCopyB hsum0 (by cir_fuel)
    obtain ⟨mFreeA, hmfreeA, hfindFreeA⟩ := vfree_lockstep mCopy 0 0 blkAOut
      ⟨0, true, blkAOut.val⟩ ⟨blkAOut.val, true⟩ hfindCopyA rfl rfl rfl
      hliveAOut hfreeA
    have hfindB2 : memFind mFreeA 1 = some ⟨1, true, blkBOut.val⟩ := by
      rw [memFind_memFree_other mCopy mFreeA 0 1 0 hmfreeA (by decide)]
      exact hfindCopyB
    obtain ⟨mFreeB, hmfreeB, _hfindFreeB⟩ := vfree_lockstep mFreeA 1 1
      blkBOut ⟨1, true, blkBOut.val⟩ ⟨blkBOut.val, true⟩ hfindB2 rfl rfl
      rfl hliveBOut hfreeB
    have huvA := vec2Env_update_a blkAOut blkBOut nv nv nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      ⟨blkAOut.val, true⟩
    have huvB := vec2Env_update_b ⟨blkAOut.val, true⟩ blkBOut nv nv nv
      nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      ⟨blkBOut.val, true⟩
    have harA := mkVec2Env_a blkAOut blkBOut nv nv nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
    have harB := mkVec2Env_b ⟨blkAOut.val, true⟩ blkBOut nv nv nv
      nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
    have hars := mkVec2Env_s ⟨blkAOut.val, true⟩ ⟨blkBOut.val, true⟩ nv
      nv nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
    simp [memEvalFuncFuel, vec2Func, emptyMem, hb, memEvalStmtFuel,
      memEvalStmtZero, memEvalStmtWith, memEvalExpr, litVal, hn0, hna,
      vecNew, memAllocData, Nat.reduceAdd, henv,
      hloopF0, hloopC0, hloopS0, hfreeA, hfreeB, hmfreeA, hmfreeB,
      huvA, huvB, harA, harB, hars, hlayA, hlayB]
  | succ F =>
    have hFS : nv.toNat - 0 ≤ F + 1 := by cir_fuel
    obtain ⟨mFill, hfillLoop, hfindFillA, _hliveFill, hfindFillB⟩ :=
      memVec2FillWhile_correct
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv (F + 1) 0
        (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)
        blkAOut
        ⟨2, [(1, ⟨1, true, List.replicate nv.toNat (BitVec.ofNat 32 0)⟩),
          (0, ⟨0, true, List.replicate nv.toNat (BitVec.ofNat 32 0)⟩)], []⟩
        0 1 [("b", 1, 1), ("a", 0, 0)]
        (Nat.zero_le _) (by simp) rfl hn32 hlayA hfindA0 hfindB0
        (by decide) hfill0 hFS
    have hloopFS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          vec2FillWhile
          (mkVec2Env ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0))
          ⟨2, [(1, ⟨1, true, List.replicate nv.toNat (BitVec.ofNat 32 0)⟩),
            (0, ⟨0, true, List.replicate nv.toNat (BitVec.ofNat 32 0)⟩)], []⟩
          [("b", 1, 1), ("a", 0, 0)]
        = .ok ((mkVec2Env blkAOut
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
            (BitVec.ofNat 32 nv.toNat) (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0), mFill,
            [("b", 1, 1), ("a", 0, 0)]),
          .fellThrough) :=
      hfillLoop
    obtain ⟨mCopy, hcopyLoop, hfindCopyA, hfindCopyB, _hliveCopy⟩ :=
      memVec2CopyWhile_correct blkAOut
        ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv (F + 1) 0 nv
        (BitVec.ofNat 32 0) (BitVec.ofNat 32 0)
        blkBOut mFill 0 1 [("b", 1, 1), ("a", 0, 0)]
        (Nat.zero_le _) (by simp) rfl hn32 hlayA hlayB
        hfindFillA hfindFillB (by decide)
        (fun t ht => absurd ht (by omega))
        (fun t ht => hgetA t (by omega) (by omega)) hcopy0 hFS
    have hloopCS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          vec2CopyWhile
          (mkVec2Env blkAOut
            ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
          mFill [("b", 1, 1), ("a", 0, 0)]
        = .ok ((mkVec2Env blkAOut blkBOut nv nv
            (BitVec.ofNat 32 nv.toNat) (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0), mCopy, [("b", 1, 1), ("a", 0, 0)]),
          .fellThrough) :=
      hcopyLoop
    have hloopSS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          vec2SumWhile
          (mkVec2Env blkAOut blkBOut nv nv nv (BitVec.ofNat 32 0)
            (BitVec.ofNat 32 0))
          mCopy [("b", 1, 1), ("a", 0, 0)]
        = .ok ((mkVec2Env blkAOut blkBOut nv nv nv
            (BitVec.ofNat 32 nv.toNat)
            (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
              nv.toNat), mCopy, [("b", 1, 1), ("a", 0, 0)]),
          .fellThrough) :=
      memVec2SumWhile_correct blkAOut blkBOut nv (F + 1) 0 nv nv
        (BitVec.ofNat 32 0)
        (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
        mCopy 0 1 [("b", 1, 1), ("a", 0, 0)]
        (Nat.zero_le _)
        (by intro j hjlo hjhi; exact hgetB j hjlo hjhi) hn32 hlayB
        hfindCopyA hfindCopyB hsum0 hFS
    obtain ⟨mFreeA, hmfreeA, hfindFreeA⟩ := vfree_lockstep mCopy 0 0 blkAOut
      ⟨0, true, blkAOut.val⟩ ⟨blkAOut.val, true⟩ hfindCopyA rfl rfl rfl
      hliveAOut hfreeA
    have hfindB2 : memFind mFreeA 1 = some ⟨1, true, blkBOut.val⟩ := by
      rw [memFind_memFree_other mCopy mFreeA 0 1 0 hmfreeA (by decide)]
      exact hfindCopyB
    obtain ⟨mFreeB, hmfreeB, _hfindFreeB⟩ := vfree_lockstep mFreeA 1 1
      blkBOut ⟨1, true, blkBOut.val⟩ ⟨blkBOut.val, true⟩ hfindB2 rfl rfl
      rfl hliveBOut hfreeB
    have huvA := vec2Env_update_a blkAOut blkBOut nv nv nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      ⟨blkAOut.val, true⟩
    have huvB := vec2Env_update_b ⟨blkAOut.val, true⟩ blkBOut nv nv nv
      nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      ⟨blkBOut.val, true⟩
    have harA := mkVec2Env_a blkAOut blkBOut nv nv nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
    have harB := mkVec2Env_b ⟨blkAOut.val, true⟩ blkBOut nv nv nv
      nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
    have hars := mkVec2Env_s ⟨blkAOut.val, true⟩ ⟨blkBOut.val, true⟩ nv
      nv nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
    simp [memEvalFuncFuel, vec2Func, emptyMem, hb, memEvalStmtFuel,
      memEvalStmtWith, memEvalExpr, litVal, hn0, hna, vecNew,
      memAllocData, Nat.reduceAdd, henv,
      hloopFS, hloopCS, hloopSS, hfreeA, hfreeB, hmfreeA, hmfreeB,
      huvA, huvB, harA, harB, hars, hlayA, hlayB]

/-- Transfer for `vec_copy_sum`: both sides equal the prefix sum. -/
theorem memTransfer_vec2 (F : Nat) (nv : BitVec 32)
    (hn : nv.toNat ≤ F) (hn32 : nv.toNat < 2 ^ 32)
    (_h : oracleNoalias vec2Func [.u32 nv]) :
    memEvalFuncFuel F vec2Func [.u32 nv] =
      evalFuncFuel F vec2Func [.u32 nv] := by
  rw [memEvalFuncFuel_vec2 F nv hn hn32, evalFuncFuel_vec2 F nv hn hn32]


