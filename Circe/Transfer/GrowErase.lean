/-
Circe.Transfer.GrowErase — N7d forward-shift/erase transfer.
Over `Circe.Transfer.GrowShift` (reuses `shiftBlk`).
-/
import Circe.Transfer.GrowShift
import Circe.Transfer.GrowEmplace
import Circe.Transfer.GrowReserve
import Circe.Emit.VecCompose.Erase
import Circe.Derived

/-! ## N7d forward shift: loop transfer -/

/-- The loop condition reads `k < n` on memory too (pure variables;
    mirrors `stdVecShiftDownCond_eval`). -/
theorem memStdVecShiftDownCond_eval (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) (k : Nat) (n : BitVec 64)
    (dst : Vec32) (m : Mem) (π : Layout)
    (hk64 : k < 2 ^ 64) (hn64 : n.toNat < 2 ^ 64) :
    memEvalExpr (.ult (.var "k") (.var "n"))
      (mkStdVecShiftDownEnv b len cap first last result k n
        dst) m π =
      .ok (.b (decide (k < n.toNat))) := by
  have hk := mkStdVecShiftDownEnv_k b len cap first last result k n
    dst
  have hn := mkStdVecShiftDownEnv_n b len cap first last result k n
    dst
  have hkv : evalExpr (.var "k")
      (mkStdVecShiftDownEnv b len cap first last result k n dst) =
      .ok (.u64 (BitVec.ofNat 64 k)) := by
    simp [evalExpr, hk]
  have hnv : evalExpr (.var "n")
      (mkStdVecShiftDownEnv b len cap first last result k n dst) =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  have mhkv : memEvalExpr (.var "k")
      (mkStdVecShiftDownEnv b len cap first last result k n dst)
      m π =
      evalExpr (.var "k")
        (mkStdVecShiftDownEnv b len cap first last result k n
          dst) :=
    memEvalExpr_var _ _ _ _
  have mhnv : memEvalExpr (.var "n")
      (mkStdVecShiftDownEnv b len cap first last result k n dst)
      m π =
      evalExpr (.var "n")
        (mkStdVecShiftDownEnv b len cap first last result k n
          dst) :=
    memEvalExpr_var _ _ _ _
  have h := memEvalExpr_ult_agree (.var "k") (.var "n") _ _ _
    mhkv mhnv
  have he : evalExpr (.ult (.var "k") (.var "n"))
      (mkStdVecShiftDownEnv b len cap first last result k n
        dst) =
      .ok (.b (decide (k < n.toNat))) := by
    have hv := evalExpr_ult_u64 _ _ _ _ _ hkv hnv
    rw [ofNat64_ult k n hk64] at hv
    simpa using hv
  rw [h]
  exact he

/-- Body with a live read and a live write on memory: copy one word
    down, bump the counter, stay in the env family (mirrors
    `stdVecShiftDownBody_step_ok`; the `vgrowSet` runs before the
    increment, bottom word first). -/
theorem memStdVecShiftDownBody_step_ok (F : Nat) (b : Vec32)
    (len cap : Nat) (first last result : BitVec 64)
    (K : Nat) (n : BitVec 64) (dst : Vec32) (x : BitVec 32)
    (dst' : Vec32) (m : Mem) (π : Layout)
    (hKlt : K < n.toNat)
    (hfirst : first.toNat ≤ last.toNat)
    (hres : result.toNat ≤ first.toNat)
    (hn : n = last - first)
    (hn64 : n.toNat < 2 ^ 64)
    (hlive : dst.freed = false)
    (hlen : last.toNat ≤ len)
    (hbuf : last.toNat ≤ dst.val.length)
    (hDb : result.toNat ≤ dst.val.length)
    (hS64 : dst.val.length < 2 ^ 64)
    (hget : dst.val[first.toNat + K]? = some x)
    (hset : vecSet dst (result.toNat + K) x = .ok dst')
    (hlay : layoutLookup π "t" = some (0, 0))
    (hfind : memFind m 0 = some (shiftBlk dst len cap)) :
    ∃ m', memEvalStmtFuel F stdVecShiftDownBody
      (mkStdVecShiftDownEnv b len cap first last result K n dst)
      m π =
      .ok ((mkStdVecShiftDownEnv b len cap first last result (K + 1)
        n dst', m', π), .fellThrough)
      ∧ memFind m' 0 = some (shiftBlk dst' len cap) := by
  have hnt : n.toNat = last.toNat - first.toNat := by
    rw [hn]; exact u64sub_toNat_exact _ _ hfirst
  have hsidx : (first + BitVec.ofNat 64 K).toNat =
      first.toNat + K := by
    rw [BitVec.toNat_add, ofNat64_toNat K (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hdidx : (result + BitVec.ofNat 64 K).toNat =
      result.toNat + K := by
    rw [BitVec.toNat_add, ofNat64_toNat K (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hkL := mkStdVecShiftDownEnv_k b len cap first last result K n
    dst
  have hkv : evalExpr (.var "k")
      (mkStdVecShiftDownEnv b len cap first last result K n dst) =
      .ok (.u64 (BitVec.ofNat 64 K)) := by
    simp [evalExpr, hkL]
  have hfirstv : evalExpr (.var "first")
      (mkStdVecShiftDownEnv b len cap first last result K n dst) =
      .ok (.u64 first) := by
    have h := mkStdVecShiftDownEnv_first b len cap first last
      result K n dst
    simp [evalExpr, h]
  have hresv : evalExpr (.var "result")
      (mkStdVecShiftDownEnv b len cap first last result K n dst) =
      .ok (.u64 result) := by
    have h := mkStdVecShiftDownEnv_result b len cap first last
      result K n dst
    simp [evalExpr, h]
  have hsidxe : evalExpr (.uadd (.var "first") (.var "k"))
      (mkStdVecShiftDownEnv b len cap first last result K n dst) =
      .ok (.u64 (first + BitVec.ofNat 64 K)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hfirstv hkv
  have hdidxe : evalExpr (.uadd (.var "result") (.var "k"))
      (mkStdVecShiftDownEnv b len cap first last result K n dst) =
      .ok (.u64 (result + BitVec.ofNat 64 K)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hresv hkv
  have mhfirstv : memEvalExpr (.var "first")
      (mkStdVecShiftDownEnv b len cap first last result K n dst)
      m π =
      evalExpr (.var "first")
        (mkStdVecShiftDownEnv b len cap first last result K n
          dst) :=
    memEvalExpr_var _ _ _ _
  have mhresv : memEvalExpr (.var "result")
      (mkStdVecShiftDownEnv b len cap first last result K n dst)
      m π =
      evalExpr (.var "result")
        (mkStdVecShiftDownEnv b len cap first last result K n
          dst) :=
    memEvalExpr_var _ _ _ _
  have mhkv : memEvalExpr (.var "k")
      (mkStdVecShiftDownEnv b len cap first last result K n dst)
      m π =
      evalExpr (.var "k")
        (mkStdVecShiftDownEnv b len cap first last result K n
          dst) :=
    memEvalExpr_var _ _ _ _
  have mhsidxe := memEvalExpr_uadd_agree (.var "first") (.var "k")
    _ _ _ mhfirstv mhkv
  have mhdidxe := memEvalExpr_uadd_agree (.var "result") (.var "k")
    _ _ _ mhresv mhkv
  have mhsidxe_ok : memEvalExpr (.uadd (.var "first") (.var "k"))
      (mkStdVecShiftDownEnv b len cap first last result K n dst)
      m π = .ok (.u64 (first + BitVec.ofNat 64 K)) := by
    rw [mhsidxe]; exact hsidxe
  have mhdidxe_ok : memEvalExpr (.uadd (.var "result") (.var "k"))
      (mkStdVecShiftDownEnv b len cap first last result K n dst)
      m π = .ok (.u64 (result + BitVec.ofNat 64 K)) := by
    rw [mhdidxe]; exact hdidxe
  have hget' : dst.val[(first + BitVec.ofNat 64 K).toNat]? =
      some x := by
    rw [hsidx]; exact hget
  have hlt : (first + BitVec.ofNat 64 K).toNat < len := by
    rw [hsidx]; omega
  have hd := mkStdVecShiftDownEnv_t b len cap first last result K n
    dst
  have hmemLoad : memLoad m 0 0
      ((first + BitVec.ofNat 64 K).toNat + 2) = .ok x := by
    rw [hsidx]
    simp [memLoad, hfind, hlive, shiftBlk, hget]
  have mhat := memEvalExpr_vgrowAt_hit "t"
    (.uadd (.var "first") (.var "k")) _ _ _ dst len cap
    (first + BitVec.ofNat 64 K) x 0 0 hlay hd mhsidxe_ok hsidxe
    hlive hmemLoad hget' hlt
  have hat : evalExpr
      (.vgrowAt "t" (.uadd (.var "first") (.var "k")))
      (mkStdVecShiftDownEnv b len cap first last result K n dst) =
      .ok (.i32 x) :=
    evalExpr_vgrowAt_some "t" _ _ dst len cap _ _ hd hsidxe
      hlive hget' hlt
  have mhat_ok : memEvalExpr
      (.vgrowAt "t" (.uadd (.var "first") (.var "k")))
      (mkStdVecShiftDownEnv b len cap first last result K n dst)
      m π = .ok (.i32 x) := by
    rw [mhat]; exact hat
  have hset' : vecSet dst (result + BitVec.ofNat 64 K).toNat x =
      .ok dst' := by
    rw [hdidx]; exact hset
  obtain ⟨m', hmstore, hfindD'⟩ := vgrowSet_lockstep m 0 0 dst
    len cap (result + BitVec.ofNat 64 K).toNat x
    (shiftBlk dst len cap) dst' hfind rfl
    (by simp [hlive, shiftBlk]) rfl hlive hset'
  have hup : envUpdate
      (mkStdVecShiftDownEnv b len cap first last result K n dst)
      "t" (.stdVecOwned dst' len cap) =
      some (mkStdVecShiftDownEnv b len cap first last result K n
        dst') :=
    stdVecShiftDownEnv_update_t b len cap first last result K n
      dst dst'
  have hsetF : memEvalStmtFuel F
      (.vgrowSet "t" (.uadd (.var "result") (.var "k"))
        (.vgrowAt "t" (.uadd (.var "first") (.var "k"))))
      (mkStdVecShiftDownEnv b len cap first last result K n dst)
      m π =
      .ok (((mkStdVecShiftDownEnv b len cap first last result K n
        dst', m', π)), .fellThrough) :=
    memEvalStmtFuel_vgrowSet F "t"
      (.uadd (.var "result") (.var "k"))
      (.vgrowAt "t" (.uadd (.var "first") (.var "k")))
      _ _ _ (result + BitVec.ofNat 64 K) x 0 0 dst dst' len cap
      m' _ mhdidxe_ok mhat_ok hd hlay hset' hmstore hup
  have hlenD' : dst'.val.length = dst.val.length :=
    vecSet_length dst _ x dst' hset
  have hfreeD' : dst'.freed = false :=
    vecSet_live dst _ x dst' hset
  have hkv' : evalExpr (.var "k")
      (mkStdVecShiftDownEnv b len cap first last result K n dst') =
      .ok (.u64 (BitVec.ofNat 64 K)) := by
    have h := mkStdVecShiftDownEnv_k b len cap first last result K
      n dst'
    simp [evalExpr, h]
  have mhkv' : memEvalExpr (.var "k")
      (mkStdVecShiftDownEnv b len cap first last result K n dst')
      m' π =
      evalExpr (.var "k")
        (mkStdVecShiftDownEnv b len cap first last result K n
          dst') :=
    memEvalExpr_var _ _ _ _
  have hlit1 : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      (mkStdVecShiftDownEnv b len cap first last result K n dst') =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have mhlit1 : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      (mkStdVecShiftDownEnv b len cap first last result K n dst')
      m' π =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        (mkStdVecShiftDownEnv b len cap first last result K n
          dst') :=
    memEvalExpr_lit _ _ _ _
  have hince : evalExpr
      (.uadd (.var "k") (.lit (.u64 (BitVec.ofNat 64 1))))
      (mkStdVecShiftDownEnv b len cap first last result K n dst') =
      .ok (.u64 (BitVec.ofNat 64 (K + 1))) := by
    have h := evalExpr_uadd_u64 _ _ _ _ _ hkv' hlit1
    rwa [ofNat64_add_one] at h
  have mhince := memEvalExpr_uadd_agree (.var "k")
    (.lit (.u64 (BitVec.ofNat 64 1))) _ _ _ mhkv' mhlit1
  have hasg := memEvalStmtFuel_assign F "k"
    (.uadd (.var "k") (.lit (.u64 (BitVec.ofNat 64 1))))
    _ _ _ _ _ mhince hince
    (stdVecShiftDownEnv_update_k b len cap first last result K n
      dst' (K + 1))
  have hblk : shiftBlk dst' len cap =
      ⟨0, true, (BitVec.ofNat 32 len) ::
        (BitVec.ofNat 32 cap) :: dst'.val⟩ := by
    simp [shiftBlk, hfreeD']
  have hfind' : memFind m' 0 = some (shiftBlk dst' len cap) := by
    rw [hblk]; exact hfindD'
  refine ⟨m', ?_, hfind'⟩
  exact (memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _
    hsetF).trans hasg

/-- Body error on memory: a failing copy aborts the body (the
    increment never runs; mirrors `stdVecShiftDownBody_step_err`;
    memory untouched). -/
theorem memStdVecShiftDownBody_step_err (F : Nat) (b : Vec32)
    (len cap : Nat) (first last result : BitVec 64)
    (K : Nat) (n : BitVec 64) (dst : Vec32) (m : Mem)
    (π : Layout) (e : Panic)
    (herr : memEvalStmtFuel F
      (.vgrowSet "t" (.uadd (.var "result") (.var "k"))
        (.vgrowAt "t" (.uadd (.var "first") (.var "k"))))
      (mkStdVecShiftDownEnv b len cap first last result K n
        dst) m π = .error e) :
    memEvalStmtFuel F stdVecShiftDownBody
      (mkStdVecShiftDownEnv b len cap first last result K n
        dst) m π = .error e :=
  memEvalStmtFuel_seq_err F _ _ _ _ _ _ herr

/-- Loop correctness on memory: the ascending walk runs the forward
    blit in lockstep, threading the triple stores through memory
    (mirrors `stdVecShiftDownWhile_correct`; the single-triple pin is
    the induction invariant). -/
theorem memStdVecShiftDownWhile_correct (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64)
    (F k : Nat) (n : BitVec 64) (dst : Vec32) (m : Mem)
    (π : Layout)
    (hk : k ≤ n.toNat)
    (hfirst : first.toNat ≤ last.toNat)
    (hres : result.toNat ≤ first.toNat)
    (hn : n = last - first)
    (hn64 : n.toNat < 2 ^ 64)
    (hlive : dst.freed = false)
    (hlen : last.toNat ≤ len)
    (hbuf : last.toNat ≤ dst.val.length)
    (hDb : result.toNat ≤ dst.val.length)
    (hS64 : dst.val.length < 2 ^ 64)
    (hlay : layoutLookup π "t" = some (0, 0))
    (hfind : memFind m 0 = some (shiftBlk dst len cap))
    (hF : n.toNat - k + 1 ≤ F) :
    ∃ m', memEvalStmtFuel F stdVecShiftDownWhile
      (mkStdVecShiftDownEnv b len cap first last result k n dst)
      m π =
      match stdVecBlitFwdFold dst len (result.toNat + k)
        (first.toNat + k) (n.toNat - k) with
      | Except.error e => Except.error e
      | Except.ok dst' =>
        Except.ok (((mkStdVecShiftDownEnv b len cap first last
          result n.toNat n dst', m', π)), .fellThrough) := by
  induction F generalizing k dst m with
  | zero =>
    refine ⟨m, ?_⟩
    omega
  | succ F ih =>
    have hnt : n.toNat = last.toNat - first.toNat := by
      rw [hn]; exact u64sub_toNat_exact _ _ hfirst
    have hk64 : k < 2 ^ 64 := by omega
    have hkL := mkStdVecShiftDownEnv_k b len cap first last
      result k n dst
    have hfirstL := mkStdVecShiftDownEnv_first b len cap first
      last result k n dst
    have hresL := mkStdVecShiftDownEnv_result b len cap first
      last result k n dst
    have hkv : evalExpr (.var "k")
        (mkStdVecShiftDownEnv b len cap first last result k n
          dst) = .ok (.u64 (BitVec.ofNat 64 k)) := by
      simp [evalExpr, hkL]
    have hfirstv : evalExpr (.var "first")
        (mkStdVecShiftDownEnv b len cap first last result k n
          dst) = .ok (.u64 first) := by
      simp [evalExpr, hfirstL]
    have hresv : evalExpr (.var "result")
        (mkStdVecShiftDownEnv b len cap first last result k n
          dst) = .ok (.u64 result) := by
      simp [evalExpr, hresL]
    have mhkv : memEvalExpr (.var "k")
        (mkStdVecShiftDownEnv b len cap first last result k n
          dst) m π =
        evalExpr (.var "k")
          (mkStdVecShiftDownEnv b len cap first last result k n
            dst) :=
      memEvalExpr_var _ _ _ _
    have mhfirstv : memEvalExpr (.var "first")
        (mkStdVecShiftDownEnv b len cap first last result k n
          dst) m π =
        evalExpr (.var "first")
          (mkStdVecShiftDownEnv b len cap first last result k n
            dst) :=
      memEvalExpr_var _ _ _ _
    have mhresv : memEvalExpr (.var "result")
        (mkStdVecShiftDownEnv b len cap first last result k n
          dst) m π =
        evalExpr (.var "result")
          (mkStdVecShiftDownEnv b len cap first last result k n
            dst) :=
      memEvalExpr_var _ _ _ _
    have hsidxe : evalExpr (.uadd (.var "first") (.var "k"))
        (mkStdVecShiftDownEnv b len cap first last result k n
          dst) = .ok (.u64 (first + BitVec.ofNat 64 k)) :=
      evalExpr_uadd_u64 _ _ _ _ _ hfirstv hkv
    have hdidxe : evalExpr (.uadd (.var "result") (.var "k"))
        (mkStdVecShiftDownEnv b len cap first last result k n
          dst) = .ok (.u64 (result + BitVec.ofNat 64 k)) :=
      evalExpr_uadd_u64 _ _ _ _ _ hresv hkv
    have mhsidxe := memEvalExpr_uadd_agree (.var "first")
      (.var "k") _ _ _ mhfirstv mhkv
    have mhdidxe := memEvalExpr_uadd_agree (.var "result")
      (.var "k") _ _ _ mhresv mhkv
    have mhsidxe_ok : memEvalExpr
        (.uadd (.var "first") (.var "k"))
        (mkStdVecShiftDownEnv b len cap first last result k n
          dst) m π =
        .ok (.u64 (first + BitVec.ofNat 64 k)) := by
      rw [mhsidxe]; exact hsidxe
    have mhdidxe_ok : memEvalExpr
        (.uadd (.var "result") (.var "k"))
        (mkStdVecShiftDownEnv b len cap first last result k n
          dst) m π =
        .ok (.u64 (result + BitVec.ofNat 64 k)) := by
      rw [mhdidxe]; exact hdidxe
    have hsidx : (first + BitVec.ofNat 64 k).toNat =
        first.toNat + k := by
      rw [BitVec.toNat_add, ofNat64_toNat k (by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    have hdidx : (result + BitVec.ofNat 64 k).toNat =
        result.toNat + k := by
      rw [BitVec.toNat_add, ofNat64_toNat k (by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    by_cases hlt : k < n.toNat
    · obtain ⟨R, hR⟩ : ∃ R, n.toNat - k = R + 1 :=
        ⟨n.toNat - k - 1, by omega⟩
      have hcond : memEvalExpr (.ult (.var "k") (.var "n"))
          (mkStdVecShiftDownEnv b len cap first last result k n
            dst) m π = .ok (.b true) := by
        have h := memStdVecShiftDownCond_eval b len cap first
          last result k n dst m π hk64 hn64
        simpa [hlt] using h
      have hunfold := stdVecBlitFwdFold_step dst len
        (result.toNat + k) (first.toNat + k) R
      have hsoff : first.toNat + k < len := by omega
      cases hget : dst.val[first.toNat + k]? with
      | none =>
        have hget' : dst.val[(first + BitVec.ofNat 64 k).toNat]? =
            none := by
          rw [hsidx]; exact hget
        have hd := mkStdVecShiftDownEnv_t b len cap first last
          result k n dst
        have hmemLoadE : memLoad m 0 0
            ((first + BitVec.ofNat 64 k).toNat + 2) =
            .error .OOB := by
          rw [hsidx]
          simp [memLoad, hfind, hlive, shiftBlk, hget]
        have mhatE := memEvalExpr_vgrowAt_oob_miss "t"
          (.uadd (.var "first") (.var "k")) _ _ _ dst len cap
          (first + BitVec.ofNat 64 k) 0 0 hlay hd mhsidxe_ok
          hsidxe hlive hmemLoadE hget'
        have mhatE_ok : memEvalExpr
            (.vgrowAt "t" (.uadd (.var "first") (.var "k")))
            (mkStdVecShiftDownEnv b len cap first last result k
              n dst) m π = .error .OOB := by
          have hatE : evalExpr
              (.vgrowAt "t" (.uadd (.var "first") (.var "k")))
              (mkStdVecShiftDownEnv b len cap first last result
                k n dst) = .error .OOB :=
            evalExpr_vgrowAt_oob_miss "t" _ _ dst len cap _ hd
              hsidxe hlive hget'
          rw [mhatE]; exact hatE
        have herr : memEvalStmtFuel F
            (.vgrowSet "t" (.uadd (.var "result") (.var "k"))
              (.vgrowAt "t" (.uadd (.var "first") (.var "k"))))
            (mkStdVecShiftDownEnv b len cap first last result k
              n dst) m π = .error .OOB := by
          cases F <;>
            simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
              mhdidxe_ok, mhatE_ok]
        have hbody := memStdVecShiftDownBody_step_err F b len
          cap first last result k n dst m π .OOB herr
        have hstep : memEvalStmtFuel (F + 1) stdVecShiftDownWhile
            (mkStdVecShiftDownEnv b len cap first last result k
              n dst) m π = .error .OOB := by
          simp [stdVecShiftDownWhile, memEvalStmtFuel,
            memEvalSuccHandler, memEvalStmtWith, hcond, hbody]
        refine ⟨m, ?_⟩
        rw [hstep, hR, hunfold]
        simp [hlive, hsoff, hget]
      | some x =>
        have hd := mkStdVecShiftDownEnv_t b len cap first last
          result k n dst
        cases hset : vecSet dst (result.toNat + k) x with
        | error e =>
          have hltlen : (first + BitVec.ofNat 64 k).toNat < len := by
            rw [hsidx]; omega
          have hgetx : dst.val[(first + BitVec.ofNat 64 k).toNat]? =
              some x := by
            rw [hsidx]; exact hget
          have hat : evalExpr
              (.vgrowAt "t" (.uadd (.var "first") (.var "k")))
              (mkStdVecShiftDownEnv b len cap first last result
                k n dst) = .ok (.i32 x) :=
            evalExpr_vgrowAt_some "t" _ _ dst len cap _ _ hd
              hsidxe hlive hgetx hltlen
          have mhat := memEvalExpr_vgrowAt_hit "t"
            (.uadd (.var "first") (.var "k")) _ _ _ dst len cap
            (first + BitVec.ofNat 64 k) x 0 0 hlay hd mhsidxe_ok
            hsidxe hlive
            (by rw [hsidx]; simp [memLoad, hfind, hlive, shiftBlk, hget])
            hgetx hltlen
          have mhat_ok : memEvalExpr
              (.vgrowAt "t" (.uadd (.var "first") (.var "k")))
              (mkStdVecShiftDownEnv b len cap first last result
                k n dst) m π = .ok (.i32 x) := by
            rw [mhat]; exact hat
          have hset' : vecSet dst (result + BitVec.ofNat 64 k).toNat
              x = .error e := by
            rw [hdidx]; exact hset
          have herr : memEvalStmtFuel F
              (.vgrowSet "t" (.uadd (.var "result") (.var "k"))
                (.vgrowAt "t" (.uadd (.var "first") (.var "k"))))
              (mkStdVecShiftDownEnv b len cap first last result
                k n dst) m π = .error e :=
            memEvalStmtFuel_vgrowSet_err F "t"
              (.uadd (.var "result") (.var "k"))
              (.vgrowAt "t" (.uadd (.var "first") (.var "k")))
              _ _ _ (result + BitVec.ofNat 64 k) x 0 0 dst len
              cap e mhdidxe_ok mhat_ok hd hlay hset'
          have hbody := memStdVecShiftDownBody_step_err F b len
            cap first last result k n dst m π e herr
          have hstep : memEvalStmtFuel (F + 1) stdVecShiftDownWhile
              (mkStdVecShiftDownEnv b len cap first last result k
                n dst) m π = .error e := by
            simp [stdVecShiftDownWhile, memEvalStmtFuel,
              memEvalSuccHandler, memEvalStmtWith, hcond, hbody]
          refine ⟨m, ?_⟩
          rw [hstep, hR, hunfold]
          simp [hlive, hsoff, hget, hset]
        | ok dst' =>
          obtain ⟨m₁, hbodyEq, hfind'⟩ :=
            memStdVecShiftDownBody_step_ok F b len cap first
              last result k n dst x dst' m π hlt hfirst hres
              hn hn64 hlive hlen hbuf hDb hS64 hget hset hlay
              hfind
          have hstep : memEvalStmtFuel (F + 1) stdVecShiftDownWhile
              (mkStdVecShiftDownEnv b len cap first last result k
                n dst) m π =
              memEvalStmtFuel F stdVecShiftDownWhile
                (mkStdVecShiftDownEnv b len cap first last
                  result (k + 1) n dst') m₁ π := by
            simp [stdVecShiftDownWhile, memEvalStmtFuel,
              memEvalSuccHandler, memEvalStmtWith, hcond, hbodyEq]
          have hlenD' : dst'.val.length = dst.val.length :=
            vecSet_length dst _ x dst' hset
          have hfreeD' : dst'.freed = false :=
            vecSet_live dst _ x dst' hset
          obtain ⟨m₂, hihEq⟩ := ih (k + 1) dst' m₁ (by omega)
            hfreeD'
            (by rw [hlenD']; exact hbuf)
            (by rw [hlenD']; exact hDb)
            (by rw [hlenD']; exact hS64) hfind' (by omega)
          refine ⟨m₂, ?_⟩
          rw [hstep, hR, hunfold]
          simp only [hlive, hsoff, hget, hset]
          have e1 : result.toNat + k + 1 = result.toNat + (k + 1) :=
            by omega
          have e2 : first.toNat + k + 1 = first.toNat + (k + 1) :=
            by omega
          have e3 : R = n.toNat - (k + 1) := by omega
          rw [e1, e2, e3]
          exact hihEq
    · have hkk : k = n.toNat := by omega
      subst hkk
      have hcondF : memEvalExpr (.ult (.var "k") (.var "n"))
          (mkStdVecShiftDownEnv b len cap first last result n.toNat
            n dst) m π =
          .ok (.b false) := by
        have h := memStdVecShiftDownCond_eval b len cap first
          last result n.toNat n dst m π hn64 hn64
        have hf : decide (n.toNat < n.toNat) = false := by simp
        rwa [hf] at h
      have hzero : stdVecBlitFwdFold dst len
          (result.toNat + n.toNat) (first.toNat + n.toNat)
          (n.toNat - n.toNat) = .ok dst := by
        have h0 : n.toNat - n.toNat = 0 := by omega
        rw [h0]; rfl
      have hLHS : memEvalStmtFuel (F + 1) stdVecShiftDownWhile
          (mkStdVecShiftDownEnv b len cap first last result n.toNat
            n dst) m π =
          .ok (((mkStdVecShiftDownEnv b len cap first last result
            n.toNat n dst, m, π)),
            .fellThrough) := by
        simp [stdVecShiftDownWhile, memEvalStmtFuel,
          memEvalSuccHandler, memEvalStmtWith, hcondF]
      have hRHS : (match stdVecBlitFwdFold dst len
          (result.toNat + n.toNat) (first.toNat + n.toNat)
          (n.toNat - n.toNat) with
        | Except.error e => Except.error e
        | Except.ok dst' =>
          Except.ok (((mkStdVecShiftDownEnv b len cap first last
            result n.toNat n dst', m, π)),
            Outcome.fellThrough)) =
          .ok (((mkStdVecShiftDownEnv b len cap first last result
            n.toNat n dst, m, π)),
            Outcome.fellThrough) := by
        rw [hzero]
      refine ⟨m, ?_⟩
      exact hLHS.trans hRHS.symm

/-- `memEval` for the forward shift: bind the triple, run the counter
    setup, then the ascending loop (mirrors
    `evalFuncFuel_stdVecShiftDown`; memory is discarded at the function
    boundary, so only the value equation survives). -/
theorem memEvalFuncFuel_stdVecShiftDown (F : Nat) (b : Vec32)
    (len cap : Nat) (first last result : BitVec 64)
    (hfirst : first.toNat ≤ last.toNat)
    (hres : result.toNat ≤ first.toNat)
    (hlive : b.freed = false)
    (hlen : last.toNat ≤ len)
    (hbuf : last.toNat ≤ b.val.length)
    (hDb : result.toNat ≤ b.val.length)
    (hS64 : b.val.length < 2 ^ 64)
    (hF : last.toNat - first.toNat + 1 ≤ F) :
    memEvalFuncFuel F stdVecShiftDownFunc
      [.stdVecOwned b len cap, .u64 first, .u64 last, .u64 result] =
      stdVecShiftDownFwd b len cap first last result := by
  have hX : (last - first).toNat = last.toNat - first.toNat :=
    u64sub_toNat_exact _ _ hfirst
  have hb : bindMemArgs stdVecShiftDownFunc.args
      [.stdVecOwned b len cap, .u64 first, .u64 last, .u64 result]
      emptyMem =
      some ([("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)],
        tripleMem b len cap, [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "first", ty := .u 64, role := .owned },
       { name := "last", ty := .u 64, role := .owned },
       { name := "result", ty := .u 64, role := .owned }]
      [.stdVecOwned b len cap, .u64 first, .u64 last, .u64 result]
      emptyMem = _
    exact bindMemArgs_stdVecShiftDown b len cap first last result
  have hbody : stdVecShiftDownFunc.body =
      .seq (.let_ "k" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.seq (.let_ "n" (.u 64) (.usub (.var "last") (.var "first")))
      (.seq stdVecShiftDownWhile
        (.return_ (.var "t")))) := rfl
  have hlit0 : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  have mhlit0 : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("t", .stdVecOwned b len cap),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)] :=
    memEvalExpr_lit _ _ _ _
  have me1 : memEvalStmtFuel F
      (.let_ "k" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      [("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)]
      (tripleMem b len cap) [("t", 0, 0)] =
      .ok (((("k", .u64 (BitVec.ofNat 64 0)) ::
        [("t", .stdVecOwned b len cap),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)]),
        tripleMem b len cap, [("t", 0, 0)]),
        .fellThrough) :=
    memEvalStmtFuel_let_pure F "k" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0))) _ _ _ _
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) mhlit0 hlit0
  have hlast1 : evalExpr (.var "last")
      [(("k", .u64 (BitVec.ofNat 64 0))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] = .ok (.u64 last) := by
    simp [evalExpr, envLookup,
      show ("last" : String) ≠ "k" by decide,
      show ("last" : String) ≠ "t" by decide,
      show ("last" : String) ≠ "first" by decide]
  have hfirst1 : evalExpr (.var "first")
      [(("k", .u64 (BitVec.ofNat 64 0))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] = .ok (.u64 first) := by
    simp [evalExpr, envLookup,
      show ("first" : String) ≠ "k" by decide,
      show ("first" : String) ≠ "t" by decide]
  have mhlast1 : memEvalExpr (.var "last")
      [(("k", .u64 (BitVec.ofNat 64 0))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.var "last")
        [(("k", .u64 (BitVec.ofNat 64 0))),
          ("t", .stdVecOwned b len cap),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)] :=
    memEvalExpr_var _ _ _ _
  have mhfirst1 : memEvalExpr (.var "first")
      [(("k", .u64 (BitVec.ofNat 64 0))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.var "first")
        [(("k", .u64 (BitVec.ofNat 64 0))),
          ("t", .stdVecOwned b len cap),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)] :=
    memEvalExpr_var _ _ _ _
  have mhnEval1 := memEvalExpr_usub_agree (.var "last")
    (.var "first") _ _ _ mhlast1 mhfirst1
  have hnEval1 : evalExpr (.usub (.var "last") (.var "first"))
      [(("k", .u64 (BitVec.ofNat 64 0))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] =
      .ok (.u64 (last - first)) :=
    evalExpr_usub_u64u64 _ _ _ _ _ hlast1 hfirst1
  have me2 : memEvalStmtFuel F
      (.let_ "n" (.u 64) (.usub (.var "last") (.var "first")))
      [(("k", .u64 (BitVec.ofNat 64 0))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)]
      (tripleMem b len cap) [("t", 0, 0)] =
      .ok ((mkStdVecShiftDownEnv b len cap first last result 0
        (last - first) b,
        tripleMem b len cap, [("t", 0, 0)]),
        .fellThrough) :=
    memEvalStmtFuel_let_pure F "n" (.u 64)
      (.usub (.var "last") (.var "first")) _ _ _ _
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) mhnEval1 hnEval1
  have hF0 : (last - first).toNat - 0 + 1 ≤ F := by omega
  have hlay₀ : layoutLookup [("t", 0, 0)] "t" = some (0, 0) := by
    simp [layoutLookup]
  have hfind₀ : memFind (tripleMem b len cap) 0 =
      some (shiftBlk b len cap) := by
    simp [tripleMem, memFind, shiftBlk]
  obtain ⟨mL, hloop0⟩ := memStdVecShiftDownWhile_correct b len
    cap first last result F 0 (last - first) b
    (tripleMem b len cap) [("t", 0, 0)]
    (Nat.zero_le _) hfirst hres rfl (by omega) hlive hlen hbuf
    hDb hS64 hlay₀ hfind₀ hF0
  have hcanon : stdVecBlitFwdFold b len result.toNat first.toNat
      (last.toNat - first.toNat) =
      stdVecBlitFwdFold b len (result.toNat + 0) (first.toNat + 0)
        ((last - first).toNat - 0) := by
    simp only [Nat.add_zero, Nat.sub_zero, hX]
  cases hblit : stdVecBlitFwdFold b len (result.toNat + 0)
      (first.toNat + 0) ((last - first).toNat - 0) with
  | error e =>
    have hloopE : memEvalStmtFuel F stdVecShiftDownWhile
        (mkStdVecShiftDownEnv b len cap first last result 0
          (last - first) b)
        (tripleMem b len cap) [("t", 0, 0)] = .error e := by
      rw [hblit] at hloop0
      exact hloop0
    have hfwd : stdVecShiftDownFwd b len cap first last result =
        .error e := by
      simp only [stdVecShiftDownFwd, hcanon, hblit]
    have hstmt : memEvalStmtFuel F stdVecShiftDownFunc.body
        [("t", .stdVecOwned b len cap),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)]
        (tripleMem b len cap) [("t", 0, 0)] = .error e := by
      rw [hbody]
      exact (memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _
        me1).trans
        ((memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _
          me2).trans
          (memEvalStmtFuel_seq_err F _ _ _ _ _ _ hloopE))
    simp [memEvalFuncFuel, hb, hstmt, hfwd]
  | ok b' =>
    have hloopO : memEvalStmtFuel F stdVecShiftDownWhile
        (mkStdVecShiftDownEnv b len cap first last result 0
          (last - first) b)
        (tripleMem b len cap) [("t", 0, 0)] =
        .ok (((mkStdVecShiftDownEnv b len cap first last result
          (last - first).toNat (last - first) b',
          mL, [("t", 0, 0)])),
          .fellThrough) := by
      rw [hblit] at hloop0
      exact hloop0
    have hret : envLookup
        (mkStdVecShiftDownEnv b len cap first last result
          (last - first).toNat (last - first) b') "t" =
        some (.stdVecOwned b' len cap) :=
      mkStdVecShiftDownEnv_t b len cap first last result
        (last - first).toNat (last - first) b'
    have hvar : evalExpr (.var "t")
        (mkStdVecShiftDownEnv b len cap first last result
          (last - first).toNat (last - first) b') =
        .ok (.stdVecOwned b' len cap) := by
      simp only [evalExpr]
      rw [hret]
    have mhvar : memEvalExpr (.var "t")
        (mkStdVecShiftDownEnv b len cap first last result
          (last - first).toNat (last - first) b') mL
        [("t", 0, 0)] =
        evalExpr (.var "t")
          (mkStdVecShiftDownEnv b len cap first last result
            (last - first).toNat (last - first) b') :=
      memEvalExpr_var _ _ _ _
    have hfwd : stdVecShiftDownFwd b len cap first last result =
        .ok (.stdVecOwned b' len cap) := by
      simp only [stdVecShiftDownFwd, hcanon, hblit]
    have hstmt : memEvalStmtFuel F stdVecShiftDownFunc.body
        [("t", .stdVecOwned b len cap),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)]
        (tripleMem b len cap) [("t", 0, 0)] =
        .ok (((mkStdVecShiftDownEnv b len cap first last result
          (last - first).toNat (last - first) b', mL,
          [("t", 0, 0)])),
          .returned (.stdVecOwned b' len cap)) := by
      rw [hbody]
      exact (memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _
        me1).trans
        ((memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _
          me2).trans
          ((memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _
            hloopO).trans
            (memEvalStmtFuel_return F _ _ _ _ _ mhvar hvar)))
    simp [memEvalFuncFuel, hb, hstmt, hfwd]

/-- Transfer for the forward shift: memory execution agrees with
    value execution (both sides reduce to the forward-blit
    forward). -/
theorem memTransfer_stdVecShiftDown (F : Nat) (b : Vec32)
    (len cap : Nat) (first last result : BitVec 64)
    (hfirst : first.toNat ≤ last.toNat)
    (hres : result.toNat ≤ first.toNat)
    (hlive : b.freed = false)
    (hlen : last.toNat ≤ len)
    (hbuf : last.toNat ≤ b.val.length)
    (hDb : result.toNat ≤ b.val.length)
    (hS64 : b.val.length < 2 ^ 64)
    (hF : last.toNat - first.toNat + 1 ≤ F)
    (_h : oracleNoalias stdVecShiftDownFunc
      [.stdVecOwned b len cap, .u64 first, .u64 last,
        .u64 result]) :
    memEvalFuncFuel F stdVecShiftDownFunc
      [.stdVecOwned b len cap, .u64 first, .u64 last,
        .u64 result] =
      evalFuncFuel F stdVecShiftDownFunc
        [.stdVecOwned b len cap, .u64 first, .u64 last,
          .u64 result] := by
  rw [memEvalFuncFuel_stdVecShiftDown F b len cap first last result
    hfirst hres hlive hlen hbuf hDb hS64 hF,
    evalFuncFuel_stdVecShiftDown F b len cap first last result
      hfirst hres hlive hlen hbuf hDb hS64 hF]

/-! ## N7d `_M_erase`: composer transfer -/

/-- The call-free shift body evaluates identically under the program
    memory evaluator (mirrors `evalProgStmt_stdVecShiftDownBody`; every
    statement hits the fallback arm, so `callProg` into the leaf
    agrees with `memEvalFuncFuel`). -/
theorem memEvalProgStmt_stdVecShiftDownBody (F' : Nat) (ρ : Env)
    (m : Mem) (π : Layout) :
    memEvalProgStmt vecGrowProg F' stdVecShiftDownFunc.body ρ m π =
      memEvalStmtFuel F' stdVecShiftDownFunc.body ρ m π := by
  have hbody : stdVecShiftDownFunc.body =
      .seq (.let_ "k" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.seq (.let_ "n" (.u 64)
        (.usub (.var "last") (.var "first")))
      (.seq stdVecShiftDownWhile
        (.return_ (.var "t")))) := rfl
  rw [hbody]
  cases F' with
  | zero =>
    simp only [memEvalProgStmt, stdVecShiftDownWhile,
      memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith]
  | succ n =>
    simp only [memEvalProgStmt, stdVecShiftDownWhile,
      memEvalStmtFuel, memEvalStmtWith]

/-- `memEval` for `_M_erase`: the program over the frozen leaves agrees
    with the core forward (mirrors `evalProgFunc_stdVecEraseCore`;
    caller memory threads through unchanged — callees communicate by
    value — so every step runs against the entry triple). -/
theorem memEvalProgFunc_stdVecEraseCore (F : Nat) (b : Vec32)
    (len cap : Nat) (pos : BitVec 64)
    (hlive : b.freed = false)
    (hbuf : len ≤ b.val.length)
    (hpos : pos.toNat < len)
    (hlen1 : 1 ≤ len)
    (hS64 : b.val.length < 2 ^ 64)
    (hF : len + 1 ≤ F) :
    memEvalProgFunc vecGrowProg F stdVecEraseCoreFunc
      [.stdVecOwned b len cap, .u64 pos] =
      stdVecEraseCoreFwd b len cap pos := by
  obtain ⟨F', rfl, hF'⟩ := fuel_step_down len hF
  have hlen64 : len < 2 ^ 64 := by omega
  have hlenT : (BitVec.ofNat 64 len).toNat = len :=
    ofNat64_toNat _ hlen64
  have hnposT : (pos + BitVec.ofNat 64 1).toNat = pos.toNat + 1 := by
    rw [BitVec.toNat_add, ofNat64_toNat 1 (by decide)]
    exact Nat.mod_eq_of_lt (by omega)
  have hb : bindMemArgs stdVecEraseCoreFunc.args
      [.stdVecOwned b len cap, .u64 pos] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("pos", .u64 pos)],
        tripleMem b len cap, [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "pos", ty := .u 64, role := .owned }]
      [.stdVecOwned b len cap, .u64 pos] emptyMem = _
    exact bindMemArgs_stdVecEraseCore b len cap pos
  have hbody : stdVecEraseCoreFunc.body =
      (.seq (.let_ "len" (.u 64) (.vgrowLen "t"))
      (.seq (.let_ "npos" (.u 64)
              (.uadd (.var "pos") (.lit (.u64 (BitVec.ofNat 64 1)))))
      (.if_ (.une (.var "npos") (.var "len"))
        (.seq (.callProg "t1" stdVecShiftDownName
                ["t", "npos", "len", "pos"])
          (.seq (.let_ "t2" (.vecBlock)
                  (.vgrowSetLen "t1"
                    (.usub (.var "len")
                      (.lit (.u64 (BitVec.ofNat 64 1))))))
            (.return_ (.var "t2"))))
        (.seq (.let_ "t3" (.vecBlock)
                (.vgrowSetLen "t"
                  (.usub (.var "len")
                    (.lit (.u64 (BitVec.ofNat 64 1))))))
          (.return_ (.var "t3")))))) := rfl
  have hlay : layoutLookup [("t", 0, 0)] "t" = some (0, 0) := by
    simp [layoutLookup]
  have ht0 : envLookup [("t", .stdVecOwned b len cap),
      ("pos", .u64 pos)] "t" =
      some (.stdVecOwned b len cap) := by simp [envLookup]
  have hlenE : evalExpr (.vgrowLen "t")
      [("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)] =
      .ok (.u64 (BitVec.ofNat 64 len)) :=
    evalExpr_vgrowLen_some "t" _ b len cap ht0
  have hmemLen : memLoad (tripleMem b len cap) 0 0 0 =
      .ok (BitVec.ofNat 32 len) := by
    simp [tripleMem, memLoad, memFind, hlive]
  have mhlenE : memEvalExpr (.vgrowLen "t")
      [("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.vgrowLen "t")
        [("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] :=
    memEvalExpr_vgrowLen_hit "t" _ _ _ _ _ _ _ _ hlay ht0 hmemLen
  have mhlenE_ok : memEvalExpr (.vgrowLen "t")
      [("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)]
      (tripleMem b len cap) [("t", 0, 0)] =
      .ok (.u64 (BitVec.ofNat 64 len)) := by
    rw [mhlenE]; exact hlenE
  have elen : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "len" (.u 64) (.vgrowLen "t"))
      [("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)]
      (tripleMem b len cap) [("t", 0, 0)] =
      .ok ((([("len", .u64 (BitVec.ofNat 64 len)),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)],
        tripleMem b len cap, [("t", 0, 0)])), .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
      mhlenE hlenE
  have hposV : evalExpr (.var "pos")
      [((("len", .u64 (BitVec.ofNat 64 len)))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)] = .ok (.u64 pos) := by
    simp [evalExpr, envLookup,
      show ("pos" : String) ≠ "len" by decide]
  have mhposV : memEvalExpr (.var "pos")
      [((("len", .u64 (BitVec.ofNat 64 len)))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.var "pos")
        [((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] :=
    memEvalExpr_var _ _ _ _
  have hlit1 : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      [((("len", .u64 (BitVec.ofNat 64 len)))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)] =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have mhlit1 : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      [((("len", .u64 (BitVec.ofNat 64 len)))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        [((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] :=
    memEvalExpr_lit _ _ _ _
  have hnposE : evalExpr
      (.uadd (.var "pos") (.lit (.u64 (BitVec.ofNat 64 1))))
      [((("len", .u64 (BitVec.ofNat 64 len)))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)] =
      .ok (.u64 (pos + BitVec.ofNat 64 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hposV hlit1
  have mhnposE := memEvalExpr_uadd_agree (.var "pos")
    (.lit (.u64 (BitVec.ofNat 64 1))) _ _ _ mhposV mhlit1
  have mhnposE_ok : memEvalExpr
      (.uadd (.var "pos") (.lit (.u64 (BitVec.ofNat 64 1))))
      [((("len", .u64 (BitVec.ofNat 64 len)))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)]
      (tripleMem b len cap) [("t", 0, 0)] =
      .ok (.u64 (pos + BitVec.ofNat 64 1)) := by
    rw [mhnposE]; exact hnposE
  have enpos : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "npos" (.u 64)
        (.uadd (.var "pos") (.lit (.u64 (BitVec.ofNat 64 1)))))
      [((("len", .u64 (BitVec.ofNat 64 len)))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)]
      (tripleMem b len cap) [("t", 0, 0)] =
      .ok ((([("npos", .u64 (pos + BitVec.ofNat 64 1)),
        ("len", .u64 (BitVec.ofNat 64 len)),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)],
        tripleMem b len cap, [("t", 0, 0)])),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
      mhnposE hnposE
  have hnposV : evalExpr (.var "npos")
      [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
        ((("len", .u64 (BitVec.ofNat 64 len)))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)] =
      .ok (.u64 (pos + BitVec.ofNat 64 1)) := by
    simp [evalExpr, envLookup]
  have mhnposV : memEvalExpr (.var "npos")
      [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
        ((("len", .u64 (BitVec.ofNat 64 len)))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.var "npos")
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] :=
    memEvalExpr_var _ _ _ _
  have hlenV : evalExpr (.var "len")
      [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
        ((("len", .u64 (BitVec.ofNat 64 len)))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)] =
      .ok (.u64 (BitVec.ofNat 64 len)) := by
    simp [evalExpr, envLookup,
      show ("len" : String) ≠ "npos" by decide]
  have mhlenV : memEvalExpr (.var "len")
      [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
        ((("len", .u64 (BitVec.ofNat 64 len)))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.var "len")
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] :=
    memEvalExpr_var _ _ _ _
  have hneE : evalExpr (.une (.var "npos") (.var "len"))
      [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
        ((("len", .u64 (BitVec.ofNat 64 len)))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)] =
      .ok (.b ((pos + BitVec.ofNat 64 1) !=
        BitVec.ofNat 64 len)) := by
    simp [evalExpr, envLookup,
      show ("len" : String) ≠ "npos" by decide]
  have mhneE := memEvalExpr_une_agree (.var "npos") (.var "len")
    _ _ _ mhnposV mhlenV
  have hargsT1 : lookupArgs
      [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
        ((("len", .u64 (BitVec.ofNat 64 len)))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos)]
      ["t", "npos", "len", "pos"] =
      some [.stdVecOwned b len cap,
        .u64 (pos + BitVec.ofNat 64 1),
        .u64 (BitVec.ofNat 64 len), .u64 pos] := by
    simp [lookupArgs, envLookup,
      show ("t" : String) ≠ "npos" by decide,
      show ("t" : String) ≠ "len" by decide,
      show ("len" : String) ≠ "npos" by decide,
      show ("pos" : String) ≠ "npos" by decide,
      show ("pos" : String) ≠ "len" by decide,
      show ("pos" : String) ≠ "t" by decide]
  have hmemBindS : bindMemArgs stdVecShiftDownFunc.args
      [.stdVecOwned b len cap, .u64 (pos + BitVec.ofNat 64 1),
        .u64 (BitVec.ofNat 64 len), .u64 pos] emptyMem =
      some ([("t", .stdVecOwned b len cap),
        ("first", .u64 (pos + BitVec.ofNat 64 1)),
        ("last", .u64 (BitVec.ofNat 64 len)),
        ("result", .u64 pos)],
        tripleMem b len cap, [("t", 0, 0)]) :=
    bindMemArgs_stdVecShiftDown b len cap
      (pos + BitVec.ofNat 64 1) (BitVec.ofNat 64 len) pos
  have hfuel := memEvalFuncFuel_stdVecShiftDown F' b len cap
      (pos + BitVec.ofNat 64 1) (BitVec.ofNat 64 len) pos
      (by rw [hnposT, hlenT]; omega)
      (by rw [hnposT]; omega)
      hlive
      (by omega)
      (by rw [hlenT]; exact hbuf)
      (by omega)
      hS64
      (by rw [hlenT, hnposT]; omega)
  have harm : ∀ (r : Except Panic ((Env × Mem × Layout) × Outcome)),
        (match r with
          | .error e => (.error e : Result Value)
          | .ok (_, .returned v) => .ok v
          | .ok (_, .broke) => .error .AssertFail
          | .ok (_, .continued) => .error .AssertFail
          | .ok (_, .fellThrough) => .error .AssertFail) =
        (match r with
          | .error e => (.error e : Result Value)
          | .ok (_, .returned v) => .ok v
          | .ok _ => .error .AssertFail) := by
    intro r
    cases r with
    | error e => rfl
    | ok v => obtain ⟨_, o⟩ := v; cases o <;> rfl
  have mhcall : memEvalProgFunc vecGrowProg F'
      stdVecShiftDownFunc
      [.stdVecOwned b len cap, .u64 (pos + BitVec.ofNat 64 1),
        .u64 (BitVec.ofNat 64 len), .u64 pos] =
      stdVecShiftDownFwd b len cap (pos + BitVec.ofNat 64 1)
        (BitVec.ofNat 64 len) pos := by
    simp only [memEvalProgFunc, hmemBindS,
      memEvalProgStmt_stdVecShiftDownBody]
    have h3 := hfuel
    simp only [memEvalFuncFuel, hmemBindS] at h3
    clear hfuel
    revert h3
    cases memEvalStmtFuel F' stdVecShiftDownFunc.body
        [("t", .stdVecOwned b len cap),
          ("first", .u64 (pos + BitVec.ofNat 64 1)),
          ("last", .u64 (BitVec.ofNat 64 len)),
          ("result", .u64 pos)]
        (tripleMem b len cap) [("t", 0, 0)] with
    | error e =>
      intro h3
      dsimp only at h3 ⊢
      exact h3
    | ok v =>
      obtain ⟨p, o⟩ := v
      cases o <;>
        (intro h3
         dsimp only at h3 ⊢
         exact h3)
  cases heqB : ((pos + BitVec.ofNat 64 1) ==
      BitVec.ofNat 64 len) with
  | true =>
    have hBV : pos + BitVec.ofNat 64 1 = BitVec.ofNat 64 len :=
      beq_iff_eq.mp heqB
    have hcond : evalExpr (.une (.var "npos") (.var "len"))
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] = .ok (.b false) := by
      have hbne : ((pos + BitVec.ofNat 64 1) !=
          BitVec.ofNat 64 len) = false := by
        simp [hBV]
      rw [hneE, hbne]
    have mhcond : memEvalExpr (.une (.var "npos") (.var "len"))
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)]
        (tripleMem b len cap) [("t", 0, 0)] = .ok (.b false) := by
      rw [mhneE]; exact hcond
    have hNat : (pos.toNat + 1 == len) = true := by
      have heq : pos.toNat + 1 = len := by
        have hconT : (pos + BitVec.ofNat 64 1).toNat =
            (BitVec.ofNat 64 len).toNat := by
          rw [hBV]
        rw [hnposT, hlenT] at hconT
        exact hconT
      simp [heq]
    have ht : envLookup
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] "t" =
        some (.stdVecOwned b len cap) := by
      simp [envLookup,
        show ("t" : String) ≠ "npos" by decide,
        show ("t" : String) ≠ "len" by decide]
    have mht : memEvalExpr (.var "t")
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)]
        (tripleMem b len cap) [("t", 0, 0)] =
        evalExpr (.var "t")
          [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)] :=
      memEvalExpr_var _ _ _ _
    have hlenV1 : evalExpr (.var "len")
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] =
        .ok (.u64 (BitVec.ofNat 64 len)) := hlenV
    have mhlenV1 : memEvalExpr (.var "len")
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)]
        (tripleMem b len cap) [("t", 0, 0)] =
        evalExpr (.var "len")
          [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)] :=
      memEvalExpr_var _ _ _ _
    have hlit1' : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] =
        .ok (.u64 (BitVec.ofNat 64 1)) := by
      simp [evalExpr, litVal]
    have mhlit1' : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)]
        (tripleMem b len cap) [("t", 0, 0)] =
        .ok (.u64 (BitVec.ofNat 64 1)) := by
      rw [memEvalExpr_lit _ _ _ _]; exact hlit1'
    have hsubE : evalExpr
        (.usub (.var "len") (.lit (.u64 (BitVec.ofNat 64 1))))
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] =
        .ok (.u64 (BitVec.ofNat 64 len - BitVec.ofNat 64 1)) :=
      evalExpr_usub_u64u64 _ _ _ _ _ hlenV1 hlit1'
    have mhsubE := memEvalExpr_usub_agree (.var "len")
      (.lit (.u64 (BitVec.ofNat 64 1))) _ _ _ mhlenV1 mhlit1'
    have hsub1 : BitVec.ofNat 64 len - BitVec.ofNat 64 1 =
        BitVec.ofNat 64 (len - 1) :=
      ofNat_erase_sub_one len hlen64 hlen1
    have hsetE : evalExpr
        (.vgrowSetLen "t"
          (.usub (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] =
        .ok (.stdVecOwned b (len - 1) cap) := by
      have h := evalExpr_vgrowSetLen_hit "t" _ _
        b len cap (BitVec.ofNat 64 len - BitVec.ofNat 64 1)
        ht hsubE
      rwa [hsub1, ofNat64_toNat _ (by omega)] at h
    have mhsetE := memEvalExpr_vgrowSetLen_agree "t"
      (.usub (.var "len") (.lit (.u64 (BitVec.ofNat 64 1))))
      _ _ _ mhsubE
    have mhsetE_ok : memEvalExpr
        (.vgrowSetLen "t"
          (.usub (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)]
        (tripleMem b len cap) [("t", 0, 0)] =
        .ok (.stdVecOwned b (len - 1) cap) := by
      rw [mhsetE]; exact hsetE
    have et3 : memEvalProgStmt vecGrowProg (F' + 1)
        (.let_ "t3" (.vecBlock)
          (.vgrowSetLen "t"
            (.usub (.var "len")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)]
        (tripleMem b len cap) [("t", 0, 0)] =
        .ok ((([("t3", .stdVecOwned b (len - 1) cap),
          ("npos", .u64 (pos + BitVec.ofNat 64 1)),
          ("len", .u64 (BitVec.ofNat 64 len)),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)],
          tripleMem b len cap, [("t", 0, 0)])),
          .fellThrough) := by
      rw [memEvalProgStmt_let_fb]
      exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
        (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
        mhsetE hsetE
    have hvar : evalExpr (.var "t3")
        [((("t3", .stdVecOwned b (len - 1) cap))),
          ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] =
        .ok (.stdVecOwned b (len - 1) cap) := by
      simp [evalExpr, envLookup]
    have mhvar : memEvalExpr (.var "t3")
        [((("t3", .stdVecOwned b (len - 1) cap))),
          ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)]
        (tripleMem b len cap) [("t", 0, 0)] =
        .ok (.stdVecOwned b (len - 1) cap) := by
      rw [memEvalExpr_var _ _ _ _]; exact hvar
    have hret : memEvalProgStmt vecGrowProg (F' + 1)
        (.return_ (.var "t3"))
        [((("t3", .stdVecOwned b (len - 1) cap))),
          ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)]
        (tripleMem b len cap) [("t", 0, 0)] =
        .ok ((([("t3", .stdVecOwned b (len - 1) cap),
          ("npos", .u64 (pos + BitVec.ofNat 64 1)),
          ("len", .u64 (BitVec.ofNat 64 len)),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)],
          tripleMem b len cap, [("t", 0, 0)])),
          .returned (.stdVecOwned b (len - 1) cap)) :=
      memEvalProgStmt_return vecGrowProg (F' + 1) _ _ _ _ _
        mhvar
    have helse : memEvalProgStmt vecGrowProg (F' + 1)
        (.seq (.let_ "t3" (.vecBlock)
                (.vgrowSetLen "t"
                  (.usub (.var "len")
                    (.lit (.u64 (BitVec.ofNat 64 1))))))
          (.return_ (.var "t3")))
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)]
        (tripleMem b len cap) [("t", 0, 0)] =
        .ok ((([("t3", .stdVecOwned b (len - 1) cap),
          ("npos", .u64 (pos + BitVec.ofNat 64 1)),
          ("len", .u64 (BitVec.ofNat 64 len)),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)],
          tripleMem b len cap, [("t", 0, 0)])),
          .returned (.stdVecOwned b (len - 1) cap)) := by
      exact (memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
        et3).trans hret
    have hfwd : stdVecEraseCoreFwd b len cap pos =
        .ok (.stdVecOwned b (len - 1) cap) := by
      simp [stdVecEraseCoreFwd, hNat]
    have hstmt : memEvalProgStmt vecGrowProg (F' + 1)
        stdVecEraseCoreFunc.body
        [("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)]
        (tripleMem b len cap) [("t", 0, 0)] =
        .ok ((([("t3", .stdVecOwned b (len - 1) cap),
          ("npos", .u64 (pos + BitVec.ofNat 64 1)),
          ("len", .u64 (BitVec.ofNat 64 len)),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)],
          tripleMem b len cap, [("t", 0, 0)])),
          .returned (.stdVecOwned b (len - 1) cap)) := by
      rw [hbody]
      exact (memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
        elen).trans
        ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
          enpos).trans
          ((memEvalProgStmt_if_false _ _ _ _ _ _ _ _ mhcond).trans
            helse))
    simp only [memEvalProgFunc, hb, hstmt, hfwd]
  | false =>
    have hBV : pos + BitVec.ofNat 64 1 ≠ BitVec.ofNat 64 len := by
      intro hcon
      simp [hcon] at heqB
    have hcond : evalExpr (.une (.var "npos") (.var "len"))
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] = .ok (.b true) := by
      have hbne : ((pos + BitVec.ofNat 64 1) !=
          BitVec.ofNat 64 len) = true :=
        bne_iff_ne.mpr hBV
      rw [hneE, hbne]
    have mhcond : memEvalExpr (.une (.var "npos") (.var "len"))
        [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
          ((("len", .u64 (BitVec.ofNat 64 len)))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)]
        (tripleMem b len cap) [("t", 0, 0)] = .ok (.b true) := by
      rw [mhneE]; exact hcond
    have hNat : (pos.toNat + 1 == len) = false := by
      have hcon : pos.toNat + 1 ≠ len := by
        intro hcon
        have hconT : (pos + BitVec.ofNat 64 1).toNat =
            (BitVec.ofNat 64 len).toNat := by
          rw [hnposT, hcon, hlenT]
        have := BitVec.eq_of_toNat_eq hconT
        simp [this] at heqB
      simp [hcon]
    cases hs : stdVecShiftDownFwd b len cap
        (pos + BitVec.ofNat 64 1) (BitVec.ofNat 64 len) pos with
    | error e =>
      have hcall' : memEvalProgFunc vecGrowProg F'
          stdVecShiftDownFunc
          [.stdVecOwned b len cap,
            .u64 (pos + BitVec.ofNat 64 1),
            .u64 (BitVec.ofNat 64 len), .u64 pos] = .error e := by
        rw [mhcall, hs]
      have hstepT1 := memEvalProgStmt_callProg_err vecGrowProg F'
          "t1" stdVecShiftDownName ["t", "npos", "len", "pos"] _
          (tripleMem b len cap) [("t", 0, 0)] _
          stdVecShiftDownFunc e hargsT1 findFunc_stdVecShiftDown
          hcall'
      have hfwd : stdVecEraseCoreFwd b len cap pos = .error e := by
        simp [stdVecEraseCoreFwd, hNat, hs, vecGrow_bind_err]
      have hstmt : memEvalProgStmt vecGrowProg (F' + 1)
          stdVecEraseCoreFunc.body
          [("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)]
          (tripleMem b len cap) [("t", 0, 0)] = .error e := by
        rw [hbody]
        exact (memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
          elen).trans
          ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
            enpos).trans
            ((memEvalProgStmt_if_true _ _ _ _ _ _ _ _ mhcond).trans
              (memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstepT1)))
      simp only [memEvalProgFunc, hb, hstmt, hfwd]
    | ok s =>
      obtain ⟨b', hbc, hlive', hlenB'⟩ :=
        stdVecShiftDownFwd_ok b len cap (pos + BitVec.ofNat 64 1)
          (BitVec.ofNat 64 len) pos s hlive hs
      have hcall' : memEvalProgFunc vecGrowProg F'
          stdVecShiftDownFunc
          [.stdVecOwned b len cap,
            .u64 (pos + BitVec.ofNat 64 1),
            .u64 (BitVec.ofNat 64 len), .u64 pos] = .ok s := by
        rw [mhcall, hs]
      have hstepT1 := memEvalProgStmt_callProg_ok vecGrowProg F'
          "t1" stdVecShiftDownName ["t", "npos", "len", "pos"] _
          (tripleMem b len cap) [("t", 0, 0)] _
          stdVecShiftDownFunc s hargsT1 findFunc_stdVecShiftDown
          hcall'
      have ht1 : envLookup
          [((("t1", s))),
            ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)] "t1" =
          some (.stdVecOwned b' len cap) := by
        rw [hbc]; simp [envLookup]
      have hlenV1 : evalExpr (.var "len")
          [((("t1", s))),
            ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)] =
          .ok (.u64 (BitVec.ofNat 64 len)) := by
        simp [evalExpr, envLookup,
          show ("len" : String) ≠ "t1" by decide,
          show ("len" : String) ≠ "npos" by decide]
      have mhlenV1 : memEvalExpr (.var "len")
          [((("t1", s))),
            ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)]
          (tripleMem b len cap) [("t", 0, 0)] =
          evalExpr (.var "len")
            [((("t1", s))),
              ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
              ((("len", .u64 (BitVec.ofNat 64 len)))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos)] :=
        memEvalExpr_var _ _ _ _
      have hlit1' : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
          [((("t1", s))),
            ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)] =
          .ok (.u64 (BitVec.ofNat 64 1)) := by
        simp [evalExpr, litVal]
      have mhlit1' : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
          [((("t1", s))),
            ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)]
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok (.u64 (BitVec.ofNat 64 1)) := by
        rw [memEvalExpr_lit _ _ _ _]; exact hlit1'
      have hsubE : evalExpr
          (.usub (.var "len") (.lit (.u64 (BitVec.ofNat 64 1))))
          [((("t1", s))),
            ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)] =
          .ok (.u64 (BitVec.ofNat 64 len - BitVec.ofNat 64 1)) :=
        evalExpr_usub_u64u64 _ _ _ _ _ hlenV1 hlit1'
      have mhsubE := memEvalExpr_usub_agree (.var "len")
        (.lit (.u64 (BitVec.ofNat 64 1))) _ _ _ mhlenV1 mhlit1'
      have hsub1 : BitVec.ofNat 64 len - BitVec.ofNat 64 1 =
          BitVec.ofNat 64 (len - 1) :=
        ofNat_erase_sub_one len hlen64 hlen1
      have hsetE : evalExpr
          (.vgrowSetLen "t1"
            (.usub (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
          [((("t1", s))),
            ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)] =
          .ok (.stdVecOwned b' (len - 1) cap) := by
        have h := evalExpr_vgrowSetLen_hit "t1" _ _
          b' len cap (BitVec.ofNat 64 len - BitVec.ofNat 64 1)
          ht1 hsubE
        rwa [hsub1, ofNat64_toNat _ (by omega)] at h
      have mht1 : memEvalExpr (.var "t1")
          [((("t1", s))),
            ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)]
          (tripleMem b len cap) [("t", 0, 0)] =
          evalExpr (.var "t1")
            [((("t1", s))),
              ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
              ((("len", .u64 (BitVec.ofNat 64 len)))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos)] :=
        memEvalExpr_var _ _ _ _
      have mhsetE := memEvalExpr_vgrowSetLen_agree "t1"
        (.usub (.var "len") (.lit (.u64 (BitVec.ofNat 64 1))))
        _ _ _ mhsubE
      have mhsetE_ok : memEvalExpr
          (.vgrowSetLen "t1"
            (.usub (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
          [((("t1", s))),
            ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)]
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok (.stdVecOwned b' (len - 1) cap) := by
        rw [mhsetE]; exact hsetE
      have et2 : memEvalProgStmt vecGrowProg (F' + 1)
          (.let_ "t2" (.vecBlock)
            (.vgrowSetLen "t1"
              (.usub (.var "len")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
          [((("t1", s))),
            ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)]
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok ((([("t2", .stdVecOwned b' (len - 1) cap),
            ("t1", s),
            ("npos", .u64 (pos + BitVec.ofNat 64 1)),
            ("len", .u64 (BitVec.ofNat 64 len)),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)],
            tripleMem b len cap, [("t", 0, 0)])),
            .fellThrough) := by
        rw [memEvalProgStmt_let_fb]
        exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
          (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
          mhsetE hsetE
      have hvar : evalExpr (.var "t2")
          [((("t2", .stdVecOwned b' (len - 1) cap))),
            ((("t1", s))),
            ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)] =
          .ok (.stdVecOwned b' (len - 1) cap) := by
        simp [evalExpr, envLookup]
      have mhvar : memEvalExpr (.var "t2")
          [((("t2", .stdVecOwned b' (len - 1) cap))),
            ((("t1", s))),
            ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)]
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok (.stdVecOwned b' (len - 1) cap) := by
        rw [memEvalExpr_var _ _ _ _]; exact hvar
      have hret : memEvalProgStmt vecGrowProg (F' + 1)
          (.return_ (.var "t2"))
          [((("t2", .stdVecOwned b' (len - 1) cap))),
            ((("t1", s))),
            ((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)]
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok ((([("t2", .stdVecOwned b' (len - 1) cap),
            ("t1", s),
            ("npos", .u64 (pos + BitVec.ofNat 64 1)),
            ("len", .u64 (BitVec.ofNat 64 len)),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)],
            tripleMem b len cap, [("t", 0, 0)])),
            .returned (.stdVecOwned b' (len - 1) cap)) :=
        memEvalProgStmt_return vecGrowProg (F' + 1) _ _ _ _ _
          mhvar
      have hthen : memEvalProgStmt vecGrowProg (F' + 1)
          (.seq (.callProg "t1" stdVecShiftDownName
                  ["t", "npos", "len", "pos"])
            (.seq (.let_ "t2" (.vecBlock)
                    (.vgrowSetLen "t1"
                      (.usub (.var "len")
                        (.lit (.u64 (BitVec.ofNat 64 1))))))
              (.return_ (.var "t2"))))
          [((("npos", .u64 (pos + BitVec.ofNat 64 1)))),
            ((("len", .u64 (BitVec.ofNat 64 len)))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)]
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok ((([("t2", .stdVecOwned b' (len - 1) cap),
            ("t1", s),
            ("npos", .u64 (pos + BitVec.ofNat 64 1)),
            ("len", .u64 (BitVec.ofNat 64 len)),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)],
            tripleMem b len cap, [("t", 0, 0)])),
            .returned (.stdVecOwned b' (len - 1) cap)) := by
        exact (memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
          hstepT1).trans
          ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
            et2).trans hret)
      have hfwd : stdVecEraseCoreFwd b len cap pos =
          .ok (.stdVecOwned b' (len - 1) cap) := by
        simp only [stdVecEraseCoreFwd, hNat, hs, vecGrow_bind_ok]
        rw [hbc]
        simp [vecGrowOwned, vecGrow_bind_ok]
      have hstmt : memEvalProgStmt vecGrowProg (F' + 1)
          stdVecEraseCoreFunc.body
          [("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)]
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok ((([("t2", .stdVecOwned b' (len - 1) cap),
            ("t1", s),
            ("npos", .u64 (pos + BitVec.ofNat 64 1)),
            ("len", .u64 (BitVec.ofNat 64 len)),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos)],
            tripleMem b len cap, [("t", 0, 0)])),
            .returned (.stdVecOwned b' (len - 1) cap)) := by
        rw [hbody]
        exact (memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
          elen).trans
          ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
            enpos).trans
            ((memEvalProgStmt_if_true _ _ _ _ _ _ _ _ mhcond).trans
              hthen))
      simp only [memEvalProgFunc, hb, hstmt, hfwd]

/-- Transfer for `_M_erase`: memory execution agrees with value
    execution (both sides reduce to the core forward). -/
theorem memTransfer_stdVecEraseCore (F : Nat) (b : Vec32)
    (len cap : Nat) (pos : BitVec 64)
    (hlive : b.freed = false)
    (hbuf : len ≤ b.val.length)
    (hpos : pos.toNat < len)
    (hlen1 : 1 ≤ len)
    (hS64 : b.val.length < 2 ^ 64)
    (hF : len + 1 ≤ F)
    (_h : oracleNoalias stdVecEraseCoreFunc
      [.stdVecOwned b len cap, .u64 pos]) :
    memEvalProgFunc vecGrowProg F stdVecEraseCoreFunc
      [.stdVecOwned b len cap, .u64 pos] =
      evalProgFunc vecGrowProg F stdVecEraseCoreFunc
        [.stdVecOwned b len cap, .u64 pos] := by
  rw [memEvalProgFunc_stdVecEraseCore F b len cap pos hlive hbuf
    hpos hlen1 hS64 hF,
    evalProgFunc_stdVecEraseCore F b len cap pos hlive hbuf hpos
      hlen1 hS64 hF]

/-! ## N7d `erase` forwarder: transfer -/

/-- `memEval` for the `erase` forwarder: delegation into `_M_erase`
    agrees with the erase forward (mirrors
    `evalProgFunc_stdVecErase`). -/
theorem memEvalProgFunc_stdVecErase (F : Nat) (b : Vec32)
    (len cap : Nat) (pos : BitVec 64)
    (hlive : b.freed = false)
    (hbuf : len ≤ b.val.length)
    (hpos : pos.toNat < len)
    (hlen1 : 1 ≤ len)
    (hS64 : b.val.length < 2 ^ 64)
    (hF : len + 2 ≤ F) :
    memEvalProgFunc vecGrowProg F stdVecEraseFunc
      [.stdVecOwned b len cap, .u64 pos] =
      stdVecEraseFwd b len cap pos := by
  obtain ⟨F', rfl, hF'⟩ := fuel_step_down (len + 1) hF
  have hb : bindMemArgs stdVecEraseFunc.args
      [.stdVecOwned b len cap, .u64 pos] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("pos", .u64 pos)],
        tripleMem b len cap, [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "pos", ty := .u 64, role := .owned }]
      [.stdVecOwned b len cap, .u64 pos] emptyMem = _
    exact bindMemArgs_stdVecErase b len cap pos
  have hbody : stdVecEraseFunc.body =
      (.seq (.callProg "t1" stdVecEraseCoreName ["t", "pos"])
        (.return_ (.var "t1"))) := rfl
  have hargs : lookupArgs [("t", .stdVecOwned b len cap),
      ("pos", .u64 pos)] ["t", "pos"] =
      some [.stdVecOwned b len cap, .u64 pos] := by
    simp [lookupArgs, envLookup,
      show ("pos" : String) ≠ "t" by decide]
  have hcall : memEvalProgFunc vecGrowProg F' stdVecEraseCoreFunc
      [.stdVecOwned b len cap, .u64 pos] =
      stdVecEraseCoreFwd b len cap pos :=
    memEvalProgFunc_stdVecEraseCore F' b len cap pos hlive hbuf
      hpos hlen1 hS64 hF'
  cases hR : stdVecEraseCoreFwd b len cap pos with
  | error e =>
    have hcall' : memEvalProgFunc vecGrowProg F'
        stdVecEraseCoreFunc
        [.stdVecOwned b len cap, .u64 pos] = .error e := by
      rw [hcall, hR]
    have hstepCall := memEvalProgStmt_callProg_err vecGrowProg F'
        "t1" stdVecEraseCoreName ["t", "pos"] _
        (tripleMem b len cap) [("t", 0, 0)] _
        stdVecEraseCoreFunc e hargs findFunc_stdVecEraseCore hcall'
    have hfwd : stdVecEraseFwd b len cap pos = .error e := by
      simp only [stdVecEraseFwd, hR]
    have hstmt : memEvalProgStmt vecGrowProg (F' + 1)
        stdVecEraseFunc.body
        [("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)]
        (tripleMem b len cap) [("t", 0, 0)] = .error e := by
      rw [hbody]
      exact memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstepCall
    simp only [memEvalProgFunc, hb, hstmt, hfwd]
  | ok v =>
    have hcall' : memEvalProgFunc vecGrowProg F'
        stdVecEraseCoreFunc
        [.stdVecOwned b len cap, .u64 pos] = .ok v := by
      rw [hcall, hR]
    have hstepCall := memEvalProgStmt_callProg_ok vecGrowProg F'
        "t1" stdVecEraseCoreName ["t", "pos"] _
        (tripleMem b len cap) [("t", 0, 0)] _
        stdVecEraseCoreFunc v hargs findFunc_stdVecEraseCore hcall'
    have hvar : evalExpr (.var "t1")
        [((("t1", v))), ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)] = .ok v := by
      simp [evalExpr, envLookup]
    have mhvar : memEvalExpr (.var "t1")
        [((("t1", v))), ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)]
        (tripleMem b len cap) [("t", 0, 0)] = .ok v := by
      rw [memEvalExpr_var _ _ _ _]; exact hvar
    have hret : memEvalProgStmt vecGrowProg (F' + 1)
        (.return_ (.var "t1"))
        [((("t1", v))), ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)]
        (tripleMem b len cap) [("t", 0, 0)] =
        .ok ((([("t1", v),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)],
          tripleMem b len cap, [("t", 0, 0)])),
          .returned v) :=
      memEvalProgStmt_return vecGrowProg (F' + 1) _ _ _ _ _
        mhvar
    have hfwd : stdVecEraseFwd b len cap pos = .ok v := by
      simp only [stdVecEraseFwd, hR]
    have hstmt : memEvalProgStmt vecGrowProg (F' + 1)
        stdVecEraseFunc.body
        [("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)]
        (tripleMem b len cap) [("t", 0, 0)] =
        .ok ((([("t1", v),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos)],
          tripleMem b len cap, [("t", 0, 0)])),
          .returned v) := by
      rw [hbody]
      exact (memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
        hstepCall).trans hret
    simp only [memEvalProgFunc, hb, hstmt, hfwd]

/-- Transfer for the `erase` forwarder: memory execution agrees with
    value execution (both sides reduce to the erase forward). -/
theorem memTransfer_stdVecErase (F : Nat) (b : Vec32)
    (len cap : Nat) (pos : BitVec 64)
    (hlive : b.freed = false)
    (hbuf : len ≤ b.val.length)
    (hpos : pos.toNat < len)
    (hlen1 : 1 ≤ len)
    (hS64 : b.val.length < 2 ^ 64)
    (hF : len + 2 ≤ F)
    (_h : oracleNoalias stdVecEraseFunc
      [.stdVecOwned b len cap, .u64 pos]) :
    memEvalProgFunc vecGrowProg F stdVecEraseFunc
      [.stdVecOwned b len cap, .u64 pos] =
      evalProgFunc vecGrowProg F stdVecEraseFunc
        [.stdVecOwned b len cap, .u64 pos] := by
  rw [memEvalProgFunc_stdVecErase F b len cap pos hlive hbuf hpos
    hlen1 hS64 hF,
    evalProgFunc_stdVecErase F b len cap pos hlive hbuf hpos hlen1
      hS64 hF]

/-! ## N7d `vec_erase_sum` entry: transfer -/

/-- `memEval` for `vec_erase_sum`: the closed entry over the grown
    program agrees with the compute-to-`4` forward (mirrors
    `evalProgFunc_vecEraseSumEntry`; every step runs against
    `emptyMem` — callees communicate by value). -/
theorem memEvalProgFunc_vecEraseSumEntry (F : Nat) (hF : 6 ≤ F) :
    memEvalProgFunc vecGrowProg F vecEraseSumEntryFunc [] =
      vecEraseSumEntryFwd := by
  obtain ⟨F', rfl, hF'⟩ := fuel_step_down 5 hF
  have hbind : bindMemArgs vecEraseSumEntryFunc.args [] emptyMem =
      some ([], emptyMem, []) :=
    bindMemArgs_vecEraseSumEntry
  have hbody : vecEraseSumEntryFunc.body =
      .seq (.callRet "v0" stdVecCtorName [])
      (.seq (.let_ "n" (.u 64) (.lit (.u64 (BitVec.ofNat 64 10))))
      (.seq (.callProg "v1" stdVecReserveName ["v0", "n"])
      (.seq (.let_ "c0" (.i 32) (.lit (.i32 (BitVec.ofNat 32 1))))
      (.seq (.callProg "v2" stdVecPushBackName ["v1", "c0"])
      (.seq (.let_ "c1" (.i 32) (.lit (.i32 (BitVec.ofNat 32 2))))
      (.seq (.callProg "v3" stdVecPushBackName ["v2", "c1"])
      (.seq (.let_ "c2" (.i 32) (.lit (.i32 (BitVec.ofNat 32 3))))
      (.seq (.callProg "v4" stdVecPushBackName ["v3", "c2"])
      (.seq (.callRet "bpos" stdVecBeginName ["v4"])
      (.seq (.let_ "one" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      (.seq (.callRet "p1" stdVecPlusElName ["bpos", "one"])
      (.seq (.callProg "v5" stdVecEraseName ["v4", "p1"])
      (.seq (.let_ "n0" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.seq (.callRet "e0" stdVecGrowIndexName ["v5", "n0"])
      (.seq (.let_ "n1" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      (.seq (.callRet "e1" stdVecGrowIndexName ["v5", "n1"])
      (.seq (.let_ "s" (.i 32) (.add (.var "e0") (.var "e1")))
      (.seq (.callRet "v6" stdVecDtorName ["v5"])
        (.return_ (.var "s")))))))))))))))))))) := rfl
  -- Step 1: the default ctor.
  have hargs0 : lookupArgs ([] : Env) [] = some [] := rfl
  have hcall0 : memEvalFuncFuel (F' + 1) stdVecEmptyCtorFunc [] =
      .ok (.stdVecOwned ⟨[], false⟩ 0 0) :=
    memEvalFuncFuel_stdVecEmptyCtor _
  have hstepV0 := memEvalProgStmt_callRet_ok vecGrowProg (F' + 1)
      "v0" stdVecCtorName [] ([] : Env) emptyMem [] _
      stdVecEmptyCtorFunc
      (.stdVecOwned ⟨[], false⟩ 0 0)
      hargs0 findFunc_stdVecEmptyCtor hcall0
  -- Step 2: `n = 10`.
  have hlitN : evalExpr (.lit (.u64 (BitVec.ofNat 64 10)))
      [("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.u64 (BitVec.ofNat 64 10)) := by
    simp [evalExpr, litVal]
  have mhlitN : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 10)))
      [("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 10)))
        [("v0", .stdVecOwned ⟨[], false⟩ 0 0)] :=
    memEvalExpr_lit _ _ _ _
  have hstepN : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "n" (.u 64) (.lit (.u64 (BitVec.ofNat 64 10))))
      [("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      .ok ((([("n", .u64 (BitVec.ofNat 64 10)),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], emptyMem, [])),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
      mhlitN hlitN
  -- Step 3: `reserve(10)` over the empty triple.
  have hargsR : lookupArgs
      [(("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v0", "n"] =
      some [.stdVecOwned ⟨[], false⟩ 0 0,
        .u64 (BitVec.ofNat 64 10)] := by
    simp [lookupArgs, envLookup,
      show ("v0" : String) ≠ "n" by decide]
  have hcallR : memEvalProgFunc vecGrowProg F' stdVecReserveFunc
      [.stdVecOwned ⟨[], false⟩ 0 0, .u64 (BitVec.ofNat 64 10)] =
      stdVecReserveFwd ⟨[], false⟩ 0 0 (BitVec.ofNat 64 10) :=
    memEvalProgFunc_stdVecReserve F' _ 0 0 _ rfl (by decide)
      (Nat.zero_le _) (by decide) (by decide) (by omega)
  have hcallR' : memEvalProgFunc vecGrowProg F' stdVecReserveFunc
      [.stdVecOwned ⟨[], false⟩ 0 0, .u64 (BitVec.ofNat 64 10)] =
      .ok (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10) := by
    rw [hcallR, vecReserveStep_eq]
  have hstepV1 := memEvalProgStmt_callProg_ok vecGrowProg F' "v1"
      stdVecReserveName ["v0", "n"] _ emptyMem [] _
      stdVecReserveFunc
      (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)
      hargsR findFunc_stdVecReserve hcallR'
  -- Step 4: `c0 = 1`.
  have hlitC0 : evalExpr (.lit (.i32 (BitVec.ofNat 32 1)))
      [(("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.i32 (BitVec.ofNat 32 1)) := by
    simp [evalExpr, litVal]
  have mhlitC0 : memEvalExpr (.lit (.i32 (BitVec.ofNat 32 1)))
      [(("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      evalExpr (.lit (.i32 (BitVec.ofNat 32 1)))
        [(("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
          ((("n", .u64 (BitVec.ofNat 64 10)))),
          ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] :=
    memEvalExpr_lit _ _ _ _
  have hstepC0 : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "c0" (.i 32) (.lit (.i32 (BitVec.ofNat 32 1))))
      [(("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      .ok ((([("c0", .i32 (BitVec.ofNat 32 1)),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], emptyMem, [])),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
      mhlitC0 hlitC0
  -- Step 5: first push (`1` at index `0`).
  have hargs1 : lookupArgs
      [(("c0", .i32 (BitVec.ofNat 32 1))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v1", "c0"] =
      some [.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10,
        .i32 (BitVec.ofNat 32 1)] := by
    simp [lookupArgs, envLookup,
      show ("v1" : String) ≠ "c0" by decide]
  have hcallP1 : memEvalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10,
        .i32 (BitVec.ofNat 32 1)] =
      stdVecPushBackFwd ⟨List.replicate 10 0, false⟩ 0 10
        (BitVec.ofNat 32 1) :=
    memEvalProgFunc_stdVecPushBack F' _ 0 10 _ rfl (by decide)
      (by decide) (by decide) (by decide) (by omega)
  have hcallP1' : memEvalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10,
        .i32 (BitVec.ofNat 32 1)] =
      .ok (.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10) := by
    rw [hcallP1, vecReservePush1_eq]
  have hstepV2 := memEvalProgStmt_callProg_ok vecGrowProg F' "v2"
      stdVecPushBackName ["v1", "c0"] _ emptyMem [] _
      stdVecPushBackFunc
      (.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10)
      hargs1 findFunc_stdVecPushBack hcallP1'
  -- Step 6: `c1 = 2`.
  have hlitC1 : evalExpr (.lit (.i32 (BitVec.ofNat 32 2)))
      [(("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.i32 (BitVec.ofNat 32 2)) := by
    simp [evalExpr, litVal]
  have mhlitC1 : memEvalExpr (.lit (.i32 (BitVec.ofNat 32 2)))
      [(("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      evalExpr (.lit (.i32 (BitVec.ofNat 32 2)))
        [(("v2", .stdVecOwned
            ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
            1 10)),
          ((("c0", .i32 (BitVec.ofNat 32 1)))),
          ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
          ((("n", .u64 (BitVec.ofNat 64 10)))),
          ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] :=
    memEvalExpr_lit _ _ _ _
  have hstepC1 : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "c1" (.i 32) (.lit (.i32 (BitVec.ofNat 32 2))))
      [(("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      .ok ((([("c1", .i32 (BitVec.ofNat 32 2)),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], emptyMem, [])),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
      mhlitC1 hlitC1
  -- Step 7: second push (`2` at index `1`).
  have hargs2 : lookupArgs
      [(("c1", .i32 (BitVec.ofNat 32 2))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v2", "c1"] =
      some [.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
        1 10,
        .i32 (BitVec.ofNat 32 2)] := by
    simp [lookupArgs, envLookup,
      show ("v2" : String) ≠ "c1" by decide]
  have hcallP2 : memEvalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
        1 10,
        .i32 (BitVec.ofNat 32 2)] =
      stdVecPushBackFwd
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
        1 10 (BitVec.ofNat 32 2) :=
    memEvalProgFunc_stdVecPushBack F' _ 1 10 _ rfl (by decide)
      (by decide) (by decide) (by decide) (by omega)
  have hcallP2' : memEvalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
        1 10,
        .i32 (BitVec.ofNat 32 2)] =
      .ok (.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10) := by
    rw [hcallP2, vecReservePush2_eq]
  have hstepV3 := memEvalProgStmt_callProg_ok vecGrowProg F' "v3"
      stdVecPushBackName ["v2", "c1"] _ emptyMem [] _
      stdVecPushBackFunc
      (.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10)
      hargs2 findFunc_stdVecPushBack hcallP2'
  -- Step 8: `c2 = 3`.
  have hlitC2 : evalExpr (.lit (.i32 (BitVec.ofNat 32 3)))
      [(("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10)),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.i32 (BitVec.ofNat 32 3)) := by
    simp [evalExpr, litVal]
  have mhlitC2 : memEvalExpr (.lit (.i32 (BitVec.ofNat 32 3)))
      [(("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10)),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      evalExpr (.lit (.i32 (BitVec.ofNat 32 3)))
        [(("v3", .stdVecOwned
            ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 2), false⟩ 2 10)),
          ((("c1", .i32 (BitVec.ofNat 32 2)))),
          ((("v2", .stdVecOwned
            ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
            1 10))),
          ((("c0", .i32 (BitVec.ofNat 32 1)))),
          ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
          ((("n", .u64 (BitVec.ofNat 64 10)))),
          ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] :=
    memEvalExpr_lit _ _ _ _
  have hstepC2 : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "c2" (.i 32) (.lit (.i32 (BitVec.ofNat 32 3))))
      [(("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10)),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      .ok ((([("c2", .i32 (BitVec.ofNat 32 3)),
        (("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10)),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], emptyMem, [])),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
      mhlitC2 hlitC2
  -- Step 9: third push (`3` at index `2`).
  have hargs3 : lookupArgs
      [(("c2", .i32 (BitVec.ofNat 32 3))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v3", "c2"] =
      some [.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10,
        .i32 (BitVec.ofNat 32 3)] := by
    simp [lookupArgs, envLookup,
      show ("v3" : String) ≠ "c2" by decide]
  have hcallP3 : memEvalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10,
        .i32 (BitVec.ofNat 32 3)] =
      stdVecPushBackFwd
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩
        2 10 (BitVec.ofNat 32 3) :=
    memEvalProgFunc_stdVecPushBack F' _ 2 10 _ rfl (by decide)
      (by decide) (by decide) (by decide) (by omega)
  have hcallP3' : memEvalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10,
        .i32 (BitVec.ofNat 32 3)] =
      .ok (.stdVecOwned
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
        3 10) := by
    rw [hcallP3, vecErasePush3_eq]
  have hstepV4 := memEvalProgStmt_callProg_ok vecGrowProg F' "v4"
      stdVecPushBackName ["v3", "c2"] _ emptyMem [] _
      stdVecPushBackFunc
      (.stdVecOwned
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
        3 10)
      hargs3 findFunc_stdVecPushBack hcallP3'
  -- Step 10: `begin` reads the base offset (`0`).
  have hargsB : lookupArgs
      [(("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10)),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v4"] =
      some [.stdVecOwned
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
        3 10] := by
    simp [lookupArgs, envLookup]
  have hcallB : memEvalFuncFuel (F' + 1) stdVecBeginFunc
      [.stdVecOwned
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
        3 10] =
      stdVecBeginFwd :=
    memEvalFuncFuel_stdVecBegin _ _ _ _
  have hcallB' : memEvalFuncFuel (F' + 1) stdVecBeginFunc
      [.stdVecOwned
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
        3 10] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    rw [hcallB]; rfl
  have hstepBpos := memEvalProgStmt_callRet_ok vecGrowProg (F' + 1)
      "bpos" stdVecBeginName ["v4"] _ emptyMem [] _
      stdVecBeginFunc
      (.u64 (BitVec.ofNat 64 0))
      hargsB findFunc_stdVecBegin hcallB'
  -- Step 11: `one = 1`.
  have hlitOne : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      [(("bpos", .u64 (BitVec.ofNat 64 0))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have mhlitOne : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      [(("bpos", .u64 (BitVec.ofNat 64 0))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        [(("bpos", .u64 (BitVec.ofNat 64 0))),
          ((("v4", .stdVecOwned
            ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
            3 10))),
          ((("c2", .i32 (BitVec.ofNat 32 3)))),
          ((("v3", .stdVecOwned
            ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 2), false⟩ 2 10))),
          ((("c1", .i32 (BitVec.ofNat 32 2)))),
          ((("v2", .stdVecOwned
            ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
            1 10))),
          ((("c0", .i32 (BitVec.ofNat 32 1)))),
          ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
          ((("n", .u64 (BitVec.ofNat 64 10)))),
          ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] :=
    memEvalExpr_lit _ _ _ _
  have hstepOne : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "one" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      [(("bpos", .u64 (BitVec.ofNat 64 0))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      .ok ((([("one", .u64 (BitVec.ofNat 64 1)),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], emptyMem, [])),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
      mhlitOne hlitOne
  -- Step 12: `begin() + 1` advances to position `1`.
  have hargsP1 : lookupArgs
      [(("one", .u64 (BitVec.ofNat 64 1))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["bpos", "one"] =
      some [.u64 (BitVec.ofNat 64 0), .u64 (BitVec.ofNat 64 1)] := by
    simp [lookupArgs, envLookup,
      show ("bpos" : String) ≠ "one" by decide]
  have hcallP1x : memEvalFuncFuel (F' + 1) stdVecPlusElFunc
      [.u64 (BitVec.ofNat 64 0), .u64 (BitVec.ofNat 64 1)] =
      stdVecPlusElFwd (BitVec.ofNat 64 0) (BitVec.ofNat 64 1) :=
    memEvalFuncFuel_stdVecPlusEl _ _ _
  have hcallP1x' : memEvalFuncFuel (F' + 1) stdVecPlusElFunc
      [.u64 (BitVec.ofNat 64 0), .u64 (BitVec.ofNat 64 1)] =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    rw [hcallP1x, vecErasePlusEl_eq]
  have hstepP1 := memEvalProgStmt_callRet_ok vecGrowProg (F' + 1)
      "p1" stdVecPlusElName ["bpos", "one"] _ emptyMem [] _
      stdVecPlusElFunc
      (.u64 (BitVec.ofNat 64 1))
      hargsP1 findFunc_stdVecPlusEl hcallP1x'
  -- Step 13: the `erase` at position `1`.
  have hargsV5 : lookupArgs
      [(("p1", .u64 (BitVec.ofNat 64 1))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v4", "p1"] =
      some [.stdVecOwned
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
        3 10,
        .u64 (BitVec.ofNat 64 1)] := by
    simp [lookupArgs, envLookup,
      show ("v4" : String) ≠ "p1" by decide,
      show ("v4" : String) ≠ "one" by decide,
      show ("v4" : String) ≠ "bpos" by decide]
  have hcallV5 : memEvalProgFunc vecGrowProg F' stdVecEraseFunc
      [.stdVecOwned
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
        3 10,
        .u64 (BitVec.ofNat 64 1)] =
      stdVecEraseFwd
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
        3 10 (BitVec.ofNat 64 1) :=
    memEvalProgFunc_stdVecErase F' _ 3 10 _ rfl (by decide)
      (by decide) (by decide) (by decide) (by omega)
  have hcallV5' : memEvalProgFunc vecGrowProg F' stdVecEraseFunc
      [.stdVecOwned
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
        3 10,
        .u64 (BitVec.ofNat 64 1)] =
      .ok (.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2 10) := by
    rw [hcallV5, vecEraseStep_eq]
  have hstepV5 := memEvalProgStmt_callProg_ok vecGrowProg F' "v5"
      stdVecEraseName ["v4", "p1"] _ emptyMem [] _
      stdVecEraseFunc
      (.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2 10)
      hargsV5 findFunc_stdVecErase hcallV5'
  -- Step 14: `n0 = 0`.
  have hlitN0 : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [(("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10)),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  have mhlitN0 : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [(("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10)),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [(("v5", .stdVecOwned
            ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
              (BitVec.ofNat 32 3), false⟩ 2 10)),
          ((("p1", .u64 (BitVec.ofNat 64 1)))),
          ((("one", .u64 (BitVec.ofNat 64 1)))),
          ((("bpos", .u64 (BitVec.ofNat 64 0)))),
          ((("v4", .stdVecOwned
            ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
            3 10))),
          ((("c2", .i32 (BitVec.ofNat 32 3)))),
          ((("v3", .stdVecOwned
            ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 2), false⟩ 2 10))),
          ((("c1", .i32 (BitVec.ofNat 32 2)))),
          ((("v2", .stdVecOwned
            ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
            1 10))),
          ((("c0", .i32 (BitVec.ofNat 32 1)))),
          ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
          ((("n", .u64 (BitVec.ofNat 64 10)))),
          ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] :=
    memEvalExpr_lit _ _ _ _
  have hstepN0 : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "n0" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      [(("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10)),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      .ok ((([("n0", .u64 (BitVec.ofNat 64 0)),
        (("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10)),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], emptyMem, [])),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
      mhlitN0 hlitN0
  -- Step 15: first read pins `1`.
  have hargsE0 : lookupArgs
      [(("n0", .u64 (BitVec.ofNat 64 0))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v5", "n0"] =
      some [.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2 10,
        .u64 (BitVec.ofNat 64 0)] := by
    simp [lookupArgs, envLookup,
      show ("v5" : String) ≠ "n0" by decide]
  have hget0 : (((((List.replicate 10 0).set 0
      (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 2)).set 2
      (BitVec.ofNat 32 3)).set 1
      (BitVec.ofNat 32 3))[(BitVec.ofNat 64 0).toNat]? =
      some (BitVec.ofNat 32 1) := by decide
  have hlt0 : (BitVec.ofNat 64 0).toNat < 2 := by decide
  have hcallE0 : memEvalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2 10,
        .u64 (BitVec.ofNat 64 0)] =
      stdVecGrowIndexFwd
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2
        (BitVec.ofNat 64 0) :=
    memEvalFuncFuel_stdVecGrowIndex _ _ 2 10 _ rfl _ hget0 hlt0
  have hcallE0' : memEvalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2 10,
        .u64 (BitVec.ofNat 64 0)] =
      .ok (.i32 (BitVec.ofNat 32 1)) := by
    rw [hcallE0, vecEraseRead0_eq]
  have hstepE0 := memEvalProgStmt_callRet_ok vecGrowProg (F' + 1)
      "e0" stdVecGrowIndexName ["v5", "n0"] _ emptyMem [] _
      stdVecGrowIndexFunc
      (.i32 (BitVec.ofNat 32 1))
      hargsE0 findFunc_stdVecGrowIndex hcallE0'
  -- Step 16: `n1 = 1`.
  have hlitN1 : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      [(("e0", .i32 (BitVec.ofNat 32 1))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have mhlitN1 : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      [(("e0", .i32 (BitVec.ofNat 32 1))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        [(("e0", .i32 (BitVec.ofNat 32 1))),
          ((("n0", .u64 (BitVec.ofNat 64 0)))),
          ((("v5", .stdVecOwned
            ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
              (BitVec.ofNat 32 3), false⟩ 2 10))),
          ((("p1", .u64 (BitVec.ofNat 64 1)))),
          ((("one", .u64 (BitVec.ofNat 64 1)))),
          ((("bpos", .u64 (BitVec.ofNat 64 0)))),
          ((("v4", .stdVecOwned
            ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
            3 10))),
          ((("c2", .i32 (BitVec.ofNat 32 3)))),
          ((("v3", .stdVecOwned
            ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 2), false⟩ 2 10))),
          ((("c1", .i32 (BitVec.ofNat 32 2)))),
          ((("v2", .stdVecOwned
            ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
            1 10))),
          ((("c0", .i32 (BitVec.ofNat 32 1)))),
          ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
          ((("n", .u64 (BitVec.ofNat 64 10)))),
          ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] :=
    memEvalExpr_lit _ _ _ _
  have hstepN1 : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "n1" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      [(("e0", .i32 (BitVec.ofNat 32 1))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      .ok ((([("n1", .u64 (BitVec.ofNat 64 1)),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], emptyMem, [])),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
      mhlitN1 hlitN1
  -- Step 17: second read pins `3`.
  have hargsE1 : lookupArgs
      [(("n1", .u64 (BitVec.ofNat 64 1))),
        ((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v5", "n1"] =
      some [.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2 10,
        .u64 (BitVec.ofNat 64 1)] := by
    simp [lookupArgs, envLookup,
      show ("v5" : String) ≠ "n1" by decide]
  have hget1 : (((((List.replicate 10 0).set 0
      (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 2)).set 2
      (BitVec.ofNat 32 3)).set 1
      (BitVec.ofNat 32 3))[(BitVec.ofNat 64 1).toNat]? =
      some (BitVec.ofNat 32 3) := by decide
  have hlt1 : (BitVec.ofNat 64 1).toNat < 2 := by decide
  have hcallE1 : memEvalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2 10,
        .u64 (BitVec.ofNat 64 1)] =
      stdVecGrowIndexFwd
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2
        (BitVec.ofNat 64 1) :=
    memEvalFuncFuel_stdVecGrowIndex _ _ 2 10 _ rfl _ hget1 hlt1
  have hcallE1' : memEvalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2 10,
        .u64 (BitVec.ofNat 64 1)] =
      .ok (.i32 (BitVec.ofNat 32 3)) := by
    rw [hcallE1, vecEraseRead1_eq]
  have hstepE1 := memEvalProgStmt_callRet_ok vecGrowProg (F' + 1)
      "e1" stdVecGrowIndexName ["v5", "n1"] _ emptyMem [] _
      stdVecGrowIndexFunc
      (.i32 (BitVec.ofNat 32 3))
      hargsE1 findFunc_stdVecGrowIndex hcallE1'
  -- Step 18: `s = 1 + 3 = 4`.
  have he1 : envLookup
      [(("e1", .i32 (BitVec.ofNat 32 3))),
        ((("n1", .u64 (BitVec.ofNat 64 1)))),
        ((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] "e1" =
      some (.i32 (BitVec.ofNat 32 3)) := by
    simp [envLookup]
  have he0 : envLookup
      [(("e1", .i32 (BitVec.ofNat 32 3))),
        ((("n1", .u64 (BitVec.ofNat 64 1)))),
        ((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] "e0" =
      some (.i32 (BitVec.ofNat 32 1)) := by
    simp [envLookup,
      show ("e0" : String) ≠ "e1" by decide,
      show ("e0" : String) ≠ "n1" by decide]
  have hsE : evalExpr (.add (.var "e0") (.var "e1"))
      [(("e1", .i32 (BitVec.ofNat 32 3))),
        ((("n1", .u64 (BitVec.ofNat 64 1)))),
        ((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.i32 (BitVec.ofNat 32 4)) := by
    cir_step evalExpr [he0, he1, vecEraseAdd_eq]
  have mhsEagree : memEvalExpr (.add (.var "e0") (.var "e1"))
      [(("e1", .i32 (BitVec.ofNat 32 3))),
        ((("n1", .u64 (BitVec.ofNat 64 1)))),
        ((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      evalExpr (.add (.var "e0") (.var "e1"))
        [(("e1", .i32 (BitVec.ofNat 32 3))),
          ((("n1", .u64 (BitVec.ofNat 64 1)))),
          ((("e0", .i32 (BitVec.ofNat 32 1)))),
          ((("n0", .u64 (BitVec.ofNat 64 0)))),
          ((("v5", .stdVecOwned
            ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
              (BitVec.ofNat 32 3), false⟩ 2 10))),
          ((("p1", .u64 (BitVec.ofNat 64 1)))),
          ((("one", .u64 (BitVec.ofNat 64 1)))),
          ((("bpos", .u64 (BitVec.ofNat 64 0)))),
          ((("v4", .stdVecOwned
            ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
            3 10))),
          ((("c2", .i32 (BitVec.ofNat 32 3)))),
          ((("v3", .stdVecOwned
            ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 2), false⟩ 2 10))),
          ((("c1", .i32 (BitVec.ofNat 32 2)))),
          ((("v2", .stdVecOwned
            ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
            1 10))),
          ((("c0", .i32 (BitVec.ofNat 32 1)))),
          ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
          ((("n", .u64 (BitVec.ofNat 64 10)))),
          ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] := by
    simp only [memEvalExpr, evalExpr, he0, he1]
  have hstepS : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "s" (.i 32) (.add (.var "e0") (.var "e1")))
      [(("e1", .i32 (BitVec.ofNat 32 3))),
        ((("n1", .u64 (BitVec.ofNat 64 1)))),
        ((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      .ok ((([("s", .i32 (BitVec.ofNat 32 4)),
        (("e1", .i32 (BitVec.ofNat 32 3))),
        ((("n1", .u64 (BitVec.ofNat 64 1)))),
        ((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], emptyMem, [])),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
      mhsEagree hsE
  -- Step 19: the destructor frees the two-word triple.
  have hargsV6 : lookupArgs
      [(("s", .i32 (BitVec.ofNat 32 4))),
        ((("e1", .i32 (BitVec.ofNat 32 3)))),
        ((("n1", .u64 (BitVec.ofNat 64 1)))),
        ((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v5"] =
      some [.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2 10] := by
    simp [lookupArgs, envLookup,
      show ("v5" : String) ≠ "s" by decide,
      show ("v5" : String) ≠ "e1" by decide,
      show ("v5" : String) ≠ "n1" by decide,
      show ("v5" : String) ≠ "e0" by decide,
      show ("v5" : String) ≠ "n0" by decide]
  have hcallD6 : memEvalFuncFuel (F' + 1) stdVecDtorFunc
      [.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2 10] =
      stdVecDtorFwd
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2 10 :=
    memEvalFuncFuel_stdVecDtor _ _ _ _ (by decide) rfl
  have hcallD6' : memEvalFuncFuel (F' + 1) stdVecDtorFunc
      [.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), false⟩ 2 10] =
      .ok (.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), true⟩
        2 10) := by
    rw [hcallD6, vecEraseDtor_eq]
  have hstepV6 := memEvalProgStmt_callRet_ok vecGrowProg (F' + 1)
      "v6" stdVecDtorName ["v5"] _ emptyMem [] _
      stdVecDtorFunc
      (.stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), true⟩
        2 10)
      hargsV6 findFunc_stdVecDtor hcallD6'
  -- Step 20: return `4`.
  have hrE : evalExpr (.var "s")
      [(("v6", .stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), true⟩
        2 10)),
        ((("s", .i32 (BitVec.ofNat 32 4)))),
        ((("e1", .i32 (BitVec.ofNat 32 3)))),
        ((("n1", .u64 (BitVec.ofNat 64 1)))),
        ((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.i32 (BitVec.ofNat 32 4)) := by
    simp [evalExpr, envLookup]
  have mhrE : memEvalExpr (.var "s")
      [(("v6", .stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), true⟩
        2 10)),
        ((("s", .i32 (BitVec.ofNat 32 4)))),
        ((("e1", .i32 (BitVec.ofNat 32 3)))),
        ((("n1", .u64 (BitVec.ofNat 64 1)))),
        ((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      .ok (.i32 (BitVec.ofNat 32 4)) := by
    rw [memEvalExpr_var _ _ _ _]; exact hrE
  have hret : memEvalProgStmt vecGrowProg (F' + 1)
      (.return_ (.var "s"))
      [(("v6", .stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), true⟩
        2 10)),
        ((("s", .i32 (BitVec.ofNat 32 4)))),
        ((("e1", .i32 (BitVec.ofNat 32 3)))),
        ((("n1", .u64 (BitVec.ofNat 64 1)))),
        ((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      .ok ((([("v6", .stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), true⟩
        2 10),
        (("s", .i32 (BitVec.ofNat 32 4))),
        ((("e1", .i32 (BitVec.ofNat 32 3)))),
        ((("n1", .u64 (BitVec.ofNat 64 1)))),
        ((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], emptyMem, [])),
        .returned (.i32 (BitVec.ofNat 32 4))) :=
    memEvalProgStmt_return vecGrowProg (F' + 1) _ _ _ _ _
      mhrE
  have hstmt : memEvalProgStmt vecGrowProg (F' + 1)
      vecEraseSumEntryFunc.body [] emptyMem [] =
      .ok ((([("v6", .stdVecOwned
        ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 3), true⟩
        2 10),
        (("s", .i32 (BitVec.ofNat 32 4))),
        ((("e1", .i32 (BitVec.ofNat 32 3)))),
        ((("n1", .u64 (BitVec.ofNat 64 1)))),
        ((("e0", .i32 (BitVec.ofNat 32 1)))),
        ((("n0", .u64 (BitVec.ofNat 64 0)))),
        ((("v5", .stdVecOwned
          ⟨((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 3), false⟩ 2 10))),
        ((("p1", .u64 (BitVec.ofNat 64 1)))),
        ((("one", .u64 (BitVec.ofNat 64 1)))),
        ((("bpos", .u64 (BitVec.ofNat 64 0)))),
        ((("v4", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2)).set 2 (BitVec.ofNat 32 3), false⟩
          3 10))),
        ((("c2", .i32 (BitVec.ofNat 32 3)))),
        ((("v3", .stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))),
        ((("c1", .i32 (BitVec.ofNat 32 2)))),
        ((("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))),
        ((("c0", .i32 (BitVec.ofNat 32 1)))),
        ((("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))),
        ((("n", .u64 (BitVec.ofNat 64 10)))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], emptyMem, [])),
        .returned (.i32 (BitVec.ofNat 32 4))) := by
    rw [hbody]
    exact (memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
      hstepV0).trans
      ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
        hstepN).trans
        ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
          hstepV1).trans
          ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
            hstepC0).trans
            ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
              hstepV2).trans
              ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                hstepC1).trans
                ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                  hstepV3).trans
                  ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                    hstepC2).trans
                    ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                      hstepV4).trans
                      ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                        hstepBpos).trans
                        ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                          hstepOne).trans
                          ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                            hstepP1).trans
                            ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                              hstepV5).trans
                              ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                                hstepN0).trans
                                ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                                  hstepE0).trans
                                  ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                                    hstepN1).trans
                                    ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                                      hstepE1).trans
                                      ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                                        hstepS).trans
                                        ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                                          hstepV6).trans
                                          hret))))))))))))))))))
  have hfwd : vecEraseSumEntryFwd = .ok (.i32 (BitVec.ofNat 32 4)) := by
    simp only [vecEraseSumEntryFwd, vecReserveStep_eq,
      vecReservePush1_eq, vecReservePush2_eq, vecErasePush3_eq,
      vecErasePlusEl_eq, vecEraseStep_eq, vecEraseRead0_eq,
      vecEraseRead1_eq, vecEraseAdd_eq, vecEraseDtor_eq,
      vecGrow_bind_ok, vecGrowOwned, vecGrowU64, vecGrowI32,
      stdVecBeginFwd]
  simp only [memEvalProgFunc, hbind, hstmt, hfwd]

/-- Transfer for `vec_erase_sum`: memory execution agrees with value
    execution (both sides compute `4`). -/
theorem memTransfer_vecEraseSumEntry (F : Nat) (hF : 6 ≤ F)
    (_h : oracleNoalias vecEraseSumEntryFunc []) :
    memEvalProgFunc vecGrowProg F vecEraseSumEntryFunc [] =
      evalProgFunc vecGrowProg F vecEraseSumEntryFunc [] := by
  rw [memEvalProgFunc_vecEraseSumEntry F hF,
    evalProgFunc_vecEraseSumEntry F hF]
