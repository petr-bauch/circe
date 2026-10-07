/-
Circe.Transfer.GrowShift — N7c backward-shift loop transfer.
Over `Circe.Transfer.GrowReloc`.
-/
import Circe.Transfer.GrowReloc
import Circe.Emit.VecCompose.Insert

/-! ## N7c backward shift: loop transfer -/

/-- The single-triple block pin at an intermediate buffer (source and
    destination are the same triple; the pin is restated after every
    descending store). -/
def shiftBlk (dst : Vec32) (len cap : Nat) : Block :=
  ⟨0, !dst.freed, (BitVec.ofNat 32 len) ::
    (BitVec.ofNat 32 cap) :: dst.val⟩

/-- The loop condition reads `0 < k` on memory too (pure variables;
    mirrors `stdVecShiftBackCond_eval`). -/
theorem memStdVecShiftBackCond_eval (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64) (k : Nat) (n doff : BitVec 64)
    (dst : Vec32) (m : Mem) (π : Layout)
    (hk64 : k < 2 ^ 64) :
    memEvalExpr (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "k"))
      (mkStdVecShiftBackEnv b len cap first last result k n doff
        dst) m π =
      .ok (.b (decide (0 < k))) := by
  have hk := mkStdVecShiftBackEnv_k b len cap first last result k n
    doff dst
  have hkv : evalExpr (.var "k")
      (mkStdVecShiftBackEnv b len cap first last result k n doff
        dst) = .ok (.u64 (BitVec.ofNat 64 k)) := by
    simp [evalExpr, hk]
  have hlit0 : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (mkStdVecShiftBackEnv b len cap first last result k n doff
        dst) = .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  have mhkv : memEvalExpr (.var "k")
      (mkStdVecShiftBackEnv b len cap first last result k n doff
        dst) m π =
      evalExpr (.var "k")
        (mkStdVecShiftBackEnv b len cap first last result k n doff
          dst) :=
    memEvalExpr_var _ _ _ _
  have mhlit0 : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (mkStdVecShiftBackEnv b len cap first last result k n doff
        dst) m π =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (mkStdVecShiftBackEnv b len cap first last result k n doff
          dst) :=
    memEvalExpr_lit _ _ _ _
  have h := memEvalExpr_ult_agree (.lit (.u64 (BitVec.ofNat 64 0)))
    (.var "k") _ _ _ mhlit0 mhkv
  have he : evalExpr
      (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "k"))
      (mkStdVecShiftBackEnv b len cap first last result k n doff
        dst) =
      .ok (.b (decide (0 < k))) := by
    have hv := evalExpr_ult_u64lit (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 k) _ _ hkv
    rw [ofNat64_ult 0 _ (by decide), ofNat64_toNat k hk64] at hv
    simpa using hv
  rw [h]
  exact he

/-- Body with a live read and a live write on memory: decrement, copy
    one word top-down, stay in the env family (mirrors
    `stdVecShiftBackBody_step_ok`; the single triple is read and
    written in lockstep). -/
theorem memStdVecShiftBackBody_step_ok (F : Nat) (b : Vec32)
    (len cap : Nat) (first last result : BitVec 64)
    (K : Nat) (n doff : BitVec 64) (dst : Vec32) (x : BitVec 32)
    (dst' : Vec32) (m : Mem) (π : Layout)
    (hKlt : K + 1 ≤ last.toNat - first.toNat)
    (hfirst : first.toNat ≤ last.toNat)
    (hlastR : last.toNat ≤ result.toNat)
    (hn : n = last - first)
    (hdoff : doff = result - n)
    (hlive : dst.freed = false)
    (hSb : last.toNat ≤ dst.val.length)
    (hDb : result.toNat ≤ dst.val.length)
    (hlen : last.toNat ≤ len)
    (hS64 : dst.val.length < 2 ^ 64)
    (hget : dst.val[first.toNat + K]? = some x)
    (hset : vecSet dst (doff.toNat + K) x = .ok dst')
    (hlay : layoutLookup π "t" = some (0, 0))
    (hfind : memFind m 0 = some (shiftBlk dst len cap)) :
    ∃ m', memEvalStmtFuel F stdVecShiftBackBody
      (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
        doff dst) m π =
      .ok ((mkStdVecShiftBackEnv b len cap first last result K n
        doff dst', m', π), .fellThrough)
      ∧ memFind m' 0 = some (shiftBlk dst' len cap) := by
  have hK64 : K + 1 < 2 ^ 64 := by omega
  have hnt : n.toNat = last.toNat - first.toNat := by
    rw [hn]; exact u64sub_toNat_exact _ _ hfirst
  have hdofft : doff.toNat = result.toNat - n.toNat := by
    rw [hdoff]; exact u64sub_toNat_exact _ _ (by omega)
  have hdec : BitVec.ofNat 64 (K + 1) - BitVec.ofNat 64 1 =
      BitVec.ofNat 64 K := shiftBack_dec K hK64
  have hsidx : (first + BitVec.ofNat 64 K).toNat =
      first.toNat + K := by
    rw [BitVec.toNat_add, ofNat64_toNat K (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hdidx : (doff + BitVec.ofNat 64 K).toNat =
      doff.toNat + K := by
    rw [BitVec.toNat_add, ofNat64_toNat K (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  have hkL := mkStdVecShiftBackEnv_k b len cap first last result
    (K + 1) n doff dst
  have hkv : evalExpr (.var "k")
      (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
        doff dst) = .ok (.u64 (BitVec.ofNat 64 (K + 1))) := by
    simp [evalExpr, hkL]
  have mhkv : memEvalExpr (.var "k")
      (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
        doff dst) m π =
      evalExpr (.var "k")
        (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
          doff dst) :=
    memEvalExpr_var _ _ _ _
  have hlit1 : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
        doff dst) = .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have mhlit1 : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
        doff dst) m π =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
          doff dst) :=
    memEvalExpr_lit _ _ _ _
  have hdece : evalExpr (.usub (.var "k") (.lit (.u64 (BitVec.ofNat 64 1))))
      (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
        doff dst) = .ok (.u64 (BitVec.ofNat 64 K)) := by
    have h := evalExpr_usub_u64u64 _ _ _ _ _ hkv hlit1
    rwa [hdec] at h
  have mhdece := memEvalExpr_usub_agree (.var "k")
    (.lit (.u64 (BitVec.ofNat 64 1))) _ _ _ mhkv mhlit1
  have hupk : envUpdate
      (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
        doff dst) "k" (.u64 (BitVec.ofNat 64 K)) =
      some (mkStdVecShiftBackEnv b len cap first last result K n
        doff dst) :=
    stdVecShiftBackEnv_update_k b len cap first last result (K + 1)
      n doff dst K
  have hasg := memEvalStmtFuel_assign F "k"
    (.usub (.var "k") (.lit (.u64 (BitVec.ofNat 64 1))))
    _ _ _ _ _ mhdece hdece hupk
  have hfirstv : evalExpr (.var "first")
      (mkStdVecShiftBackEnv b len cap first last result K n doff
        dst) = .ok (.u64 first) := by
    have h := mkStdVecShiftBackEnv_first b len cap first last
      result K n doff dst
    simp [evalExpr, h]
  have hdoffv : evalExpr (.var "doff")
      (mkStdVecShiftBackEnv b len cap first last result K n doff
        dst) = .ok (.u64 doff) := by
    have h := mkStdVecShiftBackEnv_doff b len cap first last
      result K n doff dst
    simp [evalExpr, h]
  have hkv' : evalExpr (.var "k")
      (mkStdVecShiftBackEnv b len cap first last result K n doff
        dst) = .ok (.u64 (BitVec.ofNat 64 K)) := by
    have h := mkStdVecShiftBackEnv_k b len cap first last result K
      n doff dst
    simp [evalExpr, h]
  have mhfirstv : memEvalExpr (.var "first")
      (mkStdVecShiftBackEnv b len cap first last result K n doff
        dst) m π =
      evalExpr (.var "first")
        (mkStdVecShiftBackEnv b len cap first last result K n doff
          dst) :=
    memEvalExpr_var _ _ _ _
  have mhdoffv : memEvalExpr (.var "doff")
      (mkStdVecShiftBackEnv b len cap first last result K n doff
        dst) m π =
      evalExpr (.var "doff")
        (mkStdVecShiftBackEnv b len cap first last result K n doff
          dst) :=
    memEvalExpr_var _ _ _ _
  have mhkv' : memEvalExpr (.var "k")
      (mkStdVecShiftBackEnv b len cap first last result K n doff
        dst) m π =
      evalExpr (.var "k")
        (mkStdVecShiftBackEnv b len cap first last result K n doff
          dst) :=
    memEvalExpr_var _ _ _ _
  have hsidxe : evalExpr (.uadd (.var "first") (.var "k"))
      (mkStdVecShiftBackEnv b len cap first last result K n doff
        dst) = .ok (.u64 (first + BitVec.ofNat 64 K)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hfirstv hkv'
  have hdidxe : evalExpr (.uadd (.var "doff") (.var "k"))
      (mkStdVecShiftBackEnv b len cap first last result K n doff
        dst) = .ok (.u64 (doff + BitVec.ofNat 64 K)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hdoffv hkv'
  have mhsidxe := memEvalExpr_uadd_agree (.var "first") (.var "k")
    _ _ _ mhfirstv mhkv'
  have mhdidxe := memEvalExpr_uadd_agree (.var "doff") (.var "k")
    _ _ _ mhdoffv mhkv'
  have mhsidxe_ok : memEvalExpr (.uadd (.var "first") (.var "k"))
      (mkStdVecShiftBackEnv b len cap first last result K n doff
        dst) m π = .ok (.u64 (first + BitVec.ofNat 64 K)) := by
    rw [mhsidxe]; exact hsidxe
  have mhdidxe_ok : memEvalExpr (.uadd (.var "doff") (.var "k"))
      (mkStdVecShiftBackEnv b len cap first last result K n doff
        dst) m π = .ok (.u64 (doff + BitVec.ofNat 64 K)) := by
    rw [mhdidxe]; exact hdidxe
  have hget' : dst.val[(first + BitVec.ofNat 64 K).toNat]? =
      some x := by
    rw [hsidx]; exact hget
  have hlt : (first + BitVec.ofNat 64 K).toNat < len := by
    rw [hsidx]; omega
  have hset' : vecSet dst (doff + BitVec.ofNat 64 K).toNat x =
      .ok dst' := by
    rw [hdidx]; exact hset
  have hd := mkStdVecShiftBackEnv_t b len cap first last result K n
    doff dst
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
      (mkStdVecShiftBackEnv b len cap first last result K n doff
        dst) = .ok (.i32 x) :=
    evalExpr_vgrowAt_some "t" _ _ dst len cap _ _ hd hsidxe
      hlive hget' hlt
  have mhat_ok : memEvalExpr
      (.vgrowAt "t" (.uadd (.var "first") (.var "k")))
      (mkStdVecShiftBackEnv b len cap first last result K n doff
        dst) m π = .ok (.i32 x) := by
    rw [mhat]; exact hat
  obtain ⟨m', hmstore, hfindD'⟩ := vgrowSet_lockstep m 0 0 dst
    len cap (doff + BitVec.ofNat 64 K).toNat x
    (shiftBlk dst len cap) dst' hfind rfl
    (by simp [hlive, shiftBlk]) rfl hlive hset'
  have hup : envUpdate
      (mkStdVecShiftBackEnv b len cap first last result K n
        doff dst) "t" (.stdVecOwned dst' len cap) =
      some (mkStdVecShiftBackEnv b len cap first last result K n
        doff dst') :=
    stdVecShiftBackEnv_update_t b len cap first last result K n
      doff dst dst'
  have hsetF : memEvalStmtFuel F
      (.vgrowSet "t" (.uadd (.var "doff") (.var "k"))
        (.vgrowAt "t" (.uadd (.var "first") (.var "k"))))
      (mkStdVecShiftBackEnv b len cap first last result K n
        doff dst) m π =
      .ok (((mkStdVecShiftBackEnv b len cap first last result K n
        doff dst', m', π)), .fellThrough) :=
    memEvalStmtFuel_vgrowSet F "t"
      (.uadd (.var "doff") (.var "k"))
      (.vgrowAt "t" (.uadd (.var "first") (.var "k")))
      _ _ _ (doff + BitVec.ofNat 64 K) x 0 0 dst dst' len cap
      m' _ mhdidxe_ok mhat_ok hd hlay hset' hmstore hup
  have hDbK : doff.toNat + K < dst.val.length := by omega
  have hbD' : dst' =
      ⟨dst.val.set (doff.toNat + K) x, false⟩ := by
    have h := vecSet_ok dst _ x hlive hDbK
    rw [hset] at h
    simpa using h
  have hfreeD' : dst'.freed = false := by rw [hbD']
  have hblk : shiftBlk dst' len cap =
      ⟨0, true, (BitVec.ofNat 32 len) ::
        (BitVec.ofNat 32 cap) :: dst'.val⟩ := by
    simp [shiftBlk, hfreeD']
  have hfind' : memFind m' 0 = some (shiftBlk dst' len cap) := by
    rw [hblk]; exact hfindD'
  refine ⟨m', ?_, hfind'⟩
  exact (memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _
    hasg).trans hsetF

/-- Body error on memory: a failing copy step aborts the body after a
    successful decrement (mirrors `stdVecShiftBackBody_step_err`;
    memory untouched). -/
theorem memStdVecShiftBackBody_step_err (F : Nat) (b : Vec32)
    (len cap : Nat) (first last result : BitVec 64)
    (K : Nat) (n doff : BitVec 64) (dst : Vec32) (m : Mem)
    (π : Layout) (e : Panic)
    (hK64 : K + 1 < 2 ^ 64)
    (herr : memEvalStmtFuel F
      (.vgrowSet "t" (.uadd (.var "doff") (.var "k"))
        (.vgrowAt "t" (.uadd (.var "first") (.var "k"))))
      (mkStdVecShiftBackEnv b len cap first last result K n doff
        dst) m π = .error e) :
    memEvalStmtFuel F stdVecShiftBackBody
      (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
        doff dst) m π = .error e := by
  have hkL := mkStdVecShiftBackEnv_k b len cap first last result
    (K + 1) n doff dst
  have hkv : evalExpr (.var "k")
      (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
        doff dst) = .ok (.u64 (BitVec.ofNat 64 (K + 1))) := by
    simp [evalExpr, hkL]
  have mhkv : memEvalExpr (.var "k")
      (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
        doff dst) m π =
      evalExpr (.var "k")
        (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
          doff dst) :=
    memEvalExpr_var _ _ _ _
  have hlit1 : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
        doff dst) = .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have mhlit1 : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
        doff dst) m π =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
          doff dst) :=
    memEvalExpr_lit _ _ _ _
  have hdece : evalExpr (.usub (.var "k") (.lit (.u64 (BitVec.ofNat 64 1))))
      (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
        doff dst) = .ok (.u64 (BitVec.ofNat 64 K)) := by
    have h := evalExpr_usub_u64u64 _ _ _ _ _ hkv hlit1
    rwa [shiftBack_dec K hK64] at h
  have mhdece := memEvalExpr_usub_agree (.var "k")
    (.lit (.u64 (BitVec.ofNat 64 1))) _ _ _ mhkv mhlit1
  have hasg := memEvalStmtFuel_assign F "k"
    (.usub (.var "k") (.lit (.u64 (BitVec.ofNat 64 1))))
    _ _ _ _ _ mhdece hdece
    (stdVecShiftBackEnv_update_k b len cap first last result (K + 1)
      n doff dst K)
  have hseq : memEvalStmtFuel F stdVecShiftBackBody
      (mkStdVecShiftBackEnv b len cap first last result (K + 1) n
        doff dst) m π =
      memEvalStmtFuel F
        (.vgrowSet "t" (.uadd (.var "doff") (.var "k"))
          (.vgrowAt "t" (.uadd (.var "first") (.var "k"))))
        (mkStdVecShiftBackEnv b len cap first last result K n doff
          dst) m π :=
    memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _ hasg
  exact hseq.trans herr

/-- Loop correctness on memory: the descending walk runs the backward
    blit in lockstep, threading the triple stores through memory
    (mirrors `stdVecShiftBackWhile_correct`; the single-triple pin is
    the induction invariant). -/
theorem memStdVecShiftBackWhile_correct (b : Vec32) (len cap : Nat)
    (first last result : BitVec 64)
    (F k : Nat) (n doff : BitVec 64) (dst : Vec32) (m : Mem)
    (π : Layout)
    (hk : k ≤ last.toNat - first.toNat)
    (hfirst : first.toNat ≤ last.toNat)
    (hlastR : last.toNat ≤ result.toNat)
    (hn : n = last - first)
    (hdoff : doff = result - n)
    (hlive : dst.freed = false)
    (hSb : last.toNat ≤ dst.val.length)
    (hDb : result.toNat ≤ dst.val.length)
    (hlen : last.toNat ≤ len)
    (hS64 : dst.val.length < 2 ^ 64)
    (hlay : layoutLookup π "t" = some (0, 0))
    (hfind : memFind m 0 = some (shiftBlk dst len cap))
    (hF : k + 1 ≤ F) :
    ∃ m', memEvalStmtFuel F stdVecShiftBackWhile
      (mkStdVecShiftBackEnv b len cap first last result k n doff
        dst) m π =
      match stdVecBlitBackFold dst len doff.toNat first.toNat k with
      | Except.error e => Except.error e
      | Except.ok dst' =>
        Except.ok (((mkStdVecShiftBackEnv b len cap first last
          result 0 n doff dst', m', π)), .fellThrough) := by
  induction F generalizing k dst m with
  | zero =>
    refine ⟨m, ?_⟩
    omega
  | succ F ih =>
    have hnt : n.toNat = last.toNat - first.toNat := by
      rw [hn]; exact u64sub_toNat_exact _ _ hfirst
    have hdofft : doff.toNat = result.toNat - n.toNat := by
      rw [hdoff]; exact u64sub_toNat_exact _ _ (by omega)
    have hk64 : k < 2 ^ 64 := by omega
    have hkL := mkStdVecShiftBackEnv_k b len cap first last result
      k n doff dst
    have hfirstL := mkStdVecShiftBackEnv_first b len cap first last
      result k n doff dst
    have hdoffL := mkStdVecShiftBackEnv_doff b len cap first last
      result k n doff dst
    have hkv : evalExpr (.var "k")
        (mkStdVecShiftBackEnv b len cap first last result k n doff
          dst) = .ok (.u64 (BitVec.ofNat 64 k)) := by
      simp [evalExpr, hkL]
    have hfirstv : evalExpr (.var "first")
        (mkStdVecShiftBackEnv b len cap first last result k n doff
          dst) = .ok (.u64 first) := by
      simp [evalExpr, hfirstL]
    have hdoffv : evalExpr (.var "doff")
        (mkStdVecShiftBackEnv b len cap first last result k n doff
          dst) = .ok (.u64 doff) := by
      simp [evalExpr, hdoffL]
    have mhkv : memEvalExpr (.var "k")
        (mkStdVecShiftBackEnv b len cap first last result k n doff
          dst) m π =
        evalExpr (.var "k")
          (mkStdVecShiftBackEnv b len cap first last result k n
            doff dst) :=
      memEvalExpr_var _ _ _ _
    have mhfirstv : memEvalExpr (.var "first")
        (mkStdVecShiftBackEnv b len cap first last result k n doff
          dst) m π =
        evalExpr (.var "first")
          (mkStdVecShiftBackEnv b len cap first last result k n
            doff dst) :=
      memEvalExpr_var _ _ _ _
    have mhdoffv : memEvalExpr (.var "doff")
        (mkStdVecShiftBackEnv b len cap first last result k n doff
          dst) m π =
        evalExpr (.var "doff")
          (mkStdVecShiftBackEnv b len cap first last result k n
            doff dst) :=
      memEvalExpr_var _ _ _ _
    have hsidxe : evalExpr (.uadd (.var "first") (.var "k"))
        (mkStdVecShiftBackEnv b len cap first last result k n doff
          dst) = .ok (.u64 (first + BitVec.ofNat 64 k)) :=
      evalExpr_uadd_u64 _ _ _ _ _ hfirstv hkv
    have hdidxe : evalExpr (.uadd (.var "doff") (.var "k"))
        (mkStdVecShiftBackEnv b len cap first last result k n doff
          dst) = .ok (.u64 (doff + BitVec.ofNat 64 k)) :=
      evalExpr_uadd_u64 _ _ _ _ _ hdoffv hkv
    have mhsidxe := memEvalExpr_uadd_agree (.var "first")
      (.var "k") _ _ _ mhfirstv mhkv
    have mhdidxe := memEvalExpr_uadd_agree (.var "doff")
      (.var "k") _ _ _ mhdoffv mhkv
    have mhdidxe_ok : memEvalExpr
        (.uadd (.var "doff") (.var "k"))
        (mkStdVecShiftBackEnv b len cap first last result k n doff
          dst) m π =
        .ok (.u64 (doff + BitVec.ofNat 64 k)) := by
      rw [mhdidxe]; exact hdidxe
    have hkok : (BitVec.ofNat 64 k).toNat = k := ofNat64_toNat k hk64
    have hsidx : (first + BitVec.ofNat 64 k).toNat =
        first.toNat + k := by
      rw [BitVec.toNat_add, hkok]
      exact Nat.mod_eq_of_lt (by omega)
    have hdidx : (doff + BitVec.ofNat 64 k).toNat =
        doff.toNat + k := by
      rw [BitVec.toNat_add, hkok]
      exact Nat.mod_eq_of_lt (by omega)
    by_cases hlt : 0 < k
    · obtain ⟨K, hK⟩ : ∃ K, k = K + 1 := ⟨k - 1, by omega⟩
      subst hK
      have hcond : memEvalExpr
          (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "k"))
          (mkStdVecShiftBackEnv b len cap first last result (K + 1)
            n doff dst) m π = .ok (.b true) := by
        have h := memStdVecShiftBackCond_eval b len cap first last
          result (K + 1) n doff dst m π (by omega)
        simpa using h
      have hunfold := stdVecBlitBackFold_step dst len doff.toNat
        first.toNat K
      have hsoff : first.toNat + K < len := by omega
      cases hget : dst.val[first.toNat + K]? with
      | none =>
        have hsidxK : (first + BitVec.ofNat 64 K).toNat =
            first.toNat + K := by
          rw [BitVec.toNat_add, ofNat64_toNat K (by omega)]
          exact Nat.mod_eq_of_lt (by omega)
        have hdidxK : (doff + BitVec.ofNat 64 K).toNat =
            doff.toNat + K := by
          rw [BitVec.toNat_add, ofNat64_toNat K (by omega)]
          exact Nat.mod_eq_of_lt (by omega)
        have hkv' : evalExpr (.var "k")
            (mkStdVecShiftBackEnv b len cap first last result K n
              doff dst) = .ok (.u64 (BitVec.ofNat 64 K)) := by
          have h := mkStdVecShiftBackEnv_k b len cap first last
            result K n doff dst
          simp [evalExpr, h]
        have hfirstv' : evalExpr (.var "first")
            (mkStdVecShiftBackEnv b len cap first last result K n
              doff dst) = .ok (.u64 first) := by
          have h := mkStdVecShiftBackEnv_first b len cap first last
            result K n doff dst
          simp [evalExpr, h]
        have hdoffv' : evalExpr (.var "doff")
            (mkStdVecShiftBackEnv b len cap first last result K n
              doff dst) = .ok (.u64 doff) := by
          have h := mkStdVecShiftBackEnv_doff b len cap first last
            result K n doff dst
          simp [evalExpr, h]
        have mhkv' : memEvalExpr (.var "k")
            (mkStdVecShiftBackEnv b len cap first last result K n
              doff dst) m π =
            evalExpr (.var "k")
              (mkStdVecShiftBackEnv b len cap first last result K n
                doff dst) :=
          memEvalExpr_var _ _ _ _
        have mhfirstv' : memEvalExpr (.var "first")
            (mkStdVecShiftBackEnv b len cap first last result K n
              doff dst) m π =
            evalExpr (.var "first")
              (mkStdVecShiftBackEnv b len cap first last result K n
                doff dst) :=
          memEvalExpr_var _ _ _ _
        have mhdoffv' : memEvalExpr (.var "doff")
            (mkStdVecShiftBackEnv b len cap first last result K n
              doff dst) m π =
            evalExpr (.var "doff")
              (mkStdVecShiftBackEnv b len cap first last result K n
                doff dst) :=
          memEvalExpr_var _ _ _ _
        have hsidxeK : evalExpr (.uadd (.var "first") (.var "k"))
            (mkStdVecShiftBackEnv b len cap first last result K n
              doff dst) = .ok (.u64 (first + BitVec.ofNat 64 K)) :=
          evalExpr_uadd_u64 _ _ _ _ _ hfirstv' hkv'
        have hdidxeK : evalExpr (.uadd (.var "doff") (.var "k"))
            (mkStdVecShiftBackEnv b len cap first last result K n
              doff dst) = .ok (.u64 (doff + BitVec.ofNat 64 K)) :=
          evalExpr_uadd_u64 _ _ _ _ _ hdoffv' hkv'
        have mhsidxeK := memEvalExpr_uadd_agree (.var "first")
          (.var "k") _ _ _ mhfirstv' mhkv'
        have mhdidxeK := memEvalExpr_uadd_agree (.var "doff")
          (.var "k") _ _ _ mhdoffv' mhkv'
        have mhsidxeK_ok : memEvalExpr
            (.uadd (.var "first") (.var "k"))
            (mkStdVecShiftBackEnv b len cap first last result K n
              doff dst) m π =
            .ok (.u64 (first + BitVec.ofNat 64 K)) := by
          rw [mhsidxeK]; exact hsidxeK
        have mhdidxeK_ok : memEvalExpr
            (.uadd (.var "doff") (.var "k"))
            (mkStdVecShiftBackEnv b len cap first last result K n
              doff dst) m π =
            .ok (.u64 (doff + BitVec.ofNat 64 K)) := by
          rw [mhdidxeK]; exact hdidxeK
        have hget' : dst.val[(first + BitVec.ofNat 64 K).toNat]? =
            none := by
          rw [hsidxK]; exact hget
        have hd := mkStdVecShiftBackEnv_t b len cap first last
          result K n doff dst
        have hmemLoadE : memLoad m 0 0
            ((first + BitVec.ofNat 64 K).toNat + 2) =
            .error .OOB := by
          rw [hsidxK]
          simp [memLoad, hfind, hlive, shiftBlk, hget]
        have mhatE := memEvalExpr_vgrowAt_oob_miss "t"
          (.uadd (.var "first") (.var "k")) _ _ _ dst len cap
          (first + BitVec.ofNat 64 K) 0 0 hlay hd mhsidxeK_ok
          hsidxeK hlive hmemLoadE hget'
        have mhatE_ok : memEvalExpr
            (.vgrowAt "t" (.uadd (.var "first") (.var "k")))
            (mkStdVecShiftBackEnv b len cap first last result K n
              doff dst) m π = .error .OOB := by
          have hatE : evalExpr
              (.vgrowAt "t" (.uadd (.var "first") (.var "k")))
              (mkStdVecShiftBackEnv b len cap first last result K n
                doff dst) = .error .OOB :=
            evalExpr_vgrowAt_oob_miss "t" _ _ dst len cap _ hd
              hsidxeK hlive hget'
          rw [mhatE]; exact hatE
        have herr : memEvalStmtFuel F
            (.vgrowSet "t" (.uadd (.var "doff") (.var "k"))
              (.vgrowAt "t" (.uadd (.var "first") (.var "k"))))
            (mkStdVecShiftBackEnv b len cap first last result K n
              doff dst) m π = .error .OOB := by
          cases F <;>
            simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
              mhdidxeK_ok, mhatE_ok]
        have hbody := memStdVecShiftBackBody_step_err F b len cap
          first last result K n doff dst m π .OOB (by omega) herr
        have hstep : memEvalStmtFuel (F + 1) stdVecShiftBackWhile
            (mkStdVecShiftBackEnv b len cap first last result (K + 1)
              n doff dst) m π = .error .OOB := by
          simp [stdVecShiftBackWhile, memEvalStmtFuel,
            memEvalSuccHandler, memEvalStmtWith, hcond, hbody]
        refine ⟨m, ?_⟩
        rw [hstep, hunfold]
        simp [hlive, hsoff, hget]
      | some x =>
        cases hset : vecSet dst (doff.toNat + K) x with
        | error e =>
          have hsidxK : (first + BitVec.ofNat 64 K).toNat =
              first.toNat + K := by
            rw [BitVec.toNat_add, ofNat64_toNat K (by omega)]
            exact Nat.mod_eq_of_lt (by omega)
          have hdidxK : (doff + BitVec.ofNat 64 K).toNat =
              doff.toNat + K := by
            rw [BitVec.toNat_add, ofNat64_toNat K (by omega)]
            exact Nat.mod_eq_of_lt (by omega)
          have hkv' : evalExpr (.var "k")
              (mkStdVecShiftBackEnv b len cap first last result K n
                doff dst) = .ok (.u64 (BitVec.ofNat 64 K)) := by
            have h := mkStdVecShiftBackEnv_k b len cap first last
              result K n doff dst
            simp [evalExpr, h]
          have hfirstv' : evalExpr (.var "first")
              (mkStdVecShiftBackEnv b len cap first last result K n
                doff dst) = .ok (.u64 first) := by
            have h := mkStdVecShiftBackEnv_first b len cap first last
              result K n doff dst
            simp [evalExpr, h]
          have hdoffv' : evalExpr (.var "doff")
              (mkStdVecShiftBackEnv b len cap first last result K n
                doff dst) = .ok (.u64 doff) := by
            have h := mkStdVecShiftBackEnv_doff b len cap first last
              result K n doff dst
            simp [evalExpr, h]
          have mhkv' : memEvalExpr (.var "k")
              (mkStdVecShiftBackEnv b len cap first last result K n
                doff dst) m π =
              evalExpr (.var "k")
                (mkStdVecShiftBackEnv b len cap first last result K n
                  doff dst) :=
            memEvalExpr_var _ _ _ _
          have mhfirstv' : memEvalExpr (.var "first")
              (mkStdVecShiftBackEnv b len cap first last result K n
                doff dst) m π =
              evalExpr (.var "first")
                (mkStdVecShiftBackEnv b len cap first last result K n
                  doff dst) :=
            memEvalExpr_var _ _ _ _
          have mhdoffv' : memEvalExpr (.var "doff")
              (mkStdVecShiftBackEnv b len cap first last result K n
                doff dst) m π =
              evalExpr (.var "doff")
                (mkStdVecShiftBackEnv b len cap first last result K n
                  doff dst) :=
            memEvalExpr_var _ _ _ _
          have hsidxeK : evalExpr (.uadd (.var "first") (.var "k"))
              (mkStdVecShiftBackEnv b len cap first last result K n
                doff dst) = .ok (.u64 (first + BitVec.ofNat 64 K)) :=
            evalExpr_uadd_u64 _ _ _ _ _ hfirstv' hkv'
          have hdidxeK : evalExpr (.uadd (.var "doff") (.var "k"))
              (mkStdVecShiftBackEnv b len cap first last result K n
                doff dst) = .ok (.u64 (doff + BitVec.ofNat 64 K)) :=
            evalExpr_uadd_u64 _ _ _ _ _ hdoffv' hkv'
          have mhsidxeK := memEvalExpr_uadd_agree (.var "first")
            (.var "k") _ _ _ mhfirstv' mhkv'
          have mhdidxeK := memEvalExpr_uadd_agree (.var "doff")
            (.var "k") _ _ _ mhdoffv' mhkv'
          have mhsidxeK_ok : memEvalExpr
              (.uadd (.var "first") (.var "k"))
              (mkStdVecShiftBackEnv b len cap first last result K n
                doff dst) m π =
              .ok (.u64 (first + BitVec.ofNat 64 K)) := by
            rw [mhsidxeK]; exact hsidxeK
          have mhdidxeK_ok : memEvalExpr
              (.uadd (.var "doff") (.var "k"))
              (mkStdVecShiftBackEnv b len cap first last result K n
                doff dst) m π =
              .ok (.u64 (doff + BitVec.ofNat 64 K)) := by
            rw [mhdidxeK]; exact hdidxeK
          have hget' : dst.val[(first + BitVec.ofNat 64 K).toNat]? =
              some x := by
            rw [hsidxK]; exact hget
          have hltlen : (first + BitVec.ofNat 64 K).toNat < len := by
            rw [hsidxK]; omega
          have hd := mkStdVecShiftBackEnv_t b len cap first last
            result K n doff dst
          have hmemLoad : memLoad m 0 0
              ((first + BitVec.ofNat 64 K).toNat + 2) = .ok x := by
            rw [hsidxK]
            simp [memLoad, hfind, hlive, shiftBlk, hget]
          have mhat := memEvalExpr_vgrowAt_hit "t"
            (.uadd (.var "first") (.var "k")) _ _ _ dst len cap
            (first + BitVec.ofNat 64 K) x 0 0 hlay hd mhsidxeK_ok
            hsidxeK hlive hmemLoad hget' hltlen
          have hat : evalExpr
              (.vgrowAt "t" (.uadd (.var "first") (.var "k")))
              (mkStdVecShiftBackEnv b len cap first last result K n
                doff dst) = .ok (.i32 x) :=
            evalExpr_vgrowAt_some "t" _ _ dst len cap _ _ hd
              hsidxeK hlive hget' hltlen
          have mhat_ok : memEvalExpr
              (.vgrowAt "t" (.uadd (.var "first") (.var "k")))
              (mkStdVecShiftBackEnv b len cap first last result K n
                doff dst) m π = .ok (.i32 x) := by
            rw [mhat]; exact hat
          have hset' : vecSet dst (doff + BitVec.ofNat 64 K).toNat
              x = .error e := by
            rw [hdidxK]; exact hset
          have herr : memEvalStmtFuel F
              (.vgrowSet "t" (.uadd (.var "doff") (.var "k"))
                (.vgrowAt "t" (.uadd (.var "first") (.var "k"))))
              (mkStdVecShiftBackEnv b len cap first last result K n
                doff dst) m π = .error e :=
            memEvalStmtFuel_vgrowSet_err F "t"
              (.uadd (.var "doff") (.var "k"))
              (.vgrowAt "t" (.uadd (.var "first") (.var "k")))
              _ _ _ (doff + BitVec.ofNat 64 K) x 0 0 dst len cap
              e mhdidxeK_ok mhat_ok hd hlay hset'
          have hbody := memStdVecShiftBackBody_step_err F b len cap
            first last result K n doff dst m π e (by omega) herr
          have hstep : memEvalStmtFuel (F + 1) stdVecShiftBackWhile
              (mkStdVecShiftBackEnv b len cap first last result
                (K + 1) n doff dst) m π = .error e := by
            simp [stdVecShiftBackWhile, memEvalStmtFuel,
              memEvalSuccHandler, memEvalStmtWith, hcond, hbody]
          refine ⟨m, ?_⟩
          rw [hstep, hunfold]
          simp [hlive, hsoff, hget, hset]
        | ok dst' =>
          have hKlt : K + 1 ≤ last.toNat - first.toNat := hk
          obtain ⟨m₁, hbodyEq, hfind'⟩ :=
            memStdVecShiftBackBody_step_ok F b len cap first last
              result K n doff dst x dst' m π hKlt hfirst hlastR
              hn hdoff hlive hSb hDb hlen hS64 hget hset hlay
              hfind
          have hstep : memEvalStmtFuel (F + 1) stdVecShiftBackWhile
              (mkStdVecShiftBackEnv b len cap first last result
                (K + 1) n doff dst) m π =
              memEvalStmtFuel F stdVecShiftBackWhile
                (mkStdVecShiftBackEnv b len cap first last result K
                  n doff dst') m₁ π := by
            simp [stdVecShiftBackWhile, memEvalStmtFuel,
              memEvalSuccHandler, memEvalStmtWith, hcond, hbodyEq]
          have hDbK : doff.toNat + K < dst.val.length := by omega
          have hbD' : dst' =
              ⟨dst.val.set (doff.toNat + K) x, false⟩ := by
            have h := vecSet_ok dst _ x hlive hDbK
            rw [hset] at h
            simpa using h
          have hlenD' : dst'.val.length = dst.val.length := by
            simp [hbD', List.length_set]
          have hfreeD' : dst'.freed = false := by rw [hbD']
          have hfindI : memFind m₁ 0 = some (shiftBlk dst' len cap) :=
            hfind'
          obtain ⟨m₂, hihEq⟩ := ih K dst' m₁ (by omega) hfreeD'
            (by rw [hlenD']; exact hSb)
            (by rw [hlenD']; exact hDb)
            (by rw [hlenD']; exact hS64) hfindI (by omega)
          refine ⟨m₂, ?_⟩
          rw [hstep, hunfold]
          simp only [hlive, hsoff, hget, hset]
          exact hihEq
    · have hkk : k = 0 := by omega
      subst hkk
      have hk64c : (0 : Nat) < 2 ^ 64 := by decide
      have hcondF : memEvalExpr
          (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "k"))
          (mkStdVecShiftBackEnv b len cap first last result 0 n
            doff dst) m π =
          .ok (.b false) := by
        have h := memStdVecShiftBackCond_eval b len cap first last
          result 0 n doff dst m π hk64c
        have hf : decide (0 < 0) = false := by simp
        rwa [hf] at h
      have hzero : stdVecBlitBackFold dst len doff.toNat first.toNat
          0 = .ok dst := rfl
      have hLHS : memEvalStmtFuel (F + 1) stdVecShiftBackWhile
          (mkStdVecShiftBackEnv b len cap first last result 0 n
            doff dst) m π =
          .ok (((mkStdVecShiftBackEnv b len cap first last result 0
            n doff dst, m, π)),
            .fellThrough) := by
        simp [stdVecShiftBackWhile, memEvalStmtFuel,
          memEvalSuccHandler, memEvalStmtWith, hcondF]
      have hRHS : (match stdVecBlitBackFold dst len doff.toNat
          first.toNat 0 with
        | Except.error e => Except.error e
        | Except.ok dst' =>
          Except.ok (((mkStdVecShiftBackEnv b len cap first last
            result 0 n doff dst', m, π)),
            Outcome.fellThrough)) =
          .ok (((mkStdVecShiftBackEnv b len cap first last result 0
            n doff dst, m, π)),
            Outcome.fellThrough) := by
        rw [hzero]
      refine ⟨m, ?_⟩
      exact hLHS.trans hRHS.symm

/-- `memEval` for the backward shift: bind the triple, run the
    counter setup, then the descending loop (mirrors
    `evalFuncFuel_stdVecShiftBack`; memory is discarded at the
    function boundary, so only the value equation survives). -/
theorem memEvalFuncFuel_stdVecShiftBack (F : Nat) (b : Vec32)
    (len cap : Nat) (first last result : BitVec 64)
    (hfirst : first.toNat ≤ last.toNat)
    (hlastR : last.toNat ≤ result.toNat)
    (hlive : b.freed = false)
    (hSb : last.toNat ≤ b.val.length)
    (hDb : result.toNat ≤ b.val.length)
    (hlen : last.toNat ≤ len)
    (hS64 : b.val.length < 2 ^ 64)
    (hF : last.toNat - first.toNat + 1 ≤ F) :
    memEvalFuncFuel F stdVecShiftBackFunc
      [.stdVecOwned b len cap, .u64 first, .u64 last, .u64 result] =
      stdVecShiftBackFwd b len cap first last result := by
  have hX : (last - first).toNat = last.toNat - first.toNat :=
    u64sub_toNat_exact _ _ hfirst
  have hnk : last - first =
      BitVec.ofNat 64 (last.toNat - first.toNat) := by
    apply BitVec.eq_of_toNat_eq
    rw [hX, ofNat64_toNat _ (by omega)]
  have hb : bindMemArgs stdVecShiftBackFunc.args
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
    exact bindMemArgs_stdVecShiftBack b len cap first last result
  have hbody : stdVecShiftBackFunc.body =
      .seq (.let_ "k" (.u 64) (.usub (.var "last") (.var "first")))
      (.seq (.let_ "n" (.u 64) (.usub (.var "last") (.var "first")))
      (.seq (.let_ "doff" (.u 64)
              (.usub (.var "result") (.var "n")))
      (.seq stdVecShiftBackWhile
        (.return_ (.var "t"))))) := rfl
  have hlast0 : evalExpr (.var "last")
      [("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] = .ok (.u64 last) := by
    simp [evalExpr, envLookup,
      show ("last" : String) ≠ "t" by decide,
      show ("last" : String) ≠ "first" by decide]
  have hfirst0 : evalExpr (.var "first")
      [("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] = .ok (.u64 first) := by
    simp [evalExpr, envLookup,
      show ("first" : String) ≠ "t" by decide]
  have mhlast0 : memEvalExpr (.var "last")
      [("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.var "last")
        [("t", .stdVecOwned b len cap),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)] :=
    memEvalExpr_var _ _ _ _
  have mhfirst0 : memEvalExpr (.var "first")
      [("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.var "first")
        [("t", .stdVecOwned b len cap),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)] :=
    memEvalExpr_var _ _ _ _
  have mhnEval0 := memEvalExpr_usub_agree (.var "last")
    (.var "first") _ _ _ mhlast0 mhfirst0
  have hnEval0 : evalExpr (.usub (.var "last") (.var "first"))
      [("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] =
      .ok (.u64 (BitVec.ofNat 64 (last.toNat - first.toNat))) := by
    have h := evalExpr_usub_u64u64 _ _ _ _ _ hlast0 hfirst0
    rwa [hnk] at h
  have me1 : memEvalStmtFuel F
      (.let_ "k" (.u 64) (.usub (.var "last") (.var "first")))
      [("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)]
      (tripleMem b len cap) [("t", 0, 0)] =
      .ok (((("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat))) ::
        [("t", .stdVecOwned b len cap),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)]),
        tripleMem b len cap, [("t", 0, 0)]),
        .fellThrough) :=
    memEvalStmtFuel_let_pure F "k" (.u 64)
      (.usub (.var "last") (.var "first")) _ _ _ _
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) mhnEval0 hnEval0
  have hlast1 : evalExpr (.var "last")
      [(("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat)))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] = .ok (.u64 last) := by
    simp [evalExpr, envLookup,
      show ("last" : String) ≠ "k" by decide,
      show ("last" : String) ≠ "t" by decide,
      show ("last" : String) ≠ "first" by decide]
  have hfirst1 : evalExpr (.var "first")
      [(("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat)))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] = .ok (.u64 first) := by
    simp [evalExpr, envLookup,
      show ("first" : String) ≠ "k" by decide,
      show ("first" : String) ≠ "t" by decide]
  have mhlast1 : memEvalExpr (.var "last")
      ((("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat)))) ::
        [("t", .stdVecOwned b len cap),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)])
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.var "last")
        ((("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat)))) ::
          [("t", .stdVecOwned b len cap),
            ("first", .u64 first), ("last", .u64 last),
            ("result", .u64 result)]) :=
    memEvalExpr_var _ _ _ _
  have mhfirst1 : memEvalExpr (.var "first")
      ((("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat)))) ::
        [("t", .stdVecOwned b len cap),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)])
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.var "first")
        ((("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat)))) ::
          [("t", .stdVecOwned b len cap),
            ("first", .u64 first), ("last", .u64 last),
            ("result", .u64 result)]) :=
    memEvalExpr_var _ _ _ _
  have mhnEval1 := memEvalExpr_usub_agree (.var "last")
    (.var "first") _ _ _ mhlast1 mhfirst1
  have hnEval1 : evalExpr (.usub (.var "last") (.var "first"))
      [(("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat)))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] =
      .ok (.u64 (last - first)) :=
    evalExpr_usub_u64u64 _ _ _ _ _ hlast1 hfirst1
  have me2 : memEvalStmtFuel F
      (.let_ "n" (.u 64) (.usub (.var "last") (.var "first")))
      [(("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat)))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)]
      (tripleMem b len cap) [("t", 0, 0)] =
      .ok (((("n", .u64 (last - first)) ::
        ((("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat)))) ::
        [("t", .stdVecOwned b len cap),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)])),
        tripleMem b len cap, [("t", 0, 0)]),
        .fellThrough) :=
    memEvalStmtFuel_let_pure F "n" (.u 64)
      (.usub (.var "last") (.var "first")) _ _ _ _
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) mhnEval1 hnEval1
  have hres : evalExpr (.var "result")
      [(("n", .u64 (last - first))),
        (("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat)))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] = .ok (.u64 result) := by
    simp [evalExpr, envLookup,
      show ("result" : String) ≠ "n" by decide,
      show ("result" : String) ≠ "k" by decide,
      show ("result" : String) ≠ "t" by decide,
      show ("result" : String) ≠ "first" by decide,
      show ("result" : String) ≠ "last" by decide]
  have hnV : evalExpr (.var "n")
      [(("n", .u64 (last - first))),
        (("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat)))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] =
      .ok (.u64 (last - first)) := by
    simp [evalExpr, envLookup]
  have mhres : memEvalExpr (.var "result")
      [("n", .u64 (last - first)),
        ("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.var "result")
        [("n", .u64 (last - first)),
          ("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat))),
          ("t", .stdVecOwned b len cap),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)] :=
    memEvalExpr_var _ _ _ _
  have mhnV : memEvalExpr (.var "n")
      [("n", .u64 (last - first)),
        ("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.var "n")
        [("n", .u64 (last - first)),
          ("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat))),
          ("t", .stdVecOwned b len cap),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)] :=
    memEvalExpr_var _ _ _ _
  have mhdoffEval := memEvalExpr_usub_agree (.var "result")
    (.var "n") _ _ _ mhres mhnV
  have hdoffEval : evalExpr (.usub (.var "result") (.var "n"))
      [(("n", .u64 (last - first))),
        (("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat)))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] =
      .ok (.u64 (result - (last - first))) :=
    evalExpr_usub_u64u64 _ _ _ _ _ hres hnV
  have me3 : memEvalStmtFuel F
      (.let_ "doff" (.u 64) (.usub (.var "result") (.var "n")))
      [(("n", .u64 (last - first))),
        (("k", .u64 (BitVec.ofNat 64 (last.toNat - first.toNat)))),
        ("t", .stdVecOwned b len cap),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)]
      (tripleMem b len cap) [("t", 0, 0)] =
      .ok ((mkStdVecShiftBackEnv b len cap first last result
        (last.toNat - first.toNat) (last - first)
        (result - (last - first)) b,
        tripleMem b len cap, [("t", 0, 0)]),
        .fellThrough) :=
    memEvalStmtFuel_let_pure F "doff" (.u 64)
      (.usub (.var "result") (.var "n")) _ _ _ _
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) mhdoffEval hdoffEval
  have hF0 : last.toNat - first.toNat + 1 ≤ F := hF
  have hdofft0 : result.toNat - (last.toNat - first.toNat) =
      (result - (last - first)).toNat := by
    rw [u64sub_toNat_exact _ _ (by omega), hX]
  have hlay₀ : layoutLookup [("t", 0, 0)] "t" = some (0, 0) := by
    simp [layoutLookup]
  have hfind₀ : memFind (tripleMem b len cap) 0 =
      some (shiftBlk b len cap) := by
    simp [tripleMem, memFind, shiftBlk]
  obtain ⟨mL, hloop0⟩ := memStdVecShiftBackWhile_correct b len cap
    first last result F (last.toNat - first.toNat) (last - first)
    (result - (last - first)) b (tripleMem b len cap) [("t", 0, 0)]
    (Nat.le_refl _) hfirst hlastR rfl rfl hlive hSb hDb hlen hS64
    hlay₀ hfind₀ hF0
  cases hblit : stdVecBlitBackFold b len
      ((result - (last - first)).toNat) first.toNat
      (last.toNat - first.toNat) with
  | error e =>
    have hloopE : memEvalStmtFuel F stdVecShiftBackWhile
        (mkStdVecShiftBackEnv b len cap first last result
          (last.toNat - first.toNat) (last - first)
          (result - (last - first)) b)
        (tripleMem b len cap) [("t", 0, 0)] = .error e := by
      rw [hblit] at hloop0
      exact hloop0
    have hfwd : stdVecShiftBackFwd b len cap first last result =
        .error e := by
      simp only [stdVecShiftBackFwd, hdofft0, hblit]
    have hstmt : memEvalStmtFuel F stdVecShiftBackFunc.body
        [("t", .stdVecOwned b len cap),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)]
        (tripleMem b len cap) [("t", 0, 0)] = .error e := by
      rw [hbody]
      exact (memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _
        me1).trans
        ((memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _
          me2).trans
          ((memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _
            me3).trans
            (memEvalStmtFuel_seq_err F _ _ _ _ _ _ hloopE)))
    simp [memEvalFuncFuel, hb, hstmt, hfwd]
  | ok b' =>
    have hloopO : memEvalStmtFuel F stdVecShiftBackWhile
        (mkStdVecShiftBackEnv b len cap first last result
          (last.toNat - first.toNat) (last - first)
          (result - (last - first)) b)
        (tripleMem b len cap) [("t", 0, 0)] =
        .ok (((mkStdVecShiftBackEnv b len cap first last result 0
          (last - first) (result - (last - first)) b',
          mL, [("t", 0, 0)])),
          .fellThrough) := by
      rw [hblit] at hloop0
      exact hloop0
    have hret : envLookup
        (mkStdVecShiftBackEnv b len cap first last result 0
          (last - first) (result - (last - first)) b') "t" =
        some (.stdVecOwned b' len cap) :=
      mkStdVecShiftBackEnv_t b len cap first last result 0
        (last - first) (result - (last - first)) b'
    have hvar : evalExpr (.var "t")
        (mkStdVecShiftBackEnv b len cap first last result 0
          (last - first) (result - (last - first)) b') =
        .ok (.stdVecOwned b' len cap) := by
      simp [evalExpr, hret]
    have mhvar : memEvalExpr (.var "t")
        (mkStdVecShiftBackEnv b len cap first last result 0
          (last - first) (result - (last - first)) b') mL
        [("t", 0, 0)] =
        evalExpr (.var "t")
          (mkStdVecShiftBackEnv b len cap first last result 0
            (last - first) (result - (last - first)) b') :=
      memEvalExpr_var _ _ _ _
    have hfwd : stdVecShiftBackFwd b len cap first last result =
        .ok (.stdVecOwned b' len cap) := by
      simp only [stdVecShiftBackFwd, hdofft0, hblit]
    have hstmt : memEvalStmtFuel F stdVecShiftBackFunc.body
        [("t", .stdVecOwned b len cap),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)]
        (tripleMem b len cap) [("t", 0, 0)] =
        .ok (((mkStdVecShiftBackEnv b len cap first last result 0
          (last - first) (result - (last - first)) b', mL,
          [("t", 0, 0)])),
          .returned (.stdVecOwned b' len cap)) := by
      rw [hbody]
      exact (memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _
        me1).trans
        ((memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _
          me2).trans
          ((memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _
            me3).trans
            ((memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _
              hloopO).trans
              (memEvalStmtFuel_return F _ _ _ _ _ mhvar hvar))))
    simp [memEvalFuncFuel, hb, hstmt, hfwd]

/-- Transfer for the backward shift: memory execution agrees with
    value execution (both sides reduce to the backward-blit
    forward). -/
theorem memTransfer_stdVecShiftBack (F : Nat) (b : Vec32)
    (len cap : Nat) (first last result : BitVec 64)
    (hfirst : first.toNat ≤ last.toNat)
    (hlastR : last.toNat ≤ result.toNat)
    (hlive : b.freed = false)
    (hSb : last.toNat ≤ b.val.length)
    (hDb : result.toNat ≤ b.val.length)
    (hlen : last.toNat ≤ len)
    (hS64 : b.val.length < 2 ^ 64)
    (hF : last.toNat - first.toNat + 1 ≤ F)
    (_h : oracleNoalias stdVecShiftBackFunc
      [.stdVecOwned b len cap, .u64 first, .u64 last,
        .u64 result]) :
    memEvalFuncFuel F stdVecShiftBackFunc
      [.stdVecOwned b len cap, .u64 first, .u64 last,
        .u64 result] =
      evalFuncFuel F stdVecShiftBackFunc
        [.stdVecOwned b len cap, .u64 first, .u64 last,
          .u64 result] := by
  rw [memEvalFuncFuel_stdVecShiftBack F b len cap first last result
    hfirst hlastR hlive hSb hDb hlen hS64 hF,
    evalFuncFuel_stdVecShiftBack F b len cap first last result
      hfirst hlastR hlive hSb hDb hlen hS64 hF]
