/-
Circe.Transfer.GrowReloc — N4d-iv-b1 relocate loop transfer.
Over `Circe.Transfer.GrowLeaves`.
-/
import Circe.Transfer.GrowLeaves

/-! ## N4d-iv-b1 relocate: loop transfer -/

/-- Entry memory for relocate: source takes address `1`, destination
    address `0` (unwind order), each in the two-block form. -/
def relocMem (bS : Vec32) (lenS capS : Nat) (bD : Vec32)
    (lenD capD : Nat) : Mem :=
  ⟨2, [(1, ⟨1, !bS.freed, (BitVec.ofNat 32 lenS) ::
    (BitVec.ofNat 32 capS) :: bS.val⟩),
    (1, ⟨1, true, (BitVec.ofNat 32 lenS) ::
    (BitVec.ofNat 32 capS) :: bS.val⟩),
    (0, ⟨0, !bD.freed, (BitVec.ofNat 32 lenD) ::
    (BitVec.ofNat 32 capD) :: bD.val⟩),
    (0, ⟨0, true, (BitVec.ofNat 32 lenD) ::
    (BitVec.ofNat 32 capD) :: bD.val⟩)], []⟩

/-- The source block pin (read-only through the loop). -/
def relocSrcBlk (bS : Vec32) (lenS capS : Nat) : Block :=
  ⟨1, !bS.freed, (BitVec.ofNat 32 lenS) ::
    (BitVec.ofNat 32 capS) :: bS.val⟩

/-- The destination block pin at an intermediate buffer. -/
def relocDstBlk (dst : Vec32) (lenD capD : Nat) : Block :=
  ⟨0, !dst.freed, (BitVec.ofNat 32 lenD) ::
    (BitVec.ofNat 32 capD) :: dst.val⟩

/-- The loop condition reads the counter against the trip count on
    memory too (pure variables; mirrors `stdVecRelocCond_eval`). -/
theorem memStdVecRelocCond_eval (bS : Vec32) (lenS capS : Nat)
    (bD : Vec32) (lenD capD : Nat) (first last result : BitVec 64)
    (k : Nat) (n : BitVec 64) (dst : Vec32) (m : Mem) (π : Layout)
    (hk64 : k < 2 ^ 64) :
    memEvalExpr (.ult (.var "k") (.var "n"))
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
        k n dst) m π =
      .ok (.b (decide (k < n.toNat))) := by
  have hk := mkStdVecRelocEnv_k bS lenS capS bD lenD capD first last
    result k n dst
  have hn := mkStdVecRelocEnv_n bS lenS capS bD lenD capD first last
    result k n dst
  have hkv : evalExpr (.var "k")
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
        k n dst) =
      .ok (.u64 (BitVec.ofNat 64 k)) := by
    simp [evalExpr, hk]
  have hnv : evalExpr (.var "n")
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
        k n dst) =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  have hmkv : memEvalExpr (.var "k")
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
        k n dst) m π =
      evalExpr (.var "k")
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          k n dst) :=
    memEvalExpr_var _ _ _ _
  have hmnv : memEvalExpr (.var "n")
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
        k n dst) m π =
      evalExpr (.var "n")
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          k n dst) :=
    memEvalExpr_var _ _ _ _
  have h := memEvalExpr_ult_agree (.var "k") (.var "n") _ _ _
    hmkv hmnv
  have he : evalExpr (.ult (.var "k") (.var "n"))
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
        k n dst) =
      .ok (.b (decide (k < n.toNat))) := by
    have hv := evalExpr_ult_u64 _ _ _ _ _ hkv hnv
    rwa [ofNat64_ult k n hk64] at hv
  rw [h]
  exact he

/-- Body with a live read and a live write on memory: copy one word
    and step (mirrors `stdVecRelocBody_step_ok`; the destination
    store runs in lockstep, the source pin survives by framing). -/
theorem memStdVecRelocBody_step_ok (F : Nat) (bS : Vec32)
    (lenS capS : Nat) (bD : Vec32) (lenD capD : Nat)
    (first last result : BitVec 64)
    (k : Nat) (n : BitVec 64) (dst : Vec32) (x : BitVec 32)
    (bD' : Vec32) (m : Mem) (π : Layout)
    (hkc : k < last.toNat - first.toNat)
    (hfirst : first.toNat ≤ last.toNat)
    (hliveS : bS.freed = false) (hliveD : dst.freed = false)
    (hSb : last.toNat ≤ bS.val.length)
    (hDb : result.toNat + (last.toNat - first.toNat) ≤ dst.val.length)
    (hlenS : last.toNat ≤ lenS)
    (hS64 : bS.val.length < 2 ^ 64) (hD64 : dst.val.length < 2 ^ 64)
    (hget : bS.val[first.toNat + k]? = some x)
    (hset : vecSet dst (result.toNat + k) x = .ok bD')
    (hlayS : layoutLookup π "src" = some (1, 1))
    (hlayD : layoutLookup π "dst" = some (0, 0))
    (hsrcFind : memFind m 1 = some (relocSrcBlk bS lenS capS))
    (hdstFind : memFind m 0 = some (relocDstBlk dst lenD capD)) :
    ∃ m', memEvalStmtFuel F stdVecRelocBody
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
        k n dst) m π =
      .ok ((mkStdVecRelocEnv bS lenS capS bD lenD capD first last
        result (k + 1) n bD', m', π), .fellThrough)
      ∧ memFind m' 0 = some (relocDstBlk bD' lenD capD)
      ∧ memFind m' 1 = memFind m 1 := by
  have hk64 : k < 2 ^ 64 := by omega
  have hkok : (BitVec.ofNat 64 k).toNat = k := ofNat64_toNat k hk64
  have hsidx : (first + BitVec.ofNat 64 k).toNat =
      first.toNat + k := by
    rw [BitVec.toNat_add, hkok]
    exact Nat.mod_eq_of_lt (by omega)
  have hdidx : (result + BitVec.ofNat 64 k).toNat =
      result.toNat + k := by
    rw [BitVec.toNat_add, hkok]
    exact Nat.mod_eq_of_lt (by omega)
  have hs := mkStdVecRelocEnv_src bS lenS capS bD lenD capD first
    last result k n dst
  have hd := mkStdVecRelocEnv_dst bS lenS capS bD lenD capD first
    last result k n dst
  have hfirstL := mkStdVecRelocEnv_first bS lenS capS bD lenD capD
    first last result k n dst
  have hresultL := mkStdVecRelocEnv_result bS lenS capS bD lenD capD
    first last result k n dst
  have hkL := mkStdVecRelocEnv_k bS lenS capS bD lenD capD first
    last result k n dst
  have hkv : evalExpr (.var "k")
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        dst) = .ok (.u64 (BitVec.ofNat 64 k)) := by
    simp [evalExpr, hkL]
  have hfirstv : evalExpr (.var "first")
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        dst) = .ok (.u64 first) := by
    simp [evalExpr, hfirstL]
  have hresultv : evalExpr (.var "result")
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        dst) = .ok (.u64 result) := by
    simp [evalExpr, hresultL]
  have mhkv : memEvalExpr (.var "k")
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        dst) m π =
      evalExpr (.var "k")
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          k n dst) :=
    memEvalExpr_var _ _ _ _
  have mhfirstv : memEvalExpr (.var "first")
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        dst) m π =
      evalExpr (.var "first")
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          k n dst) :=
    memEvalExpr_var _ _ _ _
  have mhresultv : memEvalExpr (.var "result")
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        dst) m π =
      evalExpr (.var "result")
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          k n dst) :=
    memEvalExpr_var _ _ _ _
  have hsidxe : evalExpr (.uadd (.var "first") (.var "k"))
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        dst) = .ok (.u64 (first + BitVec.ofNat 64 k)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hfirstv hkv
  have hdidxe : evalExpr (.uadd (.var "result") (.var "k"))
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        dst) = .ok (.u64 (result + BitVec.ofNat 64 k)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hresultv hkv
  have mhsidxe := memEvalExpr_uadd_agree (.var "first") (.var "k")
    _ _ _ mhfirstv mhkv
  have mhdidxe := memEvalExpr_uadd_agree (.var "result") (.var "k")
    _ _ _ mhresultv mhkv
  have hget' : bS.val[(first + BitVec.ofNat 64 k).toNat]? = some x := by
    rw [hsidx]; exact hget
  have hlt : (first + BitVec.ofNat 64 k).toNat < lenS := by
    rw [hsidx]; omega
  have hset' : vecSet dst (result + BitVec.ofNat 64 k).toNat x =
      .ok bD' := by
    rw [hdidx]; exact hset
  have hmemLoad : memLoad m 1 1
      ((first + BitVec.ofNat 64 k).toNat + 2) = .ok x := by
    rw [hsidx]
    simp [memLoad, hsrcFind, hliveS, relocSrcBlk, hget]
  have mhat := memEvalExpr_vgrowAt_hit "src"
    (.uadd (.var "first") (.var "k")) _ _ _ bS lenS capS
    (first + BitVec.ofNat 64 k) x 1 1 hlayS hs mhsidxe hsidxe
    hliveS hmemLoad hget' hlt
  have hat : evalExpr
      (.vgrowAt "src" (.uadd (.var "first") (.var "k")))
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        dst) = .ok (.i32 x) :=
    evalExpr_vgrowAt_some "src" _ _ bS lenS capS _ _ hs
      hsidxe hliveS hget' hlt
  obtain ⟨m', hmstore, hfindD'⟩ := vgrowSet_lockstep m 0 0 dst
    lenD capD (result + BitVec.ofNat 64 k).toNat x
    (relocDstBlk dst lenD capD) bD' hdstFind rfl
    (by simp [hliveD, relocDstBlk]) rfl hliveD hset'
  have hup : envUpdate
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        dst) "dst" (.stdVecOwned bD' lenD capD) =
      some (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
        result k n bD') :=
    stdVecRelocEnv_update_dst bS lenS capS bD lenD capD first last
      result k n dst bD'
  have mhdidxe_ok : memEvalExpr (.uadd (.var "result") (.var "k"))
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        dst) m π =
      .ok (.u64 (result + BitVec.ofNat 64 k)) := by
    rw [mhdidxe]; exact hdidxe
  have mhat_ok : memEvalExpr
      (.vgrowAt "src" (.uadd (.var "first") (.var "k")))
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        dst) m π = .ok (.i32 x) := by
    rw [mhat]; exact hat
  have hsetF : memEvalStmtFuel F
      (.vgrowSet "dst" (.uadd (.var "result") (.var "k"))
        (.vgrowAt "src" (.uadd (.var "first") (.var "k"))))
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        dst) m π =
      .ok (((mkStdVecRelocEnv bS lenS capS bD lenD capD first last
        result k n bD', m', π)), .fellThrough) :=
    memEvalStmtFuel_vgrowSet F "dst"
      (.uadd (.var "result") (.var "k"))
      (.vgrowAt "src" (.uadd (.var "first") (.var "k")))
      _ _ _ (result + BitVec.ofNat 64 k) x 0 0 dst bD' lenD capD
      m' _ mhdidxe_ok mhat_ok hd hlayD hset' hmstore hup
  have hkv' : evalExpr (.var "k")
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        bD') = .ok (.u64 (BitVec.ofNat 64 k)) := by
    have h := mkStdVecRelocEnv_k bS lenS capS bD lenD capD first last
      result k n bD'
    simp [evalExpr, h]
  have mhkv' : memEvalExpr (.var "k")
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        bD') m' π =
      evalExpr (.var "k")
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          k n bD') :=
    memEvalExpr_var _ _ _ _
  have hlit1 : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        bD') = .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have mhlit1 : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        bD') m' π =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          k n bD') :=
    memEvalExpr_lit _ _ _ _
  have hincr : evalExpr
      (.uadd (.var "k") (.lit (.u64 (BitVec.ofNat 64 1))))
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        bD') = .ok (.u64 (BitVec.ofNat 64 (k + 1))) := by
    have h := evalExpr_uadd_u64 _ _ _ _ _ hkv' hlit1
    rwa [ofNat64_add_one k] at h
  have mhincr : memEvalExpr
      (.uadd (.var "k") (.lit (.u64 (BitVec.ofNat 64 1))))
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        bD') m' π =
      evalExpr
        (.uadd (.var "k") (.lit (.u64 (BitVec.ofNat 64 1))))
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          k n bD') :=
    memEvalExpr_uadd_agree (.var "k")
      (.lit (.u64 (BitVec.ofNat 64 1))) _ _ _ mhkv' mhlit1
  have hupk : envUpdate
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        bD') "k" (.u64 (BitVec.ofNat 64 (k + 1))) =
      some (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
        result (k + 1) n bD') :=
    stdVecRelocEnv_update_k bS lenS capS bD lenD capD first last
      result k (k + 1) n bD'
  have hasg := memEvalStmtFuel_assign F "k"
    (.uadd (.var "k") (.lit (.u64 (BitVec.ofNat 64 1))))
    _ _ _ _ _ mhincr hincr hupk
  have hframe : memFind m' 1 = memFind m 1 :=
    memFind_memStore_other m m' 0 1 0 _ x hmstore (by decide)
  have hDbk : result.toNat + k < dst.val.length := by omega
  have hbD' : bD' =
      ⟨dst.val.set (result.toNat + k) x, false⟩ := by
    have h := vecSet_ok dst _ x hliveD hDbk
    rw [hset] at h
    simpa using h
  have hfreeD' : bD'.freed = false := by rw [hbD']
  have hblk : relocDstBlk bD' lenD capD =
      ⟨0, true, (BitVec.ofNat 32 lenD) ::
        (BitVec.ofNat 32 capD) :: bD'.val⟩ := by
    simp [relocDstBlk, hfreeD']
  have hfindD'' : memFind m' 0 = some (relocDstBlk bD' lenD capD) := by
    rw [hblk]; exact hfindD'
  refine ⟨m', ?_, hfindD'', hframe⟩
  exact (memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _
    hsetF).trans hasg

/-- Body error on memory: a failing copy step aborts the body
    (mirrors `stdVecRelocBody_step_err`; memory untouched). -/
theorem memStdVecRelocBody_step_err (F : Nat) (bS : Vec32)
    (lenS capS : Nat) (bD : Vec32) (lenD capD : Nat)
    (first last result : BitVec 64) (k : Nat) (n : BitVec 64)
    (dst : Vec32) (m : Mem) (π : Layout) (e : Panic)
    (herr : memEvalStmtFuel F
      (.vgrowSet "dst" (.uadd (.var "result") (.var "k"))
        (.vgrowAt "src" (.uadd (.var "first") (.var "k"))))
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        dst) m π = .error e) :
    memEvalStmtFuel F stdVecRelocBody
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        dst) m π = .error e :=
  memEvalStmtFuel_seq_err F _ _ _ _ _ _ herr

/-- Loop correctness on memory: the copy loop runs the bulk blit in
    lockstep, threading the destination stores through memory while
    the source pin survives by framing (mirrors
    `stdVecRelocWhile_correct`; the destination pin is an induction
    invariant, the source pin a framed fact). -/
theorem memStdVecRelocWhile_correct (bS : Vec32) (lenS capS : Nat)
    (bD : Vec32) (lenD capD : Nat) (first last result : BitVec 64)
    (F k : Nat) (n : BitVec 64) (dst : Vec32) (m : Mem) (π : Layout)
    (hk : k ≤ last.toNat - first.toNat)
    (hfirst : first.toNat ≤ last.toNat)
    (hn : n = last - first)
    (hliveS : bS.freed = false) (hliveD : dst.freed = false)
    (hSb : last.toNat ≤ bS.val.length)
    (hDb : result.toNat + (last.toNat - first.toNat) ≤ dst.val.length)
    (hlenS : last.toNat ≤ lenS)
    (hS64 : bS.val.length < 2 ^ 64) (hD64 : dst.val.length < 2 ^ 64)
    (hlayS : layoutLookup π "src" = some (1, 1))
    (hlayD : layoutLookup π "dst" = some (0, 0))
    (hsrcFind : memFind m 1 = some (relocSrcBlk bS lenS capS))
    (hdstFind : memFind m 0 = some (relocDstBlk dst lenD capD))
    (hF : last.toNat - first.toNat - k + 1 ≤ F) :
    ∃ m', (memEvalStmtFuel F stdVecRelocWhile
      (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result k n
        dst) m π =
      match stdVecBlitFold bS.val lenS bS.freed dst (result.toNat + k)
          (first.toNat + k) (last.toNat - first.toNat - k) with
      | Except.error e => Except.error e
      | Except.ok dst' =>
        Except.ok (((mkStdVecRelocEnv bS lenS capS bD lenD capD first
          last result (last.toNat - first.toNat) n dst', m', π)),
          .fellThrough))
      ∧ memFind m' 1 = memFind m 1 := by
  induction F generalizing k dst m with
  | zero =>
    refine ⟨m, ?_, rfl⟩
    omega
  | succ F ih =>
    have hnt : n.toNat = last.toNat - first.toNat := by
      rw [hn]; exact u64sub_toNat_exact _ _ hfirst
    have hk64 : k < 2 ^ 64 := by omega
    have hkok : (BitVec.ofNat 64 k).toNat = k := ofNat64_toNat k hk64
    have hsidx : (first + BitVec.ofNat 64 k).toNat =
        first.toNat + k := by
      rw [BitVec.toNat_add, hkok]
      exact Nat.mod_eq_of_lt (by omega)
    have hdidx : (result + BitVec.ofNat 64 k).toNat =
        result.toNat + k := by
      rw [BitVec.toNat_add, hkok]
      exact Nat.mod_eq_of_lt (by omega)
    have hs := mkStdVecRelocEnv_src bS lenS capS bD lenD capD first
      last result k n dst
    have hfirstL := mkStdVecRelocEnv_first bS lenS capS bD lenD capD
      first last result k n dst
    have hresultL := mkStdVecRelocEnv_result bS lenS capS bD lenD capD
      first last result k n dst
    have hkL := mkStdVecRelocEnv_k bS lenS capS bD lenD capD first
      last result k n dst
    have hkv : evalExpr (.var "k")
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          k n dst) = .ok (.u64 (BitVec.ofNat 64 k)) := by
      simp [evalExpr, hkL]
    have hfirstv : evalExpr (.var "first")
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          k n dst) = .ok (.u64 first) := by
      simp [evalExpr, hfirstL]
    have hresultv : evalExpr (.var "result")
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          k n dst) = .ok (.u64 result) := by
      simp [evalExpr, hresultL]
    have mhkv : memEvalExpr (.var "k")
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          k n dst) m π =
        evalExpr (.var "k")
          (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
            k n dst) :=
      memEvalExpr_var _ _ _ _
    have mhfirstv : memEvalExpr (.var "first")
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          k n dst) m π =
        evalExpr (.var "first")
          (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
            k n dst) :=
      memEvalExpr_var _ _ _ _
    have mhresultv : memEvalExpr (.var "result")
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          k n dst) m π =
        evalExpr (.var "result")
          (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
            k n dst) :=
      memEvalExpr_var _ _ _ _
    have hsidxe : evalExpr (.uadd (.var "first") (.var "k"))
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          k n dst) = .ok (.u64 (first + BitVec.ofNat 64 k)) :=
      evalExpr_uadd_u64 _ _ _ _ _ hfirstv hkv
    have hdidxe : evalExpr (.uadd (.var "result") (.var "k"))
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          k n dst) = .ok (.u64 (result + BitVec.ofNat 64 k)) :=
      evalExpr_uadd_u64 _ _ _ _ _ hresultv hkv
    have mhsidxe := memEvalExpr_uadd_agree (.var "first")
      (.var "k") _ _ _ mhfirstv mhkv
    have mhdidxe := memEvalExpr_uadd_agree (.var "result")
      (.var "k") _ _ _ mhresultv mhkv
    have mhdidxe_ok : memEvalExpr
        (.uadd (.var "result") (.var "k"))
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          k n dst) m π =
        .ok (.u64 (result + BitVec.ofNat 64 k)) := by
      rw [mhdidxe]; exact hdidxe
    by_cases hlt : k < last.toNat - first.toNat
    · have hcond : memEvalExpr (.ult (.var "k") (.var "n"))
          (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
            result k n dst) m π = .ok (.b true) := by
        have h := memStdVecRelocCond_eval bS lenS capS bD lenD capD
          first last result k n dst m π hk64
        rw [hnt] at h
        simpa [hlt] using h
      obtain ⟨t, hm⟩ : ∃ t, last.toNat - first.toNat - k = t + 1 :=
        ⟨last.toNat - first.toNat - k - 1, by omega⟩
      have hunfold := stdVecBlitFold_step bS.val lenS bS.freed dst
        (result.toNat + k) (first.toNat + k) t
      have hsoff : first.toNat + k < lenS := by omega
      cases hget : bS.val[first.toNat + k]? with
      | none =>
        have hget' : bS.val[(first + BitVec.ofNat 64 k).toNat]? =
            none := by
          rw [hsidx]; exact hget
        have hatE : evalExpr
            (.vgrowAt "src" (.uadd (.var "first") (.var "k")))
            (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
              result k n dst) = .error .OOB :=
          evalExpr_vgrowAt_oob_miss "src" _ _ bS lenS capS _ hs
            hsidxe hliveS hget'
        have hmemLoadE : memLoad m 1 1
            ((first + BitVec.ofNat 64 k).toNat + 2) =
            .error .OOB := by
          rw [hsidx]
          simp [memLoad, hsrcFind, hliveS, relocSrcBlk, hget]
        have mhatE := memEvalExpr_vgrowAt_oob_miss "src"
          (.uadd (.var "first") (.var "k")) _ _ _ bS lenS capS
          (first + BitVec.ofNat 64 k) 1 1 hlayS hs mhsidxe hsidxe
          hliveS hmemLoadE hget'
        have mhatE_ok : memEvalExpr
            (.vgrowAt "src" (.uadd (.var "first") (.var "k")))
            (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
              result k n dst) m π = .error .OOB := by
          rw [mhatE]; exact hatE
        have herr : memEvalStmtFuel F
            (.vgrowSet "dst" (.uadd (.var "result") (.var "k"))
              (.vgrowAt "src" (.uadd (.var "first") (.var "k"))))
            (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
              result k n dst) m π = .error .OOB := by
          have hd := mkStdVecRelocEnv_dst bS lenS capS bD lenD capD
            first last result k n dst
          cases F <;>
            simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
              mhdidxe_ok, mhatE_ok]
        have hbody := memStdVecRelocBody_step_err F bS lenS capS bD
          lenD capD first last result k n dst m π .OOB herr
        have hstep : memEvalStmtFuel (F + 1) stdVecRelocWhile
            (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
              result k n dst) m π = .error .OOB := by
          simp [stdVecRelocWhile, memEvalStmtFuel,
            memEvalSuccHandler, memEvalStmtWith, hcond, hbody]
        refine ⟨m, ?_, rfl⟩
        rw [hstep, hm, hunfold, hliveS]
        simp [hsoff, hget]
      | some x =>
        cases hset : vecSet dst (result.toNat + k) x with
        | error e =>
          have hget' : bS.val[(first + BitVec.ofNat 64 k).toNat]? =
              some x := by
            rw [hsidx]; exact hget
          have hltlen : (first + BitVec.ofNat 64 k).toNat < lenS := by
            rw [hsidx]; omega
          have hmemLoad : memLoad m 1 1
              ((first + BitVec.ofNat 64 k).toNat + 2) = .ok x := by
            rw [hsidx]
            simp [memLoad, hsrcFind, hliveS, relocSrcBlk, hget]
          have mhat := memEvalExpr_vgrowAt_hit "src"
            (.uadd (.var "first") (.var "k")) _ _ _ bS lenS capS
            (first + BitVec.ofNat 64 k) x 1 1 hlayS hs mhsidxe
            hsidxe hliveS hmemLoad hget' hltlen
          have hat : evalExpr
              (.vgrowAt "src" (.uadd (.var "first") (.var "k")))
              (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
                result k n dst) = .ok (.i32 x) :=
            evalExpr_vgrowAt_some "src" _ _ bS lenS capS _ _ hs
              hsidxe hliveS hget' hltlen
          have mhat_ok : memEvalExpr
              (.vgrowAt "src" (.uadd (.var "first") (.var "k")))
              (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
                result k n dst) m π = .ok (.i32 x) := by
            rw [mhat]; exact hat
          have hset' : vecSet dst (result + BitVec.ofNat 64 k).toNat
              x = .error e := by
            rw [hdidx]; exact hset
          have herr : memEvalStmtFuel F
              (.vgrowSet "dst" (.uadd (.var "result") (.var "k"))
                (.vgrowAt "src" (.uadd (.var "first") (.var "k"))))
              (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
                result k n dst) m π = .error e :=
            memEvalStmtFuel_vgrowSet_err F "dst"
              (.uadd (.var "result") (.var "k"))
              (.vgrowAt "src" (.uadd (.var "first") (.var "k")))
              _ _ _ (result + BitVec.ofNat 64 k) x 0 0 dst lenD capD
              e mhdidxe_ok mhat_ok
              (mkStdVecRelocEnv_dst bS lenS capS bD lenD capD first
                last result k n dst)
              hlayD hset'
          have hbody := memStdVecRelocBody_step_err F bS lenS capS bD
            lenD capD first last result k n dst m π e herr
          have hstep : memEvalStmtFuel (F + 1) stdVecRelocWhile
              (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
                result k n dst) m π = .error e := by
            simp [stdVecRelocWhile, memEvalStmtFuel,
              memEvalSuccHandler, memEvalStmtWith, hcond, hbody]
          refine ⟨m, ?_, rfl⟩
          rw [hstep, hm, hunfold, hliveS]
          simp [hsoff, hget, hset]
        | ok bD' =>
          have hkc : k < last.toNat - first.toNat := hlt
          have hset' : vecSet dst (result + BitVec.ofNat 64 k).toNat
              x = .ok bD' := by
            rw [hdidx]; exact hset
          have hget' : bS.val[(first + BitVec.ofNat 64 k).toNat]? =
              some x := by
            rw [hsidx]; exact hget
          have hltlen : (first + BitVec.ofNat 64 k).toNat < lenS := by
            rw [hsidx]; omega
          obtain ⟨m₁, hbodyEq, hfindD', hframe⟩ :=
            memStdVecRelocBody_step_ok F bS lenS capS bD lenD capD
              first last result k n dst x bD' m π hkc hfirst hliveS
              hliveD hSb hDb hlenS hS64 hD64 hget hset hlayS hlayD
              hsrcFind hdstFind
          have hstep : memEvalStmtFuel (F + 1) stdVecRelocWhile
              (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
                result k n dst) m π =
              memEvalStmtFuel F stdVecRelocWhile
                (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
                  result (k + 1) n bD') m₁ π := by
            simp [stdVecRelocWhile, memEvalStmtFuel,
              memEvalSuccHandler, memEvalStmtWith, hcond, hbodyEq]
          have hDbk : result.toNat + k < dst.val.length := by omega
          have hbD' : bD' =
              ⟨dst.val.set (result.toNat + k) x, false⟩ := by
            have h := vecSet_ok dst _ x hliveD hDbk
            rw [hset] at h
            simpa using h
          have hlenD' : bD'.val.length = dst.val.length := by
            simp [hbD', List.length_set]
          have hfreeD' : bD'.freed = false := by rw [hbD']
          have hd1 : result.toNat + k + 1 = result.toNat + (k + 1) := by
            omega
          have hs1 : first.toNat + k + 1 = first.toNat + (k + 1) := by
            omega
          have hm1 : t = last.toNat - first.toNat - (k + 1) := by
            omega
          have hsrcFind₁ : memFind m₁ 1 =
              some (relocSrcBlk bS lenS capS) := by
            rw [hframe]; exact hsrcFind
          obtain ⟨m₂, hihEq, hframe₂⟩ := ih (k + 1) bD' m₁
            (by omega) hfreeD'
            (by rw [hlenD']; exact hDb)
            (by rw [hlenD']; exact hD64)
            hsrcFind₁ hfindD' (by omega)
          refine ⟨m₂, ?_, hframe₂.trans hframe⟩
          rw [hstep, hm, hunfold, ite_eq_right (by simp [hliveS])]
          simp only [hsoff, hget, hset, ite_true]
          rw [hd1, hs1, hm1]
          exact hihEq
    · have hkk : k = last.toNat - first.toNat := by omega
      subst hkk
      have hk64c : last.toNat - first.toNat < 2 ^ 64 := by omega
      have hcondF : memEvalExpr (.ult (.var "k") (.var "n"))
          (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
            result (last.toNat - first.toNat) n dst) m π =
          .ok (.b false) := by
        have h := memStdVecRelocCond_eval bS lenS capS bD lenD capD
          first last result (last.toNat - first.toNat) n dst m π
          hk64c
        rw [hnt] at h
        have hf : decide (last.toNat - first.toNat <
            last.toNat - first.toNat) = false := by simp
        rwa [hf] at h
      have hzero : stdVecBlitFold bS.val lenS bS.freed dst
          (result.toNat + (last.toNat - first.toNat))
          (first.toNat + (last.toNat - first.toNat))
          (last.toNat - first.toNat - (last.toNat - first.toNat)) =
          .ok dst := by
        rw [Nat.sub_self]; rfl
      have hLHS : memEvalStmtFuel (F + 1) stdVecRelocWhile
          (mkStdVecRelocEnv bS lenS capS bD lenD capD first last
            result (last.toNat - first.toNat) n dst) m π =
          .ok (((mkStdVecRelocEnv bS lenS capS bD lenD capD first last
            result (last.toNat - first.toNat) n dst, m, π)),
            .fellThrough) := by
        simp [stdVecRelocWhile, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcondF]
      have hRHS : (match stdVecBlitFold bS.val lenS bS.freed dst
          (result.toNat + (last.toNat - first.toNat))
          (first.toNat + (last.toNat - first.toNat))
          (last.toNat - first.toNat - (last.toNat - first.toNat)) with
        | Except.error e => Except.error e
        | Except.ok dst' =>
          Except.ok (((mkStdVecRelocEnv bS lenS capS bD lenD capD first
            last result (last.toNat - first.toNat) n dst', m, π)),
            Outcome.fellThrough)) =
          .ok (((mkStdVecRelocEnv bS lenS capS bD lenD capD first last
            result (last.toNat - first.toNat) n dst, m, π)),
            Outcome.fellThrough) := by
        rw [hzero]
      refine ⟨m, ?_, rfl⟩
      exact hLHS.trans hRHS.symm

/-- `memEval` for relocate: bind the two triples, run the counter
    setup, then the loop (mirrors `evalFuncFuel_stdVecReloc`; memory
    is discarded at the function boundary, so only the value equation
    survives). -/
theorem memEvalFuncFuel_stdVecReloc (F : Nat) (bS : Vec32)
    (lenS capS : Nat) (bD : Vec32) (lenD capD : Nat)
    (first last result : BitVec 64)
    (hfirst : first.toNat ≤ last.toNat)
    (hliveS : bS.freed = false) (hliveD : bD.freed = false)
    (hSb : last.toNat ≤ bS.val.length)
    (hDb : result.toNat + (last.toNat - first.toNat) ≤ bD.val.length)
    (hlenS : last.toNat ≤ lenS)
    (hS64 : bS.val.length < 2 ^ 64) (hD64 : bD.val.length < 2 ^ 64)
    (hF : last.toNat - first.toNat + 1 ≤ F) :
    memEvalFuncFuel F stdVecRelocFunc
      [.stdVecOwned bS lenS capS, .stdVecOwned bD lenD capD,
        .u64 first, .u64 last, .u64 result] =
      stdVecRelocFwd bS lenS capS bD lenD capD first last result := by
  have hb : bindMemArgs stdVecRelocFunc.args
      [.stdVecOwned bS lenS capS, .stdVecOwned bD lenD capD,
        .u64 first, .u64 last, .u64 result] emptyMem =
      some ([("src", .stdVecOwned bS lenS capS),
        ("dst", .stdVecOwned bD lenD capD),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)],
        relocMem bS lenS capS bD lenD capD,
        [("src", 1, 1), ("dst", 0, 0)]) := by
    show bindMemArgs
      [{ name := "src", ty := .vecBlock, role := .owned },
       { name := "dst", ty := .vecBlock, role := .owned },
       { name := "first", ty := .u 64, role := .owned },
       { name := "last", ty := .u 64, role := .owned },
       { name := "result", ty := .u 64, role := .owned }]
      [.stdVecOwned bS lenS capS, .stdVecOwned bD lenD capD,
        .u64 first, .u64 last, .u64 result] emptyMem = _
    exact bindMemArgs_stdVecReloc bS lenS capS bD lenD capD
      first last result
  have hbody : stdVecRelocFunc.body =
      .seq (.let_ "k" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.seq (.let_ "n" (.u 64) (.usub (.var "last") (.var "first")))
      (.seq stdVecRelocWhile
        (.return_ (.var "dst")))) := rfl
  have hlitk : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("src", .stdVecOwned bS lenS capS),
        ("dst", .stdVecOwned bD lenD capD),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  have hmlitk : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("src", .stdVecOwned bS lenS capS),
        ("dst", .stdVecOwned bD lenD capD),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)]
      (relocMem bS lenS capS bD lenD capD)
      [("src", 1, 1), ("dst", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("src", .stdVecOwned bS lenS capS),
          ("dst", .stdVecOwned bD lenD capD),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)] :=
    memEvalExpr_lit _ _ _ _
  have me1 : memEvalStmtFuel F
      (.let_ "k" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      [("src", .stdVecOwned bS lenS capS),
        ("dst", .stdVecOwned bD lenD capD),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)]
      (relocMem bS lenS capS bD lenD capD)
      [("src", 1, 1), ("dst", 0, 0)] =
      .ok (((("k", .u64 (BitVec.ofNat 64 0)) ::
        [("src", .stdVecOwned bS lenS capS),
          ("dst", .stdVecOwned bD lenD capD),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)]),
        relocMem bS lenS capS bD lenD capD,
        [("src", 1, 1), ("dst", 0, 0)]),
        .fellThrough) :=
    memEvalStmtFuel_let_pure F "k" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0))) _ _ _ _
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) hmlitk hlitk
  have hlastK : evalExpr (.var "last")
      [("k", .u64 (BitVec.ofNat 64 0)),
        ("src", .stdVecOwned bS lenS capS),
        ("dst", .stdVecOwned bD lenD capD),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] = .ok (.u64 last) := by
    simp [evalExpr, envLookup,
      show ("last" : String) ≠ "k" by decide,
      show ("last" : String) ≠ "src" by decide,
      show ("last" : String) ≠ "dst" by decide,
      show ("last" : String) ≠ "first" by decide]
  have hfirstK : evalExpr (.var "first")
      [("k", .u64 (BitVec.ofNat 64 0)),
        ("src", .stdVecOwned bS lenS capS),
        ("dst", .stdVecOwned bD lenD capD),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] = .ok (.u64 first) := by
    simp [evalExpr, envLookup,
      show ("first" : String) ≠ "k" by decide,
      show ("first" : String) ≠ "src" by decide,
      show ("first" : String) ≠ "dst" by decide]
  have hnEval : evalExpr (.usub (.var "last") (.var "first"))
      [("k", .u64 (BitVec.ofNat 64 0)),
        ("src", .stdVecOwned bS lenS capS),
        ("dst", .stdVecOwned bD lenD capD),
        ("first", .u64 first), ("last", .u64 last),
        ("result", .u64 result)] =
      .ok (.u64 (last - first)) :=
    evalExpr_usub_u64u64 _ _ _ _ _ hlastK hfirstK
  have mhlastK : memEvalExpr (.var "last")
      (("k", .u64 (BitVec.ofNat 64 0)) ::
        [("src", .stdVecOwned bS lenS capS),
          ("dst", .stdVecOwned bD lenD capD),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)])
      (relocMem bS lenS capS bD lenD capD)
      [("src", 1, 1), ("dst", 0, 0)] =
      evalExpr (.var "last")
        (("k", .u64 (BitVec.ofNat 64 0)) ::
          [("src", .stdVecOwned bS lenS capS),
            ("dst", .stdVecOwned bD lenD capD),
            ("first", .u64 first), ("last", .u64 last),
            ("result", .u64 result)]) :=
    memEvalExpr_var _ _ _ _
  have mhfirstK : memEvalExpr (.var "first")
      (("k", .u64 (BitVec.ofNat 64 0)) ::
        [("src", .stdVecOwned bS lenS capS),
          ("dst", .stdVecOwned bD lenD capD),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)])
      (relocMem bS lenS capS bD lenD capD)
      [("src", 1, 1), ("dst", 0, 0)] =
      evalExpr (.var "first")
        (("k", .u64 (BitVec.ofNat 64 0)) ::
          [("src", .stdVecOwned bS lenS capS),
            ("dst", .stdVecOwned bD lenD capD),
            ("first", .u64 first), ("last", .u64 last),
            ("result", .u64 result)]) :=
    memEvalExpr_var _ _ _ _
  have mhnEval := memEvalExpr_usub_agree (.var "last") (.var "first")
    _ _ _ mhlastK mhfirstK
  have me2 : memEvalStmtFuel F
      (.let_ "n" (.u 64) (.usub (.var "last") (.var "first")))
      (("k", .u64 (BitVec.ofNat 64 0)) ::
        [("src", .stdVecOwned bS lenS capS),
          ("dst", .stdVecOwned bD lenD capD),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)])
      (relocMem bS lenS capS bD lenD capD)
      [("src", 1, 1), ("dst", 0, 0)] =
      .ok (((mkStdVecRelocEnv bS lenS capS bD lenD capD first last
        result 0 (last - first) bD,
        relocMem bS lenS capS bD lenD capD,
        [("src", 1, 1), ("dst", 0, 0)])),
        .fellThrough) :=
    memEvalStmtFuel_let_pure F "n" (.u 64)
      (.usub (.var "last") (.var "first")) _ _ _ _
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) mhnEval hnEval
  have hF0 : last.toNat - first.toNat - 0 + 1 ≤ F := hF
  have hlayS₀ : layoutLookup [("src", 1, 1), ("dst", 0, 0)] "src" =
      some (1, 1) := by
    simp [layoutLookup]
  have hlayD₀ : layoutLookup [("src", 1, 1), ("dst", 0, 0)] "dst" =
      some (0, 0) := by
    simp [layoutLookup]
  have hsrcFind₀ : memFind (relocMem bS lenS capS bD lenD capD) 1 =
      some (relocSrcBlk bS lenS capS) := by
    simp [relocMem, relocSrcBlk, memFind]
  have hdstFind₀ : memFind (relocMem bS lenS capS bD lenD capD) 0 =
      some (relocDstBlk bD lenD capD) := by
    simp [relocMem, relocDstBlk, memFind]
  obtain ⟨mL, hloop0, -⟩ := memStdVecRelocWhile_correct bS lenS capS
    bD lenD capD first last result F 0 (last - first) bD
    (relocMem bS lenS capS bD lenD capD) [("src", 1, 1), ("dst", 0, 0)]
    (Nat.zero_le _) hfirst rfl hliveS hliveD hSb hDb hlenS hS64 hD64
    hlayS₀ hlayD₀ hsrcFind₀ hdstFind₀ hF0
  simp only [Nat.add_zero, Nat.sub_zero] at hloop0
  cases hblit : stdVecBlitFold bS.val lenS bS.freed bD result.toNat
      first.toNat (last.toNat - first.toNat) with
  | error e =>
    have hloopE : memEvalStmtFuel F stdVecRelocWhile
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          0 (last - first) bD)
        (relocMem bS lenS capS bD lenD capD)
        [("src", 1, 1), ("dst", 0, 0)] = .error e := by
      rw [hblit] at hloop0
      exact hloop0
    have hfwd : stdVecRelocFwd bS lenS capS bD lenD capD first last
        result = .error e := by
      simp [stdVecRelocFwd, hblit]
    have hstmt : memEvalStmtFuel F stdVecRelocFunc.body
        [("src", .stdVecOwned bS lenS capS),
          ("dst", .stdVecOwned bD lenD capD),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)]
        (relocMem bS lenS capS bD lenD capD)
        [("src", 1, 1), ("dst", 0, 0)] = .error e := by
      rw [hbody]
      exact (memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _
        me1).trans
        ((memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _
          me2).trans
          (memEvalStmtFuel_seq_err F _ _ _ _ _ _ hloopE))
    simp [memEvalFuncFuel, hb, hstmt, hfwd]
  | ok bD' =>
    have hloopO : memEvalStmtFuel F stdVecRelocWhile
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          0 (last - first) bD)
        (relocMem bS lenS capS bD lenD capD)
        [("src", 1, 1), ("dst", 0, 0)] =
        .ok (((mkStdVecRelocEnv bS lenS capS bD lenD capD first last
          result (last.toNat - first.toNat) (last - first) bD',
          mL, [("src", 1, 1), ("dst", 0, 0)])),
          .fellThrough) := by
      rw [hblit] at hloop0
      exact hloop0
    have hret : envLookup
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          (last.toNat - first.toNat) (last - first) bD') "dst" =
        some (.stdVecOwned bD' lenD capD) :=
      mkStdVecRelocEnv_dst bS lenS capS bD lenD capD first last result
        (last.toNat - first.toNat) (last - first) bD'
    have hvar : evalExpr (.var "dst")
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          (last.toNat - first.toNat) (last - first) bD') =
        .ok (.stdVecOwned bD' lenD capD) := by
      simp [evalExpr, hret]
    have mhvar : memEvalExpr (.var "dst")
        (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
          (last.toNat - first.toNat) (last - first) bD') mL
        [("src", 1, 1), ("dst", 0, 0)] =
        evalExpr (.var "dst")
          (mkStdVecRelocEnv bS lenS capS bD lenD capD first last result
            (last.toNat - first.toNat) (last - first) bD') :=
      memEvalExpr_var _ _ _ _
    have hfwd : stdVecRelocFwd bS lenS capS bD lenD capD first last
        result = .ok (.stdVecOwned bD' lenD capD) := by
      simp [stdVecRelocFwd, hblit]
    have hstmt : memEvalStmtFuel F stdVecRelocFunc.body
        [("src", .stdVecOwned bS lenS capS),
          ("dst", .stdVecOwned bD lenD capD),
          ("first", .u64 first), ("last", .u64 last),
          ("result", .u64 result)]
        (relocMem bS lenS capS bD lenD capD)
        [("src", 1, 1), ("dst", 0, 0)] =
        .ok (((mkStdVecRelocEnv bS lenS capS bD lenD capD first last
          result (last.toNat - first.toNat) (last - first) bD', mL,
          [("src", 1, 1), ("dst", 0, 0)])),
          .returned (.stdVecOwned bD' lenD capD)) := by
      rw [hbody]
      exact (memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _
        me1).trans
        ((memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _
          me2).trans
          ((memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _
            hloopO).trans
            (memEvalStmtFuel_return F _ _ _ _ _ mhvar hvar)))
    simp [memEvalFuncFuel, hb, hstmt, hfwd]

/-- Transfer for relocate: memory execution agrees with value
    execution (both sides reduce to the blit forward). -/
theorem memTransfer_stdVecReloc (F : Nat) (bS : Vec32)
    (lenS capS : Nat) (bD : Vec32) (lenD capD : Nat)
    (first last result : BitVec 64)
    (hfirst : first.toNat ≤ last.toNat)
    (hliveS : bS.freed = false) (hliveD : bD.freed = false)
    (hSb : last.toNat ≤ bS.val.length)
    (hDb : result.toNat + (last.toNat - first.toNat) ≤ bD.val.length)
    (hlenS : last.toNat ≤ lenS)
    (hS64 : bS.val.length < 2 ^ 64) (hD64 : bD.val.length < 2 ^ 64)
    (hF : last.toNat - first.toNat + 1 ≤ F)
    (_h : oracleNoalias stdVecRelocFunc
      [.stdVecOwned bS lenS capS, .stdVecOwned bD lenD capD,
        .u64 first, .u64 last, .u64 result]) :
    memEvalFuncFuel F stdVecRelocFunc
      [.stdVecOwned bS lenS capS, .stdVecOwned bD lenD capD,
        .u64 first, .u64 last, .u64 result] =
      evalFuncFuel F stdVecRelocFunc
        [.stdVecOwned bS lenS capS, .stdVecOwned bD lenD capD,
          .u64 first, .u64 last, .u64 result] := by
  rw [memEvalFuncFuel_stdVecReloc F bS lenS capS bD lenD capD first
    last result hfirst hliveS hliveD hSb hDb hlenS hS64 hD64 hF,
    evalFuncFuel_stdVecReloc F bS lenS capS bD lenD capD first last
      result hfirst hliveS hliveD hSb hDb hlenS hS64 hD64 hF]

