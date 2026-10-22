/-
Circe.Transfer.VecMergeSort — M1c transfer for the `vec_merge_sort`
segment spine.

Mem-level mirrors of the eval-level equations in
`Circe.Emit.VecMergeSort`: the copy-back body reads `tmp[t]` through
length-word-skipping loads and stores into `a[t]` (`memRevVecSet`),
the copy/drain/seg/outer loops thread by-find pins for both blocks
(`memFind_memStore_other` keeps the idle pin), and the seg-body call
step reuses the M1b general-caller-memory entry
`memEvalProgFuncOn_mergeRuns` as its `hcall` premise through the
sharing-call frame (`callShare`).
-/
import Circe.Transfer.VecReverse
import Circe.Transfer.VecMergeRuns
import Circe.Emit.VecMergeSort

open VecMergeSort

/-! ## Copy-back body mirror -/

/-- Copy-back body, hit, on memory: `tmp` guard holds, store into `a`,
    advance `t` (the `SortInv` reassembles by hit/miss chains). -/
theorem memSortCopyBody_hit (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (n w lo mid hi t : BitVec 64)
    (x v : BitVec 32)
    (aa ab : Addr) (ta tb : Nat) (nB : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_tmp : layoutLookup π "tmp" = some (ab, tb))
    (hmem_b : memFind m ab = some ⟨tb, true, nB :: lt⟩)
    (hnB : nB = BitVec.ofNat 32 lt.length)
    (hinv : SortInv ρ la lt n w lo mid hi t)
    (hlent : lt.length < 2 ^ 64)
    (hgetT : lt[t.toNat]? = some x)
    (hgetA : la[t.toNat]? = some v)
    (hltT : t.toNat < lt.length)
    (m' : Mem)
    (hstore : memStore m aa ta (t.toNat + 1) x = .ok m')
    (ρ' : Env)
    (hu : envUpdate ρ "a" (.stdVecVal (la.set t.toNat x)) = some ρ')
    (ρ'' : Env)
    (huT : envUpdate ρ' "t" (.u64 (t + 1)) = some ρ'') :
    memEvalProgStmt prog F sortCopyBody ρ m π =
      .ok ((ρ'', m', π), .fellThrough) ∧
      SortInv ρ'' (la.set t.toNat x) lt n w lo mid hi (t + 1) := by
  obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
  have hvarT : memEvalExpr (.var "t") ρ m π = evalExpr (.var "t") ρ :=
    memEvalExpr_var _ _ _ _
  have hevT : evalExpr (.var "t") ρ = .ok (.u64 t) :=
    evalExpr_var_hit _ _ _ htt
  have hmemLen : memLoad m ab tb 0 =
      .ok (BitVec.ofNat 32 lt.length) := by
    rw [← hnB]
    exact memLoad_cellsAt m ab tb 0 (nB :: lt) nB hmem_b rfl
  have hlenAg : memEvalExpr (.stdVecLen "tmp") ρ m π =
      evalExpr (.stdVecLen "tmp") ρ :=
    memEvalExpr_stdVecLen_hit "tmp" ρ m π lt ab tb
      hlay_tmp htmp hmemLen
  have hgTE : evalExpr (.ult (.var "t") (.stdVecLen "tmp")) ρ =
      .ok (.b true) := by
    have h := sortCopyGuard_eval ρ la lt n w lo mid hi t
      ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ hlent
    rwa [decide_eq_true hltT] at h
  have hgT : memEvalExpr (.ult (.var "t") (.stdVecLen "tmp")) ρ m π =
      .ok (.b true) :=
    (memEvalExpr_ult_agree _ _ _ _ _ hvarT hlenAg).trans hgTE
  have hloadT : memLoad m ab tb (t.toNat + 1) = .ok x :=
    memLoad_cellsAt m ab tb (t.toNat + 1) (nB :: lt) x hmem_b
      (by rw [List.getElem?_cons_succ]; exact hgetT)
  have hagT : memEvalExpr (.stdVecAt "tmp" (.var "t")) ρ m π =
      evalExpr (.stdVecAt "tmp" (.var "t")) ρ :=
    memEvalExpr_stdVecAt_hit "tmp" (.var "t") ρ m π lt t x ab tb
      hlay_tmp htmp hvarT hevT hloadT hgetT
  have hrT : evalExpr (.stdVecAt "tmp" (.var "t")) ρ =
      .ok (.i32 x) :=
    sortCopyRead_hit ρ la lt n w lo mid hi t x
      ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ hgetT
  have hread : memEvalExpr (.stdVecAt "tmp" (.var "t")) ρ m π =
      .ok (.i32 x) :=
    hagT.trans hrT
  have hset := memRevVecSet prog F "a" (.var "t")
    (.stdVecAt "tmp" (.var "t")) ρ m π t x aa ta la v m' ρ'
    (hvarT.trans hevT) hread ha hlay_a hgetA hstore hu
  have hlookT' : envLookup ρ' "t" = some (.u64 t) := by
    have h := envLookup_update_miss ρ "t" "a"
      (.stdVecVal (la.set t.toNat x)) ρ' (by decide) hu
    rw [h, htt]
  have hevT' : evalExpr (.var "t") ρ' = .ok (.u64 t) :=
    evalExpr_var_hit _ _ _ hlookT'
  have hev1 : evalExpr (.lit (.u64 1)) ρ' = .ok (.u64 1) := by
    simp [evalExpr, litVal]
  have hevUT : evalExpr (.uadd (.var "t") (.lit (.u64 1))) ρ' =
      .ok (.u64 (t + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hevT' hev1
  have hmemT : memEvalExpr (.uadd (.var "t") (.lit (.u64 1))) ρ' m' π =
      .ok (.u64 (t + 1)) :=
    (memEvalExpr_uadd_agree _ _ _ _ _
      (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)).trans hevUT
  have hstepT := memRevAssign prog F "t" _ ρ' m' π _ ρ''
    hmemT hevUT huT
  have hthen : memEvalProgStmt prog F
      (.seq (.if_ (.ult (.var "t") (.stdVecLen "tmp"))
        (.vecSet "a" (.var "t") (.stdVecAt "tmp" (.var "t"))) .fail)
        (.assign "t" (.uadd (.var "t") (.lit (.u64 1))))) ρ m π =
      .ok ((ρ'', m', π), .fellThrough) :=
    memEvalProgStmt_seq prog F _ _ ρ m π ρ' m' π
      ρ'' m' π .fellThrough
      ((memEvalProgStmt_if_true prog F _ _ _ _ _ _ hgT).trans hset)
      hstepT
  have hinv' : SortInv ρ'' (la.set t.toNat x) lt n w lo mid hi
      (t + 1) := by
    have ha'' : envLookup ρ'' "a" =
        some (.stdVecVal (la.set t.toNat x)) := by
      have h := envLookup_update_miss ρ' "a" "t" (.u64 (t + 1)) ρ''
        (by decide) huT
      rw [h]
      exact envLookup_update_hit ρ "a" _ ρ' hu
    have htmp'' : envLookup ρ'' "tmp" = some (.stdVecVal lt) := by
      have h1 := envLookup_update_miss ρ' "tmp" "t" (.u64 (t + 1))
        ρ'' (by decide) huT
      have h2 := envLookup_update_miss ρ "tmp" "a"
        (.stdVecVal (la.set t.toNat x)) ρ' (by decide) hu
      rw [h1, h2, htmp]
    have hn'' : envLookup ρ'' "n" = some (.u64 n) := by
      have h1 := envLookup_update_miss ρ' "n" "t" (.u64 (t + 1))
        ρ'' (by decide) huT
      have h2 := envLookup_update_miss ρ "n" "a"
        (.stdVecVal (la.set t.toNat x)) ρ' (by decide) hu
      rw [h1, h2, hn]
    have hw'' : envLookup ρ'' "width" = some (.u64 w) := by
      have h1 := envLookup_update_miss ρ' "width" "t" (.u64 (t + 1))
        ρ'' (by decide) huT
      have h2 := envLookup_update_miss ρ "width" "a"
        (.stdVecVal (la.set t.toNat x)) ρ' (by decide) hu
      rw [h1, h2, hw]
    have hlo'' : envLookup ρ'' "lo" = some (.u64 lo) := by
      have h1 := envLookup_update_miss ρ' "lo" "t" (.u64 (t + 1))
        ρ'' (by decide) huT
      have h2 := envLookup_update_miss ρ "lo" "a"
        (.stdVecVal (la.set t.toNat x)) ρ' (by decide) hu
      rw [h1, h2, hlo]
    have hmid'' : envLookup ρ'' "mid" = some (.u64 mid) := by
      have h1 := envLookup_update_miss ρ' "mid" "t" (.u64 (t + 1))
        ρ'' (by decide) huT
      have h2 := envLookup_update_miss ρ "mid" "a"
        (.stdVecVal (la.set t.toNat x)) ρ' (by decide) hu
      rw [h1, h2, hmid]
    have hhi'' : envLookup ρ'' "hi" = some (.u64 hi) := by
      have h1 := envLookup_update_miss ρ' "hi" "t" (.u64 (t + 1))
        ρ'' (by decide) huT
      have h2 := envLookup_update_miss ρ "hi" "a"
        (.stdVecVal (la.set t.toNat x)) ρ' (by decide) hu
      rw [h1, h2, hhi]
    have htt'' : envLookup ρ'' "t" = some (.u64 (t + 1)) :=
      envLookup_update_hit ρ' "t" _ ρ'' huT
    exact ⟨ha'', htmp'', hn'', hw'', hlo'', hmid'', hhi'', htt''⟩
  exact ⟨hthen, hinv'⟩

/-! ## Copy-back loop inductions -/

/-- Copy-back ok soundness on memory: the loop copies `lt[lo..hi]`
    into `a` and exits with the forward-model state (fuel induction
    mirroring `sortCopy_ok`; the `a`-block shadows forward,
    `memFind_memStore_other` keeps the `tmp` pin). -/
theorem memSortCopy_ok (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (n w lo mid hi t : BitVec 64)
    (la' : List (BitVec 32)) (t' : Nat)
    (aa ab : Addr) (ta tb : Nat) (nA nB : BitVec 32)
    (haa : aa ≠ ab)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_tmp : layoutLookup π "tmp" = some (ab, tb))
    (hmem_a : memFind m aa = some ⟨ta, true, nA :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nB :: lt⟩)
    (hnB : nB = BitVec.ofNat 32 lt.length)
    (hinv : SortInv ρ la lt n w lo mid hi t)
    (hlent : lt.length < 2 ^ 64) (hlena : la.length < 2 ^ 64)
    (hhi_la : hi.toNat ≤ la.length) (hhi_lt : hi.toNat ≤ lt.length)
    (ht_le : t.toNat ≤ hi.toNat)
    (hF : (hi.toNat - t.toNat) + 1 ≤ F)
    (hfwd : sortCopyFwd lt la (hi.toNat - t.toNat) t.toNat hi.toNat =
      .ok (la', t')) :
    ∃ ρ' m', memEvalProgStmt prog F sortCopyBack ρ m π =
        .ok ((ρ', m', π), .fellThrough) ∧
      SortInv ρ' la' lt n w lo mid hi (BitVec.ofNat 64 t') ∧
      memFind m' aa = some ⟨ta, true, nA :: la'⟩ ∧
      memFind m' ab = some ⟨tb, true, nB :: lt⟩ := by
  induction F generalizing ρ m π la lt n w lo mid hi t la' t' with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hT : t.toNat < hi.toNat
    · have hcond : memEvalExpr (.ult (.var "t") (.var "hi")) ρ m π =
          .ok (.b true) := by
        have hvarT : memEvalExpr (.var "t") ρ m π =
            evalExpr (.var "t") ρ := memEvalExpr_var _ _ _ _
        have hvarH : memEvalExpr (.var "hi") ρ m π =
            evalExpr (.var "hi") ρ := memEvalExpr_var _ _ _ _
        have hE : evalExpr (.ult (.var "t") (.var "hi")) ρ =
            .ok (.b true) := by
          obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
          have h := sortCopyGuardT_eval ρ la lt n w lo mid hi t
            ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩
          rwa [decide_eq_true hT] at h
        exact (memEvalExpr_ult_agree _ _ _ _ _ hvarT hvarH).trans hE
      have hM : (hi.toNat - t.toNat) =
          ((hi.toNat - t.toNat) - 1) + 1 := by omega
      rw [hM] at hfwd
      have hgetT : lt[t.toNat]? = some lt[t.toNat] :=
        List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hT hhi_lt)
      have hgetA : la[t.toNat]? = some la[t.toNat] :=
        List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hT hhi_la)
      have hfwdT : sortCopyFwd lt (la.set t.toNat lt[t.toNat])
          ((hi.toNat - t.toNat) - 1)
          (t.toNat + 1) hi.toNat = .ok (la', t') := by
        have h := hfwd
        simp only [sortCopyFwd, dite_eq_left hT, hgetT, hgetA] at h
        exact h
      obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
      obtain ⟨ρ', hwr⟩ := envUpdate_some_of_lookup ρ "a"
        (.stdVecVal la) (.stdVecVal (la.set t.toNat lt[t.toNat])) ha
      have htt' : envLookup ρ' "t" = some (.u64 t) := by
        rw [envLookup_update_miss _ _ _ _ _
          (show ("t" : String) ≠ "a" by decide) hwr]
        exact htt
      obtain ⟨ρ'', hu⟩ := envUpdate_some_of_lookup ρ' "t"
        (.u64 t) (.u64 (t + 1)) htt'
      have hlt1 : t.toNat + 1 < (nA :: la).length := by
        have hltA : t.toNat < la.length :=
          list_lt_of_getElem?_some la t.toNat la[t.toNat] hgetA
        simp only [List.length_cons]
        omega
      obtain ⟨m₁, hstore⟩ : ∃ m₁, memStore m aa ta
          (t.toNat + 1) lt[t.toNat] = .ok m₁ :=
        ⟨_, memStore_cellsAt m aa ta (t.toNat + 1) (nA :: la)
          lt[t.toNat] hmem_a hlt1⟩
      have hstep := memSortCopyBody_hit prog F ρ m π la lt
        n w lo mid hi t lt[t.toNat] la[t.toNat]
        aa ab ta tb nB hlay_a hlay_tmp hmem_b hnB
        ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ hlent
        hgetT hgetA (Nat.lt_of_lt_of_le hT hhi_lt) _ hstore _ hwr _ hu
      have hloop : memEvalProgStmt prog (F + 1) sortCopyBack
          ρ m π = memEvalProgStmt prog F sortCopyBack ρ'' m₁ π := by
        cir_unfold_prog (sortCopyBack, prog, F, hcond, hstep.1)
      have h1t : (t + 1).toNat = t.toNat + 1 :=
        bv64_succ_toNat t _ hT (by omega)
      have hlena' : (la.set t.toNat lt[t.toNat]).length < 2 ^ 64 := by
        rw [List.length_set]; exact hlena
      have hhi_la' : hi.toNat ≤
          (la.set t.toNat lt[t.toNat]).length := by
        rw [List.length_set]; exact hhi_la
      have ht_le' : (t + 1).toNat ≤ hi.toNat := by omega
      have hF' : (hi.toNat - (t + 1).toNat) + 1 ≤ F := by omega
      have hM' : (hi.toNat - t.toNat) - 1 =
          (hi.toNat - (t + 1).toNat) := by omega
      have hfwd' : sortCopyFwd lt (la.set t.toNat lt[t.toNat])
          (hi.toNat - (t + 1).toNat) ((t + 1).toNat) hi.toNat =
          .ok (la', t') := by
        rw [← h1t, hM'] at hfwdT
        exact hfwdT
      have hmem_a₁ : memFind m₁ aa =
          some ⟨ta, true, nA :: la.set t.toNat lt[t.toNat]⟩ := by
        have hcells := memFind_cellsAt_store m aa ta (t.toNat + 1)
          (nA :: la) lt[t.toNat] m₁ hmem_a hlt1 hstore
        have hsetEq : (nA :: la).set (t.toNat + 1) lt[t.toNat] =
            nA :: la.set t.toNat lt[t.toNat] :=
          List.set_cons_succ
        rw [hsetEq] at hcells
        exact hcells
      have hmem_b₁ : memFind m₁ ab = some ⟨tb, true, nB :: lt⟩ := by
        have h := memFind_memStore_other m m₁ aa ab ta
          (t.toNat + 1) lt[t.toNat] hstore (Ne.symm haa)
        rw [h]
        exact hmem_b
      rw [hloop]
      exact ih ρ'' m₁ π (la.set t.toNat lt[t.toNat]) lt n w lo mid
        hi (t + 1) la' t' hlay_a hlay_tmp hmem_a₁ hmem_b₁ hnB
        hstep.2 hlent hlena' hhi_la' hhi_lt ht_le' hF' hfwd'
    · have hcond : memEvalExpr (.ult (.var "t") (.var "hi")) ρ m π =
          .ok (.b false) := by
        have hvarT : memEvalExpr (.var "t") ρ m π =
            evalExpr (.var "t") ρ := memEvalExpr_var _ _ _ _
        have hvarH : memEvalExpr (.var "hi") ρ m π =
            evalExpr (.var "hi") ρ := memEvalExpr_var _ _ _ _
        have hE : evalExpr (.ult (.var "t") (.var "hi")) ρ =
            .ok (.b false) := by
          obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
          have h := sortCopyGuardT_eval ρ la lt n w lo mid hi t
            ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩
          rwa [decide_eq_false hT] at h
        exact (memEvalExpr_ult_agree _ _ _ _ _ hvarT hvarH).trans hE
      have hfwd0 : sortCopyFwd lt la (hi.toNat - t.toNat) t.toNat
          hi.toNat = .ok (la, t.toNat) := by
        match hm : (hi.toNat - t.toNat) with
        | 0 => simp only [sortCopyFwd]
        | _ + 1 => simp only [sortCopyFwd, dite_eq_right hT]
      rw [hfwd0] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl⟩ := hfwd
      have hexit : memEvalProgStmt prog (F + 1) sortCopyBack
          ρ m π = .ok ((ρ, m, π), .fellThrough) := by
        simp only [sortCopyBack,
          memEvalProgStmt_while_false prog _ _ _ _ _ _ hcond]
      refine ⟨ρ, m, hexit, ?_, ?_, ?_⟩
      · rwa [bv64_ofNat_toNat t]
      · exact hmem_a
      · exact hmem_b

/-- Copy-back err soundness on memory: a model abort replays as the
    same abort (fuel induction mirroring `sortCopy_err`). -/
theorem memSortCopy_err (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (n w lo mid hi t : BitVec 64)
    (e : Panic)
    (aa ab : Addr) (ta tb : Nat) (nA nB : BitVec 32)
    (haa : aa ≠ ab)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_tmp : layoutLookup π "tmp" = some (ab, tb))
    (hmem_a : memFind m aa = some ⟨ta, true, nA :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nB :: lt⟩)
    (hnB : nB = BitVec.ofNat 32 lt.length)
    (hinv : SortInv ρ la lt n w lo mid hi t)
    (hlent : lt.length < 2 ^ 64) (hlena : la.length < 2 ^ 64)
    (hhi_la : hi.toNat ≤ la.length) (hhi_lt : hi.toNat ≤ lt.length)
    (ht_le : t.toNat ≤ hi.toNat)
    (hF : (hi.toNat - t.toNat) + 1 ≤ F)
    (hfwd : sortCopyFwd lt la (hi.toNat - t.toNat) t.toNat hi.toNat =
      .error e) :
    memEvalProgStmt prog F sortCopyBack ρ m π = .error e := by
  induction F generalizing ρ m π la lt n w lo mid hi t e with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hT : t.toNat < hi.toNat
    · have hcond : memEvalExpr (.ult (.var "t") (.var "hi")) ρ m π =
          .ok (.b true) := by
        have hvarT : memEvalExpr (.var "t") ρ m π =
            evalExpr (.var "t") ρ := memEvalExpr_var _ _ _ _
        have hvarH : memEvalExpr (.var "hi") ρ m π =
            evalExpr (.var "hi") ρ := memEvalExpr_var _ _ _ _
        have hE : evalExpr (.ult (.var "t") (.var "hi")) ρ =
            .ok (.b true) := by
          obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
          have h := sortCopyGuardT_eval ρ la lt n w lo mid hi t
            ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩
          rwa [decide_eq_true hT] at h
        exact (memEvalExpr_ult_agree _ _ _ _ _ hvarT hvarH).trans hE
      have hM : (hi.toNat - t.toNat) =
          ((hi.toNat - t.toNat) - 1) + 1 := by omega
      rw [hM] at hfwd
      have hgetT : lt[t.toNat]? = some lt[t.toNat] :=
        List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hT hhi_lt)
      have hgetA : la[t.toNat]? = some la[t.toNat] :=
        List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hT hhi_la)
      have hfwdT : sortCopyFwd lt (la.set t.toNat lt[t.toNat])
          ((hi.toNat - t.toNat) - 1)
          (t.toNat + 1) hi.toNat = .error e := by
        have h := hfwd
        simp only [sortCopyFwd, dite_eq_left hT, hgetT, hgetA] at h
        exact h
      obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
      obtain ⟨ρ', hwr⟩ := envUpdate_some_of_lookup ρ "a"
        (.stdVecVal la) (.stdVecVal (la.set t.toNat lt[t.toNat])) ha
      have htt' : envLookup ρ' "t" = some (.u64 t) := by
        rw [envLookup_update_miss _ _ _ _ _
          (show ("t" : String) ≠ "a" by decide) hwr]
        exact htt
      obtain ⟨ρ'', hu⟩ := envUpdate_some_of_lookup ρ' "t"
        (.u64 t) (.u64 (t + 1)) htt'
      have hlt1 : t.toNat + 1 < (nA :: la).length := by
        have hltA : t.toNat < la.length :=
          list_lt_of_getElem?_some la t.toNat la[t.toNat] hgetA
        simp only [List.length_cons]
        omega
      obtain ⟨m₁, hstore⟩ : ∃ m₁, memStore m aa ta
          (t.toNat + 1) lt[t.toNat] = .ok m₁ :=
        ⟨_, memStore_cellsAt m aa ta (t.toNat + 1) (nA :: la)
          lt[t.toNat] hmem_a hlt1⟩
      have hstep := memSortCopyBody_hit prog F ρ m π la lt
        n w lo mid hi t lt[t.toNat] la[t.toNat]
        aa ab ta tb nB hlay_a hlay_tmp hmem_b hnB
        ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ hlent
        hgetT hgetA (Nat.lt_of_lt_of_le hT hhi_lt) _ hstore _ hwr _ hu
      have hloop : memEvalProgStmt prog (F + 1) sortCopyBack
          ρ m π = memEvalProgStmt prog F sortCopyBack ρ'' m₁ π := by
        cir_unfold_prog (sortCopyBack, prog, F, hcond, hstep.1)
      have h1t : (t + 1).toNat = t.toNat + 1 :=
        bv64_succ_toNat t _ hT (by omega)
      have hlena' : (la.set t.toNat lt[t.toNat]).length < 2 ^ 64 := by
        rw [List.length_set]; exact hlena
      have hhi_la' : hi.toNat ≤
          (la.set t.toNat lt[t.toNat]).length := by
        rw [List.length_set]; exact hhi_la
      have ht_le' : (t + 1).toNat ≤ hi.toNat := by omega
      have hF' : (hi.toNat - (t + 1).toNat) + 1 ≤ F := by omega
      have hM' : (hi.toNat - t.toNat) - 1 =
          (hi.toNat - (t + 1).toNat) := by omega
      have hfwd' : sortCopyFwd lt (la.set t.toNat lt[t.toNat])
          (hi.toNat - (t + 1).toNat) ((t + 1).toNat) hi.toNat =
          .error e := by
        rw [← h1t, hM'] at hfwdT
        exact hfwdT
      have hmem_a₁ : memFind m₁ aa =
          some ⟨ta, true, nA :: la.set t.toNat lt[t.toNat]⟩ := by
        have hcells := memFind_cellsAt_store m aa ta (t.toNat + 1)
          (nA :: la) lt[t.toNat] m₁ hmem_a hlt1 hstore
        have hsetEq : (nA :: la).set (t.toNat + 1) lt[t.toNat] =
            nA :: la.set t.toNat lt[t.toNat] :=
          List.set_cons_succ
        rw [hsetEq] at hcells
        exact hcells
      have hmem_b₁ : memFind m₁ ab = some ⟨tb, true, nB :: lt⟩ := by
        have h := memFind_memStore_other m m₁ aa ab ta
          (t.toNat + 1) lt[t.toNat] hstore (Ne.symm haa)
        rw [h]
        exact hmem_b
      rw [hloop]
      exact ih ρ'' m₁ π (la.set t.toNat lt[t.toNat]) lt n w lo mid
        hi (t + 1) e hlay_a hlay_tmp hmem_a₁ hmem_b₁ hnB
        hstep.2 hlent hlena' hhi_la' hhi_lt ht_le' hF' hfwd'
    · have hcond : memEvalExpr (.ult (.var "t") (.var "hi")) ρ m π =
          .ok (.b false) := by
        have hvarT : memEvalExpr (.var "t") ρ m π =
            evalExpr (.var "t") ρ := memEvalExpr_var _ _ _ _
        have hvarH : memEvalExpr (.var "hi") ρ m π =
            evalExpr (.var "hi") ρ := memEvalExpr_var _ _ _ _
        have hE : evalExpr (.ult (.var "t") (.var "hi")) ρ =
            .ok (.b false) := by
          obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
          have h := sortCopyGuardT_eval ρ la lt n w lo mid hi t
            ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩
          rwa [decide_eq_false hT] at h
        exact (memEvalExpr_ult_agree _ _ _ _ _ hvarT hvarH).trans hE
      have hfwd0 : sortCopyFwd lt la (hi.toNat - t.toNat) t.toNat
          hi.toNat = .ok (la, t.toNat) := by
        match hm : (hi.toNat - t.toNat) with
        | 0 => simp only [sortCopyFwd]
        | _ + 1 => simp only [sortCopyFwd, dite_eq_right hT]
      rw [hfwd0] at hfwd
      cases hfwd

/-! ## Clamp mirrors -/

/-- Program-level memory `skip` is a no-op (via the `memEvalStmtFuel`
fallback arm). -/
theorem memEvalProgStmt_skip (prog : Prog) (F : Nat) (ρ : Env)
    (m : Mem) (π : Layout) :
    memEvalProgStmt prog F .skip ρ m π = .ok ((ρ, m, π), .fellThrough) := by
  simp only [memEvalProgStmt]
  cases F <;> simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith]

/-- Clamp-`mid` step on memory: `mid := min mid n` (mem mirrors the
    eval `sortClampMid_step`; clamps touch env only). -/
theorem memSortClampMid_step (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (n w lo mid hi t : BitVec 64)
    (hinv : SortInv ρ la lt n w lo mid hi t)
    (hmid_eq : mid.toNat = lo.toNat + w.toNat) :
    ∃ ρ' mid', memEvalProgStmt prog F sortClampMid ρ m π =
      .ok ((ρ', m, π), .fellThrough) ∧
      SortInv ρ' la lt n w lo mid' hi t ∧
      mid'.toNat = Nat.min (lo.toNat + w.toNat) n.toNat := by
  obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
  have hvarN : memEvalExpr (.var "n") ρ m π = evalExpr (.var "n") ρ :=
    memEvalExpr_var _ _ _ _
  have hvarM : memEvalExpr (.var "mid") ρ m π =
      evalExpr (.var "mid") ρ := memEvalExpr_var _ _ _ _
  have hguard : memEvalExpr (.ult (.var "n") (.var "mid")) ρ m π =
      evalExpr (.ult (.var "n") (.var "mid")) ρ :=
    memEvalExpr_ult_agree _ _ _ _ _ hvarN hvarM
  have hguardE : evalExpr (.ult (.var "n") (.var "mid")) ρ =
      .ok (.b (decide (n.toNat < lo.toNat + w.toNat))) := by
    have hnv : evalExpr (.var "n") ρ = .ok (.u64 n) :=
      evalExpr_var_hit _ _ _ hn
    have hmv : evalExpr (.var "mid") ρ = .ok (.u64 mid) :=
      evalExpr_var_hit _ _ _ hmid
    have hult := evalExpr_ult_u64 _ _ _ _ _ hnv hmv
    rw [VecMergeRuns.bv64_ult_toNat n mid, hmid_eq] at hult
    exact hult
  by_cases hC : n.toNat < lo.toNat + w.toNat
  · have hcond : memEvalExpr (.ult (.var "n") (.var "mid")) ρ m π =
        .ok (.b true) := by
      have h := hguard.trans hguardE
      rwa [decide_eq_true hC] at h
    obtain ⟨ρ', hu⟩ := envUpdate_some_of_lookup ρ "mid"
      (.u64 mid) (.u64 n) hmid
    have hevN : evalExpr (.var "n") ρ = .ok (.u64 n) :=
      evalExpr_var_hit _ _ _ hn
    have hmemN : memEvalExpr (.var "n") ρ m π = .ok (.u64 n) :=
      hvarN.trans hevN
    have hassign : memEvalProgStmt prog F
        (.assign "mid" (.var "n")) ρ m π =
        .ok ((ρ', m, π), .fellThrough) :=
      memRevAssign prog F "mid" _ ρ m π _ ρ' hmemN hevN hu
    refine ⟨ρ', n, ?_, ?_, ?_⟩
    · have hbody : sortClampMid =
          (.if_ (.ult (.var "n") (.var "mid"))
            (.assign "mid" (.var "n")) .skip) := rfl
      rw [hbody]
      exact (memEvalProgStmt_if_true prog F _ _ _ _ _ _ hcond).trans
        hassign
    · exact sortInv_update_mid _ _ _ _ _ _ _ _ _ _ _
        ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ hu
    · show n.toNat = Nat.min (lo.toNat + w.toNat) n.toNat
      exact (Nat.min_eq_right (Nat.le_of_lt hC)).symm
  · have hcond : memEvalExpr (.ult (.var "n") (.var "mid")) ρ m π =
        .ok (.b false) := by
      have h := hguard.trans hguardE
      rwa [decide_eq_false hC] at h
    refine ⟨ρ, mid, ?_, ?_, ?_⟩
    · have hbody : sortClampMid =
          (.if_ (.ult (.var "n") (.var "mid"))
            (.assign "mid" (.var "n")) .skip) := rfl
      rw [hbody]
      exact (memEvalProgStmt_if_false prog F _ _ _ _ _ _ hcond).trans
        (memEvalProgStmt_skip prog F ρ m π)
    · exact ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩
    · show mid.toNat = Nat.min (lo.toNat + w.toNat) n.toNat
      rw [hmid_eq]
      exact (Nat.min_eq_left (Nat.le_of_not_gt hC)).symm

/-- Clamp-`hi` step on memory: `hi := min hi n` (mem mirrors the
    eval `sortClampHi_step`; clamps touch env only). -/
theorem memSortClampHi_step (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (n w lo mid hi t : BitVec 64)
    (hinv : SortInv ρ la lt n w lo mid hi t)
    (hhi_eq : hi.toNat = lo.toNat + w.toNat + w.toNat) :
    ∃ ρ' hi', memEvalProgStmt prog F sortClampHi ρ m π =
      .ok ((ρ', m, π), .fellThrough) ∧
      SortInv ρ' la lt n w lo mid hi' t ∧
      hi'.toNat = Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat := by
  obtain ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ := hinv
  have hvarN : memEvalExpr (.var "n") ρ m π = evalExpr (.var "n") ρ :=
    memEvalExpr_var _ _ _ _
  have hvarH : memEvalExpr (.var "hi") ρ m π =
      evalExpr (.var "hi") ρ := memEvalExpr_var _ _ _ _
  have hguard : memEvalExpr (.ult (.var "n") (.var "hi")) ρ m π =
      evalExpr (.ult (.var "n") (.var "hi")) ρ :=
    memEvalExpr_ult_agree _ _ _ _ _ hvarN hvarH
  have hguardE : evalExpr (.ult (.var "n") (.var "hi")) ρ =
      .ok (.b (decide (n.toNat < lo.toNat + w.toNat + w.toNat))) := by
    have hnv : evalExpr (.var "n") ρ = .ok (.u64 n) :=
      evalExpr_var_hit _ _ _ hn
    have hhv : evalExpr (.var "hi") ρ = .ok (.u64 hi) :=
      evalExpr_var_hit _ _ _ hhi
    have hult := evalExpr_ult_u64 _ _ _ _ _ hnv hhv
    rw [VecMergeRuns.bv64_ult_toNat n hi, hhi_eq] at hult
    exact hult
  by_cases hC : n.toNat < lo.toNat + w.toNat + w.toNat
  · have hcond : memEvalExpr (.ult (.var "n") (.var "hi")) ρ m π =
        .ok (.b true) := by
      have h := hguard.trans hguardE
      rwa [decide_eq_true hC] at h
    obtain ⟨ρ', hu⟩ := envUpdate_some_of_lookup ρ "hi"
      (.u64 hi) (.u64 n) hhi
    have hevN : evalExpr (.var "n") ρ = .ok (.u64 n) :=
      evalExpr_var_hit _ _ _ hn
    have hmemN : memEvalExpr (.var "n") ρ m π = .ok (.u64 n) :=
      hvarN.trans hevN
    have hassign : memEvalProgStmt prog F
        (.assign "hi" (.var "n")) ρ m π =
        .ok ((ρ', m, π), .fellThrough) :=
      memRevAssign prog F "hi" _ ρ m π _ ρ' hmemN hevN hu
    refine ⟨ρ', n, ?_, ?_, ?_⟩
    · have hbody : sortClampHi =
          (.if_ (.ult (.var "n") (.var "hi"))
            (.assign "hi" (.var "n")) .skip) := rfl
      rw [hbody]
      exact (memEvalProgStmt_if_true prog F _ _ _ _ _ _ hcond).trans
        hassign
    · exact sortInv_update_hi _ _ _ _ _ _ _ _ _ _ _
        ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩ hu
    · show n.toNat = Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat
      exact (Nat.min_eq_right (Nat.le_of_lt hC)).symm
  · have hcond : memEvalExpr (.ult (.var "n") (.var "hi")) ρ m π =
        .ok (.b false) := by
      have h := hguard.trans hguardE
      rwa [decide_eq_false hC] at h
    refine ⟨ρ, hi, ?_, ?_, ?_⟩
    · have hbody : sortClampHi =
          (.if_ (.ult (.var "n") (.var "hi"))
            (.assign "hi" (.var "n")) .skip) := rfl
      rw [hbody]
      exact (memEvalProgStmt_if_false prog F _ _ _ _ _ _ hcond).trans
        (memEvalProgStmt_skip prog F ρ m π)
    · exact ⟨ha, htmp, hn, hw, hlo, hmid, hhi, htt⟩
    · show hi.toNat = Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat
      rw [hhi_eq]
      exact (Nat.min_eq_left (Nat.le_of_not_gt hC)).symm

/-- Segment-body step on memory: bounds, clamps, sharing call into
    `merge_runs`, copy-back, advance. The call runs over the caller
    memory `m` (fresh callee blocks above `m.next`); the copy-back
    consumes the exported `tmp` pin, and the final state re-establishes
    the caller-visible pin set for the segment loop. -/
theorem memSortSegBody_step (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (n w lo mid₀ hi₀ t₀ : BitVec 64)
    (la_next : List (BitVec 32)) (lt' : List (BitVec 32))
    (t_next : Nat)
    (hinv : SortInv ρ la lt n w lo mid₀ hi₀ t₀)
    (hn : n.toNat = la.length)
    (hlent : lt.length < 2 ^ 64) (hlena : la.length < 2 ^ 64)
    (hlen62 : la.length < 2 ^ 62)
    (htmp_ge : la.length ≤ lt.length)
    (hw1 : 1 ≤ w.toNat) (hw_lt : w.toNat < n.toNat)
    (hLo : lo.toNat < n.toNat)
    (hF1 : 1 ≤ F)
    (hF : 2 * (n.toNat - lo.toNat) + 8 ≤ F)
    (hmr : VecMergeRuns.mergeRunsFwd la lt lo.toNat
      (Nat.min (lo.toNat + w.toNat) n.toNat)
      (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat) =
      .ok (.stdVecVal lt'))
    (hcp : sortCopyFwd lt' la
      (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat - lo.toNat)
      lo.toNat
      (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat) =
      .ok (la_next, t_next)) :
    ∃ ρ' m' π' lo' mid' hi' t' aa ab ta tb nA nB,
      memEvalProgStmt vecMergeSortProg F sortSegBody ρ m π =
        .ok ((ρ', m', π'), .fellThrough) ∧
      SortInv ρ' la_next lt' n w lo' mid' hi' t' ∧
      lo'.toNat = lo.toNat + w.toNat + w.toNat ∧
      lt'.length = lt.length ∧ la_next.length = la.length ∧
      layoutLookup π' "a" = some (aa, ta) ∧
      layoutLookup π' "tmp" = some (ab, tb) ∧
      memFind m' aa = some ⟨ta, true, nA :: la_next⟩ ∧
      memFind m' ab = some ⟨tb, true, nB :: lt'⟩ ∧
      nB = BitVec.ofNat 32 lt'.length := by
  obtain ⟨G, rfl, _⟩ := fuel_step_down 0 hF1
  obtain ⟨ha, htmp, hnL, hw, hlo, hmid₀, hhi₀, htt₀⟩ := hinv
  -- `mid ← lo + width`.
  have hadd1 : (lo + w).toNat = lo.toNat + w.toNat :=
    bv64_add_toNat lo w (by omega)
  have heval_mw : evalExpr (.uadd (.var "lo") (.var "width")) ρ =
      .ok (.u64 (lo + w)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hlo) (evalExpr_var_hit _ _ _ hw)
  have hmem_mw : memEvalExpr (.uadd (.var "lo") (.var "width")) ρ m π =
      .ok (.u64 (lo + w)) :=
    (memEvalExpr_uadd_agree _ _ _ _ _
      (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _)).trans heval_mw
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "mid"
    (.u64 mid₀) (.u64 (lo + w)) hmid₀
  have hstep₁ : memEvalProgStmt vecMergeSortProg (G + 1)
      (.assign "mid" (.uadd (.var "lo") (.var "width"))) ρ m π =
      .ok ((ρ₁, m, π), .fellThrough) :=
    memRevAssign vecMergeSortProg (G + 1) "mid" _ ρ m π _ ρ₁ hmem_mw heval_mw hu₁
  have hinv₁ : SortInv ρ₁ la lt n w lo (lo + w) hi₀ t₀ :=
    sortInv_update_mid _ _ _ _ _ _ _ _ _ _ _
      ⟨ha, htmp, hnL, hw, hlo, hmid₀, hhi₀, htt₀⟩ hu₁
  -- Clamp `mid`.
  obtain ⟨ρ₂, mid₂, heval₂, hinv₂, hmid₂⟩ :=
    memSortClampMid_step vecMergeSortProg (G + 1) ρ₁ m π la lt n w lo (lo + w) hi₀ t₀
      hinv₁ hadd1
  obtain ⟨ha₂, htmp₂, hnL₂, hw₂, hlo₂, hmid₂L, hhi₂, htt₂⟩ := hinv₂
  -- `hi ← (lo + width) + width`.
  have heval_lw : evalExpr (.uadd (.var "lo") (.var "width")) ρ₂ =
      .ok (.u64 (lo + w)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hlo₂) (evalExpr_var_hit _ _ _ hw₂)
  have heval_ww : evalExpr
      (.uadd (.uadd (.var "lo") (.var "width")) (.var "width")) ρ₂ =
      .ok (.u64 ((lo + w) + w)) :=
    evalExpr_uadd_u64 _ _ _ _ _ heval_lw
      (evalExpr_var_hit _ _ _ hw₂)
  have hagr_lw : memEvalExpr (.uadd (.var "lo") (.var "width")) ρ₂ m π =
      evalExpr (.uadd (.var "lo") (.var "width")) ρ₂ :=
    memEvalExpr_uadd_agree _ _ _ _ _
      (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _)
  have hmem_ww : memEvalExpr
      (.uadd (.uadd (.var "lo") (.var "width")) (.var "width")) ρ₂ m π =
      .ok (.u64 ((lo + w) + w)) :=
    (memEvalExpr_uadd_agree _ _ _ _ _ hagr_lw
      (memEvalExpr_var _ _ _ _)).trans heval_ww
  have hadd2 : ((lo + w) + w).toNat =
      lo.toNat + w.toNat + w.toNat := by
    have h2 : ((lo + w) + w).toNat = (lo + w).toNat + w.toNat :=
      bv64_add_toNat _ _ (by omega)
    omega
  obtain ⟨ρ₃, hu₃⟩ := envUpdate_some_of_lookup ρ₂ "hi"
    (.u64 hi₀) (.u64 ((lo + w) + w)) hhi₂
  have hstep₃ : memEvalProgStmt vecMergeSortProg (G + 1)
      (.assign "hi"
        (.uadd (.uadd (.var "lo") (.var "width")) (.var "width"))) ρ₂ m π =
      .ok ((ρ₃, m, π), .fellThrough) :=
    memRevAssign vecMergeSortProg (G + 1) "hi" _ ρ₂ m π _ ρ₃ hmem_ww heval_ww hu₃
  have hinv₃ : SortInv ρ₃ la lt n w lo mid₂ ((lo + w) + w) t₀ :=
    sortInv_update_hi _ _ _ _ _ _ _ _ _ _ _
      ⟨ha₂, htmp₂, hnL₂, hw₂, hlo₂, hmid₂L, hhi₂, htt₂⟩ hu₃
  -- Clamp `hi`.
  obtain ⟨ρ₄, hi₂, heval₄, hinv₄, hhi₂⟩ :=
    memSortClampHi_step vecMergeSortProg (G + 1) ρ₃ m π la lt n w lo mid₂
      ((lo + w) + w) t₀ hinv₃ hadd2
  obtain ⟨ha₄, htmp₄, hnL₄, hw₄, hlo₄, hmid₄, hhi₄, htt₄⟩ := hinv₄
  -- Clamp facts.
  have hmid_le_n : mid₂.toNat ≤ n.toNat := by
    rw [hmid₂]; exact Nat.min_le_right _ _
  have hhi_le_n : hi₂.toNat ≤ n.toNat := by
    rw [hhi₂]; exact Nat.min_le_right _ _
  have hlo_mid : lo.toNat ≤ mid₂.toNat := by
    rw [hmid₂]
    exact Nat.le_min.mpr ⟨Nat.le_add_right _ _, Nat.le_of_lt hLo⟩
  have hmid_hi : mid₂.toNat ≤ hi₂.toNat := by
    rw [hhi₂]
    refine Nat.le_min.mpr ⟨?_, hmid_le_n⟩
    have h1 : mid₂.toNat ≤ lo.toNat + w.toNat := by
      rw [hmid₂]; exact Nat.min_le_left _ _
    omega
  have hhi_n : hi₂.toNat ≤ n.toNat := hhi_le_n
  have hmid_le : mid₂.toNat ≤ la.length := by omega
  have hhi_le : hi₂.toNat ≤ la.length := by omega
  have hlo_lt : lo.toNat ≤ lt.length := by omega
  -- The call.
  have hargs : lookupArgs ρ₄ ["a", "tmp", "lo", "mid", "hi"] =
      some [.stdVecVal la, .stdVecVal lt, .u64 lo, .u64 mid₂,
        .u64 hi₂] := by
    simp [lookupArgs, ha₄, htmp₄, hlo₄, hmid₄, hhi₄]
  have hF_cal : ((mid₂.toNat - lo.toNat) + (hi₂.toNat - lo.toNat)) + 1 ≤
      G := by
    omega
  have hmr' : VecMergeRuns.mergeRunsFwd la lt lo.toNat mid₂.toNat
      hi₂.toNat = .ok (.stdVecVal lt') := by
    rwa [← hmid₂, ← hhi₂] at hmr
  obtain ⟨m_c, π_c, hOn, hPins⟩ := memEvalProgFuncOn_mergeRuns
    vecMergeSortProg G la lt lo mid₂ hi₂ m hlent hlo_mid hmid_hi hmid_le
    hhi_le hlo_lt hF_cal
  simp only [hmr'] at hOn
  simp only [hmr'] at hPins
  obtain ⟨hmpB, hmpA, hπeq⟩ := hPins
  have hcall : memEvalProgFuncOn vecMergeSortProg G
      VecMergeRuns.mergeRunsFunc
      [.stdVecVal la, .stdVecVal lt, .u64 lo, .u64 mid₂, .u64 hi₂] m =
      .ok ((.stdVecVal lt'), m_c, π_c) := hOn
  have hstep_call : memEvalProgStmt vecMergeSortProg (G + 1) sortSegCall
      ρ₄ m π =
      .ok ((envExtend ρ₄ "tmp" (.stdVecVal lt'), m_c, π_c ++ π),
        .fellThrough) :=
    memEvalProgStmt_callShare_ok vecMergeSortProg G "tmp"
      VecMergeRuns.mergeRunsName ["a", "tmp", "lo", "mid", "hi"] ρ₄ m π
      [.stdVecVal la, .stdVecVal lt, .u64 lo, .u64 mid₂, .u64 hi₂]
      VecMergeRuns.mergeRunsFunc (.stdVecVal lt') m_c π_c
      hargs findFunc_mergeRuns hcall
  have hlen' : lt'.length = lt.length := by
    exact VecMergeRuns.mergeRunsFwd_length la lt lo.toNat mid₂.toNat
      hi₂.toNat lt' hlo_mid hmid_hi hlo_lt hmr'
  have hlent' : lt'.length < 2 ^ 64 := by rw [hlen']; exact hlent
  have hinv₅ : SortInv (envExtend ρ₄ "tmp" (.stdVecVal lt')) la lt'
      n w lo mid₂ hi₂ t₀ :=
    sortInv_extend_tmp ρ₄ la lt lt' n w lo mid₂ hi₂ t₀
      ⟨ha₄, htmp₄, hnL₄, hw₄, hlo₄, hmid₄, hhi₄, htt₄⟩
  -- `t ← lo`.
  obtain ⟨ha₅, htmp₅, hnL₅, hw₅, hlo₅, hmid₅, hhi₅, htt₅⟩ := hinv₅
  have heval_tlo : evalExpr (.var "lo")
      (envExtend ρ₄ "tmp" (.stdVecVal lt')) = .ok (.u64 lo) :=
    evalExpr_var_hit _ _ _ hlo₅
  have hmem_tlo : memEvalExpr (.var "lo")
      (envExtend ρ₄ "tmp" (.stdVecVal lt')) m_c (π_c ++ π) =
      .ok (.u64 lo) :=
    (memEvalExpr_var _ _ _ _).trans heval_tlo
  obtain ⟨ρ₆, hu₆⟩ := envUpdate_some_of_lookup
    (envExtend ρ₄ "tmp" (.stdVecVal lt')) "t" (.u64 t₀) (.u64 lo) htt₅
  have hstep_t : memEvalProgStmt vecMergeSortProg (G + 1)
      (.assign "t" (.var "lo"))
      (envExtend ρ₄ "tmp" (.stdVecVal lt')) m_c (π_c ++ π) =
      .ok ((ρ₆, m_c, π_c ++ π), .fellThrough) :=
    memRevAssign vecMergeSortProg (G + 1) "t" _
      (envExtend ρ₄ "tmp" (.stdVecVal lt')) m_c (π_c ++ π) _ ρ₆
      hmem_tlo heval_tlo hu₆
  have hinv₆ : SortInv ρ₆ la lt' n w lo mid₂ hi₂ lo :=
    sortInv_update_t _ _ _ _ _ _ _ _ _ _ _
      ⟨ha₅, htmp₅, hnL₅, hw₅, hlo₅, hmid₅, hhi₅, htt₅⟩ hu₆
  -- Copy-back.
  have hhi_lt' : hi₂.toNat ≤ lt'.length := by omega
  have hF_copy : (hi₂.toNat - lo.toNat) + 1 ≤ G + 1 := by omega
  have hcp' : sortCopyFwd lt' la (hi₂.toNat - lo.toNat) lo.toNat
      hi₂.toNat = .ok (la_next, t_next) := by
    rwa [← hhi₂] at hcp
  have hlay_a_copy : layoutLookup (π_c ++ π) "a" =
      some (m.next + 1, m.next + 1) := by
    rw [hπeq]; rfl
  have hlay_tmp_copy : layoutLookup (π_c ++ π) "tmp" =
      some (m.next, m.next) := by
    rw [hπeq]; rfl
  have hnB_copy : BitVec.ofNat 32 lt.length =
      BitVec.ofNat 32 lt'.length := by
    rw [hlen']
  obtain ⟨ρ₇, m₇, hcopy, hinv₇', hmemA₇, hmemB₇⟩ := memSortCopy_ok
    vecMergeSortProg (G + 1) ρ₆ m_c (π_c ++ π)
    la lt' n w lo mid₂ hi₂ lo la_next t_next
    (m.next + 1) m.next (m.next + 1) m.next
    (BitVec.ofNat 32 la.length) (BitVec.ofNat 32 lt.length)
    (by omega : m.next + 1 ≠ m.next)
    hlay_a_copy hlay_tmp_copy hmpA hmpB hnB_copy
    hinv₆ hlent' hlena hhi_le hhi_lt' (by omega : lo.toNat ≤ hi₂.toNat)
    hF_copy hcp'
  obtain ⟨ha₇, htmp₇, hnL₇, hw₇, hlo₇, hmid₇, hhi₇, htt₇⟩ := hinv₇'
  -- `lo ← (lo + width) + width`.
  have heval_lw7 : evalExpr (.uadd (.var "lo") (.var "width")) ρ₇ =
      .ok (.u64 (lo + w)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hlo₇) (evalExpr_var_hit _ _ _ hw₇)
  have heval_ww7 : evalExpr
      (.uadd (.uadd (.var "lo") (.var "width")) (.var "width")) ρ₇ =
      .ok (.u64 ((lo + w) + w)) :=
    evalExpr_uadd_u64 _ _ _ _ _ heval_lw7
      (evalExpr_var_hit _ _ _ hw₇)
  have hagr_lw7 : memEvalExpr (.uadd (.var "lo") (.var "width")) ρ₇ m₇
      (π_c ++ π) =
      evalExpr (.uadd (.var "lo") (.var "width")) ρ₇ :=
    memEvalExpr_uadd_agree _ _ _ _ _
      (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _)
  have hmem_ww7 : memEvalExpr
      (.uadd (.uadd (.var "lo") (.var "width")) (.var "width")) ρ₇ m₇
      (π_c ++ π) =
      .ok (.u64 ((lo + w) + w)) :=
    (memEvalExpr_uadd_agree _ _ _ _ _ hagr_lw7
      (memEvalExpr_var _ _ _ _)).trans heval_ww7
  obtain ⟨ρ₈, hu₈⟩ := envUpdate_some_of_lookup ρ₇ "lo"
    (.u64 lo) (.u64 ((lo + w) + w)) hlo₇
  have hstep_lo : memEvalProgStmt vecMergeSortProg (G + 1)
      (.assign "lo"
        (.uadd (.uadd (.var "lo") (.var "width"))
          (.var "width"))) ρ₇ m₇ (π_c ++ π) =
      .ok ((ρ₈, m₇, π_c ++ π), .fellThrough) :=
    memRevAssign vecMergeSortProg (G + 1) "lo" _ ρ₇ m₇ (π_c ++ π) _ ρ₈
      hmem_ww7 heval_ww7 hu₈
  have hinv₈ : SortInv ρ₈ la_next lt' n w ((lo + w) + w) mid₂ hi₂
      (BitVec.ofNat 64 t_next) :=
    sortInv_update_lo _ _ _ _ _ _ _ _ _ _ _
      ⟨ha₇, htmp₇, hnL₇, hw₇, hlo₇, hmid₇, hhi₇, htt₇⟩ hu₈
  -- Assemble.
  have hbody : sortSegBody =
      (.seq (.assign "mid" (.uadd (.var "lo") (.var "width")))
        (.seq sortClampMid
          (.seq (.assign "hi"
                  (.uadd (.uadd (.var "lo") (.var "width"))
                    (.var "width")))
            (.seq sortClampHi
              (.seq sortSegCall
                (.seq (.assign "t" (.var "lo"))
                  (.seq sortCopyBack
                    (.assign "lo"
                      (.uadd (.uadd (.var "lo") (.var "width"))
                        (.var "width")))))))))) := rfl
  have hlen_copy : la_next.length = la.length :=
    sortCopyFwd_length lt' la
      (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat - lo.toNat)
      lo.toNat
      (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat)
      la_next t_next hcp
  refine ⟨ρ₈, m₇, (π_c ++ π), ((lo + w) + w), mid₂, hi₂,
    (BitVec.ofNat 64 t_next), (m.next + 1), m.next, (m.next + 1), m.next,
    (BitVec.ofNat 32 la.length), (BitVec.ofNat 32 lt.length),
    ?_, hinv₈, hadd2, hlen', hlen_copy, hlay_a_copy, hlay_tmp_copy,
    hmemA₇, hmemB₇, hnB_copy⟩
  rw [hbody,
    memEvalProgStmt_seq_fallthrough vecMergeSortProg (G + 1) _ _ _ _ _ _ _ _
      hstep₁,
    memEvalProgStmt_seq_fallthrough vecMergeSortProg (G + 1) _ _ _ _ _ _ _ _
      heval₂,
    memEvalProgStmt_seq_fallthrough vecMergeSortProg (G + 1) _ _ _ _ _ _ _ _
      hstep₃,
    memEvalProgStmt_seq_fallthrough vecMergeSortProg (G + 1) _ _ _ _ _ _ _ _
      heval₄,
    memEvalProgStmt_seq_fallthrough vecMergeSortProg (G + 1) _ _ _ _ _ _ _ _
      hstep_call,
    memEvalProgStmt_seq_fallthrough vecMergeSortProg (G + 1) _ _ _ _ _ _ _ _
      hstep_t,
    memEvalProgStmt_seq_fallthrough vecMergeSortProg (G + 1) _ _ _ _ _ _ _ _
      hcopy]
  exact hstep_lo

/-- Combined clamps on memory: `mid ← lo + width`, clamp `mid`,
    `hi ← (lo + width) + width`, clamp `hi` (env-only; memory and
    layout thread through untouched). -/
theorem memSortSegClamps_step (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (n w lo mid₀ hi₀ t₀ : BitVec 64)
    (hinv : SortInv ρ la lt n w lo mid₀ hi₀ t₀)
    (hn : n.toNat = la.length)
    (hlent : lt.length < 2 ^ 64) (hlena : la.length < 2 ^ 64)
    (hlen62 : la.length < 2 ^ 62)
    (htmp_ge : la.length ≤ lt.length)
    (hw1 : 1 ≤ w.toNat) (hw_lt : w.toNat < n.toNat)
    (hLo : lo.toNat < n.toNat) :
    ∃ ρ₁ ρ₂ ρ₃ ρ₄ mid₂ hi₂,
      memEvalProgStmt vecMergeSortProg F
        (.assign "mid" (.uadd (.var "lo") (.var "width"))) ρ m π =
        .ok ((ρ₁, m, π), .fellThrough) ∧
      memEvalProgStmt vecMergeSortProg F sortClampMid ρ₁ m π =
        .ok ((ρ₂, m, π), .fellThrough) ∧
      memEvalProgStmt vecMergeSortProg F
        (.assign "hi"
          (.uadd (.uadd (.var "lo") (.var "width"))
            (.var "width"))) ρ₂ m π = .ok ((ρ₃, m, π), .fellThrough) ∧
      memEvalProgStmt vecMergeSortProg F sortClampHi ρ₃ m π =
        .ok ((ρ₄, m, π), .fellThrough) ∧
      SortInv ρ₄ la lt n w lo mid₂ hi₂ t₀ ∧
      mid₂.toNat = Nat.min (lo.toNat + w.toNat) n.toNat ∧
      hi₂.toNat = Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat := by
  obtain ⟨ha, htmp, hnL, hw, hlo, hmid₀, hhi₀, htt₀⟩ := hinv
  have hadd1 : (lo + w).toNat = lo.toNat + w.toNat :=
    bv64_add_toNat lo w (by omega)
  have heval_mw : evalExpr (.uadd (.var "lo") (.var "width")) ρ =
      .ok (.u64 (lo + w)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hlo) (evalExpr_var_hit _ _ _ hw)
  have hmem_mw : memEvalExpr (.uadd (.var "lo") (.var "width")) ρ m π =
      .ok (.u64 (lo + w)) :=
    (memEvalExpr_uadd_agree _ _ _ _ _
      (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _)).trans heval_mw
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "mid"
    (.u64 mid₀) (.u64 (lo + w)) hmid₀
  have hstep₁ : memEvalProgStmt vecMergeSortProg F
      (.assign "mid" (.uadd (.var "lo") (.var "width"))) ρ m π =
      .ok ((ρ₁, m, π), .fellThrough) :=
    memRevAssign vecMergeSortProg F "mid" _ ρ m π _ ρ₁ hmem_mw heval_mw hu₁
  have hinv₁ : SortInv ρ₁ la lt n w lo (lo + w) hi₀ t₀ :=
    sortInv_update_mid _ _ _ _ _ _ _ _ _ _ _
      ⟨ha, htmp, hnL, hw, hlo, hmid₀, hhi₀, htt₀⟩ hu₁
  obtain ⟨ρ₂, mid₂, heval₂, hinv₂, hmid₂⟩ :=
    memSortClampMid_step vecMergeSortProg F ρ₁ m π la lt n w lo (lo + w)
      hi₀ t₀ hinv₁ hadd1
  obtain ⟨ha₂, htmp₂, hnL₂, hw₂, hlo₂, hmid₂L, hhi₂, htt₂⟩ := hinv₂
  have heval_lw : evalExpr (.uadd (.var "lo") (.var "width")) ρ₂ =
      .ok (.u64 (lo + w)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hlo₂) (evalExpr_var_hit _ _ _ hw₂)
  have heval_ww : evalExpr
      (.uadd (.uadd (.var "lo") (.var "width")) (.var "width")) ρ₂ =
      .ok (.u64 ((lo + w) + w)) :=
    evalExpr_uadd_u64 _ _ _ _ _ heval_lw
      (evalExpr_var_hit _ _ _ hw₂)
  have hagr_lw : memEvalExpr (.uadd (.var "lo") (.var "width")) ρ₂ m π =
      evalExpr (.uadd (.var "lo") (.var "width")) ρ₂ :=
    memEvalExpr_uadd_agree _ _ _ _ _
      (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _)
  have hmem_ww : memEvalExpr
      (.uadd (.uadd (.var "lo") (.var "width")) (.var "width")) ρ₂ m π =
      .ok (.u64 ((lo + w) + w)) :=
    (memEvalExpr_uadd_agree _ _ _ _ _ hagr_lw
      (memEvalExpr_var _ _ _ _)).trans heval_ww
  have hadd2 : ((lo + w) + w).toNat =
      lo.toNat + w.toNat + w.toNat := by
    have h2 : ((lo + w) + w).toNat = (lo + w).toNat + w.toNat :=
      bv64_add_toNat _ _ (by omega)
    omega
  obtain ⟨ρ₃, hu₃⟩ := envUpdate_some_of_lookup ρ₂ "hi"
    (.u64 hi₀) (.u64 ((lo + w) + w)) hhi₂
  have hstep₃ : memEvalProgStmt vecMergeSortProg F
      (.assign "hi"
        (.uadd (.uadd (.var "lo") (.var "width")) (.var "width"))) ρ₂ m π =
      .ok ((ρ₃, m, π), .fellThrough) :=
    memRevAssign vecMergeSortProg F "hi" _ ρ₂ m π _ ρ₃ hmem_ww heval_ww hu₃
  have hinv₃ : SortInv ρ₃ la lt n w lo mid₂ ((lo + w) + w) t₀ :=
    sortInv_update_hi _ _ _ _ _ _ _ _ _ _ _
      ⟨ha₂, htmp₂, hnL₂, hw₂, hlo₂, hmid₂L, hhi₂, htt₂⟩ hu₃
  obtain ⟨ρ₄, hi₂, heval₄, hinv₄, hhi₂⟩ :=
    memSortClampHi_step vecMergeSortProg F ρ₃ m π la lt n w lo mid₂
      ((lo + w) + w) t₀ hinv₃ hadd2
  exact ⟨ρ₁, ρ₂, ρ₃, ρ₄, mid₂, hi₂, hstep₁, heval₂, hstep₃, heval₄, hinv₄,
    hmid₂, hhi₂⟩

/-- Segment-loop ok soundness on memory: the first calls-in-loops
    induction, threading the pin set through iterations (each body
    re-establishes fresh pins over the grown memory). -/
theorem memSortSeg_ok (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (n w lo mid₀ hi₀ t₀ : BitVec 64)
    (la' lt' : List (BitVec 32))
    (aa ab : Addr) (ta tb : Nat) (nA nB : BitVec 32)
    (hinv : SortInv ρ la lt n w lo mid₀ hi₀ t₀)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_tmp : layoutLookup π "tmp" = some (ab, tb))
    (hmem_a : memFind m aa = some ⟨ta, true, nA :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nB :: lt⟩)
    (hnB : nB = BitVec.ofNat 32 lt.length)
    (hn : n.toNat = la.length)
    (hlent : lt.length < 2 ^ 64) (hlena : la.length < 2 ^ 64)
    (hlen62 : la.length < 2 ^ 62)
    (htmp_ge : la.length ≤ lt.length)
    (hw1 : 1 ≤ w.toNat) (hw_lt : w.toNat < n.toNat)
    (hF : 2 * (n.toNat - lo.toNat) + 9 ≤ F)
    (hfwd : sortSegFwd la lt F w.toNat lo.toNat n.toNat =
      .ok (la', lt')) :
    ∃ ρ' m' π' lo' mid' hi' t' aa' ab' ta' tb' nA' nB',
      memEvalProgStmt vecMergeSortProg F sortSegLoop ρ m π =
        .ok ((ρ', m', π'), .fellThrough) ∧
      SortInv ρ' la' lt' n w lo' mid' hi' t' ∧
      layoutLookup π' "a" = some (aa', ta') ∧
      layoutLookup π' "tmp" = some (ab', tb') ∧
      memFind m' aa' = some ⟨ta', true, nA' :: la'⟩ ∧
      memFind m' ab' = some ⟨tb', true, nB' :: lt'⟩ ∧
      nB' = BitVec.ofNat 32 lt'.length := by
  induction F generalizing ρ m π la lt n w lo mid₀ hi₀ t₀ la' lt'
      aa ab ta tb nA nB with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hLo : lo.toNat < n.toNat
    · have hguard : memEvalExpr (.ult (.var "lo") (.var "n")) ρ m π =
          evalExpr (.ult (.var "lo") (.var "n")) ρ :=
        memEvalExpr_ult_agree _ _ _ _ _
          (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _)
      have hcond : memEvalExpr (.ult (.var "lo") (.var "n")) ρ m π =
          .ok (.b true) := by
        rw [hguard]
        have h := sortSegGuardLo_eval ρ la lt n w lo mid₀ hi₀ t₀ hinv
        rwa [decide_eq_true hLo] at h
      simp only [sortSegFwd, dite_eq_left hLo] at hfwd
      match hmr : VecMergeRuns.mergeRunsFwd la lt lo.toNat
          (Nat.min (lo.toNat + w.toNat) n.toNat)
          (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat) with
      | .error e => simp [hmr] at hfwd
      | .ok v =>
        obtain ⟨lt₁, rfl⟩ := VecMergeRuns.mergeRunsFwd_ok_shape la lt lo.toNat
          (Nat.min (lo.toNat + w.toNat) n.toNat)
          (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat) v hmr
        simp only [hmr] at hfwd
        match hcp : sortCopyFwd lt₁ la
            (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat -
              lo.toNat)
            lo.toNat
            (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat) with
        | .error e => simp [hcp] at hfwd
        | .ok (la₁, t₁) =>
          simp only [hcp] at hfwd
          obtain ⟨ρ₁, m₁, π₁, lo₁, mid₁, hi₁, t₁', aa₁, ab₁, ta₁, tb₁,
              nA₁, nB₁, heval_body, hinv₁, hlo₁eq, hlen₁', hlen_copy₁,
              hlay_a₁, hlay_tmp₁, hmem_a₁, hmem_b₁, hnB₁⟩ :=
            memSortSegBody_step F ρ m π la lt n w lo mid₀ hi₀ t₀ la₁ lt₁ t₁
              hinv hn hlent hlena hlen62 htmp_ge hw1 hw_lt hLo
              (by omega) (by omega) hmr hcp
          have hlent₁ : lt₁.length < 2 ^ 64 := by
            rw [hlen₁']; exact hlent
          have hn₁ : n.toNat = la₁.length := by
            rw [hlen_copy₁]; exact hn
          have hlena₁ : la₁.length < 2 ^ 64 := by
            rw [hlen_copy₁]; exact hlena
          have hlen62₁ : la₁.length < 2 ^ 62 := by
            rw [hlen_copy₁]; exact hlen62
          have htmp_ge₁ : la₁.length ≤ lt₁.length := by
            rw [hlen_copy₁, hlen₁']; exact htmp_ge
          have hloop : memEvalProgStmt vecMergeSortProg (F + 1)
              sortSegLoop ρ m π =
              memEvalProgStmt vecMergeSortProg F sortSegLoop ρ₁ m₁ π₁ := by
            cir_unfold_prog (sortSegLoop, vecMergeSortProg, F, hcond, heval_body)
          have hF' : 2 * (n.toNat - lo₁.toNat) + 9 ≤ F := by omega
          have hfwd' : sortSegFwd la₁ lt₁ F w.toNat lo₁.toNat
              n.toNat = .ok (la', lt') := by
            rw [hlo₁eq]; exact hfwd
          rw [hloop]
          obtain ⟨ρ', m', π', lo', mid', hi', t', aa', ab', ta', tb', nA',
              nB', hev, hinv', hlay_a', hlay_tmp', hmem_a', hmem_b',
              hnB'⟩ :=
            ih _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinv₁ hlay_a₁
              hlay_tmp₁ hmem_a₁ hmem_b₁ hnB₁ hn₁ hlent₁ hlena₁ hlen62₁
              htmp_ge₁ hw1 hw_lt hF' hfwd'
          exact ⟨ρ', m', π', lo', mid', hi', t', aa', ab', ta', tb', nA',
            nB', hev, hinv', hlay_a', hlay_tmp', hmem_a', hmem_b', hnB'⟩
    · have hguard : memEvalExpr (.ult (.var "lo") (.var "n")) ρ m π =
          evalExpr (.ult (.var "lo") (.var "n")) ρ :=
        memEvalExpr_ult_agree _ _ _ _ _
          (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _)
      have hcond : memEvalExpr (.ult (.var "lo") (.var "n")) ρ m π =
          .ok (.b false) := by
        rw [hguard]
        have h := sortSegGuardLo_eval ρ la lt n w lo mid₀ hi₀ t₀ hinv
        rwa [decide_eq_false hLo] at h
      have hfwd0 : sortSegFwd la lt (F + 1) w.toNat lo.toNat
          n.toNat = .ok (la, lt) := by
        simp only [sortSegFwd, dite_eq_right hLo]
      rw [hfwd0] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl⟩ := hfwd
      have hexit : memEvalProgStmt vecMergeSortProg (F + 1) sortSegLoop
          ρ m π = .ok ((ρ, m, π), .fellThrough) :=
        memEvalProgStmt_while_false vecMergeSortProg _ _ _ _ _ _ hcond
      exact ⟨ρ, m, π, lo, mid₀, hi₀, t₀, aa, ab, ta, tb, nA, nB, hexit,
        hinv, hlay_a, hlay_tmp, hmem_a, hmem_b, hnB⟩

/-- Segment-loop err soundness on memory. -/
theorem memSortSeg_err (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (n w lo mid₀ hi₀ t₀ : BitVec 64)
    (e : Panic)
    (hinv : SortInv ρ la lt n w lo mid₀ hi₀ t₀)
    (hn : n.toNat = la.length)
    (hlent : lt.length < 2 ^ 64) (hlena : la.length < 2 ^ 64)
    (hlen62 : la.length < 2 ^ 62)
    (htmp_ge : la.length ≤ lt.length)
    (hw1 : 1 ≤ w.toNat) (hw_lt : w.toNat < n.toNat)
    (hF : 2 * (n.toNat - lo.toNat) + 9 ≤ F)
    (hfwd : sortSegFwd la lt F w.toNat lo.toNat n.toNat = .error e) :
    memEvalProgStmt vecMergeSortProg F sortSegLoop ρ m π = .error e := by
  induction F generalizing ρ m π la lt n w lo mid₀ hi₀ t₀ e with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hLo : lo.toNat < n.toNat
    · have hguard : memEvalExpr (.ult (.var "lo") (.var "n")) ρ m π =
          evalExpr (.ult (.var "lo") (.var "n")) ρ :=
        memEvalExpr_ult_agree _ _ _ _ _
          (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _)
      have hcond : memEvalExpr (.ult (.var "lo") (.var "n")) ρ m π =
          .ok (.b true) := by
        rw [hguard]
        have h := sortSegGuardLo_eval ρ la lt n w lo mid₀ hi₀ t₀ hinv
        rwa [decide_eq_true hLo] at h
      have hF8 : 2 * (n.toNat - lo.toNat) + 8 ≤ F :=
        Nat.le_of_succ_le_succ hF
      obtain ⟨G, rfl, _⟩ :=
        fuel_step_down (2 * (n.toNat - lo.toNat) + 7) hF8
      obtain ⟨ρ₁, ρ₂, ρ₃, ρ₄, mid₂, hi₂, hstep₁, heval₂,
          hstep₃, heval₄, hinv₄, hmid₂, hhi₂⟩ :=
        memSortSegClamps_step (G + 1) ρ m π la lt n w lo mid₀ hi₀ t₀ hinv
          hn hlent hlena hlen62 htmp_ge hw1 hw_lt hLo
      have hbody : sortSegBody =
          (.seq (.assign "mid" (.uadd (.var "lo") (.var "width")))
            (.seq sortClampMid
              (.seq (.assign "hi"
                      (.uadd (.uadd (.var "lo") (.var "width"))
                        (.var "width")))
                (.seq sortClampHi
                  (.seq sortSegCall
                    (.seq (.assign "t" (.var "lo"))
                      (.seq sortCopyBack
                        (.assign "lo"
                          (.uadd (.uadd (.var "lo") (.var "width"))
                            (.var "width")))))))))) := rfl
      have hpre : memEvalProgStmt vecMergeSortProg (G + 1) sortSegBody
          ρ m π = memEvalProgStmt vecMergeSortProg (G + 1)
          (.seq sortSegCall
            (.seq (.assign "t" (.var "lo"))
              (.seq sortCopyBack
                (.assign "lo"
                  (.uadd (.uadd (.var "lo") (.var "width"))
                    (.var "width")))))) ρ₄ m π := by
        rw [hbody,
          memEvalProgStmt_seq_fallthrough vecMergeSortProg (G + 1) _ _ _ _ _ _ _ _
            hstep₁,
          memEvalProgStmt_seq_fallthrough vecMergeSortProg (G + 1) _ _ _ _ _ _ _ _
            heval₂,
          memEvalProgStmt_seq_fallthrough vecMergeSortProg (G + 1) _ _ _ _ _ _ _ _
            hstep₃,
          memEvalProgStmt_seq_fallthrough vecMergeSortProg (G + 1) _ _ _ _ _ _ _ _
            heval₄]
      obtain ⟨ha₄, htmp₄, hnL₄, hw₄, hlo₄, hmid₄, hhi₄, htt₄⟩ := hinv₄
      have hmid_le_n : mid₂.toNat ≤ n.toNat := by
        rw [hmid₂]; exact Nat.min_le_right _ _
      have hhi_le_n : hi₂.toNat ≤ n.toNat := by
        rw [hhi₂]; exact Nat.min_le_right _ _
      have hlo_mid : lo.toNat ≤ mid₂.toNat := by
        rw [hmid₂]
        exact Nat.le_min.mpr ⟨Nat.le_add_right _ _, Nat.le_of_lt hLo⟩
      have hmid_hi : mid₂.toNat ≤ hi₂.toNat := by
        rw [hhi₂]
        refine Nat.le_min.mpr ⟨?_, hmid_le_n⟩
        · have h1 : mid₂.toNat ≤ lo.toNat + w.toNat := by
            rw [hmid₂]; exact Nat.min_le_left _ _
          omega
      have hmid_le : mid₂.toNat ≤ la.length := by omega
      have hhi_le : hi₂.toNat ≤ la.length := by omega
      have hlo_lt : lo.toNat ≤ lt.length := by omega
      have hargs : lookupArgs ρ₄ ["a", "tmp", "lo", "mid", "hi"] =
          some [.stdVecVal la, .stdVecVal lt, .u64 lo, .u64 mid₂,
            .u64 hi₂] := by
        simp [lookupArgs, ha₄, htmp₄, hlo₄, hmid₄, hhi₄]
      have hF_cal : ((mid₂.toNat - lo.toNat) +
          (hi₂.toNat - lo.toNat)) + 1 ≤ G := by
        omega
      obtain ⟨m_c, π_c, hOn, hPins⟩ := memEvalProgFuncOn_mergeRuns
        vecMergeSortProg G la lt lo mid₂ hi₂ m hlent hlo_mid hmid_hi
        hmid_le hhi_le hlo_lt hF_cal
      rw [hmid₂, hhi₂] at hOn
      simp only [sortSegFwd, dite_eq_left hLo] at hfwd
      match hmr : VecMergeRuns.mergeRunsFwd la lt lo.toNat
          (Nat.min (lo.toNat + w.toNat) n.toNat)
          (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat) with
      | .error e' =>
        simp [hmr] at hfwd
        cases hfwd
        have hcall : memEvalProgFuncOn vecMergeSortProg G
            VecMergeRuns.mergeRunsFunc
            [.stdVecVal la, .stdVecVal lt, .u64 lo, .u64 mid₂,
              .u64 hi₂] m =
            .error e := by
          rw [hOn, hmr]
        have hstep_call := memEvalProgStmt_callShare_err vecMergeSortProg
          G "tmp" VecMergeRuns.mergeRunsName ["a", "tmp", "lo", "mid", "hi"]
          ρ₄ m π
          [.stdVecVal la, .stdVecVal lt, .u64 lo, .u64 mid₂, .u64 hi₂]
          VecMergeRuns.mergeRunsFunc e hargs findFunc_mergeRuns hcall
        have hfull : memEvalProgStmt vecMergeSortProg (G + 1)
            sortSegBody ρ m π = .error e := by
          rw [hpre]
          exact memEvalProgStmt_seq_err vecMergeSortProg (G + 1) _ _ _ _ _ _
            hstep_call
        have hloop : memEvalProgStmt vecMergeSortProg ((G + 1) + 1)
            sortSegLoop ρ m π = .error e := by
          cir_unfold_prog (sortSegLoop, vecMergeSortProg, (G + 1), hcond, hfull)
        exact hloop
      | .ok v =>
        obtain ⟨lt₁, rfl⟩ := VecMergeRuns.mergeRunsFwd_ok_shape la lt lo.toNat
          (Nat.min (lo.toNat + w.toNat) n.toNat)
          (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat) v hmr
        simp only [hmr] at hfwd
        have hmr' : VecMergeRuns.mergeRunsFwd la lt lo.toNat mid₂.toNat
            hi₂.toNat = .ok (.stdVecVal lt₁) := by
          rwa [← hmid₂, ← hhi₂] at hmr
        simp only [hmr] at hOn
        simp only [hmr'] at hPins
        obtain ⟨hmpB, hmpA, hπeq⟩ := hPins
        have hcall : memEvalProgFuncOn vecMergeSortProg G
            VecMergeRuns.mergeRunsFunc
            [.stdVecVal la, .stdVecVal lt, .u64 lo, .u64 mid₂,
              .u64 hi₂] m =
            .ok ((.stdVecVal lt₁), m_c, π_c) := hOn
        have hstep_call : memEvalProgStmt vecMergeSortProg (G + 1)
            sortSegCall ρ₄ m π =
            .ok ((envExtend ρ₄ "tmp" (.stdVecVal lt₁), m_c, π_c ++ π),
              .fellThrough) :=
          memEvalProgStmt_callShare_ok vecMergeSortProg G "tmp"
            VecMergeRuns.mergeRunsName ["a", "tmp", "lo", "mid", "hi"] ρ₄
            m π
            [.stdVecVal la, .stdVecVal lt, .u64 lo, .u64 mid₂, .u64 hi₂]
            VecMergeRuns.mergeRunsFunc (.stdVecVal lt₁) m_c π_c
            hargs findFunc_mergeRuns hcall
        have hlen₁' : lt₁.length = lt.length := by
          exact VecMergeRuns.mergeRunsFwd_length la lt lo.toNat mid₂.toNat
            hi₂.toNat lt₁ hlo_mid hmid_hi hlo_lt hmr'
        have hlent₁ : lt₁.length < 2 ^ 64 := by
          rw [hlen₁']; exact hlent
        have hinv₅ : SortInv
            (envExtend ρ₄ "tmp" (.stdVecVal lt₁)) la lt₁ n w lo mid₂
            hi₂ t₀ :=
          sortInv_extend_tmp ρ₄ la lt lt₁ n w lo mid₂ hi₂ t₀
            ⟨ha₄, htmp₄, hnL₄, hw₄, hlo₄, hmid₄, hhi₄, htt₄⟩
        obtain ⟨ha₅, htmp₅, hnL₅, hw₅, hlo₅, hmid₅, hhi₅, htt₅⟩ :=
          hinv₅
        have heval_tlo : evalExpr (.var "lo")
            (envExtend ρ₄ "tmp" (.stdVecVal lt₁)) = .ok (.u64 lo) :=
          evalExpr_var_hit _ _ _ hlo₅
        have hmem_tlo : memEvalExpr (.var "lo")
            (envExtend ρ₄ "tmp" (.stdVecVal lt₁)) m_c (π_c ++ π) =
            .ok (.u64 lo) :=
          (memEvalExpr_var _ _ _ _).trans heval_tlo
        obtain ⟨ρ₆, hu₆⟩ := envUpdate_some_of_lookup
          (envExtend ρ₄ "tmp" (.stdVecVal lt₁)) "t" (.u64 t₀)
          (.u64 lo) htt₅
        have hstep_t : memEvalProgStmt vecMergeSortProg (G + 1)
            (.assign "t" (.var "lo"))
            (envExtend ρ₄ "tmp" (.stdVecVal lt₁)) m_c (π_c ++ π) =
            .ok ((ρ₆, m_c, π_c ++ π), .fellThrough) :=
          memRevAssign vecMergeSortProg (G + 1) "t" _
            (envExtend ρ₄ "tmp" (.stdVecVal lt₁)) m_c (π_c ++ π) _ ρ₆
            hmem_tlo heval_tlo hu₆
        have hinv₆ : SortInv ρ₆ la lt₁ n w lo mid₂ hi₂ lo :=
          sortInv_update_t _ _ _ _ _ _ _ _ _ _ _
            ⟨ha₅, htmp₅, hnL₅, hw₅, hlo₅, hmid₅, hhi₅, htt₅⟩ hu₆
        match hcp : sortCopyFwd lt₁ la
            (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat -
              lo.toNat)
            lo.toNat
            (Nat.min (lo.toNat + w.toNat + w.toNat) n.toNat) with
        | .error e' =>
          simp [hcp] at hfwd
          cases hfwd
          have hhi_lt₁ : hi₂.toNat ≤ lt₁.length := by omega
          have hF_copy : (hi₂.toNat - lo.toNat) + 1 ≤ G + 1 := by
            omega
          have hcp' : sortCopyFwd lt₁ la (hi₂.toNat - lo.toNat)
              lo.toNat hi₂.toNat = .error e := by
            rwa [← hhi₂] at hcp
          have hlay_a_copy : layoutLookup (π_c ++ π) "a" =
              some (m.next + 1, m.next + 1) := by
            rw [hπeq]; rfl
          have hlay_tmp_copy : layoutLookup (π_c ++ π) "tmp" =
              some (m.next, m.next) := by
            rw [hπeq]; rfl
          have hnB_copy : BitVec.ofNat 32 lt.length =
              BitVec.ofNat 32 lt₁.length := by
            rw [hlen₁']
          have hcp_err := memSortCopy_err vecMergeSortProg (G + 1) ρ₆ m_c
            (π_c ++ π) la lt₁ n w lo mid₂ hi₂ lo e
            (m.next + 1) m.next (m.next + 1) m.next
            (BitVec.ofNat 32 la.length) (BitVec.ofNat 32 lt.length)
            (by omega : m.next + 1 ≠ m.next)
            hlay_a_copy hlay_tmp_copy hmpA hmpB hnB_copy
            hinv₆ hlent₁ hlena hhi_le hhi_lt₁ (by omega : lo.toNat ≤ hi₂.toNat)
            hF_copy hcp'
          have hrest : memEvalProgStmt vecMergeSortProg (G + 1)
              (.seq sortSegCall
                (.seq (.assign "t" (.var "lo"))
                  (.seq sortCopyBack
                    (.assign "lo"
                      (.uadd (.uadd (.var "lo") (.var "width"))
                        (.var "width")))))) ρ₄ m π = .error e := by
            rw [memEvalProgStmt_seq_fallthrough vecMergeSortProg (G + 1) _ _ _ _ _ _ _ _
              hstep_call,
              memEvalProgStmt_seq_fallthrough vecMergeSortProg (G + 1) _ _ _ _ _ _ _ _
                hstep_t]
            exact memEvalProgStmt_seq_err vecMergeSortProg (G + 1) _ _ _ _ _ _
              hcp_err
          have hfull : memEvalProgStmt vecMergeSortProg (G + 1)
              sortSegBody ρ m π = .error e := by
            rw [hpre]
            exact hrest
          have hloop : memEvalProgStmt vecMergeSortProg ((G + 1) + 1)
              sortSegLoop ρ m π = .error e := by
            cir_unfold_prog (sortSegLoop, vecMergeSortProg, (G + 1), hcond, hfull)
          exact hloop
        | .ok (la₁, t₁) =>
          simp only [hcp] at hfwd
          obtain ⟨ρ₈, m₈, π₈, lo₈, mid₈, hi₈, t₈, aa₈, ab₈, ta₈, tb₈, nA₈,
              nB₈, heval_ok, hinv₈, hlo₈eq, hlen₈', hlen_copy₈, hlay_a₈,
              hlay_tmp₈, hmem_a₈, hmem_b₈, hnB₈⟩ :=
            memSortSegBody_step (G + 1) ρ m π la lt n w lo mid₀ hi₀ t₀ la₁
              lt₁ t₁ hinv hn hlent hlena hlen62 htmp_ge hw1 hw_lt hLo
              (by omega) (by omega) hmr hcp
          have hlent₈ : lt₁.length < 2 ^ 64 := by
            rw [hlen₈']; exact hlent
          have hn₈ : n.toNat = la₁.length := by
            rw [hlen_copy₈]; exact hn
          have hlena₈ : la₁.length < 2 ^ 64 := by
            rw [hlen_copy₈]; exact hlena
          have hlen62₈ : la₁.length < 2 ^ 62 := by
            rw [hlen_copy₈]; exact hlen62
          have htmp_ge₈ : la₁.length ≤ lt₁.length := by
            rw [hlen_copy₈, hlen₈']; exact htmp_ge
          have hF' : 2 * (n.toNat - lo₈.toNat) + 9 ≤ G + 1 := by
            omega
          have hfwd' : sortSegFwd la₁ lt₁ (G + 1) w.toNat lo₈.toNat
              n.toNat = .error e := by
            rw [hlo₈eq]; exact hfwd
          have hloop : memEvalProgStmt vecMergeSortProg ((G + 1) + 1)
              sortSegLoop ρ m π =
              memEvalProgStmt vecMergeSortProg (G + 1) sortSegLoop
                ρ₈ m₈ π₈ := by
            cir_unfold_prog (sortSegLoop, vecMergeSortProg, (G + 1), hcond, heval_ok)
          rw [hloop]
          exact ih _ _ _ _ _ _ _ _ _ _ _ _ hinv₈ hn₈ hlent₈ hlena₈
            hlen62₈ htmp_ge₈ hw1 hw_lt hF' hfwd'
    · have hguard : memEvalExpr (.ult (.var "lo") (.var "n")) ρ m π =
          evalExpr (.ult (.var "lo") (.var "n")) ρ :=
        memEvalExpr_ult_agree _ _ _ _ _
          (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _)
      have hcond : memEvalExpr (.ult (.var "lo") (.var "n")) ρ m π =
          .ok (.b false) := by
        rw [hguard]
        have h := sortSegGuardLo_eval ρ la lt n w lo mid₀ hi₀ t₀ hinv
        rwa [decide_eq_false hLo] at h
      have hfwd0 : sortSegFwd la lt (F + 1) w.toNat lo.toNat
          n.toNat = .ok (la, lt) := by
        simp only [sortSegFwd, dite_eq_right hLo]
      rw [hfwd0] at hfwd
      cases hfwd

/-- Outer-body step on memory: `lo ← 0`, run the segments, double
    `width`; pins thread through (assigns touch env only). -/
theorem memSortOuterBody_step (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (n w lo₀ mid₀ hi₀ t₀ : BitVec 64)
    (la₁ lt₁ : List (BitVec 32))
    (aa ab : Addr) (ta tb : Nat) (nA nB : BitVec 32)
    (hinv : SortInv ρ la lt n w lo₀ mid₀ hi₀ t₀)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_tmp : layoutLookup π "tmp" = some (ab, tb))
    (hmem_a : memFind m aa = some ⟨ta, true, nA :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nB :: lt⟩)
    (hnB : nB = BitVec.ofNat 32 lt.length)
    (hn : n.toNat = la.length)
    (hlent : lt.length < 2 ^ 64) (hlena : la.length < 2 ^ 64)
    (hlen62 : la.length < 2 ^ 62)
    (htmp_ge : la.length ≤ lt.length)
    (hw1 : 1 ≤ w.toNat) (hw_lt : w.toNat < n.toNat)
    (hF : 2 * n.toNat + 9 ≤ F)
    (hseg : sortSegFwd la lt F w.toNat 0 n.toNat = .ok (la₁, lt₁)) :
    ∃ ρ' m' π' w' lo' mid' hi' t' aa' ab' ta' tb' nA' nB',
      memEvalProgStmt vecMergeSortProg F VecMergeSort.sortOuterBody ρ m π =
        .ok ((ρ', m', π'), .fellThrough) ∧
      SortInv ρ' la₁ lt₁ n w' lo' mid' hi' t' ∧
      w'.toNat = w.toNat + w.toNat ∧
      layoutLookup π' "a" = some (aa', ta') ∧
      layoutLookup π' "tmp" = some (ab', tb') ∧
      memFind m' aa' = some ⟨ta', true, nA' :: la₁⟩ ∧
      memFind m' ab' = some ⟨tb', true, nB' :: lt₁⟩ ∧
      nB' = BitVec.ofNat 32 lt₁.length := by
  obtain ⟨ha, htmp, hnL, hw, hlo₀, hmid₀, hhi₀, htt₀⟩ := hinv
  -- `lo ← 0`.
  have heval_z : evalExpr (.lit (.u64 (BitVec.ofNat 64 0))) ρ =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  have hmem_z : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0))) ρ m π =
      .ok (.u64 (BitVec.ofNat 64 0)) :=
    (memEvalExpr_lit _ _ _ _).trans heval_z
  obtain ⟨ρ_a, hu_a⟩ := envUpdate_some_of_lookup ρ "lo"
    (.u64 lo₀) (.u64 (BitVec.ofNat 64 0)) hlo₀
  have hstep_a : memEvalProgStmt vecMergeSortProg F
      (.assign "lo" (.lit (.u64 (BitVec.ofNat 64 0)))) ρ m π =
      .ok ((ρ_a, m, π), .fellThrough) :=
    memRevAssign vecMergeSortProg F "lo" _ ρ m π _ ρ_a hmem_z heval_z hu_a
  have hinv_a : SortInv ρ_a la lt n w (BitVec.ofNat 64 0) mid₀ hi₀
      t₀ :=
    sortInv_update_lo _ _ _ _ _ _ _ _ _ _ _
      ⟨ha, htmp, hnL, hw, hlo₀, hmid₀, hhi₀, htt₀⟩ hu_a
  -- Segments from `lo = 0`.
  have hz : (BitVec.ofNat 64 0).toNat = 0 := bv64_toNat_ofNat 0
    (by omega)
  have hF_seg : 2 * (n.toNat - 0) + 9 ≤ F := by omega
  have hseg' : sortSegFwd la lt F w.toNat
      (BitVec.ofNat 64 0).toNat n.toNat = .ok (la₁, lt₁) := by
    rw [hz]; exact hseg
  obtain ⟨ρ_b, m_b, π_b, lo_b, mid_b, hi_b, t_b, aa_b, ab_b, ta_b, tb_b,
      nA_b, nB_b, heval_seg, hinv_b, hlay_a_b, hlay_tmp_b, hmem_a_b,
      hmem_b_b, hnB_b⟩ :=
    memSortSeg_ok F ρ_a m π la lt n w (BitVec.ofNat 64 0) mid₀ hi₀ t₀ la₁
      lt₁ aa ab ta tb nA nB
      hinv_a hlay_a hlay_tmp hmem_a hmem_b hnB hn hlent hlena hlen62
      htmp_ge hw1 hw_lt hF_seg hseg'
  obtain ⟨ha_b, htmp_b, hnL_b, hw_b, hlo_b, hmid_b, hhi_b,
      htt_b⟩ := hinv_b
  -- `width ← width + width`.
  have hw2 : (w + w).toNat = w.toNat + w.toNat :=
    bv64_add_toNat w w (by omega)
  have heval_ww : evalExpr
      (.uadd (.var "width") (.var "width")) ρ_b =
      .ok (.u64 (w + w)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hw_b) (evalExpr_var_hit _ _ _ hw_b)
  have hmem_ww : memEvalExpr
      (.uadd (.var "width") (.var "width")) ρ_b m_b π_b =
      .ok (.u64 (w + w)) :=
    (memEvalExpr_uadd_agree _ _ _ _ _
      (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _)).trans heval_ww
  obtain ⟨ρ_c, hu_c⟩ := envUpdate_some_of_lookup ρ_b "width"
    (.u64 w) (.u64 (w + w)) hw_b
  have hstep_c : memEvalProgStmt vecMergeSortProg F
      (.assign "width" (.uadd (.var "width") (.var "width"))) ρ_b m_b
      π_b =
      .ok ((ρ_c, m_b, π_b), .fellThrough) :=
    memRevAssign vecMergeSortProg F "width" _ ρ_b m_b π_b _ ρ_c hmem_ww
      heval_ww hu_c
  have hinv_c : SortInv ρ_c la₁ lt₁ n (w + w) lo_b mid_b hi_b t_b :=
    sortInv_update_width _ _ _ _ _ _ _ _ _ _ _
      ⟨ha_b, htmp_b, hnL_b, hw_b, hlo_b, hmid_b, hhi_b, htt_b⟩ hu_c
  -- Assemble.
  have hbody : VecMergeSort.sortOuterBody =
      (.seq (.assign "lo" (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq sortSegLoop
          (.assign "width"
            (.uadd (.var "width") (.var "width"))))) := rfl
  refine ⟨ρ_c, m_b, π_b, (w + w), lo_b, mid_b, hi_b, t_b, aa_b, ab_b, ta_b,
    tb_b, nA_b, nB_b, ?_, hinv_c, hw2, hlay_a_b, hlay_tmp_b, hmem_a_b,
    hmem_b_b, hnB_b⟩
  rw [hbody,
    memEvalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _ _ _ _ _
      hstep_a,
    memEvalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _ _ _ _ _
      heval_seg]
  exact hstep_c

/-- Outer-body err on memory: `lo ← 0`, then the segments fail. -/
theorem memSortOuterBody_err (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (n w lo₀ mid₀ hi₀ t₀ : BitVec 64)
    (e : Panic)
    (hinv : SortInv ρ la lt n w lo₀ mid₀ hi₀ t₀)
    (hn : n.toNat = la.length)
    (hlent : lt.length < 2 ^ 64) (hlena : la.length < 2 ^ 64)
    (hlen62 : la.length < 2 ^ 62)
    (htmp_ge : la.length ≤ lt.length)
    (hw1 : 1 ≤ w.toNat) (hw_lt : w.toNat < n.toNat)
    (hF : 2 * n.toNat + 9 ≤ F)
    (hseg : sortSegFwd la lt F w.toNat 0 n.toNat = .error e) :
    memEvalProgStmt vecMergeSortProg F VecMergeSort.sortOuterBody ρ m π = .error e := by
  obtain ⟨ha, htmp, hnL, hw, hlo₀, hmid₀, hhi₀, htt₀⟩ := hinv
  have heval_z : evalExpr (.lit (.u64 (BitVec.ofNat 64 0))) ρ =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  have hmem_z : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0))) ρ m π =
      .ok (.u64 (BitVec.ofNat 64 0)) :=
    (memEvalExpr_lit _ _ _ _).trans heval_z
  obtain ⟨ρ_a, hu_a⟩ := envUpdate_some_of_lookup ρ "lo"
    (.u64 lo₀) (.u64 (BitVec.ofNat 64 0)) hlo₀
  have hstep_a : memEvalProgStmt vecMergeSortProg F
      (.assign "lo" (.lit (.u64 (BitVec.ofNat 64 0)))) ρ m π =
      .ok ((ρ_a, m, π), .fellThrough) :=
    memRevAssign vecMergeSortProg F "lo" _ ρ m π _ ρ_a hmem_z heval_z hu_a
  have hinv_a : SortInv ρ_a la lt n w (BitVec.ofNat 64 0) mid₀ hi₀
      t₀ :=
    sortInv_update_lo _ _ _ _ _ _ _ _ _ _ _
      ⟨ha, htmp, hnL, hw, hlo₀, hmid₀, hhi₀, htt₀⟩ hu_a
  have hz : (BitVec.ofNat 64 0).toNat = 0 := bv64_toNat_ofNat 0
    (by omega)
  have hF_seg : 2 * (n.toNat - 0) + 9 ≤ F := by omega
  have hseg' : sortSegFwd la lt F w.toNat
      (BitVec.ofNat 64 0).toNat n.toNat = .error e := by
    rw [hz]; exact hseg
  have heval_seg : memEvalProgStmt vecMergeSortProg F sortSegLoop ρ_a m
      π = .error e :=
    memSortSeg_err F ρ_a m π la lt n w (BitVec.ofNat 64 0) mid₀ hi₀ t₀ e
      hinv_a hn hlent hlena hlen62 htmp_ge hw1 hw_lt hF_seg hseg'
  have hbody : VecMergeSort.sortOuterBody =
      (.seq (.assign "lo" (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq sortSegLoop
          (.assign "width"
            (.uadd (.var "width") (.var "width"))))) := rfl
  rw [hbody,
    memEvalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _ _ _ _ _
      hstep_a]
  exact memEvalProgStmt_seq_err vecMergeSortProg F _ _ _ _ _ _
    heval_seg

/-- Outer-loop ok soundness on memory. -/
theorem memSortOuter_ok (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (n w lo₀ mid₀ hi₀ t₀ : BitVec 64)
    (la' lt' : List (BitVec 32))
    (aa ab : Addr) (ta tb : Nat) (nA nB : BitVec 32)
    (hinv : SortInv ρ la lt n w lo₀ mid₀ hi₀ t₀)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_tmp : layoutLookup π "tmp" = some (ab, tb))
    (hmem_a : memFind m aa = some ⟨ta, true, nA :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nB :: lt⟩)
    (hnB : nB = BitVec.ofNat 32 lt.length)
    (hn : n.toNat = la.length)
    (hlent : lt.length < 2 ^ 64) (hlena : la.length < 2 ^ 64)
    (hlen62 : la.length < 2 ^ 62)
    (htmp_ge : la.length ≤ lt.length)
    (hw1 : 1 ≤ w.toNat)
    (hF : 2 * (n.toNat - w.toNat) + 2 * n.toNat + 10 ≤ F)
    (hfwd : sortOuterFwd la lt F w.toNat n.toNat = .ok (la', lt')) :
    ∃ ρ' m' π' w' lo' mid' hi' t' aa' ab' ta' tb' nA' nB',
      memEvalProgStmt vecMergeSortProg F VecMergeSort.sortOuterLoop ρ m
        π = .ok ((ρ', m', π'), .fellThrough) ∧
      SortInv ρ' la' lt' n w' lo' mid' hi' t' ∧
      layoutLookup π' "a" = some (aa', ta') ∧
      layoutLookup π' "tmp" = some (ab', tb') ∧
      memFind m' aa' = some ⟨ta', true, nA' :: la'⟩ ∧
      memFind m' ab' = some ⟨tb', true, nB' :: lt'⟩ ∧
      nB' = BitVec.ofNat 32 lt'.length := by
  induction F generalizing ρ m π la lt n w lo₀ mid₀ hi₀ t₀ la' lt'
      aa ab ta tb nA nB with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hW : w.toNat < n.toNat
    · have hguard : memEvalExpr (.ult (.var "width") (.var "n")) ρ m π =
          evalExpr (.ult (.var "width") (.var "n")) ρ :=
        memEvalExpr_ult_agree _ _ _ _ _
          (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _)
      have hcond : memEvalExpr (.ult (.var "width") (.var "n")) ρ m π =
          .ok (.b true) := by
        rw [hguard]
        have h := sortOuterGuardW_eval ρ la lt n w lo₀ mid₀ hi₀ t₀
          hinv
        rwa [decide_eq_true hW] at h
      simp only [sortOuterFwd, dite_eq_left hW] at hfwd
      match hseg : sortSegFwd la lt F w.toNat 0 n.toNat with
      | .error e => simp [hseg] at hfwd
      | .ok (la₁, lt₁) =>
        simp only [hseg] at hfwd
        obtain ⟨ρ₁, m₁, π₁, w₁, lo₁, mid₁, hi₁, t₁, aa₁, ab₁, ta₁, tb₁,
            nA₁, nB₁, heval_body, hinv₁, hw₁eq, hlay_a₁, hlay_tmp₁,
            hmem_a₁, hmem_b₁, hnB₁⟩ :=
          memSortOuterBody_step F ρ m π la lt n w lo₀ mid₀ hi₀ t₀ la₁ lt₁
            aa ab ta tb nA nB
            hinv hlay_a hlay_tmp hmem_a hmem_b hnB hn hlent hlena hlen62
            htmp_ge hw1 hW (by omega) hseg
        have hloop : memEvalProgStmt vecMergeSortProg (F + 1)
            VecMergeSort.sortOuterLoop ρ m π =
            memEvalProgStmt vecMergeSortProg F
              VecMergeSort.sortOuterLoop ρ₁ m₁ π₁ := by
          cir_unfold_prog (VecMergeSort.sortOuterLoop, vecMergeSortProg, F, hcond, heval_body)
        have hw1' : 1 ≤ w₁.toNat := by omega
        have hF' : 2 * (n.toNat - w₁.toNat) + 2 * n.toNat + 10 ≤
            F := by
          omega
        have hfwd' : sortOuterFwd la₁ lt₁ F w₁.toNat n.toNat =
            .ok (la', lt') := by
          rw [hw₁eq]; exact hfwd
        rw [hloop]
        have hlen_la : la₁.length = la.length :=
          sortSegFwd_length_la la lt F w.toNat 0 n.toNat la₁ lt₁ hseg
        have hlen_lt : lt₁.length = lt.length :=
          sortSegFwd_length_lt la lt F w.toNat 0 n.toNat la₁ lt₁
            hn htmp_ge hseg
        have hn₁ : n.toNat = la₁.length := by
          rw [hlen_la]; exact hn
        have hlent₁ : lt₁.length < 2 ^ 64 := by
          rw [hlen_lt]; exact hlent
        have hlena₁ : la₁.length < 2 ^ 64 := by
          rw [hlen_la]; exact hlena
        have hlen62₁ : la₁.length < 2 ^ 62 := by
          rw [hlen_la]; exact hlen62
        have htmp_ge₁ : la₁.length ≤ lt₁.length := by
          rw [hlen_la, hlen_lt]; exact htmp_ge
        obtain ⟨ρ', m', π', w', lo', mid', hi', t', aa', ab', ta', tb',
            nA', nB', hev, hinv', hlay_a', hlay_tmp', hmem_a', hmem_b',
            hnB'⟩ :=
          ih _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinv₁ hlay_a₁
            hlay_tmp₁ hmem_a₁ hmem_b₁ hnB₁ hn₁ hlent₁ hlena₁ hlen62₁
            htmp_ge₁ hw1' hF' hfwd'
        exact ⟨ρ', m', π', w', lo', mid', hi', t', aa', ab', ta', tb', nA',
          nB', hev, hinv', hlay_a', hlay_tmp', hmem_a', hmem_b', hnB'⟩
    · have hguard : memEvalExpr (.ult (.var "width") (.var "n")) ρ m π =
          evalExpr (.ult (.var "width") (.var "n")) ρ :=
        memEvalExpr_ult_agree _ _ _ _ _
          (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _)
      have hcond : memEvalExpr (.ult (.var "width") (.var "n")) ρ m π =
          .ok (.b false) := by
        rw [hguard]
        have h := sortOuterGuardW_eval ρ la lt n w lo₀ mid₀ hi₀ t₀
          hinv
        rwa [decide_eq_false hW] at h
      have hfwd0 : sortOuterFwd la lt (F + 1) w.toNat n.toNat =
          .ok (la, lt) := by
        simp only [sortOuterFwd, dite_eq_right hW]
      rw [hfwd0] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl⟩ := hfwd
      have hexit : memEvalProgStmt vecMergeSortProg (F + 1)
          VecMergeSort.sortOuterLoop ρ m π =
          .ok ((ρ, m, π), .fellThrough) :=
        memEvalProgStmt_while_false vecMergeSortProg _ _ _ _ _ _ hcond
      exact ⟨ρ, m, π, w, lo₀, mid₀, hi₀, t₀, aa, ab, ta, tb, nA, nB, hexit,
        hinv, hlay_a, hlay_tmp, hmem_a, hmem_b, hnB⟩

/-- Outer-loop error soundness on memory. -/
theorem memSortOuter_err (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (n w lo₀ mid₀ hi₀ t₀ : BitVec 64)
    (e : Panic)
    (aa ab : Addr) (ta tb : Nat) (nA nB : BitVec 32)
    (hinv : SortInv ρ la lt n w lo₀ mid₀ hi₀ t₀)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_tmp : layoutLookup π "tmp" = some (ab, tb))
    (hmem_a : memFind m aa = some ⟨ta, true, nA :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nB :: lt⟩)
    (hnB : nB = BitVec.ofNat 32 lt.length)
    (hn : n.toNat = la.length)
    (hlent : lt.length < 2 ^ 64) (hlena : la.length < 2 ^ 64)
    (hlen62 : la.length < 2 ^ 62)
    (htmp_ge : la.length ≤ lt.length)
    (hw1 : 1 ≤ w.toNat)
    (hF : 2 * (n.toNat - w.toNat) + 2 * n.toNat + 10 ≤ F)
    (hfwd : sortOuterFwd la lt F w.toNat n.toNat = .error e) :
    memEvalProgStmt vecMergeSortProg F VecMergeSort.sortOuterLoop ρ m
      π = .error e := by
  induction F generalizing ρ m π la lt n w lo₀ mid₀ hi₀ t₀ e
      aa ab ta tb nA nB with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hW : w.toNat < n.toNat
    · have hguard : memEvalExpr (.ult (.var "width") (.var "n")) ρ m π =
          evalExpr (.ult (.var "width") (.var "n")) ρ :=
        memEvalExpr_ult_agree _ _ _ _ _
          (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _)
      have hcond : memEvalExpr (.ult (.var "width") (.var "n")) ρ m π =
          .ok (.b true) := by
        rw [hguard]
        have h := sortOuterGuardW_eval ρ la lt n w lo₀ mid₀ hi₀ t₀
          hinv
        rwa [decide_eq_true hW] at h
      simp only [sortOuterFwd, dite_eq_left hW] at hfwd
      match hseg : sortSegFwd la lt F w.toNat 0 n.toNat with
      | .error e' =>
        simp [hseg] at hfwd
        cases hfwd
        have heval_body : memEvalProgStmt vecMergeSortProg F
            VecMergeSort.sortOuterBody ρ m π = .error e :=
          memSortOuterBody_err F ρ m π la lt n w lo₀ mid₀ hi₀ t₀ e
            hinv hn hlent hlena hlen62 htmp_ge hw1 hW (by omega) hseg
        cir_unfold_prog (VecMergeSort.sortOuterLoop, vecMergeSortProg, F, hcond, heval_body)
      | .ok (la₁, lt₁) =>
        simp only [hseg] at hfwd
        obtain ⟨ρ₁, m₁, π₁, w₁, lo₁, mid₁, hi₁, t₁, aa₁, ab₁, ta₁, tb₁,
            nA₁, nB₁, heval_body, hinv₁, hw₁eq, hlay_a₁, hlay_tmp₁,
            hmem_a₁, hmem_b₁, hnB₁⟩ :=
          memSortOuterBody_step F ρ m π la lt n w lo₀ mid₀ hi₀ t₀ la₁ lt₁
            aa ab ta tb nA nB
            hinv hlay_a hlay_tmp hmem_a hmem_b hnB hn hlent hlena hlen62
            htmp_ge hw1 hW (by omega) hseg
        have hloop : memEvalProgStmt vecMergeSortProg (F + 1)
            VecMergeSort.sortOuterLoop ρ m π =
            memEvalProgStmt vecMergeSortProg F
              VecMergeSort.sortOuterLoop ρ₁ m₁ π₁ := by
          cir_unfold_prog (VecMergeSort.sortOuterLoop, vecMergeSortProg, F, hcond, heval_body)
        have hw1' : 1 ≤ w₁.toNat := by omega
        have hF' : 2 * (n.toNat - w₁.toNat) + 2 * n.toNat + 10 ≤
            F := by
          omega
        have hfwd' : sortOuterFwd la₁ lt₁ F w₁.toNat n.toNat =
            .error e := by
          rw [hw₁eq]; exact hfwd
        rw [hloop]
        have hlen_la : la₁.length = la.length :=
          sortSegFwd_length_la la lt F w.toNat 0 n.toNat la₁ lt₁ hseg
        have hlen_lt : lt₁.length = lt.length :=
          sortSegFwd_length_lt la lt F w.toNat 0 n.toNat la₁ lt₁
            hn htmp_ge hseg
        have hn₁ : n.toNat = la₁.length := by
          rw [hlen_la]; exact hn
        have hlent₁ : lt₁.length < 2 ^ 64 := by
          rw [hlen_lt]; exact hlent
        have hlena₁ : la₁.length < 2 ^ 64 := by
          rw [hlen_la]; exact hlena
        have hlen62₁ : la₁.length < 2 ^ 62 := by
          rw [hlen_la]; exact hlen62
        have htmp_ge₁ : la₁.length ≤ lt₁.length := by
          rw [hlen_la, hlen_lt]; exact htmp_ge
        exact ih _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hinv₁ hlay_a₁
          hlay_tmp₁ hmem_a₁ hmem_b₁ hnB₁ hn₁ hlent₁ hlena₁ hlen62₁
          htmp_ge₁ hw1' hF' hfwd'
    · have hguard : memEvalExpr (.ult (.var "width") (.var "n")) ρ m π =
          evalExpr (.ult (.var "width") (.var "n")) ρ :=
        memEvalExpr_ult_agree _ _ _ _ _
          (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _)
      have hcond : memEvalExpr (.ult (.var "width") (.var "n")) ρ m π =
          .ok (.b false) := by
        rw [hguard]
        have h := sortOuterGuardW_eval ρ la lt n w lo₀ mid₀ hi₀ t₀
          hinv
        rwa [decide_eq_false hW] at h
      have hfwd0 : sortOuterFwd la lt (F + 1) w.toNat n.toNat =
          .ok (la, lt) := by
        simp only [sortOuterFwd, dite_eq_right hW]
      rw [hfwd0] at hfwd
      cases hfwd

/-- Whole-function memory transfer for `vec_merge_sort`: the callee
    binds its snapshots over `emptyMem`, threads them through the
    prelude lets and the outer loop, and (on the ok leg) pins the
    final `a`/`tmp` blocks for the caller. -/
theorem memEvalProgFunc_vecMergeSort (F : Nat)
    (la lt : List (BitVec 32))
    (hlena : la.length < 2 ^ 64)
    (hlen62 : la.length < 2 ^ 62)
    (hlent : lt.length < 2 ^ 64)
    (htmp_ge : la.length ≤ lt.length)
    (hF : 2 * (la.length - 1) + 2 * la.length + 10 ≤ F) :
    ∃ m' π', (memEvalProgFuncOn vecMergeSortProg F vecMergeSortFunc
      [.stdVecVal la, .stdVecVal lt] emptyMem =
      match vecMergeSortFwd la lt F with
      | .error e => .error e
      | .ok (.stdVecVal la') => .ok ((.stdVecVal la'), m', π')
      | .ok _ => .error .AssertFail)
      ∧ (match vecMergeSortFwd la lt F with
      | .ok (.stdVecVal la') =>
        ∃ aa ab ta tb nA nB lt',
          layoutLookup π' "a" = some (aa, ta) ∧
          layoutLookup π' "tmp" = some (ab, tb) ∧
          memFind m' aa = some ⟨ta, true, nA :: la'⟩ ∧
          memFind m' ab = some ⟨tb, true, nB :: lt'⟩ ∧
          nB = BitVec.ofNat 32 lt'.length
      | _ => True) := by
  have hn64 : (BitVec.ofNat 64 la.length).toNat = la.length :=
    bv64_toNat_ofNat _ hlena
  have hw64 : (BitVec.ofNat 64 1).toNat = 1 :=
    bv64_toNat_ofNat 1 (by omega)
  have hbind : bindMemArgs vecMergeSortFunc.args
      [.stdVecVal la, .stdVecVal lt] emptyMem =
      some ([("a", .stdVecVal la), ("tmp", .stdVecVal lt)],
        ⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 la.length) :: la⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩,
        [("a", 1, 1), ("tmp", 0, 0)]) :=
    bindMemArgs_vecMergeSort la lt
  have hbody : vecMergeSortFunc.body =
      (.seq (.let_ "n" (.u 64) (.stdVecLen "a"))
        (.seq (.let_ "width" (.u 64)
            (.lit (.u64 (BitVec.ofNat 64 1))))
          (.seq (.let_ "lo" (.u 64)
              (.lit (.u64 (BitVec.ofNat 64 0))))
            (.seq (.let_ "mid" (.u 64)
                (.lit (.u64 (BitVec.ofNat 64 0))))
              (.seq (.let_ "hi" (.u 64)
                  (.lit (.u64 (BitVec.ofNat 64 0))))
                (.seq (.let_ "t" (.u 64)
                    (.lit (.u64 (BitVec.ofNat 64 0))))
                  (.seq VecMergeSort.sortOuterLoop
                    (.return_ (.var "a"))))))))) := rfl
  have hmem_a0 : memFind
      ⟨2, [(1, ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩ 1 =
      some ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩ :=
    memFind_cons_hit _ _ _ _ _
  have hmem_b0 : memFind
      ⟨2, [(1, ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩ 0 =
      some ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩ := by
    rw [memFind_cons_miss _ _ _ _ _ _ (by decide : (0 : Addr) ≠ 1)]
    exact memFind_cons_hit _ _ _ _ _
  have hlay_a0 : layoutLookup [("a", 1, 1), ("tmp", 0, 0)] "a" =
      some (1, 1) := by
    simp [layoutLookup]
  have hlay_tmp0 : layoutLookup [("a", 1, 1), ("tmp", 0, 0)] "tmp" =
      some (0, 0) := by
    simp [layoutLookup]
  have hnB0 : BitVec.ofNat 32 lt.length =
      BitVec.ofNat 32 lt.length := rfl
  -- Prelude lets (memory and layout thread through untouched).
  have hlen_n : evalExpr (.stdVecLen "a")
      [("a", .stdVecVal la), ("tmp", .stdVecVal lt)] =
      .ok (.u64 (BitVec.ofNat 64 la.length)) :=
    evalExpr_stdVecLen_some "a" _ la rfl
  have hmemLen : memLoad
      ⟨2, [(1, ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩)],
        []⟩ 1 1 0 = .ok (BitVec.ofNat 32 la.length) := by
    simp [memLoad, hmem_a0]
  have hlenAg : memEvalExpr (.stdVecLen "a")
      [("a", .stdVecVal la), ("tmp", .stdVecVal lt)]
      ⟨2, [(1, ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩
      [("a", 1, 1), ("tmp", 0, 0)] =
      evalExpr (.stdVecLen "a")
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt)] :=
    memEvalExpr_stdVecLen_hit "a" _ _ _ la 1 1
      (by simp [layoutLookup]) rfl hmemLen
  have hlet_n := memRevLet vecMergeSortProg F "n" (.u 64) (.stdVecLen "a")
    [("a", .stdVecVal la), ("tmp", .stdVecVal lt)]
    ⟨2, [(1, ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩),
      (0, ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩
    [("a", 1, 1), ("tmp", 0, 0)] (.u64 (BitVec.ofNat 64 la.length))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h)
    hlenAg hlen_n
  have hone : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      ([("n", .u64 (BitVec.ofNat 64 la.length)),
        ("a", .stdVecVal la), ("tmp", .stdVecVal lt)]) =
      .ok (.u64 (BitVec.ofNat 64 1)) :=
    evalExpr_lit _ _
  have honeAg : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      ([("n", .u64 (BitVec.ofNat 64 la.length)),
        ("a", .stdVecVal la), ("tmp", .stdVecVal lt)])
      ⟨2, [(1, ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩
      [("a", 1, 1), ("tmp", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        ([("n", .u64 (BitVec.ofNat 64 la.length)),
          ("a", .stdVecVal la), ("tmp", .stdVecVal lt)]) :=
    memEvalExpr_lit _ _ _ _
  have hlet_width := memRevLet vecMergeSortProg F "width" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 1)))
    (envExtend [("a", .stdVecVal la), ("tmp", .stdVecVal lt)] "n" (.u64 (BitVec.ofNat 64 la.length)))
    ⟨2, [(1, ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩),
      (0, ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩
    [("a", 1, 1), ("tmp", 0, 0)] (.u64 (BitVec.ofNat 64 1))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h)
    honeAg hone
  have hzero_e : ∀ (ρ : Env),
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0))) ρ =
        .ok (.u64 (BitVec.ofNat 64 0)) :=
    fun ρ => evalExpr_lit _ _
  have hzeroAg : ∀ (ρ : Env),
      memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0))) ρ
        ⟨2, [(1, ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩
        [("a", 1, 1), ("tmp", 0, 0)] =
        evalExpr (.lit (.u64 (BitVec.ofNat 64 0))) ρ :=
    fun ρ => memEvalExpr_lit _ _ _ _
  have hlet_lo := memRevLet vecMergeSortProg F "lo" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (envExtend (envExtend [("a", .stdVecVal la), ("tmp", .stdVecVal lt)] "n" (.u64 (BitVec.ofNat 64 la.length))) "width" (.u64 (BitVec.ofNat 64 1)))
    ⟨2, [(1, ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩),
      (0, ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩
    [("a", 1, 1), ("tmp", 0, 0)] (.u64 (BitVec.ofNat 64 0))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h)
    (hzeroAg _) (hzero_e _)
  have hlet_mid := memRevLet vecMergeSortProg F "mid" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (envExtend (envExtend (envExtend [("a", .stdVecVal la), ("tmp", .stdVecVal lt)] "n" (.u64 (BitVec.ofNat 64 la.length))) "width" (.u64 (BitVec.ofNat 64 1))) "lo" (.u64 (BitVec.ofNat 64 0)))
    ⟨2, [(1, ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩),
      (0, ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩
    [("a", 1, 1), ("tmp", 0, 0)] (.u64 (BitVec.ofNat 64 0))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h)
    (hzeroAg _) (hzero_e _)
  have hlet_hi := memRevLet vecMergeSortProg F "hi" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (envExtend (envExtend (envExtend (envExtend [("a", .stdVecVal la), ("tmp", .stdVecVal lt)] "n" (.u64 (BitVec.ofNat 64 la.length))) "width" (.u64 (BitVec.ofNat 64 1))) "lo" (.u64 (BitVec.ofNat 64 0))) "mid" (.u64 (BitVec.ofNat 64 0)))
    ⟨2, [(1, ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩),
      (0, ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩
    [("a", 1, 1), ("tmp", 0, 0)] (.u64 (BitVec.ofNat 64 0))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h)
    (hzeroAg _) (hzero_e _)
  have hlet_t := memRevLet vecMergeSortProg F "t" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .stdVecVal la), ("tmp", .stdVecVal lt)] "n" (.u64 (BitVec.ofNat 64 la.length))) "width" (.u64 (BitVec.ofNat 64 1))) "lo" (.u64 (BitVec.ofNat 64 0))) "mid" (.u64 (BitVec.ofNat 64 0))) "hi" (.u64 (BitVec.ofNat 64 0)))
    ⟨2, [(1, ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩),
      (0, ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩
    [("a", 1, 1), ("tmp", 0, 0)] (.u64 (BitVec.ofNat 64 0))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h)
    (hzeroAg _) (hzero_e _)
  have henv : (envExtend (envExtend (envExtend (envExtend (envExtend
      (envExtend [("a", .stdVecVal la), ("tmp", .stdVecVal lt)]
        "n" (.u64 (BitVec.ofNat 64 la.length)))
        "width" (.u64 (BitVec.ofNat 64 1)))
        "lo" (.u64 (BitVec.ofNat 64 0)))
        "mid" (.u64 (BitVec.ofNat 64 0)))
        "hi" (.u64 (BitVec.ofNat 64 0)))
        "t" (.u64 (BitVec.ofNat 64 0))) =
      mkSortEnv la lt (BitVec.ofNat 64 la.length)
        (BitVec.ofNat 64 1) (BitVec.ofNat 64 0)
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
        (BitVec.ofNat 64 0) := rfl
  have hinv : SortInv
      (mkSortEnv la lt (BitVec.ofNat 64 la.length)
        (BitVec.ofNat 64 1) (BitVec.ofNat 64 0)
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
        (BitVec.ofNat 64 0))
      la lt (BitVec.ofNat 64 la.length) (BitVec.ofNat 64 1)
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) :=
    mkSortEnv_inv _ _ _ _ _ _ _ _
  have hw1 : 1 ≤ (BitVec.ofNat 64 1).toNat := by simp [hw64]
  have hF' : 2 * ((BitVec.ofNat 64 la.length).toNat -
      (BitVec.ofNat 64 1).toNat) +
      2 * (BitVec.ofNat 64 la.length).toNat + 10 ≤ F := by
    rw [hn64, hw64]; exact hF
  match houter : sortOuterFwd la lt F 1 la.length with
  | .error e =>
    have houter' : sortOuterFwd la lt F
        (BitVec.ofNat 64 1).toNat
        (BitVec.ofNat 64 la.length).toNat = .error e := by
      rw [hw64, hn64]; exact houter
    have hO := memSortOuter_err F
      (mkSortEnv la lt (BitVec.ofNat 64 la.length)
        (BitVec.ofNat 64 1) (BitVec.ofNat 64 0)
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
        (BitVec.ofNat 64 0))
      ⟨2, [(1, ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩
      [("a", 1, 1), ("tmp", 0, 0)]
      la lt (BitVec.ofNat 64 la.length) (BitVec.ofNat 64 1)
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) e
      1 0 1 0 (BitVec.ofNat 32 la.length) (BitVec.ofNat 32 lt.length)
      hinv hlay_a0 hlay_tmp0 hmem_a0 hmem_b0 hnB0
      hn64 hlent hlena hlen62 htmp_ge hw1 hF' houter'
    have hfwd : vecMergeSortFwd la lt F = .error e := by
      simp [vecMergeSortFwd, houter]
    have hstmt : memEvalProgStmt vecMergeSortProg F
        vecMergeSortFunc.body
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt)]
        ⟨2, [(1, ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩
        [("a", 1, 1), ("tmp", 0, 0)] =
        .error e := by
      rw [hbody,
        memEvalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _ _ _ _ _
          hlet_n,
        memEvalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _ _ _ _ _
          hlet_width,
        memEvalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _ _ _ _ _
          hlet_lo,
        memEvalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _ _ _ _ _
          hlet_mid,
        memEvalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _ _ _ _ _
          hlet_hi,
        memEvalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _ _ _ _ _
          hlet_t, henv,
        memEvalProgStmt_seq_err vecMergeSortProg F _ _ _ _ _ _ hO]
    exact ⟨⟨2, [(1, ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩,
      [("a", 1, 1), ("tmp", 0, 0)],
      by simp [hfwd, memEvalProgFuncOn, hbind, hstmt],
      by simp [hfwd]⟩
  | .ok (la', lt') =>
    have houter' : sortOuterFwd la lt F
        (BitVec.ofNat 64 1).toNat
        (BitVec.ofNat 64 la.length).toNat = .ok (la', lt') := by
      rw [hw64, hn64]; exact houter
    obtain ⟨ρ', m', π', w', lo', mid', hi', t', aa', ab', ta', tb', nA',
        nB', heval_O, hinv', hlay_a', hlay_tmp', hmem_a', hmem_b',
        hnB'⟩ :=
      memSortOuter_ok F
        (mkSortEnv la lt (BitVec.ofNat 64 la.length)
          (BitVec.ofNat 64 1) (BitVec.ofNat 64 0)
          (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
          (BitVec.ofNat 64 0))
        ⟨2, [(1, ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩
        [("a", 1, 1), ("tmp", 0, 0)]
        la lt (BitVec.ofNat 64 la.length) (BitVec.ofNat 64 1)
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) la' lt'
        1 0 1 0 (BitVec.ofNat 32 la.length) (BitVec.ofNat 32 lt.length)
        hinv hlay_a0 hlay_tmp0 hmem_a0 hmem_b0 hnB0
        hn64 hlent hlena hlen62 htmp_ge hw1 hF' houter'
    obtain ⟨ha', htmp', hn', hw', hlo', hmid', hhi', htt'⟩ := hinv'
    have hmem_ret : memEvalExpr (.var "a") ρ' m' π' =
        .ok (.stdVecVal la') :=
      (memEvalExpr_var _ _ _ _).trans
        (evalExpr_var_hit _ _ _ ha')
    have hret : memEvalProgStmt vecMergeSortProg F (.return_ (.var "a"))
        ρ' m' π' =
        .ok ((ρ', m', π'), .returned (.stdVecVal la')) :=
      memEvalProgStmt_return vecMergeSortProg F _ _ _ _ _ hmem_ret
    have hfwd : vecMergeSortFwd la lt F = .ok (.stdVecVal la') := by
      simp [vecMergeSortFwd, houter]
    have hstmt : memEvalProgStmt vecMergeSortProg F
        vecMergeSortFunc.body
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt)]
        ⟨2, [(1, ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩
        [("a", 1, 1), ("tmp", 0, 0)] =
        .ok ((ρ', m', π'), .returned (.stdVecVal la')) := by
      rw [hbody,
        memEvalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _ _ _ _ _
          hlet_n,
        memEvalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _ _ _ _ _
          hlet_width,
        memEvalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _ _ _ _ _
          hlet_lo,
        memEvalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _ _ _ _ _
          hlet_mid,
        memEvalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _ _ _ _ _
          hlet_hi,
        memEvalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _ _ _ _ _
          hlet_t, henv,
        memEvalProgStmt_seq_fallthrough vecMergeSortProg F _ _ _ _ _ _ _ _
          heval_O]
      exact hret
    exact ⟨m', π',
      by simp [hfwd, memEvalProgFuncOn, hbind, hstmt],
      by simp only [hfwd]; exact ⟨aa', ab', ta', tb', nA', nB', lt', hlay_a',
        hlay_tmp', hmem_a', hmem_b', hnB'⟩⟩
