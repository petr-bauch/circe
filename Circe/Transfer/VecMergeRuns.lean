/-
Circe.Transfer.VecMergeRuns — M1b transfer for the `mergeRuns` helper
of `std::vector<int32_t>` merge sort.

Mem-level mirrors of the eval-level body equations in
`Circe.Emit.VecMergeRuns`: inline `stdVecAt` reads go through
`memEvalExpr_stdVecAt_hit` (length-word-skipping loads), the `tmp`
bound guard through `memEvalExpr_stdVecLen_hit` + `ult_ofNat64_len`,
stores through `memRevVecSet`, and increments through `memRevAssign`
(`envLookup_update_miss` threads lookups across the shadowing
updates). Loop inductions and the entry theorem build on these
mirrors next.
-/
import Circe.Transfer.VecReverse
import Circe.Emit.VecMergeRuns
import Circe.Derived

open VecMergeRuns

/-! ## Memory `fail` (the miss-leg abort) -/

/-- Program-level memory `fail` aborts loudly (via the `memEvalStmtFuel`
fallback arm; fuel-split mirrors `evalStmtFuel_fail`). -/
theorem memEvalProgStmt_fail (prog : Prog) (F : Nat) (ρ : Env)
    (m : Mem) (π : Layout) :
    memEvalProgStmt prog F .fail ρ m π = .error .AssertFail := by
  simp only [memEvalProgStmt]
  cases F <;> simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith]

/-! ## Main-body mirrors -/

/-- Main body, take-`i` side, on memory: guard `true`, store, advance. -/
theorem memRunsMainBody_hitI (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (i j k : BitVec 64)
    (x y w : BitVec 32)
    (aa ab : Addr) (ta tb : Nat) (nA nB : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_tmp : layoutLookup π "tmp" = some (ab, tb))
    (hmem_a : memFind m aa = some ⟨ta, true, nA :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nB :: lt⟩)
    (hmemLen : memLoad m ab tb 0 = .ok (BitVec.ofNat 32 lt.length))
    (hi_env : envLookup ρ "i" = some (.u64 i))
    (hj_env : envLookup ρ "j" = some (.u64 j))
    (hk_env : envLookup ρ "k" = some (.u64 k))
    (ha_env : envLookup ρ "a" = some (.stdVecVal la))
    (htmp_env : envLookup ρ "tmp" = some (.stdVecVal lt))
    (hgetI : la[i.toNat]? = some x) (hgetJ : la[j.toNat]? = some y)
    (hltXY : (x.slt y) = true)
    (hltK : k.toNat < lt.length)
    (hlent : lt.length < 2 ^ 64)
    (hgetK : lt[k.toNat]? = some w)
    (m' : Mem)
    (hstore : memStore m ab tb (k.toNat + 1) x = .ok m')
    (ρ' : Env)
    (hu : envUpdate ρ "tmp" (.stdVecVal (lt.set k.toNat x)) = some ρ')
    (ρI ρK : Env)
    (huI : envUpdate ρ' "i" (.u64 (i + 1)) = some ρI)
    (huK : envUpdate ρI "k" (.u64 (k + 1)) = some ρK) :
    memEvalProgStmt prog F mergeRunsMainBody ρ m π =
      .ok ((ρK, m', π), .fellThrough) := by
  have hvarI : memEvalExpr (.var "i") ρ m π = evalExpr (.var "i") ρ :=
    memEvalExpr_var _ _ _ _
  have hevI : evalExpr (.var "i") ρ = .ok (.u64 i) :=
    evalExpr_var_hit _ _ _ hi_env
  have hloadI : memLoad m aa ta (i.toNat + 1) = .ok x :=
    memLoad_cellsAt m aa ta (i.toNat + 1) (nA :: la) x hmem_a
      (by rw [List.getElem?_cons_succ]; exact hgetI)
  have hagI : memEvalExpr (.stdVecAt "a" (.var "i")) ρ m π =
      evalExpr (.stdVecAt "a" (.var "i")) ρ :=
    memEvalExpr_stdVecAt_hit "a" (.var "i") ρ m π la i x aa ta
      hlay_a ha_env hvarI hevI hloadI hgetI
  have hrIe : evalExpr (.stdVecAt "a" (.var "i")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some "a" _ _ _ _ _ ha_env hevI hgetI
  have hrI : memEvalExpr (.stdVecAt "a" (.var "i")) ρ m π =
      .ok (.i32 x) := hagI.trans hrIe
  have hvarJ : memEvalExpr (.var "j") ρ m π = evalExpr (.var "j") ρ :=
    memEvalExpr_var _ _ _ _
  have hevJ : evalExpr (.var "j") ρ = .ok (.u64 j) :=
    evalExpr_var_hit _ _ _ hj_env
  have hloadJ : memLoad m aa ta (j.toNat + 1) = .ok y :=
    memLoad_cellsAt m aa ta (j.toNat + 1) (nA :: la) y hmem_a
      (by rw [List.getElem?_cons_succ]; exact hgetJ)
  have hagJ : memEvalExpr (.stdVecAt "a" (.var "j")) ρ m π =
      evalExpr (.stdVecAt "a" (.var "j")) ρ :=
    memEvalExpr_stdVecAt_hit "a" (.var "j") ρ m π la j y aa ta
      hlay_a ha_env hvarJ hevJ hloadJ hgetJ
  have hrJe : evalExpr (.stdVecAt "a" (.var "j")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some "a" _ _ _ _ _ ha_env hevJ hgetJ
  have hcmpE : evalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "a" (.var "j"))) ρ =
      .ok (.b (x.slt y)) :=
    evalExpr_slt_i32 _ _ _ _ _ hrIe hrJe
  have hcmp : memEvalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "a" (.var "j")))
      ρ m π = .ok (.b true) := by
    have h := (memEvalExpr_slt_agree _ _ _ _ _ hagI hagJ).trans hcmpE
    rwa [hltXY] at h
  have hvarK : memEvalExpr (.var "k") ρ m π = evalExpr (.var "k") ρ :=
    memEvalExpr_var _ _ _ _
  have hevK : evalExpr (.var "k") ρ = .ok (.u64 k) :=
    evalExpr_var_hit _ _ _ hk_env
  have hlenAg : memEvalExpr (.stdVecLen "tmp") ρ m π =
      evalExpr (.stdVecLen "tmp") ρ :=
    memEvalExpr_stdVecLen_hit "tmp" ρ m π lt ab tb
      hlay_tmp htmp_env hmemLen
  have hgKE : evalExpr (.ult (.var "k") (.stdVecLen "tmp")) ρ =
      .ok (.b true) := by
    have hs := evalExpr_stdVecLen_some "tmp" _ lt htmp_env
    have h := evalExpr_ult_u64 _ _ _ _ _ hevK hs
    rwa [ult_ofNat64_len k lt.length hlent, decide_eq_true hltK] at h
  have hgK : memEvalExpr (.ult (.var "k") (.stdVecLen "tmp")) ρ m π =
      .ok (.b true) :=
    (memEvalExpr_ult_agree _ _ _ _ _ hvarK hlenAg).trans hgKE
  have hset := memRevVecSet prog F "tmp" (.var "k")
    (.stdVecAt "a" (.var "i")) ρ m π k x ab tb lt w m' ρ'
    (hvarK.trans hevK) hrI htmp_env hlay_tmp hgetK hstore hu
  have hlookI' : envLookup ρ' "i" = some (.u64 i) := by
    have h := envLookup_update_miss ρ "i" "tmp"
      (.stdVecVal (lt.set k.toNat x)) ρ' (by decide) hu
    rw [h, hi_env]
  have hevI' : evalExpr (.var "i") ρ' = .ok (.u64 i) :=
    evalExpr_var_hit _ _ _ hlookI'
  have hev1 : evalExpr (.lit (.u64 1)) ρ' = .ok (.u64 1) := by
    simp [evalExpr, litVal]
  have hevUI : evalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ' =
      .ok (.u64 (i + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hevI' hev1
  have hmemI : memEvalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ' m' π =
      .ok (.u64 (i + 1)) :=
    (memEvalExpr_uadd_agree _ _ _ _ _
      (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)).trans hevUI
  have hstepI := memRevAssign prog F "i" _ ρ' m' π _ ρI
    hmemI hevUI huI
  have hlookK' : envLookup ρ' "k" = some (.u64 k) := by
    have h := envLookup_update_miss ρ "k" "tmp"
      (.stdVecVal (lt.set k.toNat x)) ρ' (by decide) hu
    rw [h, hk_env]
  have hlookKI : envLookup ρI "k" = some (.u64 k) := by
    have h := envLookup_update_miss ρ' "k" "i" (.u64 (i + 1)) ρI
      (by decide) huI
    rw [h, hlookK']
  have hevK' : evalExpr (.var "k") ρI = .ok (.u64 k) :=
    evalExpr_var_hit _ _ _ hlookKI
  have hev1K : evalExpr (.lit (.u64 1)) ρI = .ok (.u64 1) := by
    simp [evalExpr, litVal]
  have hevUK : evalExpr (.uadd (.var "k") (.lit (.u64 1))) ρI =
      .ok (.u64 (k + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hevK' hev1K
  have hmemK : memEvalExpr (.uadd (.var "k") (.lit (.u64 1))) ρI m' π =
      .ok (.u64 (k + 1)) :=
    (memEvalExpr_uadd_agree _ _ _ _ _
      (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)).trans hevUK
  have hstepK := memRevAssign prog F "k" _ ρI m' π _ ρK
    hmemK hevUK huK
  have hseqIK := memEvalProgStmt_seq prog F _ _ ρ' m' π ρI m' π
    ρK m' π .fellThrough hstepI hstepK
  have hthen : memEvalProgStmt prog F
      (.seq (.if_ (.ult (.var "k") (.stdVecLen "tmp"))
        (.vecSet "tmp" (.var "k") (.stdVecAt "a" (.var "i"))) .fail)
        (.seq (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))
          (.assign "k" (.uadd (.var "k") (.lit (.u64 1)))))) ρ m π =
      .ok ((ρK, m', π), .fellThrough) :=
    memEvalProgStmt_seq prog F _ _ ρ m π ρ' m' π ρK m' π .fellThrough
      ((memEvalProgStmt_if_true prog F _ _ _ _ _ _ hgK).trans hset) hseqIK
  exact (memEvalProgStmt_if_true prog F _ _ _ _ _ _ hcmp).trans hthen

/-- Main body, take-`j` side, on memory: guard `false`, store, advance. -/
theorem memRunsMainBody_hitJ (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (i j k : BitVec 64)
    (x y w : BitVec 32)
    (aa ab : Addr) (ta tb : Nat) (nA nB : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_tmp : layoutLookup π "tmp" = some (ab, tb))
    (hmem_a : memFind m aa = some ⟨ta, true, nA :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nB :: lt⟩)
    (hmemLen : memLoad m ab tb 0 = .ok (BitVec.ofNat 32 lt.length))
    (hi_env : envLookup ρ "i" = some (.u64 i))
    (hj_env : envLookup ρ "j" = some (.u64 j))
    (hk_env : envLookup ρ "k" = some (.u64 k))
    (ha_env : envLookup ρ "a" = some (.stdVecVal la))
    (htmp_env : envLookup ρ "tmp" = some (.stdVecVal lt))
    (hgetI : la[i.toNat]? = some x) (hgetJ : la[j.toNat]? = some y)
    (hltYX : (x.slt y) = false)
    (hltK : k.toNat < lt.length)
    (hlent : lt.length < 2 ^ 64)
    (hgetK : lt[k.toNat]? = some w)
    (m' : Mem)
    (hstore : memStore m ab tb (k.toNat + 1) y = .ok m')
    (ρ' : Env)
    (hu : envUpdate ρ "tmp" (.stdVecVal (lt.set k.toNat y)) = some ρ')
    (ρJ ρK : Env)
    (huJ : envUpdate ρ' "j" (.u64 (j + 1)) = some ρJ)
    (huK : envUpdate ρJ "k" (.u64 (k + 1)) = some ρK) :
    memEvalProgStmt prog F mergeRunsMainBody ρ m π =
      .ok ((ρK, m', π), .fellThrough) := by
  have hvarI : memEvalExpr (.var "i") ρ m π = evalExpr (.var "i") ρ :=
    memEvalExpr_var _ _ _ _
  have hevI : evalExpr (.var "i") ρ = .ok (.u64 i) :=
    evalExpr_var_hit _ _ _ hi_env
  have hloadI : memLoad m aa ta (i.toNat + 1) = .ok x :=
    memLoad_cellsAt m aa ta (i.toNat + 1) (nA :: la) x hmem_a
      (by rw [List.getElem?_cons_succ]; exact hgetI)
  have hagI : memEvalExpr (.stdVecAt "a" (.var "i")) ρ m π =
      evalExpr (.stdVecAt "a" (.var "i")) ρ :=
    memEvalExpr_stdVecAt_hit "a" (.var "i") ρ m π la i x aa ta
      hlay_a ha_env hvarI hevI hloadI hgetI
  have hrIe : evalExpr (.stdVecAt "a" (.var "i")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some "a" _ _ _ _ _ ha_env hevI hgetI
  have hvarJ : memEvalExpr (.var "j") ρ m π = evalExpr (.var "j") ρ :=
    memEvalExpr_var _ _ _ _
  have hevJ : evalExpr (.var "j") ρ = .ok (.u64 j) :=
    evalExpr_var_hit _ _ _ hj_env
  have hloadJ : memLoad m aa ta (j.toNat + 1) = .ok y :=
    memLoad_cellsAt m aa ta (j.toNat + 1) (nA :: la) y hmem_a
      (by rw [List.getElem?_cons_succ]; exact hgetJ)
  have hagJ : memEvalExpr (.stdVecAt "a" (.var "j")) ρ m π =
      evalExpr (.stdVecAt "a" (.var "j")) ρ :=
    memEvalExpr_stdVecAt_hit "a" (.var "j") ρ m π la j y aa ta
      hlay_a ha_env hvarJ hevJ hloadJ hgetJ
  have hrJe : evalExpr (.stdVecAt "a" (.var "j")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some "a" _ _ _ _ _ ha_env hevJ hgetJ
  have hrJ : memEvalExpr (.stdVecAt "a" (.var "j")) ρ m π =
      .ok (.i32 y) := hagJ.trans hrJe
  have hcmpE : evalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "a" (.var "j"))) ρ =
      .ok (.b (x.slt y)) :=
    evalExpr_slt_i32 _ _ _ _ _ hrIe hrJe
  have hcmp : memEvalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "a" (.var "j")))
      ρ m π = .ok (.b false) := by
    have h := (memEvalExpr_slt_agree _ _ _ _ _ hagI hagJ).trans hcmpE
    rwa [hltYX] at h
  have hvarK : memEvalExpr (.var "k") ρ m π = evalExpr (.var "k") ρ :=
    memEvalExpr_var _ _ _ _
  have hevK : evalExpr (.var "k") ρ = .ok (.u64 k) :=
    evalExpr_var_hit _ _ _ hk_env
  have hlenAg : memEvalExpr (.stdVecLen "tmp") ρ m π =
      evalExpr (.stdVecLen "tmp") ρ :=
    memEvalExpr_stdVecLen_hit "tmp" ρ m π lt ab tb
      hlay_tmp htmp_env hmemLen
  have hgKE : evalExpr (.ult (.var "k") (.stdVecLen "tmp")) ρ =
      .ok (.b true) := by
    have hs := evalExpr_stdVecLen_some "tmp" _ lt htmp_env
    have h := evalExpr_ult_u64 _ _ _ _ _ hevK hs
    rwa [ult_ofNat64_len k lt.length hlent, decide_eq_true hltK] at h
  have hgK : memEvalExpr (.ult (.var "k") (.stdVecLen "tmp")) ρ m π =
      .ok (.b true) :=
    (memEvalExpr_ult_agree _ _ _ _ _ hvarK hlenAg).trans hgKE
  have hset := memRevVecSet prog F "tmp" (.var "k")
    (.stdVecAt "a" (.var "j")) ρ m π k y ab tb lt w m' ρ'
    (hvarK.trans hevK) hrJ htmp_env hlay_tmp hgetK hstore hu
  have hlookJ' : envLookup ρ' "j" = some (.u64 j) := by
    have h := envLookup_update_miss ρ "j" "tmp"
      (.stdVecVal (lt.set k.toNat y)) ρ' (by decide) hu
    rw [h, hj_env]
  have hevJ' : evalExpr (.var "j") ρ' = .ok (.u64 j) :=
    evalExpr_var_hit _ _ _ hlookJ'
  have hev1 : evalExpr (.lit (.u64 1)) ρ' = .ok (.u64 1) := by
    simp [evalExpr, litVal]
  have hevUJ : evalExpr (.uadd (.var "j") (.lit (.u64 1))) ρ' =
      .ok (.u64 (j + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hevJ' hev1
  have hmemJ : memEvalExpr (.uadd (.var "j") (.lit (.u64 1))) ρ' m' π =
      .ok (.u64 (j + 1)) :=
    (memEvalExpr_uadd_agree _ _ _ _ _
      (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)).trans hevUJ
  have hstepJ := memRevAssign prog F "j" _ ρ' m' π _ ρJ
    hmemJ hevUJ huJ
  have hlookK' : envLookup ρ' "k" = some (.u64 k) := by
    have h := envLookup_update_miss ρ "k" "tmp"
      (.stdVecVal (lt.set k.toNat y)) ρ' (by decide) hu
    rw [h, hk_env]
  have hlookKJ : envLookup ρJ "k" = some (.u64 k) := by
    have h := envLookup_update_miss ρ' "k" "j" (.u64 (j + 1)) ρJ
      (by decide) huJ
    rw [h, hlookK']
  have hevK' : evalExpr (.var "k") ρJ = .ok (.u64 k) :=
    evalExpr_var_hit _ _ _ hlookKJ
  have hev1K : evalExpr (.lit (.u64 1)) ρJ = .ok (.u64 1) := by
    simp [evalExpr, litVal]
  have hevUK : evalExpr (.uadd (.var "k") (.lit (.u64 1))) ρJ =
      .ok (.u64 (k + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hevK' hev1K
  have hmemK : memEvalExpr (.uadd (.var "k") (.lit (.u64 1))) ρJ m' π =
      .ok (.u64 (k + 1)) :=
    (memEvalExpr_uadd_agree _ _ _ _ _
      (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)).trans hevUK
  have hstepK := memRevAssign prog F "k" _ ρJ m' π _ ρK
    hmemK hevUK huK
  have hseqJK := memEvalProgStmt_seq prog F _ _ ρ' m' π ρJ m' π
    ρK m' π .fellThrough hstepJ hstepK
  have hels : memEvalProgStmt prog F
      (.seq (.if_ (.ult (.var "k") (.stdVecLen "tmp"))
        (.vecSet "tmp" (.var "k") (.stdVecAt "a" (.var "j"))) .fail)
        (.seq (.assign "j" (.uadd (.var "j") (.lit (.u64 1))))
          (.assign "k" (.uadd (.var "k") (.lit (.u64 1)))))) ρ m π =
      .ok ((ρK, m', π), .fellThrough) :=
    memEvalProgStmt_seq prog F _ _ ρ m π ρ' m' π ρK m' π .fellThrough
      ((memEvalProgStmt_if_true prog F _ _ _ _ _ _ hgK).trans hset) hseqJK
  exact (memEvalProgStmt_if_false prog F _ _ _ _ _ _ hcmp).trans hels

/-- Main body, short-`tmp` miss (take-`i` side): loud abort. -/
theorem memRunsMainBody_missI (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (i j k : BitVec 64)
    (x y : BitVec 32)
    (aa ab : Addr) (ta tb : Nat) (nA nB : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_tmp : layoutLookup π "tmp" = some (ab, tb))
    (hmem_a : memFind m aa = some ⟨ta, true, nA :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nB :: lt⟩)
    (hmemLen : memLoad m ab tb 0 = .ok (BitVec.ofNat 32 lt.length))
    (hi_env : envLookup ρ "i" = some (.u64 i))
    (hj_env : envLookup ρ "j" = some (.u64 j))
    (hk_env : envLookup ρ "k" = some (.u64 k))
    (ha_env : envLookup ρ "a" = some (.stdVecVal la))
    (htmp_env : envLookup ρ "tmp" = some (.stdVecVal lt))
    (hgetI : la[i.toNat]? = some x) (hgetJ : la[j.toNat]? = some y)
    (hltXY : (x.slt y) = true)
    (hltK : ¬ k.toNat < lt.length)
    (hlent : lt.length < 2 ^ 64) :
    memEvalProgStmt prog F mergeRunsMainBody ρ m π =
      .error .AssertFail := by
  have hvarI : memEvalExpr (.var "i") ρ m π = evalExpr (.var "i") ρ :=
    memEvalExpr_var _ _ _ _
  have hevI : evalExpr (.var "i") ρ = .ok (.u64 i) :=
    evalExpr_var_hit _ _ _ hi_env
  have hloadI : memLoad m aa ta (i.toNat + 1) = .ok x :=
    memLoad_cellsAt m aa ta (i.toNat + 1) (nA :: la) x hmem_a
      (by rw [List.getElem?_cons_succ]; exact hgetI)
  have hagI : memEvalExpr (.stdVecAt "a" (.var "i")) ρ m π =
      evalExpr (.stdVecAt "a" (.var "i")) ρ :=
    memEvalExpr_stdVecAt_hit "a" (.var "i") ρ m π la i x aa ta
      hlay_a ha_env hvarI hevI hloadI hgetI
  have hrIe : evalExpr (.stdVecAt "a" (.var "i")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some "a" _ _ _ _ _ ha_env hevI hgetI
  have hvarJ : memEvalExpr (.var "j") ρ m π = evalExpr (.var "j") ρ :=
    memEvalExpr_var _ _ _ _
  have hevJ : evalExpr (.var "j") ρ = .ok (.u64 j) :=
    evalExpr_var_hit _ _ _ hj_env
  have hloadJ : memLoad m aa ta (j.toNat + 1) = .ok y :=
    memLoad_cellsAt m aa ta (j.toNat + 1) (nA :: la) y hmem_a
      (by rw [List.getElem?_cons_succ]; exact hgetJ)
  have hagJ : memEvalExpr (.stdVecAt "a" (.var "j")) ρ m π =
      evalExpr (.stdVecAt "a" (.var "j")) ρ :=
    memEvalExpr_stdVecAt_hit "a" (.var "j") ρ m π la j y aa ta
      hlay_a ha_env hvarJ hevJ hloadJ hgetJ
  have hrJe : evalExpr (.stdVecAt "a" (.var "j")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some "a" _ _ _ _ _ ha_env hevJ hgetJ
  have hcmpE : evalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "a" (.var "j"))) ρ =
      .ok (.b (x.slt y)) :=
    evalExpr_slt_i32 _ _ _ _ _ hrIe hrJe
  have hcmp : memEvalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "a" (.var "j")))
      ρ m π = .ok (.b true) := by
    have h := (memEvalExpr_slt_agree _ _ _ _ _ hagI hagJ).trans hcmpE
    rwa [hltXY] at h
  have hvarK : memEvalExpr (.var "k") ρ m π = evalExpr (.var "k") ρ :=
    memEvalExpr_var _ _ _ _
  have hevK : evalExpr (.var "k") ρ = .ok (.u64 k) :=
    evalExpr_var_hit _ _ _ hk_env
  have hlenAg : memEvalExpr (.stdVecLen "tmp") ρ m π =
      evalExpr (.stdVecLen "tmp") ρ :=
    memEvalExpr_stdVecLen_hit "tmp" ρ m π lt ab tb
      hlay_tmp htmp_env hmemLen
  have hgKE : evalExpr (.ult (.var "k") (.stdVecLen "tmp")) ρ =
      .ok (.b false) := by
    have hs := evalExpr_stdVecLen_some "tmp" _ lt htmp_env
    have h := evalExpr_ult_u64 _ _ _ _ _ hevK hs
    rwa [ult_ofNat64_len k lt.length hlent, decide_eq_false hltK] at h
  have hgK : memEvalExpr (.ult (.var "k") (.stdVecLen "tmp")) ρ m π =
      .ok (.b false) :=
    (memEvalExpr_ult_agree _ _ _ _ _ hvarK hlenAg).trans hgKE
  have herr : memEvalProgStmt prog F
      (.if_ (.ult (.var "k") (.stdVecLen "tmp"))
        (.vecSet "tmp" (.var "k") (.stdVecAt "a" (.var "i"))) .fail)
      ρ m π = .error .AssertFail :=
    (memEvalProgStmt_if_false prog F _ _ _ ρ m π hgK).trans
      (memEvalProgStmt_fail prog F ρ m π)
  unfold mergeRunsMainBody
  rw [memEvalProgStmt_if_true prog F _ _ _ _ _ _ hcmp]
  exact memEvalProgStmt_seq_err prog F _ _ ρ m π .AssertFail herr

/-- Main body, short-`tmp` miss (take-`j` side): loud abort. -/
theorem memRunsMainBody_missJ (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (i j k : BitVec 64)
    (x y : BitVec 32)
    (aa ab : Addr) (ta tb : Nat) (nA nB : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_tmp : layoutLookup π "tmp" = some (ab, tb))
    (hmem_a : memFind m aa = some ⟨ta, true, nA :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nB :: lt⟩)
    (hmemLen : memLoad m ab tb 0 = .ok (BitVec.ofNat 32 lt.length))
    (hi_env : envLookup ρ "i" = some (.u64 i))
    (hj_env : envLookup ρ "j" = some (.u64 j))
    (hk_env : envLookup ρ "k" = some (.u64 k))
    (ha_env : envLookup ρ "a" = some (.stdVecVal la))
    (htmp_env : envLookup ρ "tmp" = some (.stdVecVal lt))
    (hgetI : la[i.toNat]? = some x) (hgetJ : la[j.toNat]? = some y)
    (hltYX : (x.slt y) = false)
    (hltK : ¬ k.toNat < lt.length)
    (hlent : lt.length < 2 ^ 64) :
    memEvalProgStmt prog F mergeRunsMainBody ρ m π =
      .error .AssertFail := by
  have hvarI : memEvalExpr (.var "i") ρ m π = evalExpr (.var "i") ρ :=
    memEvalExpr_var _ _ _ _
  have hevI : evalExpr (.var "i") ρ = .ok (.u64 i) :=
    evalExpr_var_hit _ _ _ hi_env
  have hloadI : memLoad m aa ta (i.toNat + 1) = .ok x :=
    memLoad_cellsAt m aa ta (i.toNat + 1) (nA :: la) x hmem_a
      (by rw [List.getElem?_cons_succ]; exact hgetI)
  have hagI : memEvalExpr (.stdVecAt "a" (.var "i")) ρ m π =
      evalExpr (.stdVecAt "a" (.var "i")) ρ :=
    memEvalExpr_stdVecAt_hit "a" (.var "i") ρ m π la i x aa ta
      hlay_a ha_env hvarI hevI hloadI hgetI
  have hrIe : evalExpr (.stdVecAt "a" (.var "i")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some "a" _ _ _ _ _ ha_env hevI hgetI
  have hvarJ : memEvalExpr (.var "j") ρ m π = evalExpr (.var "j") ρ :=
    memEvalExpr_var _ _ _ _
  have hevJ : evalExpr (.var "j") ρ = .ok (.u64 j) :=
    evalExpr_var_hit _ _ _ hj_env
  have hloadJ : memLoad m aa ta (j.toNat + 1) = .ok y :=
    memLoad_cellsAt m aa ta (j.toNat + 1) (nA :: la) y hmem_a
      (by rw [List.getElem?_cons_succ]; exact hgetJ)
  have hagJ : memEvalExpr (.stdVecAt "a" (.var "j")) ρ m π =
      evalExpr (.stdVecAt "a" (.var "j")) ρ :=
    memEvalExpr_stdVecAt_hit "a" (.var "j") ρ m π la j y aa ta
      hlay_a ha_env hvarJ hevJ hloadJ hgetJ
  have hrJe : evalExpr (.stdVecAt "a" (.var "j")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some "a" _ _ _ _ _ ha_env hevJ hgetJ
  have hcmpE : evalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "a" (.var "j"))) ρ =
      .ok (.b (x.slt y)) :=
    evalExpr_slt_i32 _ _ _ _ _ hrIe hrJe
  have hcmp : memEvalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "a" (.var "j")))
      ρ m π = .ok (.b false) := by
    have h := (memEvalExpr_slt_agree _ _ _ _ _ hagI hagJ).trans hcmpE
    rwa [hltYX] at h
  have hvarK : memEvalExpr (.var "k") ρ m π = evalExpr (.var "k") ρ :=
    memEvalExpr_var _ _ _ _
  have hevK : evalExpr (.var "k") ρ = .ok (.u64 k) :=
    evalExpr_var_hit _ _ _ hk_env
  have hlenAg : memEvalExpr (.stdVecLen "tmp") ρ m π =
      evalExpr (.stdVecLen "tmp") ρ :=
    memEvalExpr_stdVecLen_hit "tmp" ρ m π lt ab tb
      hlay_tmp htmp_env hmemLen
  have hgKE : evalExpr (.ult (.var "k") (.stdVecLen "tmp")) ρ =
      .ok (.b false) := by
    have hs := evalExpr_stdVecLen_some "tmp" _ lt htmp_env
    have h := evalExpr_ult_u64 _ _ _ _ _ hevK hs
    rwa [ult_ofNat64_len k lt.length hlent, decide_eq_false hltK] at h
  have hgK : memEvalExpr (.ult (.var "k") (.stdVecLen "tmp")) ρ m π =
      .ok (.b false) :=
    (memEvalExpr_ult_agree _ _ _ _ _ hvarK hlenAg).trans hgKE
  have herr : memEvalProgStmt prog F
      (.if_ (.ult (.var "k") (.stdVecLen "tmp"))
        (.vecSet "tmp" (.var "k") (.stdVecAt "a" (.var "j"))) .fail)
      ρ m π = .error .AssertFail :=
    (memEvalProgStmt_if_false prog F _ _ _ ρ m π hgK).trans
      (memEvalProgStmt_fail prog F ρ m π)
  unfold mergeRunsMainBody
  rw [memEvalProgStmt_if_false prog F _ _ _ _ _ _ hcmp]
  exact memEvalProgStmt_seq_err prog F _ _ ρ m π .AssertFail herr

/-! ## Drain-body mirrors -/

/-- Drain-`i` body, hit, on memory: store, advance. -/
theorem memRunsDrainIBody_hit (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (i k : BitVec 64)
    (x w : BitVec 32)
    (aa ab : Addr) (ta tb : Nat) (nA nB : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_tmp : layoutLookup π "tmp" = some (ab, tb))
    (hmem_a : memFind m aa = some ⟨ta, true, nA :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nB :: lt⟩)
    (hmemLen : memLoad m ab tb 0 = .ok (BitVec.ofNat 32 lt.length))
    (hi_env : envLookup ρ "i" = some (.u64 i))
    (hk_env : envLookup ρ "k" = some (.u64 k))
    (ha_env : envLookup ρ "a" = some (.stdVecVal la))
    (htmp_env : envLookup ρ "tmp" = some (.stdVecVal lt))
    (hgetI : la[i.toNat]? = some x)
    (hltK : k.toNat < lt.length)
    (hlent : lt.length < 2 ^ 64)
    (hgetK : lt[k.toNat]? = some w)
    (m' : Mem)
    (hstore : memStore m ab tb (k.toNat + 1) x = .ok m')
    (ρ' : Env)
    (hu : envUpdate ρ "tmp" (.stdVecVal (lt.set k.toNat x)) = some ρ')
    (ρI ρK : Env)
    (huI : envUpdate ρ' "i" (.u64 (i + 1)) = some ρI)
    (huK : envUpdate ρI "k" (.u64 (k + 1)) = some ρK) :
    memEvalProgStmt prog F mergeRunsDrainIBody ρ m π =
      .ok ((ρK, m', π), .fellThrough) := by
  have hvarI : memEvalExpr (.var "i") ρ m π = evalExpr (.var "i") ρ :=
    memEvalExpr_var _ _ _ _
  have hevI : evalExpr (.var "i") ρ = .ok (.u64 i) :=
    evalExpr_var_hit _ _ _ hi_env
  have hloadI : memLoad m aa ta (i.toNat + 1) = .ok x :=
    memLoad_cellsAt m aa ta (i.toNat + 1) (nA :: la) x hmem_a
      (by rw [List.getElem?_cons_succ]; exact hgetI)
  have hrIe : evalExpr (.stdVecAt "a" (.var "i")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some "a" _ _ _ _ _ ha_env hevI hgetI
  have hrI : memEvalExpr (.stdVecAt "a" (.var "i")) ρ m π =
      .ok (.i32 x) :=
    (memEvalExpr_stdVecAt_hit "a" (.var "i") ρ m π la i x aa ta
      hlay_a ha_env hvarI hevI hloadI hgetI).trans hrIe
  have hvarK : memEvalExpr (.var "k") ρ m π = evalExpr (.var "k") ρ :=
    memEvalExpr_var _ _ _ _
  have hevK : evalExpr (.var "k") ρ = .ok (.u64 k) :=
    evalExpr_var_hit _ _ _ hk_env
  have hlenAg : memEvalExpr (.stdVecLen "tmp") ρ m π =
      evalExpr (.stdVecLen "tmp") ρ :=
    memEvalExpr_stdVecLen_hit "tmp" ρ m π lt ab tb
      hlay_tmp htmp_env hmemLen
  have hgKE : evalExpr (.ult (.var "k") (.stdVecLen "tmp")) ρ =
      .ok (.b true) := by
    have hs := evalExpr_stdVecLen_some "tmp" _ lt htmp_env
    have h := evalExpr_ult_u64 _ _ _ _ _ hevK hs
    rwa [ult_ofNat64_len k lt.length hlent, decide_eq_true hltK] at h
  have hgK : memEvalExpr (.ult (.var "k") (.stdVecLen "tmp")) ρ m π =
      .ok (.b true) :=
    (memEvalExpr_ult_agree _ _ _ _ _ hvarK hlenAg).trans hgKE
  have hset := memRevVecSet prog F "tmp" (.var "k")
    (.stdVecAt "a" (.var "i")) ρ m π k x ab tb lt w m' ρ'
    (hvarK.trans hevK) hrI htmp_env hlay_tmp hgetK hstore hu
  have hlookI' : envLookup ρ' "i" = some (.u64 i) := by
    have h := envLookup_update_miss ρ "i" "tmp"
      (.stdVecVal (lt.set k.toNat x)) ρ' (by decide) hu
    rw [h, hi_env]
  have hevI' : evalExpr (.var "i") ρ' = .ok (.u64 i) :=
    evalExpr_var_hit _ _ _ hlookI'
  have hev1 : evalExpr (.lit (.u64 1)) ρ' = .ok (.u64 1) := by
    simp [evalExpr, litVal]
  have hevUI : evalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ' =
      .ok (.u64 (i + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hevI' hev1
  have hmemI : memEvalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ' m' π =
      .ok (.u64 (i + 1)) :=
    (memEvalExpr_uadd_agree _ _ _ _ _
      (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)).trans hevUI
  have hstepI := memRevAssign prog F "i" _ ρ' m' π _ ρI
    hmemI hevUI huI
  have hlookK' : envLookup ρ' "k" = some (.u64 k) := by
    have h := envLookup_update_miss ρ "k" "tmp"
      (.stdVecVal (lt.set k.toNat x)) ρ' (by decide) hu
    rw [h, hk_env]
  have hlookKI : envLookup ρI "k" = some (.u64 k) := by
    have h := envLookup_update_miss ρ' "k" "i" (.u64 (i + 1)) ρI
      (by decide) huI
    rw [h, hlookK']
  have hevK' : evalExpr (.var "k") ρI = .ok (.u64 k) :=
    evalExpr_var_hit _ _ _ hlookKI
  have hev1K : evalExpr (.lit (.u64 1)) ρI = .ok (.u64 1) := by
    simp [evalExpr, litVal]
  have hevUK : evalExpr (.uadd (.var "k") (.lit (.u64 1))) ρI =
      .ok (.u64 (k + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hevK' hev1K
  have hmemK : memEvalExpr (.uadd (.var "k") (.lit (.u64 1))) ρI m' π =
      .ok (.u64 (k + 1)) :=
    (memEvalExpr_uadd_agree _ _ _ _ _
      (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)).trans hevUK
  have hstepK := memRevAssign prog F "k" _ ρI m' π _ ρK
    hmemK hevUK huK
  have hseqIK := memEvalProgStmt_seq prog F _ _ ρ' m' π ρI m' π
    ρK m' π .fellThrough hstepI hstepK
  exact memEvalProgStmt_seq prog F _ _ ρ m π ρ' m' π
    ρK m' π .fellThrough
    ((memEvalProgStmt_if_true prog F _ _ _ _ _ _ hgK).trans hset) hseqIK

/-- Drain-`i` body, short-`tmp` miss: loud abort. -/
theorem memRunsDrainIBody_miss (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (i k : BitVec 64)
    (x : BitVec 32)
    (aa ab : Addr) (ta tb : Nat) (nA nB : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_tmp : layoutLookup π "tmp" = some (ab, tb))
    (hmem_a : memFind m aa = some ⟨ta, true, nA :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nB :: lt⟩)
    (hmemLen : memLoad m ab tb 0 = .ok (BitVec.ofNat 32 lt.length))
    (hi_env : envLookup ρ "i" = some (.u64 i))
    (hk_env : envLookup ρ "k" = some (.u64 k))
    (ha_env : envLookup ρ "a" = some (.stdVecVal la))
    (htmp_env : envLookup ρ "tmp" = some (.stdVecVal lt))
    (hgetI : la[i.toNat]? = some x)
    (hltK : ¬ k.toNat < lt.length)
    (hlent : lt.length < 2 ^ 64) :
    memEvalProgStmt prog F mergeRunsDrainIBody ρ m π =
      .error .AssertFail := by
  have hvarK : memEvalExpr (.var "k") ρ m π = evalExpr (.var "k") ρ :=
    memEvalExpr_var _ _ _ _
  have hevK : evalExpr (.var "k") ρ = .ok (.u64 k) :=
    evalExpr_var_hit _ _ _ hk_env
  have hlenAg : memEvalExpr (.stdVecLen "tmp") ρ m π =
      evalExpr (.stdVecLen "tmp") ρ :=
    memEvalExpr_stdVecLen_hit "tmp" ρ m π lt ab tb
      hlay_tmp htmp_env hmemLen
  have hgKE : evalExpr (.ult (.var "k") (.stdVecLen "tmp")) ρ =
      .ok (.b false) := by
    have hs := evalExpr_stdVecLen_some "tmp" _ lt htmp_env
    have h := evalExpr_ult_u64 _ _ _ _ _ hevK hs
    rwa [ult_ofNat64_len k lt.length hlent, decide_eq_false hltK] at h
  have hgK : memEvalExpr (.ult (.var "k") (.stdVecLen "tmp")) ρ m π =
      .ok (.b false) :=
    (memEvalExpr_ult_agree _ _ _ _ _ hvarK hlenAg).trans hgKE
  have herr : memEvalProgStmt prog F
      (.if_ (.ult (.var "k") (.stdVecLen "tmp"))
        (.vecSet "tmp" (.var "k") (.stdVecAt "a" (.var "i"))) .fail)
      ρ m π = .error .AssertFail :=
    (memEvalProgStmt_if_false prog F _ _ _ ρ m π hgK).trans
      (memEvalProgStmt_fail prog F ρ m π)
  unfold mergeRunsDrainIBody
  exact memEvalProgStmt_seq_err prog F _ _ ρ m π .AssertFail herr

/-- Drain-`j` body, hit, on memory: store, advance. -/
theorem memRunsDrainJBody_hit (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (j k : BitVec 64)
    (y w : BitVec 32)
    (aa ab : Addr) (ta tb : Nat) (nA nB : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_tmp : layoutLookup π "tmp" = some (ab, tb))
    (hmem_a : memFind m aa = some ⟨ta, true, nA :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nB :: lt⟩)
    (hmemLen : memLoad m ab tb 0 = .ok (BitVec.ofNat 32 lt.length))
    (hj_env : envLookup ρ "j" = some (.u64 j))
    (hk_env : envLookup ρ "k" = some (.u64 k))
    (ha_env : envLookup ρ "a" = some (.stdVecVal la))
    (htmp_env : envLookup ρ "tmp" = some (.stdVecVal lt))
    (hgetJ : la[j.toNat]? = some y)
    (hltK : k.toNat < lt.length)
    (hlent : lt.length < 2 ^ 64)
    (hgetK : lt[k.toNat]? = some w)
    (m' : Mem)
    (hstore : memStore m ab tb (k.toNat + 1) y = .ok m')
    (ρ' : Env)
    (hu : envUpdate ρ "tmp" (.stdVecVal (lt.set k.toNat y)) = some ρ')
    (ρJ ρK : Env)
    (huJ : envUpdate ρ' "j" (.u64 (j + 1)) = some ρJ)
    (huK : envUpdate ρJ "k" (.u64 (k + 1)) = some ρK) :
    memEvalProgStmt prog F mergeRunsDrainJBody ρ m π =
      .ok ((ρK, m', π), .fellThrough) := by
  have hvarJ : memEvalExpr (.var "j") ρ m π = evalExpr (.var "j") ρ :=
    memEvalExpr_var _ _ _ _
  have hevJ : evalExpr (.var "j") ρ = .ok (.u64 j) :=
    evalExpr_var_hit _ _ _ hj_env
  have hloadJ : memLoad m aa ta (j.toNat + 1) = .ok y :=
    memLoad_cellsAt m aa ta (j.toNat + 1) (nA :: la) y hmem_a
      (by rw [List.getElem?_cons_succ]; exact hgetJ)
  have hrJe : evalExpr (.stdVecAt "a" (.var "j")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some "a" _ _ _ _ _ ha_env hevJ hgetJ
  have hrJ : memEvalExpr (.stdVecAt "a" (.var "j")) ρ m π =
      .ok (.i32 y) :=
    (memEvalExpr_stdVecAt_hit "a" (.var "j") ρ m π la j y aa ta
      hlay_a ha_env hvarJ hevJ hloadJ hgetJ).trans hrJe
  have hvarK : memEvalExpr (.var "k") ρ m π = evalExpr (.var "k") ρ :=
    memEvalExpr_var _ _ _ _
  have hevK : evalExpr (.var "k") ρ = .ok (.u64 k) :=
    evalExpr_var_hit _ _ _ hk_env
  have hlenAg : memEvalExpr (.stdVecLen "tmp") ρ m π =
      evalExpr (.stdVecLen "tmp") ρ :=
    memEvalExpr_stdVecLen_hit "tmp" ρ m π lt ab tb
      hlay_tmp htmp_env hmemLen
  have hgKE : evalExpr (.ult (.var "k") (.stdVecLen "tmp")) ρ =
      .ok (.b true) := by
    have hs := evalExpr_stdVecLen_some "tmp" _ lt htmp_env
    have h := evalExpr_ult_u64 _ _ _ _ _ hevK hs
    rwa [ult_ofNat64_len k lt.length hlent, decide_eq_true hltK] at h
  have hgK : memEvalExpr (.ult (.var "k") (.stdVecLen "tmp")) ρ m π =
      .ok (.b true) :=
    (memEvalExpr_ult_agree _ _ _ _ _ hvarK hlenAg).trans hgKE
  have hset := memRevVecSet prog F "tmp" (.var "k")
    (.stdVecAt "a" (.var "j")) ρ m π k y ab tb lt w m' ρ'
    (hvarK.trans hevK) hrJ htmp_env hlay_tmp hgetK hstore hu
  have hlookJ' : envLookup ρ' "j" = some (.u64 j) := by
    have h := envLookup_update_miss ρ "j" "tmp"
      (.stdVecVal (lt.set k.toNat y)) ρ' (by decide) hu
    rw [h, hj_env]
  have hevJ' : evalExpr (.var "j") ρ' = .ok (.u64 j) :=
    evalExpr_var_hit _ _ _ hlookJ'
  have hev1 : evalExpr (.lit (.u64 1)) ρ' = .ok (.u64 1) := by
    simp [evalExpr, litVal]
  have hevUJ : evalExpr (.uadd (.var "j") (.lit (.u64 1))) ρ' =
      .ok (.u64 (j + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hevJ' hev1
  have hmemJ : memEvalExpr (.uadd (.var "j") (.lit (.u64 1))) ρ' m' π =
      .ok (.u64 (j + 1)) :=
    (memEvalExpr_uadd_agree _ _ _ _ _
      (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)).trans hevUJ
  have hstepJ := memRevAssign prog F "j" _ ρ' m' π _ ρJ
    hmemJ hevUJ huJ
  have hlookK' : envLookup ρ' "k" = some (.u64 k) := by
    have h := envLookup_update_miss ρ "k" "tmp"
      (.stdVecVal (lt.set k.toNat y)) ρ' (by decide) hu
    rw [h, hk_env]
  have hlookKJ : envLookup ρJ "k" = some (.u64 k) := by
    have h := envLookup_update_miss ρ' "k" "j" (.u64 (j + 1)) ρJ
      (by decide) huJ
    rw [h, hlookK']
  have hevK' : evalExpr (.var "k") ρJ = .ok (.u64 k) :=
    evalExpr_var_hit _ _ _ hlookKJ
  have hev1K : evalExpr (.lit (.u64 1)) ρJ = .ok (.u64 1) := by
    simp [evalExpr, litVal]
  have hevUK : evalExpr (.uadd (.var "k") (.lit (.u64 1))) ρJ =
      .ok (.u64 (k + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hevK' hev1K
  have hmemK : memEvalExpr (.uadd (.var "k") (.lit (.u64 1))) ρJ m' π =
      .ok (.u64 (k + 1)) :=
    (memEvalExpr_uadd_agree _ _ _ _ _
      (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)).trans hevUK
  have hstepK := memRevAssign prog F "k" _ ρJ m' π _ ρK
    hmemK hevUK huK
  have hseqJK := memEvalProgStmt_seq prog F _ _ ρ' m' π ρJ m' π
    ρK m' π .fellThrough hstepJ hstepK
  exact memEvalProgStmt_seq prog F _ _ ρ m π ρ' m' π
    ρK m' π .fellThrough
    ((memEvalProgStmt_if_true prog F _ _ _ _ _ _ hgK).trans hset) hseqJK

/-- Drain-`j` body, short-`tmp` miss: loud abort. -/
theorem memRunsDrainJBody_miss (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (j k : BitVec 64)
    (y : BitVec 32)
    (aa ab : Addr) (ta tb : Nat) (nA nB : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_tmp : layoutLookup π "tmp" = some (ab, tb))
    (hmem_a : memFind m aa = some ⟨ta, true, nA :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nB :: lt⟩)
    (hmemLen : memLoad m ab tb 0 = .ok (BitVec.ofNat 32 lt.length))
    (hj_env : envLookup ρ "j" = some (.u64 j))
    (hk_env : envLookup ρ "k" = some (.u64 k))
    (ha_env : envLookup ρ "a" = some (.stdVecVal la))
    (htmp_env : envLookup ρ "tmp" = some (.stdVecVal lt))
    (hgetJ : la[j.toNat]? = some y)
    (hltK : ¬ k.toNat < lt.length)
    (hlent : lt.length < 2 ^ 64) :
    memEvalProgStmt prog F mergeRunsDrainJBody ρ m π =
      .error .AssertFail := by
  have hvarK : memEvalExpr (.var "k") ρ m π = evalExpr (.var "k") ρ :=
    memEvalExpr_var _ _ _ _
  have hevK : evalExpr (.var "k") ρ = .ok (.u64 k) :=
    evalExpr_var_hit _ _ _ hk_env
  have hlenAg : memEvalExpr (.stdVecLen "tmp") ρ m π =
      evalExpr (.stdVecLen "tmp") ρ :=
    memEvalExpr_stdVecLen_hit "tmp" ρ m π lt ab tb
      hlay_tmp htmp_env hmemLen
  have hgKE : evalExpr (.ult (.var "k") (.stdVecLen "tmp")) ρ =
      .ok (.b false) := by
    have hs := evalExpr_stdVecLen_some "tmp" _ lt htmp_env
    have h := evalExpr_ult_u64 _ _ _ _ _ hevK hs
    rwa [ult_ofNat64_len k lt.length hlent, decide_eq_false hltK] at h
  have hgK : memEvalExpr (.ult (.var "k") (.stdVecLen "tmp")) ρ m π =
      .ok (.b false) :=
    (memEvalExpr_ult_agree _ _ _ _ _ hvarK hlenAg).trans hgKE
  have herr : memEvalProgStmt prog F
      (.if_ (.ult (.var "k") (.stdVecLen "tmp"))
        (.vecSet "tmp" (.var "k") (.stdVecAt "a" (.var "j"))) .fail)
      ρ m π = .error .AssertFail :=
    (memEvalProgStmt_if_false prog F _ _ _ ρ m π hgK).trans
      (memEvalProgStmt_fail prog F ρ m π)
  unfold mergeRunsDrainJBody
  exact memEvalProgStmt_seq_err prog F _ _ ρ m π .AssertFail herr

/-! ## Memory loop inductions -/

/-- Drain-`i` ok soundness on memory: the loop copies `la[i..mid]`
    into `tmp` and exits with the forward-model state (fuel induction
    mirroring `mergeRunsDrainI_ok`; the by-find blocks thread the
    shadowing snapshots, `memFind_memStore_other` keeps the `a` pin). -/
theorem memRunsDrainI_ok (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (mid hi i j k : BitVec 64)
    (i' k' : Nat) (lt' : List (BitVec 32))
    (aa ab : Addr) (ta tb : Nat) (nA nB : BitVec 32)
    (haa : aa ≠ ab)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_tmp : layoutLookup π "tmp" = some (ab, tb))
    (hmem_a : memFind m aa = some ⟨ta, true, nA :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nB :: lt⟩)
    (hnB : nB = BitVec.ofNat 32 lt.length)
    (hi_env : envLookup ρ "i" = some (.u64 i))
    (hk_env : envLookup ρ "k" = some (.u64 k))
    (ha_env : envLookup ρ "a" = some (.stdVecVal la))
    (hmid_env : envLookup ρ "mid" = some (.u64 mid))
    (htmp_env : envLookup ρ "tmp" = some (.stdVecVal lt))
    (hj_env : envLookup ρ "j" = some (.u64 j))
    (hhi_env : envLookup ρ "hi" = some (.u64 hi))
    (hlent : lt.length < 2 ^ 64)
    (hmid_le : mid.toNat ≤ la.length)
    (hF : (mid.toNat - i.toNat) + 1 ≤ F)
    (hfwd : mergeRunsDrainIFwd la lt (mid.toNat - i.toNat)
      i.toNat k.toNat mid.toNat = .ok (i', k', lt')) :
    ∃ ρ' m', memEvalProgStmt prog F mergeRunsDrainI ρ m π =
        .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "tmp" = some (.stdVecVal lt') ∧
      envLookup ρ' "i" = some (.u64 (BitVec.ofNat 64 i')) ∧
      envLookup ρ' "k" = some (.u64 (BitVec.ofNat 64 k')) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "mid" = some (.u64 mid) ∧
      envLookup ρ' "j" = some (.u64 j) ∧
      envLookup ρ' "hi" = some (.u64 hi) ∧
      memFind m' aa = some ⟨ta, true, nA :: la⟩ ∧
      memFind m' ab = some ⟨tb, true, nB :: lt'⟩ ∧
      nB = BitVec.ofNat 32 lt'.length := by
  induction F generalizing ρ m π la lt i k i' k' lt' with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hI : i.toNat < mid.toNat
    · have hcond : memEvalExpr (.ult (.var "i") (.var "mid")) ρ m π =
          .ok (.b true) := by
        have hvarI : memEvalExpr (.var "i") ρ m π =
            evalExpr (.var "i") ρ := memEvalExpr_var _ _ _ _
        have hvarM : memEvalExpr (.var "mid") ρ m π =
            evalExpr (.var "mid") ρ := memEvalExpr_var _ _ _ _
        have hE : evalExpr (.ult (.var "i") (.var "mid")) ρ =
            .ok (.b true) := by
          have h := evalExpr_ult_u64 _ _ _ _ _
            (evalExpr_var_hit _ _ _ hi_env)
            (evalExpr_var_hit _ _ _ hmid_env)
          have ht : (i.ult mid) = true := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_true hI
          rwa [ht] at h
        exact (memEvalExpr_ult_agree _ _ _ _ _ hvarI hvarM).trans hE
      have hM : (mid.toNat - i.toNat) =
          ((mid.toNat - i.toNat) - 1) + 1 := by omega
      rw [hM] at hfwd
      have hgetI : la[i.toNat]? = some la[i.toNat] :=
        List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hI hmid_le)
      cases hgetK : lt[k.toNat]? with
      | none =>
        have hcontra : mergeRunsDrainIFwd la lt
            (((mid.toNat - i.toNat) - 1) + 1)
            i.toNat k.toNat mid.toNat = .error .AssertFail := by
          simp only [mergeRunsDrainIFwd, dite_eq_left hI, hgetK]
        rw [hcontra] at hfwd
        cases hfwd
      | some w =>
        have hltK : k.toNat < lt.length :=
          list_lt_of_getElem?_some lt k.toNat w hgetK
        have hfwdI : mergeRunsDrainIFwd la (lt.set k.toNat la[i.toNat])
            ((mid.toNat - i.toNat) - 1)
            (i.toNat + 1) (k.toNat + 1) mid.toNat =
            .ok (i', k', lt') := by
          have h := hfwd
          simp only [mergeRunsDrainIFwd, dite_eq_left hI, hgetK,
            hgetI] at h
          exact h
        have hmemLen : memLoad m ab tb 0 =
            .ok (BitVec.ofNat 32 lt.length) := by
          rw [← hnB]
          exact memLoad_cellsAt m ab tb 0 (nB :: lt) nB hmem_b rfl
        have hlt1 : k.toNat + 1 < (nB :: lt).length := by
          simp only [List.length_cons]
          omega
        obtain ⟨m₁, hstore⟩ : ∃ m₁, memStore m ab tb
            (k.toNat + 1) la[i.toNat] = .ok m₁ :=
          ⟨_, memStore_cellsAt m ab tb (k.toNat + 1) (nB :: lt)
            la[i.toNat] hmem_b hlt1⟩
        obtain ⟨ρt, hu⟩ := envUpdate_some_of_lookup ρ "tmp"
          (.stdVecVal lt) (.stdVecVal (lt.set k.toNat la[i.toNat]))
          htmp_env
        have hlookI' : envLookup ρt "i" = some (.u64 i) := by
          have h := envLookup_update_miss ρ "i" "tmp" _ ρt
            (by decide) hu
          rw [h, hi_env]
        obtain ⟨ρI, huI⟩ := envUpdate_some_of_lookup ρt "i"
          (.u64 i) (.u64 (i + 1)) hlookI'
        have hlookK' : envLookup ρt "k" = some (.u64 k) := by
          have h := envLookup_update_miss ρ "k" "tmp" _ ρt
            (by decide) hu
          rw [h, hk_env]
        have hlookKI : envLookup ρI "k" = some (.u64 k) := by
          have h := envLookup_update_miss ρt "k" "i" _ ρI
            (by decide) huI
          rw [h, hlookK']
        obtain ⟨ρK, huK⟩ := envUpdate_some_of_lookup ρI "k"
          (.u64 k) (.u64 (k + 1)) hlookKI
        have hstep : memEvalProgStmt prog F mergeRunsDrainIBody
            ρ m π = .ok ((ρK, m₁, π), .fellThrough) :=
          memRunsDrainIBody_hit prog F ρ m π la lt i k la[i.toNat] w
            aa ab ta tb nA nB hlay_a hlay_tmp hmem_a hmem_b hmemLen
            hi_env hk_env ha_env htmp_env hgetI hltK hlent hgetK _
            hstore _ hu _ _ huI huK
        have hloop : memEvalProgStmt prog (F + 1) mergeRunsDrainI
            ρ m π = memEvalProgStmt prog F mergeRunsDrainI ρK m₁ π := by
          simp only [mergeRunsDrainI,
            memEvalProgStmt_while_true prog F _ _ _ _ _ hcond, hstep]
        have h1i : (i + 1).toNat = i.toNat + 1 :=
          bv64_succ_toNat i _ hI (by omega)
        have h1k : (k + 1).toNat = k.toNat + 1 :=
          bv64_succ_toNat k _ hltK hlent
        have hlent' : (lt.set k.toNat la[i.toNat]).length < 2 ^ 64 := by
          rw [List.length_set]
          exact hlent
        have hF' : (mid.toNat - (i + 1).toNat) + 1 ≤ F := by omega
        have hM' : (mid.toNat - i.toNat) - 1 =
            (mid.toNat - (i + 1).toNat) := by omega
        have hfwd' : mergeRunsDrainIFwd la (lt.set k.toNat la[i.toNat])
            (mid.toNat - (i + 1).toNat)
            ((i + 1).toNat) ((k + 1).toNat) mid.toNat =
            .ok (i', k', lt') := by
          rw [← h1i, ← h1k, hM'] at hfwdI
          exact hfwdI
        have hmem_a₁ : memFind m₁ aa = some ⟨ta, true, nA :: la⟩ := by
          have h := memFind_memStore_other m m₁ ab aa tb
            (k.toNat + 1) la[i.toNat] hstore haa
          rw [h]
          exact hmem_a
        have hmem_b₁ : memFind m₁ ab =
            some ⟨tb, true, nB :: lt.set k.toNat la[i.toNat]⟩ := by
          have hcells := memFind_cellsAt_store m ab tb (k.toNat + 1)
            (nB :: lt) la[i.toNat] m₁ hmem_b hlt1 hstore
          have hsetEq : (nB :: lt).set (k.toNat + 1) la[i.toNat] =
              nB :: lt.set k.toNat la[i.toNat] :=
            List.set_cons_succ
          rw [hsetEq] at hcells
          exact hcells
        have hnB₁ : nB =
            BitVec.ofNat 32 (lt.set k.toNat la[i.toNat]).length := by
          rw [List.length_set]
          exact hnB
        have hlookIK : envLookup ρI "i" = some (.u64 (i + 1)) :=
          envLookup_update_hit ρt "i" _ ρI huI
        have hi_env₁ : envLookup ρK "i" = some (.u64 (i + 1)) := by
          have h := envLookup_update_miss ρI "i" "k" _ ρK
            (by decide) huK
          rw [h, hlookIK]
        have hk_env₁ : envLookup ρK "k" = some (.u64 (k + 1)) :=
          envLookup_update_hit ρI "k" _ ρK huK
        have ha_env₁ : envLookup ρK "a" = some (.stdVecVal la) := by
          have h1 := envLookup_update_miss ρI "a" "k" _ ρK
            (by decide) huK
          have h2 := envLookup_update_miss ρt "a" "i" _ ρI
            (by decide) huI
          have h3 := envLookup_update_miss ρ "a" "tmp" _ ρt
            (by decide) hu
          rw [h1, h2, h3, ha_env]
        have hmid_env₁ : envLookup ρK "mid" = some (.u64 mid) := by
          have h1 := envLookup_update_miss ρI "mid" "k" _ ρK
            (by decide) huK
          have h2 := envLookup_update_miss ρt "mid" "i" _ ρI
            (by decide) huI
          have h3 := envLookup_update_miss ρ "mid" "tmp" _ ρt
            (by decide) hu
          rw [h1, h2, h3, hmid_env]
        have htmp_env₁ : envLookup ρK "tmp" =
            some (.stdVecVal (lt.set k.toNat la[i.toNat])) := by
          have h1 := envLookup_update_miss ρI "tmp" "k" _ ρK
            (by decide) huK
          have h2 := envLookup_update_miss ρt "tmp" "i" _ ρI
            (by decide) huI
          rw [h1, h2]
          exact envLookup_update_hit ρ "tmp" _ ρt hu
        have hj_env₁ : envLookup ρK "j" = some (.u64 j) := by
          have h1 := envLookup_update_miss ρI "j" "k" _ ρK
            (by decide) huK
          have h2 := envLookup_update_miss ρt "j" "i" _ ρI
            (by decide) huI
          have h3 := envLookup_update_miss ρ "j" "tmp" _ ρt
            (by decide) hu
          rw [h1, h2, h3, hj_env]
        have hhi_env₁ : envLookup ρK "hi" = some (.u64 hi) := by
          have h1 := envLookup_update_miss ρI "hi" "k" _ ρK
            (by decide) huK
          have h2 := envLookup_update_miss ρt "hi" "i" _ ρI
            (by decide) huI
          have h3 := envLookup_update_miss ρ "hi" "tmp" _ ρt
            (by decide) hu
          rw [h1, h2, h3, hhi_env]
        rw [hloop]
        exact ih ρK m₁ π la (lt.set k.toNat la[i.toNat]) (i + 1)
          (k + 1) i' k' lt' hlay_a hlay_tmp hmem_a₁ hmem_b₁ hnB₁
          hi_env₁ hk_env₁ ha_env₁ hmid_env₁ htmp_env₁ hj_env₁ hhi_env₁
          hlent' hmid_le
          hF' hfwd'
    · have hcond : memEvalExpr (.ult (.var "i") (.var "mid")) ρ m π =
          .ok (.b false) := by
        have hvarI : memEvalExpr (.var "i") ρ m π =
            evalExpr (.var "i") ρ := memEvalExpr_var _ _ _ _
        have hvarM : memEvalExpr (.var "mid") ρ m π =
            evalExpr (.var "mid") ρ := memEvalExpr_var _ _ _ _
        have hE : evalExpr (.ult (.var "i") (.var "mid")) ρ =
            .ok (.b false) := by
          have h := evalExpr_ult_u64 _ _ _ _ _
            (evalExpr_var_hit _ _ _ hi_env)
            (evalExpr_var_hit _ _ _ hmid_env)
          have ht : (i.ult mid) = false := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_false hI
          rwa [ht] at h
        exact (memEvalExpr_ult_agree _ _ _ _ _ hvarI hvarM).trans hE
      have hfwd0 : mergeRunsDrainIFwd la lt (mid.toNat - i.toNat)
          i.toNat k.toNat mid.toNat = .ok (i.toNat, k.toNat, lt) := by
        match hm : (mid.toNat - i.toNat) with
        | 0 => simp only [mergeRunsDrainIFwd]
        | _ + 1 =>
          simp only [mergeRunsDrainIFwd, dite_eq_right hI]
      rw [hfwd0] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hfwd
      have hexit : memEvalProgStmt prog (F + 1) mergeRunsDrainI
          ρ m π = .ok ((ρ, m, π), .fellThrough) := by
        simp only [mergeRunsDrainI,
          memEvalProgStmt_while_false prog _ _ _ _ _ _ hcond]
      refine ⟨ρ, m, hexit, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact htmp_env
      · have hto : BitVec.ofNat 64 i.toNat = i := bv64_ofNat_toNat i
        rw [hto]
        exact hi_env
      · have hto : BitVec.ofNat 64 k.toNat = k := bv64_ofNat_toNat k
        rw [hto]
        exact hk_env
      · exact ha_env
      · exact hmid_env
      · exact hj_env
      · exact hhi_env
      · exact hmem_a
      · exact hmem_b
      · exact hnB

/-- Drain-`i` err soundness on memory: a model abort replays as the
    same abort (fuel induction mirroring `mergeRunsDrainI_err`; the
    miss leg aborts via `memRunsDrainIBody_miss`, the hit leg steps
    and re-inducts). -/
theorem memRunsDrainI_err (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (mid i k : BitVec 64)
    (e : Panic)
    (aa ab : Addr) (ta tb : Nat) (nA nB : BitVec 32)
    (haa : aa ≠ ab)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_tmp : layoutLookup π "tmp" = some (ab, tb))
    (hmem_a : memFind m aa = some ⟨ta, true, nA :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nB :: lt⟩)
    (hnB : nB = BitVec.ofNat 32 lt.length)
    (hi_env : envLookup ρ "i" = some (.u64 i))
    (hk_env : envLookup ρ "k" = some (.u64 k))
    (ha_env : envLookup ρ "a" = some (.stdVecVal la))
    (hmid_env : envLookup ρ "mid" = some (.u64 mid))
    (htmp_env : envLookup ρ "tmp" = some (.stdVecVal lt))
    (hlent : lt.length < 2 ^ 64)
    (hmid_le : mid.toNat ≤ la.length)
    (hF : (mid.toNat - i.toNat) + 1 ≤ F)
    (hfwd : mergeRunsDrainIFwd la lt (mid.toNat - i.toNat)
      i.toNat k.toNat mid.toNat = .error e) :
    memEvalProgStmt prog F mergeRunsDrainI ρ m π = .error e := by
  induction F generalizing ρ m π la lt i k e with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hI : i.toNat < mid.toNat
    · have hcond : memEvalExpr (.ult (.var "i") (.var "mid")) ρ m π =
          .ok (.b true) := by
        have hvarI : memEvalExpr (.var "i") ρ m π =
            evalExpr (.var "i") ρ := memEvalExpr_var _ _ _ _
        have hvarM : memEvalExpr (.var "mid") ρ m π =
            evalExpr (.var "mid") ρ := memEvalExpr_var _ _ _ _
        have hE : evalExpr (.ult (.var "i") (.var "mid")) ρ =
            .ok (.b true) := by
          have h := evalExpr_ult_u64 _ _ _ _ _
            (evalExpr_var_hit _ _ _ hi_env)
            (evalExpr_var_hit _ _ _ hmid_env)
          have ht : (i.ult mid) = true := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_true hI
          rwa [ht] at h
        exact (memEvalExpr_ult_agree _ _ _ _ _ hvarI hvarM).trans hE
      have hM : (mid.toNat - i.toNat) =
          ((mid.toNat - i.toNat) - 1) + 1 := by omega
      rw [hM] at hfwd
      have hgetI : la[i.toNat]? = some la[i.toNat] :=
        List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hI hmid_le)
      cases hgetK : lt[k.toNat]? with
      | none =>
        have hfwde : mergeRunsDrainIFwd la lt
            (((mid.toNat - i.toNat) - 1) + 1)
            i.toNat k.toNat mid.toNat = .error .AssertFail := by
          simp only [mergeRunsDrainIFwd, dite_eq_left hI, hgetK]
        rw [hfwde] at hfwd
        cases hfwd
        have hltK : ¬ k.toNat < lt.length := by
          intro hc
          have hsome := List.getElem?_eq_getElem hc
          rw [hsome] at hgetK
          cases hgetK
        have hmemLen : memLoad m ab tb 0 =
            .ok (BitVec.ofNat 32 lt.length) := by
          rw [← hnB]
          exact memLoad_cellsAt m ab tb 0 (nB :: lt) nB hmem_b rfl
        have hbody := memRunsDrainIBody_miss prog F ρ m π la lt i k
          la[i.toNat] aa ab ta tb nA nB hlay_a hlay_tmp hmem_a hmem_b
          hmemLen hi_env hk_env ha_env htmp_env hgetI hltK hlent
        have herr : memEvalProgStmt prog (F + 1) mergeRunsDrainI
            ρ m π = .error .AssertFail := by
          simp only [mergeRunsDrainI,
            memEvalProgStmt_while_true prog F _ _ _ _ _ hcond, hbody]
        exact herr
      | some w =>
        have hltK : k.toNat < lt.length :=
          list_lt_of_getElem?_some lt k.toNat w hgetK
        have hfwdI : mergeRunsDrainIFwd la (lt.set k.toNat la[i.toNat])
            ((mid.toNat - i.toNat) - 1)
            (i.toNat + 1) (k.toNat + 1) mid.toNat = .error e := by
          have h := hfwd
          simp only [mergeRunsDrainIFwd, dite_eq_left hI, hgetK,
            hgetI] at h
          exact h
        have hmemLen : memLoad m ab tb 0 =
            .ok (BitVec.ofNat 32 lt.length) := by
          rw [← hnB]
          exact memLoad_cellsAt m ab tb 0 (nB :: lt) nB hmem_b rfl
        have hlt1 : k.toNat + 1 < (nB :: lt).length := by
          simp only [List.length_cons]
          omega
        obtain ⟨m₁, hstore⟩ : ∃ m₁, memStore m ab tb
            (k.toNat + 1) la[i.toNat] = .ok m₁ :=
          ⟨_, memStore_cellsAt m ab tb (k.toNat + 1) (nB :: lt)
            la[i.toNat] hmem_b hlt1⟩
        obtain ⟨ρt, hu⟩ := envUpdate_some_of_lookup ρ "tmp"
          (.stdVecVal lt) (.stdVecVal (lt.set k.toNat la[i.toNat]))
          htmp_env
        have hlookI' : envLookup ρt "i" = some (.u64 i) := by
          have h := envLookup_update_miss ρ "i" "tmp" _ ρt
            (by decide) hu
          rw [h, hi_env]
        obtain ⟨ρI, huI⟩ := envUpdate_some_of_lookup ρt "i"
          (.u64 i) (.u64 (i + 1)) hlookI'
        have hlookK' : envLookup ρt "k" = some (.u64 k) := by
          have h := envLookup_update_miss ρ "k" "tmp" _ ρt
            (by decide) hu
          rw [h, hk_env]
        have hlookKI : envLookup ρI "k" = some (.u64 k) := by
          have h := envLookup_update_miss ρt "k" "i" _ ρI
            (by decide) huI
          rw [h, hlookK']
        obtain ⟨ρK, huK⟩ := envUpdate_some_of_lookup ρI "k"
          (.u64 k) (.u64 (k + 1)) hlookKI
        have hstep : memEvalProgStmt prog F mergeRunsDrainIBody
            ρ m π = .ok ((ρK, m₁, π), .fellThrough) :=
          memRunsDrainIBody_hit prog F ρ m π la lt i k la[i.toNat] w
            aa ab ta tb nA nB hlay_a hlay_tmp hmem_a hmem_b hmemLen
            hi_env hk_env ha_env htmp_env hgetI hltK hlent hgetK _
            hstore _ hu _ _ huI huK
        have hloop : memEvalProgStmt prog (F + 1) mergeRunsDrainI
            ρ m π = memEvalProgStmt prog F mergeRunsDrainI ρK m₁ π := by
          simp only [mergeRunsDrainI,
            memEvalProgStmt_while_true prog F _ _ _ _ _ hcond, hstep]
        have h1i : (i + 1).toNat = i.toNat + 1 :=
          bv64_succ_toNat i _ hI (by omega)
        have h1k : (k + 1).toNat = k.toNat + 1 :=
          bv64_succ_toNat k _ hltK hlent
        have hlent' : (lt.set k.toNat la[i.toNat]).length < 2 ^ 64 := by
          rw [List.length_set]
          exact hlent
        have hF' : (mid.toNat - (i + 1).toNat) + 1 ≤ F := by omega
        have hM' : (mid.toNat - i.toNat) - 1 =
            (mid.toNat - (i + 1).toNat) := by omega
        have hfwd' : mergeRunsDrainIFwd la (lt.set k.toNat la[i.toNat])
            (mid.toNat - (i + 1).toNat)
            ((i + 1).toNat) ((k + 1).toNat) mid.toNat = .error e := by
          rw [← h1i, ← h1k, hM'] at hfwdI
          exact hfwdI
        have hmem_a₁ : memFind m₁ aa = some ⟨ta, true, nA :: la⟩ := by
          have h := memFind_memStore_other m m₁ ab aa tb
            (k.toNat + 1) la[i.toNat] hstore haa
          rw [h]
          exact hmem_a
        have hmem_b₁ : memFind m₁ ab =
            some ⟨tb, true, nB :: lt.set k.toNat la[i.toNat]⟩ := by
          have hcells := memFind_cellsAt_store m ab tb (k.toNat + 1)
            (nB :: lt) la[i.toNat] m₁ hmem_b hlt1 hstore
          have hsetEq : (nB :: lt).set (k.toNat + 1) la[i.toNat] =
              nB :: lt.set k.toNat la[i.toNat] :=
            List.set_cons_succ
          rw [hsetEq] at hcells
          exact hcells
        have hnB₁ : nB =
            BitVec.ofNat 32 (lt.set k.toNat la[i.toNat]).length := by
          rw [List.length_set]
          exact hnB
        have hlookIK : envLookup ρI "i" = some (.u64 (i + 1)) :=
          envLookup_update_hit ρt "i" _ ρI huI
        have hi_env₁ : envLookup ρK "i" = some (.u64 (i + 1)) := by
          have h := envLookup_update_miss ρI "i" "k" _ ρK
            (by decide) huK
          rw [h, hlookIK]
        have hk_env₁ : envLookup ρK "k" = some (.u64 (k + 1)) :=
          envLookup_update_hit ρI "k" _ ρK huK
        have ha_env₁ : envLookup ρK "a" = some (.stdVecVal la) := by
          have h1 := envLookup_update_miss ρI "a" "k" _ ρK
            (by decide) huK
          have h2 := envLookup_update_miss ρt "a" "i" _ ρI
            (by decide) huI
          have h3 := envLookup_update_miss ρ "a" "tmp" _ ρt
            (by decide) hu
          rw [h1, h2, h3, ha_env]
        have hmid_env₁ : envLookup ρK "mid" = some (.u64 mid) := by
          have h1 := envLookup_update_miss ρI "mid" "k" _ ρK
            (by decide) huK
          have h2 := envLookup_update_miss ρt "mid" "i" _ ρI
            (by decide) huI
          have h3 := envLookup_update_miss ρ "mid" "tmp" _ ρt
            (by decide) hu
          rw [h1, h2, h3, hmid_env]
        have htmp_env₁ : envLookup ρK "tmp" =
            some (.stdVecVal (lt.set k.toNat la[i.toNat])) := by
          have h1 := envLookup_update_miss ρI "tmp" "k" _ ρK
            (by decide) huK
          have h2 := envLookup_update_miss ρt "tmp" "i" _ ρI
            (by decide) huI
          rw [h1, h2]
          exact envLookup_update_hit ρ "tmp" _ ρt hu
        rw [hloop]
        exact ih ρK m₁ π la (lt.set k.toNat la[i.toNat]) (i + 1)
          (k + 1) e hlay_a hlay_tmp hmem_a₁ hmem_b₁ hnB₁
          hi_env₁ hk_env₁ ha_env₁ hmid_env₁ htmp_env₁ hlent' hmid_le
          hF' hfwd'
    · have hcond : memEvalExpr (.ult (.var "i") (.var "mid")) ρ m π =
          .ok (.b false) := by
        have hvarI : memEvalExpr (.var "i") ρ m π =
            evalExpr (.var "i") ρ := memEvalExpr_var _ _ _ _
        have hvarM : memEvalExpr (.var "mid") ρ m π =
            evalExpr (.var "mid") ρ := memEvalExpr_var _ _ _ _
        have hE : evalExpr (.ult (.var "i") (.var "mid")) ρ =
            .ok (.b false) := by
          have h := evalExpr_ult_u64 _ _ _ _ _
            (evalExpr_var_hit _ _ _ hi_env)
            (evalExpr_var_hit _ _ _ hmid_env)
          have ht : (i.ult mid) = false := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_false hI
          rwa [ht] at h
        exact (memEvalExpr_ult_agree _ _ _ _ _ hvarI hvarM).trans hE
      have hfwd0 : mergeRunsDrainIFwd la lt (mid.toNat - i.toNat)
          i.toNat k.toNat mid.toNat = .ok (i.toNat, k.toNat, lt) := by
        match hm : (mid.toNat - i.toNat) with
        | 0 => simp only [mergeRunsDrainIFwd]
        | _ + 1 =>
          simp only [mergeRunsDrainIFwd, dite_eq_right hI]
      rw [hfwd0] at hfwd
      cases hfwd

/-- Drain-`j` err soundness on memory: a model abort replays as the
    same abort (fuel induction mirroring `mergeRunsDrainJ_err`; the
    miss leg aborts via `memRunsDrainJBody_miss`, the hit leg steps
    and re-inducts). -/
theorem memRunsDrainJ_err (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (hi j k : BitVec 64)
    (e : Panic)
    (aa ab : Addr) (ta tb : Nat) (nA nB : BitVec 32)
    (haa : aa ≠ ab)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_tmp : layoutLookup π "tmp" = some (ab, tb))
    (hmem_a : memFind m aa = some ⟨ta, true, nA :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nB :: lt⟩)
    (hnB : nB = BitVec.ofNat 32 lt.length)
    (hj_env : envLookup ρ "j" = some (.u64 j))
    (hk_env : envLookup ρ "k" = some (.u64 k))
    (ha_env : envLookup ρ "a" = some (.stdVecVal la))
    (hhi_env : envLookup ρ "hi" = some (.u64 hi))
    (htmp_env : envLookup ρ "tmp" = some (.stdVecVal lt))
    (hlent : lt.length < 2 ^ 64)
    (hhi_le : hi.toNat ≤ la.length)
    (hF : (hi.toNat - j.toNat) + 1 ≤ F)
    (hfwd : mergeRunsDrainJFwd la lt (hi.toNat - j.toNat)
      j.toNat k.toNat hi.toNat = .error e) :
    memEvalProgStmt prog F mergeRunsDrainJ ρ m π = .error e := by
  induction F generalizing ρ m π la lt j k e with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hJ : j.toNat < hi.toNat
    · have hcond : memEvalExpr (.ult (.var "j") (.var "hi")) ρ m π =
          .ok (.b true) := by
        have hvarI : memEvalExpr (.var "j") ρ m π =
            evalExpr (.var "j") ρ := memEvalExpr_var _ _ _ _
        have hvarM : memEvalExpr (.var "hi") ρ m π =
            evalExpr (.var "hi") ρ := memEvalExpr_var _ _ _ _
        have hE : evalExpr (.ult (.var "j") (.var "hi")) ρ =
            .ok (.b true) := by
          have h := evalExpr_ult_u64 _ _ _ _ _
            (evalExpr_var_hit _ _ _ hj_env)
            (evalExpr_var_hit _ _ _ hhi_env)
          have ht : (j.ult hi) = true := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_true hJ
          rwa [ht] at h
        exact (memEvalExpr_ult_agree _ _ _ _ _ hvarI hvarM).trans hE
      have hM : (hi.toNat - j.toNat) =
          ((hi.toNat - j.toNat) - 1) + 1 := by omega
      rw [hM] at hfwd
      have hgetJ : la[j.toNat]? = some la[j.toNat] :=
        List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hJ hhi_le)
      cases hgetK : lt[k.toNat]? with
      | none =>
        have hfwde : mergeRunsDrainJFwd la lt
            (((hi.toNat - j.toNat) - 1) + 1)
            j.toNat k.toNat hi.toNat = .error .AssertFail := by
          simp only [mergeRunsDrainJFwd, dite_eq_left hJ, hgetK]
        rw [hfwde] at hfwd
        cases hfwd
        have hltK : ¬ k.toNat < lt.length := by
          intro hc
          have hsome := List.getElem?_eq_getElem hc
          rw [hsome] at hgetK
          cases hgetK
        have hmemLen : memLoad m ab tb 0 =
            .ok (BitVec.ofNat 32 lt.length) := by
          rw [← hnB]
          exact memLoad_cellsAt m ab tb 0 (nB :: lt) nB hmem_b rfl
        have hbody := memRunsDrainJBody_miss prog F ρ m π la lt j k
          la[j.toNat] aa ab ta tb nA nB hlay_a hlay_tmp hmem_a hmem_b
          hmemLen hj_env hk_env ha_env htmp_env hgetJ hltK hlent
        have herr : memEvalProgStmt prog (F + 1) mergeRunsDrainJ
            ρ m π = .error .AssertFail := by
          simp only [mergeRunsDrainJ,
            memEvalProgStmt_while_true prog F _ _ _ _ _ hcond, hbody]
        exact herr
      | some w =>
        have hltK : k.toNat < lt.length :=
          list_lt_of_getElem?_some lt k.toNat w hgetK
        have hfwdI : mergeRunsDrainJFwd la (lt.set k.toNat la[j.toNat])
            ((hi.toNat - j.toNat) - 1)
            (j.toNat + 1) (k.toNat + 1) hi.toNat = .error e := by
          have h := hfwd
          simp only [mergeRunsDrainJFwd, dite_eq_left hJ, hgetK,
            hgetJ] at h
          exact h
        have hmemLen : memLoad m ab tb 0 =
            .ok (BitVec.ofNat 32 lt.length) := by
          rw [← hnB]
          exact memLoad_cellsAt m ab tb 0 (nB :: lt) nB hmem_b rfl
        have hlt1 : k.toNat + 1 < (nB :: lt).length := by
          simp only [List.length_cons]
          omega
        obtain ⟨m₁, hstore⟩ : ∃ m₁, memStore m ab tb
            (k.toNat + 1) la[j.toNat] = .ok m₁ :=
          ⟨_, memStore_cellsAt m ab tb (k.toNat + 1) (nB :: lt)
            la[j.toNat] hmem_b hlt1⟩
        obtain ⟨ρt, hu⟩ := envUpdate_some_of_lookup ρ "tmp"
          (.stdVecVal lt) (.stdVecVal (lt.set k.toNat la[j.toNat]))
          htmp_env
        have hlookJ' : envLookup ρt "j" = some (.u64 j) := by
          have h := envLookup_update_miss ρ "j" "tmp" _ ρt
            (by decide) hu
          rw [h, hj_env]
        obtain ⟨ρJ, huJ⟩ := envUpdate_some_of_lookup ρt "j"
          (.u64 j) (.u64 (j + 1)) hlookJ'
        have hlookK' : envLookup ρt "k" = some (.u64 k) := by
          have h := envLookup_update_miss ρ "k" "tmp" _ ρt
            (by decide) hu
          rw [h, hk_env]
        have hlookKI : envLookup ρJ "k" = some (.u64 k) := by
          have h := envLookup_update_miss ρt "k" "j" _ ρJ
            (by decide) huJ
          rw [h, hlookK']
        obtain ⟨ρK, huK⟩ := envUpdate_some_of_lookup ρJ "k"
          (.u64 k) (.u64 (k + 1)) hlookKI
        have hstep : memEvalProgStmt prog F mergeRunsDrainJBody
            ρ m π = .ok ((ρK, m₁, π), .fellThrough) :=
          memRunsDrainJBody_hit prog F ρ m π la lt j k la[j.toNat] w
            aa ab ta tb nA nB hlay_a hlay_tmp hmem_a hmem_b hmemLen
            hj_env hk_env ha_env htmp_env hgetJ hltK hlent hgetK _
            hstore _ hu _ _ huJ huK
        have hloop : memEvalProgStmt prog (F + 1) mergeRunsDrainJ
            ρ m π = memEvalProgStmt prog F mergeRunsDrainJ ρK m₁ π := by
          simp only [mergeRunsDrainJ,
            memEvalProgStmt_while_true prog F _ _ _ _ _ hcond, hstep]
        have h1j : (j + 1).toNat = j.toNat + 1 :=
          bv64_succ_toNat j _ hJ (by omega)
        have h1k : (k + 1).toNat = k.toNat + 1 :=
          bv64_succ_toNat k _ hltK hlent
        have hlent' : (lt.set k.toNat la[j.toNat]).length < 2 ^ 64 := by
          rw [List.length_set]
          exact hlent
        have hF' : (hi.toNat - (j + 1).toNat) + 1 ≤ F := by omega
        have hM' : (hi.toNat - j.toNat) - 1 =
            (hi.toNat - (j + 1).toNat) := by omega
        have hfwd' : mergeRunsDrainJFwd la (lt.set k.toNat la[j.toNat])
            (hi.toNat - (j + 1).toNat)
            ((j + 1).toNat) ((k + 1).toNat) hi.toNat = .error e := by
          rw [← h1j, ← h1k, hM'] at hfwdI
          exact hfwdI
        have hmem_a₁ : memFind m₁ aa = some ⟨ta, true, nA :: la⟩ := by
          have h := memFind_memStore_other m m₁ ab aa tb
            (k.toNat + 1) la[j.toNat] hstore haa
          rw [h]
          exact hmem_a
        have hmem_b₁ : memFind m₁ ab =
            some ⟨tb, true, nB :: lt.set k.toNat la[j.toNat]⟩ := by
          have hcells := memFind_cellsAt_store m ab tb (k.toNat + 1)
            (nB :: lt) la[j.toNat] m₁ hmem_b hlt1 hstore
          have hsetEq : (nB :: lt).set (k.toNat + 1) la[j.toNat] =
              nB :: lt.set k.toNat la[j.toNat] :=
            List.set_cons_succ
          rw [hsetEq] at hcells
          exact hcells
        have hnB₁ : nB =
            BitVec.ofNat 32 (lt.set k.toNat la[j.toNat]).length := by
          rw [List.length_set]
          exact hnB
        have hlookJK : envLookup ρJ "j" = some (.u64 (j + 1)) :=
          envLookup_update_hit ρt "j" _ ρJ huJ
        have hj_env₁ : envLookup ρK "j" = some (.u64 (j + 1)) := by
          have h := envLookup_update_miss ρJ "j" "k" _ ρK
            (by decide) huK
          rw [h, hlookJK]
        have hk_env₁ : envLookup ρK "k" = some (.u64 (k + 1)) :=
          envLookup_update_hit ρJ "k" _ ρK huK
        have ha_env₁ : envLookup ρK "a" = some (.stdVecVal la) := by
          have h1 := envLookup_update_miss ρJ "a" "k" _ ρK
            (by decide) huK
          have h2 := envLookup_update_miss ρt "a" "j" _ ρJ
            (by decide) huJ
          have h3 := envLookup_update_miss ρ "a" "tmp" _ ρt
            (by decide) hu
          rw [h1, h2, h3, ha_env]
        have hhi_env₁ : envLookup ρK "hi" = some (.u64 hi) := by
          have h1 := envLookup_update_miss ρJ "hi" "k" _ ρK
            (by decide) huK
          have h2 := envLookup_update_miss ρt "hi" "j" _ ρJ
            (by decide) huJ
          have h3 := envLookup_update_miss ρ "hi" "tmp" _ ρt
            (by decide) hu
          rw [h1, h2, h3, hhi_env]
        have htmp_env₁ : envLookup ρK "tmp" =
            some (.stdVecVal (lt.set k.toNat la[j.toNat])) := by
          have h1 := envLookup_update_miss ρJ "tmp" "k" _ ρK
            (by decide) huK
          have h2 := envLookup_update_miss ρt "tmp" "j" _ ρJ
            (by decide) huJ
          rw [h1, h2]
          exact envLookup_update_hit ρ "tmp" _ ρt hu
        rw [hloop]
        exact ih ρK m₁ π la (lt.set k.toNat la[j.toNat]) (j + 1)
          (k + 1) e hlay_a hlay_tmp hmem_a₁ hmem_b₁ hnB₁
          hj_env₁ hk_env₁ ha_env₁ hhi_env₁ htmp_env₁ hlent' hhi_le
          hF' hfwd'
    · have hcond : memEvalExpr (.ult (.var "j") (.var "hi")) ρ m π =
          .ok (.b false) := by
        have hvarI : memEvalExpr (.var "j") ρ m π =
            evalExpr (.var "j") ρ := memEvalExpr_var _ _ _ _
        have hvarM : memEvalExpr (.var "hi") ρ m π =
            evalExpr (.var "hi") ρ := memEvalExpr_var _ _ _ _
        have hE : evalExpr (.ult (.var "j") (.var "hi")) ρ =
            .ok (.b false) := by
          have h := evalExpr_ult_u64 _ _ _ _ _
            (evalExpr_var_hit _ _ _ hj_env)
            (evalExpr_var_hit _ _ _ hhi_env)
          have ht : (j.ult hi) = false := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_false hJ
          rwa [ht] at h
        exact (memEvalExpr_ult_agree _ _ _ _ _ hvarI hvarM).trans hE
      have hfwd0 : mergeRunsDrainJFwd la lt (hi.toNat - j.toNat)
          j.toNat k.toNat hi.toNat = .ok (j.toNat, k.toNat, lt) := by
        match hm : (hi.toNat - j.toNat) with
        | 0 => simp only [mergeRunsDrainJFwd]
        | _ + 1 =>
          simp only [mergeRunsDrainJFwd, dite_eq_right hJ]
      rw [hfwd0] at hfwd
      cases hfwd

/-- Drain-`j` ok soundness on memory: the loop copies `la[j..hi]`
    into `tmp` and exits with the forward-model state (fuel induction
    mirroring `mergeRunsDrainJ_ok`; the by-find blocks thread the
    shadowing snapshots, `memFind_memStore_other` keeps the `a` pin). -/
theorem memRunsDrainJ_ok (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (hi j k : BitVec 64)
    (j' k' : Nat) (lt' : List (BitVec 32))
    (aa ab : Addr) (ta tb : Nat) (nA nB : BitVec 32)
    (haa : aa ≠ ab)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_tmp : layoutLookup π "tmp" = some (ab, tb))
    (hmem_a : memFind m aa = some ⟨ta, true, nA :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nB :: lt⟩)
    (hnB : nB = BitVec.ofNat 32 lt.length)
    (hj_env : envLookup ρ "j" = some (.u64 j))
    (hk_env : envLookup ρ "k" = some (.u64 k))
    (ha_env : envLookup ρ "a" = some (.stdVecVal la))
    (hhi_env : envLookup ρ "hi" = some (.u64 hi))
    (htmp_env : envLookup ρ "tmp" = some (.stdVecVal lt))
    (hlent : lt.length < 2 ^ 64)
    (hhi_le : hi.toNat ≤ la.length)
    (hF : (hi.toNat - j.toNat) + 1 ≤ F)
    (hfwd : mergeRunsDrainJFwd la lt (hi.toNat - j.toNat)
      j.toNat k.toNat hi.toNat = .ok (j', k', lt')) :
    ∃ ρ' m', memEvalProgStmt prog F mergeRunsDrainJ ρ m π =
        .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "tmp" = some (.stdVecVal lt') ∧
      envLookup ρ' "j" = some (.u64 (BitVec.ofNat 64 j')) ∧
      envLookup ρ' "k" = some (.u64 (BitVec.ofNat 64 k')) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "hi" = some (.u64 hi) ∧
      memFind m' aa = some ⟨ta, true, nA :: la⟩ ∧
      memFind m' ab = some ⟨tb, true, nB :: lt'⟩ ∧
      nB = BitVec.ofNat 32 lt'.length := by
  induction F generalizing ρ m π la lt j k j' k' lt' with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hJ : j.toNat < hi.toNat
    · have hcond : memEvalExpr (.ult (.var "j") (.var "hi")) ρ m π =
          .ok (.b true) := by
        have hvarI : memEvalExpr (.var "j") ρ m π =
            evalExpr (.var "j") ρ := memEvalExpr_var _ _ _ _
        have hvarM : memEvalExpr (.var "hi") ρ m π =
            evalExpr (.var "hi") ρ := memEvalExpr_var _ _ _ _
        have hE : evalExpr (.ult (.var "j") (.var "hi")) ρ =
            .ok (.b true) := by
          have h := evalExpr_ult_u64 _ _ _ _ _
            (evalExpr_var_hit _ _ _ hj_env)
            (evalExpr_var_hit _ _ _ hhi_env)
          have ht : (j.ult hi) = true := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_true hJ
          rwa [ht] at h
        exact (memEvalExpr_ult_agree _ _ _ _ _ hvarI hvarM).trans hE
      have hM : (hi.toNat - j.toNat) =
          ((hi.toNat - j.toNat) - 1) + 1 := by omega
      rw [hM] at hfwd
      have hgetJ : la[j.toNat]? = some la[j.toNat] :=
        List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hJ hhi_le)
      cases hgetK : lt[k.toNat]? with
      | none =>
        have hcontra : mergeRunsDrainJFwd la lt
            (((hi.toNat - j.toNat) - 1) + 1)
            j.toNat k.toNat hi.toNat = .error .AssertFail := by
          simp only [mergeRunsDrainJFwd, dite_eq_left hJ, hgetK]
        rw [hcontra] at hfwd
        cases hfwd
      | some w =>
        have hltK : k.toNat < lt.length :=
          list_lt_of_getElem?_some lt k.toNat w hgetK
        have hfwdI : mergeRunsDrainJFwd la (lt.set k.toNat la[j.toNat])
            ((hi.toNat - j.toNat) - 1)
            (j.toNat + 1) (k.toNat + 1) hi.toNat =
            .ok (j', k', lt') := by
          have h := hfwd
          simp only [mergeRunsDrainJFwd, dite_eq_left hJ, hgetK,
            hgetJ] at h
          exact h
        have hmemLen : memLoad m ab tb 0 =
            .ok (BitVec.ofNat 32 lt.length) := by
          rw [← hnB]
          exact memLoad_cellsAt m ab tb 0 (nB :: lt) nB hmem_b rfl
        have hlt1 : k.toNat + 1 < (nB :: lt).length := by
          simp only [List.length_cons]
          omega
        obtain ⟨m₁, hstore⟩ : ∃ m₁, memStore m ab tb
            (k.toNat + 1) la[j.toNat] = .ok m₁ :=
          ⟨_, memStore_cellsAt m ab tb (k.toNat + 1) (nB :: lt)
            la[j.toNat] hmem_b hlt1⟩
        obtain ⟨ρt, hu⟩ := envUpdate_some_of_lookup ρ "tmp"
          (.stdVecVal lt) (.stdVecVal (lt.set k.toNat la[j.toNat]))
          htmp_env
        have hlookJ' : envLookup ρt "j" = some (.u64 j) := by
          have h := envLookup_update_miss ρ "j" "tmp" _ ρt
            (by decide) hu
          rw [h, hj_env]
        obtain ⟨ρJ, huJ⟩ := envUpdate_some_of_lookup ρt "j"
          (.u64 j) (.u64 (j + 1)) hlookJ'
        have hlookK' : envLookup ρt "k" = some (.u64 k) := by
          have h := envLookup_update_miss ρ "k" "tmp" _ ρt
            (by decide) hu
          rw [h, hk_env]
        have hlookKI : envLookup ρJ "k" = some (.u64 k) := by
          have h := envLookup_update_miss ρt "k" "j" _ ρJ
            (by decide) huJ
          rw [h, hlookK']
        obtain ⟨ρK, huK⟩ := envUpdate_some_of_lookup ρJ "k"
          (.u64 k) (.u64 (k + 1)) hlookKI
        have hstep : memEvalProgStmt prog F mergeRunsDrainJBody
            ρ m π = .ok ((ρK, m₁, π), .fellThrough) :=
          memRunsDrainJBody_hit prog F ρ m π la lt j k la[j.toNat] w
            aa ab ta tb nA nB hlay_a hlay_tmp hmem_a hmem_b hmemLen
            hj_env hk_env ha_env htmp_env hgetJ hltK hlent hgetK _
            hstore _ hu _ _ huJ huK
        have hloop : memEvalProgStmt prog (F + 1) mergeRunsDrainJ
            ρ m π = memEvalProgStmt prog F mergeRunsDrainJ ρK m₁ π := by
          simp only [mergeRunsDrainJ,
            memEvalProgStmt_while_true prog F _ _ _ _ _ hcond, hstep]
        have h1j : (j + 1).toNat = j.toNat + 1 :=
          bv64_succ_toNat j _ hJ (by omega)
        have h1k : (k + 1).toNat = k.toNat + 1 :=
          bv64_succ_toNat k _ hltK hlent
        have hlent' : (lt.set k.toNat la[j.toNat]).length < 2 ^ 64 := by
          rw [List.length_set]
          exact hlent
        have hF' : (hi.toNat - (j + 1).toNat) + 1 ≤ F := by omega
        have hM' : (hi.toNat - j.toNat) - 1 =
            (hi.toNat - (j + 1).toNat) := by omega
        have hfwd' : mergeRunsDrainJFwd la (lt.set k.toNat la[j.toNat])
            (hi.toNat - (j + 1).toNat)
            ((j + 1).toNat) ((k + 1).toNat) hi.toNat =
            .ok (j', k', lt') := by
          rw [← h1j, ← h1k, hM'] at hfwdI
          exact hfwdI
        have hmem_a₁ : memFind m₁ aa = some ⟨ta, true, nA :: la⟩ := by
          have h := memFind_memStore_other m m₁ ab aa tb
            (k.toNat + 1) la[j.toNat] hstore haa
          rw [h]
          exact hmem_a
        have hmem_b₁ : memFind m₁ ab =
            some ⟨tb, true, nB :: lt.set k.toNat la[j.toNat]⟩ := by
          have hcells := memFind_cellsAt_store m ab tb (k.toNat + 1)
            (nB :: lt) la[j.toNat] m₁ hmem_b hlt1 hstore
          have hsetEq : (nB :: lt).set (k.toNat + 1) la[j.toNat] =
              nB :: lt.set k.toNat la[j.toNat] :=
            List.set_cons_succ
          rw [hsetEq] at hcells
          exact hcells
        have hnB₁ : nB =
            BitVec.ofNat 32 (lt.set k.toNat la[j.toNat]).length := by
          rw [List.length_set]
          exact hnB
        have hlookJK : envLookup ρJ "j" = some (.u64 (j + 1)) :=
          envLookup_update_hit ρt "j" _ ρJ huJ
        have hj_env₁ : envLookup ρK "j" = some (.u64 (j + 1)) := by
          have h := envLookup_update_miss ρJ "j" "k" _ ρK
            (by decide) huK
          rw [h, hlookJK]
        have hk_env₁ : envLookup ρK "k" = some (.u64 (k + 1)) :=
          envLookup_update_hit ρJ "k" _ ρK huK
        have ha_env₁ : envLookup ρK "a" = some (.stdVecVal la) := by
          have h1 := envLookup_update_miss ρJ "a" "k" _ ρK
            (by decide) huK
          have h2 := envLookup_update_miss ρt "a" "j" _ ρJ
            (by decide) huJ
          have h3 := envLookup_update_miss ρ "a" "tmp" _ ρt
            (by decide) hu
          rw [h1, h2, h3, ha_env]
        have hhi_env₁ : envLookup ρK "hi" = some (.u64 hi) := by
          have h1 := envLookup_update_miss ρJ "hi" "k" _ ρK
            (by decide) huK
          have h2 := envLookup_update_miss ρt "hi" "j" _ ρJ
            (by decide) huJ
          have h3 := envLookup_update_miss ρ "hi" "tmp" _ ρt
            (by decide) hu
          rw [h1, h2, h3, hhi_env]
        have htmp_env₁ : envLookup ρK "tmp" =
            some (.stdVecVal (lt.set k.toNat la[j.toNat])) := by
          have h1 := envLookup_update_miss ρJ "tmp" "k" _ ρK
            (by decide) huK
          have h2 := envLookup_update_miss ρt "tmp" "j" _ ρJ
            (by decide) huJ
          rw [h1, h2]
          exact envLookup_update_hit ρ "tmp" _ ρt hu
        rw [hloop]
        exact ih ρK m₁ π la (lt.set k.toNat la[j.toNat]) (j + 1)
          (k + 1) j' k' lt' hlay_a hlay_tmp hmem_a₁ hmem_b₁ hnB₁
          hj_env₁ hk_env₁ ha_env₁ hhi_env₁ htmp_env₁ hlent' hhi_le
          hF' hfwd'
    · have hcond : memEvalExpr (.ult (.var "j") (.var "hi")) ρ m π =
          .ok (.b false) := by
        have hvarI : memEvalExpr (.var "j") ρ m π =
            evalExpr (.var "j") ρ := memEvalExpr_var _ _ _ _
        have hvarM : memEvalExpr (.var "hi") ρ m π =
            evalExpr (.var "hi") ρ := memEvalExpr_var _ _ _ _
        have hE : evalExpr (.ult (.var "j") (.var "hi")) ρ =
            .ok (.b false) := by
          have h := evalExpr_ult_u64 _ _ _ _ _
            (evalExpr_var_hit _ _ _ hj_env)
            (evalExpr_var_hit _ _ _ hhi_env)
          have ht : (j.ult hi) = false := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_false hJ
          rwa [ht] at h
        exact (memEvalExpr_ult_agree _ _ _ _ _ hvarI hvarM).trans hE
      have hfwd0 : mergeRunsDrainJFwd la lt (hi.toNat - j.toNat)
          j.toNat k.toNat hi.toNat = .ok (j.toNat, k.toNat, lt) := by
        match hm : (hi.toNat - j.toNat) with
        | 0 => simp only [mergeRunsDrainJFwd]
        | _ + 1 =>
          simp only [mergeRunsDrainJFwd, dite_eq_right hJ]
      rw [hfwd0] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hfwd
      have hexit : memEvalProgStmt prog (F + 1) mergeRunsDrainJ
          ρ m π = .ok ((ρ, m, π), .fellThrough) := by
        simp only [mergeRunsDrainJ,
          memEvalProgStmt_while_false prog _ _ _ _ _ _ hcond]
      refine ⟨ρ, m, hexit, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact htmp_env
      · have hto : BitVec.ofNat 64 j.toNat = j := bv64_ofNat_toNat j
        rw [hto]
        exact hj_env
      · have hto : BitVec.ofNat 64 k.toNat = k := bv64_ofNat_toNat k
        rw [hto]
        exact hk_env
      · exact ha_env
      · exact hhi_env
      · exact hmem_a
      · exact hmem_b
      · exact hnB

/-- Main-loop ok soundness on memory: the merge loop copies both runs
    into `tmp` and exits with the forward-model state (fuel induction
    mirroring `mergeRunsMain_ok`; the guard is the short-circuit `tif`,
    the live step splits on `slt` into the two body mirrors). -/
theorem memRunsMain_ok (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (mid hi i j k : BitVec 64)
    (i' j' k' : Nat) (lt' : List (BitVec 32))
    (aa ab : Addr) (ta tb : Nat) (nA nB : BitVec 32)
    (haa : aa ≠ ab)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_tmp : layoutLookup π "tmp" = some (ab, tb))
    (hmem_a : memFind m aa = some ⟨ta, true, nA :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nB :: lt⟩)
    (hnB : nB = BitVec.ofNat 32 lt.length)
    (hi_env : envLookup ρ "i" = some (.u64 i))
    (hj_env : envLookup ρ "j" = some (.u64 j))
    (hk_env : envLookup ρ "k" = some (.u64 k))
    (ha_env : envLookup ρ "a" = some (.stdVecVal la))
    (hmid_env : envLookup ρ "mid" = some (.u64 mid))
    (hhi_env : envLookup ρ "hi" = some (.u64 hi))
    (htmp_env : envLookup ρ "tmp" = some (.stdVecVal lt))
    (hlent : lt.length < 2 ^ 64)
    (hmid_le : mid.toNat ≤ la.length) (hhi_le : hi.toNat ≤ la.length)
    (hF : (mid.toNat - i.toNat) + (hi.toNat - j.toNat) + 1 ≤ F)
    (hfwd : mergeRunsMainFwd la lt
      ((mid.toNat - i.toNat) + (hi.toNat - j.toNat))
      i.toNat j.toNat k.toNat mid.toNat hi.toNat =
      .ok (i', j', k', lt')) :
    ∃ ρ' m', memEvalProgStmt prog F mergeRunsMain ρ m π =
        .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "tmp" = some (.stdVecVal lt') ∧
      envLookup ρ' "i" = some (.u64 (BitVec.ofNat 64 i')) ∧
      envLookup ρ' "j" = some (.u64 (BitVec.ofNat 64 j')) ∧
      envLookup ρ' "k" = some (.u64 (BitVec.ofNat 64 k')) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "mid" = some (.u64 mid) ∧
      envLookup ρ' "hi" = some (.u64 hi) ∧
      memFind m' aa = some ⟨ta, true, nA :: la⟩ ∧
      memFind m' ab = some ⟨tb, true, nB :: lt'⟩ ∧
      nB = BitVec.ofNat 32 lt'.length := by
  induction F generalizing ρ m π la lt i j k i' j' k' lt' with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hguard : (i.toNat < mid.toNat ∧ j.toNat < hi.toNat)
    · obtain ⟨hI, hJ⟩ := hguard
      have hvarI : memEvalExpr (.var "i") ρ m π =
          evalExpr (.var "i") ρ := memEvalExpr_var _ _ _ _
      have hvarM : memEvalExpr (.var "mid") ρ m π =
          evalExpr (.var "mid") ρ := memEvalExpr_var _ _ _ _
      have hvarJ : memEvalExpr (.var "j") ρ m π =
          evalExpr (.var "j") ρ := memEvalExpr_var _ _ _ _
      have hvarH : memEvalExpr (.var "hi") ρ m π =
          evalExpr (.var "hi") ρ := memEvalExpr_var _ _ _ _
      have hag1 : memEvalExpr (.ult (.var "i") (.var "mid")) ρ m π =
          evalExpr (.ult (.var "i") (.var "mid")) ρ :=
        memEvalExpr_ult_agree _ _ _ _ _ hvarI hvarM
      have hc1 : evalExpr (.ult (.var "i") (.var "mid")) ρ =
          .ok (.b true) := by
        have h := evalExpr_ult_u64 _ _ _ _ _
          (evalExpr_var_hit _ _ _ hi_env)
          (evalExpr_var_hit _ _ _ hmid_env)
        have ht : (i.ult mid) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true hI
        rwa [ht] at h
      have hag2 : memEvalExpr (.ult (.var "j") (.var "hi")) ρ m π =
          evalExpr (.ult (.var "j") (.var "hi")) ρ :=
        memEvalExpr_ult_agree _ _ _ _ _ hvarJ hvarH
      have hc2 : evalExpr (.ult (.var "j") (.var "hi")) ρ =
          .ok (.b true) := by
        have h := evalExpr_ult_u64 _ _ _ _ _
          (evalExpr_var_hit _ _ _ hj_env)
          (evalExpr_var_hit _ _ _ hhi_env)
        have ht : (j.ult hi) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true hJ
        rwa [ht] at h
      have hE : evalExpr
          (.tif (.ult (.var "i") (.var "mid"))
            (.ult (.var "j") (.var "hi"))
            (.lit (.b false))) ρ = .ok (.b true) := by
        rw [evalExpr_tif_true _ _ _ _ hc1]
        exact hc2
      have hcond : memEvalExpr
          (.tif (.ult (.var "i") (.var "mid"))
            (.ult (.var "j") (.var "hi"))
            (.lit (.b false))) ρ m π = .ok (.b true) :=
        (memEvalExpr_tif_true _ _ _ _ _ _ hag1 hc1 hag2).trans hE
      have hM : (mid.toNat - i.toNat) + (hi.toNat - j.toNat) =
          ((mid.toNat - i.toNat) + (hi.toNat - j.toNat) - 1) + 1 := by
        omega
      rw [hM] at hfwd
      have hgetI : la[i.toNat]? = some la[i.toNat] :=
        List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hI hmid_le)
      have hgetJ : la[j.toNat]? = some la[j.toNat] :=
        List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hJ hhi_le)
      cases hgetK : lt[k.toNat]? with
      | none =>
        have hcontra : mergeRunsMainFwd la lt
            (((mid.toNat - i.toNat) + (hi.toNat - j.toNat) - 1) + 1)
            i.toNat j.toNat k.toNat mid.toNat hi.toNat =
            .error .AssertFail := by
          simp only [mergeRunsMainFwd, dite_eq_left hI, dite_eq_left hJ,
            hgetK]
        rw [hcontra] at hfwd
        cases hfwd
      | some w =>
        have hltK : k.toNat < lt.length :=
          list_lt_of_getElem?_some lt k.toNat w hgetK
        have hmemLen : memLoad m ab tb 0 =
            .ok (BitVec.ofNat 32 lt.length) := by
          rw [← hnB]
          exact memLoad_cellsAt m ab tb 0 (nB :: lt) nB hmem_b rfl
        have hlt1 : k.toNat + 1 < (nB :: lt).length := by
          simp only [List.length_cons]
          omega
        have h1k : (k + 1).toNat = k.toNat + 1 :=
          bv64_succ_toNat k _ hltK hlent
        by_cases hslt : (la[i.toNat].slt la[j.toNat]) = true
        · have hfwdI : mergeRunsMainFwd la (lt.set k.toNat la[i.toNat])
              ((mid.toNat - i.toNat) + (hi.toNat - j.toNat) - 1)
              (i.toNat + 1) j.toNat (k.toNat + 1) mid.toNat hi.toNat =
              .ok (i', j', k', lt') := by
            have h := hfwd
            simp only [mergeRunsMainFwd, dite_eq_left hI,
              dite_eq_left hJ, hgetK, hgetI, hgetJ, hslt] at h
            exact h
          obtain ⟨m₁, hstore⟩ : ∃ m₁, memStore m ab tb
              (k.toNat + 1) la[i.toNat] = .ok m₁ :=
            ⟨_, memStore_cellsAt m ab tb (k.toNat + 1) (nB :: lt)
              la[i.toNat] hmem_b hlt1⟩
          obtain ⟨ρt, hu⟩ := envUpdate_some_of_lookup ρ "tmp"
            (.stdVecVal lt) (.stdVecVal (lt.set k.toNat la[i.toNat]))
            htmp_env
          have hlookI' : envLookup ρt "i" = some (.u64 i) := by
            have h := envLookup_update_miss ρ "i" "tmp" _ ρt
              (by decide) hu
            rw [h, hi_env]
          obtain ⟨ρI, huI⟩ := envUpdate_some_of_lookup ρt "i"
            (.u64 i) (.u64 (i + 1)) hlookI'
          have hlookK' : envLookup ρt "k" = some (.u64 k) := by
            have h := envLookup_update_miss ρ "k" "tmp" _ ρt
              (by decide) hu
            rw [h, hk_env]
          have hlookKI : envLookup ρI "k" = some (.u64 k) := by
            have h := envLookup_update_miss ρt "k" "i" _ ρI
              (by decide) huI
            rw [h, hlookK']
          obtain ⟨ρK, huK⟩ := envUpdate_some_of_lookup ρI "k"
            (.u64 k) (.u64 (k + 1)) hlookKI
          have hstep : memEvalProgStmt prog F mergeRunsMainBody
              ρ m π = .ok ((ρK, m₁, π), .fellThrough) :=
            memRunsMainBody_hitI prog F ρ m π la lt i j k
              la[i.toNat] la[j.toNat] w
              aa ab ta tb nA nB
              hlay_a hlay_tmp hmem_a hmem_b hmemLen
              hi_env hj_env hk_env ha_env htmp_env
              hgetI hgetJ hslt hltK hlent hgetK _ hstore _ hu _ _ huI huK
          have hloop : memEvalProgStmt prog (F + 1) mergeRunsMain
              ρ m π =
              memEvalProgStmt prog F mergeRunsMain ρK m₁ π := by
            simp only [mergeRunsMain,
              memEvalProgStmt_while_true prog F _ _ _ _ _ hcond, hstep]
          have h1i : (i + 1).toNat = i.toNat + 1 :=
            bv64_succ_toNat i _ hI (by omega)
          have hlent' : (lt.set k.toNat la[i.toNat]).length < 2 ^ 64 := by
            rw [List.length_set]
            exact hlent
          have hF' : (mid.toNat - (i + 1).toNat) +
              (hi.toNat - j.toNat) + 1 ≤ F := by omega
          have hM' : (mid.toNat - i.toNat) + (hi.toNat - j.toNat) - 1 =
              (mid.toNat - (i + 1).toNat) + (hi.toNat - j.toNat) := by
            omega
          have hfwd' : mergeRunsMainFwd la (lt.set k.toNat la[i.toNat])
              ((mid.toNat - (i + 1).toNat) + (hi.toNat - j.toNat))
              ((i + 1).toNat) j.toNat ((k + 1).toNat)
              mid.toNat hi.toNat =
              .ok (i', j', k', lt') := by
            rw [← h1i, ← h1k, hM'] at hfwdI
            exact hfwdI
          have hmem_a₁ : memFind m₁ aa = some ⟨ta, true, nA :: la⟩ := by
            have h := memFind_memStore_other m m₁ ab aa tb
              (k.toNat + 1) la[i.toNat] hstore haa
            rw [h]
            exact hmem_a
          have hmem_b₁ : memFind m₁ ab =
              some ⟨tb, true, nB :: lt.set k.toNat la[i.toNat]⟩ := by
            have hcells := memFind_cellsAt_store m ab tb (k.toNat + 1)
              (nB :: lt) la[i.toNat] m₁ hmem_b hlt1 hstore
            have hsetEq : (nB :: lt).set (k.toNat + 1) la[i.toNat] =
                nB :: lt.set k.toNat la[i.toNat] :=
              List.set_cons_succ
            rw [hsetEq] at hcells
            exact hcells
          have hnB₁ : nB =
              BitVec.ofNat 32 (lt.set k.toNat la[i.toNat]).length := by
            rw [List.length_set]
            exact hnB
          have hlookIK : envLookup ρI "i" = some (.u64 (i + 1)) :=
            envLookup_update_hit ρt "i" _ ρI huI
          have hi_env₁ : envLookup ρK "i" = some (.u64 (i + 1)) := by
            have h := envLookup_update_miss ρI "i" "k" _ ρK
              (by decide) huK
            rw [h, hlookIK]
          have hk_env₁ : envLookup ρK "k" = some (.u64 (k + 1)) :=
            envLookup_update_hit ρI "k" _ ρK huK
          have hj_env₁ : envLookup ρK "j" = some (.u64 j) := by
            have h1 := envLookup_update_miss ρI "j" "k" _ ρK
              (by decide) huK
            have h2 := envLookup_update_miss ρt "j" "i" _ ρI
              (by decide) huI
            have h3 := envLookup_update_miss ρ "j" "tmp" _ ρt
              (by decide) hu
            rw [h1, h2, h3, hj_env]
          have ha_env₁ : envLookup ρK "a" = some (.stdVecVal la) := by
            have h1 := envLookup_update_miss ρI "a" "k" _ ρK
              (by decide) huK
            have h2 := envLookup_update_miss ρt "a" "i" _ ρI
              (by decide) huI
            have h3 := envLookup_update_miss ρ "a" "tmp" _ ρt
              (by decide) hu
            rw [h1, h2, h3, ha_env]
          have hmid_env₁ : envLookup ρK "mid" = some (.u64 mid) := by
            have h1 := envLookup_update_miss ρI "mid" "k" _ ρK
              (by decide) huK
            have h2 := envLookup_update_miss ρt "mid" "i" _ ρI
              (by decide) huI
            have h3 := envLookup_update_miss ρ "mid" "tmp" _ ρt
              (by decide) hu
            rw [h1, h2, h3, hmid_env]
          have hhi_env₁ : envLookup ρK "hi" = some (.u64 hi) := by
            have h1 := envLookup_update_miss ρI "hi" "k" _ ρK
              (by decide) huK
            have h2 := envLookup_update_miss ρt "hi" "i" _ ρI
              (by decide) huI
            have h3 := envLookup_update_miss ρ "hi" "tmp" _ ρt
              (by decide) hu
            rw [h1, h2, h3, hhi_env]
          have htmp_env₁ : envLookup ρK "tmp" =
              some (.stdVecVal (lt.set k.toNat la[i.toNat])) := by
            have h1 := envLookup_update_miss ρI "tmp" "k" _ ρK
              (by decide) huK
            have h2 := envLookup_update_miss ρt "tmp" "i" _ ρI
              (by decide) huI
            rw [h1, h2]
            exact envLookup_update_hit ρ "tmp" _ ρt hu
          rw [hloop]
          exact ih ρK m₁ π la (lt.set k.toNat la[i.toNat]) (i + 1)
            j (k + 1) i' j' k' lt' hlay_a hlay_tmp hmem_a₁ hmem_b₁
            hnB₁ hi_env₁ hj_env₁ hk_env₁ ha_env₁ hmid_env₁ hhi_env₁
            htmp_env₁ hlent' hmid_le hhi_le hF' hfwd'
        · have hsltF : (la[i.toNat].slt la[j.toNat]) = false :=
            Bool.eq_false_of_ne_true hslt
          have hfwdJ : mergeRunsMainFwd la (lt.set k.toNat la[j.toNat])
              ((mid.toNat - i.toNat) + (hi.toNat - j.toNat) - 1)
              i.toNat (j.toNat + 1) (k.toNat + 1) mid.toNat hi.toNat =
              .ok (i', j', k', lt') := by
            have h := hfwd
            simp only [mergeRunsMainFwd, dite_eq_left hI,
              dite_eq_left hJ, hgetK, hgetI, hgetJ, hsltF] at h
            exact h
          obtain ⟨m₁, hstore⟩ : ∃ m₁, memStore m ab tb
              (k.toNat + 1) la[j.toNat] = .ok m₁ :=
            ⟨_, memStore_cellsAt m ab tb (k.toNat + 1) (nB :: lt)
              la[j.toNat] hmem_b hlt1⟩
          obtain ⟨ρt, hu⟩ := envUpdate_some_of_lookup ρ "tmp"
            (.stdVecVal lt) (.stdVecVal (lt.set k.toNat la[j.toNat]))
            htmp_env
          have hlookJ' : envLookup ρt "j" = some (.u64 j) := by
            have h := envLookup_update_miss ρ "j" "tmp" _ ρt
              (by decide) hu
            rw [h, hj_env]
          obtain ⟨ρJ, huJ⟩ := envUpdate_some_of_lookup ρt "j"
            (.u64 j) (.u64 (j + 1)) hlookJ'
          have hlookK' : envLookup ρt "k" = some (.u64 k) := by
            have h := envLookup_update_miss ρ "k" "tmp" _ ρt
              (by decide) hu
            rw [h, hk_env]
          have hlookKJ : envLookup ρJ "k" = some (.u64 k) := by
            have h := envLookup_update_miss ρt "k" "j" _ ρJ
              (by decide) huJ
            rw [h, hlookK']
          obtain ⟨ρK, huK⟩ := envUpdate_some_of_lookup ρJ "k"
            (.u64 k) (.u64 (k + 1)) hlookKJ
          have hstep : memEvalProgStmt prog F mergeRunsMainBody
              ρ m π = .ok ((ρK, m₁, π), .fellThrough) :=
            memRunsMainBody_hitJ prog F ρ m π la lt i j k
              la[i.toNat] la[j.toNat] w
              aa ab ta tb nA nB
              hlay_a hlay_tmp hmem_a hmem_b hmemLen
              hi_env hj_env hk_env ha_env htmp_env
              hgetI hgetJ hsltF hltK hlent hgetK _ hstore _ hu _ _ huJ huK
          have hloop : memEvalProgStmt prog (F + 1) mergeRunsMain
              ρ m π =
              memEvalProgStmt prog F mergeRunsMain ρK m₁ π := by
            simp only [mergeRunsMain,
              memEvalProgStmt_while_true prog F _ _ _ _ _ hcond, hstep]
          have h1j : (j + 1).toNat = j.toNat + 1 :=
            bv64_succ_toNat j _ hJ (by omega)
          have hlent' : (lt.set k.toNat la[j.toNat]).length < 2 ^ 64 := by
            rw [List.length_set]
            exact hlent
          have hF' : (mid.toNat - i.toNat) +
              (hi.toNat - (j + 1).toNat) + 1 ≤ F := by omega
          have hM' : (mid.toNat - i.toNat) + (hi.toNat - j.toNat) - 1 =
              (mid.toNat - i.toNat) + (hi.toNat - (j + 1).toNat) := by
            omega
          have hfwd' : mergeRunsMainFwd la (lt.set k.toNat la[j.toNat])
              ((mid.toNat - i.toNat) + (hi.toNat - (j + 1).toNat))
              i.toNat ((j + 1).toNat) ((k + 1).toNat)
              mid.toNat hi.toNat =
              .ok (i', j', k', lt') := by
            rw [← h1j, ← h1k, hM'] at hfwdJ
            exact hfwdJ
          have hmem_a₁ : memFind m₁ aa = some ⟨ta, true, nA :: la⟩ := by
            have h := memFind_memStore_other m m₁ ab aa tb
              (k.toNat + 1) la[j.toNat] hstore haa
            rw [h]
            exact hmem_a
          have hmem_b₁ : memFind m₁ ab =
              some ⟨tb, true, nB :: lt.set k.toNat la[j.toNat]⟩ := by
            have hcells := memFind_cellsAt_store m ab tb (k.toNat + 1)
              (nB :: lt) la[j.toNat] m₁ hmem_b hlt1 hstore
            have hsetEq : (nB :: lt).set (k.toNat + 1) la[j.toNat] =
                nB :: lt.set k.toNat la[j.toNat] :=
              List.set_cons_succ
            rw [hsetEq] at hcells
            exact hcells
          have hnB₁ : nB =
              BitVec.ofNat 32 (lt.set k.toNat la[j.toNat]).length := by
            rw [List.length_set]
            exact hnB
          have hlookJK : envLookup ρJ "j" = some (.u64 (j + 1)) :=
            envLookup_update_hit ρt "j" _ ρJ huJ
          have hj_env₁ : envLookup ρK "j" = some (.u64 (j + 1)) := by
            have h := envLookup_update_miss ρJ "j" "k" _ ρK
              (by decide) huK
            rw [h, hlookJK]
          have hk_env₁ : envLookup ρK "k" = some (.u64 (k + 1)) :=
            envLookup_update_hit ρJ "k" _ ρK huK
          have hi_env₁ : envLookup ρK "i" = some (.u64 i) := by
            have h1 := envLookup_update_miss ρJ "i" "k" _ ρK
              (by decide) huK
            have h2 := envLookup_update_miss ρt "i" "j" _ ρJ
              (by decide) huJ
            have h3 := envLookup_update_miss ρ "i" "tmp" _ ρt
              (by decide) hu
            rw [h1, h2, h3, hi_env]
          have ha_env₁ : envLookup ρK "a" = some (.stdVecVal la) := by
            have h1 := envLookup_update_miss ρJ "a" "k" _ ρK
              (by decide) huK
            have h2 := envLookup_update_miss ρt "a" "j" _ ρJ
              (by decide) huJ
            have h3 := envLookup_update_miss ρ "a" "tmp" _ ρt
              (by decide) hu
            rw [h1, h2, h3, ha_env]
          have hmid_env₁ : envLookup ρK "mid" = some (.u64 mid) := by
            have h1 := envLookup_update_miss ρJ "mid" "k" _ ρK
              (by decide) huK
            have h2 := envLookup_update_miss ρt "mid" "j" _ ρJ
              (by decide) huJ
            have h3 := envLookup_update_miss ρ "mid" "tmp" _ ρt
              (by decide) hu
            rw [h1, h2, h3, hmid_env]
          have hhi_env₁ : envLookup ρK "hi" = some (.u64 hi) := by
            have h1 := envLookup_update_miss ρJ "hi" "k" _ ρK
              (by decide) huK
            have h2 := envLookup_update_miss ρt "hi" "j" _ ρJ
              (by decide) huJ
            have h3 := envLookup_update_miss ρ "hi" "tmp" _ ρt
              (by decide) hu
            rw [h1, h2, h3, hhi_env]
          have htmp_env₁ : envLookup ρK "tmp" =
              some (.stdVecVal (lt.set k.toNat la[j.toNat])) := by
            have h1 := envLookup_update_miss ρJ "tmp" "k" _ ρK
              (by decide) huK
            have h2 := envLookup_update_miss ρt "tmp" "j" _ ρJ
              (by decide) huJ
            rw [h1, h2]
            exact envLookup_update_hit ρ "tmp" _ ρt hu
          rw [hloop]
          exact ih ρK m₁ π la (lt.set k.toNat la[j.toNat]) i
            (j + 1) (k + 1) i' j' k' lt' hlay_a hlay_tmp hmem_a₁
            hmem_b₁ hnB₁ hi_env₁ hj_env₁ hk_env₁ ha_env₁ hmid_env₁
            hhi_env₁ htmp_env₁ hlent' hmid_le hhi_le hF' hfwd'
    · have hcond : memEvalExpr
          (.tif (.ult (.var "i") (.var "mid"))
            (.ult (.var "j") (.var "hi"))
            (.lit (.b false))) ρ m π = .ok (.b false) := by
        have hvarI : memEvalExpr (.var "i") ρ m π =
            evalExpr (.var "i") ρ := memEvalExpr_var _ _ _ _
        have hvarM : memEvalExpr (.var "mid") ρ m π =
            evalExpr (.var "mid") ρ := memEvalExpr_var _ _ _ _
        have hvarJ : memEvalExpr (.var "j") ρ m π =
            evalExpr (.var "j") ρ := memEvalExpr_var _ _ _ _
        have hvarH : memEvalExpr (.var "hi") ρ m π =
            evalExpr (.var "hi") ρ := memEvalExpr_var _ _ _ _
        have hag1 : memEvalExpr (.ult (.var "i") (.var "mid")) ρ m π =
            evalExpr (.ult (.var "i") (.var "mid")) ρ :=
          memEvalExpr_ult_agree _ _ _ _ _ hvarI hvarM
        have hag2 : memEvalExpr (.ult (.var "j") (.var "hi")) ρ m π =
            evalExpr (.ult (.var "j") (.var "hi")) ρ :=
          memEvalExpr_ult_agree _ _ _ _ _ hvarJ hvarH
        have heag : memEvalExpr (.lit (.b false)) ρ m π =
            evalExpr (.lit (.b false)) ρ :=
          memEvalExpr_lit _ _ _ _
        by_cases hI' : i.toNat < mid.toNat
        · have hnJ : ¬ j.toNat < hi.toNat :=
            fun hj => hguard ⟨hI', hj⟩
          have hc1 : evalExpr (.ult (.var "i") (.var "mid")) ρ =
              .ok (.b true) := by
            have h := evalExpr_ult_u64 _ _ _ _ _
              (evalExpr_var_hit _ _ _ hi_env)
              (evalExpr_var_hit _ _ _ hmid_env)
            have ht : (i.ult mid) = true := by
              rw [BitVec.ult_eq_decide]
              exact decide_eq_true hI'
            rwa [ht] at h
          have hc2 : evalExpr (.ult (.var "j") (.var "hi")) ρ =
              .ok (.b false) := by
            have h := evalExpr_ult_u64 _ _ _ _ _
              (evalExpr_var_hit _ _ _ hj_env)
              (evalExpr_var_hit _ _ _ hhi_env)
            have ht : (j.ult hi) = false := by
              rw [BitVec.ult_eq_decide]
              exact decide_eq_false hnJ
            rwa [ht] at h
          have hE : evalExpr
              (.tif (.ult (.var "i") (.var "mid"))
                (.ult (.var "j") (.var "hi"))
                (.lit (.b false))) ρ = .ok (.b false) := by
            rw [evalExpr_tif_true _ _ _ _ hc1]
            exact hc2
          exact (memEvalExpr_tif_true _ _ _ _ _ _ hag1 hc1 hag2).trans hE
        · have hc1 : evalExpr (.ult (.var "i") (.var "mid")) ρ =
              .ok (.b false) := by
            have h := evalExpr_ult_u64 _ _ _ _ _
              (evalExpr_var_hit _ _ _ hi_env)
              (evalExpr_var_hit _ _ _ hmid_env)
            have ht : (i.ult mid) = false := by
              rw [BitVec.ult_eq_decide]
              exact decide_eq_false hI'
            rwa [ht] at h
          have hE : evalExpr
              (.tif (.ult (.var "i") (.var "mid"))
                (.ult (.var "j") (.var "hi"))
                (.lit (.b false))) ρ = .ok (.b false) := by
            rw [evalExpr_tif_false _ _ _ _ hc1]
            simp [evalExpr, litVal]
          exact (memEvalExpr_tif_false _ _ _ _ _ _ hag1 hc1 heag).trans hE
      have hfwd0 : mergeRunsMainFwd la lt
          ((mid.toNat - i.toNat) + (hi.toNat - j.toNat))
          i.toNat j.toNat k.toNat mid.toNat hi.toNat =
          .ok (i.toNat, j.toNat, k.toNat, lt) := by
        match hm : (mid.toNat - i.toNat) + (hi.toNat - j.toNat) with
        | 0 => simp only [mergeRunsMainFwd]
        | _ + 1 =>
          by_cases hI' : i.toNat < mid.toNat
          · have hnJ : ¬ j.toNat < hi.toNat :=
              fun hj => hguard ⟨hI', hj⟩
            simp only [mergeRunsMainFwd, dite_eq_left hI',
              dite_eq_right hnJ]
          · simp only [mergeRunsMainFwd, dite_eq_right hI']
      rw [hfwd0] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hfwd
      have hexit : memEvalProgStmt prog (F + 1) mergeRunsMain
          ρ m π = .ok ((ρ, m, π), .fellThrough) := by
        simp only [mergeRunsMain,
          memEvalProgStmt_while_false prog _ _ _ _ _ _ hcond]
      refine ⟨ρ, m, hexit, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact htmp_env
      · have hto : BitVec.ofNat 64 i.toNat = i := bv64_ofNat_toNat i
        rw [hto]
        exact hi_env
      · have hto : BitVec.ofNat 64 j.toNat = j := bv64_ofNat_toNat j
        rw [hto]
        exact hj_env
      · have hto : BitVec.ofNat 64 k.toNat = k := bv64_ofNat_toNat k
        rw [hto]
        exact hk_env
      · exact ha_env
      · exact hmid_env
      · exact hhi_env
      · exact hmem_a
      · exact hmem_b
      · exact hnB

/-- Main-loop err soundness on memory: a model abort replays as the
    same abort (fuel induction mirroring `mergeRunsMain_err`; the live
    step splits on `slt`, miss legs abort, hit legs step and re-induct). -/
theorem memRunsMain_err (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lt : List (BitVec 32)) (mid hi i j k : BitVec 64)
    (e : Panic)
    (aa ab : Addr) (ta tb : Nat) (nA nB : BitVec 32)
    (haa : aa ≠ ab)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_tmp : layoutLookup π "tmp" = some (ab, tb))
    (hmem_a : memFind m aa = some ⟨ta, true, nA :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nB :: lt⟩)
    (hnB : nB = BitVec.ofNat 32 lt.length)
    (hi_env : envLookup ρ "i" = some (.u64 i))
    (hj_env : envLookup ρ "j" = some (.u64 j))
    (hk_env : envLookup ρ "k" = some (.u64 k))
    (ha_env : envLookup ρ "a" = some (.stdVecVal la))
    (hmid_env : envLookup ρ "mid" = some (.u64 mid))
    (hhi_env : envLookup ρ "hi" = some (.u64 hi))
    (htmp_env : envLookup ρ "tmp" = some (.stdVecVal lt))
    (hlent : lt.length < 2 ^ 64)
    (hmid_le : mid.toNat ≤ la.length) (hhi_le : hi.toNat ≤ la.length)
    (hF : (mid.toNat - i.toNat) + (hi.toNat - j.toNat) + 1 ≤ F)
    (hfwd : mergeRunsMainFwd la lt
      ((mid.toNat - i.toNat) + (hi.toNat - j.toNat))
      i.toNat j.toNat k.toNat mid.toNat hi.toNat =
      .error e) :
    memEvalProgStmt prog F mergeRunsMain ρ m π = .error e := by
  induction F generalizing ρ m π la lt i j k e with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hguard : (i.toNat < mid.toNat ∧ j.toNat < hi.toNat)
    · obtain ⟨hI, hJ⟩ := hguard
      have hvarI : memEvalExpr (.var "i") ρ m π =
          evalExpr (.var "i") ρ := memEvalExpr_var _ _ _ _
      have hvarM : memEvalExpr (.var "mid") ρ m π =
          evalExpr (.var "mid") ρ := memEvalExpr_var _ _ _ _
      have hvarJ : memEvalExpr (.var "j") ρ m π =
          evalExpr (.var "j") ρ := memEvalExpr_var _ _ _ _
      have hvarH : memEvalExpr (.var "hi") ρ m π =
          evalExpr (.var "hi") ρ := memEvalExpr_var _ _ _ _
      have hag1 : memEvalExpr (.ult (.var "i") (.var "mid")) ρ m π =
          evalExpr (.ult (.var "i") (.var "mid")) ρ :=
        memEvalExpr_ult_agree _ _ _ _ _ hvarI hvarM
      have hc1 : evalExpr (.ult (.var "i") (.var "mid")) ρ =
          .ok (.b true) := by
        have h := evalExpr_ult_u64 _ _ _ _ _
          (evalExpr_var_hit _ _ _ hi_env)
          (evalExpr_var_hit _ _ _ hmid_env)
        have ht : (i.ult mid) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true hI
        rwa [ht] at h
      have hag2 : memEvalExpr (.ult (.var "j") (.var "hi")) ρ m π =
          evalExpr (.ult (.var "j") (.var "hi")) ρ :=
        memEvalExpr_ult_agree _ _ _ _ _ hvarJ hvarH
      have hc2 : evalExpr (.ult (.var "j") (.var "hi")) ρ =
          .ok (.b true) := by
        have h := evalExpr_ult_u64 _ _ _ _ _
          (evalExpr_var_hit _ _ _ hj_env)
          (evalExpr_var_hit _ _ _ hhi_env)
        have ht : (j.ult hi) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true hJ
        rwa [ht] at h
      have hE : evalExpr
          (.tif (.ult (.var "i") (.var "mid"))
            (.ult (.var "j") (.var "hi"))
            (.lit (.b false))) ρ = .ok (.b true) := by
        rw [evalExpr_tif_true _ _ _ _ hc1]
        exact hc2
      have hcond : memEvalExpr
          (.tif (.ult (.var "i") (.var "mid"))
            (.ult (.var "j") (.var "hi"))
            (.lit (.b false))) ρ m π = .ok (.b true) :=
        (memEvalExpr_tif_true _ _ _ _ _ _ hag1 hc1 hag2).trans hE
      have hM : (mid.toNat - i.toNat) + (hi.toNat - j.toNat) =
          ((mid.toNat - i.toNat) + (hi.toNat - j.toNat) - 1) + 1 := by
        omega
      rw [hM] at hfwd
      have hgetI : la[i.toNat]? = some la[i.toNat] :=
        List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hI hmid_le)
      have hgetJ : la[j.toNat]? = some la[j.toNat] :=
        List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hJ hhi_le)
      cases hgetK : lt[k.toNat]? with
      | none =>
        have hcontra : mergeRunsMainFwd la lt
            (((mid.toNat - i.toNat) + (hi.toNat - j.toNat) - 1) + 1)
            i.toNat j.toNat k.toNat mid.toNat hi.toNat =
            .error .AssertFail := by
          simp only [mergeRunsMainFwd, dite_eq_left hI, dite_eq_left hJ,
            hgetK]
        rw [hcontra] at hfwd
        cases hfwd
        have hltK : ¬ k.toNat < lt.length := by
          intro hc
          have hsome := List.getElem?_eq_getElem hc
          rw [hsome] at hgetK
          cases hgetK
        have hmemLen : memLoad m ab tb 0 =
            .ok (BitVec.ofNat 32 lt.length) := by
          rw [← hnB]
          exact memLoad_cellsAt m ab tb 0 (nB :: lt) nB hmem_b rfl
        by_cases hslt : (la[i.toNat].slt la[j.toNat]) = true
        · have hbody := memRunsMainBody_missI prog F ρ m π la lt i j k
            la[i.toNat] la[j.toNat] aa ab ta tb nA nB
            hlay_a hlay_tmp hmem_a hmem_b hmemLen
            hi_env hj_env hk_env ha_env htmp_env
            hgetI hgetJ hslt hltK hlent
          have herr : memEvalProgStmt prog (F + 1) mergeRunsMain
              ρ m π = .error .AssertFail := by
            simp only [mergeRunsMain,
              memEvalProgStmt_while_true prog F _ _ _ _ _ hcond, hbody]
          exact herr
        · have hsltF : (la[i.toNat].slt la[j.toNat]) = false :=
            Bool.eq_false_of_ne_true hslt
          have hbody := memRunsMainBody_missJ prog F ρ m π la lt i j k
            la[i.toNat] la[j.toNat] aa ab ta tb nA nB
            hlay_a hlay_tmp hmem_a hmem_b hmemLen
            hi_env hj_env hk_env ha_env htmp_env
            hgetI hgetJ hsltF hltK hlent
          have herr : memEvalProgStmt prog (F + 1) mergeRunsMain
              ρ m π = .error .AssertFail := by
            simp only [mergeRunsMain,
              memEvalProgStmt_while_true prog F _ _ _ _ _ hcond, hbody]
          exact herr
      | some w =>
        have hltK : k.toNat < lt.length :=
          list_lt_of_getElem?_some lt k.toNat w hgetK
        have hmemLen : memLoad m ab tb 0 =
            .ok (BitVec.ofNat 32 lt.length) := by
          rw [← hnB]
          exact memLoad_cellsAt m ab tb 0 (nB :: lt) nB hmem_b rfl
        have hlt1 : k.toNat + 1 < (nB :: lt).length := by
          simp only [List.length_cons]
          omega
        have h1k : (k + 1).toNat = k.toNat + 1 :=
          bv64_succ_toNat k _ hltK hlent
        by_cases hslt : (la[i.toNat].slt la[j.toNat]) = true
        · have hfwdI : mergeRunsMainFwd la (lt.set k.toNat la[i.toNat])
              ((mid.toNat - i.toNat) + (hi.toNat - j.toNat) - 1)
              (i.toNat + 1) j.toNat (k.toNat + 1) mid.toNat hi.toNat =
              .error e := by
            have h := hfwd
            simp only [mergeRunsMainFwd, dite_eq_left hI,
              dite_eq_left hJ, hgetK, hgetI, hgetJ, hslt] at h
            exact h
          obtain ⟨m₁, hstore⟩ : ∃ m₁, memStore m ab tb
              (k.toNat + 1) la[i.toNat] = .ok m₁ :=
            ⟨_, memStore_cellsAt m ab tb (k.toNat + 1) (nB :: lt)
              la[i.toNat] hmem_b hlt1⟩
          obtain ⟨ρt, hu⟩ := envUpdate_some_of_lookup ρ "tmp"
            (.stdVecVal lt) (.stdVecVal (lt.set k.toNat la[i.toNat]))
            htmp_env
          have hlookI' : envLookup ρt "i" = some (.u64 i) := by
            have h := envLookup_update_miss ρ "i" "tmp" _ ρt
              (by decide) hu
            rw [h, hi_env]
          obtain ⟨ρI, huI⟩ := envUpdate_some_of_lookup ρt "i"
            (.u64 i) (.u64 (i + 1)) hlookI'
          have hlookK' : envLookup ρt "k" = some (.u64 k) := by
            have h := envLookup_update_miss ρ "k" "tmp" _ ρt
              (by decide) hu
            rw [h, hk_env]
          have hlookKI : envLookup ρI "k" = some (.u64 k) := by
            have h := envLookup_update_miss ρt "k" "i" _ ρI
              (by decide) huI
            rw [h, hlookK']
          obtain ⟨ρK, huK⟩ := envUpdate_some_of_lookup ρI "k"
            (.u64 k) (.u64 (k + 1)) hlookKI
          have hstep : memEvalProgStmt prog F mergeRunsMainBody
              ρ m π = .ok ((ρK, m₁, π), .fellThrough) :=
            memRunsMainBody_hitI prog F ρ m π la lt i j k
              la[i.toNat] la[j.toNat] w
              aa ab ta tb nA nB
              hlay_a hlay_tmp hmem_a hmem_b hmemLen
              hi_env hj_env hk_env ha_env htmp_env
              hgetI hgetJ hslt hltK hlent hgetK _ hstore _ hu _ _ huI huK
          have hloop : memEvalProgStmt prog (F + 1) mergeRunsMain
              ρ m π =
              memEvalProgStmt prog F mergeRunsMain ρK m₁ π := by
            simp only [mergeRunsMain,
              memEvalProgStmt_while_true prog F _ _ _ _ _ hcond, hstep]
          have h1i : (i + 1).toNat = i.toNat + 1 :=
            bv64_succ_toNat i _ hI (by omega)
          have hlent' : (lt.set k.toNat la[i.toNat]).length < 2 ^ 64 := by
            rw [List.length_set]
            exact hlent
          have hF' : (mid.toNat - (i + 1).toNat) +
              (hi.toNat - j.toNat) + 1 ≤ F := by omega
          have hM' : (mid.toNat - i.toNat) + (hi.toNat - j.toNat) - 1 =
              (mid.toNat - (i + 1).toNat) + (hi.toNat - j.toNat) := by
            omega
          have hfwd' : mergeRunsMainFwd la (lt.set k.toNat la[i.toNat])
              ((mid.toNat - (i + 1).toNat) + (hi.toNat - j.toNat))
              ((i + 1).toNat) j.toNat ((k + 1).toNat)
              mid.toNat hi.toNat =
              .error e := by
            rw [← h1i, ← h1k, hM'] at hfwdI
            exact hfwdI
          have hmem_a₁ : memFind m₁ aa = some ⟨ta, true, nA :: la⟩ := by
            have h := memFind_memStore_other m m₁ ab aa tb
              (k.toNat + 1) la[i.toNat] hstore haa
            rw [h]
            exact hmem_a
          have hmem_b₁ : memFind m₁ ab =
              some ⟨tb, true, nB :: lt.set k.toNat la[i.toNat]⟩ := by
            have hcells := memFind_cellsAt_store m ab tb (k.toNat + 1)
              (nB :: lt) la[i.toNat] m₁ hmem_b hlt1 hstore
            have hsetEq : (nB :: lt).set (k.toNat + 1) la[i.toNat] =
                nB :: lt.set k.toNat la[i.toNat] :=
              List.set_cons_succ
            rw [hsetEq] at hcells
            exact hcells
          have hnB₁ : nB =
              BitVec.ofNat 32 (lt.set k.toNat la[i.toNat]).length := by
            rw [List.length_set]
            exact hnB
          have hlookIK : envLookup ρI "i" = some (.u64 (i + 1)) :=
            envLookup_update_hit ρt "i" _ ρI huI
          have hi_env₁ : envLookup ρK "i" = some (.u64 (i + 1)) := by
            have h := envLookup_update_miss ρI "i" "k" _ ρK
              (by decide) huK
            rw [h, hlookIK]
          have hk_env₁ : envLookup ρK "k" = some (.u64 (k + 1)) :=
            envLookup_update_hit ρI "k" _ ρK huK
          have hj_env₁ : envLookup ρK "j" = some (.u64 j) := by
            have h1 := envLookup_update_miss ρI "j" "k" _ ρK
              (by decide) huK
            have h2 := envLookup_update_miss ρt "j" "i" _ ρI
              (by decide) huI
            have h3 := envLookup_update_miss ρ "j" "tmp" _ ρt
              (by decide) hu
            rw [h1, h2, h3, hj_env]
          have ha_env₁ : envLookup ρK "a" = some (.stdVecVal la) := by
            have h1 := envLookup_update_miss ρI "a" "k" _ ρK
              (by decide) huK
            have h2 := envLookup_update_miss ρt "a" "i" _ ρI
              (by decide) huI
            have h3 := envLookup_update_miss ρ "a" "tmp" _ ρt
              (by decide) hu
            rw [h1, h2, h3, ha_env]
          have hmid_env₁ : envLookup ρK "mid" = some (.u64 mid) := by
            have h1 := envLookup_update_miss ρI "mid" "k" _ ρK
              (by decide) huK
            have h2 := envLookup_update_miss ρt "mid" "i" _ ρI
              (by decide) huI
            have h3 := envLookup_update_miss ρ "mid" "tmp" _ ρt
              (by decide) hu
            rw [h1, h2, h3, hmid_env]
          have hhi_env₁ : envLookup ρK "hi" = some (.u64 hi) := by
            have h1 := envLookup_update_miss ρI "hi" "k" _ ρK
              (by decide) huK
            have h2 := envLookup_update_miss ρt "hi" "i" _ ρI
              (by decide) huI
            have h3 := envLookup_update_miss ρ "hi" "tmp" _ ρt
              (by decide) hu
            rw [h1, h2, h3, hhi_env]
          have htmp_env₁ : envLookup ρK "tmp" =
              some (.stdVecVal (lt.set k.toNat la[i.toNat])) := by
            have h1 := envLookup_update_miss ρI "tmp" "k" _ ρK
              (by decide) huK
            have h2 := envLookup_update_miss ρt "tmp" "i" _ ρI
              (by decide) huI
            rw [h1, h2]
            exact envLookup_update_hit ρ "tmp" _ ρt hu
          rw [hloop]
          exact ih ρK m₁ π la (lt.set k.toNat la[i.toNat]) (i + 1)
            j (k + 1) e hlay_a hlay_tmp hmem_a₁ hmem_b₁
            hnB₁ hi_env₁ hj_env₁ hk_env₁ ha_env₁ hmid_env₁ hhi_env₁
            htmp_env₁ hlent' hmid_le hhi_le hF' hfwd'
        · have hsltF : (la[i.toNat].slt la[j.toNat]) = false :=
            Bool.eq_false_of_ne_true hslt
          have hfwdJ : mergeRunsMainFwd la (lt.set k.toNat la[j.toNat])
              ((mid.toNat - i.toNat) + (hi.toNat - j.toNat) - 1)
              i.toNat (j.toNat + 1) (k.toNat + 1) mid.toNat hi.toNat =
              .error e := by
            have h := hfwd
            simp only [mergeRunsMainFwd, dite_eq_left hI,
              dite_eq_left hJ, hgetK, hgetI, hgetJ, hsltF] at h
            exact h
          obtain ⟨m₁, hstore⟩ : ∃ m₁, memStore m ab tb
              (k.toNat + 1) la[j.toNat] = .ok m₁ :=
            ⟨_, memStore_cellsAt m ab tb (k.toNat + 1) (nB :: lt)
              la[j.toNat] hmem_b hlt1⟩
          obtain ⟨ρt, hu⟩ := envUpdate_some_of_lookup ρ "tmp"
            (.stdVecVal lt) (.stdVecVal (lt.set k.toNat la[j.toNat]))
            htmp_env
          have hlookJ' : envLookup ρt "j" = some (.u64 j) := by
            have h := envLookup_update_miss ρ "j" "tmp" _ ρt
              (by decide) hu
            rw [h, hj_env]
          obtain ⟨ρJ, huJ⟩ := envUpdate_some_of_lookup ρt "j"
            (.u64 j) (.u64 (j + 1)) hlookJ'
          have hlookK' : envLookup ρt "k" = some (.u64 k) := by
            have h := envLookup_update_miss ρ "k" "tmp" _ ρt
              (by decide) hu
            rw [h, hk_env]
          have hlookKJ : envLookup ρJ "k" = some (.u64 k) := by
            have h := envLookup_update_miss ρt "k" "j" _ ρJ
              (by decide) huJ
            rw [h, hlookK']
          obtain ⟨ρK, huK⟩ := envUpdate_some_of_lookup ρJ "k"
            (.u64 k) (.u64 (k + 1)) hlookKJ
          have hstep : memEvalProgStmt prog F mergeRunsMainBody
              ρ m π = .ok ((ρK, m₁, π), .fellThrough) :=
            memRunsMainBody_hitJ prog F ρ m π la lt i j k
              la[i.toNat] la[j.toNat] w
              aa ab ta tb nA nB
              hlay_a hlay_tmp hmem_a hmem_b hmemLen
              hi_env hj_env hk_env ha_env htmp_env
              hgetI hgetJ hsltF hltK hlent hgetK _ hstore _ hu _ _ huJ huK
          have hloop : memEvalProgStmt prog (F + 1) mergeRunsMain
              ρ m π =
              memEvalProgStmt prog F mergeRunsMain ρK m₁ π := by
            simp only [mergeRunsMain,
              memEvalProgStmt_while_true prog F _ _ _ _ _ hcond, hstep]
          have h1j : (j + 1).toNat = j.toNat + 1 :=
            bv64_succ_toNat j _ hJ (by omega)
          have hlent' : (lt.set k.toNat la[j.toNat]).length < 2 ^ 64 := by
            rw [List.length_set]
            exact hlent
          have hF' : (mid.toNat - i.toNat) +
              (hi.toNat - (j + 1).toNat) + 1 ≤ F := by omega
          have hM' : (mid.toNat - i.toNat) + (hi.toNat - j.toNat) - 1 =
              (mid.toNat - i.toNat) + (hi.toNat - (j + 1).toNat) := by
            omega
          have hfwd' : mergeRunsMainFwd la (lt.set k.toNat la[j.toNat])
              ((mid.toNat - i.toNat) + (hi.toNat - (j + 1).toNat))
              i.toNat ((j + 1).toNat) ((k + 1).toNat)
              mid.toNat hi.toNat =
              .error e := by
            rw [← h1j, ← h1k, hM'] at hfwdJ
            exact hfwdJ
          have hmem_a₁ : memFind m₁ aa = some ⟨ta, true, nA :: la⟩ := by
            have h := memFind_memStore_other m m₁ ab aa tb
              (k.toNat + 1) la[j.toNat] hstore haa
            rw [h]
            exact hmem_a
          have hmem_b₁ : memFind m₁ ab =
              some ⟨tb, true, nB :: lt.set k.toNat la[j.toNat]⟩ := by
            have hcells := memFind_cellsAt_store m ab tb (k.toNat + 1)
              (nB :: lt) la[j.toNat] m₁ hmem_b hlt1 hstore
            have hsetEq : (nB :: lt).set (k.toNat + 1) la[j.toNat] =
                nB :: lt.set k.toNat la[j.toNat] :=
              List.set_cons_succ
            rw [hsetEq] at hcells
            exact hcells
          have hnB₁ : nB =
              BitVec.ofNat 32 (lt.set k.toNat la[j.toNat]).length := by
            rw [List.length_set]
            exact hnB
          have hlookJK : envLookup ρJ "j" = some (.u64 (j + 1)) :=
            envLookup_update_hit ρt "j" _ ρJ huJ
          have hj_env₁ : envLookup ρK "j" = some (.u64 (j + 1)) := by
            have h := envLookup_update_miss ρJ "j" "k" _ ρK
              (by decide) huK
            rw [h, hlookJK]
          have hk_env₁ : envLookup ρK "k" = some (.u64 (k + 1)) :=
            envLookup_update_hit ρJ "k" _ ρK huK
          have hi_env₁ : envLookup ρK "i" = some (.u64 i) := by
            have h1 := envLookup_update_miss ρJ "i" "k" _ ρK
              (by decide) huK
            have h2 := envLookup_update_miss ρt "i" "j" _ ρJ
              (by decide) huJ
            have h3 := envLookup_update_miss ρ "i" "tmp" _ ρt
              (by decide) hu
            rw [h1, h2, h3, hi_env]
          have ha_env₁ : envLookup ρK "a" = some (.stdVecVal la) := by
            have h1 := envLookup_update_miss ρJ "a" "k" _ ρK
              (by decide) huK
            have h2 := envLookup_update_miss ρt "a" "j" _ ρJ
              (by decide) huJ
            have h3 := envLookup_update_miss ρ "a" "tmp" _ ρt
              (by decide) hu
            rw [h1, h2, h3, ha_env]
          have hmid_env₁ : envLookup ρK "mid" = some (.u64 mid) := by
            have h1 := envLookup_update_miss ρJ "mid" "k" _ ρK
              (by decide) huK
            have h2 := envLookup_update_miss ρt "mid" "j" _ ρJ
              (by decide) huJ
            have h3 := envLookup_update_miss ρ "mid" "tmp" _ ρt
              (by decide) hu
            rw [h1, h2, h3, hmid_env]
          have hhi_env₁ : envLookup ρK "hi" = some (.u64 hi) := by
            have h1 := envLookup_update_miss ρJ "hi" "k" _ ρK
              (by decide) huK
            have h2 := envLookup_update_miss ρt "hi" "j" _ ρJ
              (by decide) huJ
            have h3 := envLookup_update_miss ρ "hi" "tmp" _ ρt
              (by decide) hu
            rw [h1, h2, h3, hhi_env]
          have htmp_env₁ : envLookup ρK "tmp" =
              some (.stdVecVal (lt.set k.toNat la[j.toNat])) := by
            have h1 := envLookup_update_miss ρJ "tmp" "k" _ ρK
              (by decide) huK
            have h2 := envLookup_update_miss ρt "tmp" "j" _ ρJ
              (by decide) huJ
            rw [h1, h2]
            exact envLookup_update_hit ρ "tmp" _ ρt hu
          rw [hloop]
          exact ih ρK m₁ π la (lt.set k.toNat la[j.toNat]) i
            (j + 1) (k + 1) e hlay_a hlay_tmp hmem_a₁
            hmem_b₁ hnB₁ hi_env₁ hj_env₁ hk_env₁ ha_env₁ hmid_env₁
            hhi_env₁ htmp_env₁ hlent' hmid_le hhi_le hF' hfwd'
    · have hcond : memEvalExpr
          (.tif (.ult (.var "i") (.var "mid"))
            (.ult (.var "j") (.var "hi"))
            (.lit (.b false))) ρ m π = .ok (.b false) := by
        have hvarI : memEvalExpr (.var "i") ρ m π =
            evalExpr (.var "i") ρ := memEvalExpr_var _ _ _ _
        have hvarM : memEvalExpr (.var "mid") ρ m π =
            evalExpr (.var "mid") ρ := memEvalExpr_var _ _ _ _
        have hvarJ : memEvalExpr (.var "j") ρ m π =
            evalExpr (.var "j") ρ := memEvalExpr_var _ _ _ _
        have hvarH : memEvalExpr (.var "hi") ρ m π =
            evalExpr (.var "hi") ρ := memEvalExpr_var _ _ _ _
        have hag1 : memEvalExpr (.ult (.var "i") (.var "mid")) ρ m π =
            evalExpr (.ult (.var "i") (.var "mid")) ρ :=
          memEvalExpr_ult_agree _ _ _ _ _ hvarI hvarM
        have hag2 : memEvalExpr (.ult (.var "j") (.var "hi")) ρ m π =
            evalExpr (.ult (.var "j") (.var "hi")) ρ :=
          memEvalExpr_ult_agree _ _ _ _ _ hvarJ hvarH
        have heag : memEvalExpr (.lit (.b false)) ρ m π =
            evalExpr (.lit (.b false)) ρ :=
          memEvalExpr_lit _ _ _ _
        by_cases hI' : i.toNat < mid.toNat
        · have hnJ : ¬ j.toNat < hi.toNat :=
            fun hj => hguard ⟨hI', hj⟩
          have hc1 : evalExpr (.ult (.var "i") (.var "mid")) ρ =
              .ok (.b true) := by
            have h := evalExpr_ult_u64 _ _ _ _ _
              (evalExpr_var_hit _ _ _ hi_env)
              (evalExpr_var_hit _ _ _ hmid_env)
            have ht : (i.ult mid) = true := by
              rw [BitVec.ult_eq_decide]
              exact decide_eq_true hI'
            rwa [ht] at h
          have hc2 : evalExpr (.ult (.var "j") (.var "hi")) ρ =
              .ok (.b false) := by
            have h := evalExpr_ult_u64 _ _ _ _ _
              (evalExpr_var_hit _ _ _ hj_env)
              (evalExpr_var_hit _ _ _ hhi_env)
            have ht : (j.ult hi) = false := by
              rw [BitVec.ult_eq_decide]
              exact decide_eq_false hnJ
            rwa [ht] at h
          have hE : evalExpr
              (.tif (.ult (.var "i") (.var "mid"))
                (.ult (.var "j") (.var "hi"))
                (.lit (.b false))) ρ = .ok (.b false) := by
            rw [evalExpr_tif_true _ _ _ _ hc1]
            exact hc2
          exact (memEvalExpr_tif_true _ _ _ _ _ _ hag1 hc1 hag2).trans hE
        · have hc1 : evalExpr (.ult (.var "i") (.var "mid")) ρ =
              .ok (.b false) := by
            have h := evalExpr_ult_u64 _ _ _ _ _
              (evalExpr_var_hit _ _ _ hi_env)
              (evalExpr_var_hit _ _ _ hmid_env)
            have ht : (i.ult mid) = false := by
              rw [BitVec.ult_eq_decide]
              exact decide_eq_false hI'
            rwa [ht] at h
          have hE : evalExpr
              (.tif (.ult (.var "i") (.var "mid"))
                (.ult (.var "j") (.var "hi"))
                (.lit (.b false))) ρ = .ok (.b false) := by
            rw [evalExpr_tif_false _ _ _ _ hc1]
            simp [evalExpr, litVal]
          exact (memEvalExpr_tif_false _ _ _ _ _ _ hag1 hc1 heag).trans hE
      have hfwd0 : mergeRunsMainFwd la lt
          ((mid.toNat - i.toNat) + (hi.toNat - j.toNat))
          i.toNat j.toNat k.toNat mid.toNat hi.toNat =
          .ok (i.toNat, j.toNat, k.toNat, lt) := by
        match hm : (mid.toNat - i.toNat) + (hi.toNat - j.toNat) with
        | 0 => simp only [mergeRunsMainFwd]
        | _ + 1 =>
          by_cases hI' : i.toNat < mid.toNat
          · have hnJ : ¬ j.toNat < hi.toNat :=
              fun hj => hguard ⟨hI', hj⟩
            simp only [mergeRunsMainFwd, dite_eq_left hI',
              dite_eq_right hnJ]
          · simp only [mergeRunsMainFwd, dite_eq_right hI']
      rw [hfwd0] at hfwd
      cases hfwd
/-! ## Entry transfer -/

/-- Entry transfer for `mergeRuns`: the memory evaluator runs the three
    loops on the two pinned blocks and returns the forward-model words
    (mirrors `evalProgFunc_mergeRuns`; the prelude binds by `memRevLet`,
    each loop hands its by-find state to the next). -/
theorem memEvalProgFunc_mergeRuns (prog : Prog) (F : Nat)
    (la lt : List (BitVec 32)) (lo mid hi : BitVec 64)
    (hlent : lt.length < 2 ^ 64)
    (hlo_mid : lo.toNat ≤ mid.toNat) (hmid_hi : mid.toNat ≤ hi.toNat)
    (hmid_le : mid.toNat ≤ la.length) (hhi_le : hi.toNat ≤ la.length)
    (hlo_lt : lo.toNat ≤ lt.length)
    (hF : ((mid.toNat - lo.toNat) + (hi.toNat - lo.toNat)) + 1 ≤ F) :
    memEvalProgFunc prog F mergeRunsFunc
      [.stdVecVal la, .stdVecVal lt, .u64 lo, .u64 mid, .u64 hi] =
      mergeRunsFwd la lt lo.toNat mid.toNat hi.toNat := by
  have hbind : bindMemArgs mergeRunsFunc.args
      [.stdVecVal la, .stdVecVal lt, .u64 lo, .u64 mid, .u64 hi]
      emptyMem =
      some ([("a", .stdVecVal la), ("tmp", .stdVecVal lt),
        ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)],
        ⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 la.length) :: la⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩,
        [("a", 1, 1), ("tmp", 0, 0)]) :=
    bindMemArgs_vecMergeRuns la lt lo mid hi
  have hbody : mergeRunsFunc.body =
      (.seq (.let_ "i" (.u 64) (.var "lo"))
        (.seq (.let_ "j" (.u 64) (.var "mid"))
          (.seq (.let_ "k" (.u 64) (.var "lo"))
            (.seq mergeRunsMain
              (.seq mergeRunsDrainI
                (.seq mergeRunsDrainJ
                  (.return_ (.var "tmp")))))))) := rfl
  have hvar_lo : evalExpr (.var "lo")
      [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
        ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)] =
      .ok (.u64 lo) :=
    evalExpr_var_hit _ _ _ rfl
  have hlet_i := memRevLet prog F "i" (.u 64) (.var "lo")
    [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
      ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
    ⟨2, [(1, ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩),
      (0, ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩
    [("a", 1, 1), ("tmp", 0, 0)] (.u64 lo)
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h)
    (memEvalExpr_var _ _ _ _) hvar_lo
  have hmid1 : envLookup
      (envExtend [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
        ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) "mid" =
      some (.u64 mid) := by
    rw [envExtend_miss _ _ _ _ (by decide : ("mid" : String) ≠ "i")]
    rfl
  have hvar_mid : evalExpr (.var "mid")
      (envExtend [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
        ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) =
      .ok (.u64 mid) :=
    evalExpr_var_hit _ _ _ hmid1
  have hlet_j := memRevLet prog F "j" (.u 64) (.var "mid")
    (envExtend [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
      ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
      "i" (.u64 lo))
    ⟨2, [(1, ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩),
      (0, ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩
    [("a", 1, 1), ("tmp", 0, 0)] (.u64 mid)
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h)
    (memEvalExpr_var _ _ _ _) hvar_mid
  have hlo2 : envLookup
      (envExtend (envExtend
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
          ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) "j" (.u64 mid)) "lo" =
      some (.u64 lo) := by
    rw [envExtend_miss _ _ _ _ (by decide : ("lo" : String) ≠ "j"),
      envExtend_miss _ _ _ _ (by decide : ("lo" : String) ≠ "i")]
    rfl
  have hvar_lo2 : evalExpr (.var "lo")
      (envExtend (envExtend
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
          ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) "j" (.u64 mid)) =
      .ok (.u64 lo) :=
    evalExpr_var_hit _ _ _ hlo2
  have hlet_k := memRevLet prog F "k" (.u 64) (.var "lo")
    (envExtend (envExtend
      [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
        ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
      "i" (.u64 lo)) "j" (.u64 mid))
    ⟨2, [(1, ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩),
      (0, ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩
    [("a", 1, 1), ("tmp", 0, 0)] (.u64 lo)
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h)
    (memEvalExpr_var _ _ _ _) hvar_lo2
  have hi3 : envLookup
      (envExtend (envExtend (envExtend
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
          ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) "j" (.u64 mid)) "k" (.u64 lo)) "i" =
      some (.u64 lo) := by
    rw [envExtend_miss _ _ _ _ (by decide : ("i" : String) ≠ "k"),
      envExtend_miss _ _ _ _ (by decide : ("i" : String) ≠ "j")]
    exact envExtend_hit _ _ _
  have hj3 : envLookup
      (envExtend (envExtend (envExtend
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
          ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) "j" (.u64 mid)) "k" (.u64 lo)) "j" =
      some (.u64 mid) := by
    rw [envExtend_miss _ _ _ _ (by decide : ("j" : String) ≠ "k")]
    exact envExtend_hit _ _ _
  have hk3 : envLookup
      (envExtend (envExtend (envExtend
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
          ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) "j" (.u64 mid)) "k" (.u64 lo)) "k" =
      some (.u64 lo) :=
    envExtend_hit _ _ _
  have ha3 : envLookup
      (envExtend (envExtend (envExtend
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
          ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) "j" (.u64 mid)) "k" (.u64 lo)) "a" =
      some (.stdVecVal la) := by
    rw [envExtend_miss _ _ _ _ (by decide : ("a" : String) ≠ "k"),
      envExtend_miss _ _ _ _ (by decide : ("a" : String) ≠ "j"),
      envExtend_miss _ _ _ _ (by decide : ("a" : String) ≠ "i")]
    rfl
  have hmid3 : envLookup
      (envExtend (envExtend (envExtend
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
          ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) "j" (.u64 mid)) "k" (.u64 lo)) "mid" =
      some (.u64 mid) := by
    rw [envExtend_miss _ _ _ _ (by decide : ("mid" : String) ≠ "k"),
      envExtend_miss _ _ _ _ (by decide : ("mid" : String) ≠ "j"),
      envExtend_miss _ _ _ _ (by decide : ("mid" : String) ≠ "i")]
    rfl
  have hhi3 : envLookup
      (envExtend (envExtend (envExtend
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
          ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) "j" (.u64 mid)) "k" (.u64 lo)) "hi" =
      some (.u64 hi) := by
    rw [envExtend_miss _ _ _ _ (by decide : ("hi" : String) ≠ "k"),
      envExtend_miss _ _ _ _ (by decide : ("hi" : String) ≠ "j"),
      envExtend_miss _ _ _ _ (by decide : ("hi" : String) ≠ "i")]
    rfl
  have htmp3 : envLookup
      (envExtend (envExtend (envExtend
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
          ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) "j" (.u64 mid)) "k" (.u64 lo)) "tmp" =
      some (.stdVecVal lt) := by
    rw [envExtend_miss _ _ _ _ (by decide : ("tmp" : String) ≠ "k"),
      envExtend_miss _ _ _ _ (by decide : ("tmp" : String) ≠ "j"),
      envExtend_miss _ _ _ _ (by decide : ("tmp" : String) ≠ "i")]
    rfl
  have hlay_a : layoutLookup [("a", 1, 1), ("tmp", 0, 0)] "a" =
      some (1, 1) := by
    simp [layoutLookup]
  have hlay_tmp : layoutLookup [("a", 1, 1), ("tmp", 0, 0)] "tmp" =
      some (0, 0) := by
    simp [layoutLookup]
  have hmem_a : memFind ⟨2, [(1, ⟨1, true,
      (BitVec.ofNat 32 la.length) :: la⟩),
      (0, ⟨0, true,
      (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩ 1 =
      some ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩ :=
    memFind_cons_hit _ _ _ _ _
  have hmem_b : memFind ⟨2, [(1, ⟨1, true,
      (BitVec.ofNat 32 la.length) :: la⟩),
      (0, ⟨0, true,
      (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩ 0 =
      some ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩ := by
    rw [memFind_cons_miss _ _ _ _ _ _ (by decide : (0 : Addr) ≠ 1)]
    exact memFind_cons_hit _ _ _ _ _
  have hnB0 : BitVec.ofNat 32 lt.length =
      BitVec.ofNat 32 lt.length := rfl
  match hmain : mergeRunsMainFwd la lt
      ((mid.toNat - lo.toNat) + (hi.toNat - mid.toNat))
      lo.toNat mid.toNat lo.toNat mid.toNat hi.toNat with
  | .error e =>
    have hM := memRunsMain_err prog F
      (envExtend (envExtend (envExtend
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
          ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) "j" (.u64 mid)) "k" (.u64 lo))
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩
      [("a", 1, 1), ("tmp", 0, 0)]
      la lt mid hi lo mid lo e
      1 0 1 0 (BitVec.ofNat 32 la.length) (BitVec.ofNat 32 lt.length)
      (by decide)
      hlay_a hlay_tmp hmem_a hmem_b hnB0 hi3 hj3 hk3 ha3 hmid3 hhi3 htmp3
      hlent hmid_le hhi_le (by omega) (by simpa using hmain)
    have hfwd : mergeRunsFwd la lt lo.toNat mid.toNat hi.toNat =
        .error e := by
      simp [mergeRunsFwd, hmain]
    have hstmt : memEvalProgStmt prog F mergeRunsFunc.body
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
          ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        ⟨2, [(1, ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩
        [("a", 1, 1), ("tmp", 0, 0)] =
        .error e := by
      rw [hbody,
        memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hlet_i,
        memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hlet_j,
        memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hlet_k,
        memEvalProgStmt_seq_err prog F _ _ _ _ _ _ hM]
    simp [memEvalProgFunc, hbind, hstmt, hfwd]
  | .ok (i₁, j₁, k₁, lt₁) =>
    obtain ⟨hi₁, hj₁, hk₁, hlen₁, hloi₁, hloj₁⟩ :=
      mergeRunsMainFwd_le la _ _ _ _ _ _ _ _ _ _ _
        hlo_mid hmid_hi hlo_lt hmain
    have hleno₁ : lt₁.length < 2 ^ 64 := by
      rw [hlen₁]; exact hlent
    have hk₁' : k₁ ≤ lt₁.length := by
      rw [hlen₁]; exact hk₁
    have ti₁ : (BitVec.ofNat 64 i₁).toNat = i₁ :=
      bv64_toNat_ofNat i₁ (Nat.lt_of_le_of_lt hi₁ (by omega))
    have tj₁ : (BitVec.ofNat 64 j₁).toNat = j₁ :=
      bv64_toNat_ofNat j₁ (Nat.lt_of_le_of_lt hj₁ (by omega))
    have tk₁ : (BitVec.ofNat 64 k₁).toNat = k₁ :=
      bv64_toNat_ofNat k₁ (Nat.lt_of_le_of_lt hk₁' hleno₁)
    have hM := memRunsMain_ok prog F
      (envExtend (envExtend (envExtend
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
          ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) "j" (.u64 mid)) "k" (.u64 lo))
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩
      [("a", 1, 1), ("tmp", 0, 0)]
      la lt mid hi lo mid lo i₁ j₁ k₁ lt₁
      1 0 1 0 (BitVec.ofNat 32 la.length) (BitVec.ofNat 32 lt.length)
      (by decide)
      hlay_a hlay_tmp hmem_a hmem_b hnB0 hi3 hj3 hk3 ha3 hmid3 hhi3 htmp3
      hlent hmid_le hhi_le (by omega) (by simpa using hmain)
    obtain ⟨ρ₄, m₄, hMstmt, htmp₄, hi₄, hj₄, hk₄, ha₄, hmid₄, hhi₄,
      hmem_a₄, hmem_b₄, hnB₄⟩ := hM
    match hdrainI : mergeRunsDrainIFwd la lt₁ (mid.toNat - i₁)
        i₁ k₁ mid.toNat with
    | .error e =>
      have hdrainI' : mergeRunsDrainIFwd la lt₁
          (mid.toNat - (BitVec.ofNat 64 i₁).toNat)
          (BitVec.ofNat 64 i₁).toNat (BitVec.ofNat 64 k₁).toNat
          mid.toNat = .error e := by
        rw [ti₁, tk₁]; exact hdrainI
      have hI := memRunsDrainI_err prog F ρ₄ m₄
        [("a", 1, 1), ("tmp", 0, 0)]
        la lt₁ mid (BitVec.ofNat 64 i₁)
        (BitVec.ofNat 64 k₁) e
        1 0 1 0 (BitVec.ofNat 32 la.length) (BitVec.ofNat 32 lt.length)
        (by decide)
        hlay_a hlay_tmp hmem_a₄ hmem_b₄ hnB₄ hi₄ hk₄ ha₄ hmid₄ htmp₄
        hleno₁ hmid_le (by rw [ti₁]; omega) hdrainI'
      have hfwd : mergeRunsFwd la lt lo.toNat mid.toNat hi.toNat =
          .error e := by
        simp [mergeRunsFwd, hmain, hdrainI]
      have hstmt : memEvalProgStmt prog F mergeRunsFunc.body
          [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
            ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
          ⟨2, [(1, ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩),
            (0, ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩
          [("a", 1, 1), ("tmp", 0, 0)] =
          .error e := by
        rw [hbody,
          memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hlet_i,
          memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hlet_j,
          memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hlet_k,
          memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hMstmt,
          memEvalProgStmt_seq_err prog F _ _ _ _ _ _ hI]
      simp [memEvalProgFunc, hbind, hstmt, hfwd]
    | .ok (i₂, k₂, lt₂) =>
      obtain ⟨hi₂, hk₂, hlen₂, hloi₂⟩ :=
        mergeRunsDrainIFwd_le la _ _ _ _ _ _ _ _ hi₁ hk₁' hdrainI
      have hdrainI' : mergeRunsDrainIFwd la lt₁
          (mid.toNat - (BitVec.ofNat 64 i₁).toNat)
          (BitVec.ofNat 64 i₁).toNat (BitVec.ofNat 64 k₁).toNat
          mid.toNat = .ok (i₂, k₂, lt₂) := by
        rw [ti₁, tk₁]; exact hdrainI
      have hleno₂ : lt₂.length < 2 ^ 64 := by
        rw [hlen₂, hlen₁]; exact hlent
      have hI := memRunsDrainI_ok prog F ρ₄ m₄
        [("a", 1, 1), ("tmp", 0, 0)]
        la lt₁ mid hi (BitVec.ofNat 64 i₁)
        (BitVec.ofNat 64 j₁) (BitVec.ofNat 64 k₁) i₂ k₂ lt₂
        1 0 1 0 (BitVec.ofNat 32 la.length) (BitVec.ofNat 32 lt.length)
        (by decide)
        hlay_a hlay_tmp hmem_a₄ hmem_b₄ hnB₄ hi₄ hk₄ ha₄ hmid₄ htmp₄ hj₄ hhi₄
        hleno₁ hmid_le (by rw [ti₁]; omega) hdrainI'
      have hk₂' : k₂ ≤ lt₂.length := by
        rw [hlen₂]; exact hk₂
      have tk₂ : (BitVec.ofNat 64 k₂).toNat = k₂ :=
        bv64_toNat_ofNat k₂ (Nat.lt_of_le_of_lt hk₂' hleno₂)
      obtain ⟨ρ₅, m₅, hIstmt, htmp₅, hi₅, hk₅, ha₅, hmid₅, hj₅, hhi₅,
        hmem_a₅, hmem_b₅, hnB₅⟩ := hI
      match hdrainJ : mergeRunsDrainJFwd la lt₂ (hi.toNat - j₁)
          j₁ k₂ hi.toNat with
      | .error e =>
        have hdrainJ' : mergeRunsDrainJFwd la lt₂
            (hi.toNat - (BitVec.ofNat 64 j₁).toNat)
            (BitVec.ofNat 64 j₁).toNat (BitVec.ofNat 64 k₂).toNat
            hi.toNat = .error e := by
          rw [tj₁, tk₂]; exact hdrainJ
        have hJ := memRunsDrainJ_err prog F ρ₅ m₅
          [("a", 1, 1), ("tmp", 0, 0)]
          la lt₂ hi (BitVec.ofNat 64 j₁)
          (BitVec.ofNat 64 k₂) e
          1 0 1 0 (BitVec.ofNat 32 la.length) (BitVec.ofNat 32 lt.length)
          (by decide)
          hlay_a hlay_tmp hmem_a₅ hmem_b₅ hnB₅ hj₅ hk₅ ha₅ hhi₅ htmp₅
          hleno₂ hhi_le (by rw [tj₁]; omega) hdrainJ'
        have hfwd : mergeRunsFwd la lt lo.toNat mid.toNat hi.toNat =
            .error e := by
          simp [mergeRunsFwd, hmain, hdrainI, hdrainJ]
        have hstmt : memEvalProgStmt prog F mergeRunsFunc.body
            [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
              ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
            ⟨2, [(1, ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩),
              (0, ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩
            [("a", 1, 1), ("tmp", 0, 0)] =
            .error e := by
          rw [hbody,
            memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hlet_i,
            memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hlet_j,
            memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hlet_k,
            memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hMstmt,
            memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hIstmt,
            memEvalProgStmt_seq_err prog F _ _ _ _ _ _ hJ]
        simp [memEvalProgFunc, hbind, hstmt, hfwd]
      | .ok (j₃, k₃, lt₃) =>
        obtain ⟨hj₃, hk₃, hlen₃, hloj₃⟩ :=
          mergeRunsDrainJFwd_le la _ _ _ _ _ _ _ _ hj₁ hk₂' hdrainJ
        have hdrainJ' : mergeRunsDrainJFwd la lt₂
            (hi.toNat - (BitVec.ofNat 64 j₁).toNat)
            (BitVec.ofNat 64 j₁).toNat (BitVec.ofNat 64 k₂).toNat
            hi.toNat = .ok (j₃, k₃, lt₃) := by
          rw [tj₁, tk₂]; exact hdrainJ
        have hleno₃ : lt₃.length < 2 ^ 64 := by
          rw [hlen₃, hlen₂, hlen₁]; exact hlent
        have hJ := memRunsDrainJ_ok prog F ρ₅ m₅
          [("a", 1, 1), ("tmp", 0, 0)]
          la lt₂ hi (BitVec.ofNat 64 j₁)
          (BitVec.ofNat 64 k₂) j₃ k₃ lt₃
          1 0 1 0 (BitVec.ofNat 32 la.length) (BitVec.ofNat 32 lt.length)
          (by decide)
          hlay_a hlay_tmp hmem_a₅ hmem_b₅ hnB₅ hj₅ hk₅ ha₅ hhi₅ htmp₅
          hleno₂ hhi_le (by rw [tj₁]; omega) hdrainJ'
        obtain ⟨ρ₆, m₆, hJstmt, htmp₆, hj₆, hk₆, ha₆, hhi₆,
          hmem_a₆, hmem_b₆, hnB₆⟩ := hJ
        have hmem_ret : memEvalExpr (.var "tmp") ρ₆ m₆
            [("a", 1, 1), ("tmp", 0, 0)] = .ok (.stdVecVal lt₃) :=
          (memEvalExpr_var _ _ _ _).trans
            (evalExpr_var_hit _ _ _ htmp₆)
        have hret : memEvalProgStmt prog F (.return_ (.var "tmp"))
            ρ₆ m₆ [("a", 1, 1), ("tmp", 0, 0)] =
            .ok ((ρ₆, m₆, [("a", 1, 1), ("tmp", 0, 0)]),
              .returned (.stdVecVal lt₃)) :=
          memEvalProgStmt_return prog F _ _ _ _ _ hmem_ret
        have hfwd : mergeRunsFwd la lt lo.toNat mid.toNat hi.toNat =
            .ok (.stdVecVal lt₃) := by
          simp [mergeRunsFwd, hmain, hdrainI, hdrainJ]
        have hstmt : memEvalProgStmt prog F mergeRunsFunc.body
            [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
              ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
            ⟨2, [(1, ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩),
              (0, ⟨0, true, (BitVec.ofNat 32 lt.length) :: lt⟩)], []⟩
            [("a", 1, 1), ("tmp", 0, 0)] =
            .ok ((ρ₆, m₆, [("a", 1, 1), ("tmp", 0, 0)]),
              .returned (.stdVecVal lt₃)) := by
          rw [hbody,
            memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hlet_i,
            memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hlet_j,
            memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hlet_k,
            memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hMstmt,
            memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hIstmt,
            memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hJstmt]
          exact hret
        simp [memEvalProgFunc, hbind, hstmt, hfwd]

/-- General-caller-memory entry for `mergeRunsFunc`: the callee
    binds its snapshots on fresh addrs above `m₀.next`, threads the
    caller memory through, and (on the ok leg) pins the `tmp` block
    and layout for the sharing-call consumer. -/
theorem memEvalProgFuncOn_mergeRuns (prog : Prog) (F : Nat)
    (la lt : List (BitVec 32)) (lo mid hi : BitVec 64) (m₀ : Mem)
    (hlent : lt.length < 2 ^ 64)
    (hlo_mid : lo.toNat ≤ mid.toNat) (hmid_hi : mid.toNat ≤ hi.toNat)
    (hmid_le : mid.toNat ≤ la.length) (hhi_le : hi.toNat ≤ la.length)
    (hlo_lt : lo.toNat ≤ lt.length)
    (hF : ((mid.toNat - lo.toNat) + (hi.toNat - lo.toNat)) + 1 ≤ F) :
    ∃ m' π', (memEvalProgFuncOn prog F mergeRunsFunc
      [.stdVecVal la, .stdVecVal lt, .u64 lo, .u64 mid, .u64 hi] m₀ =
      match mergeRunsFwd la lt lo.toNat mid.toNat hi.toNat with
      | .error e => .error e
      | .ok (.stdVecVal lt') => .ok ((.stdVecVal lt'), m', π')
      | .ok _ => .error .AssertFail)
      ∧ (match mergeRunsFwd la lt lo.toNat mid.toNat hi.toNat with
      | .ok (.stdVecVal lt') =>
        memFind m' m₀.next =
          some ⟨m₀.next, true,
            (BitVec.ofNat 32 lt.length) :: lt'⟩ ∧
        memFind m' (m₀.next + 1) =
          some ⟨m₀.next + 1, true,
            (BitVec.ofNat 32 la.length) :: la⟩ ∧
        π' = [("a", m₀.next + 1, m₀.next + 1),
          ("tmp", m₀.next, m₀.next)]
      | _ => True) := by
  have hbind : bindMemArgs mergeRunsFunc.args
      [.stdVecVal la, .stdVecVal lt, .u64 lo, .u64 mid, .u64 hi]
      m₀ =
      some ([("a", .stdVecVal la), ("tmp", .stdVecVal lt),
        ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)],
        ⟨m₀.next + 2, (m₀.next + 1, ⟨m₀.next + 1, true, (BitVec.ofNat 32 la.length) :: la⟩) :: (m₀.next, ⟨m₀.next, true, (BitVec.ofNat 32 lt.length) :: lt⟩) :: m₀.blocks,
          m₀.blocks64⟩,
        [("a", m₀.next + 1, m₀.next + 1),
          ("tmp", m₀.next, m₀.next)]) :=
    bindMemArgsOn_vecMergeRuns la lt lo mid hi m₀
  have hbody : mergeRunsFunc.body =
      (.seq (.let_ "i" (.u 64) (.var "lo"))
        (.seq (.let_ "j" (.u 64) (.var "mid"))
          (.seq (.let_ "k" (.u 64) (.var "lo"))
            (.seq mergeRunsMain
              (.seq mergeRunsDrainI
                (.seq mergeRunsDrainJ
                  (.return_ (.var "tmp")))))))) := rfl
  have hvar_lo : evalExpr (.var "lo")
      [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
        ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)] =
      .ok (.u64 lo) :=
    evalExpr_var_hit _ _ _ rfl
  have hlet_i := memRevLet prog F "i" (.u 64) (.var "lo")
    [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
      ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
    ⟨m₀.next + 2, (m₀.next + 1, ⟨m₀.next + 1, true, (BitVec.ofNat 32 la.length) :: la⟩) :: (m₀.next, ⟨m₀.next, true, (BitVec.ofNat 32 lt.length) :: lt⟩) :: m₀.blocks, m₀.blocks64⟩
    [("a", m₀.next + 1, m₀.next + 1), ("tmp", m₀.next, m₀.next)] (.u64 lo)
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h)
    (memEvalExpr_var _ _ _ _) hvar_lo
  have hmid1 : envLookup
      (envExtend [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
        ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) "mid" =
      some (.u64 mid) := by
    rw [envExtend_miss _ _ _ _ (by decide : ("mid" : String) ≠ "i")]
    rfl
  have hvar_mid : evalExpr (.var "mid")
      (envExtend [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
        ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) =
      .ok (.u64 mid) :=
    evalExpr_var_hit _ _ _ hmid1
  have hlet_j := memRevLet prog F "j" (.u 64) (.var "mid")
    (envExtend [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
      ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
      "i" (.u64 lo))
    ⟨m₀.next + 2, (m₀.next + 1, ⟨m₀.next + 1, true, (BitVec.ofNat 32 la.length) :: la⟩) :: (m₀.next, ⟨m₀.next, true, (BitVec.ofNat 32 lt.length) :: lt⟩) :: m₀.blocks, m₀.blocks64⟩
    [("a", m₀.next + 1, m₀.next + 1), ("tmp", m₀.next, m₀.next)] (.u64 mid)
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h)
    (memEvalExpr_var _ _ _ _) hvar_mid
  have hlo2 : envLookup
      (envExtend (envExtend
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
          ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) "j" (.u64 mid)) "lo" =
      some (.u64 lo) := by
    rw [envExtend_miss _ _ _ _ (by decide : ("lo" : String) ≠ "j"),
      envExtend_miss _ _ _ _ (by decide : ("lo" : String) ≠ "i")]
    rfl
  have hvar_lo2 : evalExpr (.var "lo")
      (envExtend (envExtend
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
          ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) "j" (.u64 mid)) =
      .ok (.u64 lo) :=
    evalExpr_var_hit _ _ _ hlo2
  have hlet_k := memRevLet prog F "k" (.u 64) (.var "lo")
    (envExtend (envExtend
      [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
        ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
      "i" (.u64 lo)) "j" (.u64 mid))
    ⟨m₀.next + 2, (m₀.next + 1, ⟨m₀.next + 1, true, (BitVec.ofNat 32 la.length) :: la⟩) :: (m₀.next, ⟨m₀.next, true, (BitVec.ofNat 32 lt.length) :: lt⟩) :: m₀.blocks, m₀.blocks64⟩
    [("a", m₀.next + 1, m₀.next + 1), ("tmp", m₀.next, m₀.next)] (.u64 lo)
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h)
    (memEvalExpr_var _ _ _ _) hvar_lo2
  have hi3 : envLookup
      (envExtend (envExtend (envExtend
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
          ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) "j" (.u64 mid)) "k" (.u64 lo)) "i" =
      some (.u64 lo) := by
    rw [envExtend_miss _ _ _ _ (by decide : ("i" : String) ≠ "k"),
      envExtend_miss _ _ _ _ (by decide : ("i" : String) ≠ "j")]
    exact envExtend_hit _ _ _
  have hj3 : envLookup
      (envExtend (envExtend (envExtend
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
          ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) "j" (.u64 mid)) "k" (.u64 lo)) "j" =
      some (.u64 mid) := by
    rw [envExtend_miss _ _ _ _ (by decide : ("j" : String) ≠ "k")]
    exact envExtend_hit _ _ _
  have hk3 : envLookup
      (envExtend (envExtend (envExtend
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
          ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) "j" (.u64 mid)) "k" (.u64 lo)) "k" =
      some (.u64 lo) :=
    envExtend_hit _ _ _
  have ha3 : envLookup
      (envExtend (envExtend (envExtend
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
          ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) "j" (.u64 mid)) "k" (.u64 lo)) "a" =
      some (.stdVecVal la) := by
    rw [envExtend_miss _ _ _ _ (by decide : ("a" : String) ≠ "k"),
      envExtend_miss _ _ _ _ (by decide : ("a" : String) ≠ "j"),
      envExtend_miss _ _ _ _ (by decide : ("a" : String) ≠ "i")]
    rfl
  have hmid3 : envLookup
      (envExtend (envExtend (envExtend
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
          ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) "j" (.u64 mid)) "k" (.u64 lo)) "mid" =
      some (.u64 mid) := by
    rw [envExtend_miss _ _ _ _ (by decide : ("mid" : String) ≠ "k"),
      envExtend_miss _ _ _ _ (by decide : ("mid" : String) ≠ "j"),
      envExtend_miss _ _ _ _ (by decide : ("mid" : String) ≠ "i")]
    rfl
  have hhi3 : envLookup
      (envExtend (envExtend (envExtend
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
          ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) "j" (.u64 mid)) "k" (.u64 lo)) "hi" =
      some (.u64 hi) := by
    rw [envExtend_miss _ _ _ _ (by decide : ("hi" : String) ≠ "k"),
      envExtend_miss _ _ _ _ (by decide : ("hi" : String) ≠ "j"),
      envExtend_miss _ _ _ _ (by decide : ("hi" : String) ≠ "i")]
    rfl
  have htmp3 : envLookup
      (envExtend (envExtend (envExtend
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
          ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) "j" (.u64 mid)) "k" (.u64 lo)) "tmp" =
      some (.stdVecVal lt) := by
    rw [envExtend_miss _ _ _ _ (by decide : ("tmp" : String) ≠ "k"),
      envExtend_miss _ _ _ _ (by decide : ("tmp" : String) ≠ "j"),
      envExtend_miss _ _ _ _ (by decide : ("tmp" : String) ≠ "i")]
    rfl
  have hlay_a : layoutLookup [("a", m₀.next + 1, m₀.next + 1), ("tmp", m₀.next, m₀.next)] "a" =
      some (m₀.next + 1, m₀.next + 1) := by
    simp [layoutLookup]
  have hlay_tmp : layoutLookup [("a", m₀.next + 1, m₀.next + 1), ("tmp", m₀.next, m₀.next)] "tmp" =
      some (m₀.next, m₀.next) := by
    simp [layoutLookup]
  have hmem_a : memFind ⟨m₀.next + 2, (m₀.next + 1, ⟨m₀.next + 1, true, (BitVec.ofNat 32 la.length) :: la⟩) :: (m₀.next, ⟨m₀.next, true, (BitVec.ofNat 32 lt.length) :: lt⟩) :: m₀.blocks, m₀.blocks64⟩ (m₀.next + 1) =
      some ⟨m₀.next + 1, true, (BitVec.ofNat 32 la.length) :: la⟩ :=
    memFind_cons_hit _ _ _ _ _
  have hmem_b : memFind ⟨m₀.next + 2, (m₀.next + 1, ⟨m₀.next + 1, true, (BitVec.ofNat 32 la.length) :: la⟩) :: (m₀.next, ⟨m₀.next, true, (BitVec.ofNat 32 lt.length) :: lt⟩) :: m₀.blocks, m₀.blocks64⟩ m₀.next =
      some ⟨m₀.next, true, (BitVec.ofNat 32 lt.length) :: lt⟩ := by
    rw [memFind_cons_miss _ _ _ _ _ _ (by omega : m₀.next ≠ m₀.next + 1)]
    exact memFind_cons_hit _ _ _ _ _
  have hnB0 : BitVec.ofNat 32 lt.length =
      BitVec.ofNat 32 lt.length := rfl
  match hmain : mergeRunsMainFwd la lt
      ((mid.toNat - lo.toNat) + (hi.toNat - mid.toNat))
      lo.toNat mid.toNat lo.toNat mid.toNat hi.toNat with
  | .error e =>
    have hM := memRunsMain_err prog F
      (envExtend (envExtend (envExtend
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
          ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) "j" (.u64 mid)) "k" (.u64 lo))
      ⟨m₀.next + 2, (m₀.next + 1, ⟨m₀.next + 1, true, (BitVec.ofNat 32 la.length) :: la⟩) :: (m₀.next, ⟨m₀.next, true, (BitVec.ofNat 32 lt.length) :: lt⟩) :: m₀.blocks, m₀.blocks64⟩
      [("a", m₀.next + 1, m₀.next + 1), ("tmp", m₀.next, m₀.next)]
      la lt mid hi lo mid lo e
      (m₀.next + 1) m₀.next (m₀.next + 1) m₀.next (BitVec.ofNat 32 la.length) (BitVec.ofNat 32 lt.length)
      (by omega : m₀.next + 1 ≠ m₀.next)
      hlay_a hlay_tmp hmem_a hmem_b hnB0 hi3 hj3 hk3 ha3 hmid3 hhi3 htmp3
      hlent hmid_le hhi_le (by omega) (by simpa using hmain)
    have hfwd : mergeRunsFwd la lt lo.toNat mid.toNat hi.toNat =
        .error e := by
      simp [mergeRunsFwd, hmain]
    have hstmt : memEvalProgStmt prog F mergeRunsFunc.body
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
          ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        ⟨m₀.next + 2, (m₀.next + 1, ⟨m₀.next + 1, true, (BitVec.ofNat 32 la.length) :: la⟩) :: (m₀.next, ⟨m₀.next, true, (BitVec.ofNat 32 lt.length) :: lt⟩) :: m₀.blocks, m₀.blocks64⟩
        [("a", m₀.next + 1, m₀.next + 1), ("tmp", m₀.next, m₀.next)] =
        .error e := by
      rw [hbody,
        memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hlet_i,
        memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hlet_j,
        memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hlet_k,
        memEvalProgStmt_seq_err prog F _ _ _ _ _ _ hM]
    exact ⟨m₀, [("a", m₀.next + 1, m₀.next + 1),
      ("tmp", m₀.next, m₀.next)],
      by simp [hfwd, memEvalProgFuncOn, hbind, hstmt], by simp [hfwd]⟩
  | .ok (i₁, j₁, k₁, lt₁) =>
    obtain ⟨hi₁, hj₁, hk₁, hlen₁, hloi₁, hloj₁⟩ :=
      mergeRunsMainFwd_le la _ _ _ _ _ _ _ _ _ _ _
        hlo_mid hmid_hi hlo_lt hmain
    have hleno₁ : lt₁.length < 2 ^ 64 := by
      rw [hlen₁]; exact hlent
    have hk₁' : k₁ ≤ lt₁.length := by
      rw [hlen₁]; exact hk₁
    have ti₁ : (BitVec.ofNat 64 i₁).toNat = i₁ :=
      bv64_toNat_ofNat i₁ (Nat.lt_of_le_of_lt hi₁ (by omega))
    have tj₁ : (BitVec.ofNat 64 j₁).toNat = j₁ :=
      bv64_toNat_ofNat j₁ (Nat.lt_of_le_of_lt hj₁ (by omega))
    have tk₁ : (BitVec.ofNat 64 k₁).toNat = k₁ :=
      bv64_toNat_ofNat k₁ (Nat.lt_of_le_of_lt hk₁' hleno₁)
    have hM := memRunsMain_ok prog F
      (envExtend (envExtend (envExtend
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
          ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
        "i" (.u64 lo)) "j" (.u64 mid)) "k" (.u64 lo))
      ⟨m₀.next + 2, (m₀.next + 1, ⟨m₀.next + 1, true, (BitVec.ofNat 32 la.length) :: la⟩) :: (m₀.next, ⟨m₀.next, true, (BitVec.ofNat 32 lt.length) :: lt⟩) :: m₀.blocks, m₀.blocks64⟩
      [("a", m₀.next + 1, m₀.next + 1), ("tmp", m₀.next, m₀.next)]
      la lt mid hi lo mid lo i₁ j₁ k₁ lt₁
      (m₀.next + 1) m₀.next (m₀.next + 1) m₀.next (BitVec.ofNat 32 la.length) (BitVec.ofNat 32 lt.length)
      (by omega : m₀.next + 1 ≠ m₀.next)
      hlay_a hlay_tmp hmem_a hmem_b hnB0 hi3 hj3 hk3 ha3 hmid3 hhi3 htmp3
      hlent hmid_le hhi_le (by omega) (by simpa using hmain)
    obtain ⟨ρ₄, m₄, hMstmt, htmp₄, hi₄, hj₄, hk₄, ha₄, hmid₄, hhi₄,
      hmem_a₄, hmem_b₄, hnB₄⟩ := hM
    match hdrainI : mergeRunsDrainIFwd la lt₁ (mid.toNat - i₁)
        i₁ k₁ mid.toNat with
    | .error e =>
      have hdrainI' : mergeRunsDrainIFwd la lt₁
          (mid.toNat - (BitVec.ofNat 64 i₁).toNat)
          (BitVec.ofNat 64 i₁).toNat (BitVec.ofNat 64 k₁).toNat
          mid.toNat = .error e := by
        rw [ti₁, tk₁]; exact hdrainI
      have hI := memRunsDrainI_err prog F ρ₄ m₄
        [("a", m₀.next + 1, m₀.next + 1), ("tmp", m₀.next, m₀.next)]
        la lt₁ mid (BitVec.ofNat 64 i₁)
        (BitVec.ofNat 64 k₁) e
        (m₀.next + 1) m₀.next (m₀.next + 1) m₀.next (BitVec.ofNat 32 la.length) (BitVec.ofNat 32 lt.length)
        (by omega : m₀.next + 1 ≠ m₀.next)
        hlay_a hlay_tmp hmem_a₄ hmem_b₄ hnB₄ hi₄ hk₄ ha₄ hmid₄ htmp₄
        hleno₁ hmid_le (by rw [ti₁]; omega) hdrainI'
      have hfwd : mergeRunsFwd la lt lo.toNat mid.toNat hi.toNat =
          .error e := by
        simp [mergeRunsFwd, hmain, hdrainI]
      have hstmt : memEvalProgStmt prog F mergeRunsFunc.body
          [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
            ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
          ⟨m₀.next + 2, (m₀.next + 1, ⟨m₀.next + 1, true, (BitVec.ofNat 32 la.length) :: la⟩) :: (m₀.next, ⟨m₀.next, true, (BitVec.ofNat 32 lt.length) :: lt⟩) :: m₀.blocks, m₀.blocks64⟩
          [("a", m₀.next + 1, m₀.next + 1), ("tmp", m₀.next, m₀.next)] =
          .error e := by
        rw [hbody,
          memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hlet_i,
          memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hlet_j,
          memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hlet_k,
          memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hMstmt,
          memEvalProgStmt_seq_err prog F _ _ _ _ _ _ hI]
      exact ⟨m₀, [("a", m₀.next + 1, m₀.next + 1),
      ("tmp", m₀.next, m₀.next)],
      by simp [hfwd, memEvalProgFuncOn, hbind, hstmt], by simp [hfwd]⟩
    | .ok (i₂, k₂, lt₂) =>
      obtain ⟨hi₂, hk₂, hlen₂, hloi₂⟩ :=
        mergeRunsDrainIFwd_le la _ _ _ _ _ _ _ _ hi₁ hk₁' hdrainI
      have hdrainI' : mergeRunsDrainIFwd la lt₁
          (mid.toNat - (BitVec.ofNat 64 i₁).toNat)
          (BitVec.ofNat 64 i₁).toNat (BitVec.ofNat 64 k₁).toNat
          mid.toNat = .ok (i₂, k₂, lt₂) := by
        rw [ti₁, tk₁]; exact hdrainI
      have hleno₂ : lt₂.length < 2 ^ 64 := by
        rw [hlen₂, hlen₁]; exact hlent
      have hI := memRunsDrainI_ok prog F ρ₄ m₄
        [("a", m₀.next + 1, m₀.next + 1), ("tmp", m₀.next, m₀.next)]
        la lt₁ mid hi (BitVec.ofNat 64 i₁)
        (BitVec.ofNat 64 j₁) (BitVec.ofNat 64 k₁) i₂ k₂ lt₂
        (m₀.next + 1) m₀.next (m₀.next + 1) m₀.next (BitVec.ofNat 32 la.length) (BitVec.ofNat 32 lt.length)
        (by omega : m₀.next + 1 ≠ m₀.next)
        hlay_a hlay_tmp hmem_a₄ hmem_b₄ hnB₄ hi₄ hk₄ ha₄ hmid₄ htmp₄ hj₄ hhi₄
        hleno₁ hmid_le (by rw [ti₁]; omega) hdrainI'
      have hk₂' : k₂ ≤ lt₂.length := by
        rw [hlen₂]; exact hk₂
      have tk₂ : (BitVec.ofNat 64 k₂).toNat = k₂ :=
        bv64_toNat_ofNat k₂ (Nat.lt_of_le_of_lt hk₂' hleno₂)
      obtain ⟨ρ₅, m₅, hIstmt, htmp₅, hi₅, hk₅, ha₅, hmid₅, hj₅, hhi₅,
        hmem_a₅, hmem_b₅, hnB₅⟩ := hI
      match hdrainJ : mergeRunsDrainJFwd la lt₂ (hi.toNat - j₁)
          j₁ k₂ hi.toNat with
      | .error e =>
        have hdrainJ' : mergeRunsDrainJFwd la lt₂
            (hi.toNat - (BitVec.ofNat 64 j₁).toNat)
            (BitVec.ofNat 64 j₁).toNat (BitVec.ofNat 64 k₂).toNat
            hi.toNat = .error e := by
          rw [tj₁, tk₂]; exact hdrainJ
        have hJ := memRunsDrainJ_err prog F ρ₅ m₅
          [("a", m₀.next + 1, m₀.next + 1), ("tmp", m₀.next, m₀.next)]
          la lt₂ hi (BitVec.ofNat 64 j₁)
          (BitVec.ofNat 64 k₂) e
          (m₀.next + 1) m₀.next (m₀.next + 1) m₀.next (BitVec.ofNat 32 la.length) (BitVec.ofNat 32 lt.length)
          (by omega : m₀.next + 1 ≠ m₀.next)
          hlay_a hlay_tmp hmem_a₅ hmem_b₅ hnB₅ hj₅ hk₅ ha₅ hhi₅ htmp₅
          hleno₂ hhi_le (by rw [tj₁]; omega) hdrainJ'
        have hfwd : mergeRunsFwd la lt lo.toNat mid.toNat hi.toNat =
            .error e := by
          simp [mergeRunsFwd, hmain, hdrainI, hdrainJ]
        have hstmt : memEvalProgStmt prog F mergeRunsFunc.body
            [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
              ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
            ⟨m₀.next + 2, (m₀.next + 1, ⟨m₀.next + 1, true, (BitVec.ofNat 32 la.length) :: la⟩) :: (m₀.next, ⟨m₀.next, true, (BitVec.ofNat 32 lt.length) :: lt⟩) :: m₀.blocks, m₀.blocks64⟩
            [("a", m₀.next + 1, m₀.next + 1), ("tmp", m₀.next, m₀.next)] =
            .error e := by
          rw [hbody,
            memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hlet_i,
            memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hlet_j,
            memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hlet_k,
            memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hMstmt,
            memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hIstmt,
            memEvalProgStmt_seq_err prog F _ _ _ _ _ _ hJ]
        exact ⟨m₀, [("a", m₀.next + 1, m₀.next + 1),
      ("tmp", m₀.next, m₀.next)],
      by simp [hfwd, memEvalProgFuncOn, hbind, hstmt], by simp [hfwd]⟩
      | .ok (j₃, k₃, lt₃) =>
        obtain ⟨hj₃, hk₃, hlen₃, hloj₃⟩ :=
          mergeRunsDrainJFwd_le la _ _ _ _ _ _ _ _ hj₁ hk₂' hdrainJ
        have hdrainJ' : mergeRunsDrainJFwd la lt₂
            (hi.toNat - (BitVec.ofNat 64 j₁).toNat)
            (BitVec.ofNat 64 j₁).toNat (BitVec.ofNat 64 k₂).toNat
            hi.toNat = .ok (j₃, k₃, lt₃) := by
          rw [tj₁, tk₂]; exact hdrainJ
        have hleno₃ : lt₃.length < 2 ^ 64 := by
          rw [hlen₃, hlen₂, hlen₁]; exact hlent
        have hJ := memRunsDrainJ_ok prog F ρ₅ m₅
          [("a", m₀.next + 1, m₀.next + 1), ("tmp", m₀.next, m₀.next)]
          la lt₂ hi (BitVec.ofNat 64 j₁)
          (BitVec.ofNat 64 k₂) j₃ k₃ lt₃
          (m₀.next + 1) m₀.next (m₀.next + 1) m₀.next (BitVec.ofNat 32 la.length) (BitVec.ofNat 32 lt.length)
          (by omega : m₀.next + 1 ≠ m₀.next)
          hlay_a hlay_tmp hmem_a₅ hmem_b₅ hnB₅ hj₅ hk₅ ha₅ hhi₅ htmp₅
          hleno₂ hhi_le (by rw [tj₁]; omega) hdrainJ'
        obtain ⟨ρ₆, m₆, hJstmt, htmp₆, hj₆, hk₆, ha₆, hhi₆,
          hmem_a₆, hmem_b₆, hnB₆⟩ := hJ
        have hmem_ret : memEvalExpr (.var "tmp") ρ₆ m₆
            [("a", m₀.next + 1, m₀.next + 1), ("tmp", m₀.next, m₀.next)] = .ok (.stdVecVal lt₃) :=
          (memEvalExpr_var _ _ _ _).trans
            (evalExpr_var_hit _ _ _ htmp₆)
        have hret : memEvalProgStmt prog F (.return_ (.var "tmp"))
            ρ₆ m₆ [("a", m₀.next + 1, m₀.next + 1), ("tmp", m₀.next, m₀.next)] =
            .ok ((ρ₆, m₆, [("a", m₀.next + 1, m₀.next + 1), ("tmp", m₀.next, m₀.next)]),
              .returned (.stdVecVal lt₃)) :=
          memEvalProgStmt_return prog F _ _ _ _ _ hmem_ret
        have hfwd : mergeRunsFwd la lt lo.toNat mid.toNat hi.toNat =
            .ok (.stdVecVal lt₃) := by
          simp [mergeRunsFwd, hmain, hdrainI, hdrainJ]
        have hstmt : memEvalProgStmt prog F mergeRunsFunc.body
            [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
              ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]
            ⟨m₀.next + 2, (m₀.next + 1, ⟨m₀.next + 1, true, (BitVec.ofNat 32 la.length) :: la⟩) :: (m₀.next, ⟨m₀.next, true, (BitVec.ofNat 32 lt.length) :: lt⟩) :: m₀.blocks, m₀.blocks64⟩
            [("a", m₀.next + 1, m₀.next + 1), ("tmp", m₀.next, m₀.next)] =
            .ok ((ρ₆, m₆, [("a", m₀.next + 1, m₀.next + 1), ("tmp", m₀.next, m₀.next)]),
              .returned (.stdVecVal lt₃)) := by
          rw [hbody,
            memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hlet_i,
            memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hlet_j,
            memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hlet_k,
            memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hMstmt,
            memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hIstmt,
            memEvalProgStmt_seq_fallthrough prog F _ _ _ _ _ _ _ _ hJstmt]
          exact hret
        exact ⟨m₆, [("a", m₀.next + 1, m₀.next + 1),
          ("tmp", m₀.next, m₀.next)],
          by simp [hfwd, memEvalProgFuncOn, hbind, hstmt],
          by simp only [hfwd]; exact ⟨hmem_b₆, hmem_a₆, trivial⟩⟩
