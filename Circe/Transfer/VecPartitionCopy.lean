/-
Circe.Transfer.VecPartitionCopy — mem transfer for the
dual-record partition (`vec_partition_copy`, the
`std::partition_copy` idiom).

Mirrors the value side (`valPartitionCopyBody_yes/_no`,
`valPartitionCopyBody_shortYes/_shortNo`,
`valPartitionCopyLoop_ok/_err` in
`Circe.Emit.VecPartitionCopy`) step for step on the memory
layer. Each store threads through `memStore` in lockstep
while the other two blocks pin their snapshots: the source
`a` block and the idle record block are each framed across
every store via `memFind_memStore_other` (two framings per
store — the first dual-record write). The signed keeper
test agrees through `memEvalExpr_slt_agree`; both capacity
guards agree through `memEvalExpr_ult_agree` with length-cell
`memLoad`s (short record fails loud via guard-false +
fail). The loop re-inducts over `(ρ, m, π)` with the forward
equation threading (two fuels) plus both keep-counts,
both record bounds, and both record lengths. Entries close
against the forward contract; the closing specs tie the
keeper count to both filtered prefixes over the pure
`List.filter` oracle (`partitionCopyFwd_*` in `Circe.Specs`).
-/
import Circe.Transfer.VecCopyIf
import Circe.Emit.VecPartitionCopy
import Circe.Specs

/-! ## Binding (closed form) -/

/-- Partition-copy binding pins three snapshots: the
    shared-borrow input at addr `2`, the first mut-borrow
    record at addr `1`, the second at addr `0`
    (tail-first allocation order — the `vec_union`
    precedent). -/
theorem bindMemArgs_vecPartitionCopy (la yes no : List (BitVec 32))
    (pivot : BitVec 32) :
    bindMemArgs vecPartitionCopyFunc.args
      [.stdVecVal la, .stdVecVal yes, .stdVecVal no,
        .i32 pivot] emptyMem =
      some ([("a", .stdVecVal la), ("yes", .stdVecVal yes),
        ("no", .stdVecVal no), ("pivot", .i32 pivot)],
        (⟨3, [(2, ⟨2, true,
          (BitVec.ofNat 32 la.length) :: la⟩),
          (1, ⟨1, true,
          (BitVec.ofNat 32 yes.length) :: yes⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 no.length) :: no⟩)], []⟩ : Mem),
        [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)]) := by
  rfl

/-- Partition-copy footprint is three disjoint singletons. -/
theorem oracleNoalias_vecPartitionCopy (la yes no : List (BitVec 32))
    (pivot : BitVec 32) :
    oracleNoalias vecPartitionCopyFunc
      [.stdVecVal la, .stdVecVal yes, .stdVecVal no,
        .i32 pivot] := by
  have hb := bindMemArgs_vecPartitionCopy la yes no pivot
  have hn : LayoutNoAlias [("a", 2, 2), ("yes", 1, 1),
      ("no", 0, 0)] := by
    simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-! ## Memory body -/

/-- One body iteration on memory, keeper branch: the `slt`
    test agrees, the `yes` guard agrees and holds, the store
    lands in the `yes` block (`a` and `no` framed),
    `wYes` and `r` advance. -/
theorem memPartitionCopyBody_yes (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la yes no : List (BitVec 32)) (pivot : BitVec 32)
    (r wYes wNo : Nat) (rB wYesB wNoB : BitVec 64)
    (y wOld : BitVec 32)
    (aa ayes ano : Nat) (ta tyes tno : Nat)
    (na nyes nno : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_yes : layoutLookup π "yes" = some (ayes, tyes))
    (_hlay_no : layoutLookup π "no" = some (ano, tno))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_yes : memFind m ayes = some ⟨tyes, true, nyes :: yes⟩)
    (hmem_no : memFind m ano = some ⟨tno, true, nno :: no⟩)
    (_hna : na = BitVec.ofNat 32 la.length)
    (hnyes : nyes = BitVec.ofNat 32 yes.length)
    (_hnno : nno = BitVec.ofNat 32 no.length)
    (haa_yes : aa ≠ ayes) (_haa_no : aa ≠ ano)
    (hyes_no : ayes ≠ ano)
    (hrN : rB.toNat = r) (hwYesN : wYesB.toNat = wYes)
    (hwNoN : wNoB.toNat = wNo)
    (hla64 : la.length < 2 ^ 64) (hyes64 : yes.length < 2 ^ 64)
    (_hno64 : no.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hyes : envLookup ρ "yes" = some (.stdVecVal yes))
    (hno : envLookup ρ "no" = some (.stdVecVal no))
    (hpiv : envLookup ρ "pivot" = some (.i32 pivot))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hwYes : envLookup ρ "wYes" = some (.u64 wYesB))
    (hwNo : envLookup ρ "wNo" = some (.u64 wNoB))
    (hrlt : r < la.length)
    (hy : la[r]? = some y)
    (hkeep : (y.slt pivot) = true)
    (hwget : yes[wYes]? = some wOld)
    (hwlt : wYes < yes.length) :
    ∃ ρ' m', memEvalProgStmt prog F vecPartitionCopyBody ρ m π =
      .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "yes" = some (.stdVecVal (yes.set wYes y)) ∧
      envLookup ρ' "no" = some (.stdVecVal no) ∧
      envLookup ρ' "pivot" = some (.i32 pivot) ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r + 1) ∧
      (∃ wYesB', envLookup ρ' "wYes" = some (.u64 wYesB') ∧
        wYesB'.toNat = wYes + 1) ∧
      (∃ wNoB', envLookup ρ' "wNo" = some (.u64 wNoB') ∧
        wNoB'.toNat = wNo) ∧
      memFind m' ayes = some ⟨tyes, true, nyes :: (yes.set wYes y)⟩ ∧
      memFind m' aa = some ⟨ta, true, na :: la⟩ ∧
      memFind m' ano = some ⟨tno, true, nno :: no⟩ := by
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
  have hwYesVar : evalExpr (.var "wYes") ρ = .ok (.u64 wYesB) :=
    evalExpr_var_hit _ _ _ hwYes
  have hpivVar : evalExpr (.var "pivot") ρ = .ok (.i32 pivot) :=
    evalExpr_var_hit _ _ _ hpiv
  have hrVarM : memEvalExpr (.var "r") ρ m π = .ok (.u64 rB) :=
    (memEvalExpr_var _ _ _ _).trans hrVar
  have hwYesVarM : memEvalExpr (.var "wYes") ρ m π =
      .ok (.u64 wYesB) :=
    (memEvalExpr_var _ _ _ _).trans hwYesVar
  have hpivVarM : memEvalExpr (.var "pivot") ρ m π =
      .ok (.i32 pivot) :=
    (memEvalExpr_var _ _ _ _).trans hpivVar
  have hgetR : la[rB.toNat]? = some y := by rw [hrN]; exact hy
  have hgetW : yes[wYesB.toNat]? = some wOld := by
    rw [hwYesN]; exact hwget
  have hmemR : memLoad m aa ta (rB.toNat + 1) = .ok y :=
    memLoad_cellsAt m aa ta (rB.toNat + 1) (na :: la) y
      hmem_a (by rw [List.getElem?_cons_succ]; exact hgetR)
  have hat : evalExpr (.stdVecAt "a" (.var "r")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hrVar hgetR
  have hatM_ag : memEvalExpr (.stdVecAt "a" (.var "r")) ρ m π =
      evalExpr (.stdVecAt "a" (.var "r")) ρ :=
    memEvalExpr_stdVecAt_hit "a" (.var "r") ρ m π la rB y aa ta
      hlay_a ha (memEvalExpr_var _ _ _ _) hrVar hmemR hgetR
  have hatM : memEvalExpr (.stdVecAt "a" (.var "r")) ρ m π =
      .ok (.i32 y) := by rw [hatM_ag]; exact hat
  have hsltV : evalExpr
      (.slt (.stdVecAt "a" (.var "r")) (.var "pivot")) ρ =
      .ok (.b true) := by
    have h := evalExpr_slt_i32 (.stdVecAt "a" (.var "r"))
      (.var "pivot") ρ y pivot hat hpivVar
    rwa [hkeep] at h
  have hsltM : memEvalExpr
      (.slt (.stdVecAt "a" (.var "r")) (.var "pivot")) ρ m π =
      .ok (.b true) := by
    have hag := memEvalExpr_slt_agree (.stdVecAt "a" (.var "r"))
      (.var "pivot") ρ m π hatM_ag (memEvalExpr_var _ _ _ _)
    rw [hag]; exact hsltV
  have hmemLenY : memLoad m ayes tyes 0 =
      .ok (BitVec.ofNat 32 yes.length) := by
    rw [← hnyes]
    exact memLoad_cellsAt m ayes tyes 0 (nyes :: yes) nyes
      hmem_yes (by simp)
  have hlenM : memEvalExpr (.stdVecLen "yes") ρ m π =
      evalExpr (.stdVecLen "yes") ρ :=
    memEvalExpr_stdVecLen_hit "yes" ρ m π yes ayes tyes
      hlay_yes hyes hmemLenY
  have hguardV : evalExpr
      (.ult (.var "wYes") (.stdVecLen "yes")) ρ =
      .ok (.b true) := by
    have hlenN : (BitVec.ofNat 64 yes.length).toNat = yes.length := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hyes64
    have hult := evalExpr_ult_u64 (.var "wYes") (.stdVecLen "yes")
      ρ wYesB (BitVec.ofNat 64 yes.length) hwYesVar
      (evalExpr_stdVecLen_some _ _ _ hyes)
    have htb : (wYesB.ult (BitVec.ofNat 64 yes.length)) = true := by
      rw [BitVec.ult_eq_decide, hwYesN, hlenN]
      exact decide_eq_true (by omega)
    rwa [htb] at hult
  have hguardM : memEvalExpr
      (.ult (.var "wYes") (.stdVecLen "yes")) ρ m π =
      .ok (.b true) := by
    have hag := memEvalExpr_ult_agree (.var "wYes")
      (.stdVecLen "yes") ρ m π (memEvalExpr_var _ _ _ _) hlenM
    rw [hag]; exact hguardV
  have hlt₁ : wYesB.toNat + 1 < (nyes :: yes).length := by
    simp only [List.length_cons]
    omega
  obtain ⟨m₁, hmstore, hmem₁⟩ :=
    memStore_cellsAt_pin m ayes tyes y hmem_yes hlt₁
  have hsetB : yes.set wYesB.toNat y = yes.set wYes y := by
    rw [hwYesN]
  rw [hsetB] at hmem₁
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "yes"
    (.stdVecVal yes) (.stdVecVal (yes.set wYesB.toNat y)) hyes
  have hgetW : yes[wYesB.toNat]? = some wOld := by
    rw [hwYesN]; exact hwget
  have hstep_set := memRevVecSet prog F "yes" (.var "wYes")
    (.stdVecAt "a" (.var "r")) ρ m π wYesB y ayes tyes
    yes wOld m₁ ρ₁
    hwYesVarM hatM hyes hlay_yes hgetW hmstore hu₁
  have hmem_a₁ : memFind m₁ aa = some ⟨ta, true, na :: la⟩ := by
    have h := memFind_memStore_other m m₁ ayes aa tyes
      (wYesB.toNat + 1) y hmstore haa_yes
    rw [h]; exact hmem_a
  have hmem_no₁ : memFind m₁ ano = some ⟨tno, true, nno :: no⟩ := by
    have h := memFind_memStore_other m m₁ ayes ano tyes
      (wYesB.toNat + 1) y hmstore (Ne.symm hyes_no)
    rw [h]; exact hmem_no
  have ha₁ : envLookup ρ₁ "a" = some (.stdVecVal la) := by
    have h := envLookup_update_miss ρ "a" "yes" _ ρ₁
      (show ("a" : String) ≠ "yes" by decide) hu₁
    rw [h]; exact ha
  have hno₁ : envLookup ρ₁ "no" = some (.stdVecVal no) := by
    have h := envLookup_update_miss ρ "no" "yes" _ ρ₁
      (show ("no" : String) ≠ "yes" by decide) hu₁
    rw [h]; exact hno
  have hpiv₁ : envLookup ρ₁ "pivot" = some (.i32 pivot) := by
    have h := envLookup_update_miss ρ "pivot" "yes" _ ρ₁
      (show ("pivot" : String) ≠ "yes" by decide) hu₁
    rw [h]; exact hpiv
  have hr₁ : envLookup ρ₁ "r" = some (.u64 rB) := by
    have h := envLookup_update_miss ρ "r" "yes" _ ρ₁
      (show ("r" : String) ≠ "yes" by decide) hu₁
    rw [h]; exact hr
  have hwNo₁ : envLookup ρ₁ "wNo" = some (.u64 wNoB) := by
    have h := envLookup_update_miss ρ "wNo" "yes" _ ρ₁
      (show ("wNo" : String) ≠ "yes" by decide) hu₁
    rw [h]; exact hwNo
  have hevW : evalExpr (.uadd (.var "wYes")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁ =
      .ok (.u64 (wYesB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _
        (by rw [envLookup_update_miss _ _ _ _ _
          (show ("wYes" : String) ≠ "yes" by decide) hu₁]; exact hwYes))
      (by simp [evalExpr, litVal])
  have hevWM : memEvalExpr
      (.uadd (.var "wYes")
        (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁ m₁ π =
      .ok (.u64 (wYesB + 1)) :=
    (memEvalExpr_uadd_agree (.var "wYes")
      (.lit (.u64 (BitVec.ofNat 64 1)))
      ρ₁ m₁ π (memEvalExpr_var _ _ _ _)
      (memEvalExpr_lit _ _ _ _)).trans hevW
  obtain ⟨ρ₂, hu₂⟩ := envUpdate_some_of_lookup ρ₁ "wYes"
    (.u64 wYesB) (.u64 (wYesB + 1))
    (by rw [envLookup_update_miss _ _ _ _ _
      (show ("wYes" : String) ≠ "yes" by decide) hu₁]; exact hwYes)
  have hstep_w := memRevAssign prog F "wYes"
    (.uadd (.var "wYes") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁ m₁ π
    (.u64 (wYesB + 1)) ρ₂ hevWM hevW hu₂
  have hevR : evalExpr (.uadd (.var "r")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ =
      .ok (.u64 (rB + 1)) := by
    have hr₂' : envLookup ρ₂ "r" = some (.u64 rB) := by
      rw [envLookup_update_miss _ _ _ _ _
        (show ("r" : String) ≠ "wYes" by decide) hu₂]
      exact hr₁
    exact evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hr₂') (by simp [evalExpr, litVal])
  have hevRM : memEvalExpr (.uadd (.var "r")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ m₁ π =
      .ok (.u64 (rB + 1)) :=
    (memEvalExpr_uadd_agree (.var "r")
      (.lit (.u64 (BitVec.ofNat 64 1)))
      ρ₂ m₁ π (memEvalExpr_var _ _ _ _)
      (memEvalExpr_lit _ _ _ _)).trans hevR
  obtain ⟨ρ₃, hu₃⟩ := envUpdate_some_of_lookup ρ₂ "r"
    (.u64 rB) (.u64 (rB + 1)) (by
      rw [envLookup_update_miss _ _ _ _ _
        (show ("r" : String) ≠ "wYes" by decide) hu₂]
      exact hr₁)
  have hstep_r := memRevAssign prog F "r"
    (.uadd (.var "r") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ m₁ π
    (.u64 (rB + 1)) ρ₃ hevRM hevR hu₃
  have hyes₃ : envLookup ρ₃ "yes" =
      some (.stdVecVal (yes.set wYes y)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("yes" : String) ≠ "r" by decide) hu₃]
    rw [envLookup_update_miss _ _ _ _ _
      (show ("yes" : String) ≠ "wYes" by decide) hu₂]
    have h := envLookup_update_hit _ _ _ _ hu₁
    rwa [hsetB] at h
  have ha₃ : envLookup ρ₃ "a" = some (.stdVecVal la) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "r" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "wYes" by decide) hu₂]
    exact ha₁
  have hno₃ : envLookup ρ₃ "no" = some (.stdVecVal no) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("no" : String) ≠ "r" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("no" : String) ≠ "wYes" by decide) hu₂]
    exact hno₁
  have hpiv₃ : envLookup ρ₃ "pivot" = some (.i32 pivot) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("pivot" : String) ≠ "r" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("pivot" : String) ≠ "wYes" by decide) hu₂]
    exact hpiv₁
  have hwNo₃ : envLookup ρ₃ "wNo" = some (.u64 wNoB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("wNo" : String) ≠ "r" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("wNo" : String) ≠ "wYes" by decide) hu₂]
    exact hwNo₁
  have hrN' : (rB + 1).toNat = r + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hrN]
    exact Nat.mod_eq_of_lt (by omega)
  have hwYesN' : (wYesB + 1).toNat = wYes + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hwYesN]
    exact Nat.mod_eq_of_lt (by omega)
  have hr' : envLookup ρ₃ "r" = some (.u64 (rB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₃
  have hwYes₂ : envLookup ρ₂ "wYes" = some (.u64 (wYesB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₂
  have hwYes' : envLookup ρ₃ "wYes" = some (.u64 (wYesB + 1)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("wYes" : String) ≠ "r" by decide) hu₃]
    exact hwYes₂
  have hmem_a₃ : memFind m₁ aa = some ⟨ta, true, na :: la⟩ :=
    hmem_a₁
  have hmem_no₃ : memFind m₁ ano = some ⟨tno, true, nno :: no⟩ :=
    hmem_no₁
  have hinner : memEvalProgStmt prog F
      (.if_ (.ult (.var "wYes") (.stdVecLen "yes"))
        (.seq (.vecSet "yes" (.var "wYes")
                (.stdVecAt "a" (.var "r")))
          (.assign "wYes" (.uadd (.var "wYes")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        .fail) ρ m π = .ok ((ρ₂, m₁, π), .fellThrough) := by
    have hthen : memEvalProgStmt prog F
        (.seq (.vecSet "yes" (.var "wYes")
                (.stdVecAt "a" (.var "r")))
          (.assign "wYes" (.uadd (.var "wYes")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        ρ m π = .ok ((ρ₂, m₁, π), .fellThrough) := by
      rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
        hstep_set, hstep_w]
    exact (memEvalProgStmt_if_true prog F _ _ _ _ _ _ hguardM).trans
      hthen
  have hif : memEvalProgStmt prog F
      (.if_ (.slt (.stdVecAt "a" (.var "r")) (.var "pivot"))
        (.if_ (.ult (.var "wYes") (.stdVecLen "yes"))
          (.seq (.vecSet "yes" (.var "wYes")
                  (.stdVecAt "a" (.var "r")))
            (.assign "wYes" (.uadd (.var "wYes")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)
        (.if_ (.ult (.var "wNo") (.stdVecLen "no"))
          (.seq (.vecSet "no" (.var "wNo")
                  (.stdVecAt "a" (.var "r")))
            (.assign "wNo" (.uadd (.var "wNo")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)) ρ m π = .ok ((ρ₂, m₁, π), .fellThrough) :=
    (memEvalProgStmt_if_true prog F _ _ _ _ _ _ hsltM).trans hinner
  have hbody : vecPartitionCopyBody =
      (.seq (.if_ (.slt (.stdVecAt "a" (.var "r")) (.var "pivot"))
          (.if_ (.ult (.var "wYes") (.stdVecLen "yes"))
            (.seq (.vecSet "yes" (.var "wYes")
                    (.stdVecAt "a" (.var "r")))
              (.assign "wYes" (.uadd (.var "wYes")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
            .fail)
          (.if_ (.ult (.var "wNo") (.stdVecLen "no"))
            (.seq (.vecSet "no" (.var "wNo")
                    (.stdVecAt "a" (.var "r")))
              (.assign "wNo" (.uadd (.var "wNo")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
            .fail))
        (.assign "r" (.uadd (.var "r")
          (.lit (.u64 (BitVec.ofNat 64 1)))))) := rfl
  have heval : memEvalProgStmt prog F vecPartitionCopyBody ρ m π =
      .ok ((ρ₃, m₁, π), .fellThrough) := by
    rw [hbody,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hif,
      hstep_r]
  exact ⟨ρ₃, m₁, heval, ha₃, hyes₃, hno₃, hpiv₃,
    ⟨_, hr', hrN'⟩, ⟨_, hwYes', hwYesN'⟩,
    ⟨_, hwNo₃, hwNoN⟩, hmem₁, hmem_a₃, hmem_no₃⟩

/-- One body iteration on memory, dropper branch: the `slt`
    test disagrees, the `no` guard agrees and holds, the store
    lands in the `no` block (`a` and `yes` framed), `wNo` and
    `r` advance. -/
theorem memPartitionCopyBody_no (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la yes no : List (BitVec 32)) (pivot : BitVec 32)
    (r wYes wNo : Nat) (rB wYesB wNoB : BitVec 64)
    (y wOld : BitVec 32)
    (aa ayes ano : Nat) (ta tyes tno : Nat)
    (na nyes nno : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (_hlay_yes : layoutLookup π "yes" = some (ayes, tyes))
    (hlay_no : layoutLookup π "no" = some (ano, tno))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_yes : memFind m ayes = some ⟨tyes, true, nyes :: yes⟩)
    (hmem_no : memFind m ano = some ⟨tno, true, nno :: no⟩)
    (_hna : na = BitVec.ofNat 32 la.length)
    (_hnyes : nyes = BitVec.ofNat 32 yes.length)
    (hnno : nno = BitVec.ofNat 32 no.length)
    (_haa_yes : aa ≠ ayes) (haa_no : aa ≠ ano)
    (hyes_no : ayes ≠ ano)
    (hrN : rB.toNat = r) (hwYesN : wYesB.toNat = wYes)
    (hwNoN : wNoB.toNat = wNo)
    (hla64 : la.length < 2 ^ 64) (_hyes64 : yes.length < 2 ^ 64)
    (hno64 : no.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hyes : envLookup ρ "yes" = some (.stdVecVal yes))
    (hno : envLookup ρ "no" = some (.stdVecVal no))
    (hpiv : envLookup ρ "pivot" = some (.i32 pivot))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hwYes : envLookup ρ "wYes" = some (.u64 wYesB))
    (hwNo : envLookup ρ "wNo" = some (.u64 wNoB))
    (hrlt : r < la.length)
    (hy : la[r]? = some y)
    (hdrop : (y.slt pivot) = false)
    (hwget : no[wNo]? = some wOld)
    (hwlt : wNo < no.length) :
    ∃ ρ' m', memEvalProgStmt prog F vecPartitionCopyBody ρ m π =
      .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "yes" = some (.stdVecVal yes) ∧
      envLookup ρ' "no" = some (.stdVecVal (no.set wNo y)) ∧
      envLookup ρ' "pivot" = some (.i32 pivot) ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r + 1) ∧
      (∃ wYesB', envLookup ρ' "wYes" = some (.u64 wYesB') ∧
        wYesB'.toNat = wYes) ∧
      (∃ wNoB', envLookup ρ' "wNo" = some (.u64 wNoB') ∧
        wNoB'.toNat = wNo + 1) ∧
      memFind m' ano = some ⟨tno, true, nno :: (no.set wNo y)⟩ ∧
      memFind m' aa = some ⟨ta, true, na :: la⟩ ∧
      memFind m' ayes = some ⟨tyes, true, nyes :: yes⟩ := by
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
  have hwNoVar : evalExpr (.var "wNo") ρ = .ok (.u64 wNoB) :=
    evalExpr_var_hit _ _ _ hwNo
  have hpivVar : evalExpr (.var "pivot") ρ = .ok (.i32 pivot) :=
    evalExpr_var_hit _ _ _ hpiv
  have hrVarM : memEvalExpr (.var "r") ρ m π = .ok (.u64 rB) :=
    (memEvalExpr_var _ _ _ _).trans hrVar
  have hwNoVarM : memEvalExpr (.var "wNo") ρ m π =
      .ok (.u64 wNoB) :=
    (memEvalExpr_var _ _ _ _).trans hwNoVar
  have hgetR : la[rB.toNat]? = some y := by rw [hrN]; exact hy
  have hgetW : no[wNoB.toNat]? = some wOld := by
    rw [hwNoN]; exact hwget
  have hmemR : memLoad m aa ta (rB.toNat + 1) = .ok y :=
    memLoad_cellsAt m aa ta (rB.toNat + 1) (na :: la) y
      hmem_a (by rw [List.getElem?_cons_succ]; exact hgetR)
  have hat : evalExpr (.stdVecAt "a" (.var "r")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hrVar hgetR
  have hatM_ag : memEvalExpr (.stdVecAt "a" (.var "r")) ρ m π =
      evalExpr (.stdVecAt "a" (.var "r")) ρ :=
    memEvalExpr_stdVecAt_hit "a" (.var "r") ρ m π la rB y aa ta
      hlay_a ha (memEvalExpr_var _ _ _ _) hrVar hmemR hgetR
  have hatM : memEvalExpr (.stdVecAt "a" (.var "r")) ρ m π =
      .ok (.i32 y) := by rw [hatM_ag]; exact hat
  have hsltF : evalExpr
      (.slt (.stdVecAt "a" (.var "r")) (.var "pivot")) ρ =
      .ok (.b false) := by
    have h := evalExpr_slt_i32 (.stdVecAt "a" (.var "r"))
      (.var "pivot") ρ y pivot hat hpivVar
    rwa [hdrop] at h
  have hsltM : memEvalExpr
      (.slt (.stdVecAt "a" (.var "r")) (.var "pivot")) ρ m π =
      .ok (.b false) := by
    have hag := memEvalExpr_slt_agree (.stdVecAt "a" (.var "r"))
      (.var "pivot") ρ m π hatM_ag (memEvalExpr_var _ _ _ _)
    rw [hag]; exact hsltF
  have hmemLenN : memLoad m ano tno 0 =
      .ok (BitVec.ofNat 32 no.length) := by
    rw [← hnno]
    exact memLoad_cellsAt m ano tno 0 (nno :: no) nno hmem_no
      (by simp)
  have hlenM : memEvalExpr (.stdVecLen "no") ρ m π =
      evalExpr (.stdVecLen "no") ρ :=
    memEvalExpr_stdVecLen_hit "no" ρ m π no ano tno
      hlay_no hno hmemLenN
  have hlenN : (BitVec.ofNat 64 no.length).toNat = no.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hno64
  have hguardV : evalExpr
      (.ult (.var "wNo") (.stdVecLen "no")) ρ =
      .ok (.b true) := by
    have hult := evalExpr_ult_u64 (.var "wNo") (.stdVecLen "no") ρ
      wNoB (BitVec.ofNat 64 no.length) hwNoVar
      (evalExpr_stdVecLen_some _ _ _ hno)
    have htb : (wNoB.ult (BitVec.ofNat 64 no.length)) = true := by
      rw [BitVec.ult_eq_decide, hwNoN, hlenN]
      exact decide_eq_true (by omega)
    rwa [htb] at hult
  have hguardM : memEvalExpr
      (.ult (.var "wNo") (.stdVecLen "no")) ρ m π =
      .ok (.b true) := by
    have hag := memEvalExpr_ult_agree (.var "wNo")
      (.stdVecLen "no") ρ m π (memEvalExpr_var _ _ _ _) hlenM
    rw [hag]; exact hguardV
  have hlt₁ : wNoB.toNat + 1 < (nno :: no).length := by
    simp only [List.length_cons]
    omega
  obtain ⟨m₁, hmstore, hmem₁⟩ :=
    memStore_cellsAt_pin m ano tno y hmem_no hlt₁
  have hsetB : no.set wNoB.toNat y = no.set wNo y := by
    rw [hwNoN]
  rw [hsetB] at hmem₁
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "no"
    (.stdVecVal no) (.stdVecVal (no.set wNoB.toNat y)) hno
  have hgetW : no[wNoB.toNat]? = some wOld := by
    rw [hwNoN]; exact hwget
  have hstep_set := memRevVecSet prog F "no" (.var "wNo")
    (.stdVecAt "a" (.var "r")) ρ m π wNoB y ano tno
    no wOld m₁ ρ₁
    hwNoVarM hatM hno hlay_no hgetW hmstore hu₁
  have hmem_a₁ : memFind m₁ aa = some ⟨ta, true, na :: la⟩ := by
    have h := memFind_memStore_other m m₁ ano aa tno
      (wNoB.toNat + 1) y hmstore haa_no
    rw [h]; exact hmem_a
  have hmem_yes₁ : memFind m₁ ayes =
      some ⟨tyes, true, nyes :: yes⟩ := by
    have h := memFind_memStore_other m m₁ ano ayes tno
      (wNoB.toNat + 1) y hmstore hyes_no
    rw [h]; exact hmem_yes
  have ha₁ : envLookup ρ₁ "a" = some (.stdVecVal la) := by
    have h := envLookup_update_miss ρ "a" "no" _ ρ₁
      (show ("a" : String) ≠ "no" by decide) hu₁
    rw [h]; exact ha
  have hyes₁ : envLookup ρ₁ "yes" = some (.stdVecVal yes) := by
    have h := envLookup_update_miss ρ "yes" "no" _ ρ₁
      (show ("yes" : String) ≠ "no" by decide) hu₁
    rw [h]; exact hyes
  have hpiv₁ : envLookup ρ₁ "pivot" = some (.i32 pivot) := by
    have h := envLookup_update_miss ρ "pivot" "no" _ ρ₁
      (show ("pivot" : String) ≠ "no" by decide) hu₁
    rw [h]; exact hpiv
  have hr₁ : envLookup ρ₁ "r" = some (.u64 rB) := by
    have h := envLookup_update_miss ρ "r" "no" _ ρ₁
      (show ("r" : String) ≠ "no" by decide) hu₁
    rw [h]; exact hr
  have hwYes₁ : envLookup ρ₁ "wYes" = some (.u64 wYesB) := by
    have h := envLookup_update_miss ρ "wYes" "no" _ ρ₁
      (show ("wYes" : String) ≠ "no" by decide) hu₁
    rw [h]; exact hwYes
  have hevW : evalExpr (.uadd (.var "wNo")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁ =
      .ok (.u64 (wNoB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _
        (by rw [envLookup_update_miss _ _ _ _ _
          (show ("wNo" : String) ≠ "no" by decide) hu₁]; exact hwNo))
      (by simp [evalExpr, litVal])
  have hevWM : memEvalExpr
      (.uadd (.var "wNo")
        (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁ m₁ π =
      .ok (.u64 (wNoB + 1)) :=
    (memEvalExpr_uadd_agree (.var "wNo")
      (.lit (.u64 (BitVec.ofNat 64 1)))
      ρ₁ m₁ π (memEvalExpr_var _ _ _ _)
      (memEvalExpr_lit _ _ _ _)).trans hevW
  obtain ⟨ρ₂, hu₂⟩ := envUpdate_some_of_lookup ρ₁ "wNo"
    (.u64 wNoB) (.u64 (wNoB + 1))
    (by rw [envLookup_update_miss _ _ _ _ _
      (show ("wNo" : String) ≠ "no" by decide) hu₁]; exact hwNo)
  have hstep_w := memRevAssign prog F "wNo"
    (.uadd (.var "wNo") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁ m₁ π
    (.u64 (wNoB + 1)) ρ₂ hevWM hevW hu₂
  have hevR : evalExpr (.uadd (.var "r")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ =
      .ok (.u64 (rB + 1)) := by
    have hr₂' : envLookup ρ₂ "r" = some (.u64 rB) := by
      rw [envLookup_update_miss _ _ _ _ _
        (show ("r" : String) ≠ "wNo" by decide) hu₂]
      exact hr₁
    exact evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hr₂') (by simp [evalExpr, litVal])
  have hevRM : memEvalExpr (.uadd (.var "r")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ m₁ π =
      .ok (.u64 (rB + 1)) :=
    (memEvalExpr_uadd_agree (.var "r")
      (.lit (.u64 (BitVec.ofNat 64 1)))
      ρ₂ m₁ π (memEvalExpr_var _ _ _ _)
      (memEvalExpr_lit _ _ _ _)).trans hevR
  obtain ⟨ρ₃, hu₃⟩ := envUpdate_some_of_lookup ρ₂ "r"
    (.u64 rB) (.u64 (rB + 1)) (by
      rw [envLookup_update_miss _ _ _ _ _
        (show ("r" : String) ≠ "wNo" by decide) hu₂]
      exact hr₁)
  have hstep_r := memRevAssign prog F "r"
    (.uadd (.var "r") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ m₁ π
    (.u64 (rB + 1)) ρ₃ hevRM hevR hu₃
  have hno₃ : envLookup ρ₃ "no" =
      some (.stdVecVal (no.set wNo y)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("no" : String) ≠ "r" by decide) hu₃]
    rw [envLookup_update_miss _ _ _ _ _
      (show ("no" : String) ≠ "wNo" by decide) hu₂]
    have h := envLookup_update_hit _ _ _ _ hu₁
    rwa [hsetB] at h
  have ha₃ : envLookup ρ₃ "a" = some (.stdVecVal la) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "r" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "wNo" by decide) hu₂]
    exact ha₁
  have hyes₃ : envLookup ρ₃ "yes" = some (.stdVecVal yes) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("yes" : String) ≠ "r" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("yes" : String) ≠ "wNo" by decide) hu₂]
    exact hyes₁
  have hpiv₃ : envLookup ρ₃ "pivot" = some (.i32 pivot) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("pivot" : String) ≠ "r" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("pivot" : String) ≠ "wNo" by decide) hu₂]
    exact hpiv₁
  have hwYes₃ : envLookup ρ₃ "wYes" = some (.u64 wYesB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("wYes" : String) ≠ "r" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("wYes" : String) ≠ "wNo" by decide) hu₂]
    exact hwYes₁
  have hrN' : (rB + 1).toNat = r + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hrN]
    exact Nat.mod_eq_of_lt (by omega)
  have hwNoN' : (wNoB + 1).toNat = wNo + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hwNoN]
    exact Nat.mod_eq_of_lt (by omega)
  have hr' : envLookup ρ₃ "r" = some (.u64 (rB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₃
  have hwNo₂ : envLookup ρ₂ "wNo" = some (.u64 (wNoB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₂
  have hwNo' : envLookup ρ₃ "wNo" = some (.u64 (wNoB + 1)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("wNo" : String) ≠ "r" by decide) hu₃]
    exact hwNo₂
  have hmem_a₃ : memFind m₁ aa = some ⟨ta, true, na :: la⟩ :=
    hmem_a₁
  have hmem_yes₃ : memFind m₁ ayes = some ⟨tyes, true, nyes :: yes⟩ :=
    hmem_yes₁
  have hinner : memEvalProgStmt prog F
      (.if_ (.ult (.var "wNo") (.stdVecLen "no"))
        (.seq (.vecSet "no" (.var "wNo")
                (.stdVecAt "a" (.var "r")))
          (.assign "wNo" (.uadd (.var "wNo")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        .fail) ρ m π = .ok ((ρ₂, m₁, π), .fellThrough) := by
    have hthen : memEvalProgStmt prog F
        (.seq (.vecSet "no" (.var "wNo")
                (.stdVecAt "a" (.var "r")))
          (.assign "wNo" (.uadd (.var "wNo")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        ρ m π = .ok ((ρ₂, m₁, π), .fellThrough) := by
      rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
        hstep_set, hstep_w]
    exact (memEvalProgStmt_if_true prog F _ _ _ _ _ _ hguardM).trans
      hthen
  have hif : memEvalProgStmt prog F
      (.if_ (.slt (.stdVecAt "a" (.var "r")) (.var "pivot"))
        (.if_ (.ult (.var "wYes") (.stdVecLen "yes"))
          (.seq (.vecSet "yes" (.var "wYes")
                  (.stdVecAt "a" (.var "r")))
            (.assign "wYes" (.uadd (.var "wYes")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)
        (.if_ (.ult (.var "wNo") (.stdVecLen "no"))
          (.seq (.vecSet "no" (.var "wNo")
                  (.stdVecAt "a" (.var "r")))
            (.assign "wNo" (.uadd (.var "wNo")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)) ρ m π = .ok ((ρ₂, m₁, π), .fellThrough) := by
    exact (memEvalProgStmt_if_false prog F _ _ _ _ _ _
      hsltM).trans hinner
  have hbody : vecPartitionCopyBody =
      (.seq (.if_ (.slt (.stdVecAt "a" (.var "r")) (.var "pivot"))
          (.if_ (.ult (.var "wYes") (.stdVecLen "yes"))
            (.seq (.vecSet "yes" (.var "wYes")
                    (.stdVecAt "a" (.var "r")))
              (.assign "wYes" (.uadd (.var "wYes")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
            .fail)
          (.if_ (.ult (.var "wNo") (.stdVecLen "no"))
            (.seq (.vecSet "no" (.var "wNo")
                    (.stdVecAt "a" (.var "r")))
              (.assign "wNo" (.uadd (.var "wNo")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
            .fail))
        (.assign "r" (.uadd (.var "r")
          (.lit (.u64 (BitVec.ofNat 64 1)))))) := rfl
  have heval : memEvalProgStmt prog F vecPartitionCopyBody ρ m π =
      .ok ((ρ₃, m₁, π), .fellThrough) := by
    rw [hbody,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hif,
      hstep_r]
  exact ⟨ρ₃, m₁, heval, ha₃, hyes₃, hno₃, hpiv₃,
    ⟨_, hr', hrN'⟩, ⟨_, hwYes₃, hwYesN⟩,
    ⟨_, hwNo', hwNoN'⟩, hmem₁, hmem_a₃, hmem_yes₃⟩

/-- One body iteration on memory, short-`yes` branch: the
    `slt` test agrees, the `yes` guard fails, loud `AssertFail`
    (no store happens, so no block changes). -/
theorem memPartitionCopyBody_shortYes (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la yes : List (BitVec 32)) (pivot : BitVec 32)
    (r wYes : Nat) (rB wYesB : BitVec 64) (y : BitVec 32)
    (aa ayes : Nat) (ta tyes : Nat) (na nyes : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_yes : layoutLookup π "yes" = some (ayes, tyes))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_yes : memFind m ayes = some ⟨tyes, true, nyes :: yes⟩)
    (_hna : na = BitVec.ofNat 32 la.length)
    (hnyes : nyes = BitVec.ofNat 32 yes.length)
    (_haa_yes : aa ≠ ayes)
    (hrN : rB.toNat = r) (hwYesN : wYesB.toNat = wYes)
    (hyes64 : yes.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hyes : envLookup ρ "yes" = some (.stdVecVal yes))
    (hpiv : envLookup ρ "pivot" = some (.i32 pivot))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hwYes : envLookup ρ "wYes" = some (.u64 wYesB))
    (_hrlt : r < la.length)
    (hy : la[r]? = some y)
    (hkeep : (y.slt pivot) = true)
    (hmiss : yes[wYes]? = none) :
    memEvalProgStmt prog F vecPartitionCopyBody ρ m π =
      .error .AssertFail := by
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
  have hwYesVar : evalExpr (.var "wYes") ρ = .ok (.u64 wYesB) :=
    evalExpr_var_hit _ _ _ hwYes
  have hpivVar : evalExpr (.var "pivot") ρ = .ok (.i32 pivot) :=
    evalExpr_var_hit _ _ _ hpiv
  have hgetR : la[rB.toNat]? = some y := by rw [hrN]; exact hy
  have hmemR : memLoad m aa ta (rB.toNat + 1) = .ok y :=
    memLoad_cellsAt m aa ta (rB.toNat + 1) (na :: la) y
      hmem_a (by rw [List.getElem?_cons_succ]; exact hgetR)
  have hat : evalExpr (.stdVecAt "a" (.var "r")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hrVar hgetR
  have hatM_ag : memEvalExpr (.stdVecAt "a" (.var "r")) ρ m π =
      evalExpr (.stdVecAt "a" (.var "r")) ρ :=
    memEvalExpr_stdVecAt_hit "a" (.var "r") ρ m π la rB y aa ta
      hlay_a ha (memEvalExpr_var _ _ _ _) hrVar hmemR hgetR
  have hatM : memEvalExpr (.stdVecAt "a" (.var "r")) ρ m π =
      .ok (.i32 y) := by rw [hatM_ag]; exact hat
  have hsltV : evalExpr
      (.slt (.stdVecAt "a" (.var "r")) (.var "pivot")) ρ =
      .ok (.b true) := by
    have h := evalExpr_slt_i32 (.stdVecAt "a" (.var "r"))
      (.var "pivot") ρ y pivot hat hpivVar
    rwa [hkeep] at h
  have hsltM : memEvalExpr
      (.slt (.stdVecAt "a" (.var "r")) (.var "pivot")) ρ m π =
      .ok (.b true) := by
    have hag := memEvalExpr_slt_agree (.stdVecAt "a" (.var "r"))
      (.var "pivot") ρ m π hatM_ag (memEvalExpr_var _ _ _ _)
    rw [hag]; exact hsltV
  have hnl : ¬ wYes < yes.length := by
    intro h
    have hsome : yes[wYes]? = some yes[wYes] :=
      List.getElem?_eq_getElem h
    rw [hsome] at hmiss
    simp at hmiss
  have hlenN : (BitVec.ofNat 64 yes.length).toNat = yes.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hyes64
  have hguardV : evalExpr
      (.ult (.var "wYes") (.stdVecLen "yes")) ρ =
      .ok (.b false) := by
    have hwYesVar' : evalExpr (.var "wYes") ρ = .ok (.u64 wYesB) :=
      evalExpr_var_hit _ _ _ hwYes
    have hult := evalExpr_ult_u64 (.var "wYes") (.stdVecLen "yes") ρ
      wYesB (BitVec.ofNat 64 yes.length) hwYesVar'
      (evalExpr_stdVecLen_some _ _ _ hyes)
    have hfb : (wYesB.ult (BitVec.ofNat 64 yes.length)) = false := by
      rw [BitVec.ult_eq_decide, hwYesN, hlenN]
      exact decide_eq_false (by omega)
    rwa [hfb] at hult
  have hmemLenY : memLoad m ayes tyes 0 =
      .ok (BitVec.ofNat 32 yes.length) := by
    rw [← hnyes]
    exact memLoad_cellsAt m ayes tyes 0 (nyes :: yes) nyes
      hmem_yes (by simp)
  have hlenM : memEvalExpr (.stdVecLen "yes") ρ m π =
      evalExpr (.stdVecLen "yes") ρ :=
    memEvalExpr_stdVecLen_hit "yes" ρ m π yes ayes tyes
      hlay_yes hyes hmemLenY
  have hguardM : memEvalExpr
      (.ult (.var "wYes") (.stdVecLen "yes")) ρ m π =
      .ok (.b false) := by
    have hag := memEvalExpr_ult_agree (.var "wYes")
      (.stdVecLen "yes") ρ m π (memEvalExpr_var _ _ _ _) hlenM
    rw [hag]; exact hguardV
  have hfail : memEvalProgStmt prog F .fail ρ m π =
      .error .AssertFail := by
    simpa [memEvalProgStmt] using (memEvalStmtFuel_fail F ρ m π)
  have hinner : memEvalProgStmt prog F
      (.if_ (.ult (.var "wYes") (.stdVecLen "yes"))
        (.seq (.vecSet "yes" (.var "wYes")
                (.stdVecAt "a" (.var "r")))
          (.assign "wYes" (.uadd (.var "wYes")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        .fail) ρ m π = .error .AssertFail :=
    (memEvalProgStmt_if_false prog F _ _ _ _ _ _ hguardM).trans
      hfail
  have hif : memEvalProgStmt prog F
      (.if_ (.slt (.stdVecAt "a" (.var "r")) (.var "pivot"))
        (.if_ (.ult (.var "wYes") (.stdVecLen "yes"))
          (.seq (.vecSet "yes" (.var "wYes")
                  (.stdVecAt "a" (.var "r")))
            (.assign "wYes" (.uadd (.var "wYes")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)
        (.if_ (.ult (.var "wNo") (.stdVecLen "no"))
          (.seq (.vecSet "no" (.var "wNo")
                  (.stdVecAt "a" (.var "r")))
            (.assign "wNo" (.uadd (.var "wNo")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)) ρ m π = .error .AssertFail :=
    (memEvalProgStmt_if_true prog F _ _ _ _ _ _ hsltM).trans hinner
  have hbody : vecPartitionCopyBody =
      (.seq (.if_ (.slt (.stdVecAt "a" (.var "r")) (.var "pivot"))
          (.if_ (.ult (.var "wYes") (.stdVecLen "yes"))
            (.seq (.vecSet "yes" (.var "wYes")
                    (.stdVecAt "a" (.var "r")))
              (.assign "wYes" (.uadd (.var "wYes")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
            .fail)
          (.if_ (.ult (.var "wNo") (.stdVecLen "no"))
            (.seq (.vecSet "no" (.var "wNo")
                    (.stdVecAt "a" (.var "r")))
              (.assign "wNo" (.uadd (.var "wNo")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
            .fail))
        (.assign "r" (.uadd (.var "r")
          (.lit (.u64 (BitVec.ofNat 64 1)))))) := rfl
  rw [hbody]
  exact memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hif

/-- One body iteration on memory, short-`no` branch: the `slt`
    test disagrees, the `no` guard fails, loud `AssertFail`. -/
theorem memPartitionCopyBody_shortNo (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la no : List (BitVec 32)) (pivot : BitVec 32)
    (r wNo : Nat) (rB wNoB : BitVec 64) (y : BitVec 32)
    (aa ano : Nat) (ta tno : Nat) (na nno : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_no : layoutLookup π "no" = some (ano, tno))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_no : memFind m ano = some ⟨tno, true, nno :: no⟩)
    (_hna : na = BitVec.ofNat 32 la.length)
    (hnno : nno = BitVec.ofNat 32 no.length)
    (_haa_no : aa ≠ ano)
    (hrN : rB.toNat = r) (hwNoN : wNoB.toNat = wNo)
    (hno64 : no.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hno : envLookup ρ "no" = some (.stdVecVal no))
    (hpiv : envLookup ρ "pivot" = some (.i32 pivot))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hwNo : envLookup ρ "wNo" = some (.u64 wNoB))
    (_hrlt : r < la.length)
    (hy : la[r]? = some y)
    (hdrop : (y.slt pivot) = false)
    (hmiss : no[wNo]? = none) :
    memEvalProgStmt prog F vecPartitionCopyBody ρ m π =
      .error .AssertFail := by
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
  have hwNoVar : evalExpr (.var "wNo") ρ = .ok (.u64 wNoB) :=
    evalExpr_var_hit _ _ _ hwNo
  have hpivVar : evalExpr (.var "pivot") ρ = .ok (.i32 pivot) :=
    evalExpr_var_hit _ _ _ hpiv
  have hgetR : la[rB.toNat]? = some y := by rw [hrN]; exact hy
  have hmemR : memLoad m aa ta (rB.toNat + 1) = .ok y :=
    memLoad_cellsAt m aa ta (rB.toNat + 1) (na :: la) y
      hmem_a (by rw [List.getElem?_cons_succ]; exact hgetR)
  have hat : evalExpr (.stdVecAt "a" (.var "r")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hrVar hgetR
  have hatM_ag : memEvalExpr (.stdVecAt "a" (.var "r")) ρ m π =
      evalExpr (.stdVecAt "a" (.var "r")) ρ :=
    memEvalExpr_stdVecAt_hit "a" (.var "r") ρ m π la rB y aa ta
      hlay_a ha (memEvalExpr_var _ _ _ _) hrVar hmemR hgetR
  have hatM : memEvalExpr (.stdVecAt "a" (.var "r")) ρ m π =
      .ok (.i32 y) := by rw [hatM_ag]; exact hat
  have hsltF : evalExpr
      (.slt (.stdVecAt "a" (.var "r")) (.var "pivot")) ρ =
      .ok (.b false) := by
    have h := evalExpr_slt_i32 (.stdVecAt "a" (.var "r"))
      (.var "pivot") ρ y pivot hat hpivVar
    rwa [hdrop] at h
  have hsltM : memEvalExpr
      (.slt (.stdVecAt "a" (.var "r")) (.var "pivot")) ρ m π =
      .ok (.b false) := by
    have hag := memEvalExpr_slt_agree (.stdVecAt "a" (.var "r"))
      (.var "pivot") ρ m π hatM_ag (memEvalExpr_var _ _ _ _)
    rw [hag]; exact hsltF
  have hnl : ¬ wNo < no.length := by
    intro h
    have hsome : no[wNo]? = some no[wNo] :=
      List.getElem?_eq_getElem h
    rw [hsome] at hmiss
    simp at hmiss
  have hlenN : (BitVec.ofNat 64 no.length).toNat = no.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hno64
  have hguardV : evalExpr
      (.ult (.var "wNo") (.stdVecLen "no")) ρ =
      .ok (.b false) := by
    have hwNoVar' : evalExpr (.var "wNo") ρ = .ok (.u64 wNoB) :=
      evalExpr_var_hit _ _ _ hwNo
    have hult := evalExpr_ult_u64 (.var "wNo") (.stdVecLen "no") ρ
      wNoB (BitVec.ofNat 64 no.length) hwNoVar'
      (evalExpr_stdVecLen_some _ _ _ hno)
    have hfb : (wNoB.ult (BitVec.ofNat 64 no.length)) = false := by
      rw [BitVec.ult_eq_decide, hwNoN, hlenN]
      exact decide_eq_false (by omega)
    rwa [hfb] at hult
  have hmemLenN : memLoad m ano tno 0 =
      .ok (BitVec.ofNat 32 no.length) := by
    rw [← hnno]
    exact memLoad_cellsAt m ano tno 0 (nno :: no) nno hmem_no
      (by simp)
  have hlenM : memEvalExpr (.stdVecLen "no") ρ m π =
      evalExpr (.stdVecLen "no") ρ :=
    memEvalExpr_stdVecLen_hit "no" ρ m π no ano tno
      hlay_no hno hmemLenN
  have hguardM : memEvalExpr
      (.ult (.var "wNo") (.stdVecLen "no")) ρ m π =
      .ok (.b false) := by
    have hag := memEvalExpr_ult_agree (.var "wNo")
      (.stdVecLen "no") ρ m π (memEvalExpr_var _ _ _ _) hlenM
    rw [hag]; exact hguardV
  have hfail : memEvalProgStmt prog F .fail ρ m π =
      .error .AssertFail := by
    simpa [memEvalProgStmt] using (memEvalStmtFuel_fail F ρ m π)
  have hinner : memEvalProgStmt prog F
      (.if_ (.ult (.var "wNo") (.stdVecLen "no"))
        (.seq (.vecSet "no" (.var "wNo")
                (.stdVecAt "a" (.var "r")))
          (.assign "wNo" (.uadd (.var "wNo")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        .fail) ρ m π = .error .AssertFail :=
    (memEvalProgStmt_if_false prog F _ _ _ _ _ _ hguardM).trans
      hfail
  have hif : memEvalProgStmt prog F
      (.if_ (.slt (.stdVecAt "a" (.var "r")) (.var "pivot"))
        (.if_ (.ult (.var "wYes") (.stdVecLen "yes"))
          (.seq (.vecSet "yes" (.var "wYes")
                  (.stdVecAt "a" (.var "r")))
            (.assign "wYes" (.uadd (.var "wYes")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)
        (.if_ (.ult (.var "wNo") (.stdVecLen "no"))
          (.seq (.vecSet "no" (.var "wNo")
                  (.stdVecAt "a" (.var "r")))
            (.assign "wNo" (.uadd (.var "wNo")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)) ρ m π = .error .AssertFail :=
    (memEvalProgStmt_if_false prog F _ _ _ _ _ _ hsltM).trans hinner
  have hbody : vecPartitionCopyBody =
      (.seq (.if_ (.slt (.stdVecAt "a" (.var "r")) (.var "pivot"))
          (.if_ (.ult (.var "wYes") (.stdVecLen "yes"))
            (.seq (.vecSet "yes" (.var "wYes")
                    (.stdVecAt "a" (.var "r")))
              (.assign "wYes" (.uadd (.var "wYes")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
            .fail)
          (.if_ (.ult (.var "wNo") (.stdVecLen "no"))
            (.seq (.vecSet "no" (.var "wNo")
                    (.stdVecAt "a" (.var "r")))
              (.assign "wNo" (.uadd (.var "wNo")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
            .fail))
        (.assign "r" (.uadd (.var "r")
          (.lit (.u64 (BitVec.ofNat 64 1)))))) := rfl
  rw [hbody]
  exact memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hif


/-! ## Memory loop -/

/-- Loop bridge on memory, ok leg: both keep counts and both
    record bounds thread through the loop to the forward
    model, with both written blocks tracked. -/
theorem memPartitionCopyLoop_ok (prog : Prog) (F G : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la yes no : List (BitVec 32)) (pivot : BitVec 32)
    (r wYes wNo : Nat) (rB wYesB wNoB : BitVec 64)
    (yes' no' : List (BitVec 32)) (r' wYes' wNo' : Nat)
    (aa ayes ano : Nat) (ta tyes tno : Nat)
    (na nyes nno : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_yes : layoutLookup π "yes" = some (ayes, tyes))
    (hlay_no : layoutLookup π "no" = some (ano, tno))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_yes : memFind m ayes = some ⟨tyes, true, nyes :: yes⟩)
    (hmem_no : memFind m ano = some ⟨tno, true, nno :: no⟩)
    (hna : na = BitVec.ofNat 32 la.length)
    (hnyes : nyes = BitVec.ofNat 32 yes.length)
    (hnno : nno = BitVec.ofNat 32 no.length)
    (haa_yes : aa ≠ ayes) (haa_no : aa ≠ ano)
    (hyes_no : ayes ≠ ano)
    (hrN : rB.toNat = r) (hwYesN : wYesB.toNat = wYes)
    (hwNoN : wNoB.toNat = wNo)
    (hla64 : la.length < 2 ^ 64) (hyes64 : yes.length < 2 ^ 64)
    (hno64 : no.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hyes : envLookup ρ "yes" = some (.stdVecVal yes))
    (hno : envLookup ρ "no" = some (.stdVecVal no))
    (hpiv : envLookup ρ "pivot" = some (.i32 pivot))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hwYes : envLookup ρ "wYes" = some (.u64 wYesB))
    (hwNo : envLookup ρ "wNo" = some (.u64 wNoB))
    (hle : r ≤ la.length)
    (hF : la.length - r ≤ F) (hG : la.length - r ≤ G)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hwcntYes : ((la.take r).filter (fun z => z.slt pivot)).length
      = wYes)
    (hwcntNo : ((la.take r).filter
      (fun z => !(z.slt pivot))).length = wNo)
    (hcapYes : (la.filter (fun y => y.slt pivot)).length
      ≤ yes.length)
    (hcapNo : (la.filter (fun y => !(y.slt pivot))).length
      ≤ no.length)
    (hfwd : partitionCopyFwd pivot la yes no G r wYes wNo =
      .ok (r', wYes', wNo', yes', no')) :
    ∃ ρ' m', memEvalProgStmt prog F vecPartitionCopyLoop ρ m π =
      .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "yes" = some (.stdVecVal yes') ∧
      envLookup ρ' "no" = some (.stdVecVal no') ∧
      envLookup ρ' "pivot" = some (.i32 pivot) ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r') ∧
      (∃ wYesB', envLookup ρ' "wYes" = some (.u64 wYesB') ∧
        wYesB'.toNat = wYes') ∧
      (∃ wNoB', envLookup ρ' "wNo" = some (.u64 wNoB') ∧
        wNoB'.toNat = wNo') ∧
      memFind m' ayes = some ⟨tyes, true, nyes :: yes'⟩ ∧
      memFind m' ano = some ⟨tno, true, nno :: no'⟩ ∧
      memFind m' aa = some ⟨ta, true, na :: la⟩ := by
  induction F generalizing G ρ m yes no r wYes wNo
    rB wYesB wNoB with
  | zero =>
    have him : r = la.length := by omega
    have hguardF : memEvalExpr
        (.ult (.var "r") (.stdVecLen "a")) ρ m π =
        .ok (.b false) := by
      have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "a") ρ rB
        (BitVec.ofNat 64 la.length)
        (evalExpr_var_hit _ _ _ hr)
        (evalExpr_stdVecLen_some _ _ _ ha)
      have hlenN : (BitVec.ofNat 64 la.length).toNat =
          la.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
      have hfb : (rB.ult (BitVec.ofNat 64 la.length)) = false := by
        rw [BitVec.ult_eq_decide, hrN, him, hlenN]
        exact decide_eq_false (by omega)
      have hultF : evalExpr (.ult (.var "r") (.stdVecLen "a")) ρ =
          .ok (.b false) := by
        rwa [hfb] at hult
      have hmemLen : memLoad m aa ta 0 =
          .ok (BitVec.ofNat 32 la.length) := by
        rw [← hna]
        exact memLoad_cellsAt m aa ta 0 (na :: la) na hmem_a
          (by simp)
      have hag := memEvalExpr_ult_agree (.var "r")
        (.stdVecLen "a") ρ m π (memEvalExpr_var _ _ _ _)
        (memEvalExpr_stdVecLen_hit "a" ρ m π la aa ta
          hlay_a ha hmemLen)
      rw [hag]; exact hultF
    have hexit : memEvalProgStmt prog 0 vecPartitionCopyLoop
        ρ m π = .ok ((ρ, m, π), .fellThrough) :=
      memEvalProgStmt_while_false prog 0 _ _ _ _ _ hguardF
    have hpair : (r, wYes, wNo, yes, no) =
        (r', wYes', wNo', yes', no') := by
      cases G with
      | zero => simpa [partitionCopyFwd] using hfwd
      | succ G =>
        have hneg : ¬ r < la.length := by omega
        simpa [partitionCopyFwd, dite_eq_right hneg] using hfwd
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hpair
    exact ⟨ρ, m, hexit, ha, hyes, hno, hpiv, ⟨rB, hr, hrN⟩,
      ⟨wYesB, hwYes, hwYesN⟩, ⟨wNoB, hwNo, hwNoN⟩,
      hmem_yes, hmem_no, hmem_a⟩
  | succ F ih =>
    by_cases hlt : r < la.length
    · have hguardT : memEvalExpr
          (.ult (.var "r") (.stdVecLen "a")) ρ m π =
          .ok (.b true) := by
        have hlenN : (BitVec.ofNat 64 la.length).toNat =
            la.length := by
          rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
        have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "a") ρ
          rB (BitVec.ofNat 64 la.length)
          (evalExpr_var_hit _ _ _ hr)
          (evalExpr_stdVecLen_some _ _ _ ha)
        have htb : (rB.ult (BitVec.ofNat 64 la.length)) = true := by
          rw [BitVec.ult_eq_decide, hrN, hlenN]
          exact decide_eq_true hlt
        have hultT : evalExpr (.ult (.var "r") (.stdVecLen "a")) ρ =
            .ok (.b true) := by
          rwa [htb] at hult
        have hmemLen : memLoad m aa ta 0 =
            .ok (BitVec.ofNat 32 la.length) := by
          rw [← hna]
          exact memLoad_cellsAt m aa ta 0 (na :: la) na hmem_a
            (by simp)
        have hag := memEvalExpr_ult_agree (.var "r")
          (.stdVecLen "a") ρ m π (memEvalExpr_var _ _ _ _)
          (memEvalExpr_stdVecLen_hit "a" ρ m π la aa ta
            hlay_a ha hmemLen)
        rw [hag]; exact hultT
      obtain ⟨y, hy⟩ := hread r hlt
      cir_fuel_step (F, G, la.length - (r + 1))
      by_cases hkeep : (y.slt pivot) = true
      · by_cases hmiss : yes[wYes]? = none
        · have hcon := hfwd
          simp only [partitionCopyFwd, dite_eq_left hlt, hy, hkeep,
            hmiss] at hcon
          exact absurd hcon (by simp)
        · have hsome : ∃ z, yes[wYes]? = some z := by
            match h : yes[wYes]? with
            | none => exact absurd h hmiss
            | some z => exact ⟨z, rfl⟩
          obtain ⟨wOld, hwget⟩ := hsome
          have hwlt : wYes < yes.length := by
            have hsplit := partFilterYes_split pivot la r
              (by omega)
            have hstepY :=
              partFilterYes_take_succ pivot la r y hy hkeep
            have hkeeps1 := congrArg List.length hstepY
            rw [List.length_append, hwcntYes,
              List.length_singleton] at hkeeps1
            omega
          have hstepY :=
            partFilterYes_take_succ pivot la r y hy hkeep
          have hkeeps1 := congrArg List.length hstepY
          rw [List.length_append, hwcntYes,
            List.length_singleton] at hkeeps1
          have hwcntYes' := hkeeps1
          have hdropNo : (!(y.slt pivot)) = false := by
            simp [hkeep]
          have hstepNo :=
            partFilterNo_take_succ_drop pivot la r y hy hdropNo
          have hwcntNo' := congrArg List.length hstepNo
          rw [hwcntNo] at hwcntNo'
          have hlenS : (yes.set wYes y).length = yes.length := by
            simp [List.length_set]
          have hcapYes' : (la.filter
              (fun y => y.slt pivot)).length ≤
              (yes.set wYes y).length := by
            rw [hlenS]; exact hcapYes
          have hwltM : wYes < yes.length := hwlt
          have hF'' : la.length - (r + 1) ≤ F := by omega
          have hG'' : la.length - (r + 1) ≤ G' := by omega
          have hfwd' : partitionCopyFwd pivot la (yes.set wYes y)
              no G' (r + 1) (wYes + 1) wNo =
              .ok (r', wYes', wNo', yes', no') := by
            simpa only [partitionCopyFwd, dite_eq_left hlt, hy,
              hkeep, hwget, ite_true] using hfwd
          obtain ⟨ρ₁, m₁, hbody, ha₁, hyes₁, hno₁, hpiv₁,
              ⟨rB₁, hrB₁, hrN₁⟩, ⟨wYesB₁, hwYesB₁, hwYesN₁⟩,
              ⟨wNoB₁, hwNoB₁, hwNoN₁⟩, hmem₁, hmem_a₁,
              hmem_no₁⟩ :=
            memPartitionCopyBody_yes prog F ρ m π la yes no
              pivot r wYes wNo rB wYesB wNoB y wOld
              aa ayes ano ta tyes tno na nyes nno
              hlay_a hlay_yes hlay_no hmem_a hmem_yes hmem_no
              hna hnyes hnno haa_yes haa_no hyes_no
              hrN hwYesN hwNoN hla64 hyes64 hno64 ha hyes hno
              hpiv hr hwYes hwNo hlt hy hkeep hwget hwlt
          obtain ⟨ρ', m', hloop, ha', hyes', hno', hpiv',
              ⟨rB', hrB', hrN'⟩, ⟨wYesB', hwYesB', hwYesN'⟩,
              ⟨wNoB', hwNoB', hwNoN'⟩, hmem', hmem_no', hmem_a'⟩ :=
            ih (G := G') (ρ := ρ₁) (m := m₁)
              (yes := yes.set wYes y) (no := no)
              (r := r + 1) (wYes := wYes + 1) (wNo := wNo)
              (rB := rB₁) (wYesB := wYesB₁) (wNoB := wNoB₁)
              (hwYesN := hwYesN₁) (hwNoN := hwNoN₁) (hrN := hrN₁)
              (hyes64 := by rw [hlenS]; exact hyes64)
              (hno64 := hno64)
              (ha := ha₁) (hyes := hyes₁)
              (hno := hno₁) (hpiv := hpiv₁)
              (hr := hrB₁) (hwYes := hwYesB₁) (hwNo := hwNoB₁)
              (hle := by omega)
              (hF := hF'') (hG := hG'')
              (hwcntYes := hwcntYes') (hwcntNo := hwcntNo')
              (hcapYes := hcapYes') (hcapNo := hcapNo)
              (hfwd := hfwd')
              (hmem_a := hmem_a₁) (hmem_yes := hmem₁)
              (hmem_no := hmem_no₁)
              (hnyes := by rw [hlenS]; exact hnyes)
              (hnno := hnno)
          refine ⟨ρ', m', ?_, ha', hyes', hno', hpiv',
            ⟨rB', hrB', hrN'⟩, ⟨wYesB', hwYesB', hwYesN'⟩,
            ⟨wNoB', hwNoB', hwNoN'⟩, hmem', hmem_no', hmem_a'⟩
          have hwhile : memEvalProgStmt prog (F + 1)
              vecPartitionCopyLoop ρ m π =
              memEvalProgStmt prog F vecPartitionCopyLoop ρ₁ m₁
                π := by
            cir_unfold_prog (vecPartitionCopyLoop, prog, F, hguardT,
              hbody)
          rw [hwhile]
          exact hloop
      · have hdrop : (y.slt pivot) = false := by
          cases h : (y.slt pivot) with
          | true => exact absurd h hkeep
          | false => rfl
        have hkeepNo : (!(y.slt pivot)) = true := by simp [hdrop]
        by_cases hmiss : no[wNo]? = none
        · have hcon := hfwd
          simp only [partitionCopyFwd, dite_eq_left hlt, hy, hdrop,
            hmiss] at hcon
          exact absurd hcon (by simp)
        · have hsome : ∃ z, no[wNo]? = some z := by
            match h : no[wNo]? with
            | none => exact absurd h hmiss
            | some z => exact ⟨z, rfl⟩
          obtain ⟨wOld, hwget⟩ := hsome
          have hwlt : wNo < no.length := by
            have hsplit := partFilterNo_split pivot la r (by omega)
            have hstepN :=
              partFilterNo_take_succ pivot la r y hy hkeepNo
            have hkeeps1 := congrArg List.length hstepN
            rw [List.length_append, hwcntNo,
              List.length_singleton] at hkeeps1
            omega
          have hstepN :=
            partFilterNo_take_succ pivot la r y hy hkeepNo
          have hkeeps1 := congrArg List.length hstepN
          rw [List.length_append, hwcntNo,
            List.length_singleton] at hkeeps1
          have hwcntNo' := hkeeps1
          have hstepY :=
            partFilterYes_take_succ_drop pivot la r y hy hdrop
          have hwcntYes' := congrArg List.length hstepY
          rw [hwcntYes] at hwcntYes'
          have hlenS : (no.set wNo y).length = no.length := by
            simp [List.length_set]
          have hcapNo' : (la.filter
              (fun y => !(y.slt pivot))).length ≤
              (no.set wNo y).length := by
            rw [hlenS]; exact hcapNo
          have hwltM : wNo < no.length := hwlt
          have hF'' : la.length - (r + 1) ≤ F := by omega
          have hG'' : la.length - (r + 1) ≤ G' := by omega
          have hfwd' : partitionCopyFwd pivot la yes
              (no.set wNo y) G' (r + 1) wYes (wNo + 1) =
              .ok (r', wYes', wNo', yes', no') := by
            simpa only [partitionCopyFwd, dite_eq_left hlt, hy,
              hdrop, hwget, Bool.false_eq_true, ite_false] using hfwd
          obtain ⟨ρ₁, m₁, hbody, ha₁, hyes₁, hno₁, hpiv₁,
              ⟨rB₁, hrB₁, hrN₁⟩, ⟨wYesB₁, hwYesB₁, hwYesN₁⟩,
              ⟨wNoB₁, hwNoB₁, hwNoN₁⟩, hmem₁, hmem_a₁,
              hmem_yes₁⟩ :=
            memPartitionCopyBody_no prog F ρ m π la yes no
              pivot r wYes wNo rB wYesB wNoB y wOld
              aa ayes ano ta tyes tno na nyes nno
              hlay_a hlay_yes hlay_no hmem_a hmem_yes hmem_no
              hna hnyes hnno haa_yes haa_no hyes_no
              hrN hwYesN hwNoN hla64 hyes64 hno64 ha hyes hno
              hpiv hr hwYes hwNo hlt hy hdrop hwget hwlt
          obtain ⟨ρ', m', hloop, ha', hyes', hno', hpiv',
              ⟨rB', hrB', hrN'⟩, ⟨wYesB', hwYesB', hwYesN'⟩,
              ⟨wNoB', hwNoB', hwNoN'⟩, hmem', hmem_a', hmem_yes'⟩ :=
            ih (G := G') (ρ := ρ₁) (m := m₁)
              (yes := yes) (no := no.set wNo y)
              (r := r + 1) (wYes := wYes) (wNo := wNo + 1)
              (rB := rB₁) (wYesB := wYesB₁) (wNoB := wNoB₁)
              (hwYesN := hwYesN₁) (hwNoN := hwNoN₁) (hrN := hrN₁)
              (hyes64 := hyes64)
              (hno64 := by rw [hlenS]; exact hno64)
              (ha := ha₁) (hyes := hyes₁)
              (hno := hno₁) (hpiv := hpiv₁)
              (hr := hrB₁) (hwYes := hwYesB₁) (hwNo := hwNoB₁)
              (hle := by omega)
              (hF := hF'') (hG := hG'')
              (hwcntYes := hwcntYes') (hwcntNo := hwcntNo')
              (hcapYes := hcapYes) (hcapNo := hcapNo')
              (hfwd := hfwd')
              (hmem_a := hmem_a₁) (hmem_yes := hmem_yes₁)
              (hmem_no := hmem₁)
              (hnyes := hnyes)
              (hnno := by rw [hlenS]; exact hnno)
          refine ⟨ρ', m', ?_, ha', hyes', hno', hpiv',
            ⟨rB', hrB', hrN'⟩, ⟨wYesB', hwYesB', hwYesN'⟩,
            ⟨wNoB', hwNoB', hwNoN'⟩, hmem', hmem_a', hmem_yes'⟩
          have hwhile : memEvalProgStmt prog (F + 1)
              vecPartitionCopyLoop ρ m π =
              memEvalProgStmt prog F vecPartitionCopyLoop ρ₁ m₁
                π := by
            cir_unfold_prog (vecPartitionCopyLoop, prog, F, hguardT,
              hbody)
          rw [hwhile]
          exact hloop
    · have him : r = la.length := by omega
      have hguardF : memEvalExpr
          (.ult (.var "r") (.stdVecLen "a")) ρ m π =
          .ok (.b false) := by
        have hlenN : (BitVec.ofNat 64 la.length).toNat =
            la.length := by
          rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
        have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "a") ρ
          rB (BitVec.ofNat 64 la.length)
          (evalExpr_var_hit _ _ _ hr)
          (evalExpr_stdVecLen_some _ _ _ ha)
        have hfb : (rB.ult (BitVec.ofNat 64 la.length)) = false := by
          rw [BitVec.ult_eq_decide, hrN, hlenN]
          exact decide_eq_false (by omega)
        have hultF : evalExpr (.ult (.var "r") (.stdVecLen "a")) ρ =
            .ok (.b false) := by
          rwa [hfb] at hult
        have hmemLen : memLoad m aa ta 0 =
            .ok (BitVec.ofNat 32 la.length) := by
          rw [← hna]
          exact memLoad_cellsAt m aa ta 0 (na :: la) na hmem_a
            (by simp)
        have hag := memEvalExpr_ult_agree (.var "r")
          (.stdVecLen "a") ρ m π (memEvalExpr_var _ _ _ _)
          (memEvalExpr_stdVecLen_hit "a" ρ m π la aa ta
            hlay_a ha hmemLen)
        rw [hag]; exact hultF
      have hexit : memEvalProgStmt prog (F + 1) vecPartitionCopyLoop
          ρ m π = .ok ((ρ, m, π), .fellThrough) :=
        memEvalProgStmt_while_false prog (F + 1) _ _ _ _ _ hguardF
      have hpair : (r, wYes, wNo, yes, no) =
          (r', wYes', wNo', yes', no') := by
        cases G with
        | zero => simpa [partitionCopyFwd] using hfwd
        | succ G =>
          have hneg : ¬ r < la.length := by omega
          simpa [partitionCopyFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hpair
      exact ⟨ρ, m, hexit, ha, hyes, hno, hpiv, ⟨rB, hr, hrN⟩,
        ⟨wYesB, hwYes, hwYesN⟩, ⟨wNoB, hwNo, hwNoN⟩,
        hmem_yes, hmem_no, hmem_a⟩

/-- Loop bridge on memory, error leg: a short record on
    either side fails loud at the first overflowing store. -/
theorem memPartitionCopyLoop_err (prog : Prog) (F G : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la yes no : List (BitVec 32)) (pivot : BitVec 32)
    (r wYes wNo : Nat) (rB wYesB wNoB : BitVec 64)
    (aa ayes ano : Nat) (ta tyes tno : Nat)
    (na nyes nno : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_yes : layoutLookup π "yes" = some (ayes, tyes))
    (hlay_no : layoutLookup π "no" = some (ano, tno))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_yes : memFind m ayes = some ⟨tyes, true, nyes :: yes⟩)
    (hmem_no : memFind m ano = some ⟨tno, true, nno :: no⟩)
    (hna : na = BitVec.ofNat 32 la.length)
    (hnyes : nyes = BitVec.ofNat 32 yes.length)
    (hnno : nno = BitVec.ofNat 32 no.length)
    (haa_yes : aa ≠ ayes) (haa_no : aa ≠ ano)
    (hyes_no : ayes ≠ ano)
    (hrN : rB.toNat = r) (hwYesN : wYesB.toNat = wYes)
    (hwNoN : wNoB.toNat = wNo)
    (hla64 : la.length < 2 ^ 64) (hyes64 : yes.length < 2 ^ 64)
    (hno64 : no.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hyes : envLookup ρ "yes" = some (.stdVecVal yes))
    (hno : envLookup ρ "no" = some (.stdVecVal no))
    (hpiv : envLookup ρ "pivot" = some (.i32 pivot))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hwYes : envLookup ρ "wYes" = some (.u64 wYesB))
    (hwNo : envLookup ρ "wNo" = some (.u64 wNoB))
    (hle : r ≤ la.length)
    (hF : la.length - r ≤ F) (hG : la.length - r ≤ G)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hwcntYes : ((la.take r).filter (fun z => z.slt pivot)).length
      = wYes)
    (hwcntNo : ((la.take r).filter
      (fun z => !(z.slt pivot))).length = wNo)
    (hfwd : partitionCopyFwd pivot la yes no G r wYes wNo =
      .error .AssertFail) :
    memEvalProgStmt prog F vecPartitionCopyLoop ρ m π =
      .error .AssertFail := by
  induction F generalizing G ρ m yes no r wYes wNo
    rB wYesB wNoB with
  | zero =>
    have him : r = la.length := by omega
    subst him
    cases G with
    | zero => exact absurd hfwd (by simp [partitionCopyFwd])
    | succ _ =>
      have hneg : ¬ la.length < la.length := by omega
      have hcon := hfwd
      simp only [partitionCopyFwd, dite_eq_right hneg] at hcon
      exact absurd hcon (by simp)
  | succ F ih =>
    by_cases hlt : r < la.length
    · have hguardT : memEvalExpr
          (.ult (.var "r") (.stdVecLen "a")) ρ m π =
          .ok (.b true) := by
        have hlenN : (BitVec.ofNat 64 la.length).toNat =
            la.length := by
          rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
        have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "a") ρ
          rB (BitVec.ofNat 64 la.length)
          (evalExpr_var_hit _ _ _ hr)
          (evalExpr_stdVecLen_some _ _ _ ha)
        have htb : (rB.ult (BitVec.ofNat 64 la.length)) = true := by
          rw [BitVec.ult_eq_decide, hrN, hlenN]
          exact decide_eq_true hlt
        have hultT : evalExpr (.ult (.var "r") (.stdVecLen "a")) ρ =
            .ok (.b true) := by
          rwa [htb] at hult
        have hmemLen : memLoad m aa ta 0 =
            .ok (BitVec.ofNat 32 la.length) := by
          rw [← hna]
          exact memLoad_cellsAt m aa ta 0 (na :: la) na hmem_a
            (by simp)
        have hag := memEvalExpr_ult_agree (.var "r")
          (.stdVecLen "a") ρ m π (memEvalExpr_var _ _ _ _)
          (memEvalExpr_stdVecLen_hit "a" ρ m π la aa ta
            hlay_a ha hmemLen)
        rw [hag]; exact hultT
      obtain ⟨y, hy⟩ := hread r hlt
      cir_fuel_step (F, G, la.length - (r + 1))
      by_cases hkeep : (y.slt pivot) = true
      · by_cases hmiss : yes[wYes]? = none
        · have hshort := memPartitionCopyBody_shortYes prog F ρ
            m π la yes pivot r wYes rB wYesB y aa ayes ta tyes
            na nyes hlay_a hlay_yes hmem_a hmem_yes hna hnyes
            haa_yes hrN hwYesN hyes64 ha hyes hpiv hr hwYes
            hlt hy hkeep hmiss
          have hwhile : memEvalProgStmt prog (F + 1)
              vecPartitionCopyLoop ρ m π = .error .AssertFail := by
            have hloop : vecPartitionCopyLoop =
                (.while_ (.ult (.var "r") (.stdVecLen "a"))
                  vecPartitionCopyBody) := rfl
            rw [hloop, memEvalProgStmt_while_true prog F _ _ _ _ _
              hguardT, hshort]
          exact hwhile
        · have hsome : ∃ z, yes[wYes]? = some z := by
            match h : yes[wYes]? with
            | none => exact absurd h hmiss
            | some z => exact ⟨z, rfl⟩
          obtain ⟨wOld, hwget⟩ := hsome
          have hwlt : wYes < yes.length :=
            transformRead_lt yes wYes wOld hwget
          have hstepY :=
            partFilterYes_take_succ pivot la r y hy hkeep
          have hkeeps1 := congrArg List.length hstepY
          rw [List.length_append, hwcntYes,
            List.length_singleton] at hkeeps1
          have hwcntYes' := hkeeps1
          have hdropNo : (!(y.slt pivot)) = false := by
            simp [hkeep]
          have hstepNo :=
            partFilterNo_take_succ_drop pivot la r y hy hdropNo
          have hwcntNo' := congrArg List.length hstepNo
          rw [hwcntNo] at hwcntNo'
          have hF'' : la.length - (r + 1) ≤ F := by omega
          have hG'' : la.length - (r + 1) ≤ G' := by omega
          have hfwd' : partitionCopyFwd pivot la (yes.set wYes y)
              no G' (r + 1) (wYes + 1) wNo = .error .AssertFail := by
            have h := hfwd
            simp only [partitionCopyFwd, dite_eq_left hlt, hy,
              hkeep, hwget, ite_true] at h
            exact h
          obtain ⟨ρ₁, m₁, hbody, ha₁, hyes₁, hno₁, hpiv₁,
              ⟨rB₁, hrB₁, hrN₁⟩, ⟨wYesB₁, hwYesB₁, hwYesN₁⟩,
              ⟨wNoB₁, hwNoB₁, hwNoN₁⟩, hmem₁, hmem_a₁,
              hmem_no₁⟩ :=
            memPartitionCopyBody_yes prog F ρ m π la yes no
              pivot r wYes wNo rB wYesB wNoB y wOld
              aa ayes ano ta tyes tno na nyes nno
              hlay_a hlay_yes hlay_no hmem_a hmem_yes hmem_no
              hna hnyes hnno haa_yes haa_no hyes_no
              hrN hwYesN hwNoN hla64 hyes64 hno64 ha hyes hno
              hpiv hr hwYes hwNo hlt hy hkeep hwget hwlt
          have hloop : memEvalProgStmt prog F vecPartitionCopyLoop
              ρ₁ m₁ π = .error .AssertFail :=
            ih (G := G') (ρ := ρ₁) (m := m₁)
              (yes := yes.set wYes y) (no := no)
              (r := r + 1) (wYes := wYes + 1) (wNo := wNo)
              (rB := rB₁) (wYesB := wYesB₁) (wNoB := wNoB₁)
              (hwYesN := hwYesN₁) (hwNoN := hwNoN₁) (hrN := hrN₁)
              (hyes64 := by simpa [List.length_set] using hyes64)
              (hno64 := hno64)
              (ha := ha₁) (hyes := hyes₁)
              (hno := hno₁) (hpiv := hpiv₁)
              (hr := hrB₁) (hwYes := hwYesB₁) (hwNo := hwNoB₁)
              (hle := by omega)
              (hF := hF'') (hG := hG'')
              (hwcntYes := hwcntYes') (hwcntNo := hwcntNo')
              (hfwd := hfwd')
              (hmem_a := hmem_a₁) (hmem_yes := hmem₁)
              (hmem_no := hmem_no₁)
              (hnyes := by rw [List.length_set]; exact hnyes)
              (hnno := hnno)
          have hwhile : memEvalProgStmt prog (F + 1)
              vecPartitionCopyLoop ρ m π = .error .AssertFail := by
            cir_unfold_prog (vecPartitionCopyLoop, prog, F, hguardT,
              hbody)
            exact hloop
          exact hwhile
      · have hdrop : (y.slt pivot) = false := by
          cases h : (y.slt pivot) with
          | true => exact absurd h hkeep
          | false => rfl
        have hkeepNo : (!(y.slt pivot)) = true := by simp [hdrop]
        by_cases hmiss : no[wNo]? = none
        · have hshort := memPartitionCopyBody_shortNo prog F ρ
            m π la no pivot r wNo rB wNoB y aa ano ta tno na
            nno hlay_a hlay_no hmem_a hmem_no hna hnno haa_no
            hrN hwNoN hno64 ha hno hpiv hr hwNo hlt hy hdrop
            hmiss
          have hwhile : memEvalProgStmt prog (F + 1)
              vecPartitionCopyLoop ρ m π = .error .AssertFail := by
            have hloop : vecPartitionCopyLoop =
                (.while_ (.ult (.var "r") (.stdVecLen "a"))
                  vecPartitionCopyBody) := rfl
            rw [hloop, memEvalProgStmt_while_true prog F _ _ _ _ _
              hguardT, hshort]
          exact hwhile
        · have hsome : ∃ z, no[wNo]? = some z := by
            match h : no[wNo]? with
            | none => exact absurd h hmiss
            | some z => exact ⟨z, rfl⟩
          obtain ⟨wOld, hwget⟩ := hsome
          have hwlt : wNo < no.length :=
            transformRead_lt no wNo wOld hwget
          have hstepN :=
            partFilterNo_take_succ pivot la r y hy hkeepNo
          have hkeeps1 := congrArg List.length hstepN
          rw [List.length_append, hwcntNo,
            List.length_singleton] at hkeeps1
          have hwcntNo' := hkeeps1
          have hstepY :=
            partFilterYes_take_succ_drop pivot la r y hy hdrop
          have hwcntYes' := congrArg List.length hstepY
          rw [hwcntYes] at hwcntYes'
          have hF'' : la.length - (r + 1) ≤ F := by omega
          have hG'' : la.length - (r + 1) ≤ G' := by omega
          have hfwd' : partitionCopyFwd pivot la yes
              (no.set wNo y) G' (r + 1) wYes (wNo + 1) =
              .error .AssertFail := by
            have h := hfwd
            simp only [partitionCopyFwd, dite_eq_left hlt, hy,
              hdrop, hwget, Bool.false_eq_true, ite_false] at h
            exact h
          obtain ⟨ρ₁, m₁, hbody, ha₁, hyes₁, hno₁, hpiv₁,
              ⟨rB₁, hrB₁, hrN₁⟩, ⟨wYesB₁, hwYesB₁, hwYesN₁⟩,
              ⟨wNoB₁, hwNoB₁, hwNoN₁⟩, hmem₁, hmem_a₁,
              hmem_yes₁⟩ :=
            memPartitionCopyBody_no prog F ρ m π la yes no
              pivot r wYes wNo rB wYesB wNoB y wOld
              aa ayes ano ta tyes tno na nyes nno
              hlay_a hlay_yes hlay_no hmem_a hmem_yes hmem_no
              hna hnyes hnno haa_yes haa_no hyes_no
              hrN hwYesN hwNoN hla64 hyes64 hno64 ha hyes hno
              hpiv hr hwYes hwNo hlt hy hdrop hwget hwlt
          have hloop : memEvalProgStmt prog F vecPartitionCopyLoop
              ρ₁ m₁ π = .error .AssertFail :=
            ih (G := G') (ρ := ρ₁) (m := m₁)
              (yes := yes) (no := no.set wNo y)
              (r := r + 1) (wYes := wYes) (wNo := wNo + 1)
              (rB := rB₁) (wYesB := wYesB₁) (wNoB := wNoB₁)
              (hwYesN := hwYesN₁) (hwNoN := hwNoN₁) (hrN := hrN₁)
              (hyes64 := hyes64)
              (hno64 := by simpa [List.length_set] using hno64)
              (ha := ha₁) (hyes := hyes₁)
              (hno := hno₁) (hpiv := hpiv₁)
              (hr := hrB₁) (hwYes := hwYesB₁) (hwNo := hwNoB₁)
              (hle := by omega)
              (hF := hF'') (hG := hG'')
              (hwcntYes := hwcntYes') (hwcntNo := hwcntNo')
              (hfwd := hfwd')
              (hmem_a := hmem_a₁) (hmem_yes := hmem_yes₁)
              (hmem_no := hmem₁)
              (hnyes := hnyes)
              (hnno := by rw [List.length_set]; exact hnno)
          have hwhile : memEvalProgStmt prog (F + 1)
              vecPartitionCopyLoop ρ m π = .error .AssertFail := by
            cir_unfold_prog (vecPartitionCopyLoop, prog, F, hguardT,
              hbody)
            exact hloop
          exact hwhile
    · have him : r = la.length := by omega
      subst him
      cases G with
      | zero => exact absurd hfwd (by simp [partitionCopyFwd])
      | succ _ =>
        have hneg : ¬ la.length < la.length := by omega
        have hcon := hfwd
        simp only [partitionCopyFwd, dite_eq_right hneg] at hcon
        exact absurd hcon (by simp)

/-! ## Memory entries -/

/-- Memory entry, nil leg: the prelude binds the three cursors
    at 0, the loop exits immediately on the empty input, and the
    keeper count reads back 0. -/
theorem memEvalProgFunc_vecPartitionCopy_nil (F : Nat)
    (yes no : List (BitVec 32)) (pivot : BitVec 32)
    (hyes64 : yes.length < 2 ^ 64) (hno64 : no.length < 2 ^ 64) :
    memEvalProgFunc vecPartitionCopyProg F vecPartitionCopyFunc
      [.stdVecVal ([] : List (BitVec 32)),
        .stdVecVal yes, .stdVecVal no, .i32 pivot] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
  have hbind := bindMemArgs_vecPartitionCopy
    ([] : List (BitVec 32)) yes no pivot
  have hbody : vecPartitionCopyFunc.body =
      (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq (.let_ "wYes" (.u 64)
          (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq (.let_ "wNo" (.u 64)
            (.lit (.u64 (BitVec.ofNat 64 0))))
            (.seq vecPartitionCopyLoop
              (.return_ (.var "wYes")))))) := rfl
  have hlitR : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)]
      (⟨3, [(2, ⟨2, true,
        (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
          ([] : List (BitVec 32))⟩),
        (1, ⟨1, true,
        (BitVec.ofNat 32 yes.length) :: yes⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 no.length) :: no⟩)], []⟩ : Mem)
      [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal ([] : List (BitVec 32))),
          ("yes", .stdVecVal yes), ("no", .stdVecVal no),
          ("pivot", .i32 pivot)] :=
    memEvalExpr_lit _ _ _ _
  have hlitRV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletR := memRevLet vecPartitionCopyProg F "r" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("a", .stdVecVal ([] : List (BitVec 32))),
      ("yes", .stdVecVal yes), ("no", .stdVecVal no),
      ("pivot", .i32 pivot)]
    (⟨3, [(2, ⟨2, true,
      (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
        ([] : List (BitVec 32))⟩),
      (1, ⟨1, true,
      (BitVec.ofNat 32 yes.length) :: yes⟩),
      (0, ⟨0, true,
      (BitVec.ofNat 32 no.length) :: no⟩)], []⟩ : Mem)
    [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)]
    (.u64 (BitVec.ofNat 64 0))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) (by intro h; cases h) hlitR hlitRV
  have hlitW : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("a", .stdVecVal ([] : List (BitVec 32))),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
      (⟨3, [(2, ⟨2, true,
        (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
          ([] : List (BitVec 32))⟩),
        (1, ⟨1, true,
        (BitVec.ofNat 32 yes.length) :: yes⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 no.length) :: no⟩)], []⟩ : Mem)
      [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend [("a", .stdVecVal ([] : List (BitVec 32))),
          ("yes", .stdVecVal yes), ("no", .stdVecVal no),
          ("pivot", .i32 pivot)]
          "r" (.u64 (BitVec.ofNat 64 0))) :=
    memEvalExpr_lit _ _ _ _
  have hlitWV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("a", .stdVecVal ([] : List (BitVec 32))),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0))) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletW := memRevLet vecPartitionCopyProg F "wYes" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (envExtend [("a", .stdVecVal ([] : List (BitVec 32))),
      ("yes", .stdVecVal yes), ("no", .stdVecVal no),
      ("pivot", .i32 pivot)]
      "r" (.u64 (BitVec.ofNat 64 0)))
    (⟨3, [(2, ⟨2, true,
      (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
        ([] : List (BitVec 32))⟩),
      (1, ⟨1, true,
      (BitVec.ofNat 32 yes.length) :: yes⟩),
      (0, ⟨0, true,
      (BitVec.ofNat 32 no.length) :: no⟩)], []⟩ : Mem)
    [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)]
    (.u64 (BitVec.ofNat 64 0))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) (by intro h; cases h) hlitW hlitWV
  have hlitN : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend (envExtend
        [("a", .stdVecVal ([] : List (BitVec 32))),
          ("yes", .stdVecVal yes), ("no", .stdVecVal no),
          ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
      (⟨3, [(2, ⟨2, true,
        (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
          ([] : List (BitVec 32))⟩),
        (1, ⟨1, true,
        (BitVec.ofNat 32 yes.length) :: yes⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 no.length) :: no⟩)], []⟩ : Mem)
      [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend (envExtend
          [("a", .stdVecVal ([] : List (BitVec 32))),
            ("yes", .stdVecVal yes), ("no", .stdVecVal no),
            ("pivot", .i32 pivot)]
          "r" (.u64 (BitVec.ofNat 64 0)))
          "wYes" (.u64 (BitVec.ofNat 64 0))) :=
    memEvalExpr_lit _ _ _ _
  have hlitNV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend (envExtend
        [("a", .stdVecVal ([] : List (BitVec 32))),
          ("yes", .stdVecVal yes), ("no", .stdVecVal no),
          ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0))) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletN := memRevLet vecPartitionCopyProg F "wNo" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (envExtend (envExtend
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)]
      "r" (.u64 (BitVec.ofNat 64 0)))
      "wYes" (.u64 (BitVec.ofNat 64 0)))
    (⟨3, [(2, ⟨2, true,
      (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
        ([] : List (BitVec 32))⟩),
      (1, ⟨1, true,
      (BitVec.ofNat 32 yes.length) :: yes⟩),
      (0, ⟨0, true,
      (BitVec.ofNat 32 no.length) :: no⟩)], []⟩ : Mem)
    [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)]
    (.u64 (BitVec.ofNat 64 0))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) (by intro h; cases h) hlitN hlitNV
  have hw0N : (BitVec.ofNat 64 0).toNat = 0 := by decide
  have haN : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)]
      "r" (.u64 (BitVec.ofNat 64 0)))
      "wYes" (.u64 (BitVec.ofNat 64 0)))
      "wNo" (.u64 (BitVec.ofNat 64 0))) "a" =
      some (.stdVecVal ([] : List (BitVec 32))) := by
    rw [envExtend_miss _ _ _ _
      (show ("a" : String) ≠ "wNo" by decide),
      envExtend_miss _ _ _ _
      (show ("a" : String) ≠ "wYes" by decide),
      envExtend_miss _ _ _ _
      (show ("a" : String) ≠ "r" by decide)]
    simp [envLookup]
  have hyesN : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)]
      "r" (.u64 (BitVec.ofNat 64 0)))
      "wYes" (.u64 (BitVec.ofNat 64 0)))
      "wNo" (.u64 (BitVec.ofNat 64 0))) "yes" =
      some (.stdVecVal yes) := by
    rw [envExtend_miss _ _ _ _
      (show ("yes" : String) ≠ "wNo" by decide),
      envExtend_miss _ _ _ _
      (show ("yes" : String) ≠ "wYes" by decide),
      envExtend_miss _ _ _ _
      (show ("yes" : String) ≠ "r" by decide)]
    simp [envLookup, show ("yes" : String) ≠ "a" by decide]
  have hnoN : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)]
      "r" (.u64 (BitVec.ofNat 64 0)))
      "wYes" (.u64 (BitVec.ofNat 64 0)))
      "wNo" (.u64 (BitVec.ofNat 64 0))) "no" =
      some (.stdVecVal no) := by
    rw [envExtend_miss _ _ _ _
      (show ("no" : String) ≠ "wNo" by decide),
      envExtend_miss _ _ _ _
      (show ("no" : String) ≠ "wYes" by decide),
      envExtend_miss _ _ _ _
      (show ("no" : String) ≠ "r" by decide)]
    simp [envLookup, show ("no" : String) ≠ "a" by decide]
  have hpivN : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)]
      "r" (.u64 (BitVec.ofNat 64 0)))
      "wYes" (.u64 (BitVec.ofNat 64 0)))
      "wNo" (.u64 (BitVec.ofNat 64 0))) "pivot" =
      some (.i32 pivot) := by
    rw [envExtend_miss _ _ _ _
      (show ("pivot" : String) ≠ "wNo" by decide),
      envExtend_miss _ _ _ _
      (show ("pivot" : String) ≠ "wYes" by decide),
      envExtend_miss _ _ _ _
      (show ("pivot" : String) ≠ "r" by decide)]
    simp [envLookup, show ("pivot" : String) ≠ "a" by decide]
  have hrN : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)]
      "r" (.u64 (BitVec.ofNat 64 0)))
      "wYes" (.u64 (BitVec.ofNat 64 0)))
      "wNo" (.u64 (BitVec.ofNat 64 0))) "r" =
      some (.u64 (BitVec.ofNat 64 0)) := by
    rw [envExtend_miss _ _ _ _
      (show ("r" : String) ≠ "wNo" by decide),
      envExtend_miss _ _ _ _
      (show ("r" : String) ≠ "wYes" by decide)]
    exact envExtend_hit _ _ _
  have hwYesN : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)]
      "r" (.u64 (BitVec.ofNat 64 0)))
      "wYes" (.u64 (BitVec.ofNat 64 0)))
      "wNo" (.u64 (BitVec.ofNat 64 0))) "wYes" =
      some (.u64 (BitVec.ofNat 64 0)) := by
    rw [envExtend_miss _ _ _ _
      (show ("wYes" : String) ≠ "wNo" by decide)]
    exact envExtend_hit _ _ _
  have hwNoN : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)]
      "r" (.u64 (BitVec.ofNat 64 0)))
      "wYes" (.u64 (BitVec.ofNat 64 0)))
      "wNo" (.u64 (BitVec.ofNat 64 0))) "wNo" =
      some (.u64 (BitVec.ofNat 64 0)) :=
    envExtend_hit _ _ _
  obtain ⟨ρ', m', hloop, -, -, -, -,
      ⟨rB', -, -⟩, ⟨wYesB', hwYesB', hwYesN'⟩,
      ⟨wNoB', -, -⟩, -, -, -⟩ :=
    memPartitionCopyLoop_ok vecPartitionCopyProg F 0
      (envExtend (envExtend (envExtend
        [("a", .stdVecVal ([] : List (BitVec 32))),
          ("yes", .stdVecVal yes), ("no", .stdVecVal no),
          ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0)))
      (⟨3, [(2, ⟨2, true,
        (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
          ([] : List (BitVec 32))⟩),
        (1, ⟨1, true,
        (BitVec.ofNat 32 yes.length) :: yes⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 no.length) :: no⟩)], []⟩ : Mem)
      [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)]
      ([] : List (BitVec 32)) yes no pivot 0 0 0
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 0)
      yes no 0 0 0
      2 1 0 2 1 0
      (BitVec.ofNat 32 ([] : List (BitVec 32)).length)
      (BitVec.ofNat 32 yes.length)
      (BitVec.ofNat 32 no.length)
      (by simp [layoutLookup]) (by simp [layoutLookup])
      (by simp [layoutLookup])
      (memFind_cons_hit _ _ _ _ _)
      (by
        have hne : (1 : Nat) ≠ 2 := by decide
        rw [memFind_cons_miss _ _ _ _ _ _ hne]
        exact memFind_cons_hit _ _ _ _ _)
      (by
        have hne2 : (0 : Nat) ≠ 2 := by decide
        have hne1 : (0 : Nat) ≠ 1 := by decide
        rw [memFind_cons_miss _ _ _ _ _ _ hne2,
          memFind_cons_miss _ _ _ _ _ _ hne1]
        exact memFind_cons_hit _ _ _ _ _)
      rfl rfl rfl
      (by decide) (by decide) (by decide)
      hw0N hw0N hw0N (by simp) hyes64 hno64
      haN hyesN hnoN hpivN hrN hwYesN hwNoN
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
      (fun p hp => absurd hp (Nat.not_lt_zero p))
      (by simp) (by simp) (by simp) (by simp) rfl
  have hwEq : wYesB' = BitVec.ofNat 64 0 :=
    BitVec.eq_of_toNat_eq (by rw [hwYesN']; simp)
  have hevW' : memEvalExpr (.var "wYes") ρ' m'
      [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    rw [← hwEq]
    exact (memEvalExpr_var _ _ _ _).trans
      (evalExpr_var_hit _ _ _ hwYesB')
  have hretM := memEvalProgStmt_return vecPartitionCopyProg F
    (.var "wYes") ρ' m' [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)]
    (.u64 (BitVec.ofNat 64 0)) hevW'
  simp only [memEvalProgFunc, hbind, hbody]
  rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletR,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletW,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletN,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hloop,
    hretM]

/-- Memory entry, ok leg: a nonempty input with fitting
    records binds the prelude, runs the loop on memory, and
    returns the keeper count. -/
theorem memEvalProgFunc_vecPartitionCopy_ok (F : Nat)
    (la yes no : List (BitVec 32)) (pivot : BitVec 32)
    (wYes' wNo' : Nat) (yes' no' : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hyes64 : yes.length < 2 ^ 64)
    (hno64 : no.length < 2 ^ 64)
    (hF : la.length ≤ F)
    (hle : 1 ≤ la.length)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hcapYes : (la.filter (fun y => y.slt pivot)).length
      ≤ yes.length)
    (hcapNo : (la.filter (fun y => !(y.slt pivot))).length
      ≤ no.length)
    (hfwd : partitionCopyFwd pivot la yes no la.length 0 0 0 =
      .ok (la.length, wYes', wNo', yes', no'))
    (hwlen : wYes' = (la.filter (fun y => y.slt pivot)).length) :
    memEvalProgFunc vecPartitionCopyProg F vecPartitionCopyFunc
      [.stdVecVal la, .stdVecVal yes, .stdVecVal no,
        .i32 pivot] =
      .ok (.u64 (BitVec.ofNat 64 wYes')) := by
  have hbind := bindMemArgs_vecPartitionCopy la yes no pivot
  have hbody : vecPartitionCopyFunc.body =
      (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq (.let_ "wYes" (.u 64)
          (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq (.let_ "wNo" (.u 64)
            (.lit (.u64 (BitVec.ofNat 64 0))))
            (.seq vecPartitionCopyLoop
              (.return_ (.var "wYes")))))) := rfl
  cases hla : la with
  | nil =>
    subst hla
    simp at hle
  | cons b0 ys =>
    subst hla
    have hlitR : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        (⟨3, [(2, ⟨2, true,
          (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
          (1, ⟨1, true,
          (BitVec.ofNat 32 yes.length) :: yes⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 no.length) :: no⟩)], []⟩ : Mem)
        [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)] =
        evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
          [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
            ("no", .stdVecVal no), ("pivot", .i32 pivot)] :=
      memEvalExpr_lit _ _ _ _
    have hlitRV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)] =
        .ok (.u64 (BitVec.ofNat 64 0)) := by
      simp [evalExpr, litVal]
    have hletR := memRevLet vecPartitionCopyProg F "r" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
        ("no", .stdVecVal no), ("pivot", .i32 pivot)]
      (⟨3, [(2, ⟨2, true,
        (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
        (1, ⟨1, true,
        (BitVec.ofNat 32 yes.length) :: yes⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 no.length) :: no⟩)], []⟩ : Mem)
      [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)]
      (.u64 (BitVec.ofNat 64 0))
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) (by intro h; cases h) hlitR hlitRV
    have hlitW : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend [("a", .stdVecVal (b0 :: ys)),
          ("yes", .stdVecVal yes), ("no", .stdVecVal no),
          ("pivot", .i32 pivot)]
          "r" (.u64 (BitVec.ofNat 64 0)))
        (⟨3, [(2, ⟨2, true,
          (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
          (1, ⟨1, true,
          (BitVec.ofNat 32 yes.length) :: yes⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 no.length) :: no⟩)], []⟩ : Mem)
        [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)] =
        evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
          (envExtend [("a", .stdVecVal (b0 :: ys)),
            ("yes", .stdVecVal yes), ("no", .stdVecVal no),
            ("pivot", .i32 pivot)]
            "r" (.u64 (BitVec.ofNat 64 0))) :=
      memEvalExpr_lit _ _ _ _
    have hlitWV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend [("a", .stdVecVal (b0 :: ys)),
          ("yes", .stdVecVal yes), ("no", .stdVecVal no),
          ("pivot", .i32 pivot)]
          "r" (.u64 (BitVec.ofNat 64 0))) =
        .ok (.u64 (BitVec.ofNat 64 0)) := by
      simp [evalExpr, litVal]
    have hletW := memRevLet vecPartitionCopyProg F "wYes" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("a", .stdVecVal (b0 :: ys)),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
      (⟨3, [(2, ⟨2, true,
        (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
        (1, ⟨1, true,
        (BitVec.ofNat 32 yes.length) :: yes⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 no.length) :: no⟩)], []⟩ : Mem)
      [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)]
      (.u64 (BitVec.ofNat 64 0))
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) (by intro h; cases h) hlitW hlitWV
    have hlitN : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend (envExtend
          [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
            ("no", .stdVecVal no), ("pivot", .i32 pivot)]
          "r" (.u64 (BitVec.ofNat 64 0)))
          "wYes" (.u64 (BitVec.ofNat 64 0)))
        (⟨3, [(2, ⟨2, true,
          (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
          (1, ⟨1, true,
          (BitVec.ofNat 32 yes.length) :: yes⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 no.length) :: no⟩)], []⟩ : Mem)
        [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)] =
        evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
          (envExtend (envExtend
            [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
              ("no", .stdVecVal no), ("pivot", .i32 pivot)]
            "r" (.u64 (BitVec.ofNat 64 0)))
            "wYes" (.u64 (BitVec.ofNat 64 0))) :=
      memEvalExpr_lit _ _ _ _
    have hlitNV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend (envExtend
          [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
            ("no", .stdVecVal no), ("pivot", .i32 pivot)]
          "r" (.u64 (BitVec.ofNat 64 0)))
          "wYes" (.u64 (BitVec.ofNat 64 0))) =
        .ok (.u64 (BitVec.ofNat 64 0)) := by
      simp [evalExpr, litVal]
    have hletN := memRevLet vecPartitionCopyProg F "wNo" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
      (⟨3, [(2, ⟨2, true,
        (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
        (1, ⟨1, true,
        (BitVec.ofNat 32 yes.length) :: yes⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 no.length) :: no⟩)], []⟩ : Mem)
      [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)]
      (.u64 (BitVec.ofNat 64 0))
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) (by intro h; cases h) hlitN hlitNV
    have hw0N : (BitVec.ofNat 64 0).toNat = 0 := by decide
    have haA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "a" =
        some (.stdVecVal (b0 :: ys)) := by
      rw [envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "wNo" by decide),
        envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "wYes" by decide),
        envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "r" by decide)]
      simp [envLookup]
    have hyesA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "yes" =
        some (.stdVecVal yes) := by
      rw [envExtend_miss _ _ _ _
        (show ("yes" : String) ≠ "wNo" by decide),
        envExtend_miss _ _ _ _
        (show ("yes" : String) ≠ "wYes" by decide),
        envExtend_miss _ _ _ _
        (show ("yes" : String) ≠ "r" by decide)]
      simp [envLookup, show ("yes" : String) ≠ "a" by decide]
    have hnoA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "no" =
        some (.stdVecVal no) := by
      rw [envExtend_miss _ _ _ _
        (show ("no" : String) ≠ "wNo" by decide),
        envExtend_miss _ _ _ _
        (show ("no" : String) ≠ "wYes" by decide),
        envExtend_miss _ _ _ _
        (show ("no" : String) ≠ "r" by decide)]
      simp [envLookup, show ("no" : String) ≠ "a" by decide]
    have hpivA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "pivot" =
        some (.i32 pivot) := by
      rw [envExtend_miss _ _ _ _
        (show ("pivot" : String) ≠ "wNo" by decide),
        envExtend_miss _ _ _ _
        (show ("pivot" : String) ≠ "wYes" by decide),
        envExtend_miss _ _ _ _
        (show ("pivot" : String) ≠ "r" by decide)]
      simp [envLookup, show ("pivot" : String) ≠ "a" by decide]
    have hrA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "r" =
        some (.u64 (BitVec.ofNat 64 0)) := by
      rw [envExtend_miss _ _ _ _
        (show ("r" : String) ≠ "wNo" by decide),
        envExtend_miss _ _ _ _
        (show ("r" : String) ≠ "wYes" by decide)]
      exact envExtend_hit _ _ _
    have hwYesA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "wYes" =
        some (.u64 (BitVec.ofNat 64 0)) := by
      rw [envExtend_miss _ _ _ _
        (show ("wYes" : String) ≠ "wNo" by decide)]
      exact envExtend_hit _ _ _
    have hwNoA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "wNo" =
        some (.u64 (BitVec.ofNat 64 0)) :=
      envExtend_hit _ _ _
    obtain ⟨ρ', m', hloop, -, -, -, -,
        ⟨rB', -, -⟩, ⟨wYesB', hwYesB', hwYesN'⟩,
        ⟨wNoB', -, -⟩, -, -, -⟩ :=
      memPartitionCopyLoop_ok vecPartitionCopyProg F
        ((b0 :: ys).length)
        (envExtend (envExtend (envExtend
          [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
            ("no", .stdVecVal no), ("pivot", .i32 pivot)]
          "r" (.u64 (BitVec.ofNat 64 0)))
          "wYes" (.u64 (BitVec.ofNat 64 0)))
          "wNo" (.u64 (BitVec.ofNat 64 0)))
        (⟨3, [(2, ⟨2, true,
          (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
          (1, ⟨1, true,
          (BitVec.ofNat 32 yes.length) :: yes⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 no.length) :: no⟩)], []⟩ : Mem)
        [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)]
        (b0 :: ys) yes no pivot 0 0 0
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
        (BitVec.ofNat 64 0)
        yes' no' ((b0 :: ys).length) wYes' wNo'
        2 1 0 2 1 0
        (BitVec.ofNat 32 (b0 :: ys).length)
        (BitVec.ofNat 32 yes.length)
        (BitVec.ofNat 32 no.length)
        (by simp [layoutLookup]) (by simp [layoutLookup])
        (by simp [layoutLookup])
        (memFind_cons_hit _ _ _ _ _)
        (by
          have hne : (1 : Nat) ≠ 2 := by decide
          rw [memFind_cons_miss _ _ _ _ _ _ hne]
          exact memFind_cons_hit _ _ _ _ _)
        (by
          have hne2 : (0 : Nat) ≠ 2 := by decide
          have hne1 : (0 : Nat) ≠ 1 := by decide
          rw [memFind_cons_miss _ _ _ _ _ _ hne2,
            memFind_cons_miss _ _ _ _ _ _ hne1]
          exact memFind_cons_hit _ _ _ _ _)
        rfl rfl rfl
        (by decide) (by decide) (by decide)
        hw0N hw0N hw0N hla64 hyes64 hno64
        haA hyesA hnoA hpivA hrA hwYesA hwNoA
        (by omega) hF (Nat.le_refl _)
        hread (by simp) (by simp) hcapYes hcapNo hfwd
    have hwEq : wYesB' = BitVec.ofNat 64 wYes' := by
      apply BitVec.eq_of_toNat_eq
      rw [hwYesN', BitVec.toNat_ofNat]
      have hlen : wYes' < 2 ^ 64 := by omega
      exact (Nat.mod_eq_of_lt hlen).symm
    have hevW' : memEvalExpr (.var "wYes") ρ' m'
        [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)] =
        .ok (.u64 (BitVec.ofNat 64 wYes')) := by
      rw [← hwEq]
      exact (memEvalExpr_var _ _ _ _).trans
        (evalExpr_var_hit _ _ _ hwYesB')
    have hretM := memEvalProgStmt_return vecPartitionCopyProg F
      (.var "wYes") ρ' m' [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)]
      (.u64 (BitVec.ofNat 64 wYes')) hevW'
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletR,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletW,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletN,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hloop,
      hretM]

/-- Memory entry, err leg: a nonempty input with a short
    record on either side binds the prelude, then the loop
    fails loud (the `return` is unreachable). -/
theorem memEvalProgFunc_vecPartitionCopy_err (F : Nat)
    (la yes no : List (BitVec 32)) (pivot : BitVec 32)
    (hla64 : la.length < 2 ^ 64) (hyes64 : yes.length < 2 ^ 64)
    (hno64 : no.length < 2 ^ 64)
    (hF : la.length ≤ F)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hmore : yes.length < (la.filter (fun y => y.slt pivot)).length ∨
      no.length < (la.filter (fun y => !(y.slt pivot))).length)
    (hfwd : partitionCopyFwd pivot la yes no la.length 0 0 0 =
      .error .AssertFail) :
    memEvalProgFunc vecPartitionCopyProg F vecPartitionCopyFunc
      [.stdVecVal la, .stdVecVal yes, .stdVecVal no,
        .i32 pivot] =
      .error .AssertFail := by
  have hbind := bindMemArgs_vecPartitionCopy la yes no pivot
  have hbody : vecPartitionCopyFunc.body =
      (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq (.let_ "wYes" (.u 64)
          (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq (.let_ "wNo" (.u 64)
            (.lit (.u64 (BitVec.ofNat 64 0))))
            (.seq vecPartitionCopyLoop
              (.return_ (.var "wYes")))))) := rfl
  cases hla : la with
  | nil =>
    subst hla
    simp at hmore
  | cons b0 ys =>
    subst hla
    have hlitR : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        (⟨3, [(2, ⟨2, true,
          (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
          (1, ⟨1, true,
          (BitVec.ofNat 32 yes.length) :: yes⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 no.length) :: no⟩)], []⟩ : Mem)
        [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)] =
        evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
          [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
            ("no", .stdVecVal no), ("pivot", .i32 pivot)] :=
      memEvalExpr_lit _ _ _ _
    have hlitRV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)] =
        .ok (.u64 (BitVec.ofNat 64 0)) := by
      simp [evalExpr, litVal]
    have hletR := memRevLet vecPartitionCopyProg F "r" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
        ("no", .stdVecVal no), ("pivot", .i32 pivot)]
      (⟨3, [(2, ⟨2, true,
        (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
        (1, ⟨1, true,
        (BitVec.ofNat 32 yes.length) :: yes⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 no.length) :: no⟩)], []⟩ : Mem)
      [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)]
      (.u64 (BitVec.ofNat 64 0))
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) (by intro h; cases h) hlitR hlitRV
    have hlitW : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend [("a", .stdVecVal (b0 :: ys)),
          ("yes", .stdVecVal yes), ("no", .stdVecVal no),
          ("pivot", .i32 pivot)]
          "r" (.u64 (BitVec.ofNat 64 0)))
        (⟨3, [(2, ⟨2, true,
          (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
          (1, ⟨1, true,
          (BitVec.ofNat 32 yes.length) :: yes⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 no.length) :: no⟩)], []⟩ : Mem)
        [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)] =
        evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
          (envExtend [("a", .stdVecVal (b0 :: ys)),
            ("yes", .stdVecVal yes), ("no", .stdVecVal no),
            ("pivot", .i32 pivot)]
            "r" (.u64 (BitVec.ofNat 64 0))) :=
      memEvalExpr_lit _ _ _ _
    have hlitWV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend [("a", .stdVecVal (b0 :: ys)),
          ("yes", .stdVecVal yes), ("no", .stdVecVal no),
          ("pivot", .i32 pivot)]
          "r" (.u64 (BitVec.ofNat 64 0))) =
        .ok (.u64 (BitVec.ofNat 64 0)) := by
      simp [evalExpr, litVal]
    have hletW := memRevLet vecPartitionCopyProg F "wYes" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("a", .stdVecVal (b0 :: ys)),
        ("yes", .stdVecVal yes), ("no", .stdVecVal no),
        ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
      (⟨3, [(2, ⟨2, true,
        (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
        (1, ⟨1, true,
        (BitVec.ofNat 32 yes.length) :: yes⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 no.length) :: no⟩)], []⟩ : Mem)
      [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)]
      (.u64 (BitVec.ofNat 64 0))
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) (by intro h; cases h) hlitW hlitWV
    have hlitN : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend (envExtend
          [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
            ("no", .stdVecVal no), ("pivot", .i32 pivot)]
          "r" (.u64 (BitVec.ofNat 64 0)))
          "wYes" (.u64 (BitVec.ofNat 64 0)))
        (⟨3, [(2, ⟨2, true,
          (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
          (1, ⟨1, true,
          (BitVec.ofNat 32 yes.length) :: yes⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 no.length) :: no⟩)], []⟩ : Mem)
        [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)] =
        evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
          (envExtend (envExtend
            [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
              ("no", .stdVecVal no), ("pivot", .i32 pivot)]
            "r" (.u64 (BitVec.ofNat 64 0)))
            "wYes" (.u64 (BitVec.ofNat 64 0))) :=
      memEvalExpr_lit _ _ _ _
    have hlitNV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend (envExtend
          [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
            ("no", .stdVecVal no), ("pivot", .i32 pivot)]
          "r" (.u64 (BitVec.ofNat 64 0)))
          "wYes" (.u64 (BitVec.ofNat 64 0))) =
        .ok (.u64 (BitVec.ofNat 64 0)) := by
      simp [evalExpr, litVal]
    have hletN := memRevLet vecPartitionCopyProg F "wNo" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
      (⟨3, [(2, ⟨2, true,
        (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
        (1, ⟨1, true,
        (BitVec.ofNat 32 yes.length) :: yes⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 no.length) :: no⟩)], []⟩ : Mem)
      [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)]
      (.u64 (BitVec.ofNat 64 0))
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) (by intro h; cases h) hlitN hlitNV
    have hw0N : (BitVec.ofNat 64 0).toNat = 0 := by decide
    have heA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "a" =
        some (.stdVecVal (b0 :: ys)) := by
      rw [envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "wNo" by decide),
        envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "wYes" by decide),
        envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "r" by decide)]
      simp [envLookup]
    have heYesA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "yes" =
        some (.stdVecVal yes) := by
      rw [envExtend_miss _ _ _ _
        (show ("yes" : String) ≠ "wNo" by decide),
        envExtend_miss _ _ _ _
        (show ("yes" : String) ≠ "wYes" by decide),
        envExtend_miss _ _ _ _
        (show ("yes" : String) ≠ "r" by decide)]
      simp [envLookup, show ("yes" : String) ≠ "a" by decide]
    have heNoA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "no" =
        some (.stdVecVal no) := by
      rw [envExtend_miss _ _ _ _
        (show ("no" : String) ≠ "wNo" by decide),
        envExtend_miss _ _ _ _
        (show ("no" : String) ≠ "wYes" by decide),
        envExtend_miss _ _ _ _
        (show ("no" : String) ≠ "r" by decide)]
      simp [envLookup, show ("no" : String) ≠ "a" by decide]
    have hepivA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "pivot" =
        some (.i32 pivot) := by
      rw [envExtend_miss _ _ _ _
        (show ("pivot" : String) ≠ "wNo" by decide),
        envExtend_miss _ _ _ _
        (show ("pivot" : String) ≠ "wYes" by decide),
        envExtend_miss _ _ _ _
        (show ("pivot" : String) ≠ "r" by decide)]
      simp [envLookup, show ("pivot" : String) ≠ "a" by decide]
    have herA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "r" =
        some (.u64 (BitVec.ofNat 64 0)) := by
      rw [envExtend_miss _ _ _ _
        (show ("r" : String) ≠ "wNo" by decide),
        envExtend_miss _ _ _ _
        (show ("r" : String) ≠ "wYes" by decide)]
      exact envExtend_hit _ _ _
    have hewYesA : envLookup (envExtend (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
          ("no", .stdVecVal no), ("pivot", .i32 pivot)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "wYes" (.u64 (BitVec.ofNat 64 0)))
        "wNo" (.u64 (BitVec.ofNat 64 0))) "wYes" =
        some (.u64 (BitVec.ofNat 64 0)) := by
      rw [envExtend_miss _ _ _ _
        (show ("wYes" : String) ≠ "wNo" by decide)]
      exact envExtend_hit _ _ _
    have hloop : memEvalProgStmt vecPartitionCopyProg F
        vecPartitionCopyLoop
        (envExtend (envExtend (envExtend
          [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
            ("no", .stdVecVal no), ("pivot", .i32 pivot)]
          "r" (.u64 (BitVec.ofNat 64 0)))
          "wYes" (.u64 (BitVec.ofNat 64 0)))
          "wNo" (.u64 (BitVec.ofNat 64 0)))
        (⟨3, [(2, ⟨2, true,
          (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
          (1, ⟨1, true,
          (BitVec.ofNat 32 yes.length) :: yes⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 no.length) :: no⟩)], []⟩ : Mem)
        [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)] =
        .error .AssertFail :=
      memPartitionCopyLoop_err vecPartitionCopyProg F
        ((b0 :: ys).length)
        (envExtend (envExtend (envExtend
          [("a", .stdVecVal (b0 :: ys)), ("yes", .stdVecVal yes),
            ("no", .stdVecVal no), ("pivot", .i32 pivot)]
          "r" (.u64 (BitVec.ofNat 64 0)))
          "wYes" (.u64 (BitVec.ofNat 64 0)))
          "wNo" (.u64 (BitVec.ofNat 64 0)))
        (⟨3, [(2, ⟨2, true,
          (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
          (1, ⟨1, true,
          (BitVec.ofNat 32 yes.length) :: yes⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 no.length) :: no⟩)], []⟩ : Mem)
        [("a", 2, 2), ("yes", 1, 1), ("no", 0, 0)]
        (b0 :: ys) yes no pivot 0 0 0
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
        (BitVec.ofNat 64 0)
        2 1 0 2 1 0
        (BitVec.ofNat 32 (b0 :: ys).length)
        (BitVec.ofNat 32 yes.length)
        (BitVec.ofNat 32 no.length)
        (by simp [layoutLookup]) (by simp [layoutLookup])
        (by simp [layoutLookup])
        (memFind_cons_hit _ _ _ _ _)
        (by
          have hne : (1 : Nat) ≠ 2 := by decide
          rw [memFind_cons_miss _ _ _ _ _ _ hne]
          exact memFind_cons_hit _ _ _ _ _)
        (by
          have hne2 : (0 : Nat) ≠ 2 := by decide
          have hne1 : (0 : Nat) ≠ 1 := by decide
          rw [memFind_cons_miss _ _ _ _ _ _ hne2,
            memFind_cons_miss _ _ _ _ _ _ hne1]
          exact memFind_cons_hit _ _ _ _ _)
        rfl rfl rfl
        (by decide) (by decide) (by decide)
        hw0N hw0N hw0N hla64 hyes64 hno64
        heA heYesA heNoA hepivA herA hewYesA
        (envExtend_hit _ _ _)
        (by omega) hF (Nat.le_refl _)
        hread (by simp) (by simp) hfwd
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletR,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletW,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletN,
      memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hloop]

/-! ## Transfer + closing contract -/

/-- Transfer for `vec_partition_copy`, ok leg: both layers agree
    on the keeper count. -/
theorem memTransferProg_vecPartitionCopy_ok (F : Nat)
    (la yes no : List (BitVec 32)) (pivot : BitVec 32)
    (wYes' wNo' : Nat) (yes' no' : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hyes64 : yes.length < 2 ^ 64)
    (hno64 : no.length < 2 ^ 64)
    (hF : la.length ≤ F)
    (hle : 1 ≤ la.length)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hcapYes : (la.filter (fun y => y.slt pivot)).length
      ≤ yes.length)
    (hcapNo : (la.filter (fun y => !(y.slt pivot))).length
      ≤ no.length)
    (hfwd : partitionCopyFwd pivot la yes no la.length 0 0 0 =
      .ok (la.length, wYes', wNo', yes', no'))
    (hwlen : wYes' = (la.filter (fun y => y.slt pivot)).length)
    (_h : oracleNoalias vecPartitionCopyFunc
      [.stdVecVal la, .stdVecVal yes, .stdVecVal no,
        .i32 pivot]) :
    memEvalProgFunc vecPartitionCopyProg F vecPartitionCopyFunc
      [.stdVecVal la, .stdVecVal yes, .stdVecVal no,
        .i32 pivot] =
      evalProgFunc vecPartitionCopyProg F vecPartitionCopyFunc
        [.stdVecVal la, .stdVecVal yes, .stdVecVal no,
          .i32 pivot] := by
  rw [memEvalProgFunc_vecPartitionCopy_ok F la yes no pivot
    wYes' wNo' yes' no' hla64 hyes64 hno64 hF hle hread hcapYes
    hcapNo hfwd hwlen,
    evalProgFunc_vecPartitionCopy_ok F la yes no pivot
    wYes' wNo' yes' no' hla64 hyes64 hno64 hF hle hread hcapYes
    hcapNo hfwd hwlen]

/-- Transfer for `vec_partition_copy`, err leg: both sides fail
    loud on a short record. -/
theorem memTransferProg_vecPartitionCopy_err (F : Nat)
    (la yes no : List (BitVec 32)) (pivot : BitVec 32)
    (hla64 : la.length < 2 ^ 64) (hyes64 : yes.length < 2 ^ 64)
    (hno64 : no.length < 2 ^ 64)
    (hF : la.length ≤ F)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hmore : yes.length < (la.filter (fun y => y.slt pivot)).length ∨
      no.length < (la.filter (fun y => !(y.slt pivot))).length)
    (hfwd : partitionCopyFwd pivot la yes no la.length 0 0 0 =
      .error .AssertFail)
    (_h : oracleNoalias vecPartitionCopyFunc
      [.stdVecVal la, .stdVecVal yes, .stdVecVal no,
        .i32 pivot]) :
    memEvalProgFunc vecPartitionCopyProg F vecPartitionCopyFunc
      [.stdVecVal la, .stdVecVal yes, .stdVecVal no,
        .i32 pivot] =
      evalProgFunc vecPartitionCopyProg F vecPartitionCopyFunc
        [.stdVecVal la, .stdVecVal yes, .stdVecVal no,
          .i32 pivot] := by
  rw [memEvalProgFunc_vecPartitionCopy_err F la yes no pivot
    hla64 hyes64 hno64 hF hread hmore hfwd,
    evalProgFunc_vecPartitionCopy_err F la yes no pivot
    hla64 hyes64 hno64 hF hread hmore hfwd]

/-- Closing dual-record partition contract, ok leg: when both
    records fit, the forward returns the keeper count over the
    keeper prefix and the dropper prefix, both record lengths
    unchanged. -/
theorem evalProgFunc_vecPartitionCopy_spec_ok (F : Nat)
    (la yes no : List (BitVec 32)) (pivot : BitVec 32)
    (hla64 : la.length < 2 ^ 64) (hyes64 : yes.length < 2 ^ 64)
    (hno64 : no.length < 2 ^ 64)
    (hF : la.length ≤ F)
    (hcapYes : (la.filter (fun y => y.slt pivot)).length
      ≤ yes.length)
    (hcapNo : (la.filter (fun y => !(y.slt pivot))).length
      ≤ no.length) :
    ∃ (wYes' : Nat) (wNo' : Nat) (yes' no' : List (BitVec 32)),
      memEvalProgFunc vecPartitionCopyProg F vecPartitionCopyFunc
        [.stdVecVal la, .stdVecVal yes, .stdVecVal no,
          .i32 pivot] =
        .ok (.u64 (BitVec.ofNat 64 wYes')) ∧
      yes'.take wYes' = la.filter (fun y => y.slt pivot) ∧
      no'.take wNo' = la.filter (fun y => !(y.slt pivot)) ∧
      wYes' = (la.filter (fun y => y.slt pivot)).length ∧
      wNo' = (la.filter (fun y => !(y.slt pivot))).length ∧
      yes'.length = yes.length ∧ no'.length = no.length := by
  have hread : ∀ p, p < la.length → ∃ y, la[p]? = some y :=
    fun p hp => ⟨_, List.getElem?_eq_getElem hp⟩
  cases hla : la with
  | nil =>
    subst hla
    refine ⟨0, 0, yes, no,
      memEvalProgFunc_vecPartitionCopy_nil F yes no pivot
        hyes64 hno64, ?_, ?_, rfl, rfl, rfl, rfl⟩
    · simp
    · simp
  | cons b0 ys =>
    subst hla
    obtain ⟨wYes', wNo', yes', no', hfwd, hcntYes, hcntNo⟩ :=
      partitionCopyFwd_ok pivot (b0 :: ys) yes no
        ((b0 :: ys).length) 0 0 0 (Nat.zero_le _) (Nat.le_refl _)
        hread (by simp) (by simp) hcapYes hcapNo
    obtain ⟨hprefYes, hprefNo, -, -, hlenYes, hlenNo⟩ :=
      partitionCopyFwd_prefix pivot (b0 :: ys) yes no
        ((b0 :: ys).length) 0 0 0 wYes' wNo' yes no yes' no'
        (Nat.zero_le _) (Nat.le_refl _) rfl rfl hread (by simp)
        (by simp) hcapYes hcapNo (by simp) (by simp)
        (fun j _ => rfl) (fun j _ => rfl) hfwd
    have hwEq : wYes' =
        ((b0 :: ys).filter (fun y => y.slt pivot)).length := by
      rw [List.take_length] at hcntYes
      exact hcntYes.symm
    have hwEqNo : wNo' =
        ((b0 :: ys).filter
          (fun y => !(y.slt pivot))).length := by
      rw [List.take_length] at hcntNo
      exact hcntNo.symm
    have heval := evalProgFunc_vecPartitionCopy_ok F (b0 :: ys)
      yes no pivot wYes' wNo' yes' no' hla64 hyes64 hno64 hF
      (by simp) hread hcapYes hcapNo hfwd hwEq
    have htrans := memTransferProg_vecPartitionCopy_ok F (b0 :: ys)
      yes no pivot wYes' wNo' yes' no' hla64 hyes64 hno64 hF
      (by simp) hread hcapYes hcapNo hfwd hwEq
      (oracleNoalias_vecPartitionCopy _ _ _ _)
    rw [htrans]
    exact ⟨wYes', wNo', yes', no', heval, hprefYes, hprefNo, hwEq,
      hwEqNo, hlenYes, hlenNo⟩

/-- Closing dual-record partition contract, err leg: a short
    record on either side fails loud on both layers. -/
theorem evalProgFunc_vecPartitionCopy_spec_err (F : Nat)
    (la yes no : List (BitVec 32)) (pivot : BitVec 32)
    (hla64 : la.length < 2 ^ 64) (hyes64 : yes.length < 2 ^ 64)
    (hno64 : no.length < 2 ^ 64)
    (hF : la.length ≤ F)
    (hmore : yes.length < (la.filter (fun y => y.slt pivot)).length ∨
      no.length < (la.filter (fun y => !(y.slt pivot))).length) :
    memEvalProgFunc vecPartitionCopyProg F vecPartitionCopyFunc
      [.stdVecVal la, .stdVecVal yes, .stdVecVal no,
        .i32 pivot] =
      .error .AssertFail := by
  have hread : ∀ p, p < la.length → ∃ y, la[p]? = some y :=
    fun p hp => ⟨_, List.getElem?_eq_getElem hp⟩
  cases hla : la with
  | nil =>
    subst hla
    simp at hmore
  | cons b0 ys =>
    subst hla
    have hfwd := hmore.elim
      (partitionCopyFwd_err_of_yes_short pivot (b0 :: ys) yes no
        hread)
      (partitionCopyFwd_err_of_no_short pivot (b0 :: ys) yes no
        hread)
    have herrM := memEvalProgFunc_vecPartitionCopy_err F (b0 :: ys)
      yes no pivot hla64 hyes64 hno64 hF hread hmore hfwd
    exact herrM
