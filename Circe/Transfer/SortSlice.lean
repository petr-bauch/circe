/-
Circe.Transfer.SortSlice — N9 insertion-sort transfer (mutating slice).

Over `Circe.Emit.ArraySort` (the value-side forward-as-fold proof):
each step is replayed with the memory side threaded alongside —
reads cross-checked via `memLoad`, writes lockstepped via
`arrSet_lockstep`, loops re-inducted with the block tracking the
current value list — and the func-level transfer closes both sides
at `insertionSortFwd` under the `oracleNoalias` footprint.
-/
import Circe.Mem
import Circe.Derived
import Circe.Emit.ArraySort

/-! ## Memory condition evaluations (reuse the value cond lemmas) -/

/-- The inner condition at `j = 0` on the memory side: the guard
    evaluates purely, so agreement plus the value lemma suffices. -/
theorem memSortInnerCond_eval_zero (ρ : Env) (m : Mem) (π : Layout)
    (l : List (BitVec 32))
    (hj : envLookup ρ "j" = some (.u64 (BitVec.ofNat 64 0)))
    (hlay : layoutLookup π "a" = some (0, 0))
    (hmem : memFind m 0 = some ⟨0, true, l⟩) :
    memEvalExpr sortInnerCond ρ m π = .ok (.b false) := by
  have hc : memEvalExpr
      (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j")) ρ m π =
      evalExpr (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j")) ρ :=
    memEvalExpr_ult_agree _ _ _ _ _
      (memEvalExpr_lit _ _ _ _) (memEvalExpr_var _ _ _ _)
  have hvc : evalExpr
      (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j")) ρ =
      .ok (.b false) := by
    have h := evalExpr_ult_u64lit (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
      (.var "j") ρ (evalExpr_var_hit _ _ _ hj)
    have hf : (BitVec.ofNat 64 0).ult (BitVec.ofNat 64 0) = false := by
      rw [ofNat64_ult 0 _ (by decide : 0 < 2 ^ 64),
        ofNat64_toNat 0 (by decide : 0 < 2 ^ 64)]
      decide
    rw [hf] at h
    exact h
  have he := memEvalExpr_lit (.b false) ρ m π
  have mtif : memEvalExpr sortInnerCond ρ m π =
      evalExpr sortInnerCond ρ := by
    simp only [sortInnerCond]
    exact memEvalExpr_tif_false _ _ _ _ _ _ hc hvc he
  rw [mtif]
  exact sortInnerCond_eval_zero ρ l 0 hj rfl

/-- The inner condition at `j ≥ 1` on the memory side: both reads
    hit the pinned block, so the comparison agrees and the value
    lemma finishes. -/
theorem memSortInnerCond_eval_succ (ρ : Env) (m : Mem) (π : Layout)
    (l : List (BitVec 32)) (j : Nat)
    (ha : envLookup ρ "a" = some (.arr32 l))
    (hj : envLookup ρ "j" = some (.u64 (BitVec.ofNat 64 j)))
    (hlen : l.length = 4) (hj3 : j ≤ 3) (hj1 : 1 ≤ j)
    (hlay : layoutLookup π "a" = some (0, 0))
    (hmem : memFind m 0 = some ⟨0, true, l⟩) :
    memEvalExpr sortInnerCond ρ m π =
      .ok (.b (l[j].ult l[j - 1])) := by
  have hj64 : j < 2 ^ 64 := by omega
  have htoNat_j : (BitVec.ofNat 64 j).toNat = j := ofNat64_toNat j hj64
  have hsub_toNat := ofNat64_sub_one_toNat j hj1 hj64
  have hj_get : l[j]? = some l[j] := List.getElem?_eq_getElem (by omega)
  have hjm_get : l[j - 1]? = some l[j - 1] :=
    List.getElem?_eq_getElem (by omega)
  have hget_j : l[(BitVec.ofNat 64 j).toNat]? = some l[j] := by
    rw [htoNat_j]
    exact hj_get
  have hget_jm : l[(BitVec.ofNat 64 j - BitVec.ofNat 64 1).toNat]? =
      some l[j - 1] := by
    rw [hsub_toNat]
    exact hjm_get
  have hload_j : memLoad m 0 0 (BitVec.ofNat 64 j).toNat = .ok l[j] :=
    memLoad_hit m 0 0 _ _ _ hmem rfl rfl hget_j
  have hload_jm : memLoad m 0 0
      (BitVec.ofNat 64 j - BitVec.ofNat 64 1).toNat = .ok l[j - 1] :=
    memLoad_hit m 0 0 _ _ _ hmem rfl rfl hget_jm
  have he_j : evalExpr (.var "j") ρ = .ok (.u64 (BitVec.ofNat 64 j)) :=
    evalExpr_var_hit _ _ _ hj
  have he_sub : evalExpr
      (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ =
      .ok (.u64 (BitVec.ofNat 64 j - BitVec.ofNat 64 1)) :=
    evalExpr_u64_usub _ _ _ _ he_j
  have hi_j : memEvalExpr (.var "j") ρ m π = evalExpr (.var "j") ρ :=
    memEvalExpr_var _ _ _ _
  have hi_sub : memEvalExpr
      (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ m π =
      evalExpr
        (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ :=
    memEvalExpr_usub_agree _ _ _ _ _ hi_j (memEvalExpr_lit _ _ _ _)
  have ha_j : memEvalExpr (.idxu "a" (.var "j")) ρ m π =
      evalExpr (.idxu "a" (.var "j")) ρ :=
    memEvalExpr_idxu_hit _ _ _ _ _ _ _ _ _ _ hlay ha hi_j he_j
      hload_j hget_j
  have ha_jm : memEvalExpr
      (.idxu "a" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))))
      ρ m π =
      evalExpr
        (.idxu "a" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))))
        ρ :=
    memEvalExpr_idxu_hit _ _ _ _ _ _ _ _ _ _ hlay ha hi_sub he_sub
      hload_jm hget_jm
  have ht : memEvalExpr
      (.ult (.idxu "a" (.var "j"))
        (.idxu "a" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1))))))
      ρ m π =
      evalExpr
        (.ult (.idxu "a" (.var "j"))
          (.idxu "a" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1))))))
        ρ :=
    memEvalExpr_ult_agree _ _ _ _ _ ha_j ha_jm
  have hc : memEvalExpr
      (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j")) ρ m π =
      evalExpr (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j")) ρ :=
    memEvalExpr_ult_agree _ _ _ _ _
      (memEvalExpr_lit _ _ _ _) hi_j
  have hvc : evalExpr
      (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j")) ρ =
      .ok (.b true) := by
    have h := evalExpr_ult_u64lit (BitVec.ofNat 64 0) (BitVec.ofNat 64 j)
      (.var "j") ρ (evalExpr_var_hit _ _ _ hj)
    have htrue : (BitVec.ofNat 64 0).ult (BitVec.ofNat 64 j) = true := by
      rw [ofNat64_ult 0 _ (by decide : (0 : Nat) < 2 ^ 64),
        ofNat64_toNat j hj64]
      exact decide_eq_true (by omega : 0 < j)
    rw [htrue] at h
    exact h
  have mtif : memEvalExpr sortInnerCond ρ m π =
      evalExpr sortInnerCond ρ := by
    simp only [sortInnerCond]
    exact memEvalExpr_tif_true _ _ _ _ _ _ hc hvc ht
  rw [mtif]
  exact sortInnerCond_eval_succ 4 ρ l j ha hj hlen (by decide) (by omega) hj1

/-- The outer condition on the memory side: pure index comparison,
    so agreement plus the value lemma suffices. -/
theorem memSortOuterCond_eval (ρ : Env) (m : Mem) (π : Layout) (i : Nat)
    (hi : envLookup ρ "i" = some (.u64 (BitVec.ofNat 64 i))) :
    memEvalExpr (sortOuterCond 4) ρ m π =
      .ok (.b ((BitVec.ofNat 64 i).ult (BitVec.ofNat 64 4))) := by
  have hcond : memEvalExpr (sortOuterCond 4) ρ m π =
      evalExpr (sortOuterCond 4) ρ := by
    simp only [sortOuterCond]
    exact memEvalExpr_ult_agree (.var "i")
      (.lit (.u64 (BitVec.ofNat 64 4))) ρ m π
      (memEvalExpr_var _ _ _ _)
      (memEvalExpr_lit (.u64 (BitVec.ofNat 64 4)) _ _ _)
  rw [hcond]
  exact sortOuterCond_eval 4 ρ i hi

/-! ## Memory swap body (writes lockstepped) -/

/-- One memory swap step: the temp read hits the pinned block, both
    `arrSet`s store lockstep with the value `List.set`
    (`arrSet_lockstep`), the countdown is pure. The block tracks the
    value list exactly. -/
theorem memSortSwapBody_step (F : Nat) (ρ : Env) (m : Mem) (π : Layout)
    (l : List (BitVec 32)) (j : Nat)
    (ha : envLookup ρ "a" = some (.arr32 l))
    (hj : envLookup ρ "j" = some (.u64 (BitVec.ofNat 64 j)))
    (hlen : l.length = 4) (hj3 : j ≤ 3) (hj1 : 1 ≤ j)
    (hlay : layoutLookup π "a" = some (0, 0))
    (hmem : memFind m 0 = some ⟨0, true, l⟩) :
    ∃ ρ₄ m₄, memEvalStmtFuel F sortSwapBody ρ m π =
        .ok ((ρ₄, m₄, π), .fellThrough) ∧
      envLookup ρ₄ "a" =
        some (.arr32 (l.take (j - 1) ++ [l[j], l[j - 1]] ++
          l.drop (j + 1))) ∧
      envLookup ρ₄ "j" = some (.u64 (BitVec.ofNat 64 (j - 1))) ∧
      memFind m₄ 0 =
        some ⟨0, true, l.take (j - 1) ++ [l[j], l[j - 1]] ++
          l.drop (j + 1)⟩ ∧
      envLookup ρ₄ "i" = envLookup ρ "i" := by
  have hj64 : j < 2 ^ 64 := by omega
  have hj_get : l[j]? = some l[j] := List.getElem?_eq_getElem (by omega)
  have hjm_get : l[j - 1]? = some l[j - 1] :=
    List.getElem?_eq_getElem (by omega)
  have hsub_toNat := ofNat64_sub_one_toNat j hj1 hj64
  have hsub_eq := ofNat64_sub_one j hj1 hj64
  have htoNat_j : (BitVec.ofNat 64 j).toNat = j := ofNat64_toNat j hj64
  have hget_j : l[(BitVec.ofNat 64 j).toNat]? = some l[j] := by
    rw [htoNat_j]
    exact hj_get
  have hget_jm : l[(BitVec.ofNat 64 j - BitVec.ofNat 64 1).toNat]? =
      some l[j - 1] := by
    rw [hsub_toNat]
    exact hjm_get
  have hload_j : memLoad m 0 0 (BitVec.ofNat 64 j).toNat = .ok l[j] :=
    memLoad_hit m 0 0 _ _ _ hmem rfl rfl hget_j
  have hload_jm : memLoad m 0 0
      (BitVec.ofNat 64 j - BitVec.ofNat 64 1).toNat = .ok l[j - 1] :=
    memLoad_hit m 0 0 _ _ _ hmem rfl rfl hget_jm
  -- Value expression facts (agreement right sides).
  have e_j : evalExpr (.var "j") ρ = .ok (.u64 (BitVec.ofNat 64 j)) :=
    evalExpr_var_hit _ _ _ hj
  have e_sub : evalExpr
      (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ =
      .ok (.u64 (BitVec.ofNat 64 j - BitVec.ofNat 64 1)) :=
    evalExpr_u64_usub _ _ _ _ e_j
  have e_readj : evalExpr (.idxu "a" (.var "j")) ρ = .ok (.u32 l[j]) := by
    simp only [evalExpr, hj, ha, htoNat_j, hj_get]
  have e_readjm : evalExpr
      (.idxu "a" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))))
      ρ = .ok (.u32 l[j - 1]) := by
    simp only [evalExpr, litVal, hj, ha, hsub_toNat, hjm_get]
  -- Memory expression facts.
  have magree_readj : memEvalExpr (.idxu "a" (.var "j")) ρ m π =
      evalExpr (.idxu "a" (.var "j")) ρ :=
    memEvalExpr_idxu_hit _ _ _ _ _ _ _ _ _ _ hlay ha
      (memEvalExpr_var _ _ _ _) e_j hload_j hget_j
  have me_readj : memEvalExpr (.idxu "a" (.var "j")) ρ m π =
      .ok (.u32 l[j]) := by
    rw [magree_readj]
    exact e_readj
  have me_readjm : memEvalExpr
      (.idxu "a" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))))
      ρ m π = .ok (.u32 l[j - 1]) := by
    have magree := memEvalExpr_idxu_hit _ _ _ _ _ _ _ _ _ _ hlay ha
      (memEvalExpr_usub_agree _ _ _ _ _
        (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _))
      e_sub hload_jm hget_jm
    rw [magree]
    exact e_readjm
  -- The temp `t` (memory untouched).
  have s1 : memEvalStmtFuel F
      (.let_ "t" (.u 32) (.idxu "a" (.var "j"))) ρ m π =
      .ok (((("t", .u32 l[j]) :: ρ, m, π)), .fellThrough) :=
    memEvalStmtFuel_let_pure F _ _ _ _ _ _ _
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) magree_readj e_readj
  have ha₁ : envLookup ((("t", .u32 l[j]) :: ρ)) "a" =
      some (.arr32 l) := by
    simp [envLookup, show ("a" : String) ≠ "t" by decide, ha]
  have hj₁ : envLookup ((("t", .u32 l[j]) :: ρ)) "j" =
      some (.u64 (BitVec.ofNat 64 j)) := by
    simp [envLookup, show ("j" : String) ≠ "t" by decide, hj]
  have ht₁ : envLookup ((("t", .u32 l[j]) :: ρ)) "t" =
      some (.u32 l[j]) := by
    simp [envLookup]
  have hi₁ : envLookup ((("t", .u32 l[j]) :: ρ)) "i" =
      envLookup ρ "i" := by
    simp [envLookup, show ("i" : String) ≠ "t" by decide]
  have me_j₁ : memEvalExpr (.var "j") ((("t", .u32 l[j]) :: ρ)) m π =
      .ok (.u64 (BitVec.ofNat 64 j)) := by
    rw [memEvalExpr_var]
    exact evalExpr_var_hit _ _ _ hj₁
  have me_readjm₁ : memEvalExpr
      (.idxu "a" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))))
      ((("t", .u32 l[j]) :: ρ)) m π = .ok (.u32 l[j - 1]) := by
    have magree := memEvalExpr_idxu_hit _ _ _ _ _ _ _ _ _ _ hlay ha₁
      (memEvalExpr_usub_agree _ _ _ _ _
        (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _))
      (evalExpr_u64_usub _ _ _ _
        (evalExpr_var_hit _ _ _ hj₁)) hload_jm hget_jm
    rw [magree]
    simp only [evalExpr, litVal, hj₁, ha₁, hsub_toNat, hjm_get]
  -- First `arrSet`: write `l[j-1]` at `j`, lockstep.
  obtain ⟨m₂, hstore₁, hfind₂⟩ := arrSet_lockstep m 0 0 l
    (BitVec.ofNat 64 j).toNat l[j - 1] l[j] ⟨0, true, l⟩ hmem rfl
    rfl rfl hget_j
  obtain ⟨ρ₂, hu₁⟩ := envUpdate_some_of_lookup
    ((("t", .u32 l[j]) :: ρ)) "a" (.arr32 l)
    (.arr32 (l.set (BitVec.ofNat 64 j).toNat l[j - 1])) ha₁
  have s2 : memEvalStmtFuel F
      (.arrSet "a" (.var "j")
        (.idxu "a" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1))))))
      ((("t", .u32 l[j]) :: ρ)) m π =
      .ok ((ρ₂, m₂, π), .fellThrough) := by
    cases F <;>
      simp only [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
        me_j₁, me_readjm₁, ha₁, hlay, hget_j, hstore₁, hu₁]
  have ha₂ : envLookup ρ₂ "a" =
      some (.arr32 (l.set (BitVec.ofNat 64 j).toNat l[j - 1])) :=
    envLookup_envUpdate_same _ _ _ _ hu₁
  have hj₂ : envLookup ρ₂ "j" = some (.u64 (BitVec.ofNat 64 j)) := by
    have h := envLookup_envUpdate_diff ((("t", .u32 l[j]) :: ρ)) "a" "j"
      _ _ hu₁ (by decide)
    rw [hj₁] at h
    exact h
  have ht₂ : envLookup ρ₂ "t" = some (.u32 l[j]) := by
    have h := envLookup_envUpdate_diff ((("t", .u32 l[j]) :: ρ)) "a" "t"
      _ _ hu₁ (by decide)
    rw [ht₁] at h
    exact h
  have hi₂ : envLookup ρ₂ "i" = envLookup ρ "i" := by
    have h := envLookup_envUpdate_diff ((("t", .u32 l[j]) :: ρ)) "a" "i"
      _ _ hu₁ (by decide)
    rw [hi₁] at h
    exact h
  have me_j₂ : memEvalExpr (.var "j") ρ₂ m₂ π =
      .ok (.u64 (BitVec.ofNat 64 j)) := by
    rw [memEvalExpr_var]
    exact evalExpr_var_hit _ _ _ hj₂
  have me_t₂ : memEvalExpr (.var "t") ρ₂ m₂ π = .ok (.u32 l[j]) := by
    rw [memEvalExpr_var]
    exact evalExpr_var_hit _ _ _ ht₂
  have me_sub₂ : memEvalExpr
      (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ m₂ π =
      .ok (.u64 (BitVec.ofNat 64 j - BitVec.ofNat 64 1)) := by
    have magree : memEvalExpr
        (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ m₂ π =
        evalExpr
          (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ :=
      memEvalExpr_usub_agree _ _ _ _ _
        (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)
    rw [magree]
    exact evalExpr_u64_usub _ _ _ _ (evalExpr_var_hit _ _ _ hj₂)
  -- Second `arrSet`: write `t` at `j - 1`, lockstep.
  have hset2_get : (l.set (BitVec.ofNat 64 j).toNat l[j - 1])[
      (BitVec.ofNat 64 j - BitVec.ofNat 64 1).toNat]? =
      some l[j - 1] := by
    rw [hsub_toNat, htoNat_j, List.getElem?_set_ne (by omega : j ≠ j - 1)]
    exact hjm_get
  obtain ⟨m₃, hstore₂, hfind₃⟩ := arrSet_lockstep m₂ 0 0
    (l.set (BitVec.ofNat 64 j).toNat l[j - 1])
    (BitVec.ofNat 64 j - BitVec.ofNat 64 1).toNat l[j] l[j - 1]
    ⟨0, true, l.set (BitVec.ofNat 64 j).toNat l[j - 1]⟩ hfind₂ rfl rfl
    rfl hset2_get
  obtain ⟨ρ₃, hu₂⟩ := envUpdate_some_of_lookup ρ₂ "a"
    (.arr32 (l.set (BitVec.ofNat 64 j).toNat l[j - 1]))
    (.arr32 ((l.set (BitVec.ofNat 64 j).toNat l[j - 1]).set
      (BitVec.ofNat 64 j - BitVec.ofNat 64 1).toNat l[j])) ha₂
  have s3 : memEvalStmtFuel F
      (.arrSet "a" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1))))
        (.var "t")) ρ₂ m₂ π = .ok ((ρ₃, m₃, π), .fellThrough) := by
    cases F <;>
      simp only [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
        me_sub₂, me_t₂, ha₂, hlay, hset2_get, hstore₂, hu₂]
  have ha₃ : envLookup ρ₃ "a" = some (.arr32
      (((l.set (BitVec.ofNat 64 j).toNat l[j - 1]).set
        (BitVec.ofNat 64 j - BitVec.ofNat 64 1).toNat l[j]))) :=
    envLookup_envUpdate_same _ _ _ _ hu₂
  have hj₃' : envLookup ρ₃ "j" = some (.u64 (BitVec.ofNat 64 j)) := by
    have h := envLookup_envUpdate_diff ρ₂ "a" "j" _ _ hu₂ (by decide)
    rw [hj₂] at h
    exact h
  have hi₃ : envLookup ρ₃ "i" = envLookup ρ "i" := by
    have h := envLookup_envUpdate_diff ρ₂ "a" "i" _ _ hu₂ (by decide)
    rw [hi₂] at h
    exact h
  have me_sub₃ : memEvalExpr
      (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₃ m₃ π =
      evalExpr
        (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₃ :=
    memEvalExpr_usub_agree _ _ _ _ _
      (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)
  have ve_sub₃ : evalExpr
      (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₃ =
      .ok (.u64 (BitVec.ofNat 64 j - BitVec.ofNat 64 1)) :=
    evalExpr_u64_usub _ _ _ _ (evalExpr_var_hit _ _ _ hj₃')
  -- The countdown `j := j - 1` (memory untouched).
  obtain ⟨ρ₄, hu₃⟩ := envUpdate_some_of_lookup ρ₃ "j"
    (.u64 (BitVec.ofNat 64 j))
    (.u64 (BitVec.ofNat 64 j - BitVec.ofNat 64 1)) hj₃'
  have s4 : memEvalStmtFuel F
      (.assign "j" (.usub (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))))
      ρ₃ m₃ π = .ok ((ρ₄, m₃, π), .fellThrough) :=
    memEvalStmtFuel_assign F _ _ _ _ _ _ _ me_sub₃ ve_sub₃ hu₃
  have hj₄ : envLookup ρ₄ "j" = some (.u64 (BitVec.ofNat 64 (j - 1))) := by
    rw [← hsub_eq]
    exact envLookup_envUpdate_same _ _ _ _ hu₃
  have hi₄ : envLookup ρ₄ "i" = envLookup ρ "i" := by
    have h := envLookup_envUpdate_diff ρ₃ "j" "i" _ _ hu₃ (by decide)
    rw [hi₃] at h
    exact h
  -- The spliced array and block are the take/drop step.
  have harr : (l.set (BitVec.ofNat 64 j).toNat l[j - 1]).set
        (BitVec.ofNat 64 j - BitVec.ofNat 64 1).toNat l[j] =
        l.take (j - 1) ++ [l[j], l[j - 1]] ++ l.drop (j + 1) := by
    rw [htoNat_j, hsub_toNat]
    have h := set_take_drop l (j - 1) l[j - 1] l[j] (by omega)
    rw [show (j - 1) + 1 = j from by omega] at h
    rw [show (j - 1) + 2 = j + 1 from by omega] at h
    exact h
  have hfind₄ : memFind m₃ 0 =
      some ⟨0, true, l.take (j - 1) ++ [l[j], l[j - 1]] ++
        l.drop (j + 1)⟩ := by
    rw [harr] at hfind₃
    exact hfind₃
  have ha₄ : envLookup ρ₄ "a" = some (.arr32
      (l.take (j - 1) ++ [l[j], l[j - 1]] ++ l.drop (j + 1))) := by
    have h := envLookup_envUpdate_diff ρ₃ "j" "a" _ _ hu₃ (by decide)
    rw [harr] at ha₃
    rw [ha₃] at h
    exact h
  refine ⟨ρ₄, m₃, ?_, ha₄, hj₄, hfind₄, hi₄⟩
  simp only [sortSwapBody]
  rw [memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _ s1,
    memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _ s2,
    memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _ s3]
  exact s4

/-! ## Memory inner loop (block tracks the bubble-down) -/

/-- Inner-loop correctness on the memory side: the loop mirrors
    `bubbleDown` with the block tracking the current value list
    (fuel covers the `j + 1` live indices; `i` is untouched). -/
theorem memSortInnerWhile_correct (F : Nat) (ρ : Env) (m : Mem)
    (π : Layout) (l₀ : List (BitVec 32)) (l : List (BitVec 32))
    (j : Nat) (z : BitVec 32)
    (ha : envLookup ρ "a" = some (.arr32 l))
    (hj : envLookup ρ "j" = some (.u64 (BitVec.ofNat 64 j)))
    (hlen : l.length = 4) (hj3 : j ≤ 3)
    (hz : l[j]? = some z)
    (htake : l.take j = l₀.take j)
    (hF : j + 1 ≤ F)
    (hlay : layoutLookup π "a" = some (0, 0))
    (hmem : memFind m 0 = some ⟨0, true, l⟩) :
    ∃ ρ' m', memEvalStmtFuel F sortInnerWhile ρ m π =
        .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "a" = some (.arr32 (bubbleDown l j)) ∧
      memFind m' 0 = some ⟨0, true, bubbleDown l j⟩ ∧
      envLookup ρ' "i" = envLookup ρ "i" := by
  refine Nat.rec
    (motive := fun F => ∀ (ρ : Env) (m : Mem) (π : Layout)
      (l : List (BitVec 32)) (j : Nat)
      (ha : envLookup ρ "a" = some (.arr32 l))
      (hj : envLookup ρ "j" = some (.u64 (BitVec.ofNat 64 j)))
      (hlen : l.length = 4) (hj3 : j ≤ 3)
      (hz : l[j]? = some z) (htake : l.take j = l₀.take j)
      (hF : j + 1 ≤ F)
      (hlay : layoutLookup π "a" = some (0, 0))
      (hmem : memFind m 0 = some ⟨0, true, l⟩),
      ∃ ρ' m', memEvalStmtFuel F sortInnerWhile ρ m π =
          .ok ((ρ', m', π), .fellThrough) ∧
        envLookup ρ' "a" = some (.arr32 (bubbleDown l j)) ∧
        memFind m' 0 = some ⟨0, true, bubbleDown l j⟩ ∧
        envLookup ρ' "i" = envLookup ρ "i")
    ?_ ?_ F ρ m π l j ha hj hlen hj3 hz htake hF hlay hmem
  · clear F ρ m π l j ha hj hlen hj3 hz htake hF hlay hmem
    intro ρ m π l j ha hj hlen hj3 hz htake hF hlay hmem
    have h0 : j + 1 ≤ 0 := hF
    exact (Nat.not_succ_le_zero j h0).elim
  · clear F ρ m π l j ha hj hlen hj3 hz htake hF hlay hmem
    intro F ih ρ m π l j ha hj hlen hj3 hz htake hF hlay hmem
    -- Structural split on the index (as on the value side).
    cases j with
    | zero =>
      have hcond := memSortInnerCond_eval_zero ρ m π l hj hlay hmem
      have hexit : memEvalStmtFuel (F + 1) sortInnerWhile ρ m π =
          .ok ((ρ, m, π), .fellThrough) := by
        simp [sortInnerWhile, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond]
      rw [hexit]
      refine ⟨ρ, m, rfl, ?_, ?_, rfl⟩
      · -- `bubbleDown` at zero is definitionally `l`.
        show envLookup ρ "a" = some (.arr32 l)
        exact ha
      · show memFind m 0 = some ⟨0, true, l⟩
        exact hmem
    | succ k =>
      have hj1 : 1 ≤ k + 1 := by omega
      have hcond := memSortInnerCond_eval_succ ρ m π l (k + 1) ha hj
        hlen hj3 hj1 hlay hmem
      by_cases hc : l[k + 1].ult l[(k + 1) - 1] = true
      · -- Swap iteration: body, then the IH below.
        rw [hc] at hcond
        obtain ⟨ρ₄, m₄, hbody, ha₄, hj₄, hmem₄, hi₄⟩ :=
          memSortSwapBody_step F ρ m π l (k + 1) ha hj hlen
            (by omega) (by omega) hlay hmem
        -- `(k+1)-1 ≡ k`, `(k+1)+1 ≡ k+2` definitionally: ascribe the
        -- post-state in `k`-form.
        have ha₄k : envLookup ρ₄ "a" = some (.arr32
          (l.take k ++ [l[k + 1], l[k]] ++ l.drop (k + 2))) := ha₄
        have hj₄k : envLookup ρ₄ "j" =
          some (.u64 (BitVec.ofNat 64 k)) := hj₄
        have hmem₄k : memFind m₄ 0 = some ⟨0, true,
          l.take k ++ [l[k + 1], l[k]] ++ l.drop (k + 2)⟩ := hmem₄
        have hstep : memEvalStmtFuel (F + 1) sortInnerWhile ρ m π =
            memEvalStmtFuel F sortInnerWhile ρ₄ m₄ π := by
          simp [sortInnerWhile, memEvalStmtFuel, memEvalSuccHandler,
            memEvalStmtWith, hcond, hbody]
        rw [hstep]
        have hAlen : (l.take k).length = k := take_length_eq _ _ (by omega)
        have hzj : l[k + 1] = z := by
          have hinj : ∀ (a b : BitVec 32), (some a = some b) → a = b := by
            intro a b h
            cases h
            rfl
          have g := List.getElem?_eq_getElem (show k + 1 < l.length from by omega)
          rw [hz] at g
          exact (hinj _ _ g).symm
        -- Value-form post-state: the swapped head is the tracked `z`.
        have ha₄z : envLookup ρ₄ "a" = some (.arr32
          (l.take k ++ [z, l[k]] ++ l.drop (k + 2))) := by
          have g := ha₄k
          rw [hzj] at g
          exact g
        have hmem₄z : memFind m₄ 0 = some ⟨0, true,
          l.take k ++ [z, l[k]] ++ l.drop (k + 2)⟩ := by
          have g := hmem₄k
          rw [hzj] at g
          exact g
        have hz' : ((l.take k ++ [z, l[k]] ++ l.drop (k + 2)))[k]? =
            some z := by
          have e := getElem?_append_add (l.take k)
            ([z, l[k]] ++ l.drop (k + 2)) 0
          rw [hAlen, show k + 0 = k from by omega] at e
          rw [List.append_assoc, e]
          have hB0 : (([z, l[k]] ++ l.drop (k + 2))[0]?) = some z := rfl
          rw [hB0]
        have htake' :
            ((l.take k ++ [z, l[k]] ++ l.drop (k + 2))).take k =
            l₀.take k := by
          have e := take_append_self (l.take k) ([z, l[k]] ++ l.drop (k + 2))
          rw [hAlen] at e
          rw [List.append_assoc, e]
          have hA : l.take k = l₀.take k := by
            have e1 : (l.take (k + 1)).take k = l.take k := by
              rw [List.take_take, show min k (k + 1) = k from by omega]
            have e2 : (l₀.take (k + 1)).take k = l₀.take k := by
              rw [List.take_take, show min k (k + 1) = k from by omega]
            rw [htake] at e1
            rw [e2] at e1
            exact e1.symm
          exact hA
        have hlen' : (l.take k ++ [z, l[k]] ++ l.drop (k + 2)).length = 4 := by
          have hmin : min k l.length = k := by omega
          have h2 : [z, l[k]].length = 2 := rfl
          rw [List.length_append, List.length_append, List.length_take, hmin,
            h2, List.length_drop, hlen]
          omega
        have hF' : k + 1 ≤ F := by omega
        have hj3' : k ≤ 3 := by omega
        obtain ⟨ρ', m', hloop, ha', hmem', hi'⟩ :=
          ih ρ₄ m₄ π _ k ha₄z hj₄k hlen' hj3' hz' htake' hF' hlay hmem₄z
        -- The loop head equals the pure unfold.
        have hbub : bubbleDown l (k + 1) = bubbleDown
            (l.take k ++ [z, l[k]] ++ l.drop (k + 2)) k := by
          have hgetk : l[k]? = some l[k] :=
            List.getElem?_eq_getElem (by omega)
          simp only [bubbleDown, hz, hgetk]
          -- `(k+1)-1` is definitionally `k`, so `hc` ascribes directly.
          have hck : l[k + 1].ult l[k] = true := hc
          have hc' : z.ult l[k] = true := by
            rw [hzj] at hck
            exact hck
          rw [if_pos hc']
          rw [set_take_drop l k l[k] z (by omega)]
        refine ⟨ρ', m', hloop, ?_, ?_, ?_⟩
        · rw [hbub]
          exact ha'
        · rw [hbub]
          exact hmem'
        · rw [hi']
          exact hi₄
      · -- Exit with `¬ z < l[j-1]`: the array is already bubbled.
        have hc' : l[k + 1].ult l[(k + 1) - 1] = false :=
          bool_eq_false_of_not_true hc
        rw [hc'] at hcond
        have hexit : memEvalStmtFuel (F + 1) sortInnerWhile ρ m π =
            .ok ((ρ, m, π), .fellThrough) := by
          simp [sortInnerWhile, memEvalStmtFuel, memEvalSuccHandler,
            memEvalStmtWith, hcond]
        rw [hexit]
        have hbub : bubbleDown l (k + 1) = l := by
          have hgetk : l[k]? = some l[k] :=
            List.getElem?_eq_getElem (by omega)
          simp only [bubbleDown, hz, hgetk]
          -- Same definitional `(k+1)-1 = k` ascription as above.
          have hck : ¬ l[k + 1].ult l[k] = true := hc
          have hzj : l[k + 1] = z := by
            have hinj : ∀ (a b : BitVec 32), (some a = some b) → a = b := by
              intro a b h
              cases h
              rfl
            have g := List.getElem?_eq_getElem
              (show k + 1 < l.length from by omega)
            rw [hz] at g
            exact (hinj _ _ g).symm
          have hc'' : ¬ z.ult l[k] = true := by
            rw [hzj] at hck
            exact hck
          rw [if_neg hc'']
        refine ⟨ρ, m, rfl, ?_, ?_, rfl⟩
        · rw [hbub]
          exact ha
        · rw [hbub]
          exact hmem

/-! ## Memory outer pass (sorted prefix preserved in the block) -/

/-- One memory outer pass: rebind `j`, bubble down (block follows
    the value list), step `i`. The post-pass block holds the outer
    step with sorted `take (i+1)` prefix. -/
theorem memSortOuterBody_step (F : Nat) (ρ : Env) (m : Mem) (π : Layout)
    (l : List (BitVec 32)) (i : Nat)
    (ha : envLookup ρ "a" = some (.arr32 l))
    (hi : envLookup ρ "i" = some (.u64 (BitVec.ofNat 64 i)))
    (hlen : l.length = 4) (hi3 : i ≤ 3)
    (hsorted : (l.take i).Pairwise (fun a b => b.ult a = false))
    (hF : i + 1 ≤ F)
    (hlay : layoutLookup π "a" = some (0, 0))
    (hmem : memFind m 0 = some ⟨0, true, l⟩) :
    ∃ ρ' m', memEvalStmtFuel F sortOuterBody ρ m π =
        .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "a" =
        some (.arr32 (outerListStep l i (l[i]?.getD 0))) ∧
      envLookup ρ' "i" = some (.u64 (BitVec.ofNat 64 (i + 1))) ∧
      memFind m' 0 =
        some ⟨0, true, outerListStep l i (l[i]?.getD 0)⟩ ∧
      ((outerListStep l i (l[i]?.getD 0)).take (i + 1)).Pairwise
        (fun a b => b.ult a = false) ∧
      (outerListStep l i (l[i]?.getD 0)).length = 4 := by
  have hi64 : i < 2 ^ 64 := by omega
  have hz : l[i]? = some l[i] := List.getElem?_eq_getElem (by omega)
  have hgetD : l[i]?.getD 0 = l[i] := by simp [hz]
  have hstep_eq : outerListStep l i (l[i]?.getD 0) =
      insertU32 l[i] (l.take i) ++ l.drop (i + 1) := by
    simp only [outerListStep, hgetD]
  -- Rebind `j` at `i` (memory untouched).
  have e_i : evalExpr (.var "i") ρ = .ok (.u64 (BitVec.ofNat 64 i)) :=
    evalExpr_var_hit _ _ _ hi
  have s1 : memEvalStmtFuel F (.let_ "j" (.u 64) (.var "i")) ρ m π =
      .ok (((("j", .u64 (BitVec.ofNat 64 i)) :: ρ, m, π)),
        .fellThrough) :=
    memEvalStmtFuel_let_pure F _ _ _ _ _ _ _
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) (memEvalExpr_var _ _ _ _) e_i
  have ha₁ : envLookup ((("j", .u64 (BitVec.ofNat 64 i)) :: ρ)) "a" =
      some (.arr32 l) := by
    simp [envLookup, show ("a" : String) ≠ "j" by decide, ha]
  have hj₁ : envLookup ((("j", .u64 (BitVec.ofNat 64 i)) :: ρ)) "j" =
      some (.u64 (BitVec.ofNat 64 i)) := by
    simp [envLookup]
  have hi₁ : envLookup ((("j", .u64 (BitVec.ofNat 64 i)) :: ρ)) "i" =
      envLookup ρ "i" := by
    simp [envLookup, show ("i" : String) ≠ "j" by decide]
  -- Bubble down from `j = i`.
  obtain ⟨ρ₂, m₂, hloop, ha₂raw, hmem₂raw, hi₂raw⟩ :=
    memSortInnerWhile_correct F
      ((("j", .u64 (BitVec.ofNat 64 i)) :: ρ)) m π l l i l[i]
      ha₁ hj₁ hlen hi3 hz rfl hF hlay hmem
  have hi₂' : envLookup ρ₂ "i" = some (.u64 (BitVec.ofNat 64 i)) := by
    rw [hi₂raw, hi₁]
    exact hi
  -- The bubbled array and block are the outer step.
  have hdrop : (l.take i).drop i = [] := by
    have hL : (l.take i).length = i := take_length_eq _ _ (by omega)
    have h := drop_all (l.take i)
    rw [hL] at h
    exact h
  have hslice : l.drop (i + 1) = (l.take i).drop i ++ l.drop (i + 1) := by
    simp [hdrop]
  have hmid : ∀ w ∈ (l.take i).drop i, l[i].ult w = true := by
    intro w hw
    rw [hdrop] at hw
    simp at hw
  have hbub := bubbleDown_eq_outerListStep 4 l i l i l[i] hlen (by omega)
    hsorted hlen (Nat.le_refl i) hz rfl hslice hmid
  have ha₂ : envLookup ρ₂ "a" =
      some (.arr32 (outerListStep l i (l[i]?.getD 0))) := by
    rw [hbub] at ha₂raw
    rw [← hstep_eq] at ha₂raw
    exact ha₂raw
  have hmem₂ : memFind m₂ 0 =
      some ⟨0, true, outerListStep l i (l[i]?.getD 0)⟩ := by
    rw [hbub] at hmem₂raw
    rw [← hstep_eq] at hmem₂raw
    exact hmem₂raw
  -- Step `i` (memory untouched).
  have e_i₂ : evalExpr (.var "i") ρ₂ = .ok (.u64 (BitVec.ofNat 64 i)) :=
    evalExpr_var_hit _ _ _ hi₂'
  have euadd : ∀ (e : CExpr) (r : Env) (x : BitVec 64),
      evalExpr e r = .ok (.u64 x) →
      evalExpr (.uadd e (.lit (.u64 (BitVec.ofNat 64 1)))) r =
        .ok (.u64 (x + BitVec.ofNat 64 1)) := by
    intro e r x h
    simp [evalExpr, litVal, h]
  have e_add : evalExpr
      (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ =
      .ok (.u64 (BitVec.ofNat 64 (i + 1))) := by
    have h := euadd _ _ _ e_i₂
    rw [ofNat64_add_one] at h
    exact h
  have magree_add : memEvalExpr
      (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ m₂ π =
      evalExpr
        (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ :=
    memEvalExpr_uadd_agree _ _ _ _ _
      (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)
  obtain ⟨ρ₃, hu⟩ := envUpdate_some_of_lookup ρ₂ "i"
    (.u64 (BitVec.ofNat 64 i)) (.u64 (BitVec.ofNat 64 (i + 1))) hi₂'
  have s3 : memEvalStmtFuel F
      (.assign "i" (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))))
      ρ₂ m₂ π = .ok ((ρ₃, m₂, π), .fellThrough) :=
    memEvalStmtFuel_assign F _ _ _ _ _ _ _ magree_add e_add hu
  have ha₃ : envLookup ρ₃ "a" =
      some (.arr32 (outerListStep l i (l[i]?.getD 0))) := by
    have h := envLookup_envUpdate_diff ρ₂ "i" "a" _ _ hu (by decide)
    rw [ha₂] at h
    exact h
  have hi₃ : envLookup ρ₃ "i" = some (.u64 (BitVec.ofNat 64 (i + 1))) :=
    envLookup_envUpdate_same _ _ _ _ hu
  -- The post-pass prefix is sorted with length preserved.
  have hL : (insertU32 l[i] (l.take i)).length = i + 1 := by
    rw [insertU32_length, take_length_eq _ _ (by omega)]
  have htakeN : ((insertU32 l[i] (l.take i) ++ l.drop (i + 1)).take
      (i + 1)) = insertU32 l[i] (l.take i) := by
    have e := take_append_self (insertU32 l[i] (l.take i)) (l.drop (i + 1))
    rw [hL] at e
    exact e
  have hnew_sorted : ((outerListStep l i (l[i]?.getD 0)).take
      (i + 1)).Pairwise (fun a b => b.ult a = false) := by
    rw [hstep_eq, htakeN]
    exact pairwise_insertU32_sorted _ _ hsorted
  have hnew_len : (outerListStep l i (l[i]?.getD 0)).length = 4 := by
    rw [hstep_eq, List.length_append, insertU32_length,
      take_length_eq _ _ (by omega), List.length_drop, hlen]
    omega
  refine ⟨ρ₃, m₂, ?_, ha₃, hi₃, hmem₂, hnew_sorted, hnew_len⟩
  simp only [sortOuterBody]
  rw [memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _ s1,
    memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _ hloop]
  exact s3

/-! ## Memory outer loop (block tracks the passes) -/

/-- Outer-loop correctness on the memory side: pass `i` bubbles
    `l[i]` into the sorted prefix with the block following, and the
    IH runs the remaining passes. Same fuel bound as the value side. -/
theorem memSortOuterWhile_correct (F : Nat) (ρ : Env) (m : Mem)
    (π : Layout) (l : List (BitVec 32)) (i : Nat)
    (ha : envLookup ρ "a" = some (.arr32 l))
    (hi : envLookup ρ "i" = some (.u64 (BitVec.ofNat 64 i)))
    (hlen : l.length = 4) (hi1 : 1 ≤ i) (hi4 : i ≤ 4)
    (hsorted : (l.take i).Pairwise (fun a b => b.ult a = false))
    (hF : (4 - i) + 4 ≤ F)
    (hlay : layoutLookup π "a" = some (0, 0))
    (hmem : memFind m 0 = some ⟨0, true, l⟩) :
    ∃ ρ' m', memEvalStmtFuel F (sortOuterWhile 4) ρ m π =
        .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "a" = some (.arr32 (outerListAux 4 l i (4 - i))) ∧
      memFind m' 0 = some ⟨0, true, outerListAux 4 l i (4 - i)⟩ ∧
      envLookup ρ' "i" = some (.u64 (BitVec.ofNat 64 4)) := by
  refine Nat.rec
    (motive := fun F => ∀ (ρ : Env) (m : Mem) (π : Layout)
      (l : List (BitVec 32)) (i : Nat)
      (ha : envLookup ρ "a" = some (.arr32 l))
      (hi : envLookup ρ "i" = some (.u64 (BitVec.ofNat 64 i)))
      (hlen : l.length = 4) (hi1 : 1 ≤ i) (hi4 : i ≤ 4)
      (hsorted : (l.take i).Pairwise (fun a b => b.ult a = false))
      (hF : (4 - i) + 4 ≤ F)
      (hlay : layoutLookup π "a" = some (0, 0))
      (hmem : memFind m 0 = some ⟨0, true, l⟩),
      ∃ ρ' m', memEvalStmtFuel F (sortOuterWhile 4) ρ m π =
          .ok ((ρ', m', π), .fellThrough) ∧
        envLookup ρ' "a" = some (.arr32 (outerListAux 4 l i (4 - i))) ∧
        memFind m' 0 = some ⟨0, true, outerListAux 4 l i (4 - i)⟩ ∧
        envLookup ρ' "i" = some (.u64 (BitVec.ofNat 64 4)))
    ?_ ?_ F ρ m π l i ha hi hlen hi1 hi4 hsorted hF hlay hmem
  · intro ρ m π l i ha hi hlen hi1 hi4 hsorted hF hlay hmem
    have h0 : (4 - i) + 4 ≤ 0 := hF
    exact (Nat.not_succ_le_zero _ h0).elim
  · intro F ih ρ m π l i ha hi hlen hi1 hi4 hsorted hF hlay hmem
    have hi64 : i < 2 ^ 64 := by omega
    have hcond := memSortOuterCond_eval ρ m π i hi
    by_cases hi4' : i < 4
    · -- Pass `i`: body, then the remaining passes below.
      have hc : (BitVec.ofNat 64 i).ult (BitVec.ofNat 64 4) = true := by
        rw [ofNat64_ult i _ hi64, ofNat64_toNat 4 (by decide : 4 < 2 ^ 64)]
        exact decide_eq_true hi4'
      rw [hc] at hcond
      obtain ⟨ρ₂, m₂, hbody, ha₂, hi₂, hmem₂, hsorted₂, hlen₂⟩ :=
        memSortOuterBody_step F ρ m π l i ha hi hlen (by omega)
          hsorted (by omega) hlay hmem
      have hstep : memEvalStmtFuel (F + 1) (sortOuterWhile 4) ρ m π =
          memEvalStmtFuel F (sortOuterWhile 4) ρ₂ m₂ π := by
        simp [sortOuterWhile, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond, hbody]
      rw [hstep]
      have hfuel : 4 - i = (3 - i) + 1 := by omega
      have hF' : (4 - (i + 1)) + 4 ≤ F := by omega
      obtain ⟨ρ', m', hloop, ha', hmem', hi'⟩ :=
        ih ρ₂ m₂ π _ (i + 1) ha₂ hi₂ hlen₂ (by omega) (by omega)
          hsorted₂ hF' hlay hmem₂
      -- The loop head equals the pure unfold.
      have haux : outerListAux 4 l i (4 - i) = outerListAux 4
          (outerListStep l i (l[i]?.getD 0)) (i + 1) (4 - (i + 1)) := by
        rw [hfuel, outerListAux_succ, if_pos hi4']
        have heq : 4 - (i + 1) = 3 - i := by omega
        rw [heq]
      refine ⟨ρ', m', hloop, ?_, ?_, hi'⟩
      · rw [haux]
        exact ha'
      · rw [haux]
        exact hmem'
    · -- Exit at `i = 4`: no passes remain.
      have hi4eq : i = 4 := by omega
      have hc : (BitVec.ofNat 64 i).ult (BitVec.ofNat 64 4) = false := by
        rw [ofNat64_ult i _ hi64, ofNat64_toNat 4 (by decide : 4 < 2 ^ 64),
          hi4eq]
        decide
      rw [hc] at hcond
      have hexit : memEvalStmtFuel (F + 1) (sortOuterWhile 4) ρ m π =
          .ok ((ρ, m, π), .fellThrough) := by
        simp [sortOuterWhile, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond]
      rw [hexit]
      subst hi4eq
      have hemp : outerListAux 4 l 4 (4 - 4) = l := rfl
      refine ⟨ρ, m, rfl, ?_, ?_, ?_⟩
      · rw [hemp]
        exact ha
      · rw [hemp]
        exact hmem
      · exact hi

/-! ## Whole-function correctness (fuel-generalized, then transfer) -/

/-- `memEval` for `insertion_sort` at any fuel covering the passes
    (mirrors `evalFuncFuel_insertionSort`; the block rides alongside
    and ends holding the sorted words). -/
theorem memEvalFuncFuel_insertionSort (F : Nat) (l : List (BitVec 32))
    (hlen : l.length = 4) (hF : 7 ≤ F) :
    memEvalFuncFuel F (insertionSortFunc 4) [.arr32 l] = insertionSortFwd l := by
  have hb : bindMemArgs (insertionSortFunc 4).args [.arr32 l] emptyMem =
      some ([("a", .arr32 l)],
        ⟨1, [(0, ⟨0, true, l⟩)], []⟩, [("a", 0, 0)]) :=
    bindMemArgs_insertionSort l
  have hlay : layoutLookup [("a", 0, 0)] "a" = some (0, 0) := by
    simp [layoutLookup]
  have hmem : memFind ⟨1, [(0, ⟨0, true, l⟩)], []⟩ 0 =
      some ⟨0, true, l⟩ := by
    simp [memFind]
  have e_one : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      [("a", .arr32 l)] ⟨1, [(0, ⟨0, true, l⟩)], []⟩ [("a", 0, 0)] =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    rw [memEvalExpr_lit]
    simp [evalExpr, litVal]
  have ve_one : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      [("a", .arr32 l)] = .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have s1 : memEvalStmtFuel F (.let_ "i" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 1)))) [("a", .arr32 l)]
      ⟨1, [(0, ⟨0, true, l⟩)], []⟩ [("a", 0, 0)] =
      .ok (((("i", .u64 (BitVec.ofNat 64 1)) :: ("a", .arr32 l) :: [],
        ⟨1, [(0, ⟨0, true, l⟩)], []⟩, [("a", 0, 0)])), .fellThrough) :=
    memEvalStmtFuel_let_pure F _ _ _ _ _ _ _
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h)
      (memEvalExpr_lit (.u64 (BitVec.ofNat 64 1)) _ _ _) ve_one
  have ha₁ : envLookup
      ((("i", .u64 (BitVec.ofNat 64 1)) :: ("a", .arr32 l) :: [])) "a" =
      some (.arr32 l) := by
    simp [envLookup, show ("a" : String) ≠ "i" by decide]
  have hi₁ : envLookup
      ((("i", .u64 (BitVec.ofNat 64 1)) :: ("a", .arr32 l) :: [])) "i" =
      some (.u64 (BitVec.ofNat 64 1)) := by
    simp [envLookup]
  obtain ⟨ρ₂, m₂, hloop, ha₂, hmem₂, hi₂⟩ :=
    memSortOuterWhile_correct F
      ((("i", .u64 (BitVec.ofNat 64 1)) :: ("a", .arr32 l) :: []))
      ⟨1, [(0, ⟨0, true, l⟩)], []⟩ [("a", 0, 0)] l 1
      ha₁ hi₁ hlen (by decide : 1 ≤ 1) (by decide : 1 ≤ 4)
      (pairwise_take_one l (by omega)) (by omega : (4 - 1) + 4 ≤ F)
      hlay hmem
  have e_ret : memEvalExpr (.var "a") ρ₂ m₂ [("a", 0, 0)] =
      evalExpr (.var "a") ρ₂ :=
    memEvalExpr_var _ _ _ _
  have ve_ret : evalExpr (.var "a") ρ₂ =
      .ok (.arr32 (outerListAux 4 l 1 (4 - 1))) :=
    evalExpr_var_hit _ _ _ ha₂
  have hret : memEvalStmtFuel F (.return_ (.var "a")) ρ₂ m₂
      [("a", 0, 0)] =
      .ok ((ρ₂, m₂, [("a", 0, 0)]),
        .returned (.arr32 (outerListAux 4 l 1 (4 - 1)))) :=
    memEvalStmtFuel_return F _ _ _ _ _ e_ret ve_ret
  have hbody : memEvalStmtFuel F (insertionSortFunc 4).body [("a", .arr32 l)]
      ⟨1, [(0, ⟨0, true, l⟩)], []⟩ [("a", 0, 0)] =
      .ok ((ρ₂, m₂, [("a", 0, 0)]),
        .returned (.arr32 (outerListAux 4 l 1 (4 - 1)))) := by
    rw [insertionSortFunc_body]
    rw [memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _ s1,
      memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _ hloop]
    exact hret
  have hfunc : memEvalFuncFuel F (insertionSortFunc 4) [.arr32 l] =
      .ok (.arr32 (outerListAux 4 l 1 (4 - 1))) := by
    simp [memEvalFuncFuel, hb, hbody]
  -- The loop result is the insertion fold.
  have hsorted_eq : outerListAux 4 l 1 (4 - 1) = insertionSortList l := by
    have h := outerListAux_sortL 4 l 1 (4 - 1) hlen (by omega)
    rw [h]
    exact sortL_take_one_drop_one l (by omega)
  rw [hsorted_eq] at hfunc
  simpa [insertionSortFwd] using hfunc

/-- Transfer for `insertion_sort`: both sides equal `insertionSortFwd`
    (the block discipline is invisible at the value level). -/
theorem memTransfer_insertionSort (F : Nat) (l : List (BitVec 32))
    (hlen : l.length = 4) (hF : 7 ≤ F)
    (_h : oracleNoalias (insertionSortFunc 4) [.arr32 l]) :
    memEvalFuncFuel F (insertionSortFunc 4) [.arr32 l] =
      evalFuncFuel F (insertionSortFunc 4) [.arr32 l] := by
  rw [memEvalFuncFuel_insertionSort F l hlen hF,
    evalFuncFuel_insertionSort 4 F l hlen (by decide) (by decide) (by omega)]
