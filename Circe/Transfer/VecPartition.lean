/-
Circe.Transfer.VecPartition — M3c mem transfer for in-place Lomuto
partition (`vec_partition`).

Mirrors the value loop (`valPartitionBody_take/skip`, `valPartitionLoop_ok`
in `Circe.Emit.VecPartition`) step for step on the memory layer: the
single `mutBorrow` block pins the reified snapshot (`cellsAt` framed by
find; the length word shifts offsets by one), the two swap stores thread
through `memStore` in lockstep on the same block (no second block to
frame — the skip branch stores nothing), and the loop re-inducts over
`(ρ, m, π)` with the forward equation threading (two fuels: program fuel
and forward fuel). One leg only — the kernel is total (every access is
guard-justified). Entries close against the M3b contract.
-/
import Circe.Transfer.VecReverse
import Circe.Emit.VecPartition
import Circe.Specs

/-! ## Binding (closed form) -/

/-- Partition binding pins one snapshot: the single `mutBorrow` vector
    at addr `0`; the owned `pivot` binds by value only (no block, no
    layout — the `stdVecIndex` precedent). -/
theorem bindMemArgs_vecPartition (l : List (BitVec 32))
    (pivot : BitVec 32) :
    bindMemArgs vecPartitionFunc.args
      [.stdVecVal l, .i32 pivot] emptyMem =
      some ([("v", .stdVecVal l), ("pivot", .i32 pivot)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("v", 0, 0)]) := by
  rfl

/-- Partition footprint is a single singleton (the owned `pivot` never
    touches memory). -/
theorem oracleNoalias_vecPartition (l : List (BitVec 32))
    (pivot : BitVec 32) :
    oracleNoalias vecPartitionFunc
      [.stdVecVal l, .i32 pivot] := by
  have hb := bindMemArgs_vecPartition l pivot
  have hn : LayoutNoAlias [("v", 0, 0)] := by
    simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-! ## Memory body hit -/

/-- One body iteration on memory, take branch: the env threads exactly
    as on the value side while the two swap stores prepend shadowing
    snapshot blocks on the single `v` block (layout stays pinned). -/
theorem memPartitionBody_take (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (l : List (BitVec 32)) (pivot : BitVec 32)
    (i s : Nat) (iB sB : BitVec 64) (x w : BitVec 32)
    (a t : Nat) (n : BitVec 32)
    (hlay : layoutLookup π "v" = some (a, t))
    (hmem : memFind m a = some ⟨t, true, n :: l⟩)
    (hn : n = BitVec.ofNat 32 l.length)
    (hiN : iB.toNat = i) (hsN : sB.toNat = s)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hpiv : envLookup ρ "pivot" = some (.i32 pivot))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hs : envLookup ρ "s" = some (.u64 sB))
    (hilt : i < l.length)
    (hx : l[i]? = some x) (hw : l[s]? = some w)
    (hslt : s < l.length)
    (htake : (x.slt pivot) = true) :
    ∃ ρ' m', memEvalProgStmt prog F vecPartitionBody ρ m π =
      .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "v" =
        some (.stdVecVal ((l.set i w).set s x)) ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = i + 1) ∧
      (∃ sB', envLookup ρ' "s" = some (.u64 sB') ∧ sB'.toNat = s + 1) ∧
      envLookup ρ' "pivot" = some (.i32 pivot) ∧
      memFind m' a = some ⟨t, true, n :: ((l.set i w).set s x)⟩ := by
  have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have hsVar : evalExpr (.var "s") ρ = .ok (.u64 sB) :=
    evalExpr_var_hit _ _ _ hs
  have hiVarA : memEvalExpr (.var "i") ρ m π =
      evalExpr (.var "i") ρ :=
    memEvalExpr_var _ _ _ _
  have hsVarA : memEvalExpr (.var "s") ρ m π =
      evalExpr (.var "s") ρ :=
    memEvalExpr_var _ _ _ _
  have hiVarM : memEvalExpr (.var "i") ρ m π = .ok (.u64 iB) :=
    hiVarA.trans hiVar
  have hsVarM : memEvalExpr (.var "s") ρ m π = .ok (.u64 sB) :=
    hsVarA.trans hsVar
  have hvLen : evalExpr (.stdVecLen "v") ρ =
      .ok (.u64 (BitVec.ofNat 64 l.length)) :=
    evalExpr_stdVecLen_some _ _ _ hv
  have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
  have hmemLen : memLoad m a t 0 =
      .ok (BitVec.ofNat 32 l.length) := by
    rw [← hn]
    exact memLoad_cellsAt m a t 0 (n :: l) n hmem (by simp)
  have hoLenM : memEvalExpr (.stdVecLen "v") ρ m π =
      evalExpr (.stdVecLen "v") ρ :=
    memEvalExpr_stdVecLen_hit "v" ρ m π l a t hlay hv hmemLen
  have hguardT : evalExpr (.ult (.var "i") (.stdVecLen "v")) ρ =
      .ok (.b true) := by
    have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "v") ρ iB
      (BitVec.ofNat 64 l.length) hiVar hvLen
    have htb : (iB.ult (BitVec.ofNat 64 l.length)) = true := by
      rw [BitVec.ult_eq_decide]
      exact decide_eq_true (by omega)
    rwa [htb] at hult
  have hagT : memEvalExpr (.ult (.var "i") (.stdVecLen "v")) ρ m π =
      .ok (.b true) :=
    (memEvalExpr_ult_agree (.var "i") (.stdVecLen "v")
      ρ m π hiVarA hoLenM).trans hguardT
  have hgetB : l[iB.toNat]? = some x := by rw [hiN]; exact hx
  have hgetS : l[sB.toNat]? = some w := by rw [hsN]; exact hw
  have hmemA : memLoad m a t (iB.toNat + 1) = .ok x :=
    memLoad_cellsAt m a t (iB.toNat + 1) (n :: l) x
      hmem (by rw [List.getElem?_cons_succ]; exact hgetB)
  have hmemS : memLoad m a t (sB.toNat + 1) = .ok w :=
    memLoad_cellsAt m a t (sB.toNat + 1) (n :: l) w
      hmem (by rw [List.getElem?_cons_succ]; exact hgetS)
  have hat : evalExpr (.stdVecAt "v" (.var "i")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hiVar hgetB
  have hatM_ag : memEvalExpr (.stdVecAt "v" (.var "i")) ρ m π =
      evalExpr (.stdVecAt "v" (.var "i")) ρ :=
    memEvalExpr_stdVecAt_hit "v" (.var "i") ρ m π l iB x a t
      hlay hv hiVarA hiVar hmemA hgetB
  have hatM : memEvalExpr (.stdVecAt "v" (.var "i")) ρ m π =
      .ok (.i32 x) := by rw [hatM_ag]; exact hat
  have hatS : evalExpr (.stdVecAt "v" (.var "s")) ρ = .ok (.i32 w) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hsVar hgetS
  have hatSM_ag : memEvalExpr (.stdVecAt "v" (.var "s")) ρ m π =
      evalExpr (.stdVecAt "v" (.var "s")) ρ :=
    memEvalExpr_stdVecAt_hit "v" (.var "s") ρ m π l sB w a t
      hlay hv hsVarA hsVar hmemS hgetS
  have hatSM : memEvalExpr (.stdVecAt "v" (.var "s")) ρ m π =
      .ok (.i32 w) := by rw [hatSM_ag]; exact hatS
  have hpivV : evalExpr (.var "pivot") ρ = .ok (.i32 pivot) :=
    evalExpr_var_hit _ _ _ hpiv
  have hpivA : memEvalExpr (.var "pivot") ρ m π =
      evalExpr (.var "pivot") ρ :=
    memEvalExpr_var _ _ _ _
  have hpivM : memEvalExpr (.var "pivot") ρ m π = .ok (.i32 pivot) :=
    hpivA.trans hpivV
  have hsltV : evalExpr (.slt (.stdVecAt "v" (.var "i"))
      (.var "pivot")) ρ = .ok (.b true) := by
    have h := evalExpr_slt_i32 (.stdVecAt "v" (.var "i"))
      (.var "pivot") ρ x pivot hat hpivV
    rwa [htake] at h
  have hsltM : memEvalExpr (.slt (.stdVecAt "v" (.var "i"))
      (.var "pivot")) ρ m π = .ok (.b true) :=
    (memEvalExpr_slt_agree (.stdVecAt "v" (.var "i"))
      (.var "pivot") ρ m π hatM_ag hpivA).trans hsltV
  have hlet := memRevLet prog F "t" (.i 32)
    (.stdVecAt "v" (.var "i")) ρ m π (.i32 x)
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) hatM_ag hat
  have ht : envLookup (envExtend ρ "t" (.i32 x)) "t" =
      some (.i32 x) :=
    envExtend_hit _ _ _
  have hv₁ : envLookup (envExtend ρ "t" (.i32 x)) "v" =
      some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "t" by decide)]
    exact hv
  have hi₁ : envLookup (envExtend ρ "t" (.i32 x)) "i" =
      some (.u64 iB) := by
    rw [envExtend_miss _ _ _ _
      (show ("i" : String) ≠ "t" by decide)]
    exact hi
  have hs₁ : envLookup (envExtend ρ "t" (.i32 x)) "s" =
      some (.u64 sB) := by
    rw [envExtend_miss _ _ _ _
      (show ("s" : String) ≠ "t" by decide)]
    exact hs
  have hpiv₁ : envLookup (envExtend ρ "t" (.i32 x)) "pivot" =
      some (.i32 pivot) := by
    rw [envExtend_miss _ _ _ _
      (show ("pivot" : String) ≠ "t" by decide)]
    exact hpiv
  have hiVar₁ : evalExpr (.var "i") (envExtend ρ "t" (.i32 x)) =
      .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi₁
  have hsVar₁ : evalExpr (.var "s") (envExtend ρ "t" (.i32 x)) =
      .ok (.u64 sB) :=
    evalExpr_var_hit _ _ _ hs₁
  have hiVarA₁ : memEvalExpr (.var "i") (envExtend ρ "t" (.i32 x))
      m π = evalExpr (.var "i") (envExtend ρ "t" (.i32 x)) :=
    memEvalExpr_var _ _ _ _
  have hsVarA₁ : memEvalExpr (.var "s") (envExtend ρ "t" (.i32 x))
      m π = evalExpr (.var "s") (envExtend ρ "t" (.i32 x)) :=
    memEvalExpr_var _ _ _ _
  have hatS₁ : evalExpr (.stdVecAt "v" (.var "s"))
      (envExtend ρ "t" (.i32 x)) = .ok (.i32 w) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv₁ hsVar₁ hgetS
  have hatS₁_ag : memEvalExpr (.stdVecAt "v" (.var "s"))
      (envExtend ρ "t" (.i32 x)) m π =
      evalExpr (.stdVecAt "v" (.var "s"))
        (envExtend ρ "t" (.i32 x)) :=
    memEvalExpr_stdVecAt_hit "v" (.var "s")
      (envExtend ρ "t" (.i32 x)) m π l sB w a t
      hlay hv₁ hsVarA₁ hsVar₁ hmemS hgetS
  have hatS₁M : memEvalExpr (.stdVecAt "v" (.var "s"))
      (envExtend ρ "t" (.i32 x)) m π = .ok (.i32 w) := by
    rw [hatS₁_ag]; exact hatS₁
  have hlt₁ : iB.toNat + 1 < (n :: l).length := by
    simp only [List.length_cons]
    omega
  obtain ⟨m₁, hmstore⟩ : ∃ m', memStore m a t (iB.toNat + 1) w =
      .ok m' :=
    ⟨_, memStore_cellsAt m a t (iB.toNat + 1) (n :: l) w
      hmem hlt₁⟩
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup
    (envExtend ρ "t" (.i32 x)) "v"
    (.stdVecVal l) (.stdVecVal (l.set iB.toNat w)) hv₁
  have hiVarM₁ : memEvalExpr (.var "i")
      (envExtend ρ "t" (.i32 x)) m π = .ok (.u64 iB) :=
    hiVarA₁.trans hiVar₁
  have hstep_set1 := memRevVecSet prog F "v" (.var "i")
    (.stdVecAt "v" (.var "s")) (envExtend ρ "t" (.i32 x)) m π
    iB w a t l x m₁ ρ₁ hiVarM₁ hatS₁M hv₁ hlay hgetB hmstore hu₁
  have hcells₁ : cellsAt m₁ a t ((n :: l).set (iB.toNat + 1) w) :=
    memFind_cellsAt_store m a t (iB.toNat + 1) (n :: l) w m₁
      hmem hlt₁ hmstore
  have hsetB : l.set iB.toNat w = l.set i w := by rw [hiN]
  have hmem₁ : memFind m₁ a =
      some ⟨t, true, n :: (l.set iB.toNat w)⟩ := by
    have e : (n :: l).set (iB.toNat + 1) w =
        n :: (l.set iB.toNat w) :=
      List.set_cons_succ
    rw [e] at hcells₁
    exact hcells₁
  have hs₁' : envLookup ρ₁ "s" = some (.u64 sB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("s" : String) ≠ "v" by decide) hu₁]
    exact hs₁
  have ht₁ : envLookup ρ₁ "t" = some (.i32 x) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("t" : String) ≠ "v" by decide) hu₁]
    exact ht
  have hiB₁ : envLookup ρ₁ "i" = some (.u64 iB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "v" by decide) hu₁]
    exact hi₁
  have hpiv₂ : envLookup ρ₁ "pivot" = some (.i32 pivot) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("pivot" : String) ≠ "v" by decide) hu₁]
    exact hpiv₁
  have hsVar₂ : evalExpr (.var "s") ρ₁ = .ok (.u64 sB) :=
    evalExpr_var_hit _ _ _ hs₁'
  have hsVarM₂ : memEvalExpr (.var "s") ρ₁ m₁ π =
      .ok (.u64 sB) :=
    (memEvalExpr_var _ _ _ _).trans hsVar₂
  have htVar₂ : evalExpr (.var "t") ρ₁ = .ok (.i32 x) :=
    evalExpr_var_hit _ _ _ ht₁
  have htVarM₂ : memEvalExpr (.var "t") ρ₁ m₁ π =
      .ok (.i32 x) :=
    (memEvalExpr_var _ _ _ _).trans htVar₂
  have hgetS₁ : (l.set iB.toNat w)[sB.toNat]? = some w := by
    rw [hiN, hsN]
    by_cases hsi : s = i
    · rw [hsi]; exact List.getElem?_set_self hilt
    · rw [List.getElem?_set_ne (show i ≠ s by omega)]
      exact hw
  have hout₁ : envLookup ρ₁ "v" =
      some (.stdVecVal (l.set iB.toNat w)) :=
    envLookup_update_hit _ _ _ _ hu₁
  have hmemS₁ : memLoad m₁ a t (sB.toNat + 1) = .ok w :=
    memLoad_cellsAt m₁ a t (sB.toNat + 1)
      (n :: (l.set iB.toNat w)) w hmem₁
      (by rw [List.getElem?_cons_succ]; exact hgetS₁)
  have hatS₂ : evalExpr (.stdVecAt "v" (.var "s")) ρ₁ =
      .ok (.i32 w) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hout₁ hsVar₂ hgetS₁
  have hatS₂_ag : memEvalExpr (.stdVecAt "v" (.var "s")) ρ₁ m₁ π =
      evalExpr (.stdVecAt "v" (.var "s")) ρ₁ :=
    memEvalExpr_stdVecAt_hit "v" (.var "s") ρ₁ m₁ π
      (l.set iB.toNat w) sB w a t hlay hout₁
      (memEvalExpr_var _ _ _ _) hsVar₂ hmemS₁ hgetS₁
  have hatS₂M : memEvalExpr (.stdVecAt "v" (.var "s")) ρ₁ m₁ π =
      .ok (.i32 w) := by rw [hatS₂_ag]; exact hatS₂
  obtain ⟨ρ₂, hu₂⟩ := envUpdate_some_of_lookup ρ₁ "v"
    (.stdVecVal (l.set iB.toNat w))
    (.stdVecVal ((l.set iB.toNat w).set sB.toNat x)) hout₁
  have hlt₂ : sB.toNat + 1 < (n :: (l.set iB.toNat w)).length := by
    simp only [List.length_cons, List.length_set]
    omega
  obtain ⟨m₂, hmstore₂⟩ : ∃ m', memStore m₁ a t (sB.toNat + 1) x =
      .ok m' :=
    ⟨_, memStore_cellsAt m₁ a t (sB.toNat + 1)
      (n :: (l.set iB.toNat w)) x hmem₁ hlt₂⟩
  have hstep_set2 := memRevVecSet prog F "v" (.var "s") (.var "t")
    ρ₁ m₁ π sB x a t (l.set iB.toNat w) w m₂ ρ₂
    hsVarM₂ htVarM₂ hout₁ hlay hgetS₁ hmstore₂ hu₂
  have hcells₂ : cellsAt m₂ a t
      ((n :: (l.set iB.toNat w)).set (sB.toNat + 1) x) :=
    memFind_cellsAt_store m₁ a t (sB.toNat + 1)
      (n :: (l.set iB.toNat w)) x m₂ hmem₁ hlt₂ hmstore₂
  have hset : ((l.set iB.toNat w).set sB.toNat x) =
      ((l.set i w).set s x) := by rw [hiN, hsN]
  have hmem₂ : memFind m₂ a =
      some ⟨t, true, n :: ((l.set i w).set s x)⟩ := by
    have e : (n :: (l.set iB.toNat w)).set (sB.toNat + 1) x =
        n :: ((l.set iB.toNat w).set sB.toNat x) :=
      List.set_cons_succ
    rw [e, hset] at hcells₂
    exact hcells₂
  have hs₂ : envLookup ρ₂ "s" = some (.u64 sB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("s" : String) ≠ "v" by decide) hu₂]
    exact hs₁'
  have hi₂ : envLookup ρ₂ "i" = some (.u64 iB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "v" by decide) hu₂]
    exact hiB₁
  have hsVar₃ : evalExpr (.var "s") ρ₂ = .ok (.u64 sB) :=
    evalExpr_var_hit _ _ _ hs₂
  have hevS : evalExpr (.uadd (.var "s") (.lit (.u64 1))) ρ₂ =
      .ok (.u64 (sB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      hsVar₃ (by simp [evalExpr, litVal])
  have hevSM : memEvalExpr
      (.uadd (.var "s") (.lit (.u64 1))) ρ₂ m₂ π =
      .ok (.u64 (sB + 1)) :=
    (memEvalExpr_uadd_agree (.var "s") (.lit (.u64 1))
      ρ₂ m₂ π (memEvalExpr_var _ _ _ _)
      (memEvalExpr_lit _ _ _ _)).trans hevS
  obtain ⟨ρ₃, hu₃⟩ := envUpdate_some_of_lookup ρ₂ "s"
    (.u64 sB) (.u64 (sB + 1)) hs₂
  have hstep_s := memRevAssign prog F "s"
    (.uadd (.var "s") (.lit (.u64 1))) ρ₂ m₂ π (.u64 (sB + 1)) ρ₃
    hevSM hevS hu₃
  have hi₃ : envLookup ρ₃ "i" = some (.u64 iB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "s" by decide) hu₃]
    exact hi₂
  have hiVar₄ : evalExpr (.var "i") ρ₃ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi₃
  have hevI : evalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ₃ =
      .ok (.u64 (iB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      hiVar₄ (by simp [evalExpr, litVal])
  have hevIM : memEvalExpr
      (.uadd (.var "i") (.lit (.u64 1))) ρ₃ m₂ π =
      .ok (.u64 (iB + 1)) :=
    (memEvalExpr_uadd_agree (.var "i") (.lit (.u64 1))
      ρ₃ m₂ π (memEvalExpr_var _ _ _ _)
      (memEvalExpr_lit _ _ _ _)).trans hevI
  obtain ⟨ρ₄, hu₄⟩ := envUpdate_some_of_lookup ρ₃ "i"
    (.u64 iB) (.u64 (iB + 1)) hi₃
  have hpiv₃ : envLookup ρ₂ "pivot" = some (.i32 pivot) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("pivot" : String) ≠ "v" by decide) hu₂]
    exact hpiv₂
  have hpiv₄ : envLookup ρ₃ "pivot" = some (.i32 pivot) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("pivot" : String) ≠ "s" by decide) hu₃]
    exact hpiv₃
  have hpiv' : envLookup ρ₄ "pivot" = some (.i32 pivot) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("pivot" : String) ≠ "i" by decide) hu₄]
    exact hpiv₄
  have hstep_i := memRevAssign prog F "i"
    (.uadd (.var "i") (.lit (.u64 1))) ρ₃ m₂ π (.u64 (iB + 1)) ρ₄
    hevIM hevI hu₄
  have hout₄ : envLookup ρ₄ "v" =
      some (.stdVecVal ((l.set i w).set s x)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("v" : String) ≠ "i" by decide) hu₄]
    have : envLookup ρ₃ "v" =
        some (.stdVecVal ((l.set iB.toNat w).set sB.toNat x)) := by
      rw [envLookup_update_miss _ _ _ _ _
        (show ("v" : String) ≠ "s" by decide) hu₃]
      exact envLookup_update_hit _ _ _ _ hu₂
    rw [hset] at this
    exact this
  have hiN' : (iB + 1).toNat = i + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hiN]
    exact Nat.mod_eq_of_lt (by omega)
  have hsN' : (sB + 1).toNat = s + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hsN]
    exact Nat.mod_eq_of_lt (by omega)
  have hi' : envLookup ρ₄ "i" = some (.u64 (iB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₄
  have hs₃ : envLookup ρ₃ "s" = some (.u64 (sB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₃
  have hs' : envLookup ρ₄ "s" = some (.u64 (sB + 1)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("s" : String) ≠ "i" by decide) hu₄]
    exact hs₃
  have hthen : memEvalProgStmt prog F
      (.seq (.let_ "t" (.i 32) (.stdVecAt "v" (.var "i")))
        (.seq (.vecSet "v" (.var "i") (.stdVecAt "v" (.var "s")))
          (.seq (.vecSet "v" (.var "s") (.var "t"))
            (.assign "s" (.uadd (.var "s") (.lit (.u64 1)))))))
      ρ m π = .ok ((ρ₃, m₂, π), .fellThrough) := by
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hlet,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep_set1,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep_set2,
      hstep_s]
  have hif : memEvalProgStmt prog F
      (.if_ (.slt (.stdVecAt "v" (.var "i")) (.var "pivot"))
        (.seq (.let_ "t" (.i 32) (.stdVecAt "v" (.var "i")))
          (.seq (.vecSet "v" (.var "i") (.stdVecAt "v" (.var "s")))
            (.seq (.vecSet "v" (.var "s") (.var "t"))
              (.assign "s" (.uadd (.var "s") (.lit (.u64 1)))))))
        .skip) ρ m π = .ok ((ρ₃, m₂, π), .fellThrough) :=
    (memEvalProgStmt_if_true prog F _ _ _ _ _ _ hsltM).trans hthen
  have hbody : vecPartitionBody =
      (.seq (.if_ (.slt (.stdVecAt "v" (.var "i")) (.var "pivot"))
        (.seq (.let_ "t" (.i 32) (.stdVecAt "v" (.var "i")))
          (.seq (.vecSet "v" (.var "i") (.stdVecAt "v" (.var "s")))
            (.seq (.vecSet "v" (.var "s") (.var "t"))
              (.assign "s" (.uadd (.var "s") (.lit (.u64 1)))))))
        .skip)
        (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))) := rfl
  have heval : memEvalProgStmt prog F vecPartitionBody ρ m π =
      .ok ((ρ₄, m₂, π), .fellThrough) := by
    rw [hbody,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hif,
      hstep_i]
  exact ⟨ρ₄, m₂, heval, hout₄, ⟨(iB + 1), hi', hiN'⟩,
    ⟨(sB + 1), hs', hsN'⟩, hpiv', hmem₂⟩

/-- One body iteration on memory, skip branch: the pivot test fails,
    the state (env and memory) threads untouched, only `i` advances. -/
theorem memPartitionBody_skip (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (l : List (BitVec 32)) (pivot : BitVec 32)
    (i s : Nat) (iB sB : BitVec 64) (x : BitVec 32)
    (a t : Nat) (n : BitVec 32)
    (hlay : layoutLookup π "v" = some (a, t))
    (hmem : memFind m a = some ⟨t, true, n :: l⟩)
    (hn : n = BitVec.ofNat 32 l.length)
    (hiN : iB.toNat = i) (hsN : sB.toNat = s)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hpiv : envLookup ρ "pivot" = some (.i32 pivot))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hs : envLookup ρ "s" = some (.u64 sB))
    (hilt : i < l.length)
    (hx : l[i]? = some x)
    (hskip : (x.slt pivot) = false) :
    ∃ ρ', memEvalProgStmt prog F vecPartitionBody ρ m π =
      .ok ((ρ', m, π), .fellThrough) ∧
      envLookup ρ' "v" = some (.stdVecVal l) ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = i + 1) ∧
      (∃ sB', envLookup ρ' "s" = some (.u64 sB') ∧ sB'.toNat = s) ∧
      envLookup ρ' "pivot" = some (.i32 pivot) ∧
      memFind m a = some ⟨t, true, n :: l⟩ := by
  have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have hiVarA : memEvalExpr (.var "i") ρ m π =
      evalExpr (.var "i") ρ :=
    memEvalExpr_var _ _ _ _
  have hiVarM : memEvalExpr (.var "i") ρ m π = .ok (.u64 iB) :=
    hiVarA.trans hiVar
  have hvLen : evalExpr (.stdVecLen "v") ρ =
      .ok (.u64 (BitVec.ofNat 64 l.length)) :=
    evalExpr_stdVecLen_some _ _ _ hv
  have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
  have hmemLen : memLoad m a t 0 =
      .ok (BitVec.ofNat 32 l.length) := by
    rw [← hn]
    exact memLoad_cellsAt m a t 0 (n :: l) n hmem (by simp)
  have hoLenM : memEvalExpr (.stdVecLen "v") ρ m π =
      evalExpr (.stdVecLen "v") ρ :=
    memEvalExpr_stdVecLen_hit "v" ρ m π l a t hlay hv hmemLen
  have hguardT : evalExpr (.ult (.var "i") (.stdVecLen "v")) ρ =
      .ok (.b true) := by
    have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "v") ρ iB
      (BitVec.ofNat 64 l.length) hiVar hvLen
    have htb : (iB.ult (BitVec.ofNat 64 l.length)) = true := by
      rw [BitVec.ult_eq_decide]
      exact decide_eq_true (by omega)
    rwa [htb] at hult
  have hagT : memEvalExpr (.ult (.var "i") (.stdVecLen "v")) ρ m π =
      .ok (.b true) :=
    (memEvalExpr_ult_agree (.var "i") (.stdVecLen "v")
      ρ m π hiVarA hoLenM).trans hguardT
  have hgetB : l[iB.toNat]? = some x := by rw [hiN]; exact hx
  have hmemA : memLoad m a t (iB.toNat + 1) = .ok x :=
    memLoad_cellsAt m a t (iB.toNat + 1) (n :: l) x
      hmem (by rw [List.getElem?_cons_succ]; exact hgetB)
  have hat : evalExpr (.stdVecAt "v" (.var "i")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hiVar hgetB
  have hatM_ag : memEvalExpr (.stdVecAt "v" (.var "i")) ρ m π =
      evalExpr (.stdVecAt "v" (.var "i")) ρ :=
    memEvalExpr_stdVecAt_hit "v" (.var "i") ρ m π l iB x a t
      hlay hv hiVarA hiVar hmemA hgetB
  have hpivV : evalExpr (.var "pivot") ρ = .ok (.i32 pivot) :=
    evalExpr_var_hit _ _ _ hpiv
  have hpivA : memEvalExpr (.var "pivot") ρ m π =
      evalExpr (.var "pivot") ρ :=
    memEvalExpr_var _ _ _ _
  have hsltV : evalExpr (.slt (.stdVecAt "v" (.var "i"))
      (.var "pivot")) ρ = .ok (.b false) := by
    have h := evalExpr_slt_i32 (.stdVecAt "v" (.var "i"))
      (.var "pivot") ρ x pivot hat hpivV
    rwa [hskip] at h
  have hsltM : memEvalExpr (.slt (.stdVecAt "v" (.var "i"))
      (.var "pivot")) ρ m π = .ok (.b false) :=
    (memEvalExpr_slt_agree (.stdVecAt "v" (.var "i"))
      (.var "pivot") ρ m π hatM_ag hpivA).trans hsltV
  have hskipV : memEvalProgStmt prog F .skip ρ m π =
      .ok ((ρ, m, π), .fellThrough) := by
    cases F <;> simp [memEvalProgStmt, memEvalStmtFuel,
      memEvalStmtZero, memEvalStmtWith]
  have hif : memEvalProgStmt prog F
      (.if_ (.slt (.stdVecAt "v" (.var "i")) (.var "pivot"))
        (.seq (.let_ "t" (.i 32) (.stdVecAt "v" (.var "i")))
          (.seq (.vecSet "v" (.var "i") (.stdVecAt "v" (.var "s")))
            (.seq (.vecSet "v" (.var "s") (.var "t"))
              (.assign "s" (.uadd (.var "s") (.lit (.u64 1)))))))
        .skip) ρ m π = .ok ((ρ, m, π), .fellThrough) :=
    (memEvalProgStmt_if_false prog F _ _ _ _ _ _ hsltM).trans hskipV
  have hevI : evalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ =
      .ok (.u64 (iB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      hiVar (by simp [evalExpr, litVal])
  have hevIM : memEvalExpr
      (.uadd (.var "i") (.lit (.u64 1))) ρ m π =
      .ok (.u64 (iB + 1)) :=
    (memEvalExpr_uadd_agree (.var "i") (.lit (.u64 1))
      ρ m π hiVarA (memEvalExpr_lit _ _ _ _)).trans hevI
  obtain ⟨ρ', hu⟩ := envUpdate_some_of_lookup ρ "i"
    (.u64 iB) (.u64 (iB + 1)) hi
  have hstep_i := memRevAssign prog F "i"
    (.uadd (.var "i") (.lit (.u64 1))) ρ m π (.u64 (iB + 1)) ρ'
    hevIM hevI hu
  have hout' : envLookup ρ' "v" = some (.stdVecVal l) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("v" : String) ≠ "i" by decide) hu]
    exact hv
  have hs' : envLookup ρ' "s" = some (.u64 sB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("s" : String) ≠ "i" by decide) hu]
    exact hs
  have hpiv' : envLookup ρ' "pivot" = some (.i32 pivot) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("pivot" : String) ≠ "i" by decide) hu]
    exact hpiv
  have hiN' : (iB + 1).toNat = i + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hiN]
    exact Nat.mod_eq_of_lt (by omega)
  have hi' : envLookup ρ' "i" = some (.u64 (iB + 1)) :=
    envLookup_update_hit _ _ _ _ hu
  have hbody : vecPartitionBody =
      (.seq (.if_ (.slt (.stdVecAt "v" (.var "i")) (.var "pivot"))
        (.seq (.let_ "t" (.i 32) (.stdVecAt "v" (.var "i")))
          (.seq (.vecSet "v" (.var "i") (.stdVecAt "v" (.var "s")))
            (.seq (.vecSet "v" (.var "s") (.var "t"))
              (.assign "s" (.uadd (.var "s") (.lit (.u64 1)))))))
        .skip)
        (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))) := rfl
  have heval : memEvalProgStmt prog F vecPartitionBody ρ m π =
      .ok ((ρ', m, π), .fellThrough) := by
    rw [hbody,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hif,
      hstep_i]
  exact ⟨ρ', heval, hout', ⟨(iB + 1), hi', hiN'⟩,
    ⟨sB, hs', hsN⟩, hpiv', hmem⟩

/-! ## Memory loop induction -/

/-- Memory loop, ok leg: the scan runs to `l.length`, the block holds
    the forward-model words (fuel induction threading the memory body
    hits; the forward equation unfolds one step per iteration). -/
theorem memPartitionLoop_ok (prog : Prog) (F G : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (l : List (BitVec 32)) (pivot : BitVec 32)
    (i s : Nat) (iB sB : BitVec 64)
    (l' : List (BitVec 32)) (i' s' : Nat)
    (a t : Nat) (n : BitVec 32)
    (hlay : layoutLookup π "v" = some (a, t))
    (hn : n = BitVec.ofNat 32 l.length)
    (hiN : iB.toNat = i) (hsN : sB.toNat = s)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hpiv : envLookup ρ "pivot" = some (.i32 pivot))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hs : envLookup ρ "s" = some (.u64 sB))
    (hmem : memFind m a = some ⟨t, true, n :: l⟩)
    (hle : i ≤ l.length) (hsle : s ≤ i)
    (hF : l.length - i ≤ F) (hG : l.length - i ≤ G)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (hfwd : partitionFwd pivot l G i s = .ok (i', s', l')) :
    ∃ ρ' m', memEvalProgStmt prog F vecPartitionLoop ρ m π =
      .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "v" = some (.stdVecVal l') ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = i') ∧
      (∃ sB', envLookup ρ' "s" = some (.u64 sB') ∧ sB'.toNat = s') ∧
      envLookup ρ' "pivot" = some (.i32 pivot) ∧
      memFind m' a = some ⟨t, true, n :: l'⟩ := by
  induction F generalizing G ρ m l i s iB sB with
  | zero =>
    have him : i = l.length := by omega
    have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
    have hmemLen : memLoad m a t 0 =
        .ok (BitVec.ofNat 32 l.length) := by
      rw [← hn]
      exact memLoad_cellsAt m a t 0 (n :: l) n hmem (by simp)
    have hguardF : memEvalExpr
        (.ult (.var "i") (.stdVecLen "v")) ρ m π =
        .ok (.b false) := by
      have hag : memEvalExpr (.ult (.var "i") (.stdVecLen "v")) ρ m π =
          evalExpr (.ult (.var "i") (.stdVecLen "v")) ρ :=
        memEvalExpr_ult_agree (.var "i") (.stdVecLen "v") ρ m π
          (memEvalExpr_var _ _ _ _)
          (memEvalExpr_stdVecLen_hit "v" ρ m π l a t
            hlay hv hmemLen)
      have hval : evalExpr (.ult (.var "i") (.stdVecLen "v")) ρ =
          .ok (.b false) := by
        have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "v")
          ρ iB (BitVec.ofNat 64 l.length)
          (evalExpr_var_hit _ _ _ hi)
          (evalExpr_stdVecLen_some _ _ _ hv)
        have hfb : (iB.ult (BitVec.ofNat 64 l.length)) = false := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_false (by omega)
        rwa [hfb] at hult
      rw [hag]; exact hval
    have hexit : memEvalProgStmt prog 0 vecPartitionLoop ρ m π =
        .ok ((ρ, m, π), .fellThrough) :=
      memEvalProgStmt_while_false prog 0 _ _ _ _ _ hguardF
    have hpair : (i, s, l) = (i', s', l') := by
      cases G with
      | zero => simpa [partitionFwd] using hfwd
      | succ G =>
        have hneg : ¬ i < l.length := by omega
        simpa [partitionFwd, dite_eq_right hneg] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    exact ⟨ρ, m, hexit, hv, ⟨iB, hi, hiN⟩, ⟨sB, hs, hsN⟩, hpiv,
      hmem⟩
  | succ F ih =>
    by_cases hlt : i < l.length
    · have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
      have hmemLen : memLoad m a t 0 =
          .ok (BitVec.ofNat 32 l.length) := by
        rw [← hn]
        exact memLoad_cellsAt m a t 0 (n :: l) n hmem (by simp)
      have hguardT : memEvalExpr
          (.ult (.var "i") (.stdVecLen "v")) ρ m π =
          .ok (.b true) := by
        have hag : memEvalExpr
            (.ult (.var "i") (.stdVecLen "v")) ρ m π =
            evalExpr (.ult (.var "i") (.stdVecLen "v")) ρ :=
          memEvalExpr_ult_agree (.var "i") (.stdVecLen "v") ρ m π
            (memEvalExpr_var _ _ _ _)
            (memEvalExpr_stdVecLen_hit "v" ρ m π l a t
              hlay hv hmemLen)
        have hval : evalExpr (.ult (.var "i") (.stdVecLen "v")) ρ =
            .ok (.b true) := by
          have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "v")
            ρ iB (BitVec.ofNat 64 l.length)
            (evalExpr_var_hit _ _ _ hi)
            (evalExpr_stdVecLen_some _ _ _ hv)
          have htb : (iB.ult (BitVec.ofNat 64 l.length)) = true := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_true (by omega)
          rwa [htb] at hult
        rw [hag]; exact hval
      obtain ⟨x, hx⟩ := hread i hlt
      have hslt : s < l.length := by omega
      obtain ⟨w, hw⟩ := hread s hslt
      cir_fuel_step (F, G, l.length - (i + 1))
      by_cases htake : (x.slt pivot) = true
      · have hle' : i + 1 ≤ ((l.set i w).set s x).length := by
          have : ((l.set i w).set s x).length = l.length := by
            simp [List.length_set]
          omega
        have hsle' : s + 1 ≤ i + 1 := by omega
        have hread' : ∀ p, p < ((l.set i w).set s x).length →
            ∃ y, ((l.set i w).set s x)[p]? = some y := by
          intro p hp
          have hplen : p < l.length := by
            have : ((l.set i w).set s x).length = l.length := by
              simp [List.length_set]
            omega
          by_cases hpi : p = i
          · rw [hpi]
            by_cases hsi : s = i
            · rw [hsi]
              exact ⟨x, List.getElem?_set_self (by
                rw [List.length_set]; exact hlt)⟩
            · exact ⟨w, by
                rw [List.getElem?_set_ne (show s ≠ i by omega)]
                exact List.getElem?_set_self hlt⟩
          · by_cases hps : p = s
            · rw [hps]
              exact ⟨x, List.getElem?_set_self (by
                rw [List.length_set]; exact hslt)⟩
            · obtain ⟨y, hy⟩ := hread p hplen
              exact ⟨y, by
                rw [List.getElem?_set_ne (show s ≠ p by omega),
                  List.getElem?_set_ne (show i ≠ p by omega)]
                exact hy⟩
        obtain ⟨ρ₁, m₁, hbody, hout₁, ⟨iB₁, hiB₁, hiN₁⟩,
            ⟨sB₁, hsB₁, hsN₁⟩, hpiv₁, hmem₁⟩ :=
          memPartitionBody_take prog F ρ m π l pivot i s iB sB x w
            a t n hlay hmem hn hiN hsN hl64 hv hpiv hi hs
            hlt hx hw hslt htake
        have hlen : ((l.set i w).set s x).length = l.length := by
          simp [List.length_set]
        have hlo64' : ((l.set i w).set s x).length < 2 ^ 64 := by
          rw [hlen]; exact hl64
        have hn' : n = BitVec.ofNat 32 ((l.set i w).set s x).length := by
          rw [hlen]; exact hn
        have hF'' : ((l.set i w).set s x).length - (i + 1) ≤ F := by
          omega
        have hG'' : ((l.set i w).set s x).length - (i + 1) ≤ G' := by
          omega
        have hfwd' : partitionFwd pivot ((l.set i w).set s x) G'
            (i + 1) (s + 1) = .ok (i', s', l') := by
          have h := hfwd
          simp only [partitionFwd, dite_eq_left hlt, hx, htake, hw] at h
          exact h
        obtain ⟨ρ', m', hloop, hout', ⟨iB', hiB', hiN'⟩,
            ⟨sB', hsB', hsN'⟩, hpiv', hmem'⟩ :=
          ih (G := G') (ρ := ρ₁) (m := m₁) (l := (l.set i w).set s x)
            (i := i + 1) (s := s + 1) (iB := iB₁) (sB := sB₁)
            (hl64 := hlo64') (hn := hn')
            (hiN := hiN₁) (hsN := hsN₁)
            (hv := hout₁) (hpiv := hpiv₁) (hi := hiB₁) (hs := hsB₁)
            (hmem := hmem₁)
            (hle := hle') (hsle := hsle')
            (hF := hF'') (hG := hG'')
            (hread := hread') (hfwd := hfwd')
        refine ⟨ρ', m', ?_, hout', ⟨iB', hiB', hiN'⟩,
          ⟨sB', hsB', hsN'⟩, hpiv', hmem'⟩
        have hwhile : memEvalProgStmt prog (F + 1) vecPartitionLoop
            ρ m π =
            memEvalProgStmt prog F vecPartitionLoop ρ₁ m₁ π := by
          cir_unfold_prog (vecPartitionLoop, prog, F, hguardT, hbody)
        rw [hwhile]
        exact hloop
      · have hskip : (x.slt pivot) = false := by
          cases h : x.slt pivot with
          | true => exact absurd h htake
          | false => rfl
        obtain ⟨ρ₁, hbody, hout₁, ⟨iB₁, hiB₁, hiN₁⟩,
            ⟨sB₁, hsB₁, hsN₁⟩, hpiv₁, hmem₁⟩ :=
          memPartitionBody_skip prog F ρ m π l pivot i s iB sB x
            a t n hlay hmem hn hiN hsN hl64 hv hpiv hi hs
            hlt hx hskip
        have hsle' : s ≤ i + 1 := by omega
        have hfwd' : partitionFwd pivot l G' (i + 1) s =
            .ok (i', s', l') := by
          have h := hfwd
          simp only [partitionFwd, dite_eq_left hlt, hx, hskip] at h
          exact h
        obtain ⟨ρ', m', hloop, hout', ⟨iB', hiB', hiN'⟩,
            ⟨sB', hsB', hsN'⟩, hpiv', hmem'⟩ :=
          ih (G := G') (ρ := ρ₁) (m := m) (l := l)
            (i := i + 1) (s := s) (iB := iB₁) (sB := sB₁)
            (hl64 := hl64) (hn := hn)
            (hiN := hiN₁) (hsN := hsN₁)
            (hv := hout₁) (hpiv := hpiv₁) (hi := hiB₁) (hs := hsB₁)
            (hmem := hmem₁)
            (hle := by omega) (hsle := hsle')
            (hF := hF') (hG := hG')
            (hread := hread) (hfwd := hfwd')
        refine ⟨ρ', m', ?_, hout', ⟨iB', hiB', hiN'⟩,
          ⟨sB', hsB', hsN'⟩, hpiv', hmem'⟩
        have hwhile : memEvalProgStmt prog (F + 1) vecPartitionLoop
            ρ m π =
            memEvalProgStmt prog F vecPartitionLoop ρ₁ m π := by
          cir_unfold_prog (vecPartitionLoop, prog, F, hguardT, hbody)
        rw [hwhile]
        exact hloop
    · have him : i = l.length := by omega
      subst him
      have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
      have hmemLen : memLoad m a t 0 =
          .ok (BitVec.ofNat 32 l.length) := by
        rw [← hn]
        exact memLoad_cellsAt m a t 0 (n :: l) n hmem (by simp)
      have hguardF : memEvalExpr
          (.ult (.var "i") (.stdVecLen "v")) ρ m π =
          .ok (.b false) := by
        have hag : memEvalExpr
            (.ult (.var "i") (.stdVecLen "v")) ρ m π =
            evalExpr (.ult (.var "i") (.stdVecLen "v")) ρ :=
          memEvalExpr_ult_agree (.var "i") (.stdVecLen "v") ρ m π
            (memEvalExpr_var _ _ _ _)
            (memEvalExpr_stdVecLen_hit "v" ρ m π l a t
              hlay hv hmemLen)
        have hval : evalExpr (.ult (.var "i") (.stdVecLen "v")) ρ =
            .ok (.b false) := by
          have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "v")
            ρ iB (BitVec.ofNat 64 l.length)
            (evalExpr_var_hit _ _ _ hi)
            (evalExpr_stdVecLen_some _ _ _ hv)
          have hfb : (iB.ult (BitVec.ofNat 64 l.length)) = false := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_false (by omega)
          rwa [hfb] at hult
        rw [hag]; exact hval
      have hexit : memEvalProgStmt prog (F + 1) vecPartitionLoop
          ρ m π =
          .ok ((ρ, m, π), .fellThrough) :=
        memEvalProgStmt_while_false prog (F + 1) _ _ _ _ _ hguardF
      have hpair : (l.length, s, l) = (i', s', l') := by
        cases G with
        | zero => simpa [partitionFwd] using hfwd
        | succ G =>
          have hneg : ¬ l.length < l.length := by omega
          simpa [partitionFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      exact ⟨ρ, m, hexit, hv, ⟨iB, hi, hiN⟩, ⟨sB, hs, hsN⟩, hpiv,
        hmem⟩

/-! ## Entries and transfer -/

/-- Value entry: the `s`/`i` prelude runs, the loop closes against the
    forward model, the updated words return. -/
theorem evalProgFunc_vecPartition_ok (F : Nat)
    (l l' : List (BitVec 32)) (pivot : BitVec 32) (s' : Nat)
    (hl64 : l.length < 2 ^ 64)
    (hF : l.length ≤ F)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (hfwd : partitionFwd pivot l l.length 0 0 =
      .ok (l.length, s', l')) :
    evalProgFunc vecPartitionProg F vecPartitionFunc
      [.stdVecVal l, .i32 pivot] =
      .ok (.stdVecVal l') := by
  have hbind : bindArgs vecPartitionFunc.args
      [.stdVecVal l, .i32 pivot] =
      some [("v", .stdVecVal l), ("pivot", .i32 pivot)] := rfl
  have hbody : vecPartitionFunc.body =
      (.seq (.let_ "s" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq vecPartitionLoop
            (.return_ (.var "v"))))) := rfl
  have hlit : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("v", .stdVecVal l), ("pivot", .i32 pivot)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletS := revLet vecPartitionProg F "s" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("v", .stdVecVal l), ("pivot", .i32 pivot)]
    (.u64 (BitVec.ofNat 64 0)) hlit
  have hlitI : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("v", .stdVecVal l), ("pivot", .i32 pivot)]
        "s" (.u64 (BitVec.ofNat 64 0))) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletI := revLet vecPartitionProg F "i" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (envExtend [("v", .stdVecVal l), ("pivot", .i32 pivot)]
      "s" (.u64 (BitVec.ofNat 64 0)))
    (.u64 (BitVec.ofNat 64 0)) hlitI
  have hiN : (BitVec.ofNat 64 0).toNat = 0 := by
    simp [BitVec.toNat_ofNat]
  have hv₁ : envLookup (envExtend (envExtend
      [("v", .stdVecVal l), ("pivot", .i32 pivot)]
      "s" (.u64 (BitVec.ofNat 64 0)))
      "i" (.u64 (BitVec.ofNat 64 0))) "v" =
      some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "i" by decide),
      envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "s" by decide)]
    simp [envLookup]
  have hpiv₁ : envLookup (envExtend (envExtend
      [("v", .stdVecVal l), ("pivot", .i32 pivot)]
      "s" (.u64 (BitVec.ofNat 64 0)))
      "i" (.u64 (BitVec.ofNat 64 0))) "pivot" =
      some (.i32 pivot) := by
    rw [envExtend_miss _ _ _ _
      (show ("pivot" : String) ≠ "i" by decide),
      envExtend_miss _ _ _ _
      (show ("pivot" : String) ≠ "s" by decide)]
    simp [envLookup]
  have hs₁ : envLookup (envExtend (envExtend
      [("v", .stdVecVal l), ("pivot", .i32 pivot)]
      "s" (.u64 (BitVec.ofNat 64 0)))
      "i" (.u64 (BitVec.ofNat 64 0))) "s" =
      some (.u64 (BitVec.ofNat 64 0)) := by
    rw [envExtend_miss _ _ _ _
      (show ("s" : String) ≠ "i" by decide)]
    exact envExtend_hit _ _ _
  have hi₁ : envLookup (envExtend (envExtend
      [("v", .stdVecVal l), ("pivot", .i32 pivot)]
      "s" (.u64 (BitVec.ofNat 64 0)))
      "i" (.u64 (BitVec.ofNat 64 0))) "i" =
      some (.u64 (BitVec.ofNat 64 0)) :=
    envExtend_hit _ _ _
  obtain ⟨ρ', hloop, hout', ⟨iB', hiB', hiN'⟩,
      ⟨sB', hsB', hsN'⟩⟩ :=
    valPartitionLoop_ok vecPartitionProg F l.length
      (envExtend (envExtend [("v", .stdVecVal l),
        ("pivot", .i32 pivot)]
        "s" (.u64 (BitVec.ofNat 64 0)))
        "i" (.u64 (BitVec.ofNat 64 0)))
      l pivot 0 0 (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
      l' l.length s'
      hiN hiN hl64 hv₁ hpiv₁ hi₁ hs₁ (Nat.zero_le _)
      (Nat.le_refl _) (by omega) (by omega) hread hfwd
  have hret := evalProgStmt_return vecPartitionProg F
    (.var "v") ρ' (.stdVecVal l')
    (evalExpr_var_hit _ _ _ hout')
  simp only [evalProgFunc, hbind, hbody]
  rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletS,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletI,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hloop,
    hret]

/-- Memory entry: the `s`/`i` prelude runs on memory, the loop closes
    against the forward model, the updated words return. -/
theorem memEvalProgFunc_vecPartition_ok (F : Nat)
    (l l' : List (BitVec 32)) (pivot : BitVec 32) (s' : Nat)
    (hl64 : l.length < 2 ^ 64)
    (hF : l.length ≤ F)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (hfwd : partitionFwd pivot l l.length 0 0 =
      .ok (l.length, s', l')) :
    memEvalProgFunc vecPartitionProg F vecPartitionFunc
      [.stdVecVal l, .i32 pivot] =
      .ok (.stdVecVal l') := by
  have hbind := bindMemArgs_vecPartition l pivot
  have hbody : vecPartitionFunc.body =
      (.seq (.let_ "s" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq vecPartitionLoop
            (.return_ (.var "v"))))) := rfl
  have hmem : memFind
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ 0 =
      some ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩ :=
    memFind_cons_hit _ _ _ _ _
  have hlay : layoutLookup [("v", 0, 0)] "v" =
      some (0, 0) := by simp [layoutLookup]
  have hlitM : memEvalExpr
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("v", .stdVecVal l), ("pivot", .i32 pivot)]
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("v", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("v", .stdVecVal l), ("pivot", .i32 pivot)] :=
    memEvalExpr_lit _ _ _ _
  have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("v", .stdVecVal l), ("pivot", .i32 pivot)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletS := memRevLet vecPartitionProg F "s" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("v", .stdVecVal l), ("pivot", .i32 pivot)]
    ⟨1, [(0, ⟨0, true,
      (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
    [("v", 0, 0)] (.u64 (BitVec.ofNat 64 0))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) hlitM hlitV
  have hlitIM : memEvalExpr
      (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("v", .stdVecVal l), ("pivot", .i32 pivot)]
        "s" (.u64 (BitVec.ofNat 64 0)))
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("v", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend [("v", .stdVecVal l), ("pivot", .i32 pivot)]
          "s" (.u64 (BitVec.ofNat 64 0))) :=
    memEvalExpr_lit _ _ _ _
  have hlitIV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("v", .stdVecVal l), ("pivot", .i32 pivot)]
        "s" (.u64 (BitVec.ofNat 64 0))) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletI := memRevLet vecPartitionProg F "i" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (envExtend [("v", .stdVecVal l), ("pivot", .i32 pivot)]
      "s" (.u64 (BitVec.ofNat 64 0)))
    ⟨1, [(0, ⟨0, true,
      (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
    [("v", 0, 0)] (.u64 (BitVec.ofNat 64 0))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) hlitIM hlitIV
  have hiN : (BitVec.ofNat 64 0).toNat = 0 := by
    simp [BitVec.toNat_ofNat]
  have hv₁ : envLookup (envExtend (envExtend
      [("v", .stdVecVal l), ("pivot", .i32 pivot)]
      "s" (.u64 (BitVec.ofNat 64 0)))
      "i" (.u64 (BitVec.ofNat 64 0))) "v" =
      some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "i" by decide),
      envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "s" by decide)]
    simp [envLookup]
  have hpiv₁ : envLookup (envExtend (envExtend
      [("v", .stdVecVal l), ("pivot", .i32 pivot)]
      "s" (.u64 (BitVec.ofNat 64 0)))
      "i" (.u64 (BitVec.ofNat 64 0))) "pivot" =
      some (.i32 pivot) := by
    rw [envExtend_miss _ _ _ _
      (show ("pivot" : String) ≠ "i" by decide),
      envExtend_miss _ _ _ _
      (show ("pivot" : String) ≠ "s" by decide)]
    simp [envLookup]
  have hs₁ : envLookup (envExtend (envExtend
      [("v", .stdVecVal l), ("pivot", .i32 pivot)]
      "s" (.u64 (BitVec.ofNat 64 0)))
      "i" (.u64 (BitVec.ofNat 64 0))) "s" =
      some (.u64 (BitVec.ofNat 64 0)) := by
    rw [envExtend_miss _ _ _ _
      (show ("s" : String) ≠ "i" by decide)]
    exact envExtend_hit _ _ _
  have hi₁ : envLookup (envExtend (envExtend
      [("v", .stdVecVal l), ("pivot", .i32 pivot)]
      "s" (.u64 (BitVec.ofNat 64 0)))
      "i" (.u64 (BitVec.ofNat 64 0))) "i" =
      some (.u64 (BitVec.ofNat 64 0)) :=
    envExtend_hit _ _ _
  obtain ⟨ρ', m', hloop, hout', ⟨iB', hiB', hiN'⟩,
      ⟨sB', hsB', hsN'⟩, hpiv', hmem'⟩ :=
    memPartitionLoop_ok vecPartitionProg F l.length
      (envExtend (envExtend [("v", .stdVecVal l),
        ("pivot", .i32 pivot)]
        "s" (.u64 (BitVec.ofNat 64 0)))
        "i" (.u64 (BitVec.ofNat 64 0)))
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("v", 0, 0)]
      l pivot 0 0 (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
      l' l.length s' 0 0 _ rfl rfl
      hiN hiN hl64 hv₁ hpiv₁ hi₁ hs₁ hmem
      (Nat.zero_le _) (Nat.le_refl _)
      (by omega) (by omega) hread hfwd
  have hret := memEvalProgStmt_return vecPartitionProg F
    (.var "v") ρ' m' [("v", 0, 0)]
    (.stdVecVal l')
    ((memEvalExpr_var _ _ _ _).trans
      (evalExpr_var_hit _ _ _ hout'))
  simp only [memEvalProgFunc, hbind, hbody]
  rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletS,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletI,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hloop,
    hret]

/-- Transfer for `vec_partition`: memory evaluation agrees with value
    evaluation (single ok leg — the kernel is total). -/
theorem memTransferProg_vecPartition_ok (F : Nat)
    (l : List (BitVec 32)) (pivot : BitVec 32)
    (hl64 : l.length < 2 ^ 64)
    (hF : l.length ≤ F)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (_h : oracleNoalias vecPartitionFunc
      [.stdVecVal l, .i32 pivot]) :
    memEvalProgFunc vecPartitionProg F vecPartitionFunc
      [.stdVecVal l, .i32 pivot] =
      evalProgFunc vecPartitionProg F vecPartitionFunc
        [.stdVecVal l, .i32 pivot] := by
  obtain ⟨s', l', heq⟩ :=
    partitionFwd_ok pivot l l.length 0 0 (Nat.zero_le _)
      (Nat.le_refl _) (by omega) hread
  rw [memEvalProgFunc_vecPartition_ok F l l' pivot s' hl64 hF
    hread heq,
    evalProgFunc_vecPartition_ok F l l' pivot s' hl64 hF hread heq]

/-- Closing partition contract (M6c): the kernel returns a
    permutation of the input satisfying the partition boundary —
    everything below `s'` tests `slt`-true, everything at/above
    tests `slt`-false. Pure lemmas closed at eval. -/
theorem evalProgFunc_vecPartition_spec (F : Nat)
    (l : List (BitVec 32)) (pivot : BitVec 32)
    (hl64 : l.length < 2 ^ 64)
    (hF : l.length ≤ F)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x) :
    ∃ l' s', evalProgFunc vecPartitionProg F vecPartitionFunc
      [.stdVecVal l, .i32 pivot] = .ok (.stdVecVal l') ∧
      List.Perm l' l ∧ PartitionedAt l' s' pivot := by
  obtain ⟨s', l', heq⟩ := partitionFwd_ok pivot l l.length 0 0
    (Nat.zero_le _) (Nat.le_refl _) (by omega) hread
  have hpref0 : ∀ j, j < 0 → ∀ x, l[j]? = some x →
      (x.slt pivot) = true := by
    intro j hj
    exact False.elim (by omega)
  have hsuff0 : ∀ j, 0 ≤ j → j < 0 → ∀ x, l[j]? = some x →
      (x.slt pivot) = false := by
    intro j hsj hj
    exact False.elim (by omega)
  have hperm := partitionFwd_perm pivot l.length 0 0 l l' _ _
    (Nat.zero_le _) heq
  have hpart := partitionFwd_partitioned pivot l.length 0 0 l l' _ _
    (Nat.zero_le _) (Nat.zero_le _) (by omega) hpref0 hsuff0 heq
  exact ⟨l', s', evalProgFunc_vecPartition_ok F l l' pivot s' hl64
    hF hread heq, hperm, hpart⟩
