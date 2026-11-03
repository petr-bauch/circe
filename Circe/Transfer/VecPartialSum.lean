/-
Circe.Transfer.VecPartialSum — mem transfer for prefix-sum scan
(`vec_partial_sum`, the in-place `std::partial_sum` idiom; P2-M10).

Mirrors the value loop (`valPartialSumBody_ok/_overflow`,
`valPartialSumLoop_ok/_overflow` in `Circe.Emit.VecPartialSum`) step
for step on the memory layer: the single `mutBorrow` block pins the
reified snapshot (`cellsAt` framed by find; the length word shifts
offsets by one), the prefix-sum store threads through `memStore` in
lockstep on the same block, and the loop re-inducts over `(ρ, m, π)`
with the forward equation threading (two fuels: program fuel and
forward fuel). Both legs are proved: successful checked adds store the
running sum, while a failed checked add aborts the store loudly with
the same `Overflow`. Entries close against the forward contract; the
closing specs tie both outcomes to the independent checked scan.
-/
import Circe.Transfer.VecPartition
import Circe.Emit.VecPartialSum
import Circe.Specs

/-! ## Binding (closed form) -/

/-- Partial-sum binding pins one snapshot: the single `mutBorrow`
    vector at addr `0`. -/
theorem bindMemArgs_vecPartialSum (l : List (BitVec 32)) :
    bindMemArgs vecPartialSumFunc.args
      [.stdVecVal l] emptyMem =
      some ([("v", .stdVecVal l)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("v", 0, 0)]) := by
  rfl

/-- Partial-sum footprint is a single singleton. -/
theorem oracleNoalias_vecPartialSum (l : List (BitVec 32)) :
    oracleNoalias vecPartialSumFunc
      [.stdVecVal l] := by
  have hb := bindMemArgs_vecPartialSum l
  have hn : LayoutNoAlias [("v", 0, 0)] := by
    simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-! ## Memory body hit -/

/-- One body iteration on memory, success branch: the two reads agree
    with the value side (including the `i - 1` predecessor through
    the existing `usub` kit), the checked add succeeds, and the
    prefix-sum store prepends a shadowing snapshot block on the
    single `v` block. -/
theorem memPartialSumBody_ok (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (l : List (BitVec 32)) (i : Nat) (iB : BitVec 64)
    (cur prev sum : BitVec 32)
    (a t : Nat) (n : BitVec 32)
    (hlay : layoutLookup π "v" = some (a, t))
    (hmem : memFind m a = some ⟨t, true, n :: l⟩)
    (hn : n = BitVec.ofNat 32 l.length)
    (hiN : iB.toNat = i)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hilt : i < l.length) (hi1 : 1 ≤ i)
    (hgetC : l[i]? = some cur) (hgetP : l[i - 1]? = some prev)
    (hadd : checkedAddI32 cur prev = .ok sum) :
    ∃ ρ' m', memEvalProgStmt prog F vecPartialSumBody ρ m π =
      .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "v" = some (.stdVecVal (l.set i sum)) ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = i + 1) ∧
      memFind m' a = some ⟨t, true, n :: (l.set i sum)⟩ := by
  have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have hiVarA : memEvalExpr (.var "i") ρ m π =
      evalExpr (.var "i") ρ :=
    memEvalExpr_var _ _ _ _
  have hiVarM : memEvalExpr (.var "i") ρ m π = .ok (.u64 iB) :=
    hiVarA.trans hiVar
  have hsub : evalExpr (.usub (.var "i") (.lit (.u64 1))) ρ =
      .ok (.u64 (iB - 1)) :=
    evalExpr_u64_usub iB 1 (.var "i") ρ hiVar
  have hsubN : (iB - 1).toNat = i - 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    have hno : ¬ BitVec.usubOverflow iB 1 := by
      rw [BitVec.usubOverflow, decide_eq_true_eq, hiN, h1]
      omega
    rw [BitVec.toNat_sub_of_not_usubOverflow hno, hiN, h1]
  have hsubA : memEvalExpr (.usub (.var "i") (.lit (.u64 1))) ρ m π =
      evalExpr (.usub (.var "i") (.lit (.u64 1))) ρ :=
    memEvalExpr_usub_agree _ _ _ _ _
      (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)
  have hsubM : memEvalExpr (.usub (.var "i") (.lit (.u64 1))) ρ m π =
      .ok (.u64 (iB - 1)) := by
    rw [hsubA]; exact hsub
  have hgetI : l[iB.toNat]? = some cur := by rw [hiN]; exact hgetC
  have hgetIMinus : l[(iB - 1).toNat]? = some prev := by
    rw [hsubN]; exact hgetP
  have hatC : evalExpr (.stdVecAt "v" (.var "i")) ρ = .ok (.i32 cur) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hiVar hgetI
  have hatP : evalExpr
      (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 1))))
      ρ = .ok (.i32 prev) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hsub hgetIMinus
  have haddV : evalExpr
      (.add (.stdVecAt "v" (.var "i"))
        (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 1)))))
      ρ = .ok (.i32 sum) := by
    have e : evalExpr
        (.add (.stdVecAt "v" (.var "i"))
          (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 1)))))
        ρ = (checkedAddI32 cur prev).map .i32 := by
      unfold evalExpr
      rw [hatC, hatP]
    rw [e, hadd,
      show (Except.ok sum).map Value.i32 = Except.ok (Value.i32 sum) from rfl]
  have hmemLen : memLoad m a t 0 =
      .ok (BitVec.ofNat 32 l.length) := by
    rw [← hn]
    exact memLoad_cellsAt m a t 0 (n :: l) n hmem (by simp)
  have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
  have hoLenV : evalExpr (.stdVecLen "v") ρ =
      .ok (.u64 (BitVec.ofNat 64 l.length)) :=
    evalExpr_stdVecLen_some _ _ _ hv
  have hoLenM : memEvalExpr (.stdVecLen "v") ρ m π =
      evalExpr (.stdVecLen "v") ρ :=
    memEvalExpr_stdVecLen_hit "v" ρ m π l a t
      hlay hv hmemLen
  have hguardV : evalExpr (.ult (.var "i") (.stdVecLen "v")) ρ =
      .ok (.b true) := by
    have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "v") ρ iB
      (BitVec.ofNat 64 l.length) hiVar hoLenV
    have htb : (iB.ult (BitVec.ofNat 64 l.length)) = true := by
      rw [BitVec.ult_eq_decide]
      exact decide_eq_true (by omega)
    rwa [htb] at hult
  have hguardT : memEvalExpr (.ult (.var "i") (.stdVecLen "v")) ρ m π =
      .ok (.b true) :=
    (memEvalExpr_ult_agree (.var "i") (.stdVecLen "v")
      ρ m π hiVarA hoLenM).trans hguardV
  have hmemC : memLoad m a t (iB.toNat + 1) = .ok cur :=
    memLoad_cellsAt m a t (iB.toNat + 1) (n :: l) cur
      hmem (by rw [List.getElem?_cons_succ]; exact hgetI)
  have hatM_ag : memEvalExpr (.stdVecAt "v" (.var "i")) ρ m π =
      evalExpr (.stdVecAt "v" (.var "i")) ρ :=
    memEvalExpr_stdVecAt_hit "v" (.var "i") ρ m π l iB cur a t
      hlay hv hiVarA hiVar hmemC hgetI
  have hatM : memEvalExpr (.stdVecAt "v" (.var "i")) ρ m π =
      .ok (.i32 cur) := by rw [hatM_ag]; exact hatC
  have hmemP : memLoad m a t ((iB - 1).toNat + 1) = .ok prev :=
    memLoad_cellsAt m a t ((iB - 1).toNat + 1) (n :: l) prev
      hmem (by rw [List.getElem?_cons_succ]; exact hgetIMinus)
  have hatPM_ag : memEvalExpr
      (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 1)))) ρ m π =
      evalExpr
        (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 1)))) ρ :=
    memEvalExpr_stdVecAt_hit "v"
      (.usub (.var "i") (.lit (.u64 1))) ρ m π l (iB - 1) prev a t
      hlay hv hsubA hsubM hmemP hgetIMinus
  have hatPM : memEvalExpr
      (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 1)))) ρ m π =
      .ok (.i32 prev) := by rw [hatPM_ag]; exact hatP
  have haddVM : memEvalExpr
      (.add (.stdVecAt "v" (.var "i"))
        (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 1))))) ρ m π =
      .ok (.i32 sum) :=
    (memEvalExpr_add_agree
      (.stdVecAt "v" (.var "i"))
      (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 1)))) ρ m π
      hatM_ag hatPM_ag).trans haddV
  have hlt' : iB.toNat + 1 < (n :: l).length := by
    simp only [List.length_cons]
    omega
  obtain ⟨m₁, hmstore, hmem₁⟩ :=
    memStore_cellsAt_pin m a t sum hmem hlt'
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "v"
    (.stdVecVal l) (.stdVecVal (l.set iB.toNat sum)) hv
  have hstep_set := memRevVecSet prog F "v" (.var "i")
    (.add (.stdVecAt "v" (.var "i"))
      (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 1))))) ρ m π
    iB sum a t l cur m₁ ρ₁
    hiVarM haddVM hv hlay hgetI hmstore hu₁
  have hsetB : l.set iB.toNat sum = l.set i sum := by rw [hiN]
  rw [hsetB] at hmem₁
  have hi₁ : envLookup ρ₁ "i" = some (.u64 iB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "v" by decide) hu₁]
    exact hi
  have hevI : evalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ₁ =
      .ok (.u64 (iB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hi₁) (by simp [evalExpr, litVal])
  have hevIM : memEvalExpr
      (.uadd (.var "i") (.lit (.u64 1))) ρ₁ m₁ π =
      .ok (.u64 (iB + 1)) :=
    (memEvalExpr_uadd_agree (.var "i") (.lit (.u64 1))
      ρ₁ m₁ π (memEvalExpr_var _ _ _ _)
      (memEvalExpr_lit _ _ _ _)).trans hevI
  obtain ⟨ρ', hu₂⟩ := envUpdate_some_of_lookup ρ₁ "i"
    (.u64 iB) (.u64 (iB + 1)) hi₁
  have hstep_i := memRevAssign prog F "i"
    (.uadd (.var "i") (.lit (.u64 1))) ρ₁ m₁ π (.u64 (iB + 1)) ρ'
    hevIM hevI hu₂
  have hout' : envLookup ρ' "v" =
      some (.stdVecVal (l.set i sum)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("v" : String) ≠ "i" by decide) hu₂]
    have h := envLookup_update_hit _ _ _ _ hu₁
    rwa [hsetB] at h
  have hiN' : (iB + 1).toNat = i + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hiN]
    exact Nat.mod_eq_of_lt (by omega)
  have hi' : envLookup ρ' "i" = some (.u64 (iB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₂
  have hbody : vecPartialSumBody =
      (.seq (.vecSet "v" (.var "i")
          (.add (.stdVecAt "v" (.var "i"))
            (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 (1 : BitVec 64)))))))
        (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))) := rfl
  have heval : memEvalProgStmt prog F vecPartialSumBody ρ m π =
      .ok ((ρ', m₁, π), .fellThrough) := by
    rw [hbody,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep_set,
      hstep_i]
  exact ⟨ρ', m₁, heval, hout', ⟨(iB + 1), hi', hiN'⟩, hmem₁⟩

/-- One body iteration on memory, overflow branch: the reads agree
    with the value side, but the checked add fails, so the store
    aborts with the same panic and the state is unchanged. -/
theorem memPartialSumBody_overflow (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (l : List (BitVec 32)) (i : Nat) (iB : BitVec 64)
    (cur prev : BitVec 32) (err : Panic)
    (a t : Nat) (n : BitVec 32)
    (hlay : layoutLookup π "v" = some (a, t))
    (hmem : memFind m a = some ⟨t, true, n :: l⟩)
    (hn : n = BitVec.ofNat 32 l.length)
    (hiN : iB.toNat = i)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hilt : i < l.length) (hi1 : 1 ≤ i)
    (hgetC : l[i]? = some cur) (hgetP : l[i - 1]? = some prev)
    (herr : checkedAddI32 cur prev = .error err) :
    memEvalProgStmt prog F vecPartialSumBody ρ m π = .error err := by
  have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have hiVarA : memEvalExpr (.var "i") ρ m π =
      evalExpr (.var "i") ρ :=
    memEvalExpr_var _ _ _ _
  have hiVarM : memEvalExpr (.var "i") ρ m π = .ok (.u64 iB) :=
    hiVarA.trans hiVar
  have hsub : evalExpr (.usub (.var "i") (.lit (.u64 1#64))) ρ =
      .ok (.u64 (iB - 1#64)) :=
    evalExpr_u64_usub iB 1#64 (.var "i") ρ hiVar
  have hsubN : (iB - 1#64).toNat = i - 1 := by
    have h1 : (1#64 : BitVec 64).toNat = 1 := rfl
    have hno : ¬ BitVec.usubOverflow iB 1#64 := by
      rw [BitVec.usubOverflow, decide_eq_true_eq, hiN, h1]
      omega
    rw [BitVec.toNat_sub_of_not_usubOverflow hno, hiN, h1]
  have hsubA : memEvalExpr (.usub (.var "i") (.lit (.u64 1#64))) ρ m π =
      evalExpr (.usub (.var "i") (.lit (.u64 1#64))) ρ :=
    memEvalExpr_usub_agree _ _ _ _ _
      (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)
  have hsubM : memEvalExpr (.usub (.var "i") (.lit (.u64 1#64))) ρ m π =
      .ok (.u64 (iB - 1#64)) := by
    rw [hsubA]; exact hsub
  have hgetI : l[iB.toNat]? = some cur := by rw [hiN]; exact hgetC
  have hgetIMinus : l[(iB - 1#64).toNat]? = some prev := by
    rw [hsubN]; exact hgetP
  have hatC : evalExpr (.stdVecAt "v" (.var "i")) ρ = .ok (.i32 cur) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hiVar hgetI
  have hatP : evalExpr
      (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 1#64))))
      ρ = .ok (.i32 prev) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hsub hgetIMinus
  have haddV : evalExpr
      (.add (.stdVecAt "v" (.var "i"))
        (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 1#64)))))
      ρ = .error err := by
    have e : evalExpr
        (.add (.stdVecAt "v" (.var "i"))
          (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 1#64)))))
        ρ = (checkedAddI32 cur prev).map .i32 := by
      unfold evalExpr
      rw [hatC, hatP]
    have hmap : (checkedAddI32 cur prev).map Value.i32 = .error err := by
      rw [herr]; rfl
    rw [e, hmap]
  have hmemC : memLoad m a t (iB.toNat + 1) = .ok cur :=
    memLoad_cellsAt m a t (iB.toNat + 1) (n :: l) cur
      hmem (by rw [List.getElem?_cons_succ]; exact hgetI)
  have hatM_ag : memEvalExpr (.stdVecAt "v" (.var "i")) ρ m π =
      evalExpr (.stdVecAt "v" (.var "i")) ρ :=
    memEvalExpr_stdVecAt_hit "v" (.var "i") ρ m π l iB cur a t
      hlay hv hiVarA hiVar hmemC hgetI
  have hmemP : memLoad m a t ((iB - 1#64).toNat + 1) = .ok prev :=
    memLoad_cellsAt m a t ((iB - 1#64).toNat + 1) (n :: l) prev
      hmem (by rw [List.getElem?_cons_succ]; exact hgetIMinus)
  have hatPM_ag : memEvalExpr
      (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 1#64)))) ρ m π =
      evalExpr
        (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 1#64)))) ρ :=
    memEvalExpr_stdVecAt_hit "v"
      (.usub (.var "i") (.lit (.u64 1#64))) ρ m π l (iB - 1#64) prev a t
      hlay hv hsubA hsubM hmemP hgetIMinus
  have haddVM : memEvalExpr
      (.add (.stdVecAt "v" (.var "i"))
        (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 1#64))))) ρ m π =
      .error err :=
    (memEvalExpr_add_agree
      (.stdVecAt "v" (.var "i"))
      (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 1#64)))) ρ m π
      hatM_ag hatPM_ag).trans haddV
  have hvecSetErr : memEvalProgStmt prog F
      (.vecSet "v" (.var "i")
        (.add (.stdVecAt "v" (.var "i"))
          (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 1#64))))))
      ρ m π = .error err := by
    have hfuel : memEvalStmtFuel F
        (.vecSet "v" (.var "i")
          (.add (.stdVecAt "v" (.var "i"))
            (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 1#64))))))
        ρ m π = .error err := by
      cases F <;> simp [memEvalStmtFuel, memEvalStmtZero,
        memEvalStmtWith, hiVarM, haddVM]
    simpa [memEvalProgStmt] using hfuel
  have hbody : vecPartialSumBody =
      (.seq (.vecSet "v" (.var "i")
          (.add (.stdVecAt "v" (.var "i"))
            (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 1#64))))))
        (.assign "i" (.uadd (.var "i") (.lit (.u64 1#64))))) := rfl
  rw [hbody]
  exact memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hvecSetErr

/-! ## Memory loop inductions -/

/-- Memory loop, ok leg: the scan runs to `l.length`, the `v` block
    holds the forward-model words, and the length word is untouched
    (fuel induction threading the memory body hit; the forward
    equation unfolds one step per iteration). -/
theorem memPartialSumLoop_ok (prog : Prog) (F G : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (l : List (BitVec 32)) (i : Nat) (iB : BitVec 64)
    (l' : List (BitVec 32)) (i' : Nat)
    (a t : Nat) (n : BitVec 32)
    (hlay : layoutLookup π "v" = some (a, t))
    (hmem : memFind m a = some ⟨t, true, n :: l⟩)
    (hn : n = BitVec.ofNat 32 l.length)
    (hiN : iB.toNat = i)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hle : i ≤ l.length) (hi1 : 1 ≤ i)
    (hF : l.length - i ≤ F) (hG : l.length - i ≤ G)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (hfwd : partialSumFwd l G i = .ok (i', l')) :
    ∃ ρ' m', memEvalProgStmt prog F vecPartialSumLoop ρ m π =
      .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "v" = some (.stdVecVal l') ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = i') ∧
      memFind m' a = some ⟨t, true, n :: l'⟩ := by
  induction F generalizing G ρ m l i iB with
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
        have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "v") ρ iB
          (BitVec.ofNat 64 l.length)
          (evalExpr_var_hit _ _ _ hi)
          (evalExpr_stdVecLen_some _ _ _ hv)
        have hfb : (iB.ult (BitVec.ofNat 64 l.length)) = false := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_false (by omega)
        rwa [hfb] at hult
      rw [hag]; exact hval
    have hexit : memEvalProgStmt prog 0 vecPartialSumLoop ρ m π =
        .ok ((ρ, m, π), .fellThrough) :=
      memEvalProgStmt_while_false prog 0 _ _ _ _ _ hguardF
    have hpair : (i, l) = (i', l') := by
      cases G with
      | zero => simpa [partialSumFwd] using hfwd
      | succ G =>
        have hneg : ¬ i < l.length := by omega
        simpa [partialSumFwd, dite_eq_right hneg] using hfwd
    obtain ⟨rfl, rfl⟩ := hpair
    exact ⟨ρ, m, hexit, hv, ⟨iB, hi, hiN⟩, hmem⟩
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
      obtain ⟨cur, hgetC⟩ := hread i hlt
      have hprevlt : i - 1 < l.length := by omega
      obtain ⟨prev, hgetP⟩ := hread (i - 1) hprevlt
      cir_fuel_step (F, G, l.length - (i + 1))
      match hadd : checkedAddI32 cur prev with
      | .ok sum =>
        have hlo64' : (l.set i sum).length < 2 ^ 64 := by
          rw [List.length_set]; exact hl64
        have hread' : ∀ p, p < (l.set i sum).length →
            ∃ x, (l.set i sum)[p]? = some x := by
          intro p hp
          have hplen : p < l.length := by
            have : (l.set i sum).length = l.length := by
              simp [List.length_set]
            omega
          obtain ⟨x, hx⟩ := hread p hplen
          by_cases hpi : p = i
          · rw [hpi]
            exact ⟨sum, by
              rw [List.getElem?_set_self (by omega : i < l.length)]⟩
          · exact ⟨x, by
              rw [List.getElem?_set_ne (show i ≠ p by omega)]
              exact hx⟩
        obtain ⟨ρ₁, m₁, hbody, hout₁, ⟨iB₁, hiB₁, hiN₁⟩,
            hmem₁⟩ :=
          memPartialSumBody_ok prog F ρ m π l i iB cur prev sum
            a t n hlay hmem hn hiN hl64 hv hi hlt hi1 hgetC hgetP
            hadd
        have hfwd' : partialSumFwd (l.set i sum) G' (i + 1) =
            .ok (i', l') := by
          have h := hfwd
          simpa [partialSumFwd, dite_eq_left hlt, hgetC, hgetP, hadd]
            using h
        have hlen : (l.set i sum).length = l.length := by
          simp [List.length_set]
        have hF'' : (l.set i sum).length - (i + 1) ≤ F := by omega
        have hG'' : (l.set i sum).length - (i + 1) ≤ G' := by omega
        have hn' : n = BitVec.ofNat 32 (l.set i sum).length := by
          rw [List.length_set]; exact hn
        obtain ⟨ρ', m', hloop, hout', ⟨iB', hiB', hiN'⟩,
            hmem'⟩ :=
          ih (G := G') (ρ := ρ₁) (m := m₁) (l := l.set i sum)
            (i := i + 1) (iB := iB₁)
            (hmem := hmem₁) (hn := hn')
            (hiN := hiN₁) (hl64 := hlo64')
            (hv := hout₁) (hi := hiB₁)
            (hle := by omega) (hi1 := by omega)
            (hF := hF'') (hG := hG'')
            (hread := hread') (hfwd := hfwd')
        refine ⟨ρ', m', ?_, hout', ⟨iB', hiB', hiN'⟩, hmem'⟩
        have hwhile : memEvalProgStmt prog (F + 1) vecPartialSumLoop
            ρ m π =
            memEvalProgStmt prog F vecPartialSumLoop ρ₁ m₁ π := by
          cir_unfold_prog (vecPartialSumLoop, prog, F, hguardT, hbody)
        rw [hwhile]
        exact hloop
      | .error e =>
        have h := hfwd
        simp only [partialSumFwd, dite_eq_left hlt, hgetC, hgetP, hadd]
          at h
        exact absurd h (by simp)
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
      have hexit : memEvalProgStmt prog (F + 1) vecPartialSumLoop
          ρ m π =
          .ok ((ρ, m, π), .fellThrough) :=
        memEvalProgStmt_while_false prog (F + 1) _ _ _ _ _ hguardF
      have hpair : (l.length, l) = (i', l') := by
        cases G with
        | zero => simpa [partialSumFwd] using hfwd
        | succ G =>
          have hneg : ¬ l.length < l.length := by omega
          simpa [partialSumFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl⟩ := hpair
      exact ⟨ρ, m, hexit, hv, ⟨iB, hi, hiN⟩, hmem⟩

/-! ## Entry bridges (`evalProgFunc` per leg) -/

/-- Value entry, ok leg: binding, `i ← 1`, the loop, and `return v`
    compute the forward-model words. -/
theorem evalProgFunc_vecPartialSum_ok (F : Nat)
    (l l' : List (BitVec 32)) (i' : Nat)
    (hl64 : l.length < 2 ^ 64)
    (hF : l.length ≤ F)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (hfwd : partialSumFwd l l.length 1 = .ok (i', l')) :
    evalProgFunc vecPartialSumProg F vecPartialSumFunc
      [.stdVecVal l] = .ok (.stdVecVal l') := by
  have hbind : bindArgs vecPartialSumFunc.args [.stdVecVal l] =
      some [("v", .stdVecVal l)] := rfl
  have hbody : vecPartialSumFunc.body =
      (.seq (.let_ "i" (.u 64) (.lit (.u64 1)))
        (.seq vecPartialSumLoop
          (.return_ (.var "v")))) := rfl
  have hlit : evalExpr (.lit (.u64 1)) [("v", .stdVecVal l)] =
      .ok (.u64 1) := by simp [evalExpr, litVal]
  have hlet := revLet vecPartialSumProg F "i" (.u 64)
    (.lit (.u64 1)) [("v", .stdVecVal l)] (.u64 1) hlit
  have hv₁ : envLookup (envExtend [("v", .stdVecVal l)] "i" (.u64 1))
      "v" = some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hi₁ : envLookup (envExtend [("v", .stdVecVal l)] "i" (.u64 1))
      "i" = some (.u64 1) :=
    envExtend_hit _ _ _
  have hiN : (1 : BitVec 64).toNat = 1 := rfl
  by_cases hle : 1 ≤ l.length
  · obtain ⟨ρ', hloop, hout', ⟨iB', hiB', hiN'⟩⟩ :=
      valPartialSumLoop_ok vecPartialSumProg F l.length
        (envExtend [("v", .stdVecVal l)] "i" (.u64 1))
        l 1 1 l' i' hiN hl64 hv₁ hi₁ hle (by omega)
        (by omega) (by omega) hread hfwd
    have hret := evalProgStmt_return vecPartialSumProg F
      (.var "v") ρ' (.stdVecVal l')
      (evalExpr_var_hit _ _ _ hout')
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hlet,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hloop,
      hret]
  · have hlen0 : l.length = 0 := by omega
    have hfwd0 : partialSumFwd l 0 1 = .ok (i', l') := by
      rw [← hlen0]; exact hfwd
    have hpair : (1, l) = (i', l') := by
      simpa [partialSumFwd] using hfwd0
    have hiEq : i' = 1 := by
      simpa using (congrArg Prod.fst hpair).symm
    have hlEq : l' = l := by
      simpa using (congrArg Prod.snd hpair).symm
    have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by omega)
    have hguardF : evalExpr (.ult (.var "i") (.stdVecLen "v"))
        (envExtend [("v", .stdVecVal l)] "i" (.u64 1)) =
        .ok (.b false) := by
      have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "v")
        (envExtend [("v", .stdVecVal l)] "i" (.u64 1)) 1
        (BitVec.ofNat 64 l.length)
        (evalExpr_var_hit _ _ _ hi₁)
        (evalExpr_stdVecLen_some _ _ _ hv₁)
      have hfb : ((1 : BitVec 64).ult
          (BitVec.ofNat 64 l.length)) = false := by
        rw [BitVec.ult_eq_decide, hiN, hlenN, hlen0]
        decide
      rwa [hfb] at hult
    have hloop : evalProgStmt vecPartialSumProg F vecPartialSumLoop
        (envExtend [("v", .stdVecVal l)] "i" (.u64 1)) =
        .ok ((envExtend [("v", .stdVecVal l)] "i" (.u64 1)),
          .fellThrough) :=
      evalProgStmt_while_false vecPartialSumProg F _ _ _ hguardF
    have hret := evalProgStmt_return vecPartialSumProg F
      (.var "v")
      (envExtend [("v", .stdVecVal l)] "i" (.u64 1)) (.stdVecVal l)
      (evalExpr_var_hit _ _ _ hv₁)
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hlet,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hloop,
      hret, hlEq]

/-- Value entry, overflow leg: the first failing checked add aborts
    the whole function loudly. -/
theorem evalProgFunc_vecPartialSum_overflow (F : Nat)
    (l : List (BitVec 32)) (err : Panic)
    (hl64 : l.length < 2 ^ 64)
    (hF : l.length ≤ F)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (hfwd : partialSumFwd l l.length 1 = .error err) :
    evalProgFunc vecPartialSumProg F vecPartialSumFunc
      [.stdVecVal l] = .error err := by
  have hbind : bindArgs vecPartialSumFunc.args [.stdVecVal l] =
      some [("v", .stdVecVal l)] := rfl
  have hbody : vecPartialSumFunc.body =
      (.seq (.let_ "i" (.u 64) (.lit (.u64 1)))
        (.seq vecPartialSumLoop
          (.return_ (.var "v")))) := rfl
  have hlit : evalExpr (.lit (.u64 1)) [("v", .stdVecVal l)] =
      .ok (.u64 1) := by simp [evalExpr, litVal]
  have hlet := revLet vecPartialSumProg F "i" (.u 64)
    (.lit (.u64 1)) [("v", .stdVecVal l)] (.u64 1) hlit
  have hv₁ : envLookup (envExtend [("v", .stdVecVal l)] "i" (.u64 1))
      "v" = some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hi₁ : envLookup (envExtend [("v", .stdVecVal l)] "i" (.u64 1))
      "i" = some (.u64 1) :=
    envExtend_hit _ _ _
  have hiN : (1 : BitVec 64).toNat = 1 := rfl
  by_cases hle : 1 ≤ l.length
  · have hloop : evalProgStmt vecPartialSumProg F vecPartialSumLoop
        (envExtend [("v", .stdVecVal l)] "i" (.u64 1)) =
        .error err :=
        valPartialSumLoop_overflow vecPartialSumProg F l.length
          (envExtend [("v", .stdVecVal l)] "i" (.u64 1))
          l 1 1 err hiN hl64 hv₁ hi₁ hle (by omega) (by omega)
          (by omega) hread hfwd
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hlet,
      evalProgStmt_seq_err _ _ _ _ _ _ hloop]
  · have hlen0 : l.length = 0 := by omega
    have hcon := hfwd
    rw [hlen0] at hcon
    simp [partialSumFwd] at hcon

/-- Memory loop, overflow leg: the first failing checked add aborts
    the whole scan (the guard-false exits are impossible under an
    error equation). -/
theorem memPartialSumLoop_overflow (prog : Prog) (F G : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (l : List (BitVec 32)) (i : Nat) (iB : BitVec 64)
    (err : Panic)
    (a t : Nat) (n : BitVec 32)
    (hlay : layoutLookup π "v" = some (a, t))
    (hmem : memFind m a = some ⟨t, true, n :: l⟩)
    (hn : n = BitVec.ofNat 32 l.length)
    (hiN : iB.toNat = i)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hle : i ≤ l.length) (hi1 : 1 ≤ i)
    (hF : l.length - i ≤ F) (hG : l.length - i ≤ G)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (hfwd : partialSumFwd l G i = .error err) :
    memEvalProgStmt prog F vecPartialSumLoop ρ m π = .error err := by
  induction F generalizing G ρ m l i iB with
  | zero =>
    have him : i = l.length := by omega
    subst him
    cases G with
    | zero => exact absurd hfwd (by simp [partialSumFwd])
    | succ _ =>
      have hneg : ¬ l.length < l.length := by omega
      have hcon := hfwd
      simp only [partialSumFwd, dite_eq_right hneg] at hcon
      exact absurd hcon (by simp)
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
      obtain ⟨cur, hgetC⟩ := hread i hlt
      have hprevlt : i - 1 < l.length := by omega
      obtain ⟨prev, hgetP⟩ := hread (i - 1) hprevlt
      cir_fuel_step (F, G, l.length - (i + 1))
      match hadd : checkedAddI32 cur prev with
      | .ok sum =>
        obtain ⟨ρ₁, m₁, hbody, hout₁, ⟨iB₁, hiB₁, hiN₁⟩,
            hmem₁⟩ :=
          memPartialSumBody_ok prog F ρ m π l i iB cur prev sum
            a t n hlay hmem hn hiN hl64 hv hi hlt hi1 hgetC hgetP
            hadd
        have hlen : (l.set i sum).length = l.length := by
          simp [List.length_set]
        have hlo64' : (l.set i sum).length < 2 ^ 64 := by
          rw [hlen]; exact hl64
        have hF'' : (l.set i sum).length - (i + 1) ≤ F := by omega
        have hG'' : (l.set i sum).length - (i + 1) ≤ G' := by omega
        have hread' : ∀ p, p < (l.set i sum).length →
            ∃ x, (l.set i sum)[p]? = some x := by
          intro p hp
          have hplen : p < l.length := by omega
          obtain ⟨x, hx⟩ := hread p hplen
          by_cases hpi : p = i
          · rw [hpi]
            exact ⟨sum, by
              rw [List.getElem?_set_self (by omega : i < l.length)]⟩
          · exact ⟨x, by
              rw [List.getElem?_set_ne (show i ≠ p by omega)]
              exact hx⟩
        have hn' : n = BitVec.ofNat 32 (l.set i sum).length := by
          rw [List.length_set]; exact hn
        have hfwd' : partialSumFwd (l.set i sum) G' (i + 1) =
            .error err := by
          have h := hfwd
          simpa [partialSumFwd, dite_eq_left hlt, hgetC, hgetP, hadd]
            using h
        have hloop : memEvalProgStmt prog F vecPartialSumLoop
            ρ₁ m₁ π = .error err :=
          ih (G := G') (ρ := ρ₁) (m := m₁) (l := l.set i sum)
            (i := i + 1) (iB := iB₁)
            (hmem := hmem₁) (hn := hn')
            (hiN := hiN₁) (hl64 := hlo64')
            (hv := hout₁) (hi := hiB₁)
            (hle := by omega) (hi1 := by omega)
            (hF := hF'') (hG := hG'')
            (hread := hread') (hfwd := hfwd')
        have hwhile : memEvalProgStmt prog (F + 1) vecPartialSumLoop
            ρ m π = .error err := by
          cir_unfold_prog (vecPartialSumLoop, prog, F, hguardT, hbody)
          exact hloop
        exact hwhile
      | .error e =>
        have heq : e = err := by
          have h := hfwd
          simpa [partialSumFwd, dite_eq_left hlt, hgetC, hgetP, hadd]
            using h
        have hbodyErr :=
          memPartialSumBody_overflow prog F ρ m π l i iB cur prev e
            a t n hlay hmem hn hiN hl64 hv hi hlt hi1 hgetC hgetP
            hadd
        rw [heq] at hbodyErr
        cir_unfold_prog (vecPartialSumLoop, prog, F, hguardT, hbodyErr)
    · have him : i = l.length := by omega
      subst him
      cases G with
      | zero => exact absurd hfwd (by simp [partialSumFwd])
      | succ _ =>
        have hneg : ¬ l.length < l.length := by omega
        have hcon := hfwd
        simp only [partialSumFwd, dite_eq_right hneg] at hcon
        exact absurd hcon (by simp)

/-! ## Memory entries (`memEvalProgFunc` per leg) -/

/-- Memory entry, ok leg: the `i` prelude runs on memory, the loop
    closes against the forward model, and `return v` delivers the
    rewritten words. -/
theorem memEvalProgFunc_vecPartialSum_ok (F : Nat)
    (l l' : List (BitVec 32)) (i' : Nat)
    (hl64 : l.length < 2 ^ 64)
    (hF : l.length ≤ F)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (hfwd : partialSumFwd l l.length 1 = .ok (i', l')) :
    memEvalProgFunc vecPartialSumProg F vecPartialSumFunc
      [.stdVecVal l] = .ok (.stdVecVal l') := by
  have hbind := bindMemArgs_vecPartialSum l
  have hbody : vecPartialSumFunc.body =
      (.seq (.let_ "i" (.u 64) (.lit (.u64 1)))
        (.seq vecPartialSumLoop
          (.return_ (.var "v")))) := rfl
  have hmem : memFind
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ 0 =
      some ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩ :=
    memFind_cons_hit _ _ _ _ _
  have hlay : layoutLookup [("v", 0, 0)] "v" =
      some (0, 0) := by simp [layoutLookup]
  have hlitM : memEvalExpr
      (.lit (.u64 1))
      [("v", .stdVecVal l)]
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("v", 0, 0)] =
      evalExpr (.lit (.u64 1))
        [("v", .stdVecVal l)] :=
    memEvalExpr_lit _ _ _ _
  have hlitV : evalExpr (.lit (.u64 1))
      [("v", .stdVecVal l)] =
      .ok (.u64 1) := by simp [evalExpr, litVal]
  have hlet := memRevLet vecPartialSumProg F "i" (.u 64)
    (.lit (.u64 1))
    [("v", .stdVecVal l)]
    ⟨1, [(0, ⟨0, true,
      (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
    [("v", 0, 0)] (.u64 1)
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) (by intro h; cases h) hlitM hlitV
  have hiN : (1 : BitVec 64).toNat = 1 := rfl
  have hv₁ : envLookup (envExtend [("v", .stdVecVal l)] "i" (.u64 1))
      "v" = some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hi₁ : envLookup (envExtend [("v", .stdVecVal l)] "i" (.u64 1))
      "i" = some (.u64 1) :=
    envExtend_hit _ _ _
  have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by omega)
  by_cases hle : 1 ≤ l.length
  · obtain ⟨ρ', m', hloop, hout', ⟨iB', hiB', hiN'⟩,
        hmem'⟩ :=
      memPartialSumLoop_ok vecPartialSumProg F l.length
        (envExtend [("v", .stdVecVal l)] "i" (.u64 1))
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
        [("v", 0, 0)]
        l 1 1 l' i' 0 0 (BitVec.ofNat 32 l.length)
        hlay hmem rfl hiN hl64 hv₁ hi₁
        hle (by omega) (by omega) (by omega) hread hfwd
    have hret := memEvalProgStmt_return vecPartialSumProg F
      (.var "v") ρ' m' [("v", 0, 0)]
      (.stdVecVal l')
      ((memEvalExpr_var _ _ _ _).trans
        (evalExpr_var_hit _ _ _ hout'))
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hlet,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hloop,
      hret]
  · have hlen0 : l.length = 0 := by omega
    have hfwd0 : partialSumFwd l 0 1 = .ok (i', l') := by
      rw [← hlen0]; exact hfwd
    have hpair : (1, l) = (i', l') := by
      simpa [partialSumFwd] using hfwd0
    have hlEq : l' = l := by
      simpa using (congrArg Prod.snd hpair).symm
    have hguardF : memEvalExpr (.ult (.var "i") (.stdVecLen "v"))
        (envExtend [("v", .stdVecVal l)] "i" (.u64 1))
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
        [("v", 0, 0)] =
        .ok (.b false) := by
      have hag : memEvalExpr (.ult (.var "i") (.stdVecLen "v"))
          (envExtend [("v", .stdVecVal l)] "i" (.u64 1))
          ⟨1, [(0, ⟨0, true,
            (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
          [("v", 0, 0)] =
          evalExpr (.ult (.var "i") (.stdVecLen "v"))
            (envExtend [("v", .stdVecVal l)] "i" (.u64 1)) := by
        have hmemLen' : memLoad
            ⟨1, [(0, ⟨0, true,
              (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ 0 0 0 =
            .ok (BitVec.ofNat 32 l.length) := by
          exact memLoad_cellsAt _ _ _ _ _ _ hmem (by simp)
        exact memEvalExpr_ult_agree (.var "i") (.stdVecLen "v")
          (envExtend [("v", .stdVecVal l)] "i" (.u64 1))
          ⟨1, [(0, ⟨0, true,
            (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
          [("v", 0, 0)]
          (memEvalExpr_var _ _ _ _)
          (memEvalExpr_stdVecLen_hit "v"
            (envExtend [("v", .stdVecVal l)] "i" (.u64 1))
            ⟨1, [(0, ⟨0, true,
              (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
            [("v", 0, 0)] l 0 0
            hlay hv₁ hmemLen')
      have hval : evalExpr (.ult (.var "i") (.stdVecLen "v"))
          (envExtend [("v", .stdVecVal l)] "i" (.u64 1)) =
          .ok (.b false) := by
        have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "v")
          (envExtend [("v", .stdVecVal l)] "i" (.u64 1)) 1
          (BitVec.ofNat 64 l.length)
          (evalExpr_var_hit _ _ _ hi₁)
          (evalExpr_stdVecLen_some _ _ _ hv₁)
        have hfb : ((1 : BitVec 64).ult
            (BitVec.ofNat 64 l.length)) = false := by
          rw [BitVec.ult_eq_decide, hiN, hlenN, hlen0]
          decide
        rwa [hfb] at hult
      rw [hag]; exact hval
    have hloop : memEvalProgStmt vecPartialSumProg F vecPartialSumLoop
        (envExtend [("v", .stdVecVal l)] "i" (.u64 1))
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
        [("v", 0, 0)] =
        .ok (((envExtend [("v", .stdVecVal l)] "i" (.u64 1)),
          ⟨1, [(0, ⟨0, true,
            (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
          [("v", 0, 0)]), .fellThrough) :=
      memEvalProgStmt_while_false vecPartialSumProg F _ _ _ _ _ hguardF
    have hret := memEvalProgStmt_return vecPartialSumProg F
      (.var "v")
      (envExtend [("v", .stdVecVal l)] "i" (.u64 1))
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("v", 0, 0)] (.stdVecVal l)
      ((memEvalExpr_var _ _ _ _).trans
        (evalExpr_var_hit _ _ _ hv₁))
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hlet,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hloop,
      hret, hlEq]

/-- Memory entry, overflow leg: the first failing checked add aborts
    the whole function loudly on memory too. -/
theorem memEvalProgFunc_vecPartialSum_overflow (F : Nat)
    (l : List (BitVec 32)) (err : Panic)
    (hl64 : l.length < 2 ^ 64)
    (hF : l.length ≤ F)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (hfwd : partialSumFwd l l.length 1 = .error err) :
    memEvalProgFunc vecPartialSumProg F vecPartialSumFunc
      [.stdVecVal l] = .error err := by
  have hbind := bindMemArgs_vecPartialSum l
  have hbody : vecPartialSumFunc.body =
      (.seq (.let_ "i" (.u 64) (.lit (.u64 1)))
        (.seq vecPartialSumLoop
          (.return_ (.var "v")))) := rfl
  have hmem : memFind
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ 0 =
      some ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩ :=
    memFind_cons_hit _ _ _ _ _
  have hlitM : memEvalExpr
      (.lit (.u64 1))
      [("v", .stdVecVal l)]
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("v", 0, 0)] =
      evalExpr (.lit (.u64 1))
        [("v", .stdVecVal l)] :=
    memEvalExpr_lit _ _ _ _
  have hlitV : evalExpr (.lit (.u64 1))
      [("v", .stdVecVal l)] =
      .ok (.u64 1) := by simp [evalExpr, litVal]
  have hlet := memRevLet vecPartialSumProg F "i" (.u 64)
    (.lit (.u64 1))
    [("v", .stdVecVal l)]
    ⟨1, [(0, ⟨0, true,
      (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
    [("v", 0, 0)] (.u64 1)
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) (by intro h; cases h) hlitM hlitV
  have hiN : (1 : BitVec 64).toNat = 1 := rfl
  have hv₁ : envLookup (envExtend [("v", .stdVecVal l)] "i" (.u64 1))
      "v" = some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hi₁ : envLookup (envExtend [("v", .stdVecVal l)] "i" (.u64 1))
      "i" = some (.u64 1) :=
    envExtend_hit _ _ _
  by_cases hle : 1 ≤ l.length
  · have hloop : memEvalProgStmt vecPartialSumProg F vecPartialSumLoop
        (envExtend [("v", .stdVecVal l)] "i" (.u64 1))
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
        [("v", 0, 0)] = .error err :=
      memPartialSumLoop_overflow vecPartialSumProg F l.length
        (envExtend [("v", .stdVecVal l)] "i" (.u64 1))
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
        [("v", 0, 0)]
        l 1 1 err 0 0 (BitVec.ofNat 32 l.length)
        (by simp [layoutLookup]) hmem rfl hiN hl64 hv₁ hi₁
        hle (by omega) (by omega) (by omega) hread hfwd
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hlet,
      memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hloop]
  · have hlen0 : l.length = 0 := by omega
    have hcon := hfwd
    rw [hlen0] at hcon
    simp [partialSumFwd] at hcon

/-! ## Transfer (`memEval = Eval` per leg) -/

/-- Transfer for `vec_partial_sum`, ok leg: memory evaluation agrees
    with value evaluation on a successful scan. -/
theorem memTransferProg_vecPartialSum_ok (F : Nat)
    (l l' : List (BitVec 32)) (i' : Nat)
    (hl64 : l.length < 2 ^ 64)
    (hF : l.length ≤ F)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (hfwd : partialSumFwd l l.length 1 = .ok (i', l'))
    (_h : oracleNoalias vecPartialSumFunc
      [.stdVecVal l]) :
    memEvalProgFunc vecPartialSumProg F vecPartialSumFunc
      [.stdVecVal l] =
      evalProgFunc vecPartialSumProg F vecPartialSumFunc
        [.stdVecVal l] := by
  rw [memEvalProgFunc_vecPartialSum_ok F l l' i' hl64 hF
    hread hfwd,
    evalProgFunc_vecPartialSum_ok F l l' i' hl64 hF hread hfwd]

/-- Transfer for `vec_partial_sum`, overflow leg: memory evaluation
    agrees with value evaluation on a loud checked-add failure. -/
theorem memTransferProg_vecPartialSum_overflow (F : Nat)
    (l : List (BitVec 32)) (err : Panic)
    (hl64 : l.length < 2 ^ 64)
    (hF : l.length ≤ F)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (hfwd : partialSumFwd l l.length 1 = .error err)
    (_h : oracleNoalias vecPartialSumFunc
      [.stdVecVal l]) :
    memEvalProgFunc vecPartialSumProg F vecPartialSumFunc
      [.stdVecVal l] =
      evalProgFunc vecPartialSumProg F vecPartialSumFunc
        [.stdVecVal l] := by
  rw [memEvalProgFunc_vecPartialSum_overflow F l err hl64 hF
    hread hfwd,
    evalProgFunc_vecPartialSum_overflow F l err hl64 hF hread hfwd]

/-! ## Closing specs (against the independent checked scan) -/

/-- Closing prefix-scan contract (P2-M10), ok leg: a successful run
    returns the rewritten words, which are exactly the independent
    checked prefix sums. -/
theorem evalProgFunc_vecPartialSum_spec_ok (F : Nat)
    (l l' : List (BitVec 32)) (i' : Nat)
    (hl64 : l.length < 2 ^ 64)
    (hF : l.length ≤ F)
    (hfwd : partialSumFwd l l.length 1 = .ok (i', l')) :
    evalProgFunc vecPartialSumProg F vecPartialSumFunc
      [.stdVecVal l] = .ok (.stdVecVal l') ∧
      partialSumsChecked l = .ok l' := by
  have hread : ∀ p, p < l.length → ∃ x, l[p]? = some x :=
    fun p hp => ⟨l[p], List.getElem?_eq_getElem hp⟩
  have heval := evalProgFunc_vecPartialSum_ok F l l' i'
    hl64 hF hread hfwd
  refine ⟨heval, ?_⟩
  by_cases hle : 1 ≤ l.length
  · cases l with
    | nil => exact absurd hle (by simp)
    | cons x xs =>
      have htake1 : (x :: xs).take 1 = [x] := rfl
      have hscan0 : scanChecked ((x :: xs).take 1) 0 = .ok [x] := by
        rw [htake1]; exact scanChecked_singleton_zero x
      have hscan := partialSumFwd_scan_ok (x :: xs) ((x :: xs).length)
        1 (x :: xs) [x] l' i' (by omega) (by omega) (by omega)
        rfl htake1 hscan0 rfl hfwd
      simpa [partialSumsChecked] using hscan.2.1
  · have hlen0 : l.length = 0 := by omega
    have hempty : l = [] := List.eq_nil_of_length_eq_zero hlen0
    subst hempty
    have hfwd0 : partialSumFwd [] 0 1 = .ok (i', l') := hfwd
    have hpair : (1, ([] : List (BitVec 32))) = (i', l') := by
      simpa [partialSumFwd] using hfwd0
    have hlEq : l' = [] := by
      simpa using (congrArg Prod.snd hpair).symm
    rw [hlEq]
    simp [partialSumsChecked, scanChecked]

/-- Closing prefix-scan contract (P2-M10), overflow leg: a failing
    run aborts loudly, and the independent checked scan fails with
    the same panic. -/
theorem evalProgFunc_vecPartialSum_spec_overflow (F : Nat)
    (l : List (BitVec 32)) (err : Panic)
    (hl64 : l.length < 2 ^ 64)
    (hF : l.length ≤ F)
    (hfwd : partialSumFwd l l.length 1 = .error err) :
    evalProgFunc vecPartialSumProg F vecPartialSumFunc
      [.stdVecVal l] = .error err ∧
      partialSumsChecked l = .error err := by
  have hread : ∀ p, p < l.length → ∃ x, l[p]? = some x :=
    fun p hp => ⟨l[p], List.getElem?_eq_getElem hp⟩
  have heval := evalProgFunc_vecPartialSum_overflow F l err
    hl64 hF hread hfwd
  refine ⟨heval, ?_⟩
  by_cases hle : 1 ≤ l.length
  · cases l with
    | nil => exact absurd hle (by simp)
    | cons x xs =>
      have htake1 : (x :: xs).take 1 = [x] := rfl
      have hscan0 : scanChecked ((x :: xs).take 1) 0 = .ok [x] := by
        rw [htake1]; exact scanChecked_singleton_zero x
      have hscanErr := partialSumFwd_scan_err (x :: xs)
        ((x :: xs).length) 1 (x :: xs) [x] err (by omega) (by omega)
        (by omega) rfl rfl hscan0 rfl hfwd
      simpa [partialSumsChecked] using hscanErr
  · have hlen0 : l.length = 0 := by omega
    have hcon := hfwd
    rw [hlen0] at hcon
    simp [partialSumFwd] at hcon
