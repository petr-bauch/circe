/-
Circe.Transfer.VecUnique — mem transfer for adjacent-duplicate
squeeze (`vec_unique`, the `std::unique` idiom; P2-M13).

Mirrors the value loop (`valUniqueBody_keep/drop`,
`valUniqueLoop_ok` in `Circe.Emit.VecUnique`) step for step on
the memory layer: the single `mutBorrow` block pins the reified
snapshot, the keep test reads the predecessor survivor through
`memLoad` at `(wB - 1).toNat + 1` (the `w ≥ 1` seed fact keeps
every predecessor read in bounds), the survivor store threads
through `memStore` in lockstep on the same block (the drop
branch stores nothing), and the loop re-inducts over `(ρ, m, π)`
with the forward equation threading (two fuels: program fuel
and forward fuel). One leg only — the kernel is total (every
access is guard-justified). Entries close against the forward
contract, with the empty-input early exit evaluated directly on
both layers.
-/
import Circe.Transfer.VecRemove
import Circe.Emit.VecUnique
import Circe.Specs

/-! ## Binding (closed form) -/

/-- Unique binding pins one snapshot: the single `mutBorrow`
    vector at addr `0` (the `stdVecIndex` precedent). -/
theorem bindMemArgs_vecUnique (l : List (BitVec 32)) :
    bindMemArgs vecUniqueFunc.args
      [.stdVecVal l] emptyMem =
      some ([("v", .stdVecVal l)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("v", 0, 0)]) := by
  rfl

/-- Unique footprint is a single singleton. -/
theorem oracleNoalias_vecUnique (l : List (BitVec 32)) :
    oracleNoalias vecUniqueFunc
      [.stdVecVal l] := by
  have hb := bindMemArgs_vecUnique l
  have hn : LayoutNoAlias [("v", 0, 0)] := by
    simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-! ## Memory body hit -/

/-- One body iteration on memory, keep branch: the env threads
    exactly as on the value side while the survivor store
    prepends a shadowing snapshot block on the single `v`
    block (layout stays pinned). The keep test reads the
    predecessor survivor through a second memory load. -/
theorem memUniqueBody_keep (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (l : List (BitVec 32))
    (r w : Nat) (rB wB : BitVec 64) (y p wOld : BitVec 32)
    (a t : Nat) (n : BitVec 32)
    (hlay : layoutLookup π "v" = some (a, t))
    (hmem : memFind m a = some ⟨t, true, n :: l⟩)
    (hn : n = BitVec.ofNat 32 l.length)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hrlt : r < l.length) (hw1 : 1 ≤ w)
    (hy : l[r]? = some y) (hp : l[w - 1]? = some p)
    (hwget : l[w]? = some wOld)
    (hwlt : w < l.length)
    (hkeep : (y != p) = true) :
    ∃ ρ' m', memEvalProgStmt prog F vecUniqueBody ρ m π =
      .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "v" = some (.stdVecVal (l.set w y)) ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r + 1) ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w + 1) ∧
      memFind m' a = some ⟨t, true, n :: (l.set w y)⟩ := by
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
  have hwVar : evalExpr (.var "w") ρ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw
  have hrVarM : memEvalExpr (.var "r") ρ m π = .ok (.u64 rB) :=
    (memEvalExpr_var _ _ _ _).trans hrVar
  have hwVarM : memEvalExpr (.var "w") ρ m π = .ok (.u64 wB) :=
    (memEvalExpr_var _ _ _ _).trans hwVar
  have hgetR : l[rB.toNat]? = some y := by rw [hrN]; exact hy
  have hgetW : l[wB.toNat]? = some wOld := by rw [hwN]; exact hwget
  have hmemR : memLoad m a t (rB.toNat + 1) = .ok y :=
    memLoad_cellsAt m a t (rB.toNat + 1) (n :: l) y
      hmem (by rw [List.getElem?_cons_succ]; exact hgetR)
  have hat : evalExpr (.stdVecAt "v" (.var "r")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hrVar hgetR
  have hatM_ag : memEvalExpr (.stdVecAt "v" (.var "r")) ρ m π =
      evalExpr (.stdVecAt "v" (.var "r")) ρ :=
    memEvalExpr_stdVecAt_hit "v" (.var "r") ρ m π l rB y a t
      hlay hv (memEvalExpr_var _ _ _ _) hrVar hmemR hgetR
  have hatM : memEvalExpr (.stdVecAt "v" (.var "r")) ρ m π =
      .ok (.i32 y) := by rw [hatM_ag]; exact hat
  have hsub : evalExpr (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64)))) ρ =
      .ok (.u64 (wB - 1)) :=
    evalExpr_u64_usub wB 1 (.var "w") ρ hwVar
  have hsubN : (wB - 1).toNat = w - 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    have hno : ¬ BitVec.usubOverflow wB 1 := by
      rw [BitVec.usubOverflow, decide_eq_true_eq, hwN, h1]
      omega
    rw [BitVec.toNat_sub_of_not_usubOverflow hno, hwN, h1]
  have hsubM_ag : memEvalExpr (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64)))) ρ m π =
      evalExpr (.usub (.var "w") (.lit (.u64 (1 : BitVec 64)))) ρ :=
    memEvalExpr_usub_agree (.var "w") (.lit (.u64 (1 : BitVec 64)))
      ρ m π (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)
  have hgetP : l[(wB - 1).toNat]? = some p := by
    rw [hsubN]; exact hp
  have hmemP : memLoad m a t ((wB - 1).toNat + 1) = .ok p :=
    memLoad_cellsAt m a t ((wB - 1).toNat + 1) (n :: l) p
      hmem (by rw [List.getElem?_cons_succ]; exact hgetP)
  have hatP : evalExpr (.stdVecAt "v" (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64))))) ρ = .ok (.i32 p) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hsub hgetP
  have hatPM_ag : memEvalExpr vecUniquePrev ρ m π =
      evalExpr vecUniquePrev ρ :=
    memEvalExpr_stdVecAt_hit "v" (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64)))) ρ m π l (wB - 1) p a t
      hlay hv hsubM_ag hsub hmemP hgetP
  have hatPM : memEvalExpr vecUniquePrev ρ m π = .ok (.i32 p) := by
    rw [hatPM_ag]; exact hatP
  have huneV : evalExpr (.une (.stdVecAt "v" (.var "r"))
      vecUniquePrev) ρ = .ok (.b true) := by
    have h := evalExpr_une_i32 (.stdVecAt "v" (.var "r"))
      vecUniquePrev ρ y p hat hatP
    rwa [hkeep] at h
  have huneM : memEvalExpr (.une (.stdVecAt "v" (.var "r"))
      vecUniquePrev) ρ m π = .ok (.b true) :=
    (memEvalExpr_une_agree (.stdVecAt "v" (.var "r"))
      vecUniquePrev ρ m π hatM_ag hatPM_ag).trans huneV
  have hlt₁ : wB.toNat + 1 < (n :: l).length := by
    simp only [List.length_cons]
    omega
  obtain ⟨m₁, hmstore, hmem₁⟩ :=
    memStore_cellsAt_pin m a t y hmem hlt₁
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "v"
    (.stdVecVal l) (.stdVecVal (l.set wB.toNat y)) hv
  have hstep_set := memRevVecSet prog F "v" (.var "w")
    (.stdVecAt "v" (.var "r")) ρ m π wB y a t l wOld m₁ ρ₁
    hwVarM hatM hv hlay hgetW hmstore hu₁
  have hsetB : l.set wB.toNat y = l.set w y := by rw [hwN]
  rw [hsetB] at hmem₁
  have hw₁ : envLookup ρ₁ "w" = some (.u64 wB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "v" by decide) hu₁]
    exact hw
  have hr₁ : envLookup ρ₁ "r" = some (.u64 rB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("r" : String) ≠ "v" by decide) hu₁]
    exact hr
  have hwVarM₁ : memEvalExpr (.var "w") ρ₁ m₁ π =
      .ok (.u64 wB) :=
    (memEvalExpr_var _ _ _ _).trans
      (evalExpr_var_hit _ _ _ hw₁)
  have hevW : evalExpr (.uadd (.var "w")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁ =
      .ok (.u64 (wB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hw₁) (by simp [evalExpr, litVal])
  have hevWM : memEvalExpr
      (.uadd (.var "w") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁ m₁ π =
      .ok (.u64 (wB + 1)) :=
    (memEvalExpr_uadd_agree (.var "w") (.lit (.u64 (BitVec.ofNat 64 1)))
      ρ₁ m₁ π (memEvalExpr_var _ _ _ _)
      (memEvalExpr_lit _ _ _ _)).trans hevW
  obtain ⟨ρ₂, hu₂⟩ := envUpdate_some_of_lookup ρ₁ "w"
    (.u64 wB) (.u64 (wB + 1)) hw₁
  have hstep_w := memRevAssign prog F "w"
    (.uadd (.var "w") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁ m₁ π
    (.u64 (wB + 1)) ρ₂ hevWM hevW hu₂
  have hr₂ : envLookup ρ₂ "r" = some (.u64 rB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("r" : String) ≠ "w" by decide) hu₂]
    exact hr₁
  have hrVarM₂ : memEvalExpr (.var "r") ρ₂ m₁ π =
      .ok (.u64 rB) :=
    (memEvalExpr_var _ _ _ _).trans
      (evalExpr_var_hit _ _ _ hr₂)
  have hevR : evalExpr (.uadd (.var "r")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ =
      .ok (.u64 (rB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hr₂) (by simp [evalExpr, litVal])
  have hevRM : memEvalExpr
      (.uadd (.var "r") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ m₁ π =
      .ok (.u64 (rB + 1)) :=
    (memEvalExpr_uadd_agree (.var "r") (.lit (.u64 (BitVec.ofNat 64 1)))
      ρ₂ m₁ π (memEvalExpr_var _ _ _ _)
      (memEvalExpr_lit _ _ _ _)).trans hevR
  obtain ⟨ρ₃, hu₃⟩ := envUpdate_some_of_lookup ρ₂ "r"
    (.u64 rB) (.u64 (rB + 1)) hr₂
  have hstep_r := memRevAssign prog F "r"
    (.uadd (.var "r") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ m₁ π
    (.u64 (rB + 1)) ρ₃ hevRM hevR hu₃
  have hout₃ : envLookup ρ₃ "v" =
      some (.stdVecVal (l.set w y)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("v" : String) ≠ "r" by decide) hu₃]
    rw [envLookup_update_miss _ _ _ _ _
      (show ("v" : String) ≠ "w" by decide) hu₂]
    have h := envLookup_update_hit _ _ _ _ hu₁
    rwa [hsetB] at h
  have hrN' : (rB + 1).toNat = r + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hrN]
    exact Nat.mod_eq_of_lt (by omega)
  have hwN' : (wB + 1).toNat = w + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hwN]
    exact Nat.mod_eq_of_lt (by omega)
  have hr' : envLookup ρ₃ "r" = some (.u64 (rB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₃
  have hw₂ : envLookup ρ₂ "w" = some (.u64 (wB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₂
  have hw' : envLookup ρ₃ "w" = some (.u64 (wB + 1)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "r" by decide) hu₃]
    exact hw₂
  have hthen : memEvalProgStmt prog F
      (.seq (.vecSet "v" (.var "w") (.stdVecAt "v" (.var "r")))
        (.assign "w" (.uadd (.var "w")
          (.lit (.u64 (BitVec.ofNat 64 1))))))
      ρ m π = .ok ((ρ₂, m₁, π), .fellThrough) := by
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep_set,
      hstep_w]
  have hif : memEvalProgStmt prog F
      (.if_ (.une (.stdVecAt "v" (.var "r")) vecUniquePrev)
        (.seq (.vecSet "v" (.var "w") (.stdVecAt "v" (.var "r")))
          (.assign "w" (.uadd (.var "w")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        .skip) ρ m π = .ok ((ρ₂, m₁, π), .fellThrough) :=
    (memEvalProgStmt_if_true prog F _ _ _ _ _ _ huneM).trans hthen
  have hbody : vecUniqueBody =
      (.seq (.if_ (.une (.stdVecAt "v" (.var "r")) vecUniquePrev)
          (.seq (.vecSet "v" (.var "w") (.stdVecAt "v" (.var "r")))
            (.assign "w" (.uadd (.var "w")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .skip)
        (.assign "r" (.uadd (.var "r")
          (.lit (.u64 (BitVec.ofNat 64 1)))))) := rfl
  have heval : memEvalProgStmt prog F vecUniqueBody ρ m π =
      .ok ((ρ₃, m₁, π), .fellThrough) := by
    rw [hbody,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hif,
      hstep_r]
  exact ⟨ρ₃, m₁, heval, hout₃, ⟨(rB + 1), hr', hrN'⟩,
    ⟨(wB + 1), hw', hwN'⟩, hmem₁⟩

/-- One body iteration on memory, drop branch: the `une` test
    against the predecessor fails, the state (env and memory)
    threads untouched, only `r` advances. -/
theorem memUniqueBody_drop (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (l : List (BitVec 32))
    (r w : Nat) (rB wB : BitVec 64) (y p : BitVec 32)
    (a t : Nat) (n : BitVec 32)
    (hlay : layoutLookup π "v" = some (a, t))
    (hmem : memFind m a = some ⟨t, true, n :: l⟩)
    (hn : n = BitVec.ofNat 32 l.length)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hrlt : r < l.length) (hw1 : 1 ≤ w)
    (hy : l[r]? = some y) (hp : l[w - 1]? = some p)
    (hdrop : (y != p) = false) :
    ∃ ρ', memEvalProgStmt prog F vecUniqueBody ρ m π =
      .ok ((ρ', m, π), .fellThrough) ∧
      envLookup ρ' "v" = some (.stdVecVal l) ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r + 1) ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w) ∧
      memFind m a = some ⟨t, true, n :: l⟩ := by
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
  have hwVar : evalExpr (.var "w") ρ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw
  have hrVarM : memEvalExpr (.var "r") ρ m π = .ok (.u64 rB) :=
    (memEvalExpr_var _ _ _ _).trans hrVar
  have hgetR : l[rB.toNat]? = some y := by rw [hrN]; exact hy
  have hmemR : memLoad m a t (rB.toNat + 1) = .ok y :=
    memLoad_cellsAt m a t (rB.toNat + 1) (n :: l) y
      hmem (by rw [List.getElem?_cons_succ]; exact hgetR)
  have hat : evalExpr (.stdVecAt "v" (.var "r")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hrVar hgetR
  have hatM_ag : memEvalExpr (.stdVecAt "v" (.var "r")) ρ m π =
      evalExpr (.stdVecAt "v" (.var "r")) ρ :=
    memEvalExpr_stdVecAt_hit "v" (.var "r") ρ m π l rB y a t
      hlay hv (memEvalExpr_var _ _ _ _) hrVar hmemR hgetR
  have hsub : evalExpr (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64)))) ρ =
      .ok (.u64 (wB - 1)) :=
    evalExpr_u64_usub wB 1 (.var "w") ρ hwVar
  have hsubN : (wB - 1).toNat = w - 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    have hno : ¬ BitVec.usubOverflow wB 1 := by
      rw [BitVec.usubOverflow, decide_eq_true_eq, hwN, h1]
      omega
    rw [BitVec.toNat_sub_of_not_usubOverflow hno, hwN, h1]
  have hsubM_ag : memEvalExpr (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64)))) ρ m π =
      evalExpr (.usub (.var "w") (.lit (.u64 (1 : BitVec 64)))) ρ :=
    memEvalExpr_usub_agree (.var "w") (.lit (.u64 (1 : BitVec 64)))
      ρ m π (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)
  have hgetP : l[(wB - 1).toNat]? = some p := by
    rw [hsubN]; exact hp
  have hmemP : memLoad m a t ((wB - 1).toNat + 1) = .ok p :=
    memLoad_cellsAt m a t ((wB - 1).toNat + 1) (n :: l) p
      hmem (by rw [List.getElem?_cons_succ]; exact hgetP)
  have hatP : evalExpr (.stdVecAt "v" (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64))))) ρ = .ok (.i32 p) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hsub hgetP
  have hatPM_ag : memEvalExpr vecUniquePrev ρ m π =
      evalExpr vecUniquePrev ρ :=
    memEvalExpr_stdVecAt_hit "v" (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64)))) ρ m π l (wB - 1) p a t
      hlay hv hsubM_ag hsub hmemP hgetP
  have huneV : evalExpr (.une (.stdVecAt "v" (.var "r"))
      vecUniquePrev) ρ = .ok (.b false) := by
    have h := evalExpr_une_i32 (.stdVecAt "v" (.var "r"))
      vecUniquePrev ρ y p hat hatP
    rwa [hdrop] at h
  have huneM : memEvalExpr (.une (.stdVecAt "v" (.var "r"))
      vecUniquePrev) ρ m π = .ok (.b false) :=
    (memEvalExpr_une_agree (.stdVecAt "v" (.var "r"))
      vecUniquePrev ρ m π hatM_ag hatPM_ag).trans huneV
  have hskipV : memEvalProgStmt prog F .skip ρ m π =
      .ok ((ρ, m, π), .fellThrough) := by
    cases F <;> simp [memEvalProgStmt, memEvalStmtFuel,
      memEvalStmtZero, memEvalStmtWith]
  have hif : memEvalProgStmt prog F
      (.if_ (.une (.stdVecAt "v" (.var "r")) vecUniquePrev)
        (.seq (.vecSet "v" (.var "w") (.stdVecAt "v" (.var "r")))
          (.assign "w" (.uadd (.var "w")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        .skip) ρ m π = .ok ((ρ, m, π), .fellThrough) :=
    (memEvalProgStmt_if_false prog F _ _ _ _ _ _ huneM).trans hskipV
  have hevR : evalExpr (.uadd (.var "r")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρ =
      .ok (.u64 (rB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      hrVar (by simp [evalExpr, litVal])
  have hevRM : memEvalExpr
      (.uadd (.var "r") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ m π =
      .ok (.u64 (rB + 1)) :=
    (memEvalExpr_uadd_agree (.var "r") (.lit (.u64 (BitVec.ofNat 64 1)))
      ρ m π (memEvalExpr_var _ _ _ _)
      (memEvalExpr_lit _ _ _ _)).trans hevR
  obtain ⟨ρ', hu⟩ := envUpdate_some_of_lookup ρ "r"
    (.u64 rB) (.u64 (rB + 1)) hr
  have hstep_r := memRevAssign prog F "r"
    (.uadd (.var "r") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ m π
    (.u64 (rB + 1)) ρ' hevRM hevR hu
  have hout' : envLookup ρ' "v" = some (.stdVecVal l) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("v" : String) ≠ "r" by decide) hu]
    exact hv
  have hw' : envLookup ρ' "w" = some (.u64 wB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "r" by decide) hu]
    exact hw
  have hrN' : (rB + 1).toNat = r + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hrN]
    exact Nat.mod_eq_of_lt (by omega)
  have hr' : envLookup ρ' "r" = some (.u64 (rB + 1)) :=
    envLookup_update_hit _ _ _ _ hu
  have hbody : vecUniqueBody =
      (.seq (.if_ (.une (.stdVecAt "v" (.var "r")) vecUniquePrev)
          (.seq (.vecSet "v" (.var "w") (.stdVecAt "v" (.var "r")))
            (.assign "w" (.uadd (.var "w")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .skip)
        (.assign "r" (.uadd (.var "r")
          (.lit (.u64 (BitVec.ofNat 64 1)))))) := rfl
  have heval : memEvalProgStmt prog F vecUniqueBody ρ m π =
      .ok ((ρ', m, π), .fellThrough) := by
    rw [hbody,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hif,
      hstep_r]
  exact ⟨ρ', heval, hout', ⟨(rB + 1), hr', hrN'⟩,
    ⟨wB, hw', hwN⟩, hmem⟩

/-! ## Memory loop induction -/

/-- Memory loop, ok leg: the scan runs to `l.length`, the block
    holds the forward-model words (fuel induction threading the
    memory body hits; the forward equation unfolds one step per
    iteration; the `1 ≤ w` seed fact justifies every predecessor
    read on both layers). -/
theorem memUniqueLoop_ok (prog : Prog) (F G : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (l : List (BitVec 32))
    (r w : Nat) (rB wB : BitVec 64)
    (l' : List (BitVec 32)) (r' w' : Nat)
    (a t : Nat) (n : BitVec 32)
    (hlay : layoutLookup π "v" = some (a, t))
    (hn : n = BitVec.ofNat 32 l.length)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hmem : memFind m a = some ⟨t, true, n :: l⟩)
    (hle : r ≤ l.length) (hwle : w ≤ r) (hw1 : 1 ≤ w)
    (hF : l.length - r ≤ F) (hG : l.length - r ≤ G)
    (hread : ∀ p, p < l.length → ∃ y, l[p]? = some y)
    (hfwd : uniqueFwd l G r w = .ok (r', w', l')) :
    ∃ ρ' m', memEvalProgStmt prog F vecUniqueLoop ρ m π =
      .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "v" = some (.stdVecVal l') ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r') ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w') ∧
      memFind m' a = some ⟨t, true, n :: l'⟩ := by
  induction F generalizing G ρ m l r w rB wB with
  | zero =>
    have him : r = l.length := by omega
    have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
    have hmemLen : memLoad m a t 0 =
        .ok (BitVec.ofNat 32 l.length) := by
      rw [← hn]
      exact memLoad_cellsAt m a t 0 (n :: l) n hmem (by simp)
    have hguardF : memEvalExpr
        (.ult (.var "r") (.stdVecLen "v")) ρ m π =
        .ok (.b false) := by
      have hag : memEvalExpr (.ult (.var "r") (.stdVecLen "v")) ρ m π =
          evalExpr (.ult (.var "r") (.stdVecLen "v")) ρ :=
        memEvalExpr_ult_agree (.var "r") (.stdVecLen "v") ρ m π
          (memEvalExpr_var _ _ _ _)
          (memEvalExpr_stdVecLen_hit "v" ρ m π l a t
            hlay hv hmemLen)
      have hval : evalExpr (.ult (.var "r") (.stdVecLen "v")) ρ =
          .ok (.b false) := by
        have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "v")
          ρ rB (BitVec.ofNat 64 l.length)
          (evalExpr_var_hit _ _ _ hr)
          (evalExpr_stdVecLen_some _ _ _ hv)
        have hfb : (rB.ult (BitVec.ofNat 64 l.length)) = false := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_false (by omega)
        rwa [hfb] at hult
      rw [hag]; exact hval
    have hexit : memEvalProgStmt prog 0 vecUniqueLoop ρ m π =
        .ok ((ρ, m, π), .fellThrough) :=
      memEvalProgStmt_while_false prog 0 _ _ _ _ _ hguardF
    have hpair : (r, w, l) = (r', w', l') := by
      cases G with
      | zero => simpa [uniqueFwd] using hfwd
      | succ G =>
        have hneg : ¬ r < l.length := by omega
        simpa [uniqueFwd, dite_eq_right hneg] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    exact ⟨ρ, m, hexit, hv, ⟨rB, hr, hrN⟩, ⟨wB, hw, hwN⟩,
      hmem⟩
  | succ F ih =>
    by_cases hlt : r < l.length
    · have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
      have hmemLen : memLoad m a t 0 =
          .ok (BitVec.ofNat 32 l.length) := by
        rw [← hn]
        exact memLoad_cellsAt m a t 0 (n :: l) n hmem (by simp)
      have hguardT : memEvalExpr
          (.ult (.var "r") (.stdVecLen "v")) ρ m π =
          .ok (.b true) := by
        have hag : memEvalExpr
            (.ult (.var "r") (.stdVecLen "v")) ρ m π =
            evalExpr (.ult (.var "r") (.stdVecLen "v")) ρ :=
          memEvalExpr_ult_agree (.var "r") (.stdVecLen "v") ρ m π
            (memEvalExpr_var _ _ _ _)
            (memEvalExpr_stdVecLen_hit "v" ρ m π l a t
              hlay hv hmemLen)
        have hval : evalExpr (.ult (.var "r") (.stdVecLen "v")) ρ =
            .ok (.b true) := by
          have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "v")
            ρ rB (BitVec.ofNat 64 l.length)
            (evalExpr_var_hit _ _ _ hr)
            (evalExpr_stdVecLen_some _ _ _ hv)
          have htb : (rB.ult (BitVec.ofNat 64 l.length)) = true := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_true (by omega)
          rwa [htb] at hult
        rw [hag]; exact hval
      obtain ⟨y, hy⟩ := hread r hlt
      have hwltM : w - 1 < l.length := by omega
      obtain ⟨p, hp⟩ := hread (w - 1) hwltM
      have hwlt : w < l.length := by omega
      obtain ⟨wOld, hwget⟩ := hread w hwlt
      cir_fuel_step (F, G, l.length - (r + 1))
      by_cases hkeep : (y != p) = true
      · have hle' : r + 1 ≤ (l.set w y).length := by
          have : (l.set w y).length = l.length := by
            simp [List.length_set]
          omega
        have hwle' : w + 1 ≤ r + 1 := by omega
        have hw1' : 1 ≤ w + 1 := by omega
        have hread' : ∀ p, p < (l.set w y).length →
            ∃ z, (l.set w y)[p]? = some z := by
          intro p hp
          have hplen : p < l.length := by
            have : (l.set w y).length = l.length := by
              simp [List.length_set]
            omega
          by_cases hpw : p = w
          · rw [hpw]
            exact ⟨y, List.getElem?_set_self hwlt⟩
          · obtain ⟨z, hz⟩ := hread p hplen
            exact ⟨z, by
              rw [List.getElem?_set_ne (show w ≠ p by omega)]
              exact hz⟩
        obtain ⟨ρ₁, m₁, hbody, hout₁, ⟨rB₁, hrB₁, hrN₁⟩,
            ⟨wB₁, hwB₁, hwN₁⟩, hmem₁⟩ :=
          memUniqueBody_keep prog F ρ m π l r w rB wB y p wOld
            a t n hlay hmem hn hrN hwN hl64 hv hr hw
            hlt hw1 hy hp hwget hwlt hkeep
        have hlen : (l.set w y).length = l.length := by
          simp [List.length_set]
        have hlo64' : (l.set w y).length < 2 ^ 64 := by
          rw [hlen]; exact hl64
        have hn' : n = BitVec.ofNat 32 (l.set w y).length := by
          rw [hlen]; exact hn
        have hF'' : (l.set w y).length - (r + 1) ≤ F := by omega
        have hG'' : (l.set w y).length - (r + 1) ≤ G' := by omega
        have hfwd' : uniqueFwd (l.set w y) G' (r + 1) (w + 1) =
            .ok (r', w', l') := by
          have h := hfwd
          simp only [uniqueFwd, dite_eq_left hlt, hy, hp, hkeep] at h
          exact h
        obtain ⟨ρ', m', hloop, hout', ⟨rB', hrB', hrN'⟩,
            ⟨wB', hwB', hwN'⟩, hmem'⟩ :=
          ih (G := G') (ρ := ρ₁) (m := m₁) (l := l.set w y)
            (r := r + 1) (w := w + 1) (rB := rB₁) (wB := wB₁)
            (hn := hn') (hrN := hrN₁) (hwN := hwN₁) (hl64 := hlo64')
            (hv := hout₁) (hr := hrB₁) (hw := hwB₁)
            (hmem := hmem₁) (hle := hle') (hwle := hwle')
            (hw1 := hw1') (hF := hF'') (hG := hG'')
            (hread := hread') (hfwd := hfwd')
        refine ⟨ρ', m', ?_, hout', ⟨rB', hrB', hrN'⟩,
          ⟨wB', hwB', hwN'⟩, hmem'⟩
        have hwhile : memEvalProgStmt prog (F + 1) vecUniqueLoop ρ m π =
            memEvalProgStmt prog F vecUniqueLoop ρ₁ m₁ π := by
          cir_unfold_prog (vecUniqueLoop, prog, F, hguardT, hbody)
        rw [hwhile]
        exact hloop
      · have hdrop : (y != p) = false := by
          cases h : (y != p) with
          | true => exact absurd h hkeep
          | false => rfl
        obtain ⟨ρ₁, hbody, hout₁, ⟨rB₁, hrB₁, hrN₁⟩,
            ⟨wB₁, hwB₁, hwN₁⟩, hmem₁⟩ :=
          memUniqueBody_drop prog F ρ m π l r w rB wB y p
            a t n hlay hmem hn hrN hwN hl64 hv hr hw
            hlt hw1 hy hp hdrop
        have hwle' : w ≤ r + 1 := by omega
        have hfwd' : uniqueFwd l G' (r + 1) w =
            .ok (r', w', l') := by
          have h := hfwd
          simp only [uniqueFwd, dite_eq_left hlt, hy, hp, hdrop] at h
          exact h
        obtain ⟨ρ', m', hloop, hout', ⟨rB', hrB', hrN'⟩,
            ⟨wB', hwB', hwN'⟩, hmem'⟩ :=
          ih (G := G') (ρ := ρ₁) (m := m) (l := l)
            (r := r + 1) (w := w) (rB := rB₁) (wB := wB₁)
            (hn := hn) (hrN := hrN₁) (hwN := hwN₁) (hl64 := hl64)
            (hv := hout₁) (hr := hrB₁) (hw := hwB₁)
            (hmem := hmem₁) (hle := by omega) (hwle := hwle')
            (hw1 := hw1) (hF := hF') (hG := hG')
            (hread := hread) (hfwd := hfwd')
        refine ⟨ρ', m', ?_, hout', ⟨rB', hrB', hrN'⟩,
          ⟨wB', hwB', hwN'⟩, hmem'⟩
        have hwhile : memEvalProgStmt prog (F + 1) vecUniqueLoop ρ m π =
            memEvalProgStmt prog F vecUniqueLoop ρ₁ m π := by
          cir_unfold_prog (vecUniqueLoop, prog, F, hguardT, hbody)
        rw [hwhile]
        exact hloop
    · have him : r = l.length := by omega
      subst him
      have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
      have hmemLen : memLoad m a t 0 =
          .ok (BitVec.ofNat 32 l.length) := by
        rw [← hn]
        exact memLoad_cellsAt m a t 0 (n :: l) n hmem (by simp)
      have hguardF : memEvalExpr
          (.ult (.var "r") (.stdVecLen "v")) ρ m π =
          .ok (.b false) := by
        have hag : memEvalExpr (.ult (.var "r") (.stdVecLen "v")) ρ m π =
            evalExpr (.ult (.var "r") (.stdVecLen "v")) ρ :=
          memEvalExpr_ult_agree (.var "r") (.stdVecLen "v") ρ m π
            (memEvalExpr_var _ _ _ _)
            (memEvalExpr_stdVecLen_hit "v" ρ m π l a t
              hlay hv hmemLen)
        have hval : evalExpr (.ult (.var "r") (.stdVecLen "v")) ρ =
            .ok (.b false) := by
          have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "v")
            ρ rB (BitVec.ofNat 64 l.length)
            (evalExpr_var_hit _ _ _ hr)
            (evalExpr_stdVecLen_some _ _ _ hv)
          have hfb : (rB.ult (BitVec.ofNat 64 l.length)) = false := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_false (by omega)
          rwa [hfb] at hult
        rw [hag]; exact hval
      have hexit : memEvalProgStmt prog (F + 1) vecUniqueLoop ρ m π =
          .ok ((ρ, m, π), .fellThrough) :=
        memEvalProgStmt_while_false prog (F + 1) _ _ _ _ _ hguardF
      have hpair : (l.length, w, l) = (r', w', l') := by
        cases G with
        | zero => simpa [uniqueFwd] using hfwd
        | succ G =>
          have hneg : ¬ l.length < l.length := by omega
          simpa [uniqueFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      exact ⟨ρ, m, hexit, hv, ⟨rB, hr, hrN⟩, ⟨wB, hw, hwN⟩,
        hmem⟩

/-! ## Entry bridges (empty early exit + seeded scan) -/

/-- Value entry on empty: the length guard fires, the early
    exit returns 0. -/
theorem evalProgFunc_vecUnique_nil (F : Nat) :
    evalProgFunc vecUniqueProg F vecUniqueFunc
      [.stdVecVal ([] : List (BitVec 32))] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
  have hbind : bindArgs vecUniqueFunc.args [.stdVecVal []] =
      some [("v", .stdVecVal ([] : List (BitVec 32)))] := rfl
  have hbody : vecUniqueFunc.body =
      (.seq (.if_ (.ueq (.stdVecLen "v")
                  (.lit (.u64 (BitVec.ofNat 64 0))))
            (.return_ (.lit (.u64 (BitVec.ofNat 64 0))))
            .skip)
        (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
          (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
            (.seq vecUniqueLoop
              (.return_ (.var "w")))))) := rfl
  have hv : envLookup [("v", .stdVecVal ([] : List (BitVec 32)))]
      "v" = some (.stdVecVal []) := by simp [envLookup]
  have hlenV : evalExpr (.stdVecLen "v")
      [("v", .stdVecVal ([] : List (BitVec 32)))] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    have h := evalExpr_stdVecLen_some "v"
      [("v", .stdVecVal ([] : List (BitVec 32)))] [] hv
    simpa using h
  have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("v", .stdVecVal ([] : List (BitVec 32)))] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hguardT : evalExpr (.ueq (.stdVecLen "v")
      (.lit (.u64 (BitVec.ofNat 64 0))))
      [("v", .stdVecVal ([] : List (BitVec 32)))] =
      .ok (.b true) := by
    have hlenN : (BitVec.ofNat 64 ([] : List (BitVec 32)).length).toNat =
        ([] : List (BitVec 32)).length := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by simp)
    have h := evalExpr_ueq_u64_vars (.stdVecLen "v")
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("v", .stdVecVal ([] : List (BitVec 32)))]
      (BitVec.ofNat 64 ([] : List (BitVec 32)).length)
      (BitVec.ofNat 64 0) hlenV hlitV
    simpa [hlenN] using h
  have hif := evalProgStmt_if_true vecUniqueProg F
    (.ueq (.stdVecLen "v") (.lit (.u64 (BitVec.ofNat 64 0))))
    (.return_ (.lit (.u64 (BitVec.ofNat 64 0)))) .skip
    [("v", .stdVecVal ([] : List (BitVec 32)))] hguardT
  have hret := evalProgStmt_return vecUniqueProg F
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("v", .stdVecVal ([] : List (BitVec 32)))]
    (.u64 (BitVec.ofNat 64 0)) hlitV
  simp only [evalProgFunc, hbind, hbody]
  rw [evalProgStmt_seq_returned _ _ _ _ _ _ _ (hif.trans hret)]

/-- Value entry: the empty input exits early; otherwise the
    guard fails, the prelude seeds `(1, 1)`, the loop runs, and
    the new logical length returns. -/
theorem evalProgFunc_vecUnique_ok (F : Nat)
    (l l' : List (BitVec 32)) (w' : Nat)
    (hl64 : l.length < 2 ^ 64)
    (hF : l.length ≤ F)
    (hread : ∀ p, p < l.length → ∃ y, l[p]? = some y)
    (hfwd : uniqueFwd l l.length 1 1 = .ok (l.length, w', l')) :
    evalProgFunc vecUniqueProg F vecUniqueFunc
      [.stdVecVal l] =
      .ok (.u64 (BitVec.ofNat 64 w')) := by
  have hbind : bindArgs vecUniqueFunc.args [.stdVecVal l] =
      some [("v", .stdVecVal l)] := rfl
  have hbody : vecUniqueFunc.body =
      (.seq (.if_ (.ueq (.stdVecLen "v")
                  (.lit (.u64 (BitVec.ofNat 64 0))))
            (.return_ (.lit (.u64 (BitVec.ofNat 64 0))))
            .skip)
        (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
          (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
            (.seq vecUniqueLoop
              (.return_ (.var "w")))))) := rfl
  cases hl : l with
  | nil =>
    subst hl
    simpa [uniqueFwd] using hfwd
  | cons x xs =>
    subst hl
    have hv₀ : envLookup [("v", .stdVecVal (x :: xs))] "v" =
        some (.stdVecVal (x :: xs)) := by simp [envLookup]
    have hlenV : evalExpr (.stdVecLen "v")
        [("v", .stdVecVal (x :: xs))] =
        .ok (.u64 (BitVec.ofNat 64 (x :: xs).length)) :=
      evalExpr_stdVecLen_some _ _ _ hv₀
    have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("v", .stdVecVal (x :: xs))] =
        .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
    have hlenN : (BitVec.ofNat 64 (x :: xs).length).toNat =
        (x :: xs).length := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hl64
    have hpos : 0 < (x :: xs).length := by simp
    have hnn : BitVec.ofNat 64 (x :: xs).length ≠ BitVec.ofNat 64 0 := by
      intro hcon
      have h0 := congrArg BitVec.toNat hcon
      rw [hlenN] at h0
      simp at h0
    have hbeq : (BitVec.ofNat 64 (x :: xs).length ==
        BitVec.ofNat 64 0) = false :=
      beq_eq_false_iff_ne.mpr hnn
    have hguardF : evalExpr (.ueq (.stdVecLen "v")
        (.lit (.u64 (BitVec.ofNat 64 0))))
        [("v", .stdVecVal (x :: xs))] = .ok (.b false) := by
      have h := evalExpr_ueq_u64_vars (.stdVecLen "v")
        (.lit (.u64 (BitVec.ofNat 64 0)))
        [("v", .stdVecVal (x :: xs))]
        (BitVec.ofNat 64 (x :: xs).length)
        (BitVec.ofNat 64 0) hlenV hlitV
      rwa [hbeq] at h
    have hif := evalProgStmt_if_false vecUniqueProg F
      (.ueq (.stdVecLen "v") (.lit (.u64 (BitVec.ofNat 64 0))))
      (.return_ (.lit (.u64 (BitVec.ofNat 64 0)))) .skip
      [("v", .stdVecVal (x :: xs))] hguardF
    have hskipV : evalProgStmt vecUniqueProg F .skip
        [("v", .stdVecVal (x :: xs))] =
        .ok ([("v", .stdVecVal (x :: xs))], .fellThrough) := by
      simpa [evalProgStmt] using
        (show evalStmtFuel F .skip [("v", .stdVecVal (x :: xs))] =
          .ok ([("v", .stdVecVal (x :: xs))], .fellThrough) by
          cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith])
    have hfall : evalProgStmt vecUniqueProg F
        (.if_ (.ueq (.stdVecLen "v") (.lit (.u64 (BitVec.ofNat 64 0))))
          (.return_ (.lit (.u64 (BitVec.ofNat 64 0)))) .skip)
        [("v", .stdVecVal (x :: xs))] =
        .ok ([("v", .stdVecVal (x :: xs))], .fellThrough) :=
      hif.trans hskipV
    have h1N : (BitVec.ofNat 64 1).toNat = 1 := by decide
    have hlitW : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        [("v", .stdVecVal (x :: xs))] =
        .ok (.u64 (BitVec.ofNat 64 1)) := by simp [evalExpr, litVal]
    have hletW := revLet vecUniqueProg F "w" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 1)))
      [("v", .stdVecVal (x :: xs))]
      (.u64 (BitVec.ofNat 64 1)) hlitW
    have hlitR : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        (envExtend [("v", .stdVecVal (x :: xs))]
          "w" (.u64 (BitVec.ofNat 64 1))) =
        .ok (.u64 (BitVec.ofNat 64 1)) := by simp [evalExpr, litVal]
    have hletR := revLet vecUniqueProg F "r" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 1)))
      (envExtend [("v", .stdVecVal (x :: xs))]
        "w" (.u64 (BitVec.ofNat 64 1)))
      (.u64 (BitVec.ofNat 64 1)) hlitR
    have hv₁ : envLookup (envExtend (envExtend
        [("v", .stdVecVal (x :: xs))]
        "w" (.u64 (BitVec.ofNat 64 1)))
        "r" (.u64 (BitVec.ofNat 64 1))) "v" =
        some (.stdVecVal (x :: xs)) := by
      rw [envExtend_miss _ _ _ _
        (show ("v" : String) ≠ "r" by decide),
        envExtend_miss _ _ _ _
        (show ("v" : String) ≠ "w" by decide)]
      simp [envLookup]
    have hw₁ : envLookup (envExtend (envExtend
        [("v", .stdVecVal (x :: xs))]
        "w" (.u64 (BitVec.ofNat 64 1)))
        "r" (.u64 (BitVec.ofNat 64 1))) "w" =
        some (.u64 (BitVec.ofNat 64 1)) := by
      rw [envExtend_miss _ _ _ _
        (show ("w" : String) ≠ "r" by decide)]
      exact envExtend_hit _ _ _
    have hr₁ : envLookup (envExtend (envExtend
        [("v", .stdVecVal (x :: xs))]
        "w" (.u64 (BitVec.ofNat 64 1)))
        "r" (.u64 (BitVec.ofNat 64 1))) "r" =
        some (.u64 (BitVec.ofNat 64 1)) :=
      envExtend_hit _ _ _
    have hlen1 : 1 ≤ (x :: xs).length := by simp
    obtain ⟨ρ', hloop, hout', ⟨rB', hrB', hrN'⟩,
        ⟨wB', hwB', hwN'⟩⟩ :=
      valUniqueLoop_ok vecUniqueProg F (x :: xs).length
        (envExtend (envExtend [("v", .stdVecVal (x :: xs))]
          "w" (.u64 (BitVec.ofNat 64 1)))
          "r" (.u64 (BitVec.ofNat 64 1)))
        (x :: xs) 1 1 (BitVec.ofNat 64 1) (BitVec.ofNat 64 1)
        l' (x :: xs).length w'
        h1N h1N hl64 hv₁ hr₁ hw₁
        hlen1 (Nat.le_refl _) (Nat.le_refl _) (by omega) (by omega)
        hread hfwd
    have hbw : w' ≤ (x :: xs).length := by
      obtain ⟨h1, -⟩ := uniqueFwd_bounds (x :: xs) l'
        ((x :: xs).length) 1 1 _ w' (Nat.le_refl _)
        (Nat.le_refl _) hfwd
      exact h1
    have hwEq : wB' = BitVec.ofNat 64 w' := by
      apply BitVec.eq_of_toNat_eq
      rw [hwN', BitVec.toNat_ofNat]
      exact (Nat.mod_eq_of_lt (by omega : w' < 2 ^ 64)).symm
    have hret := evalProgStmt_return vecUniqueProg F
      (.var "w") ρ' (.u64 wB')
      (evalExpr_var_hit _ _ _ hwB')
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hfall,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletW,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletR,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hloop,
      hret, hwEq]

/-- Memory entry: the `w`/`r` prelude runs on memory, the loop
    closes against the forward model, the new logical length
    returns. The entry guard is decided on both layers; the
    empty-input case is vacuous against the forward contract
    (the `(1, 1)` seed never satisfies the forward equation
    at length `0`). -/
theorem memEvalProgFunc_vecUnique_ok (F : Nat)
    (l l' : List (BitVec 32)) (w' : Nat)
    (hl64 : l.length < 2 ^ 64)
    (hF : l.length ≤ F)
    (hread : ∀ p, p < l.length → ∃ y, l[p]? = some y)
    (hfwd : uniqueFwd l l.length 1 1 = .ok (l.length, w', l')) :
    memEvalProgFunc vecUniqueProg F vecUniqueFunc
      [.stdVecVal l] =
      .ok (.u64 (BitVec.ofNat 64 w')) := by
  have hbind := bindMemArgs_vecUnique l
  have hbody : vecUniqueFunc.body =
      (.seq (.if_ (.ueq (.stdVecLen "v")
                  (.lit (.u64 (BitVec.ofNat 64 0))))
            (.return_ (.lit (.u64 (BitVec.ofNat 64 0))))
            .skip)
        (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
          (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
            (.seq vecUniqueLoop
              (.return_ (.var "w")))))) := rfl
  have hmem : memFind
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ 0 =
      some ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩ :=
    memFind_cons_hit _ _ _ _ _
  have hlay : layoutLookup [("v", 0, 0)] "v" =
      some (0, 0) := by simp [layoutLookup]
  cases hl : l with
  | nil =>
    subst hl
    simpa [uniqueFwd] using hfwd
  | cons x xs =>
    subst hl
    have h1N : (BitVec.ofNat 64 1).toNat = 1 := by decide
    have hv₀ : envLookup [("v", .stdVecVal (x :: xs))] "v" =
        some (.stdVecVal (x :: xs)) := by simp [envLookup]
    have hlenV : evalExpr (.stdVecLen "v")
        [("v", .stdVecVal (x :: xs))] =
        .ok (.u64 (BitVec.ofNat 64 (x :: xs).length)) :=
      evalExpr_stdVecLen_some _ _ _ hv₀
    have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("v", .stdVecVal (x :: xs))] =
        .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
    have hlenN : (BitVec.ofNat 64 (x :: xs).length).toNat =
        (x :: xs).length := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hl64
    have hpos : 0 < (x :: xs).length := by simp
    have hnn : BitVec.ofNat 64 (x :: xs).length ≠ BitVec.ofNat 64 0 := by
      intro hcon
      have h0 := congrArg BitVec.toNat hcon
      rw [hlenN] at h0
      simp at h0
    have hbeq : (BitVec.ofNat 64 (x :: xs).length ==
        BitVec.ofNat 64 0) = false :=
      beq_eq_false_iff_ne.mpr hnn
    have hguardF : evalExpr (.ueq (.stdVecLen "v")
        (.lit (.u64 (BitVec.ofNat 64 0))))
        [("v", .stdVecVal (x :: xs))] = .ok (.b false) := by
      have h := evalExpr_ueq_u64_vars (.stdVecLen "v")
        (.lit (.u64 (BitVec.ofNat 64 0)))
        [("v", .stdVecVal (x :: xs))]
        (BitVec.ofNat 64 (x :: xs).length)
        (BitVec.ofNat 64 0) hlenV hlitV
      rwa [hbeq] at h
    have hmemLen : memLoad
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 (x :: xs).length) :: (x :: xs)⟩)], []⟩
        0 0 0 =
        .ok (BitVec.ofNat 32 (x :: xs).length) :=
      memLoad_cellsAt _ 0 0 0 _ _ hmem (by simp)
    have hcondF : memEvalExpr (.ueq (.stdVecLen "v")
        (.lit (.u64 (BitVec.ofNat 64 0))))
        [("v", .stdVecVal (x :: xs))]
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 (x :: xs).length) :: (x :: xs)⟩)], []⟩
        [("v", 0, 0)] = .ok (.b false) := by
      have hag := memEvalExpr_ueq_agree (.stdVecLen "v")
        (.lit (.u64 (BitVec.ofNat 64 0)))
        [("v", .stdVecVal (x :: xs))]
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 (x :: xs).length) :: (x :: xs)⟩)], []⟩
        [("v", 0, 0)]
        (memEvalExpr_stdVecLen_hit "v" _ _ _ _ 0 0 hlay hv₀ hmemLen)
        (memEvalExpr_lit _ _ _ _)
      rw [hag]; exact hguardF
    have hifF := memEvalProgStmt_if_false vecUniqueProg F
      (.ueq (.stdVecLen "v") (.lit (.u64 (BitVec.ofNat 64 0))))
      (.return_ (.lit (.u64 (BitVec.ofNat 64 0)))) .skip
      [("v", .stdVecVal (x :: xs))]
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 (x :: xs).length) :: (x :: xs)⟩)], []⟩
      [("v", 0, 0)] hcondF
    have hskipM : memEvalProgStmt vecUniqueProg F .skip
        [("v", .stdVecVal (x :: xs))]
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 (x :: xs).length) :: (x :: xs)⟩)], []⟩
        [("v", 0, 0)] =
        .ok (([("v", .stdVecVal (x :: xs))],
          ⟨1, [(0, ⟨0, true,
            (BitVec.ofNat 32 (x :: xs).length) :: (x :: xs)⟩)], []⟩,
          [("v", 0, 0)]), .fellThrough) := by
      cases F <;> simp [memEvalProgStmt, memEvalStmtFuel,
        memEvalStmtZero, memEvalStmtWith]
    have hfallM := hifF.trans hskipM
    have hlitM : memEvalExpr
        (.lit (.u64 (BitVec.ofNat 64 1)))
        [("v", .stdVecVal (x :: xs))]
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 (x :: xs).length) :: (x :: xs)⟩)], []⟩
        [("v", 0, 0)] =
        evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
          [("v", .stdVecVal (x :: xs))] :=
      memEvalExpr_lit _ _ _ _
    have hlitW : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        [("v", .stdVecVal (x :: xs))] =
        .ok (.u64 (BitVec.ofNat 64 1)) := by simp [evalExpr, litVal]
    have hletW := memRevLet vecUniqueProg F "w" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 1)))
      [("v", .stdVecVal (x :: xs))]
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 (x :: xs).length) :: (x :: xs)⟩)], []⟩
      [("v", 0, 0)] (.u64 (BitVec.ofNat 64 1))
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) (by intro h; cases h) hlitM hlitW
    have hlitRM : memEvalExpr
        (.lit (.u64 (BitVec.ofNat 64 1)))
        (envExtend [("v", .stdVecVal (x :: xs))]
          "w" (.u64 (BitVec.ofNat 64 1)))
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 (x :: xs).length) :: (x :: xs)⟩)], []⟩
        [("v", 0, 0)] =
        evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
          (envExtend [("v", .stdVecVal (x :: xs))]
            "w" (.u64 (BitVec.ofNat 64 1))) :=
      memEvalExpr_lit _ _ _ _
    have hlitR : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        (envExtend [("v", .stdVecVal (x :: xs))]
          "w" (.u64 (BitVec.ofNat 64 1))) =
        .ok (.u64 (BitVec.ofNat 64 1)) := by simp [evalExpr, litVal]
    have hletR := memRevLet vecUniqueProg F "r" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 1)))
      (envExtend [("v", .stdVecVal (x :: xs))]
        "w" (.u64 (BitVec.ofNat 64 1)))
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 (x :: xs).length) :: (x :: xs)⟩)], []⟩
      [("v", 0, 0)] (.u64 (BitVec.ofNat 64 1))
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) (by intro h; cases h) hlitRM hlitR
    have hv₁ : envLookup (envExtend (envExtend
        [("v", .stdVecVal (x :: xs))]
        "w" (.u64 (BitVec.ofNat 64 1)))
        "r" (.u64 (BitVec.ofNat 64 1))) "v" =
        some (.stdVecVal (x :: xs)) := by
      rw [envExtend_miss _ _ _ _
        (show ("v" : String) ≠ "r" by decide),
        envExtend_miss _ _ _ _
        (show ("v" : String) ≠ "w" by decide)]
      simp [envLookup]
    have hw₁ : envLookup (envExtend (envExtend
        [("v", .stdVecVal (x :: xs))]
        "w" (.u64 (BitVec.ofNat 64 1)))
        "r" (.u64 (BitVec.ofNat 64 1))) "w" =
        some (.u64 (BitVec.ofNat 64 1)) := by
      rw [envExtend_miss _ _ _ _
        (show ("w" : String) ≠ "r" by decide)]
      exact envExtend_hit _ _ _
    have hr₁ : envLookup (envExtend (envExtend
        [("v", .stdVecVal (x :: xs))]
        "w" (.u64 (BitVec.ofNat 64 1)))
        "r" (.u64 (BitVec.ofNat 64 1))) "r" =
        some (.u64 (BitVec.ofNat 64 1)) :=
      envExtend_hit _ _ _
    have hlen1 : 1 ≤ (x :: xs).length := by simp
    obtain ⟨ρ', m', hloop, hout', ⟨rB', hrB', hrN'⟩,
        ⟨wB', hwB', hwN'⟩, hmem'⟩ :=
      memUniqueLoop_ok vecUniqueProg F (x :: xs).length
        (envExtend (envExtend [("v", .stdVecVal (x :: xs))]
          "w" (.u64 (BitVec.ofNat 64 1)))
          "r" (.u64 (BitVec.ofNat 64 1)))
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 (x :: xs).length) :: (x :: xs)⟩)], []⟩
        [("v", 0, 0)]
        (x :: xs) 1 1 (BitVec.ofNat 64 1) (BitVec.ofNat 64 1)
        l' (x :: xs).length w' 0 0
        (BitVec.ofNat 32 (x :: xs).length)
        hlay rfl h1N h1N hl64 hv₁ hr₁ hw₁ hmem
        hlen1 (Nat.le_refl _) (Nat.le_refl _) (by omega) (by omega)
        hread hfwd
    have hwEq : wB' = BitVec.ofNat 64 w' := by
      have hb : w' ≤ (x :: xs).length := by
        obtain ⟨h1, -⟩ := uniqueFwd_bounds (x :: xs) l'
          ((x :: xs).length) 1 1 _ w' (Nat.le_refl _)
          (Nat.le_refl _) hfwd
        exact h1
      apply BitVec.eq_of_toNat_eq
      rw [hwN', BitVec.toNat_ofNat]
      exact (Nat.mod_eq_of_lt (by omega : w' < 2 ^ 64)).symm
    have hretM := memEvalProgStmt_return vecUniqueProg F
      (.var "w") ρ' m' [("v", 0, 0)]
      (.u64 wB')
      ((memEvalExpr_var _ _ _ _).trans
        (evalExpr_var_hit _ _ _ hwB'))
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hfallM,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletW,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletR,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hloop,
      hretM, hwEq]

/-- Memory nil: the empty input exits early with `0` on the
    memory layer (the entry guard agrees with the value
    guard through `memEvalExpr_ueq_agree`). -/
theorem memEvalProgFunc_vecUnique_nil (F : Nat) :
    memEvalProgFunc vecUniqueProg F vecUniqueFunc
      [.stdVecVal ([] : List (BitVec 32))] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
  have hbind := bindMemArgs_vecUnique ([] : List (BitVec 32))
  have hbody : vecUniqueFunc.body =
      (.seq (.if_ (.ueq (.stdVecLen "v")
                  (.lit (.u64 (BitVec.ofNat 64 0))))
            (.return_ (.lit (.u64 (BitVec.ofNat 64 0))))
            .skip)
        (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
          (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
            (.seq vecUniqueLoop
              (.return_ (.var "w")))))) := rfl
  have hmem : memFind
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
          ([] : List (BitVec 32))⟩)], []⟩ 0 =
      some ⟨0, true, (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
        ([] : List (BitVec 32))⟩ :=
    memFind_cons_hit _ _ _ _ _
  have hlay : layoutLookup [("v", 0, 0)] "v" =
      some (0, 0) := by simp [layoutLookup]
  have hv₀ : envLookup [("v", .stdVecVal ([] : List (BitVec 32)))] "v" =
      some (.stdVecVal ([] : List (BitVec 32))) := by simp [envLookup]
  have hlenV : evalExpr (.stdVecLen "v")
      [("v", .stdVecVal ([] : List (BitVec 32)))] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    have h := evalExpr_stdVecLen_some "v"
      [("v", .stdVecVal ([] : List (BitVec 32)))] [] hv₀
    simpa using h
  have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("v", .stdVecVal ([] : List (BitVec 32)))] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hguardT : evalExpr (.ueq (.stdVecLen "v")
      (.lit (.u64 (BitVec.ofNat 64 0))))
      [("v", .stdVecVal ([] : List (BitVec 32)))] =
      .ok (.b true) := by
    have hlenN : (BitVec.ofNat 64 ([] : List (BitVec 32)).length).toNat =
        ([] : List (BitVec 32)).length := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by simp)
    have h := evalExpr_ueq_u64_vars (.stdVecLen "v")
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("v", .stdVecVal ([] : List (BitVec 32)))]
      (BitVec.ofNat 64 ([] : List (BitVec 32)).length)
      (BitVec.ofNat 64 0) hlenV hlitV
    simpa [hlenN] using h
  have hmemLen : memLoad
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
          ([] : List (BitVec 32))⟩)], []⟩ 0 0 0 =
      .ok (BitVec.ofNat 32 ([] : List (BitVec 32)).length) :=
    memLoad_cellsAt _ 0 0 0 _ _ hmem (by simp)
  have hcondT : memEvalExpr (.ueq (.stdVecLen "v")
      (.lit (.u64 (BitVec.ofNat 64 0))))
      [("v", .stdVecVal ([] : List (BitVec 32)))]
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
          ([] : List (BitVec 32))⟩)], []⟩
      [("v", 0, 0)] = .ok (.b true) := by
    have hag := memEvalExpr_ueq_agree (.stdVecLen "v")
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("v", .stdVecVal ([] : List (BitVec 32)))]
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
          ([] : List (BitVec 32))⟩)], []⟩
      [("v", 0, 0)]
      (memEvalExpr_stdVecLen_hit "v" _ _ _ _ 0 0 hlay hv₀ hmemLen)
      (memEvalExpr_lit _ _ _ _)
    rw [hag]; exact hguardT
  have hifT := memEvalProgStmt_if_true vecUniqueProg F
    (.ueq (.stdVecLen "v") (.lit (.u64 (BitVec.ofNat 64 0))))
    (.return_ (.lit (.u64 (BitVec.ofNat 64 0)))) .skip
    [("v", .stdVecVal ([] : List (BitVec 32)))]
    ⟨1, [(0, ⟨0, true,
      (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
        ([] : List (BitVec 32))⟩)], []⟩
    [("v", 0, 0)] hcondT
  have hretM := memEvalProgStmt_return vecUniqueProg F
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("v", .stdVecVal ([] : List (BitVec 32)))]
    ⟨1, [(0, ⟨0, true,
      (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
        ([] : List (BitVec 32))⟩)], []⟩
    [("v", 0, 0)] (.u64 (BitVec.ofNat 64 0))
    ((memEvalExpr_lit _ _ _ _).trans hlitV)
  simp only [memEvalProgFunc, hbind, hbody]
  rw [memEvalProgStmt_seq_returned _ _ _ _ _ _ _ _ _ _ _
    (hifT.trans hretM)]

/-- Transfer for `vec_unique`: memory evaluation agrees with
    value evaluation (single ok leg — the kernel is total). -/
theorem memTransferProg_vecUnique_ok (F : Nat)
    (l : List (BitVec 32))
    (hl64 : l.length < 2 ^ 64)
    (hF : l.length ≤ F)
    (hread : ∀ p, p < l.length → ∃ y, l[p]? = some y)
    (_h : oracleNoalias vecUniqueFunc
      [.stdVecVal l]) :
    memEvalProgFunc vecUniqueProg F vecUniqueFunc
      [.stdVecVal l] =
      evalProgFunc vecUniqueProg F vecUniqueFunc
        [.stdVecVal l] := by
  cases l with
  | nil =>
    rw [memEvalProgFunc_vecUnique_nil F, evalProgFunc_vecUnique_nil F]
  | cons x xs =>
    have hlen1 : 1 ≤ (x :: xs).length := by simp
    obtain ⟨w', l', heq⟩ := uniqueFwd_ok (x :: xs)
      ((x :: xs).length) 1 1 hlen1 (Nat.le_refl _) (Nat.le_refl _)
      (Nat.sub_le _ _) hread
    rw [memEvalProgFunc_vecUnique_ok F (x :: xs) l' w' hl64 hF
      hread heq,
      evalProgFunc_vecUnique_ok F (x :: xs) l' w' hl64 hF hread heq]

/-- Closing squeeze contract (P2-M13): the kernel returns the
    new logical length — the squeezed length — bounded by the
    input length (the caller owes the `erase`: the tail past
    the returned length is don't-care). -/
theorem evalProgFunc_vecUnique_spec (F : Nat)
    (l : List (BitVec 32))
    (hl64 : l.length < 2 ^ 64)
    (hF : l.length ≤ F)
    (hread : ∀ p, p < l.length → ∃ y, l[p]? = some y) :
    ∃ w', evalProgFunc vecUniqueProg F vecUniqueFunc
      [.stdVecVal l] = .ok (.u64 (BitVec.ofNat 64 w')) ∧
      w' = (dedupAdj l).length ∧
      w' ≤ l.length := by
  cases l with
  | nil =>
    refine ⟨0, evalProgFunc_vecUnique_nil F, ?_, by simp⟩
    simp [dedupAdj]
  | cons x xs =>
    have hlen1 : 1 ≤ (x :: xs).length := by simp
    obtain ⟨w', l', hfwd⟩ := uniqueFwd_ok (x :: xs)
      ((x :: xs).length) 1 1 hlen1 (Nat.le_refl _) (Nat.le_refl _)
      (Nat.sub_le _ _) hread
    obtain ⟨hpre, -, hlen'⟩ := uniqueFwd_prefix (x :: xs)
      ((x :: xs).length) 1 1 w' (x :: xs) l'
      hlen1 (Nat.le_refl _) (Nat.le_refl _) (Nat.sub_le _ _)
      rfl (by simp [dedupAdj]) (fun j _ => rfl) hfwd
    obtain ⟨hb, -⟩ := uniqueFwd_bounds (x :: xs) l'
      ((x :: xs).length) 1 1 _ w' (Nat.le_refl _)
      (Nat.le_refl _) hfwd
    have hwlen : w' = (dedupAdj (x :: xs)).length := by
      have h1 : (l'.take w').length = w' := by
        rw [List.length_take, hlen', Nat.min_eq_left (by omega)]
      rw [← h1, hpre]
    refine ⟨w', evalProgFunc_vecUnique_ok F (x :: xs) l' w' hl64 hF
      hread hfwd, hwlen, hb⟩
