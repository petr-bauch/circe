/-
Circe.Transfer.VecRemove — mem transfer for erase-compress
(`vec_remove`, the `std::remove` idiom; P2-M9).

Mirrors the value loop (`valRemoveBody_keep/drop`,
`valRemoveLoop_ok` in `Circe.Emit.VecRemove`) step for step on
the memory layer: the single `mutBorrow` block pins the
reified snapshot (`cellsAt` framed by find; the length word
shifts offsets by one), the survivor store threads through
`memStore` in lockstep on the same block (the drop branch
stores nothing), and the loop re-inducts over `(ρ, m, π)` with
the forward equation threading (two fuels: program fuel and
forward fuel). One leg only — the kernel is total (every
access is guard-justified). Entries close against the forward
contract: the first scalar-returning mutating kernel — the
returned `u64` is the new logical length and the compacted
prefix is pinned on the final block.
-/
import Circe.Transfer.VecPartition
import Circe.Emit.VecRemove
import Circe.Lemmas.TwoCursor
import Circe.Specs

/-! ## Binding (closed form) -/

/-- Remove binding pins one snapshot: the single `mutBorrow`
    vector at addr `0`; the owned `x` binds by value only (no
    block, no layout — the `stdVecIndex` precedent). -/
theorem bindMemArgs_vecRemove (l : List (BitVec 32))
    (x : BitVec 32) :
    bindMemArgs vecRemoveFunc.args
      [.stdVecVal l, .i32 x] emptyMem =
      some ([("v", .stdVecVal l), ("x", .i32 x)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("v", 0, 0)]) := by
  rfl

/-- Remove footprint is a single singleton (the owned `x` never
    touches memory). -/
theorem oracleNoalias_vecRemove (l : List (BitVec 32))
    (x : BitVec 32) :
    oracleNoalias vecRemoveFunc
      [.stdVecVal l, .i32 x] := by
  have hb := bindMemArgs_vecRemove l x
  have hn : LayoutNoAlias [("v", 0, 0)] := by
    simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-! ## Memory body hit -/

/-- One body iteration on memory, keep branch: the env threads
    exactly as on the value side while the survivor store
    prepends a shadowing snapshot block on the single `v`
    block (layout stays pinned). -/
theorem memRemoveBody_keep (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (l : List (BitVec 32)) (x : BitVec 32)
    (r w : Nat) (rB wB : BitVec 64) (y wOld : BitVec 32)
    (a t : Nat) (n : BitVec 32)
    (hlay : layoutLookup π "v" = some (a, t))
    (hmem : memFind m a = some ⟨t, true, n :: l⟩)
    (hn : n = BitVec.ofNat 32 l.length)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hx : envLookup ρ "x" = some (.i32 x))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hrlt : r < l.length)
    (hy : l[r]? = some y) (hwget : l[w]? = some wOld)
    (hwlt : w < l.length)
    (hkeep : (y != x) = true) :
    ∃ ρ' m', memEvalProgStmt prog F vecRemoveBody ρ m π =
      .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "v" = some (.stdVecVal (l.set w y)) ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r + 1) ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w + 1) ∧
      envLookup ρ' "x" = some (.i32 x) ∧
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
  have hxV : evalExpr (.var "x") ρ = .ok (.i32 x) :=
    evalExpr_var_hit _ _ _ hx
  have huneV : evalExpr (.une (.stdVecAt "v" (.var "r")) (.var "x")) ρ =
      .ok (.b true) := by
    have h := evalExpr_une_i32 (.stdVecAt "v" (.var "r"))
      (.var "x") ρ y x hat hxV
    rwa [hkeep] at h
  have huneM : memEvalExpr (.une (.stdVecAt "v" (.var "r")) (.var "x")) ρ m π =
      .ok (.b true) :=
    (memEvalExpr_une_agree (.stdVecAt "v" (.var "r"))
      (.var "x") ρ m π hatM_ag
      (memEvalExpr_var _ _ _ _)).trans huneV
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
  have hx₁ : envLookup ρ₁ "x" = some (.i32 x) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("x" : String) ≠ "v" by decide) hu₁]
    exact hx
  have hwVarM₁ : memEvalExpr (.var "w") ρ₁ m₁ π =
      .ok (.u64 wB) :=
    (memEvalExpr_var _ _ _ _).trans
      (evalExpr_var_hit _ _ _ hw₁)
  have hevW : evalExpr (.uadd (.var "w") (.lit (.u64 1))) ρ₁ =
      .ok (.u64 (wB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hw₁) (by simp [evalExpr, litVal])
  have hevWM : memEvalExpr
      (.uadd (.var "w") (.lit (.u64 1))) ρ₁ m₁ π =
      .ok (.u64 (wB + 1)) :=
    (memEvalExpr_uadd_agree (.var "w") (.lit (.u64 1))
      ρ₁ m₁ π (memEvalExpr_var _ _ _ _)
      (memEvalExpr_lit _ _ _ _)).trans hevW
  obtain ⟨ρ₂, hu₂⟩ := envUpdate_some_of_lookup ρ₁ "w"
    (.u64 wB) (.u64 (wB + 1)) hw₁
  have hstep_w := memRevAssign prog F "w"
    (.uadd (.var "w") (.lit (.u64 1))) ρ₁ m₁ π (.u64 (wB + 1)) ρ₂
    hevWM hevW hu₂
  have hr₂ : envLookup ρ₂ "r" = some (.u64 rB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("r" : String) ≠ "w" by decide) hu₂]
    exact hr₁
  have hx₂ : envLookup ρ₂ "x" = some (.i32 x) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("x" : String) ≠ "w" by decide) hu₂]
    exact hx₁
  have hrVarM₂ : memEvalExpr (.var "r") ρ₂ m₁ π =
      .ok (.u64 rB) :=
    (memEvalExpr_var _ _ _ _).trans
      (evalExpr_var_hit _ _ _ hr₂)
  have hevR : evalExpr (.uadd (.var "r") (.lit (.u64 1))) ρ₂ =
      .ok (.u64 (rB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hr₂) (by simp [evalExpr, litVal])
  have hevRM : memEvalExpr
      (.uadd (.var "r") (.lit (.u64 1))) ρ₂ m₁ π =
      .ok (.u64 (rB + 1)) :=
    (memEvalExpr_uadd_agree (.var "r") (.lit (.u64 1))
      ρ₂ m₁ π (memEvalExpr_var _ _ _ _)
      (memEvalExpr_lit _ _ _ _)).trans hevR
  obtain ⟨ρ₃, hu₃⟩ := envUpdate_some_of_lookup ρ₂ "r"
    (.u64 rB) (.u64 (rB + 1)) hr₂
  have hstep_r := memRevAssign prog F "r"
    (.uadd (.var "r") (.lit (.u64 1))) ρ₂ m₁ π (.u64 (rB + 1)) ρ₃
    hevRM hevR hu₃
  have hout₃ : envLookup ρ₃ "v" =
      some (.stdVecVal (l.set w y)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("v" : String) ≠ "r" by decide) hu₃]
    rw [envLookup_update_miss _ _ _ _ _
      (show ("v" : String) ≠ "w" by decide) hu₂]
    have h := envLookup_update_hit _ _ _ _ hu₁
    rwa [hsetB] at h
  have hx' : envLookup ρ₃ "x" = some (.i32 x) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("x" : String) ≠ "r" by decide) hu₃]
    exact hx₂
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
        (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
      ρ m π = .ok ((ρ₂, m₁, π), .fellThrough) := by
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep_set,
      hstep_w]
  have hif : memEvalProgStmt prog F
      (.if_ (.une (.stdVecAt "v" (.var "r")) (.var "x"))
        (.seq (.vecSet "v" (.var "w") (.stdVecAt "v" (.var "r")))
          (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
        .skip) ρ m π = .ok ((ρ₂, m₁, π), .fellThrough) :=
    (memEvalProgStmt_if_true prog F _ _ _ _ _ _ huneM).trans hthen
  have hbody : vecRemoveBody =
      (.seq (.if_ (.une (.stdVecAt "v" (.var "r")) (.var "x"))
          (.seq (.vecSet "v" (.var "w") (.stdVecAt "v" (.var "r")))
            (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
          .skip)
        (.assign "r" (.uadd (.var "r") (.lit (.u64 1))))) := rfl
  have heval : memEvalProgStmt prog F vecRemoveBody ρ m π =
      .ok ((ρ₃, m₁, π), .fellThrough) := by
    rw [hbody,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hif,
      hstep_r]
  exact ⟨ρ₃, m₁, heval, hout₃, ⟨(rB + 1), hr', hrN'⟩,
    ⟨(wB + 1), hw', hwN'⟩, hx', hmem₁⟩

/-- One body iteration on memory, drop branch: the `une` test
    fails, the state (env and memory) threads untouched, only
    `r` advances. -/
theorem memRemoveBody_drop (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (l : List (BitVec 32)) (x : BitVec 32)
    (r w : Nat) (rB wB : BitVec 64) (y : BitVec 32)
    (a t : Nat) (n : BitVec 32)
    (hlay : layoutLookup π "v" = some (a, t))
    (hmem : memFind m a = some ⟨t, true, n :: l⟩)
    (hn : n = BitVec.ofNat 32 l.length)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hx : envLookup ρ "x" = some (.i32 x))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hrlt : r < l.length)
    (hy : l[r]? = some y)
    (hdrop : (y != x) = false) :
    ∃ ρ', memEvalProgStmt prog F vecRemoveBody ρ m π =
      .ok ((ρ', m, π), .fellThrough) ∧
      envLookup ρ' "v" = some (.stdVecVal l) ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r + 1) ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w) ∧
      envLookup ρ' "x" = some (.i32 x) ∧
      memFind m a = some ⟨t, true, n :: l⟩ := by
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
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
  have hxV : evalExpr (.var "x") ρ = .ok (.i32 x) :=
    evalExpr_var_hit _ _ _ hx
  have huneV : evalExpr (.une (.stdVecAt "v" (.var "r")) (.var "x")) ρ =
      .ok (.b false) := by
    have h := evalExpr_une_i32 (.stdVecAt "v" (.var "r"))
      (.var "x") ρ y x hat hxV
    rwa [hdrop] at h
  have huneM : memEvalExpr (.une (.stdVecAt "v" (.var "r")) (.var "x")) ρ m π =
      .ok (.b false) :=
    (memEvalExpr_une_agree (.stdVecAt "v" (.var "r"))
      (.var "x") ρ m π hatM_ag
      (memEvalExpr_var _ _ _ _)).trans huneV
  have hskipV : memEvalProgStmt prog F .skip ρ m π =
      .ok ((ρ, m, π), .fellThrough) := by
    cases F <;> simp [memEvalProgStmt, memEvalStmtFuel,
      memEvalStmtZero, memEvalStmtWith]
  have hif : memEvalProgStmt prog F
      (.if_ (.une (.stdVecAt "v" (.var "r")) (.var "x"))
        (.seq (.vecSet "v" (.var "w") (.stdVecAt "v" (.var "r")))
          (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
        .skip) ρ m π = .ok ((ρ, m, π), .fellThrough) :=
    (memEvalProgStmt_if_false prog F _ _ _ _ _ _ huneM).trans hskipV
  have hevR : evalExpr (.uadd (.var "r") (.lit (.u64 1))) ρ =
      .ok (.u64 (rB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      hrVar (by simp [evalExpr, litVal])
  have hevRM : memEvalExpr
      (.uadd (.var "r") (.lit (.u64 1))) ρ m π =
      .ok (.u64 (rB + 1)) :=
    (memEvalExpr_uadd_agree (.var "r") (.lit (.u64 1))
      ρ m π (memEvalExpr_var _ _ _ _)
      (memEvalExpr_lit _ _ _ _)).trans hevR
  obtain ⟨ρ', hu⟩ := envUpdate_some_of_lookup ρ "r"
    (.u64 rB) (.u64 (rB + 1)) hr
  have hstep_r := memRevAssign prog F "r"
    (.uadd (.var "r") (.lit (.u64 1))) ρ m π (.u64 (rB + 1)) ρ'
    hevRM hevR hu
  have hout' : envLookup ρ' "v" = some (.stdVecVal l) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("v" : String) ≠ "r" by decide) hu]
    exact hv
  have hw' : envLookup ρ' "w" = some (.u64 wB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "r" by decide) hu]
    exact hw
  have hx' : envLookup ρ' "x" = some (.i32 x) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("x" : String) ≠ "r" by decide) hu]
    exact hx
  have hrN' : (rB + 1).toNat = r + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hrN]
    exact Nat.mod_eq_of_lt (by omega)
  have hr' : envLookup ρ' "r" = some (.u64 (rB + 1)) :=
    envLookup_update_hit _ _ _ _ hu
  have hbody : vecRemoveBody =
      (.seq (.if_ (.une (.stdVecAt "v" (.var "r")) (.var "x"))
          (.seq (.vecSet "v" (.var "w") (.stdVecAt "v" (.var "r")))
            (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
          .skip)
        (.assign "r" (.uadd (.var "r") (.lit (.u64 1))))) := rfl
  have heval : memEvalProgStmt prog F vecRemoveBody ρ m π =
      .ok ((ρ', m, π), .fellThrough) := by
    rw [hbody,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hif,
      hstep_r]
  exact ⟨ρ', heval, hout', ⟨(rB + 1), hr', hrN'⟩,
    ⟨wB, hw', hwN⟩, hx', hmem⟩

/-! ## Memory loop induction -/

/-- Memory loop, ok leg: the scan runs to `l.length`, the block
    holds the forward-model words (fuel induction threading the
    memory body hits; the forward equation unfolds one step per
    iteration). -/
theorem memRemoveLoop_ok (prog : Prog) (F G : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (l : List (BitVec 32)) (x : BitVec 32)
    (r w : Nat) (rB wB : BitVec 64)
    (l' : List (BitVec 32)) (r' w' : Nat)
    (a t : Nat) (n : BitVec 32)
    (hlay : layoutLookup π "v" = some (a, t))
    (hn : n = BitVec.ofNat 32 l.length)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hx : envLookup ρ "x" = some (.i32 x))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hmem : memFind m a = some ⟨t, true, n :: l⟩)
    (hle : r ≤ l.length) (hwle : w ≤ r)
    (hF : l.length - r ≤ F) (hG : l.length - r ≤ G)
    (hread : ∀ p, p < l.length → ∃ y, l[p]? = some y)
    (hfwd : removeFwd x l G r w = .ok (r', w', l')) :
    ∃ ρ' m', memEvalProgStmt prog F vecRemoveLoop ρ m π =
      .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "v" = some (.stdVecVal l') ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r') ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w') ∧
      envLookup ρ' "x" = some (.i32 x) ∧
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
    have hexit : memEvalProgStmt prog 0 vecRemoveLoop ρ m π =
        .ok ((ρ, m, π), .fellThrough) :=
      memEvalProgStmt_while_false prog 0 _ _ _ _ _ hguardF
    have hpair : (r, w, l) = (r', w', l') := by
      cases G with
      | zero => simpa [removeFwd] using hfwd
      | succ G =>
        have hneg : ¬ r < l.length := by omega
        simpa [removeFwd, dite_eq_right hneg] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    exact ⟨ρ, m, hexit, hv, ⟨rB, hr, hrN⟩, ⟨wB, hw, hwN⟩, hx,
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
      have hwlt : w < l.length := by omega
      obtain ⟨wOld, hwget⟩ := hread w hwlt
      cir_fuel_step (F, G, l.length - (r + 1))
      by_cases hkeep : (y != x) = true
      · have hle' : r + 1 ≤ (l.set w y).length := by
          have : (l.set w y).length = l.length := by
            simp [List.length_set]
          omega
        have hwle' : w + 1 ≤ r + 1 := by omega
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
            ⟨wB₁, hwB₁, hwN₁⟩, hx₁, hmem₁⟩ :=
          memRemoveBody_keep prog F ρ m π l x r w rB wB y wOld
            a t n hlay hmem hn hrN hwN hl64 hv hx hr hw
            hlt hy hwget hwlt hkeep
        have hlen : (l.set w y).length = l.length := by
          simp [List.length_set]
        have hlo64' : (l.set w y).length < 2 ^ 64 := by
          rw [hlen]; exact hl64
        have hn' : n = BitVec.ofNat 32 (l.set w y).length := by
          rw [hlen]; exact hn
        have hF'' : (l.set w y).length - (r + 1) ≤ F := by omega
        have hG'' : (l.set w y).length - (r + 1) ≤ G' := by omega
        have hfwd' : removeFwd x (l.set w y) G' (r + 1) (w + 1) =
            .ok (r', w', l') := by
          have h := hfwd
          simp only [removeFwd, dite_eq_left hlt, hy, hkeep] at h
          exact h
        obtain ⟨ρ', m', hloop, hout', ⟨rB', hrB', hrN'⟩,
            ⟨wB', hwB', hwN'⟩, hx', hmem'⟩ :=
          ih (G := G') (ρ := ρ₁) (m := m₁) (l := l.set w y)
            (r := r + 1) (w := w + 1) (rB := rB₁) (wB := wB₁)
            (hl64 := hlo64') (hn := hn')
            (hrN := hrN₁) (hwN := hwN₁)
            (hv := hout₁) (hx := hx₁) (hr := hrB₁) (hw := hwB₁)
            (hmem := hmem₁)
            (hle := hle') (hwle := hwle')
            (hF := hF'') (hG := hG'')
            (hread := hread') (hfwd := hfwd')
        refine ⟨ρ', m', ?_, hout', ⟨rB', hrB', hrN'⟩,
          ⟨wB', hwB', hwN'⟩, hx', hmem'⟩
        have hwhile : memEvalProgStmt prog (F + 1) vecRemoveLoop
            ρ m π =
            memEvalProgStmt prog F vecRemoveLoop ρ₁ m₁ π := by
          cir_unfold_prog (vecRemoveLoop, prog, F, hguardT, hbody)
        rw [hwhile]
        exact hloop
      · have hdrop : (y != x) = false := by
          cases h : (y != x) with
          | true => exact absurd h hkeep
          | false => rfl
        obtain ⟨ρ₁, hbody, hout₁, ⟨rB₁, hrB₁, hrN₁⟩,
            ⟨wB₁, hwB₁, hwN₁⟩, hx₁, hmem₁⟩ :=
          memRemoveBody_drop prog F ρ m π l x r w rB wB y
            a t n hlay hmem hn hrN hwN hl64 hv hx hr hw
            hlt hy hdrop
        have hwle' : w ≤ r + 1 := by omega
        have hfwd' : removeFwd x l G' (r + 1) w =
            .ok (r', w', l') := by
          have h := hfwd
          simp only [removeFwd, dite_eq_left hlt, hy, hdrop] at h
          exact h
        obtain ⟨ρ', m', hloop, hout', ⟨rB', hrB', hrN'⟩,
            ⟨wB', hwB', hwN'⟩, hx', hmem'⟩ :=
          ih (G := G') (ρ := ρ₁) (m := m) (l := l)
            (r := r + 1) (w := w) (rB := rB₁) (wB := wB₁)
            (hl64 := hl64) (hn := hn)
            (hrN := hrN₁) (hwN := hwN₁)
            (hv := hout₁) (hx := hx₁) (hr := hrB₁) (hw := hwB₁)
            (hmem := hmem₁)
            (hle := by omega) (hwle := hwle')
            (hF := hF') (hG := hG')
            (hread := hread) (hfwd := hfwd')
        refine ⟨ρ', m', ?_, hout', ⟨rB', hrB', hrN'⟩,
          ⟨wB', hwB', hwN'⟩, hx', hmem'⟩
        have hwhile : memEvalProgStmt prog (F + 1) vecRemoveLoop
            ρ m π =
            memEvalProgStmt prog F vecRemoveLoop ρ₁ m π := by
          cir_unfold_prog (vecRemoveLoop, prog, F, hguardT, hbody)
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
        have hag : memEvalExpr
            (.ult (.var "r") (.stdVecLen "v")) ρ m π =
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
      have hexit : memEvalProgStmt prog (F + 1) vecRemoveLoop
          ρ m π =
          .ok ((ρ, m, π), .fellThrough) :=
        memEvalProgStmt_while_false prog (F + 1) _ _ _ _ _ hguardF
      have hpair : (l.length, w, l) = (r', w', l') := by
        cases G with
        | zero => simpa [removeFwd] using hfwd
        | succ G =>
          have hneg : ¬ l.length < l.length := by omega
          simpa [removeFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      exact ⟨ρ, m, hexit, hv, ⟨rB, hr, hrN⟩, ⟨wB, hw, hwN⟩, hx,
        hmem⟩

/-! ## Entries and transfer -/

/-- Value entry: the `w`/`r` prelude runs, the loop closes
    against the forward model, the new logical length
    returns. -/
theorem evalProgFunc_vecRemove_ok (F : Nat)
    (l l' : List (BitVec 32)) (x : BitVec 32) (w' : Nat)
    (hl64 : l.length < 2 ^ 64)
    (hF : l.length ≤ F)
    (hread : ∀ p, p < l.length → ∃ y, l[p]? = some y)
    (hfwd : removeFwd x l l.length 0 0 =
      .ok (l.length, w', l')) :
    evalProgFunc vecRemoveProg F vecRemoveFunc
      [.stdVecVal l, .i32 x] =
      .ok (.u64 (BitVec.ofNat 64 w')) := by
  have hbind : bindArgs vecRemoveFunc.args
      [.stdVecVal l, .i32 x] =
      some [("v", .stdVecVal l), ("x", .i32 x)] := rfl
  have hbody : vecRemoveFunc.body =
      (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq vecRemoveLoop
            (.return_ (.var "w"))))) := rfl
  have hlit : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("v", .stdVecVal l), ("x", .i32 x)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletW := revLet vecRemoveProg F "w" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("v", .stdVecVal l), ("x", .i32 x)]
    (.u64 (BitVec.ofNat 64 0)) hlit
  have hlitR : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("v", .stdVecVal l), ("x", .i32 x)]
        "w" (.u64 (BitVec.ofNat 64 0))) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletR := revLet vecRemoveProg F "r" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (envExtend [("v", .stdVecVal l), ("x", .i32 x)]
      "w" (.u64 (BitVec.ofNat 64 0)))
    (.u64 (BitVec.ofNat 64 0)) hlitR
  have h0N : (BitVec.ofNat 64 0).toNat = 0 := by
    simp [BitVec.toNat_ofNat]
  have hv₁ : envLookup (envExtend (envExtend
      [("v", .stdVecVal l), ("x", .i32 x)]
      "w" (.u64 (BitVec.ofNat 64 0)))
      "r" (.u64 (BitVec.ofNat 64 0))) "v" =
      some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "r" by decide),
      envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "w" by decide)]
    simp [envLookup]
  have hx₁ : envLookup (envExtend (envExtend
      [("v", .stdVecVal l), ("x", .i32 x)]
      "w" (.u64 (BitVec.ofNat 64 0)))
      "r" (.u64 (BitVec.ofNat 64 0))) "x" =
      some (.i32 x) := by
    rw [envExtend_miss _ _ _ _
      (show ("x" : String) ≠ "r" by decide),
      envExtend_miss _ _ _ _
      (show ("x" : String) ≠ "w" by decide)]
    simp [envLookup]
  have hw₁ : envLookup (envExtend (envExtend
      [("v", .stdVecVal l), ("x", .i32 x)]
      "w" (.u64 (BitVec.ofNat 64 0)))
      "r" (.u64 (BitVec.ofNat 64 0))) "w" =
      some (.u64 (BitVec.ofNat 64 0)) := by
    rw [envExtend_miss _ _ _ _
      (show ("w" : String) ≠ "r" by decide)]
    exact envExtend_hit _ _ _
  have hr₁ : envLookup (envExtend (envExtend
      [("v", .stdVecVal l), ("x", .i32 x)]
      "w" (.u64 (BitVec.ofNat 64 0)))
      "r" (.u64 (BitVec.ofNat 64 0))) "r" =
      some (.u64 (BitVec.ofNat 64 0)) :=
    envExtend_hit _ _ _
  obtain ⟨ρ', hloop, hout', ⟨rB', hrB', hrN'⟩,
      ⟨wB', hwB', hwN'⟩⟩ :=
    valRemoveLoop_ok vecRemoveProg F l.length
      (envExtend (envExtend [("v", .stdVecVal l),
        ("x", .i32 x)]
        "w" (.u64 (BitVec.ofNat 64 0)))
        "r" (.u64 (BitVec.ofNat 64 0)))
      l x 0 0 (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
      l' l.length w'
      h0N h0N hl64 hv₁ hx₁ hr₁ hw₁ (Nat.zero_le _)
      (Nat.le_refl _) (by omega) (by omega) hread hfwd
  have hwEq : wB' = BitVec.ofNat 64 w' := by
    have hb : w' ≤ l.length := by
      obtain ⟨h1, -⟩ := removeFwd_bounds x l l' l.length 0 0
        l.length w' (Nat.le_refl _) hfwd
      exact h1
    apply BitVec.eq_of_toNat_eq
    rw [hwN', BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by omega : w' < 2 ^ 64)).symm
  have hret := evalProgStmt_return vecRemoveProg F
    (.var "w") ρ' (.u64 wB')
    (evalExpr_var_hit _ _ _ hwB')
  simp only [evalProgFunc, hbind, hbody]
  rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletW,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletR,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hloop,
    hret, hwEq]

/-- Memory entry: the `w`/`r` prelude runs on memory, the loop
    closes against the forward model, the new logical length
    returns. -/
theorem memEvalProgFunc_vecRemove_ok (F : Nat)
    (l l' : List (BitVec 32)) (x : BitVec 32) (w' : Nat)
    (hl64 : l.length < 2 ^ 64)
    (hF : l.length ≤ F)
    (hread : ∀ p, p < l.length → ∃ y, l[p]? = some y)
    (hfwd : removeFwd x l l.length 0 0 =
      .ok (l.length, w', l')) :
    memEvalProgFunc vecRemoveProg F vecRemoveFunc
      [.stdVecVal l, .i32 x] =
      .ok (.u64 (BitVec.ofNat 64 w')) := by
  have hbind := bindMemArgs_vecRemove l x
  have hbody : vecRemoveFunc.body =
      (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq vecRemoveLoop
            (.return_ (.var "w"))))) := rfl
  have hmem : memFind
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ 0 =
      some ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩ :=
    memFind_cons_hit _ _ _ _ _
  have hlay : layoutLookup [("v", 0, 0)] "v" =
      some (0, 0) := by simp [layoutLookup]
  have hlitM : memEvalExpr
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("v", .stdVecVal l), ("x", .i32 x)]
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("v", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("v", .stdVecVal l), ("x", .i32 x)] :=
    memEvalExpr_lit _ _ _ _
  have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("v", .stdVecVal l), ("x", .i32 x)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletW := memRevLet vecRemoveProg F "w" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("v", .stdVecVal l), ("x", .i32 x)]
    ⟨1, [(0, ⟨0, true,
      (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
    [("v", 0, 0)] (.u64 (BitVec.ofNat 64 0))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) (by intro h; cases h) hlitM hlitV
  have hlitRM : memEvalExpr
      (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("v", .stdVecVal l), ("x", .i32 x)]
        "w" (.u64 (BitVec.ofNat 64 0)))
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("v", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend [("v", .stdVecVal l), ("x", .i32 x)]
          "w" (.u64 (BitVec.ofNat 64 0))) :=
    memEvalExpr_lit _ _ _ _
  have hlitRV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("v", .stdVecVal l), ("x", .i32 x)]
        "w" (.u64 (BitVec.ofNat 64 0))) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletR := memRevLet vecRemoveProg F "r" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (envExtend [("v", .stdVecVal l), ("x", .i32 x)]
      "w" (.u64 (BitVec.ofNat 64 0)))
    ⟨1, [(0, ⟨0, true,
      (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
    [("v", 0, 0)] (.u64 (BitVec.ofNat 64 0))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) (by intro h; cases h) hlitRM hlitRV
  have h0N : (BitVec.ofNat 64 0).toNat = 0 := by
    simp [BitVec.toNat_ofNat]
  have hv₁ : envLookup (envExtend (envExtend
      [("v", .stdVecVal l), ("x", .i32 x)]
      "w" (.u64 (BitVec.ofNat 64 0)))
      "r" (.u64 (BitVec.ofNat 64 0))) "v" =
      some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "r" by decide),
      envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "w" by decide)]
    simp [envLookup]
  have hx₁ : envLookup (envExtend (envExtend
      [("v", .stdVecVal l), ("x", .i32 x)]
      "w" (.u64 (BitVec.ofNat 64 0)))
      "r" (.u64 (BitVec.ofNat 64 0))) "x" =
      some (.i32 x) := by
    rw [envExtend_miss _ _ _ _
      (show ("x" : String) ≠ "r" by decide),
      envExtend_miss _ _ _ _
      (show ("x" : String) ≠ "w" by decide)]
    simp [envLookup]
  have hw₁ : envLookup (envExtend (envExtend
      [("v", .stdVecVal l), ("x", .i32 x)]
      "w" (.u64 (BitVec.ofNat 64 0)))
      "r" (.u64 (BitVec.ofNat 64 0))) "w" =
      some (.u64 (BitVec.ofNat 64 0)) := by
    rw [envExtend_miss _ _ _ _
      (show ("w" : String) ≠ "r" by decide)]
    exact envExtend_hit _ _ _
  have hr₁ : envLookup (envExtend (envExtend
      [("v", .stdVecVal l), ("x", .i32 x)]
      "w" (.u64 (BitVec.ofNat 64 0)))
      "r" (.u64 (BitVec.ofNat 64 0))) "r" =
      some (.u64 (BitVec.ofNat 64 0)) :=
    envExtend_hit _ _ _
  obtain ⟨ρ', m', hloop, hout', ⟨rB', hrB', hrN'⟩,
      ⟨wB', hwB', hwN'⟩, hx', hmem'⟩ :=
    memRemoveLoop_ok vecRemoveProg F l.length
      (envExtend (envExtend [("v", .stdVecVal l),
        ("x", .i32 x)]
        "w" (.u64 (BitVec.ofNat 64 0)))
        "r" (.u64 (BitVec.ofNat 64 0)))
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("v", 0, 0)]
      l x 0 0 (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
      l' l.length w' 0 0 (BitVec.ofNat 32 l.length)
      (by simp [layoutLookup]) rfl
      h0N h0N hl64 hv₁ hx₁ hr₁ hw₁ hmem
      (Nat.zero_le _) (Nat.le_refl _)
      (by omega) (by omega) hread hfwd
  have hwEq : wB' = BitVec.ofNat 64 w' := by
    have hb : w' ≤ l.length := by
      obtain ⟨h1, -⟩ := removeFwd_bounds x l l' l.length 0 0
        l.length w' (Nat.le_refl _) hfwd
      exact h1
    apply BitVec.eq_of_toNat_eq
    rw [hwN', BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt (by omega : w' < 2 ^ 64)).symm
  have hret := memEvalProgStmt_return vecRemoveProg F
    (.var "w") ρ' m' [("v", 0, 0)]
    (.u64 wB')
    ((memEvalExpr_var _ _ _ _).trans
      (evalExpr_var_hit _ _ _ hwB'))
  simp only [memEvalProgFunc, hbind, hbody]
  rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletW,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletR,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hloop,
    hret, hwEq]

/-- Transfer for `vec_remove`: memory evaluation agrees with
    value evaluation (single ok leg — the kernel is total). -/
theorem memTransferProg_vecRemove_ok (F : Nat)
    (l : List (BitVec 32)) (x : BitVec 32)
    (hl64 : l.length < 2 ^ 64)
    (hF : l.length ≤ F)
    (hread : ∀ p, p < l.length → ∃ y, l[p]? = some y)
    (_h : oracleNoalias vecRemoveFunc
      [.stdVecVal l, .i32 x]) :
    memEvalProgFunc vecRemoveProg F vecRemoveFunc
      [.stdVecVal l, .i32 x] =
      evalProgFunc vecRemoveProg F vecRemoveFunc
        [.stdVecVal l, .i32 x] := by
  obtain ⟨w', l', heq⟩ :=
    removeFwd_ok x l l.length 0 0 (Nat.zero_le _)
      (Nat.le_refl _) (by omega) hread
  rw [memEvalProgFunc_vecRemove_ok F l l' x w' hl64 hF
    hread heq,
    evalProgFunc_vecRemove_ok F l l' x w' hl64 hF hread heq]

/-- Closing erase-compress contract (P2-M9): the kernel returns
    the new logical length — the count of survivors — bounded
    by the input length; the survivor prefix itself is
    `l.filter (· != x)` on the final words (forward contract). -/
theorem evalProgFunc_vecRemove_spec (F : Nat)
    (l : List (BitVec 32)) (x : BitVec 32)
    (hl64 : l.length < 2 ^ 64)
    (hF : l.length ≤ F)
    (hread : ∀ p, p < l.length → ∃ y, l[p]? = some y) :
    ∃ w', evalProgFunc vecRemoveProg F vecRemoveFunc
      [.stdVecVal l, .i32 x] = .ok (.u64 (BitVec.ofNat 64 w')) ∧
      w' = (l.filter (fun y => (y != x))).length ∧
      w' ≤ l.length := by
  obtain ⟨w', l', heq⟩ :=
    removeFwd_ok x l l.length 0 0 (Nat.zero_le _)
      (Nat.le_refl _) (by omega) hread
  obtain ⟨hb, -⟩ := removeFwd_bounds x l l' l.length 0 0
    l.length w' (Nat.le_refl _) heq
  obtain ⟨htake, -, hlen'⟩ := removeFwd_prefix x l l.length 0 0
    w' l l' (Nat.zero_le _) (Nat.le_refl _) (by omega) rfl
    (by simp) (fun j _ => rfl) heq
  have hwlen : w' = (l.filter (fun y => (y != x))).length :=
    squeeze_length_eq l' _ w' htake (by rw [hlen']; exact hb)
  exact ⟨w', evalProgFunc_vecRemove_ok F l l' x w' hl64 hF
    hread heq, hwlen, hb⟩
