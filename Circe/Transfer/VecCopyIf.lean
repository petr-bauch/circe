/-
Circe.Transfer.VecCopyIf — mem transfer for the out-of-place filter
(`vec_copy_if`, the `std::copy_if` idiom; P2-M12).

Mirrors the value loop (`valCopyIfBody_copy/_short/_drop`,
`valCopyIfLoop_ok/_err` in `Circe.Emit.VecCopyIf`) step for step
on the memory layer: the read-only `a` block pins its snapshot
(`cellsAt` framed by find; the length word shifts offsets by
one), the keep test agrees, the inner `out` guard agrees over
the `out` length word, the kept element stores into the `out`
block through `memStore` in lockstep (framing the untouched
`a` block via `memFind_memStore_other`), the cursors bump
through `memRevAssign`, and the loop re-inducts over
`(ρ, m, π)` with the forward equation threading (two fuels:
program fuel and forward fuel) plus the keep-count and
capacity invariants. Two legs: the short-`out` leg fires the
loud `AssertFail` through the inner-guard-false + fail arm.
Entries close against the forward contract; the closing specs
tie the `u64` survivor count to the filter prefix over the
independent `List.filter` oracle (`copyIfFwd_*` in
`Circe.Specs`).
-/
import Circe.Transfer.VecReverse
import Circe.Emit.VecCopyIf
import Circe.Specs

/-! ## Binding (closed form) -/

/-- Copy-if binding pins two snapshots: the shared-borrow
    input at addr `1`, the mut-borrow output at addr `0`
    (tail-first allocation order; the owned `x` binds by
    value only — the `stdVecIndex` precedent). -/
theorem bindMemArgs_vecCopyIf (la lo : List (BitVec 32))
    (x : BitVec 32) :
    bindMemArgs vecCopyIfFunc.args
      [.stdVecVal la, .stdVecVal lo, .i32 x] emptyMem =
      some ([("a", .stdVecVal la), ("out", .stdVecVal lo),
        ("x", .i32 x)],
        ⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 la.length) :: la⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩,
        [("a", 1, 1), ("out", 0, 0)]) := by
  rfl

/-- Copy-if footprint is two disjoint singletons (the owned `x`
    never touches memory). -/
theorem oracleNoalias_vecCopyIf (la lo : List (BitVec 32))
    (x : BitVec 32) :
    oracleNoalias vecCopyIfFunc
      [.stdVecVal la, .stdVecVal lo, .i32 x] := by
  have hb := bindMemArgs_vecCopyIf la lo x
  have hn : LayoutNoAlias [("a", 1, 1), ("out", 0, 0)] := by
    simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-! ## Memory body hits -/

/-- One body iteration on memory, keep branch: the read agrees
    with the value side, the keep test fires, the `out` guard
    holds, the kept element stores into the `out` block in
    lockstep (the `a` block framed across the store), and both
    cursors bump. -/
theorem memCopyIfBody_copy (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lo : List (BitVec 32)) (x : BitVec 32)
    (r w : Nat) (rB wB : BitVec 64) (y wOld : BitVec 32)
    (aa ao : Nat) (ta to : Nat) (na no : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_o : layoutLookup π "out" = some (ao, to))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_o : memFind m ao = some ⟨to, true, no :: lo⟩)
    (hna : na = BitVec.ofNat 32 la.length)
    (hno : no = BitVec.ofNat 32 lo.length)
    (haa : aa ≠ ao)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hx : envLookup ρ "x" = some (.i32 x))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hrlt : r < la.length)
    (hy : la[r]? = some y) (hwget : lo[w]? = some wOld)
    (hwlt : w < lo.length)
    (hkeep : (y != x) = true) :
    ∃ ρ' m', memEvalProgStmt prog F vecCopyIfBody ρ m π =
      .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "out" = some (.stdVecVal (lo.set w y)) ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r + 1) ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w + 1) ∧
      envLookup ρ' "x" = some (.i32 x) ∧
      memFind m' ao = some ⟨to, true, no :: (lo.set w y)⟩ ∧
      memFind m' aa = some ⟨ta, true, na :: la⟩ := by
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
  have hwVar : evalExpr (.var "w") ρ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw
  have hrVarM : memEvalExpr (.var "r") ρ m π = .ok (.u64 rB) :=
    (memEvalExpr_var _ _ _ _).trans hrVar
  have hwVarM : memEvalExpr (.var "w") ρ m π = .ok (.u64 wB) :=
    (memEvalExpr_var _ _ _ _).trans hwVar
  have hgetR : la[rB.toNat]? = some y := by rw [hrN]; exact hy
  have hgetW : lo[wB.toNat]? = some wOld := by rw [hwN]; exact hwget
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
  have hxV : evalExpr (.var "x") ρ = .ok (.i32 x) :=
    evalExpr_var_hit _ _ _ hx
  have huneV : evalExpr (.une (.stdVecAt "a" (.var "r")) (.var "x")) ρ =
      .ok (.b true) := by
    have h := evalExpr_une_i32 (.stdVecAt "a" (.var "r"))
      (.var "x") ρ y x hat hxV
    rwa [hkeep] at h
  have huneM : memEvalExpr (.une (.stdVecAt "a" (.var "r")) (.var "x")) ρ m π =
      .ok (.b true) :=
    (memEvalExpr_une_agree (.stdVecAt "a" (.var "r"))
      (.var "x") ρ m π hatM_ag
      (memEvalExpr_var _ _ _ _)).trans huneV
  have hmemLenO : memLoad m ao to 0 =
      .ok (BitVec.ofNat 32 lo.length) := by
    rw [← hno]
    exact memLoad_cellsAt m ao to 0 (no :: lo) no hmem_o (by simp)
  have hlenN : (BitVec.ofNat 64 lo.length).toNat = lo.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlo64
  have hguardT : memEvalExpr (.ult (.var "w") (.stdVecLen "out")) ρ m π =
      .ok (.b true) := by
    have hag := memEvalExpr_ult_agree (.var "w") (.stdVecLen "out")
      ρ m π (memEvalExpr_var _ _ _ _)
      (memEvalExpr_stdVecLen_hit "out" ρ m π lo ao to
        hlay_o hout hmemLenO)
    have hult := evalExpr_ult_u64 (.var "w") (.stdVecLen "out") ρ wB
      (BitVec.ofNat 64 lo.length) hwVar
      (evalExpr_stdVecLen_some _ _ _ hout)
    have htb : (wB.ult (BitVec.ofNat 64 lo.length)) = true := by
      rw [BitVec.ult_eq_decide]
      exact decide_eq_true (by omega)
    have hultT : evalExpr (.ult (.var "w") (.stdVecLen "out")) ρ =
        .ok (.b true) := by
      rwa [htb] at hult
    rw [hag]; exact hultT
  have hlt₁ : wB.toNat + 1 < (no :: lo).length := by
    simp only [List.length_cons]
    omega
  obtain ⟨m₁, hmstore, hmem₁⟩ :=
    memStore_cellsAt_pin m ao to y hmem_o hlt₁
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "out"
    (.stdVecVal lo) (.stdVecVal (lo.set wB.toNat y)) hout
  have hstep_set := memRevVecSet prog F "out" (.var "w")
    (.stdVecAt "a" (.var "r")) ρ m π wB y ao to lo wOld m₁ ρ₁
    hwVarM hatM hout hlay_o hgetW hmstore hu₁
  have hsetB : lo.set wB.toNat y = lo.set w y := by rw [hwN]
  rw [hsetB] at hmem₁
  have hmem_a₁ : memFind m₁ aa = some ⟨ta, true, na :: la⟩ := by
    have h := memFind_memStore_other m m₁ ao aa to (wB.toNat + 1) y
      hmstore haa
    rw [h]; exact hmem_a
  have ha₁ : envLookup ρ₁ "a" = some (.stdVecVal la) := by
    have h := envLookup_update_miss ρ "a" "out" _ ρ₁
      (show ("a" : String) ≠ "out" by decide) hu₁
    rw [h]; exact ha
  have hx₁ : envLookup ρ₁ "x" = some (.i32 x) := by
    have h := envLookup_update_miss ρ "x" "out" _ ρ₁
      (show ("x" : String) ≠ "out" by decide) hu₁
    rw [h]; exact hx
  have hr₁ : envLookup ρ₁ "r" = some (.u64 rB) := by
    have h := envLookup_update_miss ρ "r" "out" _ ρ₁
      (show ("r" : String) ≠ "out" by decide) hu₁
    rw [h]; exact hr
  have hw₁ : envLookup ρ₁ "w" = some (.u64 wB) := by
    have h := envLookup_update_miss ρ "w" "out" _ ρ₁
      (show ("w" : String) ≠ "out" by decide) hu₁
    rw [h]; exact hw
  have hwVarM₁ : memEvalExpr (.var "w") ρ₁ m₁ π =
      .ok (.u64 wB) :=
    (memEvalExpr_var _ _ _ _).trans
      (evalExpr_var_hit _ _ _
        (by rw [envLookup_update_miss _ _ _ _ _
          (show ("w" : String) ≠ "out" by decide) hu₁]; exact hw))
  have hevW : evalExpr (.uadd (.var "w") (.lit (.u64 1))) ρ₁ =
      .ok (.u64 (wB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _
        (by rw [envLookup_update_miss _ _ _ _ _
          (show ("w" : String) ≠ "out" by decide) hu₁]; exact hw))
      (by simp [evalExpr, litVal])
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
  have ha₂ : envLookup ρ₂ "a" = some (.stdVecVal la) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "w" by decide) hu₂]
    exact ha₁
  have hout₂ : envLookup ρ₂ "out" =
      some (.stdVecVal (lo.set w y)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "w" by decide) hu₂]
    have h := envLookup_update_hit _ _ _ _ hu₁
    rwa [hsetB] at h
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
  have hout₃ : envLookup ρ₃ "out" =
      some (.stdVecVal (lo.set w y)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "r" by decide) hu₃]
    exact hout₂
  have ha₃ : envLookup ρ₃ "a" = some (.stdVecVal la) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "r" by decide) hu₃]
    exact ha₂
  have hx₃ : envLookup ρ₃ "x" = some (.i32 x) := by
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
  have hmem_o' : memFind m₁ ao = some ⟨to, true, no :: (lo.set w y)⟩ :=
    hmem₁
  have hmem_a' : memFind m₁ aa = some ⟨ta, true, na :: la⟩ :=
    hmem_a₁
  have hthen : memEvalProgStmt prog F
      (.seq (.vecSet "out" (.var "w") (.stdVecAt "a" (.var "r")))
        (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
      ρ m π = .ok ((ρ₂, m₁, π), .fellThrough) := by
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep_set,
      hstep_w]
  have hinner : memEvalProgStmt prog F
      (.if_ (.ult (.var "w") (.stdVecLen "out"))
        (.seq (.vecSet "out" (.var "w") (.stdVecAt "a" (.var "r")))
          (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
        .fail) ρ m π = .ok ((ρ₂, m₁, π), .fellThrough) :=
    (memEvalProgStmt_if_true prog F _ _ _ _ _ _ hguardT).trans hthen
  have hif : memEvalProgStmt prog F
      (.if_ (.une (.stdVecAt "a" (.var "r")) (.var "x"))
        (.if_ (.ult (.var "w") (.stdVecLen "out"))
          (.seq (.vecSet "out" (.var "w")
            (.stdVecAt "a" (.var "r")))
            (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
          .fail)
        .skip) ρ m π = .ok ((ρ₂, m₁, π), .fellThrough) :=
    (memEvalProgStmt_if_true prog F _ _ _ _ _ _ huneM).trans hinner
  have hbody : vecCopyIfBody =
      (.seq (.if_ (.une (.stdVecAt "a" (.var "r")) (.var "x"))
          (.if_ (.ult (.var "w") (.stdVecLen "out"))
            (.seq (.vecSet "out" (.var "w")
              (.stdVecAt "a" (.var "r")))
              (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
            .fail)
          .skip)
        (.assign "r" (.uadd (.var "r") (.lit (.u64 1))))) := rfl
  have heval : memEvalProgStmt prog F vecCopyIfBody ρ m π =
      .ok ((ρ₃, m₁, π), .fellThrough) := by
    rw [hbody,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hif,
      hstep_r]
  exact ⟨ρ₃, m₁, heval, ha₃, hout₃, ⟨(rB + 1), hr', hrN'⟩,
    ⟨(wB + 1), hw', hwN'⟩, hx₃, hmem_o', hmem_a'⟩

/-- One body iteration on memory, short-`out` branch: the
    keep test fires but `w` is past the output, so the inner
    guard fails and the loud `.fail` leg fires (memory
    untouched). -/
theorem memCopyIfBody_short (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lo : List (BitVec 32)) (x : BitVec 32)
    (r w : Nat) (rB wB : BitVec 64) (y : BitVec 32)
    (aa ao : Nat) (ta to : Nat) (na no : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_o : layoutLookup π "out" = some (ao, to))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_o : memFind m ao = some ⟨to, true, no :: lo⟩)
    (hna : na = BitVec.ofNat 32 la.length)
    (hno : no = BitVec.ofNat 32 lo.length)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hx : envLookup ρ "x" = some (.i32 x))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hrlt : r < la.length)
    (hy : la[r]? = some y)
    (hmiss : lo[w]? = none)
    (hkeep : (y != x) = true) :
    memEvalProgStmt prog F vecCopyIfBody ρ m π =
      .error .AssertFail := by
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
  have hwVar : evalExpr (.var "w") ρ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw
  have hrVarM : memEvalExpr (.var "r") ρ m π = .ok (.u64 rB) :=
    (memEvalExpr_var _ _ _ _).trans hrVar
  have hwVarM : memEvalExpr (.var "w") ρ m π = .ok (.u64 wB) :=
    (memEvalExpr_var _ _ _ _).trans hwVar
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
  have hxV : evalExpr (.var "x") ρ = .ok (.i32 x) :=
    evalExpr_var_hit _ _ _ hx
  have huneV : evalExpr (.une (.stdVecAt "a" (.var "r")) (.var "x")) ρ =
      .ok (.b true) := by
    have h := evalExpr_une_i32 (.stdVecAt "a" (.var "r"))
      (.var "x") ρ y x hat hxV
    rwa [hkeep] at h
  have huneM : memEvalExpr (.une (.stdVecAt "a" (.var "r")) (.var "x")) ρ m π =
      .ok (.b true) :=
    (memEvalExpr_une_agree (.stdVecAt "a" (.var "r"))
      (.var "x") ρ m π hatM_ag
      (memEvalExpr_var _ _ _ _)).trans huneV
  have hmemLenO : memLoad m ao to 0 =
      .ok (BitVec.ofNat 32 lo.length) := by
    rw [← hno]
    exact memLoad_cellsAt m ao to 0 (no :: lo) no hmem_o (by simp)
  have hlenN : (BitVec.ofNat 64 lo.length).toNat = lo.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlo64
  have hnl : ¬ w < lo.length := by
    intro h
    have hsome : lo[w]? = some lo[w] := List.getElem?_eq_getElem h
    rw [hsome] at hmiss
    simp at hmiss
  have hguardF : memEvalExpr (.ult (.var "w") (.stdVecLen "out")) ρ m π =
      .ok (.b false) := by
    have hag := memEvalExpr_ult_agree (.var "w") (.stdVecLen "out")
      ρ m π (memEvalExpr_var _ _ _ _)
      (memEvalExpr_stdVecLen_hit "out" ρ m π lo ao to
        hlay_o hout hmemLenO)
    have hult := evalExpr_ult_u64 (.var "w") (.stdVecLen "out") ρ wB
      (BitVec.ofNat 64 lo.length) hwVar
      (evalExpr_stdVecLen_some _ _ _ hout)
    have hfb : (wB.ult (BitVec.ofNat 64 lo.length)) = false := by
      rw [BitVec.ult_eq_decide, hlenN]
      exact decide_eq_false (by omega)
    have hultF : evalExpr (.ult (.var "w") (.stdVecLen "out")) ρ =
        .ok (.b false) := by
      rwa [hfb] at hult
    rw [hag]; exact hultF
  have hfail : memEvalProgStmt prog F .fail ρ m π =
      .error .AssertFail := by
    simpa [memEvalProgStmt] using (memEvalStmtFuel_fail F ρ m π)
  have hinner : memEvalProgStmt prog F
      (.if_ (.ult (.var "w") (.stdVecLen "out"))
        (.seq (.vecSet "out" (.var "w") (.stdVecAt "a" (.var "r")))
          (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
        .fail) ρ m π = .error .AssertFail :=
    (memEvalProgStmt_if_false prog F _ _ _ _ _ _ hguardF).trans hfail
  have hif : memEvalProgStmt prog F
      (.if_ (.une (.stdVecAt "a" (.var "r")) (.var "x"))
        (.if_ (.ult (.var "w") (.stdVecLen "out"))
          (.seq (.vecSet "out" (.var "w")
            (.stdVecAt "a" (.var "r")))
            (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
          .fail)
        .skip) ρ m π = .error .AssertFail :=
    (memEvalProgStmt_if_true prog F _ _ _ _ _ _ huneM).trans hinner
  have hbody : vecCopyIfBody =
      (.seq (.if_ (.une (.stdVecAt "a" (.var "r")) (.var "x"))
          (.if_ (.ult (.var "w") (.stdVecLen "out"))
            (.seq (.vecSet "out" (.var "w")
              (.stdVecAt "a" (.var "r")))
              (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
            .fail)
          .skip)
        (.assign "r" (.uadd (.var "r") (.lit (.u64 1))))) := rfl
  have heval : memEvalProgStmt prog F vecCopyIfBody ρ m π =
      .error .AssertFail := by
    rw [hbody, memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hif]
  exact heval

/-- One body iteration on memory, drop branch: the `une`
    test fails, the state (env and memory) threads untouched,
    only `r` advances. -/
theorem memCopyIfBody_drop (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lo : List (BitVec 32)) (x : BitVec 32)
    (r w : Nat) (rB wB : BitVec 64) (y : BitVec 32)
    (aa ao : Nat) (ta to : Nat) (na no : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_o : layoutLookup π "out" = some (ao, to))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_o : memFind m ao = some ⟨to, true, no :: lo⟩)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hla64 : la.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hx : envLookup ρ "x" = some (.i32 x))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hrlt : r < la.length)
    (hy : la[r]? = some y)
    (hdrop : (y != x) = false) :
    ∃ ρ', memEvalProgStmt prog F vecCopyIfBody ρ m π =
      .ok ((ρ', m, π), .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "out" = some (.stdVecVal lo) ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r + 1) ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w) ∧
      envLookup ρ' "x" = some (.i32 x) ∧
      memFind m ao = some ⟨to, true, no :: lo⟩ ∧
      memFind m aa = some ⟨ta, true, na :: la⟩ := by
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
  have hrVarM : memEvalExpr (.var "r") ρ m π = .ok (.u64 rB) :=
    (memEvalExpr_var _ _ _ _).trans hrVar
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
  have hxV : evalExpr (.var "x") ρ = .ok (.i32 x) :=
    evalExpr_var_hit _ _ _ hx
  have huneV : evalExpr (.une (.stdVecAt "a" (.var "r")) (.var "x")) ρ =
      .ok (.b false) := by
    have h := evalExpr_une_i32 (.stdVecAt "a" (.var "r"))
      (.var "x") ρ y x hat hxV
    rwa [hdrop] at h
  have huneM : memEvalExpr (.une (.stdVecAt "a" (.var "r")) (.var "x")) ρ m π =
      .ok (.b false) :=
    (memEvalExpr_une_agree (.stdVecAt "a" (.var "r"))
      (.var "x") ρ m π hatM_ag
      (memEvalExpr_var _ _ _ _)).trans huneV
  have hskipV : memEvalProgStmt prog F .skip ρ m π =
      .ok ((ρ, m, π), .fellThrough) := by
    cases F <;> simp [memEvalProgStmt, memEvalStmtFuel,
      memEvalStmtZero, memEvalStmtWith]
  have hif : memEvalProgStmt prog F
      (.if_ (.une (.stdVecAt "a" (.var "r")) (.var "x"))
        (.if_ (.ult (.var "w") (.stdVecLen "out"))
          (.seq (.vecSet "out" (.var "w")
            (.stdVecAt "a" (.var "r")))
            (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
          .fail)
        .skip) ρ m π = .ok ((ρ, m, π), .fellThrough) :=
    (memEvalProgStmt_if_false prog F _ _ _ _ _ _ huneM).trans hskipV
  have hevR : evalExpr (.uadd (.var "r") (.lit (.u64 1))) ρ =
      .ok (.u64 (rB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hr) (by simp [evalExpr, litVal])
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
  have hout' : envLookup ρ' "out" = some (.stdVecVal lo) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "r" by decide) hu]
    exact hout
  have ha' : envLookup ρ' "a" = some (.stdVecVal la) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "r" by decide) hu]
    exact ha
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
  have hbody : vecCopyIfBody =
      (.seq (.if_ (.une (.stdVecAt "a" (.var "r")) (.var "x"))
          (.if_ (.ult (.var "w") (.stdVecLen "out"))
            (.seq (.vecSet "out" (.var "w")
              (.stdVecAt "a" (.var "r")))
              (.assign "w" (.uadd (.var "w") (.lit (.u64 1)))))
            .fail)
          .skip)
        (.assign "r" (.uadd (.var "r") (.lit (.u64 1))))) := rfl
  have heval : memEvalProgStmt prog F vecCopyIfBody ρ m π =
      .ok ((ρ', m, π), .fellThrough) := by
    rw [hbody,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hif,
      hstep_r]
  exact ⟨ρ', heval, ha', hout', ⟨(rB + 1), hr', hrN'⟩, ⟨wB, hw', hwN⟩,
    hx', hmem_o, hmem_a⟩

/-! ## Memory loop -/

/-- Memory loop, ok leg: the scan runs to `la.length`,
    threading both pins with the forward equation (fuel
    induction; the value loop justifies each iteration). -/
theorem memCopyIfLoop_ok (prog : Prog) (F G : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lo : List (BitVec 32)) (x : BitVec 32)
    (r w : Nat) (rB wB : BitVec 64)
    (lo' : List (BitVec 32)) (r' w' : Nat)
    (aa ao : Nat) (ta to : Nat) (na no : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_o : layoutLookup π "out" = some (ao, to))
    (hn : na = BitVec.ofNat 32 la.length)
    (hno : no = BitVec.ofNat 32 lo.length)
    (haa : aa ≠ ao)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hx : envLookup ρ "x" = some (.i32 x))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_o : memFind m ao = some ⟨to, true, no :: lo⟩)
    (hle : r ≤ la.length)
    (hF : la.length - r ≤ F) (hG : la.length - r ≤ G)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hwcnt : ((la.take r).filter (fun y => (y != x))).length = w)
    (hcap : (la.filter (fun y => (y != x))).length ≤ lo.length)
    (hfwd : copyIfFwd x la lo G r w = .ok (r', w', lo')) :
    ∃ ρ' m', memEvalProgStmt prog F vecCopyIfLoop ρ m π =
      .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "out" = some (.stdVecVal lo') ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r') ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w') ∧
      envLookup ρ' "x" = some (.i32 x) ∧
      memFind m' ao = some ⟨to, true, no :: lo'⟩ ∧
      memFind m' aa = some ⟨ta, true, na :: la⟩ := by
  induction F generalizing G ρ m lo r w rB wB with
  | zero =>
    have him : r = la.length := by omega
    have hlenN : (BitVec.ofNat 64 la.length).toNat = la.length := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
    have hmemLen : memLoad m aa ta 0 =
        .ok (BitVec.ofNat 32 la.length) := by
      rw [← hn]
      exact memLoad_cellsAt m aa ta 0 (na :: la) na hmem_a (by simp)
    have hguardF : memEvalExpr
        (.ult (.var "r") (.stdVecLen "a")) ρ m π =
        .ok (.b false) := by
      have hag : memEvalExpr (.ult (.var "r") (.stdVecLen "a")) ρ m π =
          evalExpr (.ult (.var "r") (.stdVecLen "a")) ρ :=
        memEvalExpr_ult_agree (.var "r") (.stdVecLen "a") ρ m π
          (memEvalExpr_var _ _ _ _)
          (memEvalExpr_stdVecLen_hit "a" ρ m π la aa ta
            hlay_a ha hmemLen)
      have hval : evalExpr (.ult (.var "r") (.stdVecLen "a")) ρ =
          .ok (.b false) := by
        have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "a")
          ρ rB (BitVec.ofNat 64 la.length)
          (evalExpr_var_hit _ _ _ hr)
          (evalExpr_stdVecLen_some _ _ _ ha)
        have hfb : (rB.ult (BitVec.ofNat 64 la.length)) = false := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_false (by omega)
        rwa [hfb] at hult
      rw [hag]; exact hval
    have hexit : memEvalProgStmt prog 0 vecCopyIfLoop ρ m π =
        .ok ((ρ, m, π), .fellThrough) :=
      memEvalProgStmt_while_false prog 0 _ _ _ _ _ hguardF
    have hpair : (r, w, lo) = (r', w', lo') := by
      cases G with
      | zero => simpa [copyIfFwd] using hfwd
      | succ G =>
        have hneg : ¬ r < la.length := by omega
        simpa [copyIfFwd, dite_eq_right hneg] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    exact ⟨ρ, m, hexit, ha, hout, ⟨rB, hr, hrN⟩, ⟨wB, hw, hwN⟩,
      hx, hmem_o, hmem_a⟩
  | succ F ih =>
    by_cases hlt : r < la.length
    · have hlenN : (BitVec.ofNat 64 la.length).toNat = la.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
      have hmemLen : memLoad m aa ta 0 =
          .ok (BitVec.ofNat 32 la.length) := by
        rw [← hn]
        exact memLoad_cellsAt m aa ta 0 (na :: la) na hmem_a (by simp)
      have hguardT : memEvalExpr
          (.ult (.var "r") (.stdVecLen "a")) ρ m π =
          .ok (.b true) := by
        have hag : memEvalExpr (.ult (.var "r") (.stdVecLen "a")) ρ m π =
            evalExpr (.ult (.var "r") (.stdVecLen "a")) ρ :=
          memEvalExpr_ult_agree (.var "r") (.stdVecLen "a") ρ m π
            (memEvalExpr_var _ _ _ _)
            (memEvalExpr_stdVecLen_hit "a" ρ m π la aa ta
              hlay_a ha hmemLen)
        have hval : evalExpr (.ult (.var "r") (.stdVecLen "a")) ρ =
            .ok (.b true) := by
          have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "a")
            ρ rB (BitVec.ofNat 64 la.length)
            (evalExpr_var_hit _ _ _ hr)
            (evalExpr_stdVecLen_some _ _ _ ha)
          have htb : (rB.ult (BitVec.ofNat 64 la.length)) = true := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_true (by omega)
          rwa [htb] at hult
        rw [hag]; exact hval
      obtain ⟨y, hy⟩ := hread r hlt
      cir_fuel_step (F, G, la.length - (r + 1))
      by_cases hkeep : (y != x) = true
      · have hkeeps1 : (((la.take (r + 1)).filter
            (fun z => (z != x))).length = w + 1) := by
          rw [copyIfFilter_take_succ x la r y hy hkeep, hwcnt]
        have hwlt : w < lo.length := by
          have hsplit := copyIfFilter_split x la r (by omega)
          omega
        obtain ⟨wOld, hwget⟩ : ∃ z, lo[w]? = some z :=
          ⟨lo[w], List.getElem?_eq_getElem hwlt⟩
        have hF'' : la.length - (r + 1) ≤ F := by omega
        have hG'' : la.length - (r + 1) ≤ G' := by omega
        have hlen' : (lo.set w y).length = lo.length := by
          simp [List.length_set]
        have hlo64' : (lo.set w y).length < 2 ^ 64 := by
          rw [hlen']; exact hlo64
        have hno' : no = BitVec.ofNat 32 (lo.set w y).length := by
          rw [hlen']; exact hno
        have hwcnt' : (((la.take (r + 1)).filter
            (fun z => (z != x))).length = w + 1) := hkeeps1
        have hcap' : (la.filter (fun y => (y != x))).length ≤
            (lo.set w y).length := by
          rw [hlen']; exact hcap
        have hfwd' : copyIfFwd x la (lo.set w y) G' (r + 1) (w + 1) =
            .ok (r', w', lo') := by
          have h := hfwd
          simp only [copyIfFwd, dite_eq_left hlt, hy, hkeep, hwget] at h
          exact h
        obtain ⟨ρ₁, m₁, hbody, ha₁, hout₁, ⟨rB₁, hrB₁, hrN₁⟩,
            ⟨wB₁, hwB₁, hwN₁⟩, hx₁, hmem_o₁, hmem_a₁⟩ :=
          memCopyIfBody_copy prog F ρ m π la lo x r w rB wB y wOld
            aa ao ta to na no hlay_a hlay_o hmem_a hmem_o hn hno haa
            hrN hwN hla64 hlo64 ha hout hx hr hw hlt hy hwget hwlt
            hkeep
        obtain ⟨ρ', m', hloop, ha', hout', ⟨rB', hrB', hrN'⟩,
            ⟨wB', hwB', hwN'⟩, hx', hmem_o', hmem_a'⟩ :=
          ih (G := G') (ρ := ρ₁) (m := m₁) (lo := lo.set w y)
            (r := r + 1) (w := w + 1) (rB := rB₁) (wB := wB₁)
            (hrN := hrN₁) (hwN := hwN₁)
            (hlo64 := hlo64')
            (ha := ha₁) (hout := hout₁) (hx := hx₁)
            (hr := hrB₁) (hw := hwB₁)
            (hmem_a := hmem_a₁) (hmem_o := hmem_o₁)
            (hle := by omega)
            (hF := hF'') (hG := hG'')
            (hwcnt := hwcnt') (hcap := hcap')
            (hno := hno') (hfwd := hfwd')
        refine ⟨ρ', m', ?_, ha', hout', ⟨rB', hrB', hrN'⟩,
          ⟨wB', hwB', hwN'⟩, hx', hmem_o', hmem_a'⟩
        have hwhile : memEvalProgStmt prog (F + 1) vecCopyIfLoop ρ m π =
            memEvalProgStmt prog F vecCopyIfLoop ρ₁ m₁ π := by
          cir_unfold_prog (vecCopyIfLoop, prog, F, hguardT, hbody)
        rw [hwhile]
        exact hloop
      · have hdrop : (y != x) = false := by
          cases h : (y != x) with
          | true => exact absurd h hkeep
          | false => rfl
        have hwcnt' : (((la.take (r + 1)).filter
            (fun z => (z != x))).length = w) := by
          rw [copyIfFilter_take_succ_drop x la r y hy hdrop, hwcnt]
        have hF' : la.length - (r + 1) ≤ F := by omega
        have hG' : la.length - (r + 1) ≤ G' := by omega
        have hfwd' : copyIfFwd x la lo G' (r + 1) w =
            .ok (r', w', lo') := by
          have h := hfwd
          simp only [copyIfFwd, dite_eq_left hlt, hy, hdrop] at h
          exact h
        obtain ⟨ρ₁, hbody, ha₁, hout₁, ⟨rB₁, hrB₁, hrN₁⟩,
            ⟨wB₁, hwB₁, hwN₁⟩, hx₁, hmem_o₁, hmem_a₁⟩ :=
          memCopyIfBody_drop prog F ρ m π la lo x r w rB wB y
            aa ao ta to na no hlay_a hlay_o hmem_a hmem_o
            hrN hwN hla64 ha hout hx hr hw hlt hy hdrop
        obtain ⟨ρ', m', hloop, ha', hout', ⟨rB', hrB', hrN'⟩,
            ⟨wB', hwB', hwN'⟩, hx', hmem_o', hmem_a'⟩ :=
          ih (G := G') (ρ := ρ₁) (m := m)
            (lo := lo)
            (r := r + 1) (w := w) (rB := rB₁) (wB := wB₁)
            (hrN := hrN₁) (hwN := hwN₁)
            (hlo64 := hlo64)
            (ha := ha₁) (hout := hout₁) (hx := hx₁)
            (hr := hrB₁) (hw := hwB₁)
            (hmem_a := hmem_a₁) (hmem_o := hmem_o₁)
            (hle := by omega)
            (hF := hF') (hG := hG')
            (hwcnt := hwcnt') (hcap := hcap)
            (hno := hno) (hfwd := hfwd')
        refine ⟨ρ', m', ?_, ha', hout', ⟨rB', hrB', hrN'⟩,
          ⟨wB', hwB', hwN'⟩, hx', hmem_o', hmem_a'⟩
        have hwhile : memEvalProgStmt prog (F + 1) vecCopyIfLoop ρ m π =
            memEvalProgStmt prog F vecCopyIfLoop ρ₁ m π := by
          cir_unfold_prog (vecCopyIfLoop, prog, F, hguardT, hbody)
        rw [hwhile]
        exact hloop
    · have him : r = la.length := by omega
      subst him
      have hlenN : (BitVec.ofNat 64 la.length).toNat = la.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
      have hmemLen : memLoad m aa ta 0 =
          .ok (BitVec.ofNat 32 la.length) := by
        rw [← hn]
        exact memLoad_cellsAt m aa ta 0 (na :: la) na hmem_a (by simp)
      have hguardF : memEvalExpr
          (.ult (.var "r") (.stdVecLen "a")) ρ m π =
          .ok (.b false) := by
        have hag : memEvalExpr (.ult (.var "r") (.stdVecLen "a")) ρ m π =
            evalExpr (.ult (.var "r") (.stdVecLen "a")) ρ :=
          memEvalExpr_ult_agree (.var "r") (.stdVecLen "a") ρ m π
            (memEvalExpr_var _ _ _ _)
            (memEvalExpr_stdVecLen_hit "a" ρ m π la aa ta
              hlay_a ha hmemLen)
        have hval : evalExpr (.ult (.var "r") (.stdVecLen "a")) ρ =
            .ok (.b false) := by
          have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "a")
            ρ rB (BitVec.ofNat 64 la.length)
            (evalExpr_var_hit _ _ _ hr)
            (evalExpr_stdVecLen_some _ _ _ ha)
          have hfb : (rB.ult (BitVec.ofNat 64 la.length)) = false := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_false (by omega)
          rwa [hfb] at hult
        rw [hag]; exact hval
      have hexit : memEvalProgStmt prog (F + 1) vecCopyIfLoop ρ m π =
          .ok ((ρ, m, π), .fellThrough) :=
        memEvalProgStmt_while_false prog (F + 1) _ _ _ _ _ hguardF
      have hpair : (la.length, w, lo) = (r', w', lo') := by
        cases G with
        | zero => simpa [copyIfFwd] using hfwd
        | succ G =>
          have hneg : ¬ la.length < la.length := by omega
          simpa [copyIfFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      exact ⟨ρ, m, hexit, ha, hout, ⟨rB, hr, hrN⟩, ⟨wB, hw, hwN⟩,
        hx, hmem_o, hmem_a⟩

/-- Memory loop, err leg: when the forward errors (short `out`),
    the scan hits the missing cell and fails loud (fuel
    induction; the value err loop justifies each step). -/
theorem memCopyIfLoop_err (prog : Prog) (F G : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lo : List (BitVec 32)) (x : BitVec 32)
    (r w : Nat) (rB wB : BitVec 64)
    (aa ao : Nat) (ta to : Nat) (na no : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_o : layoutLookup π "out" = some (ao, to))
    (hn : na = BitVec.ofNat 32 la.length)
    (hno : no = BitVec.ofNat 32 lo.length)
    (haa : aa ≠ ao)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hx : envLookup ρ "x" = some (.i32 x))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_o : memFind m ao = some ⟨to, true, no :: lo⟩)
    (hle : r ≤ la.length)
    (hF : la.length - r ≤ F) (hG : la.length - r ≤ G)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hfwd : copyIfFwd x la lo G r w = .error .AssertFail) :
    memEvalProgStmt prog F vecCopyIfLoop ρ m π =
      .error .AssertFail := by
  induction F generalizing G ρ m lo r w rB wB with
  | zero =>
    have him : r = la.length := by omega
    subst him
    cases G with
    | zero => exact absurd hfwd (by simp [copyIfFwd])
    | succ _ =>
      have hneg : ¬ la.length < la.length := by omega
      have hcon := hfwd
      simp only [copyIfFwd, dite_eq_right hneg] at hcon
      exact absurd hcon (by simp)
  | succ F ih =>
    by_cases hlt : r < la.length
    · have hlenN : (BitVec.ofNat 64 la.length).toNat = la.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
      have hmemLen : memLoad m aa ta 0 =
        .ok (BitVec.ofNat 32 la.length) := by
        rw [← hn]
        exact memLoad_cellsAt m aa ta 0 (na :: la) na hmem_a (by simp)
      have hguardT : memEvalExpr
          (.ult (.var "r") (.stdVecLen "a")) ρ m π =
          .ok (.b true) := by
        have hag : memEvalExpr (.ult (.var "r") (.stdVecLen "a")) ρ m π =
            evalExpr (.ult (.var "r") (.stdVecLen "a")) ρ :=
          memEvalExpr_ult_agree (.var "r") (.stdVecLen "a") ρ m π
            (memEvalExpr_var _ _ _ _)
            (memEvalExpr_stdVecLen_hit "a" ρ m π la aa ta
              hlay_a ha hmemLen)
        have hval : evalExpr (.ult (.var "r") (.stdVecLen "a")) ρ =
            .ok (.b true) := by
          have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "a")
            ρ rB (BitVec.ofNat 64 la.length)
            (evalExpr_var_hit _ _ _ hr)
            (evalExpr_stdVecLen_some _ _ _ ha)
          have htb : (rB.ult (BitVec.ofNat 64 la.length)) = true := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_true (by omega)
          rwa [htb] at hult
        rw [hag]; exact hval
      obtain ⟨y, hy⟩ := hread r hlt
      cir_fuel_step (F, G, la.length - (r + 1))
      by_cases hkeep : (y != x) = true
      · by_cases hmiss : lo[w]? = none
        · have hshort := memCopyIfBody_short prog F ρ m π la lo x
            r w rB wB y aa ao ta to na no hlay_a hlay_o hmem_a hmem_o
            hn hno hrN hwN hla64 hlo64 ha hout hx hr hw hlt hy hmiss
            hkeep
          have hwhile : memEvalProgStmt prog (F + 1) vecCopyIfLoop
              ρ m π = .error .AssertFail := by
            cir_unfold_prog (vecCopyIfLoop, prog, F, hguardT, hshort)
          exact hwhile
        · have hsome : ∃ z, lo[w]? = some z := by
            match h : lo[w]? with
            | none => exact absurd h hmiss
            | some z => exact ⟨z, rfl⟩
          obtain ⟨wOld, hwget⟩ := hsome
          have hwlt : w < lo.length := by
            by_cases h : w < lo.length
            · exact h
            · have hc' : lo.length ≤ w := by omega
              have hnone := List.getElem?_eq_none hc'
              exact absurd hnone hmiss
          have hF'' : la.length - (r + 1) ≤ F := by omega
          have hG'' : la.length - (r + 1) ≤ G' := by omega
          have hlo64' : (lo.set w y).length < 2 ^ 64 := by
            have hlen : (lo.set w y).length = lo.length := by
              simp [List.length_set]
            rw [hlen]; exact hlo64
          have hno' : no = BitVec.ofNat 32 (lo.set w y).length := by
            have hlen : (lo.set w y).length = lo.length := by
              simp [List.length_set]
            rw [hlen]; exact hno
          have hfwd' : copyIfFwd x la (lo.set w y) G' (r + 1) (w + 1) =
              .error .AssertFail := by
            have h := hfwd
            simp only [copyIfFwd, dite_eq_left hlt, hy, hkeep, hwget] at h
            exact h
          obtain ⟨ρ₁, m₁, hbody, ha₁, hout₁, ⟨rB₁, hrB₁, hrN₁⟩,
              ⟨wB₁, hwB₁, hwN₁⟩, hx₁, hmem_o₁, hmem_a₁⟩ :=
            memCopyIfBody_copy prog F ρ m π la lo x r w rB wB y wOld
              aa ao ta to na no hlay_a hlay_o hmem_a hmem_o hn hno haa
              hrN hwN hla64 hlo64 ha hout hx hr hw hlt hy hwget hwlt
              hkeep
          have hloop : memEvalProgStmt prog F vecCopyIfLoop ρ₁ m₁ π =
              .error .AssertFail :=
            ih (G := G') (ρ := ρ₁) (m := m₁) (lo := lo.set w y)
              (r := r + 1) (w := w + 1) (rB := rB₁) (wB := wB₁)
              (hrN := hrN₁) (hwN := hwN₁)
              (hlo64 := hlo64')
              (ha := ha₁) (hout := hout₁) (hx := hx₁)
              (hr := hrB₁) (hw := hwB₁)
              (hmem_a := hmem_a₁) (hmem_o := hmem_o₁)
              (hle := by omega)
              (hF := hF'') (hG := hG'')
              (hno := hno') (hfwd := hfwd')
          have hwhile : memEvalProgStmt prog (F + 1) vecCopyIfLoop
              ρ m π = .error .AssertFail := by
            cir_unfold_prog (vecCopyIfLoop, prog, F, hguardT, hbody)
            exact hloop
          exact hwhile
      · have hdrop : (y != x) = false := by
          cases h : (y != x) with
          | true => exact absurd h hkeep
          | false => rfl
        have hF' : la.length - (r + 1) ≤ F := by omega
        have hG' : la.length - (r + 1) ≤ G' := by omega
        have hfwd' : copyIfFwd x la lo G' (r + 1) w =
            .error .AssertFail := by
          have h := hfwd
          simp only [copyIfFwd, dite_eq_left hlt, hy, hdrop] at h
          exact h
        obtain ⟨ρ₁, hbody, ha₁, hout₁, ⟨rB₁, hrB₁, hrN₁⟩,
            ⟨wB₁, hwB₁, hwN₁⟩, hx₁, hmem_o₁, hmem_a₁⟩ :=
          memCopyIfBody_drop prog F ρ m π la lo x r w rB wB y
            aa ao ta to na no hlay_a hlay_o hmem_a hmem_o
            hrN hwN hla64 ha hout hx hr hw hlt hy hdrop
        have hloop : memEvalProgStmt prog F vecCopyIfLoop ρ₁ m π =
            .error .AssertFail :=
          ih (G := G') (ρ := ρ₁) (m := m)
            (lo := lo)
            (r := r + 1) (w := w) (rB := rB₁) (wB := wB₁)
            (hrN := hrN₁) (hwN := hwN₁)
            (hlo64 := hlo64)
            (ha := ha₁) (hout := hout₁) (hx := hx₁)
            (hr := hrB₁) (hw := hwB₁)
            (hmem_a := hmem_a₁) (hmem_o := hmem_o₁)
            (hle := by omega)
            (hF := hF') (hG := hG')
            (hno := hno) (hfwd := hfwd')
        have hwhile : memEvalProgStmt prog (F + 1) vecCopyIfLoop
            ρ m π = .error .AssertFail := by
          cir_unfold_prog (vecCopyIfLoop, prog, F, hguardT, hbody)
          exact hloop
        exact hwhile
    · have him : r = la.length := by omega
      subst him
      cases G with
      | zero => exact absurd hfwd (by simp [copyIfFwd])
      | succ _ =>
        have hneg : ¬ la.length < la.length := by omega
        have hcon := hfwd
        simp only [copyIfFwd, dite_eq_right hneg] at hcon
        exact absurd hcon (by simp)

/-! ## Value entry -/

/-- Value entry, ok leg: the prelude binds `r`/`w`, the loop
    threads the keep count with the forward equation, and `w`
    returns (measure-exact forward fuel). -/
theorem evalProgFunc_vecCopyIf_ok (F : Nat)
    (la lo : List (BitVec 32)) (x : BitVec 32)
    (w' : Nat) (lo' : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length + 1 ≤ F)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hcap0 : (la.filter (fun y => (y != x))).length ≤ lo.length)
    (hfwd : copyIfFwd x la lo la.length 0 0 =
      .ok (la.length, w', lo')) :
    evalProgFunc vecCopyIfProg F vecCopyIfFunc
      [.stdVecVal la, .stdVecVal lo, .i32 x] =
      .ok (.u64 (BitVec.ofNat 64 w')) := by
  have hbind : bindArgs vecCopyIfFunc.args
      [.stdVecVal la, .stdVecVal lo, .i32 x] =
      some [("a", .stdVecVal la), ("out", .stdVecVal lo),
        ("x", .i32 x)] := rfl
  have hbody : vecCopyIfFunc.body =
      (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq vecCopyIfLoop
            (.return_ (.var "w"))))) := rfl
  have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletR := revLet vecCopyIfProg F "r" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
    (.u64 (BitVec.ofNat 64 0)) hlitV
  have hlitVW : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("a", .stdVecVal la), ("out", .stdVecVal lo),
        ("x", .i32 x)] "r" (.u64 (BitVec.ofNat 64 0))) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletW := revLet vecCopyIfProg F "w" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (envExtend [("a", .stdVecVal la), ("out", .stdVecVal lo),
      ("x", .i32 x)] "r" (.u64 (BitVec.ofNat 64 0)))
    (.u64 (BitVec.ofNat 64 0)) hlitVW
  have hv0N : (BitVec.ofNat 64 0).toNat = 0 := by
    rw [BitVec.toNat_ofNat]
  have ha₂ : envLookup (envExtend (envExtend
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "a" =
      some (.stdVecVal la) := by
    simp [envExtend, envLookup, show ("a" : String) ≠ "w" by decide,
      show ("a" : String) ≠ "r" by decide]
  have hout₂ : envLookup (envExtend (envExtend
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "out" =
      some (.stdVecVal lo) := by
    simp [envExtend, envLookup, show ("out" : String) ≠ "w" by decide,
      show ("out" : String) ≠ "r" by decide,
      show ("out" : String) ≠ "a" by decide]
  have hx₂ : envLookup (envExtend (envExtend
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "x" =
      some (.i32 x) := by
    simp [envExtend, envLookup, show ("x" : String) ≠ "w" by decide,
      show ("x" : String) ≠ "r" by decide]
  have hr₂ : envLookup (envExtend (envExtend
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "r" =
      some (.u64 (BitVec.ofNat 64 0)) := by
    simp [envExtend, envLookup, show ("r" : String) ≠ "w" by decide]
  have hw₂ : envLookup (envExtend (envExtend
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "w" =
      some (.u64 (BitVec.ofNat 64 0)) := by simp [envExtend, envLookup]
  obtain ⟨ρ', hloop, ha', hout', ⟨rB', hrB', hrN'⟩,
      ⟨wB', hwB', hwN'⟩⟩ :=
    valCopyIfLoop_ok vecCopyIfProg F la.length
      (envExtend (envExtend
        [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
          "r" (.u64 (BitVec.ofNat 64 0)))
          "w" (.u64 (BitVec.ofNat 64 0)))
      la lo x 0 0
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
      lo' la.length w' hv0N hv0N hla64 hlo64
      ha₂ hout₂ hx₂ hr₂ hw₂ (Nat.zero_le _)
      (by omega) (by omega) hread (by simp) hcap0 hfwd
  have hle_w : w' ≤ lo.length :=
    copyIfFwd_le x la lo la.length 0 0 w' lo'
      (Nat.zero_le _) (by omega) hread (by simp) hcap0 hfwd
  have hw'lt : w' < 2 ^ 64 := by omega
  have hwB'eq : wB' = BitVec.ofNat 64 w' := by
    apply BitVec.eq_of_toNat_eq
    rw [hwN', BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt hw'lt).symm
  have hevW' : evalExpr (.var "w") ρ' =
      .ok (.u64 (BitVec.ofNat 64 w')) := by
    rw [← hwB'eq]; exact evalExpr_var_hit _ _ _ hwB'
  have hret := evalProgStmt_return vecCopyIfProg F (.var "w") ρ'
    (.u64 (BitVec.ofNat 64 w')) hevW'
  simp only [evalProgFunc, hbind, hbody]
  rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletR,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletW,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hloop,
    hret]

/-- Value entry, err leg: the prelude binds, the loop hits the
    short `out` and fails loud (the `return` is unreachable). -/
theorem evalProgFunc_vecCopyIf_err (F : Nat)
    (la lo : List (BitVec 32)) (x : BitVec 32)
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length + 1 ≤ F)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hfwd : copyIfFwd x la lo la.length 0 0 = .error .AssertFail) :
    evalProgFunc vecCopyIfProg F vecCopyIfFunc
      [.stdVecVal la, .stdVecVal lo, .i32 x] =
      .error .AssertFail := by
  have hbind : bindArgs vecCopyIfFunc.args
      [.stdVecVal la, .stdVecVal lo, .i32 x] =
      some [("a", .stdVecVal la), ("out", .stdVecVal lo),
        ("x", .i32 x)] := rfl
  have hbody : vecCopyIfFunc.body =
      (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq vecCopyIfLoop
            (.return_ (.var "w"))))) := rfl
  have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletR := revLet vecCopyIfProg F "r" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
    (.u64 (BitVec.ofNat 64 0)) hlitV
  have hlitVW : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("a", .stdVecVal la), ("out", .stdVecVal lo),
        ("x", .i32 x)] "r" (.u64 (BitVec.ofNat 64 0))) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletW := revLet vecCopyIfProg F "w" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (envExtend [("a", .stdVecVal la), ("out", .stdVecVal lo),
      ("x", .i32 x)] "r" (.u64 (BitVec.ofNat 64 0)))
    (.u64 (BitVec.ofNat 64 0)) hlitVW
  have hv0N : (BitVec.ofNat 64 0).toNat = 0 := by
    rw [BitVec.toNat_ofNat]
  have ha₂ : envLookup (envExtend (envExtend
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "a" =
      some (.stdVecVal la) := by
    simp [envExtend, envLookup, show ("a" : String) ≠ "w" by decide,
      show ("a" : String) ≠ "r" by decide]
  have hout₂ : envLookup (envExtend (envExtend
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "out" =
      some (.stdVecVal lo) := by
    simp [envExtend, envLookup, show ("out" : String) ≠ "w" by decide,
      show ("out" : String) ≠ "r" by decide,
      show ("out" : String) ≠ "a" by decide]
  have hx₂ : envLookup (envExtend (envExtend
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "x" =
      some (.i32 x) := by
    simp [envExtend, envLookup, show ("x" : String) ≠ "w" by decide,
      show ("x" : String) ≠ "r" by decide]
  have hr₂ : envLookup (envExtend (envExtend
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "r" =
      some (.u64 (BitVec.ofNat 64 0)) := by
    simp [envExtend, envLookup, show ("r" : String) ≠ "w" by decide]
  have hw₂ : envLookup (envExtend (envExtend
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "w" =
      some (.u64 (BitVec.ofNat 64 0)) := by simp [envExtend, envLookup]
  have hloop : evalProgStmt vecCopyIfProg F vecCopyIfLoop
      (envExtend (envExtend
        [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
          "r" (.u64 (BitVec.ofNat 64 0)))
          "w" (.u64 (BitVec.ofNat 64 0))) =
      .error .AssertFail :=
    valCopyIfLoop_err vecCopyIfProg F la.length
      (envExtend (envExtend
        [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
          "r" (.u64 (BitVec.ofNat 64 0)))
          "w" (.u64 (BitVec.ofNat 64 0)))
      la lo x 0 0
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
      hv0N hv0N hla64 hlo64
      ha₂ hout₂ hx₂ hr₂ hw₂ (Nat.zero_le _)
      (by omega) (by omega) hread hfwd
  simp only [evalProgFunc, hbind, hbody]
  rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletR,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletW,
    evalProgStmt_seq_err _ _ _ _ _ _ hloop]

/-! ## Memory entry -/

/-- Memory entry, ok leg: same prelude on the two pinned blocks,
    the memory loop, and the `w` return. -/
theorem memEvalProgFunc_vecCopyIf_ok (F : Nat)
    (la lo : List (BitVec 32)) (x : BitVec 32)
    (w' : Nat) (lo' : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length + 1 ≤ F)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hcap0 : (la.filter (fun y => (y != x))).length ≤ lo.length)
    (hfwd : copyIfFwd x la lo la.length 0 0 =
      .ok (la.length, w', lo')) :
    memEvalProgFunc vecCopyIfProg F vecCopyIfFunc
      [.stdVecVal la, .stdVecVal lo, .i32 x] =
      .ok (.u64 (BitVec.ofNat 64 w')) := by
  have hbind := bindMemArgs_vecCopyIf la lo x
  have hbody : vecCopyIfFunc.body =
      (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq vecCopyIfLoop
            (.return_ (.var "w"))))) := rfl
  have hmem_a₀ : memFind
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ 1 =
      some ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩ :=
    memFind_cons_hit _ _ _ _ _
  have hmem_o₀ : memFind
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ 0 =
      some ⟨0, true, (BitVec.ofNat 32 lo.length) :: lo⟩ := by
    rw [memFind_cons_miss _ _ _ _ _ _ (by decide : (0 : Nat) ≠ 1)]
    exact memFind_cons_hit _ _ _ _ _
  have hlay_a₀ : layoutLookup [("a", 1, 1), ("out", 0, 0)]
      "a" = some (1, 1) := by simp [layoutLookup]
  have hlay_o₀ : layoutLookup [("a", 1, 1), ("out", 0, 0)]
      "out" = some (0, 0) := by simp [layoutLookup]
  have haa₀ : (1 : Nat) ≠ 0 := by decide
  have hlitM : memEvalExpr
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
      [("a", 1, 1), ("out", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)] :=
    memEvalExpr_lit _ _ _ _
  have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletR := memRevLet vecCopyIfProg F "r" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
    ⟨2, [(1, ⟨1, true,
      (BitVec.ofNat 32 la.length) :: la⟩),
      (0, ⟨0, true,
      (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
    [("a", 1, 1), ("out", 0, 0)]
    (.u64 (BitVec.ofNat 64 0))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) (by intro h; cases h) hlitM hlitV
  have hlitMW : memEvalExpr
      (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("a", .stdVecVal la), ("out", .stdVecVal lo),
        ("x", .i32 x)] "r" (.u64 (BitVec.ofNat 64 0)))
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
      [("a", 1, 1), ("out", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend [("a", .stdVecVal la), ("out", .stdVecVal lo),
          ("x", .i32 x)] "r" (.u64 (BitVec.ofNat 64 0))) :=
    memEvalExpr_lit _ _ _ _
  have hlitVW : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("a", .stdVecVal la), ("out", .stdVecVal lo),
        ("x", .i32 x)] "r" (.u64 (BitVec.ofNat 64 0))) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletW := memRevLet vecCopyIfProg F "w" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (envExtend [("a", .stdVecVal la), ("out", .stdVecVal lo),
      ("x", .i32 x)] "r" (.u64 (BitVec.ofNat 64 0)))
    ⟨2, [(1, ⟨1, true,
      (BitVec.ofNat 32 la.length) :: la⟩),
      (0, ⟨0, true,
      (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
    [("a", 1, 1), ("out", 0, 0)]
    (.u64 (BitVec.ofNat 64 0))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) (by intro h; cases h) hlitMW hlitVW
  have hv0N : (BitVec.ofNat 64 0).toNat = 0 := by
    rw [BitVec.toNat_ofNat]
  have ha₃ : envLookup (envExtend (envExtend
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "a" =
      some (.stdVecVal la) := by
    simp [envExtend, envLookup, show ("a" : String) ≠ "w" by decide,
      show ("a" : String) ≠ "r" by decide]
  have hout₃ : envLookup (envExtend (envExtend
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "out" =
      some (.stdVecVal lo) := by
    simp [envExtend, envLookup, show ("out" : String) ≠ "w" by decide,
      show ("out" : String) ≠ "r" by decide,
      show ("out" : String) ≠ "a" by decide]
  have hx₃ : envLookup (envExtend (envExtend
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "x" =
      some (.i32 x) := by
    simp [envExtend, envLookup, show ("x" : String) ≠ "w" by decide,
      show ("x" : String) ≠ "r" by decide]
  have hr₃ : envLookup (envExtend (envExtend
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "r" =
      some (.u64 (BitVec.ofNat 64 0)) := by
    simp [envExtend, envLookup, show ("r" : String) ≠ "w" by decide]
  have hw₃ : envLookup (envExtend (envExtend
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "w" =
      some (.u64 (BitVec.ofNat 64 0)) := by simp [envExtend, envLookup]
  obtain ⟨ρ', m', hloop, ha', hout', ⟨rB', hrB', hrN'⟩,
      ⟨wB', hwB', hwN'⟩, hx', hmem_o', hmem_a'⟩ :=
    memCopyIfLoop_ok vecCopyIfProg F la.length
      (envExtend (envExtend
        [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
          "r" (.u64 (BitVec.ofNat 64 0)))
          "w" (.u64 (BitVec.ofNat 64 0)))
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
      [("a", 1, 1), ("out", 0, 0)]
      la lo x 0 0
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
      lo' la.length w' 1 0 1 0
      (BitVec.ofNat 32 la.length) (BitVec.ofNat 32 lo.length)
      (hlay_a := hlay_a₀) (hlay_o := hlay_o₀)
      (hn := rfl) (hno := rfl)
      (haa := haa₀)
      (hrN := hv0N) (hwN := hv0N)
      (hla64 := hla64) (hlo64 := hlo64)
      (ha := ha₃) (hout := hout₃) (hx := hx₃)
      (hr := hr₃) (hw := hw₃)
      (hmem_a := hmem_a₀) (hmem_o := hmem_o₀)
      (hle := Nat.zero_le _)
      (hF := by omega) (hG := by omega)
      (hread := hread) (hwcnt := by simp) (hcap := hcap0)
      (hfwd := hfwd)
  have hle_w : w' ≤ lo.length :=
    copyIfFwd_le x la lo la.length 0 0 w' lo'
      (Nat.zero_le _) (by omega) hread (by simp) hcap0 hfwd
  have hw'lt : w' < 2 ^ 64 := by omega
  have hwB'eq : wB' = BitVec.ofNat 64 w' := by
    apply BitVec.eq_of_toNat_eq
    rw [hwN', BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt hw'lt).symm
  have hevW'V : evalExpr (.var "w") ρ' =
      .ok (.u64 (BitVec.ofNat 64 w')) := by
    rw [← hwB'eq]; exact evalExpr_var_hit _ _ _ hwB'
  have hevW' : memEvalExpr (.var "w") ρ' m'
      [("a", 1, 1), ("out", 0, 0)] =
      .ok (.u64 (BitVec.ofNat 64 w')) :=
    (memEvalExpr_var _ _ _ _).trans hevW'V
  have hret := memEvalProgStmt_return vecCopyIfProg F
    (.var "w") ρ' m' [("a", 1, 1), ("out", 0, 0)]
    (.u64 (BitVec.ofNat 64 w')) hevW'
  simp only [memEvalProgFunc, hbind, hbody]
  rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletR,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletW,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hloop,
    hret]

/-- Memory entry, err leg: same prelude, the loop hits the
    short `out` and fails loud (the `return` is unreachable). -/
theorem memEvalProgFunc_vecCopyIf_err (F : Nat)
    (la lo : List (BitVec 32)) (x : BitVec 32)
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length + 1 ≤ F)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hfwd : copyIfFwd x la lo la.length 0 0 = .error .AssertFail) :
    memEvalProgFunc vecCopyIfProg F vecCopyIfFunc
      [.stdVecVal la, .stdVecVal lo, .i32 x] =
      .error .AssertFail := by
  have hbind := bindMemArgs_vecCopyIf la lo x
  have hbody : vecCopyIfFunc.body =
      (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq vecCopyIfLoop
            (.return_ (.var "w"))))) := rfl
  have hmem_a₀ : memFind
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ 1 =
      some ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩ :=
    memFind_cons_hit _ _ _ _ _
  have hmem_o₀ : memFind
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ 0 =
      some ⟨0, true, (BitVec.ofNat 32 lo.length) :: lo⟩ := by
    rw [memFind_cons_miss _ _ _ _ _ _ (by decide : (0 : Nat) ≠ 1)]
    exact memFind_cons_hit _ _ _ _ _
  have hlay_a₀ : layoutLookup [("a", 1, 1), ("out", 0, 0)]
      "a" = some (1, 1) := by simp [layoutLookup]
  have hlay_o₀ : layoutLookup [("a", 1, 1), ("out", 0, 0)]
      "out" = some (0, 0) := by simp [layoutLookup]
  have haa₀ : (1 : Nat) ≠ 0 := by decide
  have hlitM : memEvalExpr
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
      [("a", 1, 1), ("out", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)] :=
    memEvalExpr_lit _ _ _ _
  have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletR := memRevLet vecCopyIfProg F "r" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
    ⟨2, [(1, ⟨1, true,
      (BitVec.ofNat 32 la.length) :: la⟩),
      (0, ⟨0, true,
      (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
    [("a", 1, 1), ("out", 0, 0)]
    (.u64 (BitVec.ofNat 64 0))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) (by intro h; cases h) hlitM hlitV
  have hlitMW : memEvalExpr
      (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("a", .stdVecVal la), ("out", .stdVecVal lo),
        ("x", .i32 x)] "r" (.u64 (BitVec.ofNat 64 0)))
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
      [("a", 1, 1), ("out", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend [("a", .stdVecVal la), ("out", .stdVecVal lo),
          ("x", .i32 x)] "r" (.u64 (BitVec.ofNat 64 0))) :=
    memEvalExpr_lit _ _ _ _
  have hlitVW : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("a", .stdVecVal la), ("out", .stdVecVal lo),
        ("x", .i32 x)] "r" (.u64 (BitVec.ofNat 64 0))) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletW := memRevLet vecCopyIfProg F "w" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (envExtend [("a", .stdVecVal la), ("out", .stdVecVal lo),
      ("x", .i32 x)] "r" (.u64 (BitVec.ofNat 64 0)))
    ⟨2, [(1, ⟨1, true,
      (BitVec.ofNat 32 la.length) :: la⟩),
      (0, ⟨0, true,
      (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
    [("a", 1, 1), ("out", 0, 0)]
    (.u64 (BitVec.ofNat 64 0))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) (by intro h; cases h) hlitMW hlitVW
  have hv0N : (BitVec.ofNat 64 0).toNat = 0 := by
    rw [BitVec.toNat_ofNat]
  have ha₃ : envLookup (envExtend (envExtend
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "a" =
      some (.stdVecVal la) := by
    simp [envExtend, envLookup, show ("a" : String) ≠ "w" by decide,
      show ("a" : String) ≠ "r" by decide]
  have hout₃ : envLookup (envExtend (envExtend
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "out" =
      some (.stdVecVal lo) := by
    simp [envExtend, envLookup, show ("out" : String) ≠ "w" by decide,
      show ("out" : String) ≠ "r" by decide,
      show ("out" : String) ≠ "a" by decide]
  have hx₃ : envLookup (envExtend (envExtend
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "x" =
      some (.i32 x) := by
    simp [envExtend, envLookup, show ("x" : String) ≠ "w" by decide,
      show ("x" : String) ≠ "r" by decide]
  have hr₃ : envLookup (envExtend (envExtend
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "r" =
      some (.u64 (BitVec.ofNat 64 0)) := by
    simp [envExtend, envLookup, show ("r" : String) ≠ "w" by decide]
  have hw₃ : envLookup (envExtend (envExtend
      [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
        "r" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "w" =
      some (.u64 (BitVec.ofNat 64 0)) := by simp [envExtend, envLookup]
  have hloop : memEvalProgStmt vecCopyIfProg F vecCopyIfLoop
      (envExtend (envExtend
        [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
          "r" (.u64 (BitVec.ofNat 64 0)))
          "w" (.u64 (BitVec.ofNat 64 0)))
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
      [("a", 1, 1), ("out", 0, 0)] =
      .error .AssertFail :=
    memCopyIfLoop_err vecCopyIfProg F la.length
      (envExtend (envExtend
        [("a", .stdVecVal la), ("out", .stdVecVal lo), ("x", .i32 x)]
          "r" (.u64 (BitVec.ofNat 64 0)))
          "w" (.u64 (BitVec.ofNat 64 0)))
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
      [("a", 1, 1), ("out", 0, 0)]
      la lo x 0 0
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
      1 0 1 0
      (BitVec.ofNat 32 la.length) (BitVec.ofNat 32 lo.length)
      (hlay_a := hlay_a₀) (hlay_o := hlay_o₀)
      (hn := rfl) (hno := rfl)
      (haa := haa₀)
      (hrN := hv0N) (hwN := hv0N)
      (hla64 := hla64) (hlo64 := hlo64)
      (ha := ha₃) (hout := hout₃) (hx := hx₃)
      (hr := hr₃) (hw := hw₃)
      (hmem_a := hmem_a₀) (hmem_o := hmem_o₀)
      (hle := Nat.zero_le _)
      (hF := by omega) (hG := by omega)
      (hread := hread) (hfwd := hfwd)
  simp only [memEvalProgFunc, hbind, hbody]
  rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletR,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletW,
    memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hloop]

/-! ## Transfer (`memEval = Eval`) -/

/-- Transfer for `vec_copy_if`, ok leg: memory evaluation agrees
    with value evaluation on a successful scan. -/
theorem memTransferProg_vecCopyIf_ok (F : Nat)
    (la lo : List (BitVec 32)) (x : BitVec 32)
    (w' : Nat) (lo' : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length + 1 ≤ F)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hcap0 : (la.filter (fun y => (y != x))).length ≤ lo.length)
    (hfwd : copyIfFwd x la lo la.length 0 0 =
      .ok (la.length, w', lo'))
    (_h : oracleNoalias vecCopyIfFunc
      [.stdVecVal la, .stdVecVal lo, .i32 x]) :
    memEvalProgFunc vecCopyIfProg F vecCopyIfFunc
      [.stdVecVal la, .stdVecVal lo, .i32 x] =
      evalProgFunc vecCopyIfProg F vecCopyIfFunc
        [.stdVecVal la, .stdVecVal lo, .i32 x] := by
  rw [memEvalProgFunc_vecCopyIf_ok F la lo x w' lo'
    hla64 hlo64 hF hread hcap0 hfwd,
    evalProgFunc_vecCopyIf_ok F la lo x w' lo'
    hla64 hlo64 hF hread hcap0 hfwd]

/-- Transfer for `vec_copy_if`, err leg: both sides fail loud on
    a short `out`. -/
theorem memTransferProg_vecCopyIf_err (F : Nat)
    (la lo : List (BitVec 32)) (x : BitVec 32)
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length + 1 ≤ F)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hfwd : copyIfFwd x la lo la.length 0 0 = .error .AssertFail)
    (_h : oracleNoalias vecCopyIfFunc
      [.stdVecVal la, .stdVecVal lo, .i32 x]) :
    memEvalProgFunc vecCopyIfProg F vecCopyIfFunc
      [.stdVecVal la, .stdVecVal lo, .i32 x] =
      evalProgFunc vecCopyIfProg F vecCopyIfFunc
        [.stdVecVal la, .stdVecVal lo, .i32 x] := by
  rw [memEvalProgFunc_vecCopyIf_err F la lo x
    hla64 hlo64 hF hread hfwd,
    evalProgFunc_vecCopyIf_err F la lo x
    hla64 hlo64 hF hread hfwd]

/-! ## Closing spec (against the independent oracle) -/

/-- Closed copy_if contract, ok leg: a successful run returns the
    survivor count, which is exactly the independent `List.filter`
    length (P2-M12). -/
theorem evalProgFunc_vecCopyIf_spec_ok (F : Nat)
    (la lo : List (BitVec 32)) (x : BitVec 32)
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length + 1 ≤ F)
    (hcap0 : (la.filter (fun y => (y != x))).length ≤ lo.length) :
    ∃ w', evalProgFunc vecCopyIfProg F vecCopyIfFunc
      [.stdVecVal la, .stdVecVal lo, .i32 x] =
      .ok (.u64 (BitVec.ofNat 64 w')) ∧
      w' = (la.filter (fun y => (y != x))).length := by
  have hread : ∀ p, p < la.length → ∃ y, la[p]? = some y :=
    fun p hp => ⟨_, List.getElem?_eq_getElem hp⟩
  obtain ⟨w', lo', hfwd⟩ := copyIfFwd_ok x la lo la.length 0 0
    (Nat.zero_le _) (by omega) hread (by simp) hcap0
  have heval := evalProgFunc_vecCopyIf_ok F la lo x w' lo'
    hla64 hlo64 hF hread hcap0 hfwd
  obtain ⟨hpref, _hle, hlen⟩ := copyIfFwd_prefix x la lo la.length 0 0 w'
    lo lo' (Nat.zero_le _) (by omega) rfl hread (by simp) hcap0
    (by simp) (fun j _ => rfl) hfwd
  have hb := copyIfFwd_le x la lo la.length 0 0 w' lo'
    (Nat.zero_le _) (by omega) hread (by simp) hcap0 hfwd
  have htw : (lo'.take w').length = w' := by
    rw [List.length_take, Nat.min_eq_left (by omega : w' ≤ lo'.length)]
  have hflen : (lo'.take w').length =
      (la.filter (fun y => (y != x))).length := by rw [hpref]
  exact ⟨w', heval, by omega⟩

/-- Closed copy_if contract, err leg: a short `out` fails loud. -/
theorem evalProgFunc_vecCopyIf_spec_err (F : Nat)
    (la lo : List (BitVec 32)) (x : BitVec 32)
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length + 1 ≤ F)
    (hmore : lo.length < (la.filter (fun y => (y != x))).length) :
    evalProgFunc vecCopyIfProg F vecCopyIfFunc
      [.stdVecVal la, .stdVecVal lo, .i32 x] =
      .error .AssertFail := by
  have hread : ∀ p, p < la.length → ∃ y, la[p]? = some y :=
    fun p hp => ⟨_, List.getElem?_eq_getElem hp⟩
  have hfwd := copyIfFwd_err_of_overflow x la lo hread hmore
  exact evalProgFunc_vecCopyIf_err F la lo x hla64 hlo64 hF hread hfwd
