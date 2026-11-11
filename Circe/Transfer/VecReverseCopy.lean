/-
Circe.Transfer.VecReverseCopy — mem transfer for the
caller-record out-of-place reverse (`vec_reverse_copy`, P2-M17).

Mirrors the value side (`valReverseCopyBody_keep/_short`,
`valReverseCopyLoop_ok/_err` in `Circe.Emit.VecReverseCopy`)
step for step on the memory layer: the read-only `a` block pins
its snapshot while the record block threads through `memStore`
in lockstep (the `a` block framed across each `out` store via
`memFind_memStore_other`); the countdown read comes from `a`
through `memLoad` (no predecessor read — the keep/store test
is only the `w < out.size()` guard), the store is guarded by
the inner `ult` (the short-`out` leg fires
the loud `AssertFail` through guard-false + fail), and the loop
re-inducts over `(ρ, m, π)` with the forward equation
threading (two fuels) plus the reversed-prefix invariant, the
`w + j = la.length` coupling, and the record bound. Entries
close against the forward contract; the closing specs tie the
`u64` copied count to the `List.reverse` prefix over the pure
oracle (`reverseCopyFwd_*` in `Circe.Specs`).
-/
import Circe.Transfer.VecReverse
import Circe.Emit.VecReverseCopy
import Circe.Specs

/-! ## Binding (closed form) -/

/-- Reverse-copy binding pins two snapshots: the shared-borrow
    input at addr `1`, the mut-borrow record at addr `0`
    (tail-first allocation order — the M12/M16 precedent; the
    argument roles match M16 exactly). -/
theorem bindMemArgs_vecReverseCopy (la lo : List (BitVec 32)) :
    bindMemArgs vecReverseCopyFunc.args
      [.stdVecVal la, .stdVecVal lo] emptyMem =
      some ([("a", .stdVecVal la), ("out", .stdVecVal lo)],
        (⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 la.length) :: la⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem),
        [("a", 1, 1), ("out", 0, 0)]) := by
  rfl

/-- Reverse-copy footprint is two disjoint singletons. -/
theorem oracleNoalias_vecReverseCopy (la lo : List (BitVec 32)) :
    oracleNoalias vecReverseCopyFunc
      [.stdVecVal la, .stdVecVal lo] := by
  have hb := bindMemArgs_vecReverseCopy la lo
  have hn : LayoutNoAlias [("a", 1, 1), ("out", 0, 0)] := by
    simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩


/-! ## Memory body -/

/-- One body iteration on memory, keep branch: `j` decrements
    (value + mem agree), the capacity guard holds (value + mem
    agree), the store lands in the record block (`a` framed),
    `w` advances. -/
theorem memReverseCopyBody_keep (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lo : List (BitVec 32))
    (w j : Nat) (wB jB : BitVec 64) (y wOld : BitVec 32)
    (aa ao : Nat) (ta to : Nat) (na no : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_o : layoutLookup π "out" = some (ao, to))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_o : memFind m ao = some ⟨to, true, no :: lo⟩)
    (hna : na = BitVec.ofNat 32 la.length)
    (hno : no = BitVec.ofNat 32 lo.length)
    (haa : aa ≠ ao)
    (hwN : wB.toNat = w) (hjN : jB.toNat = j)
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hj1 : 1 ≤ j)
    (hy : la[j - 1]? = some y)
    (hwget : lo[w]? = some wOld)
    (hwlt : w < lo.length) :
    ∃ ρ' m', memEvalProgStmt prog F vecReverseCopyBody ρ m π =
      .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "out" = some (.stdVecVal (lo.set w y)) ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w + 1) ∧
      (∃ jB', envLookup ρ' "j" = some (.u64 jB') ∧ jB'.toNat = j - 1) ∧
      memFind m' ao = some ⟨to, true, no :: (lo.set w y)⟩ ∧
      memFind m' aa = some ⟨ta, true, na :: la⟩ := by
  have hwVar : evalExpr (.var "w") ρ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw
  have hjVar : evalExpr (.var "j") ρ = .ok (.u64 jB) :=
    evalExpr_var_hit _ _ _ hj
  have hwVarM : memEvalExpr (.var "w") ρ m π = .ok (.u64 wB) :=
    (memEvalExpr_var _ _ _ _).trans hwVar
  have hjVarM : memEvalExpr (.var "j") ρ m π = .ok (.u64 jB) :=
    (memEvalExpr_var _ _ _ _).trans hjVar
  -- `--j` (unconditional, value + mem agree).
  have hexpr_j : evalExpr (.usub (.var "j")
      (.lit (.u64 (1 : BitVec 64)))) ρ =
      .ok (.u64 (jB - 1)) :=
    evalExpr_u64_usub jB 1 (.var "j") ρ hjVar
  have hevJM : memEvalExpr (.usub (.var "j")
      (.lit (.u64 (1 : BitVec 64)))) ρ m π =
      .ok (.u64 (jB - 1)) :=
    (memEvalExpr_usub_agree (.var "j") (.lit (.u64 (1 : BitVec 64)))
      ρ m π (memEvalExpr_var _ _ _ _)
      (memEvalExpr_lit _ _ _ _)).trans hexpr_j
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "j"
    (.u64 jB) (.u64 (jB - 1)) hj
  have hstep_j := memRevAssign prog F "j"
    (.usub (.var "j") (.lit (.u64 (1 : BitVec 64)))) ρ m π
    (.u64 (jB - 1)) ρ₁ hevJM hexpr_j hu₁
  have hj₁ : envLookup ρ₁ "j" = some (.u64 (jB - 1)) :=
    envLookup_update_hit _ _ _ _ hu₁
  have ha₁ : envLookup ρ₁ "a" = some (.stdVecVal la) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "j" by decide) hu₁]
    exact ha
  have hout₁ : envLookup ρ₁ "out" = some (.stdVecVal lo) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "j" by decide) hu₁]
    exact hout
  have hw₁ : envLookup ρ₁ "w" = some (.u64 wB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "j" by decide) hu₁]
    exact hw
  have hjN' : (jB - 1).toNat = j - 1 := by
    rw [revU64_pred_toNat jB (by omega : 1 ≤ jB.toNat), hjN]
  have hjVar₁ : evalExpr (.var "j") ρ₁ = .ok (.u64 (jB - 1)) :=
    evalExpr_var_hit _ _ _ hj₁
  have hwVar₁ : evalExpr (.var "w") ρ₁ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw₁
  have hjVarM₁ : memEvalExpr (.var "j") ρ₁ m π =
      .ok (.u64 (jB - 1)) :=
    (memEvalExpr_var _ _ _ _).trans hjVar₁
  have hwVarM₁ : memEvalExpr (.var "w") ρ₁ m π =
      .ok (.u64 wB) :=
    (memEvalExpr_var _ _ _ _).trans hwVar₁
  have hget : la[(jB - 1).toNat]? = some y := by
    rw [hjN']; exact hy
  have hmemR : memLoad m aa ta ((jB - 1).toNat + 1) = .ok y :=
    memLoad_cellsAt m aa ta ((jB - 1).toNat + 1) (na :: la) y
      hmem_a (by rw [List.getElem?_cons_succ]; exact hget)
  have hat : evalExpr (.stdVecAt "a" (.var "j")) ρ₁ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha₁ hjVar₁ hget
  have hatM_ag : memEvalExpr (.stdVecAt "a" (.var "j")) ρ₁ m π =
      evalExpr (.stdVecAt "a" (.var "j")) ρ₁ :=
    memEvalExpr_stdVecAt_hit "a" (.var "j") ρ₁ m π la (jB - 1) y aa ta
      hlay_a ha₁ (memEvalExpr_var _ _ _ _) hjVar₁ hmemR hget
  have hatM : memEvalExpr (.stdVecAt "a" (.var "j")) ρ₁ m π =
      .ok (.i32 y) := by rw [hatM_ag]; exact hat
  have hmemLenO : memLoad m ao to 0 =
      .ok (BitVec.ofNat 32 lo.length) := by
    rw [← hno]
    exact memLoad_cellsAt m ao to 0 (no :: lo) no hmem_o (by simp)
  have hlenM : memEvalExpr (.stdVecLen "out") ρ₁ m π =
      evalExpr (.stdVecLen "out") ρ₁ :=
    memEvalExpr_stdVecLen_hit "out" ρ₁ m π lo ao to
      hlay_o hout₁ hmemLenO
  have hlenN : (BitVec.ofNat 64 lo.length).toNat = lo.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlo64
  have hguardV : evalExpr (.ult (.var "w") (.stdVecLen "out")) ρ₁ =
      .ok (.b true) := by
    have hult := evalExpr_ult_u64 (.var "w") (.stdVecLen "out") ρ₁ wB
      (BitVec.ofNat 64 lo.length) hwVar₁
      (evalExpr_stdVecLen_some _ _ _ hout₁)
    have htb : (wB.ult (BitVec.ofNat 64 lo.length)) = true := by
      rw [BitVec.ult_eq_decide, hwN, hlenN]
      exact decide_eq_true (by omega)
    rwa [htb] at hult
  have hguardM : memEvalExpr (.ult (.var "w") (.stdVecLen "out"))
      ρ₁ m π = .ok (.b true) := by
    have hag := memEvalExpr_ult_agree (.var "w") (.stdVecLen "out")
      ρ₁ m π (memEvalExpr_var _ _ _ _) hlenM
    rw [hag]; exact hguardV
  have hlt₁ : wB.toNat + 1 < (no :: lo).length := by
    simp only [List.length_cons]
    omega
  obtain ⟨m₁, hmstore, hmem₁⟩ :=
    memStore_cellsAt_pin m ao to y hmem_o hlt₁
  have hsetB : lo.set wB.toNat y = lo.set w y := by rw [hwN]
  rw [hsetB] at hmem₁
  obtain ⟨ρ₂, hu₂⟩ := envUpdate_some_of_lookup ρ₁ "out"
    (.stdVecVal lo) (.stdVecVal (lo.set wB.toNat y)) hout₁
  have hgetW : lo[wB.toNat]? = some wOld := by rw [hwN]; exact hwget
  have hstep_set := memRevVecSet prog F "out" (.var "w")
    (.stdVecAt "a" (.var "j")) ρ₁ m π wB y ao to lo wOld m₁ ρ₂
    hwVarM₁ hatM hout₁ hlay_o hgetW hmstore hu₂
  have hmem_a₁ : memFind m₁ aa = some ⟨ta, true, na :: la⟩ := by
    have h := memFind_memStore_other m m₁ ao aa to (wB.toNat + 1) y
      hmstore haa
    rw [h]; exact hmem_a
  have hj₂ : envLookup ρ₂ "j" = some (.u64 (jB - 1)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("j" : String) ≠ "out" by decide) hu₂]
    exact hj₁
  have ha₂ : envLookup ρ₂ "a" = some (.stdVecVal la) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "out" by decide) hu₂]
    exact ha₁
  have hevW : evalExpr (.uadd (.var "w")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ =
      .ok (.u64 (wB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _
        (by rw [envLookup_update_miss _ _ _ _ _
          (show ("w" : String) ≠ "out" by decide) hu₂]; exact hw₁))
      (by simp [evalExpr, litVal])
  have hevWM : memEvalExpr
      (.uadd (.var "w") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ m₁ π =
      .ok (.u64 (wB + 1)) :=
    (memEvalExpr_uadd_agree (.var "w") (.lit (.u64 (BitVec.ofNat 64 1)))
      ρ₂ m₁ π (memEvalExpr_var _ _ _ _)
      (memEvalExpr_lit _ _ _ _)).trans hevW
  obtain ⟨ρ₃, hu₃⟩ := envUpdate_some_of_lookup ρ₂ "w"
    (.u64 wB) (.u64 (wB + 1))
    (by rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "out" by decide) hu₂]; exact hw₁)
  have hstep_w := memRevAssign prog F "w"
    (.uadd (.var "w") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ m₁ π
    (.u64 (wB + 1)) ρ₃ hevWM hevW hu₃
  have hout₃ : envLookup ρ₃ "out" =
      some (.stdVecVal (lo.set w y)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "w" by decide) hu₃]
    have h := envLookup_update_hit _ _ _ _ hu₂
    rwa [hsetB] at h
  have ha₃ : envLookup ρ₃ "a" = some (.stdVecVal la) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "w" by decide) hu₃]
    exact ha₂
  have hj₃ : envLookup ρ₃ "j" = some (.u64 (jB - 1)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("j" : String) ≠ "w" by decide) hu₃]
    exact hj₂
  have hwN' : (wB + 1).toNat = w + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hwN]
    exact Nat.mod_eq_of_lt (by omega)
  have hw' : envLookup ρ₃ "w" = some (.u64 (wB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₃
  have hinner : memEvalProgStmt prog F
      (.if_ (.ult (.var "w") (.stdVecLen "out"))
        (.seq (.vecSet "out" (.var "w")
                (.stdVecAt "a" (.var "j")))
          (.assign "w" (.uadd (.var "w")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        .fail) ρ₁ m π = .ok ((ρ₃, m₁, π), .fellThrough) := by
    have hthen : memEvalProgStmt prog F
        (.seq (.vecSet "out" (.var "w")
                (.stdVecAt "a" (.var "j")))
          (.assign "w" (.uadd (.var "w")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        ρ₁ m π = .ok ((ρ₃, m₁, π), .fellThrough) := by
      rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
        hstep_set, hstep_w]
    exact (memEvalProgStmt_if_true prog F _ _ _ _ _ _
      hguardM).trans hthen
  have hbody : vecReverseCopyBody =
      (.seq (.assign "j" (.usub (.var "j")
             (.lit (.u64 (1 : BitVec 64)))))
        (.if_ (.ult (.var "w") (.stdVecLen "out"))
          (.seq (.vecSet "out" (.var "w")
                  (.stdVecAt "a" (.var "j")))
            (.assign "w" (.uadd (.var "w")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)) := rfl
  have heval : memEvalProgStmt prog F vecReverseCopyBody ρ m π =
      .ok ((ρ₃, m₁, π), .fellThrough) := by
    rw [hbody,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep_j]
    exact hinner
  have hmem_a₃ : memFind m₁ aa = some ⟨ta, true, na :: la⟩ :=
    hmem_a₁
  exact ⟨ρ₃, m₁, heval, ha₃, hout₃, ⟨_, hw', hwN'⟩,
    ⟨_, hj₃, by rw [hjN']⟩, hmem₁, hmem_a₃⟩

/-- One body iteration on memory, short-record branch: `j`
    decrements (value + mem agree), the capacity guard fails,
    loud `AssertFail` (no block is ever read — the failure
    precedes both the source load and the store). -/
theorem memReverseCopyBody_short (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (lo : List (BitVec 32))
    (w : Nat) (wB jB : BitVec 64)
    (ao : Nat) (to : Nat) (no : BitVec 32)
    (hlay_o : layoutLookup π "out" = some (ao, to))
    (hmem_o : memFind m ao = some ⟨to, true, no :: lo⟩)
    (hno : no = BitVec.ofNat 32 lo.length)
    (hlo64 : lo.length < 2 ^ 64)
    (hwN : wB.toNat = w)
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hmiss : lo[w]? = none) :
    memEvalProgStmt prog F vecReverseCopyBody ρ m π =
      .error .AssertFail := by
  have hjVar : evalExpr (.var "j") ρ = .ok (.u64 jB) :=
    evalExpr_var_hit _ _ _ hj
  have hexpr_j : evalExpr (.usub (.var "j")
      (.lit (.u64 (1 : BitVec 64)))) ρ =
      .ok (.u64 (jB - 1)) :=
    evalExpr_u64_usub jB 1 (.var "j") ρ hjVar
  have hevJM : memEvalExpr (.usub (.var "j")
      (.lit (.u64 (1 : BitVec 64)))) ρ m π =
      .ok (.u64 (jB - 1)) :=
    (memEvalExpr_usub_agree (.var "j") (.lit (.u64 (1 : BitVec 64)))
      ρ m π (memEvalExpr_var _ _ _ _)
      (memEvalExpr_lit _ _ _ _)).trans hexpr_j
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "j"
    (.u64 jB) (.u64 (jB - 1)) hj
  have hstep_j := memRevAssign prog F "j"
    (.usub (.var "j") (.lit (.u64 (1 : BitVec 64)))) ρ m π
    (.u64 (jB - 1)) ρ₁ hevJM hexpr_j hu₁
  have hw₁ : envLookup ρ₁ "w" = some (.u64 wB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "j" by decide) hu₁]
    exact hw
  have hout₁ : envLookup ρ₁ "out" = some (.stdVecVal lo) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "j" by decide) hu₁]
    exact hout
  have hnl : ¬ w < lo.length := by
    intro h
    have hsome : lo[w]? = some lo[w] := List.getElem?_eq_getElem h
    rw [hsome] at hmiss
    simp at hmiss
  have hlenN : (BitVec.ofNat 64 lo.length).toNat = lo.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlo64
  have hwVar₁ : evalExpr (.var "w") ρ₁ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw₁
  have hguardV : evalExpr (.ult (.var "w") (.stdVecLen "out")) ρ₁ =
      .ok (.b false) := by
    have hult := evalExpr_ult_u64 (.var "w") (.stdVecLen "out") ρ₁ wB
      (BitVec.ofNat 64 lo.length) hwVar₁
      (evalExpr_stdVecLen_some _ _ _ hout₁)
    have hfb : (wB.ult (BitVec.ofNat 64 lo.length)) = false := by
      rw [BitVec.ult_eq_decide, hwN, hlenN]
      exact decide_eq_false (by omega)
    rwa [hfb] at hult
  have hmemLenO : memLoad m ao to 0 =
      .ok (BitVec.ofNat 32 lo.length) := by
    rw [← hno]
    exact memLoad_cellsAt m ao to 0 (no :: lo) no hmem_o (by simp)
  have hlenM : memEvalExpr (.stdVecLen "out") ρ₁ m π =
      evalExpr (.stdVecLen "out") ρ₁ :=
    memEvalExpr_stdVecLen_hit "out" ρ₁ m π lo ao to
      hlay_o hout₁ hmemLenO
  have hguardM : memEvalExpr (.ult (.var "w") (.stdVecLen "out"))
      ρ₁ m π = .ok (.b false) := by
    have hag := memEvalExpr_ult_agree (.var "w") (.stdVecLen "out")
      ρ₁ m π (memEvalExpr_var _ _ _ _) hlenM
    rw [hag]; exact hguardV
  have hfail : memEvalProgStmt prog F .fail ρ₁ m π =
      .error .AssertFail := by
    simpa [memEvalProgStmt] using (memEvalStmtFuel_fail F ρ₁ m π)
  have hinner : memEvalProgStmt prog F
      (.if_ (.ult (.var "w") (.stdVecLen "out"))
        (.seq (.vecSet "out" (.var "w")
                (.stdVecAt "a" (.var "j")))
          (.assign "w" (.uadd (.var "w")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        .fail) ρ₁ m π = .error .AssertFail :=
    (memEvalProgStmt_if_false prog F _ _ _ _ _ _ hguardM).trans hfail
  have hbody : vecReverseCopyBody =
      (.seq (.assign "j" (.usub (.var "j")
             (.lit (.u64 (1 : BitVec 64)))))
        (.if_ (.ult (.var "w") (.stdVecLen "out"))
          (.seq (.vecSet "out" (.var "w")
                  (.stdVecAt "a" (.var "j")))
            (.assign "w" (.uadd (.var "w")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)) := rfl
  rw [hbody,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep_j]
  exact hinner

/-! ## Memory loop -/

/-- Loop bridge on memory, ok leg. -/
theorem memReverseCopyLoop_ok (prog : Prog) (F G : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la : List (BitVec 32)) (lo : List (BitVec 32))
    (w j : Nat) (wB jB : BitVec 64)
    (lo' : List (BitVec 32)) (w' j' : Nat)
    (aa ao : Nat) (ta to : Nat) (na no : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_o : layoutLookup π "out" = some (ao, to))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_o : memFind m ao = some ⟨to, true, no :: lo⟩)
    (hna : na = BitVec.ofNat 32 la.length)
    (hno : no = BitVec.ofNat 32 lo.length)
    (haa : aa ≠ ao)
    (hwN : wB.toNat = w) (hjN : jB.toNat = j)
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hwj : w + j = la.length) (hle : j ≤ la.length)
    (hwlo : w ≤ lo.length)
    (hpre : lo.take w = (la.drop j).reverse)
    (hF : j ≤ F) (hG : j ≤ G)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hfwd : reverseCopyFwd la lo G w j = .ok (w', j', lo')) :
    ∃ ρ' m', memEvalProgStmt prog F vecReverseCopyLoop ρ m π =
      .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "out" = some (.stdVecVal lo') ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w') ∧
      (∃ jB', envLookup ρ' "j" = some (.u64 jB') ∧ jB'.toNat = j') ∧
      memFind m' ao = some ⟨to, true, no :: lo'⟩ ∧
      memFind m' aa = some ⟨ta, true, na :: la⟩ := by
  induction F generalizing G ρ m lo w j wB jB with
  | zero =>
    have hj0 : j = 0 := by omega
    have hguardF : memEvalExpr
        (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j"))
        ρ m π = .ok (.b false) := by
      have hult := evalExpr_ult_u64lit (BitVec.ofNat 64 0)
        jB (.var "j") ρ (evalExpr_var_hit _ _ _ hj)
      have hfb : ((BitVec.ofNat 64 0).ult jB) = false := by
        rw [BitVec.ult_eq_decide]
        exact decide_eq_false (by omega)
      have hultF : evalExpr
          (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j")) ρ =
          .ok (.b false) := by
        rwa [hfb] at hult
      have hag := memEvalExpr_ult_agree
        (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j") ρ m π
        (memEvalExpr_lit _ _ _ _) (memEvalExpr_var _ _ _ _)
      rw [hag]; exact hultF
    have hexit : memEvalProgStmt prog 0 vecReverseCopyLoop ρ m π =
        .ok ((ρ, m, π), .fellThrough) :=
      memEvalProgStmt_while_false prog 0 _ _ _ _ _ hguardF
    have hpair : (w, j, lo) = (w', j', lo') := by
      cases G with
      | zero => simpa [reverseCopyFwd] using hfwd
      | succ G =>
        have hneg : ¬ 0 < j := by omega
        simpa [reverseCopyFwd, dite_eq_right hneg] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    exact ⟨ρ, m, hexit, ha, hout, ⟨wB, hw, hwN⟩, ⟨jB, hj, hjN⟩,
      hmem_o, hmem_a⟩
  | succ F ih =>
    by_cases hj0 : 0 < j
    · have hguardT : memEvalExpr
          (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j"))
          ρ m π = .ok (.b true) := by
        have hult := evalExpr_ult_u64lit (BitVec.ofNat 64 0)
          jB (.var "j") ρ (evalExpr_var_hit _ _ _ hj)
        have h0N : (BitVec.ofNat 64 0).toNat = 0 := by decide
        have htb : ((BitVec.ofNat 64 0).ult jB) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true (by omega)
        have hultT : evalExpr
            (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j")) ρ =
            .ok (.b true) := by
          rwa [htb] at hult
        have hag := memEvalExpr_ult_agree
          (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j") ρ m π
          (memEvalExpr_lit _ _ _ _) (memEvalExpr_var _ _ _ _)
        rw [hag]; exact hultT
      obtain ⟨y, hy⟩ := hread (j - 1) (by omega)
      cir_fuel_step (F, G, j - 1)
      by_cases hmiss : lo[w]? = none
      · have hcon := hfwd
        simp only [reverseCopyFwd, dite_eq_left hj0, hy,
          hmiss] at hcon
        exact absurd hcon (by simp)
      · have hsome : ∃ z, lo[w]? = some z := by
          match h : lo[w]? with
          | none => exact absurd h hmiss
          | some z => exact ⟨z, rfl⟩
        obtain ⟨wOld, hwget⟩ := hsome
        have hwlt : w < lo.length :=
          transformRead_lt lo w wOld hwget
        have htake_set : (lo.set w y).take (w + 1)
            = (lo.take w) ++ [y] :=
          take_set_succ_self lo w y hwlt
        have hpre' : (lo.set w y).take (w + 1)
            = ((la.drop (j - 1))).reverse := by
          rw [htake_set, hpre,
            drop_reverse_succ la j y (by omega) hy]
        have hlo64' : (lo.set w y).length < 2 ^ 64 := by
          rw [List.length_set]; exact hlo64
        have hlenS : (lo.set w y).length = lo.length := by
          simp [List.length_set]
        have hwlo' : w + 1 ≤ (lo.set w y).length := by omega
        have hwj' : (w + 1) + (j - 1) = la.length := by omega
        have hF'' : j - 1 ≤ F := by omega
        have hG'' : j - 1 ≤ G' := by omega
        have hfwd' : reverseCopyFwd la (lo.set w y) G' (w + 1)
            (j - 1) = .ok (w', j', lo') := by
          have h := hfwd
          simp only [reverseCopyFwd, dite_eq_left hj0, hy,
            hwget] at h
          exact h
        obtain ⟨ρ₁, m₁, hbody, ha₁, hout₁, ⟨wB₁, hwB₁, hwN₁⟩,
            ⟨jB₁, hjB₁, hjN₁⟩, hmem₁, hmem_a₁⟩ :=
          memReverseCopyBody_keep prog F ρ m π la lo w j
            wB jB y wOld aa ao ta to na no hlay_a hlay_o hmem_a
            hmem_o hna hno haa hwN hjN hla64 hlo64 ha hout hw
            hj (by omega) hy hwget hwlt
        obtain ⟨ρ', m', hloop, ha', hout', ⟨wB', hwB', hwN'⟩,
            ⟨jB', hjB', hjN'⟩, hmem', hmem_a'⟩ :=
          ih (G := G') (ρ := ρ₁) (m := m₁) (lo := lo.set w y)
            (w := w + 1) (j := j - 1) (wB := wB₁) (jB := jB₁)
            (hwN := hwN₁) (hjN := hjN₁)
            (hlo64 := hlo64')
            (ha := ha₁) (hout := hout₁)
            (hw := hwB₁) (hj := hjB₁)
            (hwj := hwj') (hle := by omega)
            (hwlo := hwlo') (hpre := hpre')
            (hF := hF'') (hG := hG'')
            (hfwd := hfwd')
            (hmem_a := hmem_a₁) (hmem_o := hmem₁)
            (hno := by rw [hlenS]; exact hno)
        refine ⟨ρ', m', ?_, ha', hout', ⟨wB', hwB', hwN'⟩,
          ⟨jB', hjB', hjN'⟩, hmem', hmem_a'⟩
        have hwhile : memEvalProgStmt prog (F + 1)
            vecReverseCopyLoop ρ m π =
            memEvalProgStmt prog F vecReverseCopyLoop ρ₁ m₁ π := by
          cir_unfold_prog (vecReverseCopyLoop, prog, F, hguardT, hbody)
        rw [hwhile]
        exact hloop
    · have hj0' : j = 0 := by omega
      subst hj0'
      have hguardF : memEvalExpr
          (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j"))
          ρ m π = .ok (.b false) := by
        have hult := evalExpr_ult_u64lit (BitVec.ofNat 64 0)
          jB (.var "j") ρ (evalExpr_var_hit _ _ _ hj)
        have hfb : ((BitVec.ofNat 64 0).ult jB) = false := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_false (by omega)
        have hultF : evalExpr
            (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j")) ρ =
            .ok (.b false) := by
          rwa [hfb] at hult
        have hag := memEvalExpr_ult_agree
          (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j") ρ m π
          (memEvalExpr_lit _ _ _ _) (memEvalExpr_var _ _ _ _)
        rw [hag]; exact hultF
      have hexit : memEvalProgStmt prog (F + 1) vecReverseCopyLoop
          ρ m π = .ok ((ρ, m, π), .fellThrough) :=
        memEvalProgStmt_while_false prog (F + 1) _ _ _ _ _ hguardF
      have hpair : (w, 0, lo) = (w', j', lo') := by
        cases G with
        | zero => simpa [reverseCopyFwd] using hfwd
        | succ G =>
          have hneg : ¬ 0 < (0 : Nat) := by omega
          simpa [reverseCopyFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      exact ⟨ρ, m, hexit, ha, hout, ⟨wB, hw, hwN⟩, ⟨jB, hj, hjN⟩,
        hmem_o, hmem_a⟩

/-- Loop bridge on memory, error leg. -/
theorem memReverseCopyLoop_err (prog : Prog) (F G : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la : List (BitVec 32)) (lo : List (BitVec 32))
    (w j : Nat) (wB jB : BitVec 64)
    (aa ao : Nat) (ta to : Nat) (na no : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_o : layoutLookup π "out" = some (ao, to))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_o : memFind m ao = some ⟨to, true, no :: lo⟩)
    (hna : na = BitVec.ofNat 32 la.length)
    (hno : no = BitVec.ofNat 32 lo.length)
    (haa : aa ≠ ao)
    (hwN : wB.toNat = w) (hjN : jB.toNat = j)
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hwj : w + j = la.length) (hle : j ≤ la.length)
    (hwlo : w ≤ lo.length)
    (hpre : lo.take w = (la.drop j).reverse)
    (hF : j ≤ F) (hG : j ≤ G)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hfwd : reverseCopyFwd la lo G w j = .error .AssertFail) :
    memEvalProgStmt prog F vecReverseCopyLoop ρ m π =
      .error .AssertFail := by
  induction F generalizing G ρ m lo w j wB jB with
  | zero =>
    have hj0 : j = 0 := by omega
    subst hj0
    cases G with
    | zero => exact absurd hfwd (by simp [reverseCopyFwd])
    | succ _ =>
      have hneg : ¬ 0 < (0 : Nat) := by omega
      have hcon := hfwd
      simp only [reverseCopyFwd, dite_eq_right hneg] at hcon
      exact absurd hcon (by simp)
  | succ F ih =>
    by_cases hj0 : 0 < j
    · have hguardT : memEvalExpr
          (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j"))
          ρ m π = .ok (.b true) := by
        have hult := evalExpr_ult_u64lit (BitVec.ofNat 64 0)
          jB (.var "j") ρ (evalExpr_var_hit _ _ _ hj)
        have h0N : (BitVec.ofNat 64 0).toNat = 0 := by decide
        have htb : ((BitVec.ofNat 64 0).ult jB) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true (by omega)
        have hultT : evalExpr
            (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j")) ρ =
            .ok (.b true) := by
          rwa [htb] at hult
        have hag := memEvalExpr_ult_agree
          (.lit (.u64 (BitVec.ofNat 64 0))) (.var "j") ρ m π
          (memEvalExpr_lit _ _ _ _) (memEvalExpr_var _ _ _ _)
        rw [hag]; exact hultT
      obtain ⟨y, hy⟩ := hread (j - 1) (by omega)
      cir_fuel_step (F, G, j - 1)
      by_cases hmiss : lo[w]? = none
      · have hshort := memReverseCopyBody_short prog F ρ m π lo
          w wB jB ao to no hlay_o hmem_o hno hlo64 hwN hout
          hw hj hmiss
        have hwhile : memEvalProgStmt prog (F + 1)
            vecReverseCopyLoop ρ m π = .error .AssertFail := by
          have hloop : vecReverseCopyLoop =
              (.while_ (.ult (.lit (.u64 (BitVec.ofNat 64 0)))
                (.var "j"))
                vecReverseCopyBody) := rfl
          rw [hloop, memEvalProgStmt_while_true prog F _ _ _ _ _
            hguardT, hshort]
        exact hwhile
      · have hsome : ∃ z, lo[w]? = some z := by
          match h : lo[w]? with
          | none => exact absurd h hmiss
          | some z => exact ⟨z, rfl⟩
        obtain ⟨wOld, hwget⟩ := hsome
        have hwlt : w < lo.length :=
          transformRead_lt lo w wOld hwget
        have htake_set : (lo.set w y).take (w + 1)
            = (lo.take w) ++ [y] :=
          take_set_succ_self lo w y hwlt
        have hpre' : (lo.set w y).take (w + 1)
            = ((la.drop (j - 1))).reverse := by
          rw [htake_set, hpre,
            drop_reverse_succ la j y (by omega) hy]
        have hlo64' : (lo.set w y).length < 2 ^ 64 := by
          rw [List.length_set]; exact hlo64
        have hlenS : (lo.set w y).length = lo.length := by
          simp [List.length_set]
        have hwlo' : w + 1 ≤ (lo.set w y).length := by omega
        have hwj' : (w + 1) + (j - 1) = la.length := by omega
        have hF'' : j - 1 ≤ F := by omega
        have hG'' : j - 1 ≤ G' := by omega
        have hfwd' : reverseCopyFwd la (lo.set w y) G' (w + 1)
            (j - 1) = .error .AssertFail := by
          have h := hfwd
          simp only [reverseCopyFwd, dite_eq_left hj0, hy,
            hwget] at h
          exact h
        obtain ⟨ρ₁, m₁, hbody, ha₁, hout₁, ⟨wB₁, hwB₁, hwN₁⟩,
            ⟨jB₁, hjB₁, hjN₁⟩, hmem₁, hmem_a₁⟩ :=
          memReverseCopyBody_keep prog F ρ m π la lo w j
            wB jB y wOld aa ao ta to na no hlay_a hlay_o hmem_a
            hmem_o hna hno haa hwN hjN hla64 hlo64 ha hout hw
            hj (by omega) hy hwget hwlt
        have hloop : memEvalProgStmt prog F vecReverseCopyLoop ρ₁ m₁
            π = .error .AssertFail :=
          ih (G := G') (ρ := ρ₁) (m := m₁) (lo := lo.set w y)
            (w := w + 1) (j := j - 1) (wB := wB₁) (jB := jB₁)
            (hwN := hwN₁) (hjN := hjN₁)
            (hlo64 := hlo64')
            (ha := ha₁) (hout := hout₁)
            (hw := hwB₁) (hj := hjB₁)
            (hwj := hwj') (hle := by omega)
            (hwlo := hwlo') (hpre := hpre')
            (hF := hF'') (hG := hG'')
            (hfwd := hfwd')
            (hmem_a := hmem_a₁) (hmem_o := hmem₁)
            (hno := by rw [hlenS]; exact hno)
        have hwhile : memEvalProgStmt prog (F + 1)
            vecReverseCopyLoop ρ m π = .error .AssertFail := by
          cir_unfold_prog (vecReverseCopyLoop, prog, F, hguardT, hbody)
          exact hloop
        exact hwhile
    · have hj0' : j = 0 := by omega
      subst hj0'
      cases G with
      | zero => exact absurd hfwd (by simp [reverseCopyFwd])
      | succ _ =>
        have hneg : ¬ 0 < (0 : Nat) := by omega
        have hcon := hfwd
        simp only [reverseCopyFwd, dite_eq_right hneg] at hcon
        exact absurd hcon (by simp)


/-! ## Value entries -/

/-- Value entry, nil leg: the empty input exits early with `0`. -/
theorem evalProgFunc_vecReverseCopy_nil (F : Nat)
    (lo : List (BitVec 32)) :
    evalProgFunc vecReverseCopyProg F vecReverseCopyFunc
      [.stdVecVal ([] : List (BitVec 32)),
        .stdVecVal lo] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
  have hbind : bindArgs vecReverseCopyFunc.args
      [.stdVecVal ([] : List (BitVec 32)),
        .stdVecVal lo] =
      some [("a", .stdVecVal ([] : List (BitVec 32))),
        ("out", .stdVecVal lo)] := rfl
  have hbody : vecReverseCopyFunc.body =
      (.seq (.if_ (.ueq (.stdVecLen "a")
                  (.lit (.u64 (BitVec.ofNat 64 0))))
            (.return_ (.lit (.u64 (BitVec.ofNat 64 0))))
            .skip)
        (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq (.let_ "j" (.u 64) (.stdVecLen "a"))
            (.seq vecReverseCopyLoop
              (.return_ (.var "w")))))) := rfl
  have hlenV : evalExpr (.stdVecLen "a")
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("out", .stdVecVal lo)] =
      .ok (.u64 (BitVec.ofNat 64 ([] : List (BitVec 32)).length)) :=
    evalExpr_stdVecLen_some _ _ _
      (by simp [envLookup])
  have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("out", .stdVecVal lo)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hguardT : evalExpr (.ueq (.stdVecLen "a")
      (.lit (.u64 (BitVec.ofNat 64 0))))
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("out", .stdVecVal lo)] =
      .ok (.b true) := by
    have hlenN :
        (BitVec.ofNat 64 ([] : List (BitVec 32)).length).toNat =
        ([] : List (BitVec 32)).length := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt (by simp)
    have h := evalExpr_ueq_u64_vars (.stdVecLen "a")
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("out", .stdVecVal lo)]
      (BitVec.ofNat 64 ([] : List (BitVec 32)).length)
      (BitVec.ofNat 64 0) hlenV hlitV
    simpa [hlenN] using h
  have hif := evalProgStmt_if_true vecReverseCopyProg F
    (.ueq (.stdVecLen "a") (.lit (.u64 (BitVec.ofNat 64 0))))
    (.return_ (.lit (.u64 (BitVec.ofNat 64 0)))) .skip
    [("a", .stdVecVal ([] : List (BitVec 32))),
      ("out", .stdVecVal lo)] hguardT
  have hret := evalProgStmt_return vecReverseCopyProg F
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("a", .stdVecVal ([] : List (BitVec 32))),
      ("out", .stdVecVal lo)]
    (.u64 (BitVec.ofNat 64 0)) hlitV
  simp only [evalProgFunc, hbind, hbody]
  rw [evalProgStmt_seq_returned _ _ _ _ _ _ _ (hif.trans hret)]

/-- Value entry, ok leg: a nonempty input with a fitting record
    runs the `(0, size)` prelude, the loop, and returns the
    copied count. -/
theorem evalProgFunc_vecReverseCopy_ok (F : Nat)
    (la lo : List (BitVec 32))
    (w' : Nat) (lo' : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length ≤ F)
    (hle : 1 ≤ la.length)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hfwd : reverseCopyFwd la lo la.length 0 la.length =
      .ok (w', 0, lo'))
    (hwlen : w' = la.length) :
    evalProgFunc vecReverseCopyProg F vecReverseCopyFunc
      [.stdVecVal la, .stdVecVal lo] =
      .ok (.u64 (BitVec.ofNat 64 w')) := by
  have hbind : bindArgs vecReverseCopyFunc.args
      [.stdVecVal la, .stdVecVal lo] =
      some [("a", .stdVecVal la), ("out", .stdVecVal lo)] := rfl
  have hbody : vecReverseCopyFunc.body =
      (.seq (.if_ (.ueq (.stdVecLen "a")
                  (.lit (.u64 (BitVec.ofNat 64 0))))
            (.return_ (.lit (.u64 (BitVec.ofNat 64 0))))
            .skip)
        (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq (.let_ "j" (.u 64) (.stdVecLen "a"))
            (.seq vecReverseCopyLoop
              (.return_ (.var "w")))))) := rfl
  cases hla : la with
  | nil =>
    subst hla
    simp at hle
  | cons b0 xs =>
    subst hla
    have ha₂ : envLookup [("a", .stdVecVal (b0 :: xs)),
        ("out", .stdVecVal lo)] "a" =
        some (.stdVecVal (b0 :: xs)) := by simp [envLookup]
    have hout₂ : envLookup [("a", .stdVecVal (b0 :: xs)),
        ("out", .stdVecVal lo)] "out" =
        some (.stdVecVal lo) := by
      simp [envLookup, show ("out" : String) ≠ "a" by decide]
    have hlenV : evalExpr (.stdVecLen "a")
        [("a", .stdVecVal (b0 :: xs)), ("out", .stdVecVal lo)] =
        .ok (.u64 (BitVec.ofNat 64 (b0 :: xs).length)) :=
      evalExpr_stdVecLen_some _ _ _ ha₂
    have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (b0 :: xs)), ("out", .stdVecVal lo)] =
        .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
    have hlenN : (BitVec.ofNat 64 (b0 :: xs).length).toNat =
        (b0 :: xs).length := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
    have hnn : BitVec.ofNat 64 (b0 :: xs).length ≠
        BitVec.ofNat 64 0 := by
      intro hcon
      have h0 := congrArg BitVec.toNat hcon
      rw [hlenN] at h0
      simp at h0
    have hbeq : (BitVec.ofNat 64 (b0 :: xs).length ==
        BitVec.ofNat 64 0) = false :=
      beq_eq_false_iff_ne.mpr hnn
    have hguardF : evalExpr (.ueq (.stdVecLen "a")
        (.lit (.u64 (BitVec.ofNat 64 0))))
        [("a", .stdVecVal (b0 :: xs)), ("out", .stdVecVal lo)] =
        .ok (.b false) := by
      have h := evalExpr_ueq_u64_vars (.stdVecLen "a")
        (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (b0 :: xs)), ("out", .stdVecVal lo)]
        (BitVec.ofNat 64 (b0 :: xs).length)
        (BitVec.ofNat 64 0) hlenV hlitV
      rwa [hbeq] at h
    have hif := evalProgStmt_if_false vecReverseCopyProg F
      (.ueq (.stdVecLen "a") (.lit (.u64 (BitVec.ofNat 64 0))))
      (.return_ (.lit (.u64 (BitVec.ofNat 64 0)))) .skip
      [("a", .stdVecVal (b0 :: xs)), ("out", .stdVecVal lo)] hguardF
    have hskipV : evalProgStmt vecReverseCopyProg F .skip
        [("a", .stdVecVal (b0 :: xs)), ("out", .stdVecVal lo)] =
        .ok ([("a", .stdVecVal (b0 :: xs)), ("out", .stdVecVal lo)],
          .fellThrough) := by
      simpa [evalProgStmt] using
        (show evalStmtFuel F .skip [("a", .stdVecVal (b0 :: xs)),
            ("out", .stdVecVal lo)] =
          .ok ([("a", .stdVecVal (b0 :: xs)),
            ("out", .stdVecVal lo)],
            .fellThrough) by
        cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith])
    have hfall : evalProgStmt vecReverseCopyProg F
        (.if_ (.ueq (.stdVecLen "a")
                (.lit (.u64 (BitVec.ofNat 64 0))))
          (.return_ (.lit (.u64 (BitVec.ofNat 64 0)))) .skip)
        [("a", .stdVecVal (b0 :: xs)), ("out", .stdVecVal lo)] =
        .ok ([("a", .stdVecVal (b0 :: xs)), ("out", .stdVecVal lo)],
          .fellThrough) :=
      hif.trans hskipV
    -- Prelude: `w := 0`, `j := a.size()`.
    have hlitW : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (b0 :: xs)), ("out", .stdVecVal lo)] =
        .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
    have hletW := revLet vecReverseCopyProg F "w" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal (b0 :: xs)), ("out", .stdVecVal lo)]
      (.u64 (BitVec.ofNat 64 0)) hlitW
    have hlenJ : evalExpr (.stdVecLen "a")
        (envExtend [("a", .stdVecVal (b0 :: xs)), ("out", .stdVecVal lo)]
          "w" (.u64 (BitVec.ofNat 64 0))) =
        .ok (.u64 (BitVec.ofNat 64 (b0 :: xs).length)) := by
      have haJ : envLookup (envExtend
          [("a", .stdVecVal (b0 :: xs)), ("out", .stdVecVal lo)]
          "w" (.u64 (BitVec.ofNat 64 0))) "a" =
          some (.stdVecVal (b0 :: xs)) := by
        rw [envExtend_miss _ _ _ _
          (show ("a" : String) ≠ "w" by decide)]
        simp [envLookup]
      exact evalExpr_stdVecLen_some _ _ _ haJ
    have hletJ := revLet vecReverseCopyProg F "j" (.u 64)
      (.stdVecLen "a")
      (envExtend [("a", .stdVecVal (b0 :: xs)), ("out", .stdVecVal lo)]
        "w" (.u64 (BitVec.ofNat 64 0)))
      (.u64 (BitVec.ofNat 64 (b0 :: xs).length)) hlenJ
    have hw0N : (BitVec.ofNat 64 0).toNat = 0 := by decide
    have hjN : (BitVec.ofNat 64 (b0 :: xs).length).toNat =
        (b0 :: xs).length := hlenN
    have ha₁ : envLookup (envExtend (envExtend
        [("a", .stdVecVal (b0 :: xs)), ("out", .stdVecVal lo)]
        "w" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 (b0 :: xs).length))) "a" =
        some (.stdVecVal (b0 :: xs)) := by
      rw [envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "j" by decide),
        envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "w" by decide)]
      simp [envLookup]
    have hout₁ : envLookup (envExtend (envExtend
        [("a", .stdVecVal (b0 :: xs)), ("out", .stdVecVal lo)]
        "w" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 (b0 :: xs).length))) "out" =
        some (.stdVecVal lo) := by
      rw [envExtend_miss _ _ _ _
        (show ("out" : String) ≠ "j" by decide),
        envExtend_miss _ _ _ _
        (show ("out" : String) ≠ "w" by decide)]
      simp [envLookup, show ("out" : String) ≠ "a" by decide]
    have hw₁ : envLookup (envExtend (envExtend
        [("a", .stdVecVal (b0 :: xs)), ("out", .stdVecVal lo)]
        "w" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 (b0 :: xs).length))) "w" =
        some (.u64 (BitVec.ofNat 64 0)) := by
      rw [envExtend_miss _ _ _ _
        (show ("w" : String) ≠ "j" by decide)]
      exact envExtend_hit _ _ _
    have hj₁ : envLookup (envExtend (envExtend
        [("a", .stdVecVal (b0 :: xs)), ("out", .stdVecVal lo)]
        "w" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 (b0 :: xs).length))) "j" =
        some (.u64 (BitVec.ofNat 64 (b0 :: xs).length)) :=
      envExtend_hit _ _ _
    obtain ⟨ρ', hloop, ha', hout', ⟨wB', hwB', hwN'⟩,
        ⟨jB', hjB', hjN'⟩⟩ :=
      valReverseCopyLoop_ok vecReverseCopyProg F ((b0 :: xs).length)
        (envExtend (envExtend
          [("a", .stdVecVal (b0 :: xs)), ("out", .stdVecVal lo)]
          "w" (.u64 (BitVec.ofNat 64 0)))
          "j" (.u64 (BitVec.ofNat 64 (b0 :: xs).length)))
        (b0 :: xs) lo 0 ((b0 :: xs).length)
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 (b0 :: xs).length)
        lo' w' 0 hw0N hjN hla64 hlo64 ha₁ hout₁ hw₁ hj₁
        (by omega) (Nat.le_refl _) (Nat.zero_le _)
        (by simp) (by omega) (Nat.le_refl _)
        hread hfwd
    have hwEq : wB' = BitVec.ofNat 64 w' := by
      apply BitVec.eq_of_toNat_eq
      rw [hwN', hwlen, BitVec.toNat_ofNat]
      exact (Nat.mod_eq_of_lt hla64).symm
    have hevW' : evalExpr (.var "w") ρ' =
        .ok (.u64 (BitVec.ofNat 64 w')) := by
      rw [← hwEq]; exact evalExpr_var_hit _ _ _ hwB'
    have hret := evalProgStmt_return vecReverseCopyProg F
      (.var "w") ρ' (.u64 (BitVec.ofNat 64 w')) hevW'
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hfall,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletW,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletJ,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hloop,
      hret]

/-- Value entry, err leg: a nonempty input with a short record
    binds the prelude, then the loop fails loud (the `return`
    is unreachable). -/
theorem evalProgFunc_vecReverseCopy_err (F : Nat)
    (la lo : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length ≤ F)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hmore : lo.length < la.length)
    (hfwd : reverseCopyFwd la lo la.length 0 la.length =
      .error .AssertFail) :
    evalProgFunc vecReverseCopyProg F vecReverseCopyFunc
      [.stdVecVal la, .stdVecVal lo] =
      .error .AssertFail := by
  have hbind : bindArgs vecReverseCopyFunc.args
      [.stdVecVal la, .stdVecVal lo] =
      some [("a", .stdVecVal la), ("out", .stdVecVal lo)] := rfl
  have hbody : vecReverseCopyFunc.body =
      (.seq (.if_ (.ueq (.stdVecLen "a")
                  (.lit (.u64 (BitVec.ofNat 64 0))))
            (.return_ (.lit (.u64 (BitVec.ofNat 64 0))))
            .skip)
        (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq (.let_ "j" (.u 64) (.stdVecLen "a"))
            (.seq vecReverseCopyLoop
              (.return_ (.var "w")))))) := rfl
  have hle : 1 ≤ la.length := by omega
  cases hla : la with
  | nil =>
    subst hla
    simp at hmore
  | cons b0 ys =>
    subst hla
    have ha₂ : envLookup [("a", .stdVecVal (b0 :: ys)),
        ("out", .stdVecVal lo)] "a" =
        some (.stdVecVal (b0 :: ys)) := by simp [envLookup]
    have hout₂ : envLookup [("a", .stdVecVal (b0 :: ys)),
        ("out", .stdVecVal lo)] "out" =
        some (.stdVecVal lo) := by
      simp [envLookup, show ("out" : String) ≠ "a" by decide]
    have hlenV : evalExpr (.stdVecLen "a")
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)] =
        .ok (.u64 (BitVec.ofNat 64 (b0 :: ys).length)) :=
      evalExpr_stdVecLen_some _ _ _ ha₂
    have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)] =
        .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
    have hlenN : (BitVec.ofNat 64 (b0 :: ys).length).toNat =
        (b0 :: ys).length := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
    have hnn : BitVec.ofNat 64 (b0 :: ys).length ≠
        BitVec.ofNat 64 0 := by
      intro hcon
      have h0 := congrArg BitVec.toNat hcon
      rw [hlenN] at h0
      simp at h0
    have hbeq : (BitVec.ofNat 64 (b0 :: ys).length ==
        BitVec.ofNat 64 0) = false :=
      beq_eq_false_iff_ne.mpr hnn
    have hguardF : evalExpr (.ueq (.stdVecLen "a")
        (.lit (.u64 (BitVec.ofNat 64 0))))
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)] =
        .ok (.b false) := by
      have h := evalExpr_ueq_u64_vars (.stdVecLen "a")
        (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        (BitVec.ofNat 64 (b0 :: ys).length)
        (BitVec.ofNat 64 0) hlenV hlitV
      rwa [hbeq] at h
    have hif := evalProgStmt_if_false vecReverseCopyProg F
      (.ueq (.stdVecLen "a") (.lit (.u64 (BitVec.ofNat 64 0))))
      (.return_ (.lit (.u64 (BitVec.ofNat 64 0)))) .skip
      [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)] hguardF
    have hskipV : evalProgStmt vecReverseCopyProg F .skip
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)] =
        .ok ([("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)],
          .fellThrough) := by
      simpa [evalProgStmt] using
        (show evalStmtFuel F .skip [("a", .stdVecVal (b0 :: ys)),
            ("out", .stdVecVal lo)] =
          .ok ([("a", .stdVecVal (b0 :: ys)),
            ("out", .stdVecVal lo)],
            .fellThrough) by
        cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith])
    have hfall : evalProgStmt vecReverseCopyProg F
        (.if_ (.ueq (.stdVecLen "a")
                (.lit (.u64 (BitVec.ofNat 64 0))))
          (.return_ (.lit (.u64 (BitVec.ofNat 64 0)))) .skip)
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)] =
        .ok ([("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)],
          .fellThrough) :=
      hif.trans hskipV
    have hlitW : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)] =
        .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
    have hletW := revLet vecReverseCopyProg F "w" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
      (.u64 (BitVec.ofNat 64 0)) hlitW
    have hlenJ : evalExpr (.stdVecLen "a")
        (envExtend [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
          "w" (.u64 (BitVec.ofNat 64 0))) =
        .ok (.u64 (BitVec.ofNat 64 (b0 :: ys).length)) := by
      have haJ : envLookup (envExtend
          [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
          "w" (.u64 (BitVec.ofNat 64 0))) "a" =
          some (.stdVecVal (b0 :: ys)) := by
        rw [envExtend_miss _ _ _ _
          (show ("a" : String) ≠ "w" by decide)]
        simp [envLookup]
      exact evalExpr_stdVecLen_some _ _ _ haJ
    have hletJ := revLet vecReverseCopyProg F "j" (.u 64)
      (.stdVecLen "a")
      (envExtend [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        "w" (.u64 (BitVec.ofNat 64 0)))
      (.u64 (BitVec.ofNat 64 (b0 :: ys).length)) hlenJ
    have hw0N : (BitVec.ofNat 64 0).toNat = 0 := by decide
    have hjN : (BitVec.ofNat 64 (b0 :: ys).length).toNat =
        (b0 :: ys).length := hlenN
    have ha₁ : envLookup (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        "w" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 (b0 :: ys).length))) "a" =
        some (.stdVecVal (b0 :: ys)) := by
      rw [envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "j" by decide),
        envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "w" by decide)]
      simp [envLookup]
    have hout₁ : envLookup (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        "w" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 (b0 :: ys).length))) "out" =
        some (.stdVecVal lo) := by
      rw [envExtend_miss _ _ _ _
        (show ("out" : String) ≠ "j" by decide),
        envExtend_miss _ _ _ _
        (show ("out" : String) ≠ "w" by decide)]
      simp [envLookup, show ("out" : String) ≠ "a" by decide]
    have hw₁ : envLookup (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        "w" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 (b0 :: ys).length))) "w" =
        some (.u64 (BitVec.ofNat 64 0)) := by
      rw [envExtend_miss _ _ _ _
        (show ("w" : String) ≠ "j" by decide)]
      exact envExtend_hit _ _ _
    have hj₁ : envLookup (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        "w" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 (b0 :: ys).length))) "j" =
        some (.u64 (BitVec.ofNat 64 (b0 :: ys).length)) :=
      envExtend_hit _ _ _
    have hloop : evalProgStmt vecReverseCopyProg F vecReverseCopyLoop
        (envExtend (envExtend
          [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
          "w" (.u64 (BitVec.ofNat 64 0)))
          "j" (.u64 (BitVec.ofNat 64 (b0 :: ys).length))) =
        .error .AssertFail :=
      valReverseCopyLoop_err vecReverseCopyProg F ((b0 :: ys).length)
        (envExtend (envExtend
          [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
          "w" (.u64 (BitVec.ofNat 64 0)))
          "j" (.u64 (BitVec.ofNat 64 (b0 :: ys).length)))
        (b0 :: ys) lo 0 ((b0 :: ys).length)
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 (b0 :: ys).length)
        hw0N hjN hla64 hlo64 ha₁ hout₁ hw₁ hj₁
        (by omega) (Nat.le_refl _)
        (Nat.zero_le _)
        (by simp) (by omega) (Nat.le_refl _)
        hread hfwd
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hfall,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletW,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletJ,
      evalProgStmt_seq_err _ _ _ _ _ _ hloop]

/-! ## Memory entries -/

/-- Memory nil: the empty input exits early with `0` on the
    memory layer (the entry guard agrees with the value
    guard through `memEvalExpr_ueq_agree`). -/
theorem memEvalProgFunc_vecReverseCopy_nil (F : Nat)
    (lo : List (BitVec 32)) :
    memEvalProgFunc vecReverseCopyProg F vecReverseCopyFunc
      [.stdVecVal ([] : List (BitVec 32)),
        .stdVecVal lo] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
  have hbind := bindMemArgs_vecReverseCopy
    ([] : List (BitVec 32)) lo
  have hbody : vecReverseCopyFunc.body =
      (.seq (.if_ (.ueq (.stdVecLen "a")
                  (.lit (.u64 (BitVec.ofNat 64 0))))
            (.return_ (.lit (.u64 (BitVec.ofNat 64 0))))
            .skip)
        (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq (.let_ "j" (.u 64) (.stdVecLen "a"))
            (.seq vecReverseCopyLoop
              (.return_ (.var "w")))))) := rfl
  have hlenV : evalExpr (.stdVecLen "a")
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("out", .stdVecVal lo)] =
      .ok (.u64 (BitVec.ofNat 64 ([] : List (BitVec 32)).length)) :=
    evalExpr_stdVecLen_some _ _ _
      (by simp [envLookup])
  have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("out", .stdVecVal lo)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hlenN :
      (BitVec.ofNat 64 ([] : List (BitVec 32)).length).toNat =
      ([] : List (BitVec 32)).length := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (by simp)
  have hguardV : evalExpr (.ueq (.stdVecLen "a")
      (.lit (.u64 (BitVec.ofNat 64 0))))
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("out", .stdVecVal lo)] =
      .ok (.b true) := by
    have h := evalExpr_ueq_u64_vars (.stdVecLen "a")
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("out", .stdVecVal lo)]
      (BitVec.ofNat 64 ([] : List (BitVec 32)).length)
      (BitVec.ofNat 64 0) hlenV hlitV
    simpa [hlenN] using h
  have hguardM : memEvalExpr (.ueq (.stdVecLen "a")
      (.lit (.u64 (BitVec.ofNat 64 0))))
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("out", .stdVecVal lo)]
      (⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
          ([] : List (BitVec 32))⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
      [("a", 1, 1), ("out", 0, 0)] = .ok (.b true) := by
    have hmemLen : memLoad
        (⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
            ([] : List (BitVec 32))⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
        1 1 0 =
        .ok (BitVec.ofNat 32 ([] : List (BitVec 32)).length) := by
      have hmem_a : memFind
          (⟨2, [(1, ⟨1, true,
            (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
              ([] : List (BitVec 32))⟩),
            (0, ⟨0, true,
            (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem) 1 =
          some ⟨1, true,
            (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
              ([] : List (BitVec 32))⟩ :=
        memFind_cons_hit _ _ _ _ _
      exact memLoad_cellsAt _ 1 1 0 _ _ hmem_a (by simp)
    have hag := memEvalExpr_ueq_agree (.stdVecLen "a")
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("out", .stdVecVal lo)]
      (⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
          ([] : List (BitVec 32))⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
      [("a", 1, 1), ("out", 0, 0)]
      (memEvalExpr_stdVecLen_hit "a" _ _ _ _ _ _
        (by simp [layoutLookup])
        (by simp [envLookup]) hmemLen)
      (memEvalExpr_lit _ _ _ _)
    rw [hag]; exact hguardV
  have hifM := memEvalProgStmt_if_true vecReverseCopyProg F
    (.ueq (.stdVecLen "a") (.lit (.u64 (BitVec.ofNat 64 0))))
    (.return_ (.lit (.u64 (BitVec.ofNat 64 0)))) .skip
    [("a", .stdVecVal ([] : List (BitVec 32))),
      ("out", .stdVecVal lo)]
    (⟨2, [(1, ⟨1, true,
      (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
        ([] : List (BitVec 32))⟩),
      (0, ⟨0, true,
      (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
    [("a", 1, 1), ("out", 0, 0)] hguardM
  have hlitM : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("out", .stdVecVal lo)]
      (⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
          ([] : List (BitVec 32))⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
      [("a", 1, 1), ("out", 0, 0)] =
      .ok (.u64 (BitVec.ofNat 64 0)) :=
    (memEvalExpr_lit _ _ _ _).trans
      (by simp [evalExpr, litVal])
  have hretM := memEvalProgStmt_return vecReverseCopyProg F
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("a", .stdVecVal ([] : List (BitVec 32))),
      ("out", .stdVecVal lo)]
    (⟨2, [(1, ⟨1, true,
      (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
        ([] : List (BitVec 32))⟩),
      (0, ⟨0, true,
      (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
    [("a", 1, 1), ("out", 0, 0)]
    (.u64 (BitVec.ofNat 64 0)) hlitM
  simp only [memEvalProgFunc, hbind, hbody]
  rw [memEvalProgStmt_seq_returned _ _ _ _ _ _ _ _ _ _ _
    (hifM.trans hretM)]

/-- Memory entry, ok leg: a nonempty input with a fitting
    record runs the prelude and loop on the memory layer and
    returns the copied count. -/
theorem memEvalProgFunc_vecReverseCopy_ok (F : Nat)
    (la lo : List (BitVec 32))
    (w' : Nat) (lo' : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length ≤ F)
    (hle : 1 ≤ la.length)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hfwd : reverseCopyFwd la lo la.length 0 la.length =
      .ok (w', 0, lo'))
    (hwlen : w' = la.length) :
    memEvalProgFunc vecReverseCopyProg F vecReverseCopyFunc
      [.stdVecVal la, .stdVecVal lo] =
      .ok (.u64 (BitVec.ofNat 64 w')) := by
  have hbind := bindMemArgs_vecReverseCopy la lo
  have hbody : vecReverseCopyFunc.body =
      (.seq (.if_ (.ueq (.stdVecLen "a")
                  (.lit (.u64 (BitVec.ofNat 64 0))))
            (.return_ (.lit (.u64 (BitVec.ofNat 64 0))))
            .skip)
        (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq (.let_ "j" (.u 64) (.stdVecLen "a"))
            (.seq vecReverseCopyLoop
              (.return_ (.var "w")))))) := rfl
  cases hla : la with
  | nil =>
    subst hla
    simp at hle
  | cons b0 ys =>
    subst hla
    have ha₂ : envLookup [("a", .stdVecVal (b0 :: ys)),
        ("out", .stdVecVal lo)] "a" =
        some (.stdVecVal (b0 :: ys)) := by simp [envLookup]
    have hout₂ : envLookup [("a", .stdVecVal (b0 :: ys)),
        ("out", .stdVecVal lo)] "out" =
        some (.stdVecVal lo) := by
      simp [envLookup, show ("out" : String) ≠ "a" by decide]
    have hlenV : evalExpr (.stdVecLen "a")
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)] =
        .ok (.u64 (BitVec.ofNat 64 (b0 :: ys).length)) :=
      evalExpr_stdVecLen_some _ _ _ ha₂
    have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)] =
        .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
    have hlenN : (BitVec.ofNat 64 (b0 :: ys).length).toNat =
        (b0 :: ys).length := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
    have hnn : BitVec.ofNat 64 (b0 :: ys).length ≠
        BitVec.ofNat 64 0 := by
      intro hcon
      have h0 := congrArg BitVec.toNat hcon
      rw [hlenN] at h0
      simp at h0
    have hbeq : (BitVec.ofNat 64 (b0 :: ys).length ==
        BitVec.ofNat 64 0) = false :=
      beq_eq_false_iff_ne.mpr hnn
    have hguardV : evalExpr (.ueq (.stdVecLen "a")
        (.lit (.u64 (BitVec.ofNat 64 0))))
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)] =
        .ok (.b false) := by
      have h := evalExpr_ueq_u64_vars (.stdVecLen "a")
        (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        (BitVec.ofNat 64 (b0 :: ys).length)
        (BitVec.ofNat 64 0) hlenV hlitV
      rwa [hbeq] at h
    have hguardM : memEvalExpr (.ueq (.stdVecLen "a")
        (.lit (.u64 (BitVec.ofNat 64 0))))
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        (⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
        [("a", 1, 1), ("out", 0, 0)] = .ok (.b false) := by
      have hmemLen : memLoad
          (⟨2, [(1, ⟨1, true,
            (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
            (0, ⟨0, true,
            (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
          1 1 0 =
          .ok (BitVec.ofNat 32 (b0 :: ys).length) := by
        have hmem_a : memFind
            (⟨2, [(1, ⟨1, true,
              (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
              (0, ⟨0, true,
              (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem) 1 =
            some ⟨1, true,
              (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩ :=
          memFind_cons_hit _ _ _ _ _
        exact memLoad_cellsAt _ 1 1 0 _ _ hmem_a (by simp)
      have hag := memEvalExpr_ueq_agree (.stdVecLen "a")
        (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        (⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
        [("a", 1, 1), ("out", 0, 0)]
        (memEvalExpr_stdVecLen_hit "a" _ _ _ _ _ _
          (by simp [layoutLookup])
          (by simp [envLookup]) hmemLen)
        (memEvalExpr_lit _ _ _ _)
      rw [hag]; exact hguardV
    have hifF := memEvalProgStmt_if_false vecReverseCopyProg F
      (.ueq (.stdVecLen "a") (.lit (.u64 (BitVec.ofNat 64 0))))
      (.return_ (.lit (.u64 (BitVec.ofNat 64 0)))) .skip
      [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
      (⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
      [("a", 1, 1), ("out", 0, 0)] hguardM
    have hskipM : memEvalProgStmt vecReverseCopyProg F .skip
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        (⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
        [("a", 1, 1), ("out", 0, 0)] =
        .ok (([("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)],
          (⟨2, [(1, ⟨1, true,
            (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
            (0, ⟨0, true,
            (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem),
          [("a", 1, 1), ("out", 0, 0)]), .fellThrough) := by
      cases F <;> simp [memEvalProgStmt, memEvalStmtFuel,
        memEvalStmtZero, memEvalStmtWith]
    have hfallM := hifF.trans hskipM
    -- Prelude lets on memory.
    have hlitM : memEvalExpr
        (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        (⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
        [("a", 1, 1), ("out", 0, 0)] =
        evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
          [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)] :=
      memEvalExpr_lit _ _ _ _
    have hlitW : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)] =
        .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
    have hletW := memRevLet vecReverseCopyProg F "w" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
      (⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
      [("a", 1, 1), ("out", 0, 0)] (.u64 (BitVec.ofNat 64 0))
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) (by intro h; cases h) hlitM hlitW
    have hlenJM : memEvalExpr (.stdVecLen "a")
        (envExtend [("a", .stdVecVal (b0 :: ys)),
          ("out", .stdVecVal lo)]
          "w" (.u64 (BitVec.ofNat 64 0)))
        (⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
        [("a", 1, 1), ("out", 0, 0)] =
        evalExpr (.stdVecLen "a")
          (envExtend [("a", .stdVecVal (b0 :: ys)),
            ("out", .stdVecVal lo)]
            "w" (.u64 (BitVec.ofNat 64 0))) := by
      have haJ : envLookup (envExtend
          [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
          "w" (.u64 (BitVec.ofNat 64 0))) "a" =
          some (.stdVecVal (b0 :: ys)) := by
        rw [envExtend_miss _ _ _ _
          (show ("a" : String) ≠ "w" by decide)]
        simp [envLookup]
      have hmemLen : memLoad
          (⟨2, [(1, ⟨1, true,
            (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
            (0, ⟨0, true,
            (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
          1 1 0 =
          .ok (BitVec.ofNat 32 (b0 :: ys).length) := by
        have hmem_a : memFind
            (⟨2, [(1, ⟨1, true,
              (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
              (0, ⟨0, true,
              (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem) 1 =
            some ⟨1, true,
              (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩ :=
          memFind_cons_hit _ _ _ _ _
        exact memLoad_cellsAt _ 1 1 0 _ _ hmem_a (by simp)
      exact memEvalExpr_stdVecLen_hit "a" _ _ _ _ _ _
        (by simp [layoutLookup]) haJ hmemLen
    have haJw : envLookup (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        "w" (.u64 (BitVec.ofNat 64 0))) "a" =
        some (.stdVecVal (b0 :: ys)) := by
      rw [envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "w" by decide)]
      simp [envLookup]
    have hlenJ : evalExpr (.stdVecLen "a")
        (envExtend [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
          "w" (.u64 (BitVec.ofNat 64 0))) =
        .ok (.u64 (BitVec.ofNat 64 (b0 :: ys).length)) :=
      evalExpr_stdVecLen_some _ _ _ haJw
    have hletJ := memRevLet vecReverseCopyProg F "j" (.u 64)
      (.stdVecLen "a")
      (envExtend [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        "w" (.u64 (BitVec.ofNat 64 0)))
      (⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
      [("a", 1, 1), ("out", 0, 0)]
      (.u64 (BitVec.ofNat 64 (b0 :: ys).length))
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) (by intro h; cases h) hlenJM hlenJ
    have hw0N : (BitVec.ofNat 64 0).toNat = 0 := by decide
    have ha₁ : envLookup (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        "w" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 (b0 :: ys).length))) "a" =
        some (.stdVecVal (b0 :: ys)) := by
      rw [envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "j" by decide),
        envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "w" by decide)]
      simp [envLookup]
    have hout₁ : envLookup (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        "w" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 (b0 :: ys).length))) "out" =
        some (.stdVecVal lo) := by
      rw [envExtend_miss _ _ _ _
        (show ("out" : String) ≠ "j" by decide),
        envExtend_miss _ _ _ _
        (show ("out" : String) ≠ "w" by decide)]
      simp [envLookup, show ("out" : String) ≠ "a" by decide]
    have hw₁ : envLookup (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        "w" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 (b0 :: ys).length))) "w" =
        some (.u64 (BitVec.ofNat 64 0)) := by
      rw [envExtend_miss _ _ _ _
        (show ("w" : String) ≠ "j" by decide)]
      exact envExtend_hit _ _ _
    have hj₁ : envLookup (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        "w" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 (b0 :: ys).length))) "j" =
        some (.u64 (BitVec.ofNat 64 (b0 :: ys).length)) :=
      envExtend_hit _ _ _
    obtain ⟨ρ', m', hloop, ha', hout', ⟨wB', hwB', hwN'⟩,
        ⟨jB', hjB', hjN'⟩, hmem', hmem_a'⟩ :=
      memReverseCopyLoop_ok vecReverseCopyProg F ((b0 :: ys).length)
        (envExtend (envExtend
          [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
          "w" (.u64 (BitVec.ofNat 64 0)))
          "j" (.u64 (BitVec.ofNat 64 (b0 :: ys).length)))
        (⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
        [("a", 1, 1), ("out", 0, 0)]
        (b0 :: ys) lo 0 ((b0 :: ys).length)
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 (b0 :: ys).length)
        lo' w' 0
        1 0 1 0
        (BitVec.ofNat 32 (b0 :: ys).length)
        (BitVec.ofNat 32 lo.length)
        (by simp [layoutLookup]) (by simp [layoutLookup])
        (memFind_cons_hit _ _ _ _ _)
        (by
          have hne01 : (0 : Nat) ≠ 1 := by decide
          rw [memFind_cons_miss _ _ _ _ _ _ hne01]
          exact memFind_cons_hit _ _ _ _ _)
        rfl rfl (by decide)
        hw0N hlenN hla64 hlo64 ha₁ hout₁ hw₁ hj₁
        (by omega) (Nat.le_refl _)
        (Nat.zero_le _)
        (by simp) hF (Nat.le_refl _)
        hread hfwd
    have hwEq : wB' = BitVec.ofNat 64 w' := by
      apply BitVec.eq_of_toNat_eq
      rw [hwN', hwlen, BitVec.toNat_ofNat]
      exact (Nat.mod_eq_of_lt hla64).symm
    have hevW' : memEvalExpr (.var "w") ρ' m'
        [("a", 1, 1), ("out", 0, 0)] =
        .ok (.u64 (BitVec.ofNat 64 w')) := by
      rw [← hwEq]
      exact (memEvalExpr_var _ _ _ _).trans
        (evalExpr_var_hit _ _ _ hwB')
    have hretM := memEvalProgStmt_return vecReverseCopyProg F
      (.var "w") ρ' m' [("a", 1, 1), ("out", 0, 0)]
      (.u64 (BitVec.ofNat 64 w')) hevW'
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hfallM,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletW,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletJ,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hloop,
      hretM]

/-- Memory entry, err leg: the prelude binds, the loop hits
    the short `out` and fails loud. -/
theorem memEvalProgFunc_vecReverseCopy_err (F : Nat)
    (la lo : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length ≤ F)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hmore : lo.length < la.length)
    (hfwd : reverseCopyFwd la lo la.length 0 la.length =
      .error .AssertFail) :
    memEvalProgFunc vecReverseCopyProg F vecReverseCopyFunc
      [.stdVecVal la, .stdVecVal lo] =
      .error .AssertFail := by
  have hbind := bindMemArgs_vecReverseCopy la lo
  have hbody : vecReverseCopyFunc.body =
      (.seq (.if_ (.ueq (.stdVecLen "a")
                  (.lit (.u64 (BitVec.ofNat 64 0))))
            (.return_ (.lit (.u64 (BitVec.ofNat 64 0))))
            .skip)
        (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq (.let_ "j" (.u 64) (.stdVecLen "a"))
            (.seq vecReverseCopyLoop
              (.return_ (.var "w")))))) := rfl
  have hle : 1 ≤ la.length := by omega
  cases hla : la with
  | nil =>
    subst hla
    simp at hmore
  | cons b0 ys =>
    subst hla
    have ha₂ : envLookup [("a", .stdVecVal (b0 :: ys)),
        ("out", .stdVecVal lo)] "a" =
        some (.stdVecVal (b0 :: ys)) := by simp [envLookup]
    have hlenV : evalExpr (.stdVecLen "a")
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)] =
        .ok (.u64 (BitVec.ofNat 64 (b0 :: ys).length)) :=
      evalExpr_stdVecLen_some _ _ _ ha₂
    have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)] =
        .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
    have hlenN : (BitVec.ofNat 64 (b0 :: ys).length).toNat =
        (b0 :: ys).length := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
    have hnn : BitVec.ofNat 64 (b0 :: ys).length ≠
        BitVec.ofNat 64 0 := by
      intro hcon
      have h0 := congrArg BitVec.toNat hcon
      rw [hlenN] at h0
      simp at h0
    have hbeq : (BitVec.ofNat 64 (b0 :: ys).length ==
        BitVec.ofNat 64 0) = false :=
      beq_eq_false_iff_ne.mpr hnn
    have hguardV : evalExpr (.ueq (.stdVecLen "a")
        (.lit (.u64 (BitVec.ofNat 64 0))))
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)] =
        .ok (.b false) := by
      have h := evalExpr_ueq_u64_vars (.stdVecLen "a")
        (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        (BitVec.ofNat 64 (b0 :: ys).length)
        (BitVec.ofNat 64 0) hlenV hlitV
      rwa [hbeq] at h
    have hguardM : memEvalExpr (.ueq (.stdVecLen "a")
        (.lit (.u64 (BitVec.ofNat 64 0))))
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        (⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
        [("a", 1, 1), ("out", 0, 0)] = .ok (.b false) := by
      have hmemLen : memLoad
          (⟨2, [(1, ⟨1, true,
            (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
            (0, ⟨0, true,
            (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
          1 1 0 =
          .ok (BitVec.ofNat 32 (b0 :: ys).length) := by
        have hmem_a : memFind
            (⟨2, [(1, ⟨1, true,
              (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
              (0, ⟨0, true,
              (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem) 1 =
            some ⟨1, true,
              (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩ :=
          memFind_cons_hit _ _ _ _ _
        exact memLoad_cellsAt _ 1 1 0 _ _ hmem_a (by simp)
      have hag := memEvalExpr_ueq_agree (.stdVecLen "a")
        (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        (⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
        [("a", 1, 1), ("out", 0, 0)]
        (memEvalExpr_stdVecLen_hit "a" _ _ _ _ _ _
          (by simp [layoutLookup])
          (by simp [envLookup]) hmemLen)
        (memEvalExpr_lit _ _ _ _)
      rw [hag]; exact hguardV
    have hifF := memEvalProgStmt_if_false vecReverseCopyProg F
      (.ueq (.stdVecLen "a") (.lit (.u64 (BitVec.ofNat 64 0))))
      (.return_ (.lit (.u64 (BitVec.ofNat 64 0)))) .skip
      [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
      (⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
      [("a", 1, 1), ("out", 0, 0)] hguardM
    have hskipM : memEvalProgStmt vecReverseCopyProg F .skip
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        (⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
        [("a", 1, 1), ("out", 0, 0)] =
        .ok (([("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)],
          (⟨2, [(1, ⟨1, true,
            (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
            (0, ⟨0, true,
            (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem),
          [("a", 1, 1), ("out", 0, 0)]), .fellThrough) := by
      cases F <;> simp [memEvalProgStmt, memEvalStmtFuel,
        memEvalStmtZero, memEvalStmtWith]
    have hfallM := hifF.trans hskipM
    have hlitM : memEvalExpr
        (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        (⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
        [("a", 1, 1), ("out", 0, 0)] =
        evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
          [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)] :=
      memEvalExpr_lit _ _ _ _
    have hlitW : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)] =
        .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
    have hletW := memRevLet vecReverseCopyProg F "w" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
      (⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
      [("a", 1, 1), ("out", 0, 0)] (.u64 (BitVec.ofNat 64 0))
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) (by intro h; cases h) hlitM hlitW
    have haJw : envLookup (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        "w" (.u64 (BitVec.ofNat 64 0))) "a" =
        some (.stdVecVal (b0 :: ys)) := by
      rw [envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "w" by decide)]
      simp [envLookup]
    have hlenJ : evalExpr (.stdVecLen "a")
        (envExtend [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
          "w" (.u64 (BitVec.ofNat 64 0))) =
        .ok (.u64 (BitVec.ofNat 64 (b0 :: ys).length)) :=
      evalExpr_stdVecLen_some _ _ _ haJw
    have hmemLenJ : memLoad
        (⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
        1 1 0 =
        .ok (BitVec.ofNat 32 (b0 :: ys).length) := by
      have hmem_a : memFind
          (⟨2, [(1, ⟨1, true,
            (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
            (0, ⟨0, true,
            (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem) 1 =
          some ⟨1, true,
            (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩ :=
        memFind_cons_hit _ _ _ _ _
      exact memLoad_cellsAt _ 1 1 0 _ _ hmem_a (by simp)
    have hlenJM : memEvalExpr (.stdVecLen "a")
        (envExtend [("a", .stdVecVal (b0 :: ys)),
          ("out", .stdVecVal lo)]
          "w" (.u64 (BitVec.ofNat 64 0)))
        (⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
        [("a", 1, 1), ("out", 0, 0)] =
        evalExpr (.stdVecLen "a")
          (envExtend [("a", .stdVecVal (b0 :: ys)),
            ("out", .stdVecVal lo)]
            "w" (.u64 (BitVec.ofNat 64 0))) :=
      memEvalExpr_stdVecLen_hit "a" _ _ _ _ _ _
        (by simp [layoutLookup]) haJw hmemLenJ
    have hletJ := memRevLet vecReverseCopyProg F "j" (.u 64)
      (.stdVecLen "a")
      (envExtend [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        "w" (.u64 (BitVec.ofNat 64 0)))
      (⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
      [("a", 1, 1), ("out", 0, 0)]
      (.u64 (BitVec.ofNat 64 (b0 :: ys).length))
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) (by intro h; cases h) hlenJM hlenJ
    have hw0N : (BitVec.ofNat 64 0).toNat = 0 := by decide
    have ha₁ : envLookup (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        "w" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 (b0 :: ys).length))) "a" =
        some (.stdVecVal (b0 :: ys)) := by
      rw [envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "j" by decide),
        envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "w" by decide)]
      simp [envLookup]
    have hout₁ : envLookup (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        "w" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 (b0 :: ys).length))) "out" =
        some (.stdVecVal lo) := by
      rw [envExtend_miss _ _ _ _
        (show ("out" : String) ≠ "j" by decide),
        envExtend_miss _ _ _ _
        (show ("out" : String) ≠ "w" by decide)]
      simp [envLookup, show ("out" : String) ≠ "a" by decide]
    have hw₁ : envLookup (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        "w" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 (b0 :: ys).length))) "w" =
        some (.u64 (BitVec.ofNat 64 0)) := by
      rw [envExtend_miss _ _ _ _
        (show ("w" : String) ≠ "j" by decide)]
      exact envExtend_hit _ _ _
    have hj₁ : envLookup (envExtend (envExtend
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        "w" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 (b0 :: ys).length))) "j" =
        some (.u64 (BitVec.ofNat 64 (b0 :: ys).length)) :=
      envExtend_hit _ _ _
    have hloop : memEvalProgStmt vecReverseCopyProg F
        vecReverseCopyLoop
        (envExtend (envExtend
          [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
          "w" (.u64 (BitVec.ofNat 64 0)))
          "j" (.u64 (BitVec.ofNat 64 (b0 :: ys).length)))
        (⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
        [("a", 1, 1), ("out", 0, 0)] =
        .error .AssertFail :=
      memReverseCopyLoop_err vecReverseCopyProg F ((b0 :: ys).length)
        (envExtend (envExtend
          [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
          "w" (.u64 (BitVec.ofNat 64 0)))
          "j" (.u64 (BitVec.ofNat 64 (b0 :: ys).length)))
        (⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 (b0 :: ys).length) :: (b0 :: ys)⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem)
        [("a", 1, 1), ("out", 0, 0)]
        (b0 :: ys) lo 0 ((b0 :: ys).length)
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 (b0 :: ys).length)
        1 0 1 0
        (BitVec.ofNat 32 (b0 :: ys).length)
        (BitVec.ofNat 32 lo.length)
        (by simp [layoutLookup]) (by simp [layoutLookup])
        (memFind_cons_hit _ _ _ _ _)
        (by
          have hne01 : (0 : Nat) ≠ 1 := by decide
          rw [memFind_cons_miss _ _ _ _ _ _ hne01]
          exact memFind_cons_hit _ _ _ _ _)
        rfl rfl (by decide)
        hw0N hlenN hla64 hlo64 ha₁ hout₁ hw₁ hj₁
        (by omega) (Nat.le_refl _)
        (Nat.zero_le _)
        (by simp) hF (Nat.le_refl _)
        hread hfwd
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hfallM,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletW,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletJ,
      memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hloop]

/-! ## Transfer + closing contract -/

/-- Transfer for `vec_reverse_copy`, ok leg: both layers agree
    on the copied count. -/
theorem memTransferProg_vecReverseCopy_ok (F : Nat)
    (la lo : List (BitVec 32))
    (w' : Nat) (lo' : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length ≤ F)
    (hle : 1 ≤ la.length)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hfwd : reverseCopyFwd la lo la.length 0 la.length =
      .ok (w', 0, lo'))
    (hwlen : w' = la.length)
    (_h : oracleNoalias vecReverseCopyFunc
      [.stdVecVal la, .stdVecVal lo]) :
    memEvalProgFunc vecReverseCopyProg F vecReverseCopyFunc
      [.stdVecVal la, .stdVecVal lo] =
      evalProgFunc vecReverseCopyProg F vecReverseCopyFunc
        [.stdVecVal la, .stdVecVal lo] := by
  rw [memEvalProgFunc_vecReverseCopy_ok F la lo w' lo'
    hla64 hlo64 hF hle hread hfwd hwlen,
    evalProgFunc_vecReverseCopy_ok F la lo w' lo'
    hla64 hlo64 hF hle hread hfwd hwlen]

/-- Transfer for `vec_reverse_copy`, err leg: both sides fail
    loud on a short record. -/
theorem memTransferProg_vecReverseCopy_err (F : Nat)
    (la lo : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length ≤ F)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hmore : lo.length < la.length)
    (hfwd : reverseCopyFwd la lo la.length 0 la.length =
      .error .AssertFail)
    (_h : oracleNoalias vecReverseCopyFunc
      [.stdVecVal la, .stdVecVal lo]) :
    memEvalProgFunc vecReverseCopyProg F vecReverseCopyFunc
      [.stdVecVal la, .stdVecVal lo] =
      evalProgFunc vecReverseCopyProg F vecReverseCopyFunc
        [.stdVecVal la, .stdVecVal lo] := by
  rw [memEvalProgFunc_vecReverseCopy_err F la lo
    hla64 hlo64 hF hread hmore hfwd,
    evalProgFunc_vecReverseCopy_err F la lo
    hla64 hlo64 hF hread hmore hfwd]

/-- Closing caller-record reverse contract, ok leg: when the
    reverse fits, the forward returns the source length over
    the reversed prefix, record length unchanged. -/
theorem evalProgFunc_vecReverseCopy_spec_ok (F : Nat)
    (la lo : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length ≤ F)
    (hcap : la.length ≤ lo.length) :
    ∃ (w' : Nat) (lo' : List (BitVec 32)),
      memEvalProgFunc vecReverseCopyProg F vecReverseCopyFunc
        [.stdVecVal la, .stdVecVal lo] =
        .ok (.u64 (BitVec.ofNat 64 w')) ∧
      lo'.take w' = la.reverse ∧
      w' = la.length ∧
      lo'.length = lo.length := by
  have hread : ∀ p, p < la.length → ∃ y, la[p]? = some y :=
    fun p hp => ⟨_, List.getElem?_eq_getElem hp⟩
  cases hla : la with
  | nil =>
    subst hla
    refine ⟨0, lo, memEvalProgFunc_vecReverseCopy_nil F lo, ?_, rfl,
      rfl⟩
    simp
  | cons a0 xs =>
    subst hla
    obtain ⟨w', lo', hfwd, hpref, hwlen, hlen'⟩ :=
      reverseCopyFwd_ok (a0 :: xs) lo ((a0 :: xs).length) 0
        ((a0 :: xs).length)
        (by omega) (Nat.le_refl _) (Nat.le_refl _)
        hread (by simp) (Nat.zero_le _) hcap
    have heval := evalProgFunc_vecReverseCopy_ok F (a0 :: xs) lo
      w' lo' hla64 hlo64 hF (by simp) hread hfwd hwlen
    have htrans := memTransferProg_vecReverseCopy_ok F (a0 :: xs) lo
      w' lo' hla64 hlo64 hF (by simp) hread hfwd hwlen
      (oracleNoalias_vecReverseCopy _ _)
    rw [htrans]
    exact ⟨w', lo', heval, hpref, hwlen, hlen'⟩

/-- Closing caller-record reverse contract, err leg: a short
    record fails loud on both layers. -/
theorem evalProgFunc_vecReverseCopy_spec_err (F : Nat)
    (la lo : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length ≤ F)
    (hmore : lo.length < la.length) :
    memEvalProgFunc vecReverseCopyProg F vecReverseCopyFunc
      [.stdVecVal la, .stdVecVal lo] =
      .error .AssertFail := by
  have hread : ∀ p, p < la.length → ∃ y, la[p]? = some y :=
    fun p hp => ⟨_, List.getElem?_eq_getElem hp⟩
  cases hla : la with
  | nil =>
    subst hla
    simp at hmore
  | cons a0 xs =>
    subst hla
    have hfwd := reverseCopyFwd_err_of_overflow (a0 :: xs) lo
      hread hmore
    have herrM := memEvalProgFunc_vecReverseCopy_err F (a0 :: xs) lo
      hla64 hlo64 hF hread hmore hfwd
    exact herrM