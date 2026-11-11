/-
Circe.Transfer.VecUniqueCopy — mem transfer for the caller-record
squeeze (`vec_unique_copy`, the `std::unique_copy` idiom; P2-M16).

Mirrors the value side (`valUniqueCopySeed_hit/_short`,
`valUniqueCopyBody_keep/_short/_drop`, `valUniqueCopyLoop_ok/_err`
in `Circe.Emit.VecUniqueCopy`) step for step on the memory
layer: the read-only `a` block pins its snapshot while the
record block threads through `memStore` in lockstep (the `a`
block framed across each `out` store via
`memFind_memStore_other`); the keep test reads the previous
survivor from the record through `memLoad`, the keep store is
guarded by the inner `ult` (the short-`out` leg fires the loud
`AssertFail` through guard-false + fail), and the loop
re-inducts over `(ρ, m, π)` with the forward equation
threading (two fuels) plus the squeezed-prefix invariant and
the record bound. Entries close against the forward contract;
the closing specs tie the `u64` survivor count to the `dedupAdj`
prefix over the independent squeeze oracle
(`uniqueCopyFwd_*` in `Circe.Specs`).
-/
import Circe.Transfer.VecReverse
import Circe.Emit.VecUniqueCopy
import Circe.Specs

/-! ## Binding (closed form) -/

/-- Unique-copy binding pins two snapshots: the shared-borrow
    input at addr `1`, the mut-borrow record at addr `0`
    (tail-first allocation order — the M12 precedent). -/
theorem bindMemArgs_vecUniqueCopy (la lo : List (BitVec 32)) :
    bindMemArgs vecUniqueCopyFunc.args
      [.stdVecVal la, .stdVecVal lo] emptyMem =
      some ([("a", .stdVecVal la), ("out", .stdVecVal lo)],
        (⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 la.length) :: la⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ : Mem),
        [("a", 1, 1), ("out", 0, 0)]) := by
  rfl

/-- Unique-copy footprint is two disjoint singletons. -/
theorem oracleNoalias_vecUniqueCopy (la lo : List (BitVec 32)) :
    oracleNoalias vecUniqueCopyFunc
      [.stdVecVal la, .stdVecVal lo] := by
  have hb := bindMemArgs_vecUniqueCopy la lo
  have hn : LayoutNoAlias [("a", 1, 1), ("out", 0, 0)] := by
    simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩


/-! ## Memory seed store -/

/-- Seed store on memory, hit branch: `out` is nonempty, so
    the checked seed store plants `a[0]` at record index 0 in
    lockstep (the `a` block framed across the `out` store). -/
theorem memUniqueCopySeed_hit (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lo : List (BitVec 32)) (a0 o0 : BitVec 32)
    (aa ao : Nat) (ta to : Nat) (na no : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_o : layoutLookup π "out" = some (ao, to))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_o : memFind m ao = some ⟨to, true, no :: lo⟩)
    (hna : na = BitVec.ofNat 32 la.length)
    (hno : no = BitVec.ofNat 32 lo.length)
    (haa : aa ≠ ao)
    (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (ha0 : la[0]? = some a0) (ho0 : lo[0]? = some o0) :
    ∃ ρ' m', memEvalProgStmt prog F vecUniqueCopySeed ρ m π =
      .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "out" = some (.stdVecVal (lo.set 0 a0)) ∧
      memFind m' ao = some ⟨to, true, no :: (lo.set 0 a0)⟩ ∧
      memFind m' aa = some ⟨ta, true, na :: la⟩ := by
  have h0lt : 0 < lo.length := transformRead_lt lo 0 o0 ho0
  have h0N : (BitVec.ofNat 64 0).toNat = 0 := by
    simp [BitVec.toNat_ofNat]
  have hlitM : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0))) ρ m π =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0))) ρ :=
    memEvalExpr_lit _ _ _ _
  have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0))) ρ =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  have hmemLenO : memLoad m ao to 0 =
      .ok (BitVec.ofNat 32 lo.length) := by
    rw [← hno]
    exact memLoad_cellsAt m ao to 0 (no :: lo) no hmem_o (by simp)
  have hlenM : memEvalExpr (.stdVecLen "out") ρ m π =
      evalExpr (.stdVecLen "out") ρ :=
    memEvalExpr_stdVecLen_hit "out" ρ m π lo ao to
      hlay_o hout hmemLenO
  have hguardV : evalExpr
      (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "out")) ρ =
      .ok (.b true) := by
    have hult := evalExpr_ult_u64lit (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 lo.length) (.stdVecLen "out") ρ
      (evalExpr_stdVecLen_some _ _ _ hout)
    have htb : ((BitVec.ofNat 64 0).ult
        (BitVec.ofNat 64 lo.length)) = true := by
      have hlenN : (BitVec.ofNat 64 lo.length).toNat = lo.length := by
        rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt hlo64
      rw [BitVec.ult_eq_decide, h0N, hlenN]
      exact decide_eq_true (by omega)
    rwa [htb] at hult
  have hguardM : memEvalExpr
      (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "out"))
      ρ m π = .ok (.b true) := by
    have hag := memEvalExpr_ult_agree
      (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "out") ρ m π
      hlitM hlenM
    rw [hag]; exact hguardV
  have hgetA0 : la[(BitVec.ofNat 64 0).toNat]? = some a0 := by
    rw [h0N]; exact ha0
  have hgetO : lo[(BitVec.ofNat 64 0).toNat]? = some o0 := by
    rw [h0N]; exact ho0
  have hmemA0 : memLoad m aa ta ((BitVec.ofNat 64 0).toNat + 1)
      = .ok a0 :=
    memLoad_cellsAt m aa ta ((BitVec.ofNat 64 0).toNat + 1)
      (na :: la) a0 hmem_a
      (by rw [List.getElem?_cons_succ]; exact hgetA0)
  have hatA : evalExpr
      (.stdVecAt "a" (.lit (.u64 (BitVec.ofNat 64 0)))) ρ =
      .ok (.i32 a0) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hlitV hgetA0
  have hatM : memEvalExpr
      (.stdVecAt "a" (.lit (.u64 (BitVec.ofNat 64 0)))) ρ m π =
      .ok (.i32 a0) := by
    have hag := memEvalExpr_stdVecAt_hit "a"
      (.lit (.u64 (BitVec.ofNat 64 0))) ρ m π la
      (BitVec.ofNat 64 0) a0 aa ta
      hlay_a ha (memEvalExpr_lit _ _ _ _) hlitV
      hmemA0 hgetA0
    rw [hag]; exact hatA
  have hlt₁ : (BitVec.ofNat 64 0).toNat + 1 < (no :: lo).length := by
    simp only [List.length_cons]
    omega
  obtain ⟨m₁, hmstore, hmem₁⟩ :=
    memStore_cellsAt_pin m ao to a0 hmem_o hlt₁
  have hsetB : lo.set (BitVec.ofNat 64 0).toNat a0
      = lo.set 0 a0 := by rw [h0N]
  rw [hsetB] at hmem₁
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "out"
    (.stdVecVal lo)
    (.stdVecVal (lo.set (BitVec.ofNat 64 0).toNat a0)) hout
  have hstep_set := memRevVecSet prog F "out"
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (.stdVecAt "a" (.lit (.u64 (BitVec.ofNat 64 0))))
    ρ m π (BitVec.ofNat 64 0) a0 ao to lo o0 m₁ ρ₁
    hlitM hatM hout hlay_o hgetO hmstore hu₁
  have hmem_a₁ : memFind m₁ aa = some ⟨ta, true, na :: la⟩ := by
    have h := memFind_memStore_other m m₁ ao aa to
      ((BitVec.ofNat 64 0).toNat + 1) a0 hmstore haa
    rw [h]; exact hmem_a
  have ha₁ : envLookup ρ₁ "a" = some (.stdVecVal la) := by
    have h := envLookup_update_miss ρ "a" "out" _ ρ₁
      (show ("a" : String) ≠ "out" by decide) hu₁
    rw [h]; exact ha
  have hupd := envLookup_update_hit _ _ _ _ hu₁
  have hout₁ : envLookup ρ₁ "out"
      = some (.stdVecVal (lo.set 0 a0)) := by
    rwa [hsetB] at hupd
  have hif : memEvalProgStmt prog F
      (.if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0)))
              (.stdVecLen "out"))
        (.vecSet "out" (.lit (.u64 (BitVec.ofNat 64 0)))
          (.stdVecAt "a" (.lit (.u64 (BitVec.ofNat 64 0)))))
        .fail) ρ m π = .ok ((ρ₁, m₁, π), .fellThrough) :=
    (memEvalProgStmt_if_true prog F _ _ _ _ _ _ hguardM).trans
      hstep_set
  have hseed : vecUniqueCopySeed =
      (.if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0)))
              (.stdVecLen "out"))
        (.vecSet "out" (.lit (.u64 (BitVec.ofNat 64 0)))
          (.stdVecAt "a" (.lit (.u64 (BitVec.ofNat 64 0)))))
        .fail) := rfl
  have heval : memEvalProgStmt prog F vecUniqueCopySeed ρ m π =
      .ok ((ρ₁, m₁, π), .fellThrough) := by
    rw [hseed]; exact hif
  exact ⟨ρ₁, m₁, heval, ha₁, hout₁, hmem₁, hmem_a₁⟩

/-- Seed store on memory, short branch: `out` is empty, so the
    checked seed store fails loud. -/
theorem memUniqueCopySeed_short (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lo : List (BitVec 32)) (a0 : BitVec 32)
    (aa ao : Nat) (ta to : Nat) (na no : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_o : layoutLookup π "out" = some (ao, to))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_o : memFind m ao = some ⟨to, true, no :: lo⟩)
    (hno : no = BitVec.ofNat 32 lo.length)
    (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (ha0 : la[0]? = some a0) (hmiss : lo[0]? = none) :
    memEvalProgStmt prog F vecUniqueCopySeed ρ m π =
      .error .AssertFail := by
  have hnl : ¬ 0 < lo.length := by
    intro h
    have hsome : lo[0]? = some lo[0] := List.getElem?_eq_getElem h
    rw [hsome] at hmiss
    simp at hmiss
  have h0N : (BitVec.ofNat 64 0).toNat = 0 := by
    simp [BitVec.toNat_ofNat]
  have hlitM : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0))) ρ m π =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0))) ρ :=
    memEvalExpr_lit _ _ _ _
  have hmemLenO : memLoad m ao to 0 =
      .ok (BitVec.ofNat 32 lo.length) := by
    rw [← hno]
    exact memLoad_cellsAt m ao to 0 (no :: lo) no hmem_o (by simp)
  have hlenM : memEvalExpr (.stdVecLen "out") ρ m π =
      evalExpr (.stdVecLen "out") ρ :=
    memEvalExpr_stdVecLen_hit "out" ρ m π lo ao to
      hlay_o hout hmemLenO
  have hguardV : evalExpr
      (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "out")) ρ =
      .ok (.b false) := by
    have hult := evalExpr_ult_u64lit (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 lo.length) (.stdVecLen "out") ρ
      (evalExpr_stdVecLen_some _ _ _ hout)
    have hlenN : (BitVec.ofNat 64 lo.length).toNat = lo.length := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlo64
    have hfb : ((BitVec.ofNat 64 0).ult
        (BitVec.ofNat 64 lo.length)) = false := by
      rw [BitVec.ult_eq_decide, h0N, hlenN]
      exact decide_eq_false (by omega)
    rwa [hfb] at hult
  have hguardM : memEvalExpr
      (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "out"))
      ρ m π = .ok (.b false) := by
    have hag := memEvalExpr_ult_agree
      (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "out") ρ m π
      hlitM hlenM
    rw [hag]; exact hguardV
  have hfail : memEvalProgStmt prog F .fail ρ m π =
      .error .AssertFail := by
    simpa [memEvalProgStmt] using (memEvalStmtFuel_fail F ρ m π)
  have hseed : vecUniqueCopySeed =
      (.if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0)))
              (.stdVecLen "out"))
        (.vecSet "out" (.lit (.u64 (BitVec.ofNat 64 0)))
          (.stdVecAt "a" (.lit (.u64 (BitVec.ofNat 64 0)))))
        .fail) := rfl
  rw [hseed]
  exact (memEvalProgStmt_if_false prog F _ _ _ _ _ _ hguardM).trans
    hfail

/-! ## Memory body hits -/

/-- One body iteration on memory, keep branch: the reads
    agree with the value side, the keep test fires, the `out`
    guard holds, the survivor stores into the `out` block in
    lockstep (the `a` block framed across the store), and both
    cursors bump. -/
theorem memUniqueCopyBody_keep (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lo : List (BitVec 32))
    (r w : Nat) (rB wB : BitVec 64) (y p wOld : BitVec 32)
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
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hrlt : r < la.length) (hw1 : 1 ≤ w)
    (hy : la[r]? = some y) (hp : lo[w - 1]? = some p)
    (hwget : lo[w]? = some wOld)
    (hwlt : w < lo.length)
    (hkeep : (y != p) = true) :
    ∃ ρ' m', memEvalProgStmt prog F vecUniqueCopyBody ρ m π =
      .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "out" = some (.stdVecVal (lo.set w y)) ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r + 1) ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w + 1) ∧
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
  have hsub : evalExpr (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64)))) ρ =
      .ok (.u64 (wB - 1)) :=
    evalExpr_u64_usub wB 1 (.var "w") ρ hwVar
  have hsubN : (wB - 1).toNat = w - 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    have hno' : ¬ BitVec.usubOverflow wB 1 := by
      rw [BitVec.usubOverflow, decide_eq_true_eq, hwN, h1]
      omega
    rw [BitVec.toNat_sub_of_not_usubOverflow hno', hwN, h1]
  have hsubM_ag : memEvalExpr (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64)))) ρ m π =
      evalExpr (.usub (.var "w") (.lit (.u64 (1 : BitVec 64)))) ρ :=
    memEvalExpr_usub_agree (.var "w") (.lit (.u64 (1 : BitVec 64)))
      ρ m π (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)
  have hgetP : lo[(wB - 1).toNat]? = some p := by
    rw [hsubN]; exact hp
  have hmemP : memLoad m ao to ((wB - 1).toNat + 1) = .ok p :=
    memLoad_cellsAt m ao to ((wB - 1).toNat + 1) (no :: lo) p
      hmem_o (by rw [List.getElem?_cons_succ]; exact hgetP)
  have hatP : evalExpr vecUniqueCopyPrev ρ = .ok (.i32 p) := by
    show evalExpr (.stdVecAt "out" (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64))))) ρ = _
    exact evalExpr_stdVecAt_some _ _ _ _ _ _ hout hsub hgetP
  have hatPM_ag : memEvalExpr vecUniqueCopyPrev ρ m π =
      evalExpr vecUniqueCopyPrev ρ := by
    show memEvalExpr (.stdVecAt "out" (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64))))) ρ m π = _
    exact memEvalExpr_stdVecAt_hit "out" (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64)))) ρ m π lo (wB - 1) p ao to
      hlay_o hout hsubM_ag hsub hmemP hgetP
  have hatPM : memEvalExpr vecUniqueCopyPrev ρ m π =
      .ok (.i32 p) := by rw [hatPM_ag]; exact hatP
  have huneV : evalExpr
      (.une (.stdVecAt "a" (.var "r")) vecUniqueCopyPrev) ρ =
      .ok (.b true) := by
    have h := evalExpr_une_i32 (.stdVecAt "a" (.var "r"))
      vecUniqueCopyPrev ρ y p hat hatP
    rwa [hkeep] at h
  have huneM : memEvalExpr
      (.une (.stdVecAt "a" (.var "r")) vecUniqueCopyPrev) ρ m π =
      .ok (.b true) :=
    (memEvalExpr_une_agree (.stdVecAt "a" (.var "r"))
      vecUniqueCopyPrev ρ m π hatM_ag hatPM_ag).trans huneV
  have hmemLenO : memLoad m ao to 0 =
      .ok (BitVec.ofNat 32 lo.length) := by
    rw [← hno]
    exact memLoad_cellsAt m ao to 0 (no :: lo) no hmem_o (by simp)
  have hlenM : memEvalExpr (.stdVecLen "out") ρ m π =
      evalExpr (.stdVecLen "out") ρ :=
    memEvalExpr_stdVecLen_hit "out" ρ m π lo ao to
      hlay_o hout hmemLenO
  have hguardV : evalExpr (.ult (.var "w") (.stdVecLen "out")) ρ =
      .ok (.b true) := by
    have hlenN : (BitVec.ofNat 64 lo.length).toNat = lo.length := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlo64
    have hult := evalExpr_ult_u64 (.var "w") (.stdVecLen "out") ρ wB
      (BitVec.ofNat 64 lo.length) hwVar
      (evalExpr_stdVecLen_some _ _ _ hout)
    have htb : (wB.ult (BitVec.ofNat 64 lo.length)) = true := by
      rw [BitVec.ult_eq_decide, hwN, hlenN]
      exact decide_eq_true (by omega)
    rwa [htb] at hult
  have hguardM : memEvalExpr (.ult (.var "w") (.stdVecLen "out"))
      ρ m π = .ok (.b true) := by
    have hag := memEvalExpr_ult_agree (.var "w") (.stdVecLen "out")
      ρ m π (memEvalExpr_var _ _ _ _) hlenM
    rw [hag]; exact hguardV
  have hlt₁ : wB.toNat + 1 < (no :: lo).length := by
    simp only [List.length_cons]
    omega
  obtain ⟨m₁, hmstore, hmem₁⟩ :=
    memStore_cellsAt_pin m ao to y hmem_o hlt₁
  have hsetB : lo.set wB.toNat y = lo.set w y := by rw [hwN]
  rw [hsetB] at hmem₁
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "out"
    (.stdVecVal lo) (.stdVecVal (lo.set wB.toNat y)) hout
  have hstep_set := memRevVecSet prog F "out" (.var "w")
    (.stdVecAt "a" (.var "r")) ρ m π wB y ao to lo wOld m₁ ρ₁
    hwVarM hatM hout hlay_o hgetW hmstore hu₁
  have hmem_a₁ : memFind m₁ aa = some ⟨ta, true, na :: la⟩ := by
    have h := memFind_memStore_other m m₁ ao aa to (wB.toNat + 1) y
      hmstore haa
    rw [h]; exact hmem_a
  have ha₁ : envLookup ρ₁ "a" = some (.stdVecVal la) := by
    have h := envLookup_update_miss ρ "a" "out" _ ρ₁
      (show ("a" : String) ≠ "out" by decide) hu₁
    rw [h]; exact ha
  have hr₁ : envLookup ρ₁ "r" = some (.u64 rB) := by
    have h := envLookup_update_miss ρ "r" "out" _ ρ₁
      (show ("r" : String) ≠ "out" by decide) hu₁
    rw [h]; exact hr
  have hwVarM₁ : memEvalExpr (.var "w") ρ₁ m₁ π =
      .ok (.u64 wB) :=
    (memEvalExpr_var _ _ _ _).trans
      (evalExpr_var_hit _ _ _
        (by rw [envLookup_update_miss _ _ _ _ _
          (show ("w" : String) ≠ "out" by decide) hu₁]; exact hw))
  have hevW : evalExpr (.uadd (.var "w")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁ =
      .ok (.u64 (wB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _
        (by rw [envLookup_update_miss _ _ _ _ _
          (show ("w" : String) ≠ "out" by decide) hu₁]; exact hw))
      (by simp [evalExpr, litVal])
  have hevWM : memEvalExpr
      (.uadd (.var "w") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁ m₁ π =
      .ok (.u64 (wB + 1)) :=
    (memEvalExpr_uadd_agree (.var "w") (.lit (.u64 (BitVec.ofNat 64 1)))
      ρ₁ m₁ π (memEvalExpr_var _ _ _ _)
      (memEvalExpr_lit _ _ _ _)).trans hevW
  obtain ⟨ρ₂, hu₂⟩ := envUpdate_some_of_lookup ρ₁ "w"
    (.u64 wB) (.u64 (wB + 1))
    (by rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "out" by decide) hu₁]; exact hw)
  have hstep_w := memRevAssign prog F "w"
    (.uadd (.var "w") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁ m₁ π
    (.u64 (wB + 1)) ρ₂ hevWM hevW hu₂
  have hr₂ : envLookup ρ₂ "r" = some (.u64 rB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("r" : String) ≠ "w" by decide) hu₂]
    exact hr₁
  have ha₂ : envLookup ρ₂ "a" = some (.stdVecVal la) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "w" by decide) hu₂]
    exact ha₁
  have hrVarM₂ : memEvalExpr (.var "r") ρ₂ m₁ π =
      .ok (.u64 rB) := by
    have hr₂' := hr₂
    exact (memEvalExpr_var _ _ _ _).trans
      (evalExpr_var_hit _ _ _ hr₂')
  have hevR : evalExpr (.uadd (.var "r")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ =
      .ok (.u64 (rB + 1)) := by
    have hr₂' := hr₂
    exact evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hr₂') (by simp [evalExpr, litVal])
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
  have hout₃ : envLookup ρ₃ "out" =
      some (.stdVecVal (lo.set w y)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "r" by decide) hu₃]
    rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "w" by decide) hu₂]
    have h := envLookup_update_hit _ _ _ _ hu₁
    rwa [hsetB] at h
  have ha₃ : envLookup ρ₃ "a" = some (.stdVecVal la) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "r" by decide) hu₃]
    exact ha₂
  have hmem_a₃ : memFind m₁ aa = some ⟨ta, true, na :: la⟩ :=
    hmem_a₁
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
  have hinner : memEvalProgStmt prog F
      (.if_ (.ult (.var "w") (.stdVecLen "out"))
        (.seq (.vecSet "out" (.var "w")
                (.stdVecAt "a" (.var "r")))
          (.assign "w" (.uadd (.var "w")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        .fail) ρ m π = .ok ((ρ₂, m₁, π), .fellThrough) := by
    have hthen : memEvalProgStmt prog F
        (.seq (.vecSet "out" (.var "w")
                (.stdVecAt "a" (.var "r")))
          (.assign "w" (.uadd (.var "w")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        ρ m π = .ok ((ρ₂, m₁, π), .fellThrough) := by
      rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
        hstep_set, hstep_w]
    exact (memEvalProgStmt_if_true prog F _ _ _ _ _ _
      hguardM).trans hthen
  have hif : memEvalProgStmt prog F
      (.if_ (.une (.stdVecAt "a" (.var "r")) vecUniqueCopyPrev)
        (.if_ (.ult (.var "w") (.stdVecLen "out"))
          (.seq (.vecSet "out" (.var "w")
                  (.stdVecAt "a" (.var "r")))
            (.assign "w" (.uadd (.var "w")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)
        .skip) ρ m π = .ok ((ρ₂, m₁, π), .fellThrough) :=
    (memEvalProgStmt_if_true prog F _ _ _ _ _ _ huneM).trans hinner
  have hbody : vecUniqueCopyBody =
      (.seq (.if_ (.une (.stdVecAt "a" (.var "r")) vecUniqueCopyPrev)
          (.if_ (.ult (.var "w") (.stdVecLen "out"))
            (.seq (.vecSet "out" (.var "w")
                    (.stdVecAt "a" (.var "r")))
              (.assign "w" (.uadd (.var "w")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
            .fail)
          .skip)
        (.assign "r" (.uadd (.var "r")
          (.lit (.u64 (BitVec.ofNat 64 1)))))) := rfl
  have heval : memEvalProgStmt prog F vecUniqueCopyBody ρ m π =
      .ok ((ρ₃, m₁, π), .fellThrough) := by
    rw [hbody,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hif,
      hstep_r]
  exact ⟨ρ₃, m₁, heval, ha₃, hout₃, ⟨(rB + 1), hr', hrN'⟩,
    ⟨(wB + 1), hw', hwN'⟩, hmem₁, hmem_a₃⟩

/-- One body iteration on memory, short-`out` branch: the
    `une` test fires but `w` is past the record, so the inner
    guard fails and the loud `.fail` leg fires. -/
theorem memUniqueCopyBody_short (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lo : List (BitVec 32))
    (r w : Nat) (rB wB : BitVec 64) (y p : BitVec 32)
    (aa ao : Nat) (ta to : Nat) (na no : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_o : layoutLookup π "out" = some (ao, to))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_o : memFind m ao = some ⟨to, true, no :: lo⟩)
    (hno : no = BitVec.ofNat 32 lo.length)
    (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hrlt : r < la.length) (hw1 : 1 ≤ w)
    (hy : la[r]? = some y) (hp : lo[w - 1]? = some p)
    (hmiss : lo[w]? = none)
    (hkeep : (y != p) = true) :
    memEvalProgStmt prog F vecUniqueCopyBody ρ m π =
      .error .AssertFail := by
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
  have hwVar : evalExpr (.var "w") ρ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw
  have hgetR : la[rB.toNat]? = some y := by rw [hrN]; exact hy
  have hsub : evalExpr (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64)))) ρ =
      .ok (.u64 (wB - 1)) :=
    evalExpr_u64_usub wB 1 (.var "w") ρ hwVar
  have hsubN : (wB - 1).toNat = w - 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    have hno' : ¬ BitVec.usubOverflow wB 1 := by
      rw [BitVec.usubOverflow, decide_eq_true_eq, hwN, h1]
      omega
    rw [BitVec.toNat_sub_of_not_usubOverflow hno', hwN, h1]
  have hgetP : lo[(wB - 1).toNat]? = some p := by
    rw [hsubN]; exact hp
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
  have hsubM_ag : memEvalExpr (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64)))) ρ m π =
      evalExpr (.usub (.var "w") (.lit (.u64 (1 : BitVec 64)))) ρ :=
    memEvalExpr_usub_agree (.var "w") (.lit (.u64 (1 : BitVec 64)))
      ρ m π (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)
  have hmemP : memLoad m ao to ((wB - 1).toNat + 1) = .ok p :=
    memLoad_cellsAt m ao to ((wB - 1).toNat + 1) (no :: lo) p
      hmem_o (by rw [List.getElem?_cons_succ]; exact hgetP)
  have hatP : evalExpr vecUniqueCopyPrev ρ = .ok (.i32 p) := by
    show evalExpr (.stdVecAt "out" (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64))))) ρ = _
    exact evalExpr_stdVecAt_some _ _ _ _ _ _ hout hsub hgetP
  have hatPM_ag : memEvalExpr vecUniqueCopyPrev ρ m π =
      evalExpr vecUniqueCopyPrev ρ := by
    show memEvalExpr (.stdVecAt "out" (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64))))) ρ m π = _
    exact memEvalExpr_stdVecAt_hit "out" (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64)))) ρ m π lo (wB - 1) p ao to
      hlay_o hout hsubM_ag hsub hmemP hgetP
  have hatPM : memEvalExpr vecUniqueCopyPrev ρ m π =
      .ok (.i32 p) := by rw [hatPM_ag]; exact hatP
  have huneV : evalExpr
      (.une (.stdVecAt "a" (.var "r")) vecUniqueCopyPrev) ρ =
      .ok (.b true) := by
    have h := evalExpr_une_i32 (.stdVecAt "a" (.var "r"))
      vecUniqueCopyPrev ρ y p hat hatP
    rwa [hkeep] at h
  have huneM : memEvalExpr
      (.une (.stdVecAt "a" (.var "r")) vecUniqueCopyPrev) ρ m π =
      .ok (.b true) :=
    (memEvalExpr_une_agree (.stdVecAt "a" (.var "r"))
      vecUniqueCopyPrev ρ m π hatM_ag hatPM_ag).trans huneV
  have hmemLenO : memLoad m ao to 0 =
      .ok (BitVec.ofNat 32 lo.length) := by
    rw [← hno]
    exact memLoad_cellsAt m ao to 0 (no :: lo) no hmem_o (by simp)
  have hlenM : memEvalExpr (.stdVecLen "out") ρ m π =
      evalExpr (.stdVecLen "out") ρ :=
    memEvalExpr_stdVecLen_hit "out" ρ m π lo ao to
      hlay_o hout hmemLenO
  have hnl : ¬ w < lo.length := by
    intro h
    have hsome : lo[w]? = some lo[w] := List.getElem?_eq_getElem h
    rw [hsome] at hmiss
    simp at hmiss
  have hlenN : (BitVec.ofNat 64 lo.length).toNat = lo.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlo64
  have hguardV : evalExpr (.ult (.var "w") (.stdVecLen "out")) ρ =
      .ok (.b false) := by
    have hwVar' : evalExpr (.var "w") ρ = .ok (.u64 wB) :=
      evalExpr_var_hit _ _ _ hw
    have hult := evalExpr_ult_u64 (.var "w") (.stdVecLen "out") ρ wB
      (BitVec.ofNat 64 lo.length) hwVar'
      (evalExpr_stdVecLen_some _ _ _ hout)
    have hfb : (wB.ult (BitVec.ofNat 64 lo.length)) = false := by
      rw [BitVec.ult_eq_decide, hwN, hlenN]
      exact decide_eq_false (by omega)
    rwa [hfb] at hult
  have hguardM : memEvalExpr (.ult (.var "w") (.stdVecLen "out"))
      ρ m π = .ok (.b false) := by
    have hag := memEvalExpr_ult_agree (.var "w") (.stdVecLen "out")
      ρ m π (memEvalExpr_var _ _ _ _) hlenM
    rw [hag]; exact hguardV
  have hfail : memEvalProgStmt prog F .fail ρ m π =
      .error .AssertFail := by
    simpa [memEvalProgStmt] using (memEvalStmtFuel_fail F ρ m π)
  have hinner : memEvalProgStmt prog F
      (.if_ (.ult (.var "w") (.stdVecLen "out"))
        (.seq (.vecSet "out" (.var "w")
                (.stdVecAt "a" (.var "r")))
          (.assign "w" (.uadd (.var "w")
            (.lit (.u64 (BitVec.ofNat 64 1))))))
        .fail) ρ m π = .error .AssertFail :=
    (memEvalProgStmt_if_false prog F _ _ _ _ _ _ hguardM).trans hfail
  have hif : memEvalProgStmt prog F
      (.if_ (.une (.stdVecAt "a" (.var "r")) vecUniqueCopyPrev)
        (.if_ (.ult (.var "w") (.stdVecLen "out"))
          (.seq (.vecSet "out" (.var "w")
                  (.stdVecAt "a" (.var "r")))
            (.assign "w" (.uadd (.var "w")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)
        .skip) ρ m π = .error .AssertFail :=
    (memEvalProgStmt_if_true prog F _ _ _ _ _ _ huneM).trans hinner
  have hbody : vecUniqueCopyBody =
      (.seq (.if_ (.une (.stdVecAt "a" (.var "r")) vecUniqueCopyPrev)
          (.if_ (.ult (.var "w") (.stdVecLen "out"))
            (.seq (.vecSet "out" (.var "w")
                    (.stdVecAt "a" (.var "r")))
              (.assign "w" (.uadd (.var "w")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
            .fail)
          .skip)
        (.assign "r" (.uadd (.var "r")
          (.lit (.u64 (BitVec.ofNat 64 1)))))) := rfl
  rw [hbody]
  exact memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hif

/-- One body iteration on memory, drop branch: the `une`
    test against the last recorded survivor fails, the state
    (env and memory) threads untouched, only `r` advances. -/
theorem memUniqueCopyBody_drop (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lo : List (BitVec 32))
    (r w : Nat) (rB wB : BitVec 64) (y p : BitVec 32)
    (aa ao : Nat) (ta to : Nat) (na no : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_o : layoutLookup π "out" = some (ao, to))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_o : memFind m ao = some ⟨to, true, no :: lo⟩)
    (hrN : rB.toNat = r) (hwN : wB.toNat = w)
    (hla64 : la.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hrlt : r < la.length) (hw1 : 1 ≤ w)
    (hy : la[r]? = some y) (hp : lo[w - 1]? = some p)
    (hdrop : (y != p) = false) :
    ∃ ρ' m', memEvalProgStmt prog F vecUniqueCopyBody ρ m π =
      .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "out" = some (.stdVecVal lo) ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r + 1) ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w) ∧
      memFind m' ao = some ⟨to, true, no :: lo⟩ ∧
      memFind m' aa = some ⟨ta, true, na :: la⟩ := by
  have hrVar : evalExpr (.var "r") ρ = .ok (.u64 rB) :=
    evalExpr_var_hit _ _ _ hr
  have hwVar : evalExpr (.var "w") ρ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw
  have hrVarM : memEvalExpr (.var "r") ρ m π = .ok (.u64 rB) :=
    (memEvalExpr_var _ _ _ _).trans hrVar
  have hgetR : la[rB.toNat]? = some y := by rw [hrN]; exact hy
  have hsub : evalExpr (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64)))) ρ =
      .ok (.u64 (wB - 1)) :=
    evalExpr_u64_usub wB 1 (.var "w") ρ hwVar
  have hsubN : (wB - 1).toNat = w - 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    have hno' : ¬ BitVec.usubOverflow wB 1 := by
      rw [BitVec.usubOverflow, decide_eq_true_eq, hwN, h1]
      omega
    rw [BitVec.toNat_sub_of_not_usubOverflow hno', hwN, h1]
  have hsubM_ag : memEvalExpr (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64)))) ρ m π =
      evalExpr (.usub (.var "w") (.lit (.u64 (1 : BitVec 64)))) ρ :=
    memEvalExpr_usub_agree (.var "w") (.lit (.u64 (1 : BitVec 64)))
      ρ m π (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)
  have hgetP : lo[(wB - 1).toNat]? = some p := by
    rw [hsubN]; exact hp
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
  have hmemP : memLoad m ao to ((wB - 1).toNat + 1) = .ok p :=
    memLoad_cellsAt m ao to ((wB - 1).toNat + 1) (no :: lo) p
      hmem_o (by rw [List.getElem?_cons_succ]; exact hgetP)
  have hatP : evalExpr vecUniqueCopyPrev ρ = .ok (.i32 p) := by
    show evalExpr (.stdVecAt "out" (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64))))) ρ = _
    exact evalExpr_stdVecAt_some _ _ _ _ _ _ hout hsub hgetP
  have hatPM_ag : memEvalExpr vecUniqueCopyPrev ρ m π =
      evalExpr vecUniqueCopyPrev ρ := by
    show memEvalExpr (.stdVecAt "out" (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64))))) ρ m π = _
    exact memEvalExpr_stdVecAt_hit "out" (.usub (.var "w")
      (.lit (.u64 (1 : BitVec 64)))) ρ m π lo (wB - 1) p ao to
      hlay_o hout hsubM_ag hsub hmemP hgetP
  have hatPM : memEvalExpr vecUniqueCopyPrev ρ m π =
      .ok (.i32 p) := by rw [hatPM_ag]; exact hatP
  have huneV : evalExpr
      (.une (.stdVecAt "a" (.var "r")) vecUniqueCopyPrev) ρ =
      .ok (.b false) := by
    have h := evalExpr_une_i32 (.stdVecAt "a" (.var "r"))
      vecUniqueCopyPrev ρ y p hat hatP
    rwa [hdrop] at h
  have huneM : memEvalExpr
      (.une (.stdVecAt "a" (.var "r")) vecUniqueCopyPrev) ρ m π =
      .ok (.b false) :=
    (memEvalExpr_une_agree (.stdVecAt "a" (.var "r"))
      vecUniqueCopyPrev ρ m π hatM_ag hatPM_ag).trans huneV
  have hskipV : memEvalProgStmt prog F .skip ρ m π =
      .ok ((ρ, m, π), .fellThrough) := by
    simpa [memEvalProgStmt] using
      (show memEvalStmtFuel F .skip ρ m π =
        .ok ((ρ, m, π), .fellThrough) by
        cases F <;> simp [memEvalStmtFuel, memEvalStmtZero,
          memEvalStmtWith])
  have hif : memEvalProgStmt prog F
      (.if_ (.une (.stdVecAt "a" (.var "r")) vecUniqueCopyPrev)
        (.if_ (.ult (.var "w") (.stdVecLen "out"))
          (.seq (.vecSet "out" (.var "w")
                  (.stdVecAt "a" (.var "r")))
            (.assign "w" (.uadd (.var "w")
              (.lit (.u64 (BitVec.ofNat 64 1))))))
          .fail)
        .skip) ρ m π = .ok ((ρ, m, π), .fellThrough) :=
    (memEvalProgStmt_if_false prog F _ _ _ _ _ _ huneM).trans hskipV
  have hevR : evalExpr (.uadd (.var "r")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρ =
      .ok (.u64 (rB + 1)) := by
    have hrVar' := hrVar
    exact evalExpr_uadd_u64 _ _ _ _ _
      hrVar' (by simp [evalExpr, litVal])
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
  have hrN' : (rB + 1).toNat = r + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hrN]
    exact Nat.mod_eq_of_lt (by omega)
  have hr' : envLookup ρ' "r" = some (.u64 (rB + 1)) :=
    envLookup_update_hit _ _ _ _ hu
  have hbody : vecUniqueCopyBody =
      (.seq (.if_ (.une (.stdVecAt "a" (.var "r")) vecUniqueCopyPrev)
          (.if_ (.ult (.var "w") (.stdVecLen "out"))
            (.seq (.vecSet "out" (.var "w")
                    (.stdVecAt "a" (.var "r")))
              (.assign "w" (.uadd (.var "w")
                (.lit (.u64 (BitVec.ofNat 64 1))))))
            .fail)
          .skip)
        (.assign "r" (.uadd (.var "r")
          (.lit (.u64 (BitVec.ofNat 64 1)))))) := rfl
  have heval : memEvalProgStmt prog F vecUniqueCopyBody ρ m π =
      .ok ((ρ', m, π), .fellThrough) := by
    rw [hbody,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hif,
      hstep_r]
  exact ⟨ρ', m, heval, ha', hout', ⟨(rB + 1), hr', hrN'⟩,
    ⟨wB, hw', hwN⟩, hmem_o, hmem_a⟩

/-! ## Memory loop (bridges `memEvalProgStmt` to `uniqueCopyFwd`) -/

/-- Memory loop, ok leg: the scan runs to `la.length` and the
    record is the forward-model result (fuel induction threading
    the body hits in lockstep; the squeezed-prefix invariant
    plus `1 ≤ w` justifies every predecessor read, and the
    short-`out` leg is vacuous against the `ok` forward
    equation). -/
theorem memUniqueCopyLoop_ok (prog : Prog) (F G : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la : List (BitVec 32)) (lo : List (BitVec 32))
    (r w : Nat) (rB wB : BitVec 64)
    (lo' : List (BitVec 32)) (r' w' : Nat)
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
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hle : r ≤ la.length) (hwle : w ≤ r) (hw1 : 1 ≤ w)
    (hwlo : w ≤ lo.length)
    (hpre : lo.take w = dedupAdj (la.take r))
    (hF : la.length - r ≤ F) (hG : la.length - r ≤ G)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hreadLo : ∀ p, p < lo.length → ∃ y, lo[p]? = some y)
    (hfwd : uniqueCopyFwd la lo G r w = .ok (r', w', lo')) :
    ∃ ρ' m', memEvalProgStmt prog F vecUniqueCopyLoop ρ m π =
      .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "out" = some (.stdVecVal lo') ∧
      (∃ rB', envLookup ρ' "r" = some (.u64 rB') ∧ rB'.toNat = r') ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w') ∧
      memFind m' ao = some ⟨to, true, no :: lo'⟩ ∧
      memFind m' aa = some ⟨ta, true, na :: la⟩ := by
  induction F generalizing G ρ m lo r w rB wB with
  | zero =>
    have him : r = la.length := by omega
    have hlenN : (BitVec.ofNat 64 la.length).toNat = la.length := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
    have hguardF : memEvalExpr (.ult (.var "r") (.stdVecLen "a"))
        ρ m π = .ok (.b false) := by
      have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "a") ρ rB
        (BitVec.ofNat 64 la.length)
        (evalExpr_var_hit _ _ _ hr)
        (evalExpr_stdVecLen_some _ _ _ ha)
      have hfb : (rB.ult (BitVec.ofNat 64 la.length)) = false := by
        rw [BitVec.ult_eq_decide]
        exact decide_eq_false (by omega)
      have hultF : evalExpr (.ult (.var "r") (.stdVecLen "a")) ρ =
          .ok (.b false) := by
        rwa [hfb] at hult
      have hag := memEvalExpr_ult_agree (.var "r")
        (.stdVecLen "a") ρ m π (memEvalExpr_var _ _ _ _)
        (memEvalExpr_stdVecLen_hit "a" ρ m π la aa ta
          hlay_a ha
          (by
            rw [← hna]
            exact memLoad_cellsAt m aa ta 0 (na :: la) na hmem_a
              (by simp)))
      rw [hag]; exact hultF
    have hexit : memEvalProgStmt prog 0 vecUniqueCopyLoop ρ m π =
        .ok ((ρ, m, π), .fellThrough) :=
      memEvalProgStmt_while_false prog 0 _ _ _ _ _ hguardF
    have hpair : (r, w, lo) = (r', w', lo') := by
      cases G with
      | zero => simpa [uniqueCopyFwd] using hfwd
      | succ G =>
        have hneg : ¬ r < la.length := by omega
        simpa [uniqueCopyFwd, dite_eq_right hneg] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    exact ⟨ρ, m, hexit, ha, hout, ⟨rB, hr, hrN⟩, ⟨wB, hw, hwN⟩,
      hmem_o, hmem_a⟩
  | succ F ih =>
    by_cases hlt : r < la.length
    · have hlenN : (BitVec.ofNat 64 la.length).toNat = la.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
      have hguardT : memEvalExpr (.ult (.var "r") (.stdVecLen "a"))
          ρ m π = .ok (.b true) := by
        have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "a") ρ rB
          (BitVec.ofNat 64 la.length)
          (evalExpr_var_hit _ _ _ hr)
          (evalExpr_stdVecLen_some _ _ _ ha)
        have htb : (rB.ult (BitVec.ofNat 64 la.length)) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true (by omega)
        have hultT : evalExpr (.ult (.var "r") (.stdVecLen "a")) ρ =
            .ok (.b true) := by
          rwa [htb] at hult
        have hag := memEvalExpr_ult_agree (.var "r")
          (.stdVecLen "a") ρ m π (memEvalExpr_var _ _ _ _)
          (memEvalExpr_stdVecLen_hit "a" ρ m π la aa ta
            hlay_a ha
            (by
              rw [← hna]
              exact memLoad_cellsAt m aa ta 0 (na :: la) na hmem_a
                (by simp)))
        rw [hag]; exact hultT
      obtain ⟨y, hy⟩ := hread r hlt
      have hw1m : w - 1 < lo.length := by omega
      obtain ⟨p, hpred⟩ := hreadLo (w - 1) hw1m
      have hlast : (dedupAdj (la.take r)).getLast? = some p := by
        rw [← hpre]
        exact take_getLast_of_getElem? lo w p hw1 hwlo hpred
      cir_fuel_step (F, G, la.length - (r + 1))
      by_cases hkeep : (y != p) = true
      · by_cases hmiss : lo[w]? = none
        · have hcon := hfwd
          simp only [uniqueCopyFwd, dite_eq_left hlt, hy, hpred,
            hkeep, hmiss] at hcon
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
              = dedupAdj (la.take (r + 1)) := by
            rw [htake_set, hpre,
              dedupAdj_take_succ_keep la r y p hy hlast hkeep]
          have hlo64' : (lo.set w y).length < 2 ^ 64 := by
            have hlen : (lo.set w y).length = lo.length := by
              simp [List.length_set]
            rw [hlen]; exact hlo64
          have hwlo' : w + 1 ≤ (lo.set w y).length := by
            have hlen : (lo.set w y).length = lo.length := by
              simp [List.length_set]
            omega
          have hreadLo' : ∀ p, p < (lo.set w y).length →
              ∃ z, ((lo.set w y)[p]? = some z) := by
            intro p hp
            have hplen : p < lo.length := by
              have hlen : (lo.set w y).length = lo.length := by
                simp [List.length_set]
              omega
            by_cases hpw : p = w
            · rw [hpw]
              exact ⟨y, List.getElem?_set_self hwlt⟩
            · obtain ⟨z, hz⟩ := hreadLo p hplen
              exact ⟨z, by
                rw [List.getElem?_set_ne (show w ≠ p by omega)]
                exact hz⟩
          have hF'' : la.length - (r + 1) ≤ F := by omega
          have hG'' : la.length - (r + 1) ≤ G' := by omega
          have hfwd' : uniqueCopyFwd la (lo.set w y) G' (r + 1)
              (w + 1) = .ok (r', w', lo') := by
            have h := hfwd
            simp only [uniqueCopyFwd, dite_eq_left hlt, hy, hpred,
              hkeep, hwget] at h
            exact h
          obtain ⟨ρ₁, m₁, hbody, ha₁, hout₁, ⟨rB₁, hrB₁, hrN₁⟩,
              ⟨wB₁, hwB₁, hwN₁⟩, hmem₁, hmem_a₁⟩ :=
            memUniqueCopyBody_keep prog F ρ m π la lo r w rB wB
              y p wOld aa ao ta to na no hlay_a hlay_o hmem_a
              hmem_o hna hno haa hrN hwN hla64 hlo64 ha hout hr
              hw hlt hw1 hy hpred hwget hwlt hkeep
          obtain ⟨ρ', m', hloop, ha', hout', ⟨rB', hrB', hrN'⟩,
              ⟨wB', hwB', hwN'⟩, hmem', hmem_a'⟩ :=
            ih (G := G') (ρ := ρ₁) (m := m₁) (lo := lo.set w y)
              (r := r + 1) (w := w + 1) (rB := rB₁) (wB := wB₁)
              (hrN := hrN₁) (hwN := hwN₁)
              (hlo64 := hlo64')
              (ha := ha₁) (hout := hout₁)
              (hr := hrB₁) (hw := hwB₁)
              (hle := by omega) (hwle := by omega) (hw1 := by omega)
              (hwlo := hwlo') (hpre := hpre')
              (hF := hF'') (hG := hG'')
              (hreadLo := hreadLo')
              (hfwd := hfwd')
              (hmem_a := hmem_a₁) (hmem_o := hmem₁)
              (hno := by
                have hlen : (lo.set w y).length = lo.length := by
                  simp [List.length_set]
                rw [hlen]; exact hno)
          refine ⟨ρ', m', ?_, ha', hout', ⟨rB', hrB', hrN'⟩,
            ⟨wB', hwB', hwN'⟩, hmem', hmem_a'⟩
          have hwhile : memEvalProgStmt prog (F + 1)
              vecUniqueCopyLoop ρ m π =
              memEvalProgStmt prog F vecUniqueCopyLoop ρ₁ m₁ π := by
            cir_unfold_prog (vecUniqueCopyLoop, prog, F, hguardT, hbody)
          rw [hwhile]
          exact hloop
      · have hdrop : (y != p) = false := by
          cases h : (y != p) with
          | true => exact absurd h hkeep
          | false => rfl
        have hpre' : lo.take w = dedupAdj (la.take (r + 1)) := by
          rw [dedupAdj_take_succ_drop la r y p hy hlast hdrop, hpre]
        have hF' : la.length - (r + 1) ≤ F := by omega
        have hG' : la.length - (r + 1) ≤ G' := by omega
        have hfwd' : uniqueCopyFwd la lo G' (r + 1) w =
            .ok (r', w', lo') := by
          have h := hfwd
          simp only [uniqueCopyFwd, dite_eq_left hlt, hy, hpred,
            hdrop] at h
          exact h
        obtain ⟨ρ₁, m₁, hbody, ha₁, hout₁, ⟨rB₁, hrB₁, hrN₁⟩,
            ⟨wB₁, hwB₁, hwN₁⟩, hmem₁, hmem_a₁⟩ :=
          memUniqueCopyBody_drop prog F ρ m π la lo r w rB wB y p
            aa ao ta to na no hlay_a hlay_o hmem_a hmem_o hrN hwN
            hla64 ha hout hr hw hlt hw1 hy hpred hdrop
        obtain ⟨ρ', m', hloop, ha', hout', ⟨rB', hrB', hrN'⟩,
            ⟨wB', hwB', hwN'⟩, hmem', hmem_a'⟩ :=
          ih (G := G') (ρ := ρ₁) (m := m₁) (lo := lo)
            (r := r + 1) (w := w) (rB := rB₁) (wB := wB₁)
            (hrN := hrN₁) (hwN := hwN₁)
            (hlo64 := hlo64)
            (ha := ha₁) (hout := hout₁)
            (hr := hrB₁) (hw := hwB₁)
            (hle := by omega) (hwle := by omega) (hw1 := hw1)
            (hwlo := hwlo) (hpre := hpre')
            (hF := hF') (hG := hG')
            (hreadLo := hreadLo)
            (hfwd := hfwd')
            (hmem_a := hmem_a₁) (hmem_o := hmem₁)
            (hno := hno)
        refine ⟨ρ', m', ?_, ha', hout', ⟨rB', hrB', hrN'⟩,
          ⟨wB', hwB', hwN'⟩, hmem', hmem_a'⟩
        have hwhile : memEvalProgStmt prog (F + 1)
            vecUniqueCopyLoop ρ m π =
            memEvalProgStmt prog F vecUniqueCopyLoop ρ₁ m₁ π := by
          cir_unfold_prog (vecUniqueCopyLoop, prog, F, hguardT, hbody)
        rw [hwhile]
        exact hloop
    · have him : r = la.length := by omega
      subst him
      have hlenN : (BitVec.ofNat 64 la.length).toNat = la.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
      have hguardF : memEvalExpr (.ult (.var "r") (.stdVecLen "a"))
          ρ m π = .ok (.b false) := by
        have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "a") ρ rB
          (BitVec.ofNat 64 la.length)
          (evalExpr_var_hit _ _ _ hr)
          (evalExpr_stdVecLen_some _ _ _ ha)
        have hfb : (rB.ult (BitVec.ofNat 64 la.length)) = false := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_false (by omega)
        have hultF : evalExpr (.ult (.var "r") (.stdVecLen "a")) ρ =
            .ok (.b false) := by
          rwa [hfb] at hult
        have hag := memEvalExpr_ult_agree (.var "r")
          (.stdVecLen "a") ρ m π (memEvalExpr_var _ _ _ _)
          (memEvalExpr_stdVecLen_hit "a" ρ m π la aa ta
            hlay_a ha
            (by
              rw [← hna]
              exact memLoad_cellsAt m aa ta 0 (na :: la) na hmem_a
                (by simp)))
        rw [hag]; exact hultF
      have hexit : memEvalProgStmt prog (F + 1) vecUniqueCopyLoop
          ρ m π = .ok ((ρ, m, π), .fellThrough) :=
        memEvalProgStmt_while_false prog (F + 1) _ _ _ _ _ hguardF
      have hpair : (la.length, w, lo) = (r', w', lo') := by
        cases G with
        | zero => simpa [uniqueCopyFwd] using hfwd
        | succ G =>
          have hneg : ¬ la.length < la.length := by omega
          simpa [uniqueCopyFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      exact ⟨ρ, m, hexit, ha, hout, ⟨rB, hr, hrN⟩, ⟨wB, hw, hwN⟩,
        hmem_o, hmem_a⟩

/-- Memory loop, short-`out` error leg: the first overflowing
    keep aborts loudly (fuel induction; the forward equation
    threads). -/
theorem memUniqueCopyLoop_err (prog : Prog) (F G : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la : List (BitVec 32)) (lo : List (BitVec 32))
    (r w : Nat) (rB wB : BitVec 64)
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
    (hr : envLookup ρ "r" = some (.u64 rB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hle : r ≤ la.length) (hw1 : 1 ≤ w) (hwlo : w ≤ lo.length)
    (hF : la.length - r ≤ F) (hG : la.length - r ≤ G)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hreadLo : ∀ p, p < lo.length → ∃ y, lo[p]? = some y)
    (hfwd : uniqueCopyFwd la lo G r w = .error .AssertFail) :
    memEvalProgStmt prog F vecUniqueCopyLoop ρ m π =
      .error .AssertFail := by
  induction F generalizing G ρ m lo r w rB wB with
  | zero =>
    have him : r = la.length := by omega
    subst him
    cases G with
    | zero => exact absurd hfwd (by simp [uniqueCopyFwd])
    | succ _ =>
      have hneg : ¬ la.length < la.length := by omega
      have hcon := hfwd
      simp only [uniqueCopyFwd, dite_eq_right hneg] at hcon
      exact absurd hcon (by simp)
  | succ F ih =>
    by_cases hlt : r < la.length
    · have hlenN : (BitVec.ofNat 64 la.length).toNat = la.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
      have hguardT : memEvalExpr (.ult (.var "r") (.stdVecLen "a"))
          ρ m π = .ok (.b true) := by
        have hult := evalExpr_ult_u64 (.var "r") (.stdVecLen "a") ρ rB
          (BitVec.ofNat 64 la.length)
          (evalExpr_var_hit _ _ _ hr)
          (evalExpr_stdVecLen_some _ _ _ ha)
        have htb : (rB.ult (BitVec.ofNat 64 la.length)) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true (by omega)
        have hultT : evalExpr (.ult (.var "r") (.stdVecLen "a")) ρ =
            .ok (.b true) := by
          rwa [htb] at hult
        have hag := memEvalExpr_ult_agree (.var "r")
          (.stdVecLen "a") ρ m π (memEvalExpr_var _ _ _ _)
          (memEvalExpr_stdVecLen_hit "a" ρ m π la aa ta
            hlay_a ha
            (by
              rw [← hna]
              exact memLoad_cellsAt m aa ta 0 (na :: la) na hmem_a
                (by simp)))
        rw [hag]; exact hultT
      obtain ⟨y, hy⟩ := hread r hlt
      have hw1m : w - 1 < lo.length := by omega
      obtain ⟨p, hpred⟩ := hreadLo (w - 1) hw1m
      cir_fuel_step (F, G, la.length - (r + 1))
      by_cases hkeep : (y != p) = true
      · by_cases hmiss : lo[w]? = none
        · have hshort := memUniqueCopyBody_short prog F ρ m π
            la lo r w rB wB y p aa ao ta to na no hlay_a
            hlay_o hmem_a hmem_o hno hlo64 ha hout hr hw hrN hwN
            hlt hw1 hy hpred hmiss hkeep
          have hwhile : memEvalProgStmt prog (F + 1)
              vecUniqueCopyLoop ρ m π = .error .AssertFail := by
            have hloop : vecUniqueCopyLoop =
                (.while_ (.ult (.var "r") (.stdVecLen "a"))
                  vecUniqueCopyBody) := rfl
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
          have hF'' : la.length - (r + 1) ≤ F := by omega
          have hG'' : la.length - (r + 1) ≤ G' := by omega
          have hlo64' : (lo.set w y).length < 2 ^ 64 := by
            have hlen : (lo.set w y).length = lo.length := by
              simp [List.length_set]
            rw [hlen]; exact hlo64
          have hreadLo' : ∀ p, p < (lo.set w y).length →
              ∃ z, ((lo.set w y)[p]? = some z) := by
            intro p hp
            have hplen : p < lo.length := by
              have hlen : (lo.set w y).length = lo.length := by
                simp [List.length_set]
              omega
            by_cases hpw : p = w
            · rw [hpw]
              exact ⟨y, List.getElem?_set_self hwlt⟩
            · obtain ⟨z, hz⟩ := hreadLo p hplen
              exact ⟨z, by
                rw [List.getElem?_set_ne (show w ≠ p by omega)]
                exact hz⟩
          have hfwd' : uniqueCopyFwd la (lo.set w y) G' (r + 1)
              (w + 1) = .error .AssertFail := by
            have h := hfwd
            simp only [uniqueCopyFwd, dite_eq_left hlt, hy, hpred,
              hkeep, hwget] at h
            exact h
          obtain ⟨ρ₁, m₁, hbody, ha₁, hout₁, ⟨rB₁, hrB₁, hrN₁⟩,
              ⟨wB₁, hwB₁, hwN₁⟩, hmem₁, hmem_a₁⟩ :=
            memUniqueCopyBody_keep prog F ρ m π la lo r w rB wB
              y p wOld aa ao ta to na no hlay_a hlay_o hmem_a
              hmem_o hna hno haa hrN hwN hla64 hlo64 ha hout hr
              hw hlt hw1 hy hpred hwget hwlt hkeep
          have hloop : memEvalProgStmt prog F vecUniqueCopyLoop
              ρ₁ m₁ π = .error .AssertFail :=
            ih (G := G') (ρ := ρ₁) (m := m₁) (lo := lo.set w y)
              (r := r + 1) (w := w + 1) (rB := rB₁) (wB := wB₁)
              (hrN := hrN₁) (hwN := hwN₁)
              (hlo64 := hlo64')
              (ha := ha₁) (hout := hout₁)
              (hr := hrB₁) (hw := hwB₁)
              (hle := by omega) (hw1 := by omega)
              (hwlo := by
                have hlen : (lo.set w y).length = lo.length := by
                  simp [List.length_set]
                omega)
              (hF := hF'') (hG := hG'')
              (hreadLo := hreadLo')
              (hfwd := hfwd')
              (hmem_a := hmem_a₁) (hmem_o := hmem₁)
              (hno := by
                have hlen : (lo.set w y).length = lo.length := by
                  simp [List.length_set]
                rw [hlen]; exact hno)
          have hwhile : memEvalProgStmt prog (F + 1)
              vecUniqueCopyLoop ρ m π = .error .AssertFail := by
            cir_unfold_prog (vecUniqueCopyLoop, prog, F, hguardT, hbody)
            exact hloop
          exact hwhile
      · have hdrop : (y != p) = false := by
          cases h : (y != p) with
          | true => exact absurd h hkeep
          | false => rfl
        have hF' : la.length - (r + 1) ≤ F := by omega
        have hG' : la.length - (r + 1) ≤ G' := by omega
        have hfwd' : uniqueCopyFwd la lo G' (r + 1) w =
            .error .AssertFail := by
          have h := hfwd
          simp only [uniqueCopyFwd, dite_eq_left hlt, hy, hpred,
            hdrop] at h
          exact h
        obtain ⟨ρ₁, m₁, hbody, ha₁, hout₁, ⟨rB₁, hrB₁, hrN₁⟩,
            ⟨wB₁, hwB₁, hwN₁⟩, hmem₁, hmem_a₁⟩ :=
          memUniqueCopyBody_drop prog F ρ m π la lo r w rB wB y p
            aa ao ta to na no hlay_a hlay_o hmem_a hmem_o hrN hwN
            hla64 ha hout hr hw hlt hw1 hy hpred hdrop
        have hloop : memEvalProgStmt prog F vecUniqueCopyLoop ρ₁ m₁ π =
            .error .AssertFail :=
          ih (G := G') (ρ := ρ₁) (m := m₁) (lo := lo)
            (r := r + 1) (w := w) (rB := rB₁) (wB := wB₁)
            (hrN := hrN₁) (hwN := hwN₁)
            (hlo64 := hlo64)
            (ha := ha₁) (hout := hout₁)
            (hr := hrB₁) (hw := hwB₁)
            (hle := by omega) (hw1 := hw1)
            (hwlo := hwlo)
            (hF := hF') (hG := hG')
            (hreadLo := hreadLo)
            (hfwd := hfwd')
            (hmem_a := hmem_a₁) (hmem_o := hmem₁)
            (hno := hno)
        have hwhile : memEvalProgStmt prog (F + 1)
            vecUniqueCopyLoop ρ m π = .error .AssertFail := by
          cir_unfold_prog (vecUniqueCopyLoop, prog, F, hguardT, hbody)
          exact hloop
        exact hwhile
    · have him : r = la.length := by omega
      subst him
      cases G with
      | zero => exact absurd hfwd (by simp [uniqueCopyFwd])
      | succ _ =>
        have hneg : ¬ la.length < la.length := by omega
        have hcon := hfwd
        simp only [uniqueCopyFwd, dite_eq_right hneg] at hcon
        exact absurd hcon (by simp)
/-! ## Value entries -/

/-- Value nil: the empty input exits early with `0` (the
    entry guard agrees with the forward equation). -/
theorem evalProgFunc_vecUniqueCopy_nil (F : Nat)
    (lo : List (BitVec 32)) :
    evalProgFunc vecUniqueCopyProg F vecUniqueCopyFunc
      [.stdVecVal ([] : List (BitVec 32)),
        .stdVecVal lo] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
  have hbind : bindArgs vecUniqueCopyFunc.args
      [.stdVecVal ([] : List (BitVec 32)),
        .stdVecVal lo] =
      some [("a", .stdVecVal ([] : List (BitVec 32))),
        ("out", .stdVecVal lo)] := rfl
  have hbody : vecUniqueCopyFunc.body =
      (.seq (.if_ (.ueq (.stdVecLen "a")
                  (.lit (.u64 (BitVec.ofNat 64 0))))
            (.return_ (.lit (.u64 (BitVec.ofNat 64 0))))
            .skip)
        (.seq vecUniqueCopySeed
          (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
            (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
              (.seq vecUniqueCopyLoop
                (.return_ (.var "w"))))))) := rfl
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
  have hif := evalProgStmt_if_true vecUniqueCopyProg F
    (.ueq (.stdVecLen "a") (.lit (.u64 (BitVec.ofNat 64 0))))
    (.return_ (.lit (.u64 (BitVec.ofNat 64 0)))) .skip
    [("a", .stdVecVal ([] : List (BitVec 32))),
      ("out", .stdVecVal lo)] hguardT
  have hret := evalProgStmt_return vecUniqueCopyProg F
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("a", .stdVecVal ([] : List (BitVec 32))),
      ("out", .stdVecVal lo)]
    (.u64 (BitVec.ofNat 64 0)) hlitV
  simp only [evalProgFunc, hbind, hbody]
  rw [evalProgStmt_seq_returned _ _ _ _ _ _ _ (hif.trans hret)]

/-- Value entry, seed-short leg: a nonempty input with an
    empty record fails loud at the seed store (the loop is
    unreachable). -/
theorem evalProgFunc_vecUniqueCopy_seedShort (F : Nat)
    (la lo : List (BitVec 32)) (a0 : BitVec 32)
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (ha0 : la[0]? = some a0) (hmiss : lo[0]? = none) :
    evalProgFunc vecUniqueCopyProg F vecUniqueCopyFunc
      [.stdVecVal la, .stdVecVal lo] =
      .error .AssertFail := by
  have hbind : bindArgs vecUniqueCopyFunc.args
      [.stdVecVal la, .stdVecVal lo] =
      some [("a", .stdVecVal la), ("out", .stdVecVal lo)] := rfl
  have hbody : vecUniqueCopyFunc.body =
      (.seq (.if_ (.ueq (.stdVecLen "a")
                  (.lit (.u64 (BitVec.ofNat 64 0))))
            (.return_ (.lit (.u64 (BitVec.ofNat 64 0))))
            .skip)
        (.seq vecUniqueCopySeed
          (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
            (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
              (.seq vecUniqueCopyLoop
                (.return_ (.var "w"))))))) := rfl
  have ha₂ : envLookup [("a", .stdVecVal la),
      ("out", .stdVecVal lo)] "a" =
      some (.stdVecVal la) := by simp [envLookup]
  have hlenV : evalExpr (.stdVecLen "a")
      [("a", .stdVecVal la), ("out", .stdVecVal lo)] =
      .ok (.u64 (BitVec.ofNat 64 la.length)) :=
    evalExpr_stdVecLen_some _ _ _ ha₂
  have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal la), ("out", .stdVecVal lo)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hlenN : (BitVec.ofNat 64 la.length).toNat = la.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
  have hpos : 0 < la.length := by
    have hne : la ≠ [] := by
      intro hnil
      rw [hnil] at ha0
      simp at ha0
    exact List.length_pos_iff.mpr hne
  have hnn : BitVec.ofNat 64 la.length ≠ BitVec.ofNat 64 0 := by
    intro hcon
    have h0 := congrArg BitVec.toNat hcon
    rw [hlenN] at h0
    have hnil : la = [] := List.length_eq_zero_iff.mp h0
    rw [hnil] at ha0
    simp at ha0
  have hbeq : (BitVec.ofNat 64 la.length ==
      BitVec.ofNat 64 0) = false :=
    beq_eq_false_iff_ne.mpr hnn
  have hguardF : evalExpr (.ueq (.stdVecLen "a")
      (.lit (.u64 (BitVec.ofNat 64 0))))
      [("a", .stdVecVal la), ("out", .stdVecVal lo)] =
      .ok (.b false) := by
    have h := evalExpr_ueq_u64_vars (.stdVecLen "a")
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal la), ("out", .stdVecVal lo)]
      (BitVec.ofNat 64 la.length)
      (BitVec.ofNat 64 0) hlenV hlitV
    rwa [hbeq] at h
  have hout₂ : envLookup [("a", .stdVecVal la),
      ("out", .stdVecVal lo)] "out" =
      some (.stdVecVal lo) := by
    simp [envLookup, show ("out" : String) ≠ "a" by decide]
  have hif := evalProgStmt_if_false vecUniqueCopyProg F
    (.ueq (.stdVecLen "a") (.lit (.u64 (BitVec.ofNat 64 0))))
    (.return_ (.lit (.u64 (BitVec.ofNat 64 0)))) .skip
    [("a", .stdVecVal la), ("out", .stdVecVal lo)] hguardF
  have hskipV : evalProgStmt vecUniqueCopyProg F .skip
      [("a", .stdVecVal la), ("out", .stdVecVal lo)] =
      .ok ([("a", .stdVecVal la), ("out", .stdVecVal lo)],
        .fellThrough) := by
    simpa [evalProgStmt] using
      (show evalStmtFuel F .skip [("a", .stdVecVal la),
          ("out", .stdVecVal lo)] =
        .ok ([("a", .stdVecVal la), ("out", .stdVecVal lo)],
          .fellThrough) by
        cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith])
  have hfall : evalProgStmt vecUniqueCopyProg F
      (.if_ (.ueq (.stdVecLen "a")
              (.lit (.u64 (BitVec.ofNat 64 0))))
        (.return_ (.lit (.u64 (BitVec.ofNat 64 0)))) .skip)
      [("a", .stdVecVal la), ("out", .stdVecVal lo)] =
      .ok ([("a", .stdVecVal la), ("out", .stdVecVal lo)],
        .fellThrough) :=
    hif.trans hskipV
  have hseed := valUniqueCopySeed_short vecUniqueCopyProg F
    [("a", .stdVecVal la), ("out", .stdVecVal lo)] la lo a0
    hlo64 ha₂ hout₂ ha0 hmiss
  simp only [evalProgFunc, hbind, hbody]
  rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hfall,
    evalProgStmt_seq_err _ _ _ _ _ _ hseed]

/-- Value entry, ok leg: a nonempty input with a fitting
    record runs the seed store, the `(1, 1)` prelude, the
    loop, and returns the survivor count. -/
theorem evalProgFunc_vecUniqueCopy_ok (F : Nat)
    (la lo : List (BitVec 32)) (a0 : BitVec 32)
    (w' : Nat) (lo' : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length + 1 ≤ F)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hcap : (dedupAdj la).length ≤ lo.length)
    (ha0 : la[0]? = some a0)
    (hfwd : uniqueCopyFwd la (lo.set 0 a0)
      la.length 1 1 = .ok (la.length, w', lo')) :
    evalProgFunc vecUniqueCopyProg F vecUniqueCopyFunc
      [.stdVecVal la, .stdVecVal lo] =
      .ok (.u64 (BitVec.ofNat 64 w')) := by
  have hbind : bindArgs vecUniqueCopyFunc.args
      [.stdVecVal la, .stdVecVal lo] =
      some [("a", .stdVecVal la), ("out", .stdVecVal lo)] := rfl
  have hbody : vecUniqueCopyFunc.body =
      (.seq (.if_ (.ueq (.stdVecLen "a")
                  (.lit (.u64 (BitVec.ofNat 64 0))))
            (.return_ (.lit (.u64 (BitVec.ofNat 64 0))))
            .skip)
        (.seq vecUniqueCopySeed
          (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
            (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
              (.seq vecUniqueCopyLoop
                (.return_ (.var "w"))))))) := rfl
  cases hla : la with
  | nil =>
    subst hla
    simp at ha0
  | cons b0 xs =>
    subst hla
    have hlen1 : 1 ≤ (b0 :: xs).length := by simp
    have hcap1 : 0 < lo.length := by
      have hnn := dedupAdj_nonempty (show (b0 :: xs) ≠ [] by simp)
      have hpos : 0 < (dedupAdj (b0 :: xs)).length :=
        List.length_pos_iff.mpr hnn
      omega
    have h0lt : 0 < lo.length := hcap1
    have hab : a0 = b0 := by
      have hb0 : (b0 :: xs)[0]? = some b0 := by simp
      exact Option.some.inj (ha0.symm.trans hb0)
    subst b0
    obtain ⟨o0, ho0⟩ : ∃ z, lo[0]? = some z :=
      ⟨lo[0], List.getElem?_eq_getElem h0lt⟩
    have hreadLo₀ : ∀ p, p < lo.length → ∃ y, lo[p]? = some y := by
      intro p hp
      exact ⟨lo[p], List.getElem?_eq_getElem hp⟩
    have ha₂ : envLookup [("a", .stdVecVal (a0 :: xs)),
        ("out", .stdVecVal lo)] "a" =
        some (.stdVecVal (a0 :: xs)) := by simp [envLookup]
    have hout₂ : envLookup [("a", .stdVecVal (a0 :: xs)),
        ("out", .stdVecVal lo)] "out" =
        some (.stdVecVal lo) := by
      simp [envLookup, show ("out" : String) ≠ "a" by decide]
    have hlenV : evalExpr (.stdVecLen "a")
        [("a", .stdVecVal (a0 :: xs)), ("out", .stdVecVal lo)] =
        .ok (.u64 (BitVec.ofNat 64 (a0 :: xs).length)) :=
      evalExpr_stdVecLen_some _ _ _ ha₂
    have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (a0 :: xs)), ("out", .stdVecVal lo)] =
        .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
    have hlenN : (BitVec.ofNat 64 (a0 :: xs).length).toNat =
        (a0 :: xs).length := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hla64
    have hnn : BitVec.ofNat 64 (a0 :: xs).length ≠
        BitVec.ofNat 64 0 := by
      intro hcon
      have h0 := congrArg BitVec.toNat hcon
      rw [hlenN] at h0
      simp at h0
    have hbeq : (BitVec.ofNat 64 (a0 :: xs).length ==
        BitVec.ofNat 64 0) = false :=
      beq_eq_false_iff_ne.mpr hnn
    have hguardF : evalExpr (.ueq (.stdVecLen "a")
        (.lit (.u64 (BitVec.ofNat 64 0))))
        [("a", .stdVecVal (a0 :: xs)), ("out", .stdVecVal lo)] =
        .ok (.b false) := by
      have h := evalExpr_ueq_u64_vars (.stdVecLen "a")
        (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (a0 :: xs)), ("out", .stdVecVal lo)]
        (BitVec.ofNat 64 (a0 :: xs).length)
        (BitVec.ofNat 64 0) hlenV hlitV
      rwa [hbeq] at h
    have hif := evalProgStmt_if_false vecUniqueCopyProg F
      (.ueq (.stdVecLen "a") (.lit (.u64 (BitVec.ofNat 64 0))))
      (.return_ (.lit (.u64 (BitVec.ofNat 64 0)))) .skip
      [("a", .stdVecVal (a0 :: xs)), ("out", .stdVecVal lo)] hguardF
    have hskipV : evalProgStmt vecUniqueCopyProg F .skip
        [("a", .stdVecVal (a0 :: xs)), ("out", .stdVecVal lo)] =
        .ok ([("a", .stdVecVal (a0 :: xs)), ("out", .stdVecVal lo)],
          .fellThrough) := by
      simpa [evalProgStmt] using
        (show evalStmtFuel F .skip [("a", .stdVecVal (a0 :: xs)),
            ("out", .stdVecVal lo)] =
          .ok ([("a", .stdVecVal (a0 :: xs)), ("out", .stdVecVal lo)],
            .fellThrough) by
          cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith])
    have hfall : evalProgStmt vecUniqueCopyProg F
        (.if_ (.ueq (.stdVecLen "a")
                (.lit (.u64 (BitVec.ofNat 64 0))))
          (.return_ (.lit (.u64 (BitVec.ofNat 64 0)))) .skip)
        [("a", .stdVecVal (a0 :: xs)), ("out", .stdVecVal lo)] =
        .ok ([("a", .stdVecVal (a0 :: xs)), ("out", .stdVecVal lo)],
          .fellThrough) :=
      hif.trans hskipV
    obtain ⟨ρs, hseed, has, houts⟩ :=
      valUniqueCopySeed_hit vecUniqueCopyProg F
        [("a", .stdVecVal (a0 :: xs)), ("out", .stdVecVal lo)]
        (a0 :: xs) lo a0 o0 hlo64 ha₂ hout₂ ha0 ho0
    have hlitW : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        ρs = .ok (.u64 (BitVec.ofNat 64 1)) := by
      simp [evalExpr, litVal]
    have hletW := revLet vecUniqueCopyProg F "w" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 1))) ρs
      (.u64 (BitVec.ofNat 64 1)) hlitW
    have hlitR : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        (envExtend ρs "w" (.u64 (BitVec.ofNat 64 1))) =
        .ok (.u64 (BitVec.ofNat 64 1)) := by simp [evalExpr, litVal]
    have hletR := revLet vecUniqueCopyProg F "r" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 1)))
      (envExtend ρs "w" (.u64 (BitVec.ofNat 64 1)))
      (.u64 (BitVec.ofNat 64 1)) hlitR
    have h1N : (BitVec.ofNat 64 1).toNat = 1 := by decide
    have ha₁ : envLookup (envExtend (envExtend ρs
        "w" (.u64 (BitVec.ofNat 64 1)))
        "r" (.u64 (BitVec.ofNat 64 1))) "a" =
        some (.stdVecVal (a0 :: xs)) := by
      rw [envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "r" by decide),
        envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "w" by decide)]
      have h := has
      simpa [envExtend, envLookup] using h
    have hout₁ : envLookup (envExtend (envExtend ρs
        "w" (.u64 (BitVec.ofNat 64 1)))
        "r" (.u64 (BitVec.ofNat 64 1))) "out" =
        some (.stdVecVal (lo.set 0 a0)) := by
      rw [envExtend_miss _ _ _ _
        (show ("out" : String) ≠ "r" by decide),
        envExtend_miss _ _ _ _
        (show ("out" : String) ≠ "w" by decide)]
      have h := houts
      simpa [envExtend, envLookup] using h
    have hr₁ : envLookup (envExtend (envExtend ρs
        "w" (.u64 (BitVec.ofNat 64 1)))
        "r" (.u64 (BitVec.ofNat 64 1))) "r" =
        some (.u64 (BitVec.ofNat 64 1)) :=
      envExtend_hit _ _ _
    have hw₁ : envLookup (envExtend (envExtend ρs
        "w" (.u64 (BitVec.ofNat 64 1)))
        "r" (.u64 (BitVec.ofNat 64 1))) "w" =
        some (.u64 (BitVec.ofNat 64 1)) := by
      rw [envExtend_miss _ _ _ _
        (show ("w" : String) ≠ "r" by decide)]
      exact envExtend_hit _ _ _
    have hreadLo₁ : ∀ p, p < (lo.set 0 a0).length →
        ∃ y, ((lo.set 0 a0)[p]? = some y) := by
      intro p hp
      have hplen : p < lo.length := by
        have hlenS : (lo.set 0 a0).length = lo.length := by
          simp [List.length_set]
        omega
      obtain ⟨z, hz⟩ := hreadLo₀ p hplen
      by_cases hpw : p = 0
      · rw [hpw]
        exact ⟨a0, List.getElem?_set_self h0lt⟩
      · exact ⟨z, by
          rw [List.getElem?_set_ne (by omega : (0 : Nat) ≠ p)]
          exact hz⟩
    have hpre₁ : (lo.set 0 a0).take 1
        = dedupAdj ((a0 :: xs).take 1) := by
      rw [show (1 : Nat) = 0 + 1 from rfl,
        take_set_succ_self lo 0 a0 h0lt]
      simp [dedupAdj]
    have hwlo₁ : 1 ≤ (lo.set 0 a0).length := by
      have hlenS : (lo.set 0 a0).length = lo.length := by
        simp [List.length_set]
      omega
    have hcapS : (dedupAdj (a0 :: xs)).length ≤
        (lo.set 0 a0).length := by
      have hlenS : (lo.set 0 a0).length = lo.length := by
        simp [List.length_set]
      rw [hlenS]; exact hcap
    obtain ⟨ρ', hloop, ha', hout', ⟨rB', hrB', hrN'⟩,
        ⟨wB', hwB', hwN'⟩⟩ :=
      valUniqueCopyLoop_ok vecUniqueCopyProg F ((a0 :: xs).length)
        (envExtend (envExtend ρs
          "w" (.u64 (BitVec.ofNat 64 1)))
          "r" (.u64 (BitVec.ofNat 64 1)))
        (a0 :: xs) (lo.set 0 a0) 1 1
        (BitVec.ofNat 64 1) (BitVec.ofNat 64 1)
        lo' (a0 :: xs).length w' h1N h1N hla64
        (by simp [List.length_set]; exact hlo64)
        ha₁ hout₁ hr₁ hw₁
        hlen1 (Nat.le_refl _) (Nat.le_refl _)
        hwlo₁
        hpre₁
        (by omega) (by omega)
        hread hreadLo₁
        (by simpa using hfwd)
    have hwEq : wB' = BitVec.ofNat 64 w' := by
      have hb := uniqueCopyFwd_le (a0 :: xs) (lo.set 0 a0)
        ((a0 :: xs).length) 1 1 w' lo' hlen1 (Nat.le_refl _)
        (Nat.le_refl _) (Nat.sub_le _ _) hread hreadLo₁ hpre₁
        (by simp [List.length_set]; omega) hcapS hfwd
      apply BitVec.eq_of_toNat_eq
      rw [hwN', BitVec.toNat_ofNat]
      have hlenS : (lo.set 0 a0).length = lo.length := by
        simp [List.length_set]
      have hw'lt : w' < 2 ^ 64 := by
        have hlo64' : (lo.set 0 a0).length < 2 ^ 64 := by
          rw [hlenS]; exact hlo64
        omega
      exact (Nat.mod_eq_of_lt hw'lt).symm
    have hevW' : evalExpr (.var "w") ρ' =
        .ok (.u64 (BitVec.ofNat 64 w')) := by
      rw [← hwEq]; exact evalExpr_var_hit _ _ _ hwB'
    have hret := evalProgStmt_return vecUniqueCopyProg F
      (.var "w") ρ' (.u64 (BitVec.ofNat 64 w')) hevW'
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hfall,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hseed,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletW,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletR,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hloop,
      hret]

/-- Value entry, err leg: the prelude binds, the loop hits
    the short `out` and fails loud (the `return` is
    unreachable). -/
theorem evalProgFunc_vecUniqueCopy_err (F : Nat)
    (la lo : List (BitVec 32)) (a0 o0 : BitVec 32)
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length + 1 ≤ F)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hreadLo₀ : ∀ p, p < lo.length → ∃ y, lo[p]? = some y)
    (ha0 : la[0]? = some a0) (ho0 : lo[0]? = some o0)
    (hfwd : uniqueCopyFwd la (lo.set 0 a0) la.length 1 1 =
      .error .AssertFail) :
    evalProgFunc vecUniqueCopyProg F vecUniqueCopyFunc
      [.stdVecVal la, .stdVecVal lo] =
      .error .AssertFail := by
  have hbind : bindArgs vecUniqueCopyFunc.args
      [.stdVecVal la, .stdVecVal lo] =
      some [("a", .stdVecVal la), ("out", .stdVecVal lo)] := rfl
  have hbody : vecUniqueCopyFunc.body =
      (.seq (.if_ (.ueq (.stdVecLen "a")
                  (.lit (.u64 (BitVec.ofNat 64 0))))
            (.return_ (.lit (.u64 (BitVec.ofNat 64 0))))
            .skip)
        (.seq vecUniqueCopySeed
          (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
            (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
              (.seq vecUniqueCopyLoop
                (.return_ (.var "w"))))))) := rfl
  cases hla : la with
  | nil =>
    subst hla
    simp at ha0
  | cons b0 ys =>
    subst hla
    have hpos : 0 < (b0 :: ys).length := by simp
    obtain ⟨ρs, hseed, has, houts⟩ :=
      valUniqueCopySeed_hit vecUniqueCopyProg F
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        (b0 :: ys) lo a0 o0 hlo64
        (by simp [envLookup]) (by
          simp [envLookup, show ("out" : String) ≠ "a" by decide])
        (by simpa using ha0) ho0
    have hlitW : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        ρs = .ok (.u64 (BitVec.ofNat 64 1)) := by
      simp [evalExpr, litVal]
    have hletW := revLet vecUniqueCopyProg F "w" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 1))) ρs
      (.u64 (BitVec.ofNat 64 1)) hlitW
    have hlitR : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        (envExtend ρs "w" (.u64 (BitVec.ofNat 64 1))) =
        .ok (.u64 (BitVec.ofNat 64 1)) := by simp [evalExpr, litVal]
    have hletR := revLet vecUniqueCopyProg F "r" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 1)))
      (envExtend ρs "w" (.u64 (BitVec.ofNat 64 1)))
      (.u64 (BitVec.ofNat 64 1)) hlitR
    have h1N : (BitVec.ofNat 64 1).toNat = 1 := by decide
    have ha₁ : envLookup (envExtend (envExtend ρs
        "w" (.u64 (BitVec.ofNat 64 1)))
        "r" (.u64 (BitVec.ofNat 64 1))) "a" =
        some (.stdVecVal (b0 :: ys)) := by
      rw [envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "r" by decide),
        envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "w" by decide)]
      have h := has
      simpa [envExtend, envLookup] using h
    have hout₁ : envLookup (envExtend (envExtend ρs
        "w" (.u64 (BitVec.ofNat 64 1)))
        "r" (.u64 (BitVec.ofNat 64 1))) "out" =
        some (.stdVecVal (lo.set 0 a0)) := by
      rw [envExtend_miss _ _ _ _
        (show ("out" : String) ≠ "r" by decide),
        envExtend_miss _ _ _ _
        (show ("out" : String) ≠ "w" by decide)]
      have h := houts
      simpa [envExtend, envLookup] using h
    have hr₁ : envLookup (envExtend (envExtend ρs
        "w" (.u64 (BitVec.ofNat 64 1)))
        "r" (.u64 (BitVec.ofNat 64 1))) "r" =
        some (.u64 (BitVec.ofNat 64 1)) :=
      envExtend_hit _ _ _
    have hw₁ : envLookup (envExtend (envExtend ρs
        "w" (.u64 (BitVec.ofNat 64 1)))
        "r" (.u64 (BitVec.ofNat 64 1))) "w" =
        some (.u64 (BitVec.ofNat 64 1)) := by
      rw [envExtend_miss _ _ _ _
        (show ("w" : String) ≠ "r" by decide)]
      exact envExtend_hit _ _ _
    have hguardF : evalExpr (.ueq (.stdVecLen "a")
        (.lit (.u64 (BitVec.ofNat 64 0))))
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)] =
        .ok (.b false) := by
      have hlenV : evalExpr (.stdVecLen "a")
          [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)] =
          .ok (.u64 (BitVec.ofNat 64 (b0 :: ys).length)) :=
        evalExpr_stdVecLen_some _ _ _ (by simp [envLookup])
      have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
          [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)] =
          .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
      have hlenN : (BitVec.ofNat 64 (b0 :: ys).length).toNat =
          (b0 :: ys).length := by
        rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt hla64
      have hnn : BitVec.ofNat 64 (b0 :: ys).length ≠
          BitVec.ofNat 64 0 := by
        intro hcon
        have h0 := congrArg BitVec.toNat hcon
        rw [hlenN] at h0
        simp at h0
      have hbeq : (BitVec.ofNat 64 (b0 :: ys).length ==
          BitVec.ofNat 64 0) = false :=
        beq_eq_false_iff_ne.mpr hnn
      have h := evalExpr_ueq_u64_vars (.stdVecLen "a")
        (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)]
        (BitVec.ofNat 64 (b0 :: ys).length)
        (BitVec.ofNat 64 0) hlenV hlitV
      rwa [hbeq] at h
    have hif := evalProgStmt_if_false vecUniqueCopyProg F
      (.ueq (.stdVecLen "a") (.lit (.u64 (BitVec.ofNat 64 0))))
      (.return_ (.lit (.u64 (BitVec.ofNat 64 0)))) .skip
      [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)] hguardF
    have hskipV : evalProgStmt vecUniqueCopyProg F .skip
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)] =
        .ok ([("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)],
          .fellThrough) := by
      simpa [evalProgStmt] using
        (show evalStmtFuel F .skip [("a", .stdVecVal (b0 :: ys)),
            ("out", .stdVecVal lo)] =
          .ok ([("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)],
            .fellThrough) by
          cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith])
    have hfall : evalProgStmt vecUniqueCopyProg F
        (.if_ (.ueq (.stdVecLen "a")
                (.lit (.u64 (BitVec.ofNat 64 0))))
          (.return_ (.lit (.u64 (BitVec.ofNat 64 0)))) .skip)
        [("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)] =
        .ok ([("a", .stdVecVal (b0 :: ys)), ("out", .stdVecVal lo)],
          .fellThrough) :=
      hif.trans hskipV
    have h0lt : 0 < lo.length := by
      have hnil : lo ≠ [] := by
        intro hnil
        rw [hnil] at ho0
        exact absurd ho0 (by simp)
      exact List.length_pos_iff.mpr hnil
    have hreadLo₁ : ∀ p, p < (lo.set 0 a0).length →
        ∃ y, ((lo.set 0 a0)[p]? = some y) := by
      intro p hp
      have hlenS : (lo.set 0 a0).length = lo.length := by
        simp [List.length_set]
      have hplen : p < lo.length := by omega
      obtain ⟨z, hz⟩ := hreadLo₀ p hplen
      by_cases hpw : p = 0
      · rw [hpw]
        exact ⟨a0, List.getElem?_set_self h0lt⟩
      · exact ⟨z, by
          rw [List.getElem?_set_ne (by omega : (0 : Nat) ≠ p)]
          exact hz⟩
    have hlenS : (lo.set 0 a0).length = lo.length := by
      simp [List.length_set]
    have hloop : evalProgStmt vecUniqueCopyProg F vecUniqueCopyLoop
        (envExtend (envExtend ρs
          "w" (.u64 (BitVec.ofNat 64 1)))
          "r" (.u64 (BitVec.ofNat 64 1))) =
        .error .AssertFail :=
      valUniqueCopyLoop_err vecUniqueCopyProg F ((b0 :: ys).length)
        (envExtend (envExtend ρs
          "w" (.u64 (BitVec.ofNat 64 1)))
          "r" (.u64 (BitVec.ofNat 64 1)))
        (b0 :: ys) (lo.set 0 a0) 1 1
        (BitVec.ofNat 64 1) (BitVec.ofNat 64 1)
        h1N h1N hla64
        (by simp [List.length_set]; exact hlo64)
        ha₁ hout₁ hr₁ hw₁
        (by simp) (Nat.le_refl _)
        (by omega) (by omega) (by omega)
        hread hreadLo₁ hfwd
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hfall,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hseed,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletW,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletR,
      evalProgStmt_seq_err _ _ _ _ _ _ hloop]
/-! ## Memory entries -/

/-- Memory nil: the empty input exits early with `0` on the
    memory layer (the entry guard agrees with the value
    guard through `memEvalExpr_ueq_agree`). -/
theorem memEvalProgFunc_vecUniqueCopy_nil (F : Nat)
    (lo : List (BitVec 32)) :
    memEvalProgFunc vecUniqueCopyProg F vecUniqueCopyFunc
      [.stdVecVal ([] : List (BitVec 32)),
        .stdVecVal lo] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
  have hbind := bindMemArgs_vecUniqueCopy [] lo
  have hbody : vecUniqueCopyFunc.body =
      (.seq (.if_ (.ueq (.stdVecLen "a")
                  (.lit (.u64 (BitVec.ofNat 64 0))))
            (.return_ (.lit (.u64 (BitVec.ofNat 64 0))))
            .skip)
        (.seq vecUniqueCopySeed
          (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
            (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
              (.seq vecUniqueCopyLoop
                (.return_ (.var "w"))))))) := rfl
  have hmem_a : memFind
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
          ([] : List (BitVec 32))⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) ::
          lo⟩)], []⟩ 1 =
      some ⟨1, true, (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
        ([] : List (BitVec 32))⟩ :=
    memFind_cons_hit _ _ _ _ _
  have hlay_a : layoutLookup [("a", 1, 1), ("out", 0, 0)] "a" =
      some (1, 1) := by simp [layoutLookup]
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
  have hguardV : evalExpr (.ueq (.stdVecLen "a")
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
  have hguardM : memEvalExpr (.ueq (.stdVecLen "a")
      (.lit (.u64 (BitVec.ofNat 64 0))))
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("out", .stdVecVal lo)]
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
          ([] : List (BitVec 32))⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) ::
          lo⟩)], []⟩
      [("a", 1, 1), ("out", 0, 0)] = .ok (.b true) := by
    have hmemLen : memLoad
        ⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
            ([] : List (BitVec 32))⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) ::
            lo⟩)], []⟩ 1 1 0 =
        .ok (BitVec.ofNat 32 ([] : List (BitVec 32)).length) :=
      memLoad_cellsAt _ 1 1 0 _ _ hmem_a (by simp)
    have hag := memEvalExpr_ueq_agree (.stdVecLen "a")
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("out", .stdVecVal lo)]
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
          ([] : List (BitVec 32))⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) ::
          lo⟩)], []⟩
      [("a", 1, 1), ("out", 0, 0)]
      (memEvalExpr_stdVecLen_hit "a" _ _ _ _ _ _ hlay_a
        (by simp [envLookup]) hmemLen)
      (memEvalExpr_lit _ _ _ _)
    rw [hag]; exact hguardV
  have hifT := memEvalProgStmt_if_true vecUniqueCopyProg F
    (.ueq (.stdVecLen "a") (.lit (.u64 (BitVec.ofNat 64 0))))
    (.return_ (.lit (.u64 (BitVec.ofNat 64 0)))) .skip
    [("a", .stdVecVal ([] : List (BitVec 32))),
      ("out", .stdVecVal lo)]
    ⟨2, [(1, ⟨1, true,
      (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
        ([] : List (BitVec 32))⟩),
      (0, ⟨0, true,
      (BitVec.ofNat 32 lo.length) ::
        lo⟩)], []⟩
    [("a", 1, 1), ("out", 0, 0)] hguardM
  have hlitM : memEvalExpr
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal ([] : List (BitVec 32))),
        ("out", .stdVecVal lo)]
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
          ([] : List (BitVec 32))⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) ::
          lo⟩)], []⟩
      [("a", 1, 1), ("out", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal ([] : List (BitVec 32))),
          ("out", .stdVecVal lo)] :=
    memEvalExpr_lit _ _ _ _
  have hretM := memEvalProgStmt_return vecUniqueCopyProg F
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("a", .stdVecVal ([] : List (BitVec 32))),
      ("out", .stdVecVal lo)]
    ⟨2, [(1, ⟨1, true,
      (BitVec.ofNat 32 ([] : List (BitVec 32)).length) ::
        ([] : List (BitVec 32))⟩),
      (0, ⟨0, true,
      (BitVec.ofNat 32 lo.length) ::
        lo⟩)], []⟩
    [("a", 1, 1), ("out", 0, 0)]
    (.u64 (BitVec.ofNat 64 0)) (hlitM.trans hlitV)
  simp only [memEvalProgFunc, hbind, hbody]
  rw [memEvalProgStmt_seq_returned _ _ _ _ _ _ _ _ _ _ _
    (hifT.trans hretM)]

/-- Memory entry, seed-short leg: a nonempty input with an
    empty record fails loud at the seed store. -/
theorem memEvalProgFunc_vecUniqueCopy_seedShort (F : Nat)
    (la lo : List (BitVec 32)) (a0 : BitVec 32)
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (ha0 : la[0]? = some a0) (hmiss : lo[0]? = none) :
    memEvalProgFunc vecUniqueCopyProg F vecUniqueCopyFunc
      [.stdVecVal la, .stdVecVal lo] =
      .error .AssertFail := by
  have hbind := bindMemArgs_vecUniqueCopy la lo
  have hbody : vecUniqueCopyFunc.body =
      (.seq (.if_ (.ueq (.stdVecLen "a")
                  (.lit (.u64 (BitVec.ofNat 64 0))))
            (.return_ (.lit (.u64 (BitVec.ofNat 64 0))))
            .skip)
        (.seq vecUniqueCopySeed
          (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
            (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
              (.seq vecUniqueCopyLoop
                (.return_ (.var "w"))))))) := rfl
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
  have ha₂ : envLookup [("a", .stdVecVal la),
      ("out", .stdVecVal lo)] "a" =
      some (.stdVecVal la) := by simp [envLookup]
  have hout₂ : envLookup [("a", .stdVecVal la),
      ("out", .stdVecVal lo)] "out" =
      some (.stdVecVal lo) := by
    simp [envLookup, show ("out" : String) ≠ "a" by decide]
  have hlenV : evalExpr (.stdVecLen "a")
      [("a", .stdVecVal la), ("out", .stdVecVal lo)] =
      .ok (.u64 (BitVec.ofNat 64 la.length)) :=
    evalExpr_stdVecLen_some _ _ _ ha₂
  have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal la), ("out", .stdVecVal lo)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hlenN : (BitVec.ofNat 64 la.length).toNat = la.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hla64
  have hpos : 0 < la.length := by
    have hne : la ≠ [] := by
      intro hnil; rw [hnil] at ha0; simp at ha0
    exact List.length_pos_iff.mpr hne
  have hnn : BitVec.ofNat 64 la.length ≠ BitVec.ofNat 64 0 := by
    intro hcon
    have h0 := congrArg BitVec.toNat hcon
    rw [hlenN] at h0
    have hnil : la = [] := List.length_eq_zero_iff.mp h0
    rw [hnil] at ha0
    simp at ha0
  have hbeq : (BitVec.ofNat 64 la.length ==
      BitVec.ofNat 64 0) = false :=
    beq_eq_false_iff_ne.mpr hnn
  have hguardV : evalExpr (.ueq (.stdVecLen "a")
      (.lit (.u64 (BitVec.ofNat 64 0))))
      [("a", .stdVecVal la), ("out", .stdVecVal lo)] =
      .ok (.b false) := by
    have h := evalExpr_ueq_u64_vars (.stdVecLen "a")
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal la), ("out", .stdVecVal lo)]
      (BitVec.ofNat 64 la.length)
      (BitVec.ofNat 64 0) hlenV hlitV
    rwa [hbeq] at h
  have hguardM : memEvalExpr (.ueq (.stdVecLen "a")
      (.lit (.u64 (BitVec.ofNat 64 0))))
      [("a", .stdVecVal la), ("out", .stdVecVal lo)]
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
      [("a", 1, 1), ("out", 0, 0)] = .ok (.b false) := by
    have hmemLen : memLoad
        ⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 la.length) :: la⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ 1 1 0 =
        .ok (BitVec.ofNat 32 la.length) := by
      exact memLoad_cellsAt _ 1 1 0 _ _ hmem_a₀ (by simp)
    have hag := memEvalExpr_ueq_agree (.stdVecLen "a")
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal la), ("out", .stdVecVal lo)]
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
      [("a", 1, 1), ("out", 0, 0)]
      (memEvalExpr_stdVecLen_hit "a" _ _ _ _ _ _ hlay_a₀
        (by simp [envLookup]) hmemLen)
      (memEvalExpr_lit _ _ _ _)
    rw [hag]; exact hguardV
  have hifF := memEvalProgStmt_if_false vecUniqueCopyProg F
    (.ueq (.stdVecLen "a") (.lit (.u64 (BitVec.ofNat 64 0))))
    (.return_ (.lit (.u64 (BitVec.ofNat 64 0)))) .skip
    [("a", .stdVecVal la), ("out", .stdVecVal lo)]
    ⟨2, [(1, ⟨1, true,
      (BitVec.ofNat 32 la.length) :: la⟩),
      (0, ⟨0, true,
      (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
    [("a", 1, 1), ("out", 0, 0)] hguardM
  have hskipM : memEvalProgStmt vecUniqueCopyProg F .skip
      [("a", .stdVecVal la), ("out", .stdVecVal lo)]
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
      [("a", 1, 1), ("out", 0, 0)] =
      .ok (([("a", .stdVecVal la), ("out", .stdVecVal lo)],
        ⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 la.length) :: la⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩,
        [("a", 1, 1), ("out", 0, 0)]), .fellThrough) := by
    cases F <;> simp [memEvalProgStmt, memEvalStmtFuel,
      memEvalStmtZero, memEvalStmtWith]
  have hfallM := hifF.trans hskipM
  have hseedM := memUniqueCopySeed_short vecUniqueCopyProg F
    [("a", .stdVecVal la), ("out", .stdVecVal lo)]
    ⟨2, [(1, ⟨1, true,
      (BitVec.ofNat 32 la.length) :: la⟩),
      (0, ⟨0, true,
      (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
    [("a", 1, 1), ("out", 0, 0)]
    la lo a0 1 0 1 0
    (BitVec.ofNat 32 la.length) (BitVec.ofNat 32 lo.length)
    hlay_a₀ hlay_o₀ hmem_a₀ hmem_o₀ rfl
    hlo64 ha₂ hout₂ ha0 hmiss
  simp only [memEvalProgFunc, hbind, hbody]
  rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hfallM,
    memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hseedM]

/-- Memory entry, ok leg: the prelude binds, the seed plants
    the first survivor, the loop runs, and the survivor count
    returns. -/
theorem memEvalProgFunc_vecUniqueCopy_ok (F : Nat)
    (la lo : List (BitVec 32)) (a0 o0 : BitVec 32)
    (w' : Nat) (lo' : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length + 1 ≤ F)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hcap : (dedupAdj la).length ≤ lo.length)
    (ha0 : la[0]? = some a0)
    (ho0 : lo[0]? = some o0)
    (hfwd : uniqueCopyFwd la (lo.set 0 a0) la.length 1 1 =
      .ok (la.length, w', lo')) :
    memEvalProgFunc vecUniqueCopyProg F vecUniqueCopyFunc
      [.stdVecVal la, .stdVecVal lo] =
      .ok (.u64 (BitVec.ofNat 64 w')) := by
  have hbind := bindMemArgs_vecUniqueCopy la lo
  have hbody : vecUniqueCopyFunc.body =
      (.seq (.if_ (.ueq (.stdVecLen "a")
                  (.lit (.u64 (BitVec.ofNat 64 0))))
            (.return_ (.lit (.u64 (BitVec.ofNat 64 0))))
            .skip)
        (.seq vecUniqueCopySeed
          (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
            (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
              (.seq vecUniqueCopyLoop
                (.return_ (.var "w"))))))) := rfl
  cases hla : la with
  | nil =>
    subst hla
    simp at ha0
  | cons b0 ys =>
    subst hla
    have hab : a0 = b0 := by
      have hb0 : (b0 :: ys)[0]? = some b0 := by simp
      exact Option.some.inj (ha0.symm.trans hb0)
    subst b0
    have hlen1 : 1 ≤ (a0 :: ys).length := by simp
    have h0lt : 0 < lo.length := transformRead_lt lo 0 o0 ho0
    have ha₂ : envLookup [("a", .stdVecVal (a0 :: ys)),
        ("out", .stdVecVal lo)] "a" =
        some (.stdVecVal (a0 :: ys)) := by simp [envLookup]
    have hout₂ : envLookup [("a", .stdVecVal (a0 :: ys)),
        ("out", .stdVecVal lo)] "out" =
        some (.stdVecVal lo) := by
      simp [envLookup, show ("out" : String) ≠ "a" by decide]
    have hlenV : evalExpr (.stdVecLen "a")
        [("a", .stdVecVal (a0 :: ys)), ("out", .stdVecVal lo)] =
        .ok (.u64 (BitVec.ofNat 64 (a0 :: ys).length)) :=
      evalExpr_stdVecLen_some _ _ _ ha₂
    have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (a0 :: ys)), ("out", .stdVecVal lo)] =
        .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
    have hlenN : (BitVec.ofNat 64 (a0 :: ys).length).toNat =
        (a0 :: ys).length := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hla64
    have hnn : BitVec.ofNat 64 (a0 :: ys).length ≠
        BitVec.ofNat 64 0 := by
      intro hcon
      have h0 := congrArg BitVec.toNat hcon
      rw [hlenN] at h0
      simp at h0
    have hbeq : (BitVec.ofNat 64 (a0 :: ys).length ==
        BitVec.ofNat 64 0) = false :=
      beq_eq_false_iff_ne.mpr hnn
    have hguardV : evalExpr (.ueq (.stdVecLen "a")
        (.lit (.u64 (BitVec.ofNat 64 0))))
        [("a", .stdVecVal (a0 :: ys)), ("out", .stdVecVal lo)] =
        .ok (.b false) := by
      have h := evalExpr_ueq_u64_vars (.stdVecLen "a")
        (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (a0 :: ys)), ("out", .stdVecVal lo)]
        (BitVec.ofNat 64 (a0 :: ys).length)
        (BitVec.ofNat 64 0) hlenV hlitV
      rwa [hbeq] at h
    have hguardM : memEvalExpr (.ueq (.stdVecLen "a")
        (.lit (.u64 (BitVec.ofNat 64 0))))
        [("a", .stdVecVal (a0 :: ys)), ("out", .stdVecVal lo)]
        ⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 (a0 :: ys).length) :: (a0 :: ys)⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
        [("a", 1, 1), ("out", 0, 0)] = .ok (.b false) := by
      have hmemLen : memLoad
          ⟨2, [(1, ⟨1, true,
            (BitVec.ofNat 32 (a0 :: ys).length) :: (a0 :: ys)⟩),
            (0, ⟨0, true,
            (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ 1 1 0 =
          .ok (BitVec.ofNat 32 (a0 :: ys).length) := by
        have hmem_a : memFind
            ⟨2, [(1, ⟨1, true,
              (BitVec.ofNat 32 (a0 :: ys).length) :: (a0 :: ys)⟩),
              (0, ⟨0, true,
              (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ 1 =
            some ⟨1, true,
              (BitVec.ofNat 32 (a0 :: ys).length) :: (a0 :: ys)⟩ :=
          memFind_cons_hit _ _ _ _ _
        exact memLoad_cellsAt _ 1 1 0 _ _ hmem_a (by simp)
      have hag := memEvalExpr_ueq_agree (.stdVecLen "a")
        (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (a0 :: ys)), ("out", .stdVecVal lo)]
        ⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 (a0 :: ys).length) :: (a0 :: ys)⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
        [("a", 1, 1), ("out", 0, 0)]
        (memEvalExpr_stdVecLen_hit "a" _ _ _ _ _ _ (by simp [layoutLookup])
          (by simp [envLookup]) hmemLen)
        (memEvalExpr_lit _ _ _ _)
      rw [hag]; exact hguardV
    have hifF := memEvalProgStmt_if_false vecUniqueCopyProg F
      (.ueq (.stdVecLen "a") (.lit (.u64 (BitVec.ofNat 64 0))))
      (.return_ (.lit (.u64 (BitVec.ofNat 64 0)))) .skip
      [("a", .stdVecVal (a0 :: ys)), ("out", .stdVecVal lo)]
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 (a0 :: ys).length) :: (a0 :: ys)⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
      [("a", 1, 1), ("out", 0, 0)] hguardM
    have hskipM : memEvalProgStmt vecUniqueCopyProg F .skip
        [("a", .stdVecVal (a0 :: ys)), ("out", .stdVecVal lo)]
        ⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 (a0 :: ys).length) :: (a0 :: ys)⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
        [("a", 1, 1), ("out", 0, 0)] =
        .ok (([("a", .stdVecVal (a0 :: ys)), ("out", .stdVecVal lo)],
          ⟨2, [(1, ⟨1, true,
            (BitVec.ofNat 32 (a0 :: ys).length) :: (a0 :: ys)⟩),
            (0, ⟨0, true,
            (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩,
          [("a", 1, 1), ("out", 0, 0)]), .fellThrough) := by
      cases F <;> simp [memEvalProgStmt, memEvalStmtFuel,
        memEvalStmtZero, memEvalStmtWith]
    have hfallM := hifF.trans hskipM
    have hreadLo₀ : ∀ p, p < lo.length → ∃ y, lo[p]? = some y := by
      intro p hp
      exact ⟨lo[p], List.getElem?_eq_getElem hp⟩
    obtain ⟨ρs, ms, hseed, has, houts, hmems, hmem_as⟩ :=
      memUniqueCopySeed_hit vecUniqueCopyProg F
        [("a", .stdVecVal (a0 :: ys)), ("out", .stdVecVal lo)]
        ⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 (a0 :: ys).length) :: (a0 :: ys)⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
        [("a", 1, 1), ("out", 0, 0)]
        (a0 :: ys) lo a0 o0 1 0 1 0
        (BitVec.ofNat 32 (a0 :: ys).length)
        (BitVec.ofNat 32 lo.length)
        (by simp [layoutLookup]) (by simp [layoutLookup])
        (memFind_cons_hit _ _ _ _ _)
        (by
          have hne01 : (0 : Nat) ≠ 1 := by decide
          rw [memFind_cons_miss _ _ _ _ _ _ hne01]
          exact memFind_cons_hit _ _ _ _ _)
        rfl rfl (by decide) hlo64 ha₂ hout₂
        (by simpa using ha0) ho0
    have hlitM : memEvalExpr
        (.lit (.u64 (BitVec.ofNat 64 1)))
        ρs ms [("a", 1, 1), ("out", 0, 0)] =
        evalExpr (.lit (.u64 (BitVec.ofNat 64 1))) ρs :=
      memEvalExpr_lit _ _ _ _
    have hlitW : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        ρs = .ok (.u64 (BitVec.ofNat 64 1)) := by simp [evalExpr, litVal]
    have hletW := memRevLet vecUniqueCopyProg F "w" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 1))) ρs ms
      [("a", 1, 1), ("out", 0, 0)] (.u64 (BitVec.ofNat 64 1))
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) (by intro h; cases h) hlitM hlitW
    have hlitRM : memEvalExpr
        (.lit (.u64 (BitVec.ofNat 64 1)))
        (envExtend ρs "w" (.u64 (BitVec.ofNat 64 1))) ms
        [("a", 1, 1), ("out", 0, 0)] =
        evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
          (envExtend ρs "w" (.u64 (BitVec.ofNat 64 1))) :=
      memEvalExpr_lit _ _ _ _
    have hlitR : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        (envExtend ρs "w" (.u64 (BitVec.ofNat 64 1))) =
        .ok (.u64 (BitVec.ofNat 64 1)) := by simp [evalExpr, litVal]
    have hletR := memRevLet vecUniqueCopyProg F "r" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 1)))
      (envExtend ρs "w" (.u64 (BitVec.ofNat 64 1))) ms
      [("a", 1, 1), ("out", 0, 0)] (.u64 (BitVec.ofNat 64 1))
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) (by intro h; cases h) hlitRM hlitR
    have h1N : (BitVec.ofNat 64 1).toNat = 1 := by decide
    have ha₁ : envLookup (envExtend (envExtend ρs
        "w" (.u64 (BitVec.ofNat 64 1)))
        "r" (.u64 (BitVec.ofNat 64 1))) "a" =
        some (.stdVecVal (a0 :: ys)) := by
      rw [envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "r" by decide),
        envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "w" by decide)]
      have h := has
      simpa [envExtend, envLookup] using h
    have hout₁ : envLookup (envExtend (envExtend ρs
        "w" (.u64 (BitVec.ofNat 64 1)))
        "r" (.u64 (BitVec.ofNat 64 1))) "out" =
        some (.stdVecVal (lo.set 0 a0)) := by
      rw [envExtend_miss _ _ _ _
        (show ("out" : String) ≠ "r" by decide),
        envExtend_miss _ _ _ _
        (show ("out" : String) ≠ "w" by decide)]
      have h := houts
      simpa [envExtend, envLookup] using h
    have hr₁ : envLookup (envExtend (envExtend ρs
        "w" (.u64 (BitVec.ofNat 64 1)))
        "r" (.u64 (BitVec.ofNat 64 1))) "r" =
        some (.u64 (BitVec.ofNat 64 1)) :=
      envExtend_hit _ _ _
    have hw₁ : envLookup (envExtend (envExtend ρs
        "w" (.u64 (BitVec.ofNat 64 1)))
        "r" (.u64 (BitVec.ofNat 64 1))) "w" =
        some (.u64 (BitVec.ofNat 64 1)) := by
      rw [envExtend_miss _ _ _ _
        (show ("w" : String) ≠ "r" by decide)]
      exact envExtend_hit _ _ _
    have hreadLo₁ : ∀ p, p < (lo.set 0 a0).length →
        ∃ y, ((lo.set 0 a0)[p]? = some y) := by
      intro p hp
      have hlenS : (lo.set 0 a0).length = lo.length := by
        simp [List.length_set]
      have hplen : p < lo.length := by omega
      obtain ⟨z, hz⟩ := hreadLo₀ p hplen
      by_cases hpw : p = 0
      · rw [hpw]
        exact ⟨a0, List.getElem?_set_self h0lt⟩
      · exact ⟨z, by
          rw [List.getElem?_set_ne (by omega : (0 : Nat) ≠ p)]
          exact hz⟩
    have hpre₁ : (lo.set 0 a0).take 1
        = dedupAdj ((a0 :: ys).take 1) := by
      rw [show (1 : Nat) = 0 + 1 from rfl,
        take_set_succ_self lo 0 a0 h0lt]
      simp [dedupAdj]
    have hwlo₁ : 1 ≤ (lo.set 0 a0).length := by
      have hlenS : (lo.set 0 a0).length = lo.length := by
        simp [List.length_set]
      omega
    have hcapS : (dedupAdj (a0 :: ys)).length ≤
        (lo.set 0 a0).length := by
      have hlenS : (lo.set 0 a0).length = lo.length := by
        simp [List.length_set]
      rw [hlenS]; exact hcap
    obtain ⟨ρ', m', hloop, ha', hout', ⟨rB', hrB', hrN'⟩,
        ⟨wB', hwB', hwN'⟩, hmem', hmem_a'⟩ :=
      memUniqueCopyLoop_ok vecUniqueCopyProg F ((a0 :: ys).length)
        (envExtend (envExtend ρs
          "w" (.u64 (BitVec.ofNat 64 1)))
          "r" (.u64 (BitVec.ofNat 64 1)))
        ms [("a", 1, 1), ("out", 0, 0)]
        (a0 :: ys) (lo.set 0 a0) 1 1
        (BitVec.ofNat 64 1) (BitVec.ofNat 64 1)
        lo' (a0 :: ys).length w'
        1 0 1 0
        (BitVec.ofNat 32 (a0 :: ys).length)
        (BitVec.ofNat 32 lo.length)
        (by simp [layoutLookup]) (by simp [layoutLookup])
        hmem_as hmems rfl (by rw [List.length_set]) (by decide)
        h1N h1N hla64
        (by simp [List.length_set]; exact hlo64)
        ha₁ hout₁ hr₁ hw₁
        hlen1 (Nat.le_refl _) (Nat.le_refl _)
        hwlo₁ hpre₁
        (by omega) (by omega)
        hread hreadLo₁ hfwd
    have hwEq : wB' = BitVec.ofNat 64 w' := by
      have hb := uniqueCopyFwd_le (a0 :: ys) (lo.set 0 a0)
        ((a0 :: ys).length) 1 1 w' lo' hlen1 (Nat.le_refl _)
        (Nat.le_refl _) (Nat.sub_le _ _) hread hreadLo₁ hpre₁
        (by simp [List.length_set]; omega) hcapS hfwd
      apply BitVec.eq_of_toNat_eq
      rw [hwN', BitVec.toNat_ofNat]
      have hlenS : (lo.set 0 a0).length = lo.length := by
        simp [List.length_set]
      have hw'lt : w' < 2 ^ 64 := by
        have hlo64' : (lo.set 0 a0).length < 2 ^ 64 := by
          rw [hlenS]; exact hlo64
        omega
      exact (Nat.mod_eq_of_lt hw'lt).symm
    have hevW' : memEvalExpr (.var "w") ρ' m'
        [("a", 1, 1), ("out", 0, 0)] =
        .ok (.u64 (BitVec.ofNat 64 w')) := by
      rw [← hwEq]
      exact (memEvalExpr_var _ _ _ _).trans
        (evalExpr_var_hit _ _ _ hwB')
    have hretM := memEvalProgStmt_return vecUniqueCopyProg F
      (.var "w") ρ' m' [("a", 1, 1), ("out", 0, 0)]
      (.u64 (BitVec.ofNat 64 w')) hevW'
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hfallM,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hseed,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletW,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletR,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hloop,
      hretM]

/-- Memory entry, err leg: the prelude binds, the loop hits
    the short `out` and fails loud. -/
theorem memEvalProgFunc_vecUniqueCopy_err (F : Nat)
    (la lo : List (BitVec 32)) (a0 o0 : BitVec 32)
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length + 1 ≤ F)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hreadLo₀ : ∀ p, p < lo.length → ∃ y, lo[p]? = some y)
    (ha0 : la[0]? = some a0) (ho0 : lo[0]? = some o0)
    (hfwd : uniqueCopyFwd la (lo.set 0 a0) la.length 1 1 =
      .error .AssertFail) :
    memEvalProgFunc vecUniqueCopyProg F vecUniqueCopyFunc
      [.stdVecVal la, .stdVecVal lo] =
      .error .AssertFail := by
  have hbind := bindMemArgs_vecUniqueCopy la lo
  have hbody : vecUniqueCopyFunc.body =
      (.seq (.if_ (.ueq (.stdVecLen "a")
                  (.lit (.u64 (BitVec.ofNat 64 0))))
            (.return_ (.lit (.u64 (BitVec.ofNat 64 0))))
            .skip)
        (.seq vecUniqueCopySeed
          (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
            (.seq (.let_ "r" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
              (.seq vecUniqueCopyLoop
                (.return_ (.var "w"))))))) := rfl
  cases hla : la with
  | nil =>
    subst hla
    simp at ha0
  | cons b0 ys =>
    subst hla
    have hab : a0 = b0 := by
      have hb0 : (b0 :: ys)[0]? = some b0 := by simp
      exact Option.some.inj (ha0.symm.trans hb0)
    subst b0
    have hlen1 : 1 ≤ (a0 :: ys).length := by simp
    have h0lt : 0 < lo.length := transformRead_lt lo 0 o0 ho0
    have ha₂ : envLookup [("a", .stdVecVal (a0 :: ys)),
        ("out", .stdVecVal lo)] "a" =
        some (.stdVecVal (a0 :: ys)) := by simp [envLookup]
    have hout₂ : envLookup [("a", .stdVecVal (a0 :: ys)),
        ("out", .stdVecVal lo)] "out" =
        some (.stdVecVal lo) := by
      simp [envLookup, show ("out" : String) ≠ "a" by decide]
    have hlenV : evalExpr (.stdVecLen "a")
        [("a", .stdVecVal (a0 :: ys)), ("out", .stdVecVal lo)] =
        .ok (.u64 (BitVec.ofNat 64 (a0 :: ys).length)) :=
      evalExpr_stdVecLen_some _ _ _ ha₂
    have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (a0 :: ys)), ("out", .stdVecVal lo)] =
        .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
    have hlenN : (BitVec.ofNat 64 (a0 :: ys).length).toNat =
        (a0 :: ys).length := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hla64
    have hnn : BitVec.ofNat 64 (a0 :: ys).length ≠
        BitVec.ofNat 64 0 := by
      intro hcon
      have h0 := congrArg BitVec.toNat hcon
      rw [hlenN] at h0
      simp at h0
    have hbeq : (BitVec.ofNat 64 (a0 :: ys).length ==
        BitVec.ofNat 64 0) = false :=
      beq_eq_false_iff_ne.mpr hnn
    have hguardV : evalExpr (.ueq (.stdVecLen "a")
        (.lit (.u64 (BitVec.ofNat 64 0))))
        [("a", .stdVecVal (a0 :: ys)), ("out", .stdVecVal lo)] =
        .ok (.b false) := by
      have h := evalExpr_ueq_u64_vars (.stdVecLen "a")
        (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (a0 :: ys)), ("out", .stdVecVal lo)]
        (BitVec.ofNat 64 (a0 :: ys).length)
        (BitVec.ofNat 64 0) hlenV hlitV
      rwa [hbeq] at h
    have hguardM : memEvalExpr (.ueq (.stdVecLen "a")
        (.lit (.u64 (BitVec.ofNat 64 0))))
        [("a", .stdVecVal (a0 :: ys)), ("out", .stdVecVal lo)]
        ⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 (a0 :: ys).length) :: (a0 :: ys)⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
        [("a", 1, 1), ("out", 0, 0)] = .ok (.b false) := by
      have hmemLen : memLoad
          ⟨2, [(1, ⟨1, true,
            (BitVec.ofNat 32 (a0 :: ys).length) :: (a0 :: ys)⟩),
            (0, ⟨0, true,
            (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ 1 1 0 =
          .ok (BitVec.ofNat 32 (a0 :: ys).length) := by
        have hmem_a : memFind
            ⟨2, [(1, ⟨1, true,
              (BitVec.ofNat 32 (a0 :: ys).length) :: (a0 :: ys)⟩),
              (0, ⟨0, true,
              (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ 1 =
            some ⟨1, true,
              (BitVec.ofNat 32 (a0 :: ys).length) :: (a0 :: ys)⟩ :=
          memFind_cons_hit _ _ _ _ _
        exact memLoad_cellsAt _ 1 1 0 _ _ hmem_a (by simp)
      have hag := memEvalExpr_ueq_agree (.stdVecLen "a")
        (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal (a0 :: ys)), ("out", .stdVecVal lo)]
        ⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 (a0 :: ys).length) :: (a0 :: ys)⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
        [("a", 1, 1), ("out", 0, 0)]
        (memEvalExpr_stdVecLen_hit "a" _ _ _ _ _ _ (by simp [layoutLookup])
          (by simp [envLookup]) hmemLen)
        (memEvalExpr_lit _ _ _ _)
      rw [hag]; exact hguardV
    have hifF := memEvalProgStmt_if_false vecUniqueCopyProg F
      (.ueq (.stdVecLen "a") (.lit (.u64 (BitVec.ofNat 64 0))))
      (.return_ (.lit (.u64 (BitVec.ofNat 64 0)))) .skip
      [("a", .stdVecVal (a0 :: ys)), ("out", .stdVecVal lo)]
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 (a0 :: ys).length) :: (a0 :: ys)⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
      [("a", 1, 1), ("out", 0, 0)] hguardM
    have hskipM : memEvalProgStmt vecUniqueCopyProg F .skip
        [("a", .stdVecVal (a0 :: ys)), ("out", .stdVecVal lo)]
        ⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 (a0 :: ys).length) :: (a0 :: ys)⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
        [("a", 1, 1), ("out", 0, 0)] =
        .ok (([("a", .stdVecVal (a0 :: ys)), ("out", .stdVecVal lo)],
          ⟨2, [(1, ⟨1, true,
            (BitVec.ofNat 32 (a0 :: ys).length) :: (a0 :: ys)⟩),
            (0, ⟨0, true,
            (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩,
          [("a", 1, 1), ("out", 0, 0)]), .fellThrough) := by
      cases F <;> simp [memEvalProgStmt, memEvalStmtFuel,
        memEvalStmtZero, memEvalStmtWith]
    have hfallM := hifF.trans hskipM
    have hreadLo₀ : ∀ p, p < lo.length → ∃ y, lo[p]? = some y := by
      intro p hp
      exact ⟨lo[p], List.getElem?_eq_getElem hp⟩
    obtain ⟨ρs, ms, hseed, has, houts, hmems, hmem_as⟩ :=
      memUniqueCopySeed_hit vecUniqueCopyProg F
        [("a", .stdVecVal (a0 :: ys)), ("out", .stdVecVal lo)]
        ⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 (a0 :: ys).length) :: (a0 :: ys)⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
        [("a", 1, 1), ("out", 0, 0)]
        (a0 :: ys) lo a0 o0 1 0 1 0
        (BitVec.ofNat 32 (a0 :: ys).length)
        (BitVec.ofNat 32 lo.length)
        (by simp [layoutLookup]) (by simp [layoutLookup])
        (memFind_cons_hit _ _ _ _ _)
        (by
          have hne01 : (0 : Nat) ≠ 1 := by decide
          rw [memFind_cons_miss _ _ _ _ _ _ hne01]
          exact memFind_cons_hit _ _ _ _ _)
        rfl rfl (by decide) hlo64 ha₂ hout₂
        (by simpa using ha0) ho0
    have hlitM : memEvalExpr
        (.lit (.u64 (BitVec.ofNat 64 1)))
        ρs ms [("a", 1, 1), ("out", 0, 0)] =
        evalExpr (.lit (.u64 (BitVec.ofNat 64 1))) ρs :=
      memEvalExpr_lit _ _ _ _
    have hlitW : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        ρs = .ok (.u64 (BitVec.ofNat 64 1)) := by simp [evalExpr, litVal]
    have hletW := memRevLet vecUniqueCopyProg F "w" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 1))) ρs ms
      [("a", 1, 1), ("out", 0, 0)] (.u64 (BitVec.ofNat 64 1))
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) (by intro h; cases h) hlitM hlitW
    have hlitRM : memEvalExpr
        (.lit (.u64 (BitVec.ofNat 64 1)))
        (envExtend ρs "w" (.u64 (BitVec.ofNat 64 1))) ms
        [("a", 1, 1), ("out", 0, 0)] =
        evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
          (envExtend ρs "w" (.u64 (BitVec.ofNat 64 1))) :=
      memEvalExpr_lit _ _ _ _
    have hlitR : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        (envExtend ρs "w" (.u64 (BitVec.ofNat 64 1))) =
        .ok (.u64 (BitVec.ofNat 64 1)) := by simp [evalExpr, litVal]
    have hletR := memRevLet vecUniqueCopyProg F "r" (.u 64)
      (.lit (.u64 (BitVec.ofNat 64 1)))
      (envExtend ρs "w" (.u64 (BitVec.ofNat 64 1))) ms
      [("a", 1, 1), ("out", 0, 0)] (.u64 (BitVec.ofNat 64 1))
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) (by intro h; cases h) hlitRM hlitR
    have h1N : (BitVec.ofNat 64 1).toNat = 1 := by decide
    have ha₁ : envLookup (envExtend (envExtend ρs
        "w" (.u64 (BitVec.ofNat 64 1)))
        "r" (.u64 (BitVec.ofNat 64 1))) "a" =
        some (.stdVecVal (a0 :: ys)) := by
      rw [envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "r" by decide),
        envExtend_miss _ _ _ _
        (show ("a" : String) ≠ "w" by decide)]
      have h := has
      simpa [envExtend, envLookup] using h
    have hout₁ : envLookup (envExtend (envExtend ρs
        "w" (.u64 (BitVec.ofNat 64 1)))
        "r" (.u64 (BitVec.ofNat 64 1))) "out" =
        some (.stdVecVal (lo.set 0 a0)) := by
      rw [envExtend_miss _ _ _ _
        (show ("out" : String) ≠ "r" by decide),
        envExtend_miss _ _ _ _
        (show ("out" : String) ≠ "w" by decide)]
      have h := houts
      simpa [envExtend, envLookup] using h
    have hr₁ : envLookup (envExtend (envExtend ρs
        "w" (.u64 (BitVec.ofNat 64 1)))
        "r" (.u64 (BitVec.ofNat 64 1))) "r" =
        some (.u64 (BitVec.ofNat 64 1)) :=
      envExtend_hit _ _ _
    have hw₁ : envLookup (envExtend (envExtend ρs
        "w" (.u64 (BitVec.ofNat 64 1)))
        "r" (.u64 (BitVec.ofNat 64 1))) "w" =
        some (.u64 (BitVec.ofNat 64 1)) := by
      rw [envExtend_miss _ _ _ _
        (show ("w" : String) ≠ "r" by decide)]
      exact envExtend_hit _ _ _
    have hreadLo₁ : ∀ p, p < (lo.set 0 a0).length →
        ∃ y, ((lo.set 0 a0)[p]? = some y) := by
      intro p hp
      have hlenS : (lo.set 0 a0).length = lo.length := by
        simp [List.length_set]
      have hplen : p < lo.length := by omega
      obtain ⟨z, hz⟩ := hreadLo₀ p hplen
      by_cases hpw : p = 0
      · rw [hpw]
        exact ⟨a0, List.getElem?_set_self h0lt⟩
      · exact ⟨z, by
          rw [List.getElem?_set_ne (by omega : (0 : Nat) ≠ p)]
          exact hz⟩
    have hloop : memEvalProgStmt vecUniqueCopyProg F vecUniqueCopyLoop
        (envExtend (envExtend ρs
          "w" (.u64 (BitVec.ofNat 64 1)))
          "r" (.u64 (BitVec.ofNat 64 1))) ms
        [("a", 1, 1), ("out", 0, 0)] =
        .error .AssertFail :=
      memUniqueCopyLoop_err vecUniqueCopyProg F ((a0 :: ys).length)
        (envExtend (envExtend ρs
          "w" (.u64 (BitVec.ofNat 64 1)))
          "r" (.u64 (BitVec.ofNat 64 1)))
        ms [("a", 1, 1), ("out", 0, 0)]
        (a0 :: ys) (lo.set 0 a0) 1 1
        (BitVec.ofNat 64 1) (BitVec.ofNat 64 1)
        1 0 1 0
        (BitVec.ofNat 32 (a0 :: ys).length)
        (BitVec.ofNat 32 lo.length)
        (by simp [layoutLookup]) (by simp [layoutLookup])
        hmem_as hmems
        rfl (by rw [List.length_set]) (by decide)
        h1N h1N hla64
        (by simp [List.length_set]; exact hlo64)
        ha₁ hout₁ hr₁ hw₁
        (by simp) (Nat.le_refl _)
        (by simp [List.length_set]; omega)
        (by omega) (by omega)
        hread hreadLo₁ hfwd
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hfallM,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hseed,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletW,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletR,
      memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hloop]

/-- Transfer for `vec_unique_copy`, ok leg: memory evaluation
    agrees with value evaluation (the record fits). -/
theorem memTransferProg_vecUniqueCopy_ok (F : Nat)
    (la lo : List (BitVec 32)) (a0 o0 : BitVec 32)
    (w' : Nat) (lo' : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length + 1 ≤ F)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hcap : (dedupAdj la).length ≤ lo.length)
    (ha0 : la[0]? = some a0)
    (ho0 : lo[0]? = some o0)
    (hfwd : uniqueCopyFwd la (lo.set 0 a0) la.length 1 1 =
      .ok (la.length, w', lo'))
    (_h : oracleNoalias vecUniqueCopyFunc
      [.stdVecVal la, .stdVecVal lo]) :
    memEvalProgFunc vecUniqueCopyProg F vecUniqueCopyFunc
      [.stdVecVal la, .stdVecVal lo] =
      evalProgFunc vecUniqueCopyProg F vecUniqueCopyFunc
        [.stdVecVal la, .stdVecVal lo] := by
  rw [memEvalProgFunc_vecUniqueCopy_ok F la lo a0 o0 w' lo'
    hla64 hlo64 hF hread hcap ha0 ho0 hfwd,
    evalProgFunc_vecUniqueCopy_ok F la lo a0 w' lo'
    hla64 hlo64 hF hread hcap ha0 hfwd]

/-- Transfer for `vec_unique_copy`, err leg: both sides fail
    loud on a short record. -/
theorem memTransferProg_vecUniqueCopy_err (F : Nat)
    (la lo : List (BitVec 32)) (a0 o0 : BitVec 32)
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length + 1 ≤ F)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hreadLo₀ : ∀ p, p < lo.length → ∃ y, lo[p]? = some y)
    (ha0 : la[0]? = some a0) (ho0 : lo[0]? = some o0)
    (hfwd : uniqueCopyFwd la (lo.set 0 a0) la.length 1 1 =
      .error .AssertFail)
    (_h : oracleNoalias vecUniqueCopyFunc
      [.stdVecVal la, .stdVecVal lo]) :
    memEvalProgFunc vecUniqueCopyProg F vecUniqueCopyFunc
      [.stdVecVal la, .stdVecVal lo] =
      evalProgFunc vecUniqueCopyProg F vecUniqueCopyFunc
        [.stdVecVal la, .stdVecVal lo] := by
  rw [memEvalProgFunc_vecUniqueCopy_err F la lo a0 o0
    hla64 hlo64 hF hread hreadLo₀ ha0 ho0 hfwd,
    evalProgFunc_vecUniqueCopy_err F la lo a0 o0
    hla64 hlo64 hF hread hreadLo₀ ha0 ho0 hfwd]

/-- Closing caller-record squeeze contract, ok leg: when the
    squeeze fits, the forward returns the squeeze count over
    the squeeze prefix, record length unchanged. -/
theorem evalProgFunc_vecUniqueCopy_spec_ok (F : Nat)
    (la lo : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length + 1 ≤ F)
    (hcap : (dedupAdj la).length ≤ lo.length) :
    ∃ (w' : Nat) (lo' : List (BitVec 32)),
      memEvalProgFunc vecUniqueCopyProg F vecUniqueCopyFunc
        [.stdVecVal la, .stdVecVal lo] =
        .ok (.u64 (BitVec.ofNat 64 w')) ∧
      lo'.take w' = dedupAdj la ∧
      w' = (dedupAdj la).length ∧
      lo'.length = lo.length := by
  have hread : ∀ p, p < la.length → ∃ y, la[p]? = some y :=
    fun p hp => ⟨_, List.getElem?_eq_getElem hp⟩
  cases hla : la with
  | nil =>
    subst hla
    refine ⟨0, lo, memEvalProgFunc_vecUniqueCopy_nil F lo, ?_, rfl, rfl⟩
    simp [dedupAdj]
  | cons a0 xs =>
    subst hla
    have hlen1 : 1 ≤ (a0 :: xs).length := by simp
    have hcap1 : 0 < lo.length := by
      have hnn := dedupAdj_nonempty (show (a0 :: xs) ≠ [] by simp)
      have hpos : 0 < (dedupAdj (a0 :: xs)).length :=
        List.length_pos_iff.mpr hnn
      omega
    have h0lt : 0 < lo.length := hcap1
    have ha0 : (a0 :: xs)[0]? = some a0 := by simp
    have ho0 : lo[0]? = some lo[0] :=
      List.getElem?_eq_getElem h0lt
    have hreadLo₀ : ∀ p, p < lo.length → ∃ y, lo[p]? = some y := by
      intro p hp
      exact ⟨lo[p], List.getElem?_eq_getElem hp⟩
    have hpre₁ : (lo.set 0 a0).take 1
        = dedupAdj ((a0 :: xs).take 1) := by
      rw [show (1 : Nat) = 0 + 1 from rfl,
        take_set_succ_self lo 0 a0 h0lt]
      simp [dedupAdj]
    have hwlo₁ : 1 ≤ (lo.set 0 a0).length := by
      have hlenS : (lo.set 0 a0).length = lo.length := by
        simp [List.length_set]
      omega
    have hreadLo₁ : ∀ p, p < (lo.set 0 a0).length →
        ∃ y, ((lo.set 0 a0)[p]? = some y) := by
      intro p hp
      have hlenS : (lo.set 0 a0).length = lo.length := by
        simp [List.length_set]
      have hplen : p < lo.length := by omega
      obtain ⟨z, hz⟩ := hreadLo₀ p hplen
      by_cases hpw : p = 0
      · rw [hpw]
        exact ⟨a0, List.getElem?_set_self h0lt⟩
      · exact ⟨z, by
          rw [List.getElem?_set_ne (by omega : (0 : Nat) ≠ p)]
          exact hz⟩
    have hcapS : (dedupAdj (a0 :: xs)).length ≤
        (lo.set 0 a0).length := by
      have hlenS : (lo.set 0 a0).length = lo.length := by
        simp [List.length_set]
      rw [hlenS]; exact hcap
    obtain ⟨w', lo', hfwd⟩ := uniqueCopyFwd_ok (a0 :: xs)
      (lo.set 0 a0) ((a0 :: xs).length) 1 1 hlen1
      (Nat.le_refl _) (Nat.le_refl _) (Nat.sub_le _ _)
      hread hreadLo₁ hpre₁
      (by simp [List.length_set]; omega) hcapS
    obtain ⟨hpref, hleW, hlen'⟩ := uniqueCopyFwd_prefix
      (a0 :: xs) lo ((a0 :: xs).length) 1 1 w' (lo.set 0 a0) lo'
      hlen1 (Nat.le_refl _) (Nat.le_refl _)
      (Nat.sub_le _ _) (by simp [List.length_set])
      hread hreadLo₁ hpre₁
      (by simp [List.length_set]; omega) hcap
      (fun j hj =>
        List.getElem?_set_ne (show (0 : Nat) ≠ j by omega))
      hfwd
    have hb := uniqueCopyFwd_le (a0 :: xs) (lo.set 0 a0)
      ((a0 :: xs).length) 1 1 w' lo' hlen1
      (Nat.le_refl _) (Nat.le_refl _) (Nat.sub_le _ _)
      hread hreadLo₁ hpre₁
      (by simp [List.length_set]; omega) hcapS hfwd
    have hlenS : (lo.set 0 a0).length = lo.length := by
      simp [List.length_set]
    have hwlen : w' = (dedupAdj (a0 :: xs)).length :=
      squeeze_length_eq lo' _ w' hpref (by omega)
    have heval := evalProgFunc_vecUniqueCopy_ok F (a0 :: xs) lo
      a0 w' lo' hla64 hlo64 hF hread hcap ha0 hfwd
    have htrans := memTransferProg_vecUniqueCopy_ok F (a0 :: xs) lo
      a0 lo[0] w' lo' hla64 hlo64 hF hread hcap ha0 ho0 hfwd
      (oracleNoalias_vecUniqueCopy _ _)
    rw [htrans]
    exact ⟨w', lo', heval, hpref, hwlen, hlen'⟩

/-- Closing caller-record squeeze contract, err leg: a short
    record fails loud on both layers. -/
theorem evalProgFunc_vecUniqueCopy_spec_err (F : Nat)
    (la lo : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length + 1 ≤ F)
    (hcap : (dedupAdj la).length ≤ lo.length)
    (hmore : lo.length < (dedupAdj la).length) :
    memEvalProgFunc vecUniqueCopyProg F vecUniqueCopyFunc
      [.stdVecVal la, .stdVecVal lo] =
      .error .AssertFail := by
  have hread : ∀ p, p < la.length → ∃ y, la[p]? = some y :=
    fun p hp => ⟨_, List.getElem?_eq_getElem hp⟩
  cases hla : la with
  | nil =>
    subst hla
    simp [dedupAdj] at hmore
  | cons a0 xs =>
    subst hla
    have hlen1 : 1 ≤ (a0 :: xs).length := by simp
    have ha0 : (a0 :: xs)[0]? = some a0 := by simp
    by_cases hlo0 : lo = []
    · subst hlo0
      have hseedV := evalProgFunc_vecUniqueCopy_seedShort F
        (a0 :: xs) [] a0 hla64 (by simp) hread ha0 rfl
      have hseedM := memEvalProgFunc_vecUniqueCopy_seedShort F
        (a0 :: xs) [] a0 hla64 (by simp) hread ha0 rfl
      exact hseedM
    · have hne : lo ≠ [] := hlo0
      have h0lt : 0 < lo.length := List.length_pos_iff.mpr hne
      obtain ⟨o0, ho0⟩ : ∃ z, lo[0]? = some z :=
        ⟨lo[0], List.getElem?_eq_getElem h0lt⟩
      have hreadLo₀ : ∀ p, p < lo.length → ∃ y, lo[p]? = some y := by
        intro p hp
        exact ⟨lo[p], List.getElem?_eq_getElem hp⟩
      have hpre₁ : (lo.set 0 a0).take 1
          = dedupAdj ((a0 :: xs).take 1) := by
        rw [show (1 : Nat) = 0 + 1 from rfl,
          take_set_succ_self lo 0 a0 h0lt]
        simp [dedupAdj]
      have hwlo₁ : 1 ≤ (lo.set 0 a0).length := by
        have hlenS : (lo.set 0 a0).length = lo.length := by
          simp [List.length_set]
        omega
      have hreadLo₁ : ∀ p, p < (lo.set 0 a0).length →
          ∃ y, ((lo.set 0 a0)[p]? = some y) := by
        intro p hp
        have hlenS : (lo.set 0 a0).length = lo.length := by
          simp [List.length_set]
        have hplen : p < lo.length := by omega
        obtain ⟨z, hz⟩ := hreadLo₀ p hplen
        by_cases hpw : p = 0
        · rw [hpw]
          exact ⟨a0, List.getElem?_set_self h0lt⟩
        · exact ⟨z, by
            rw [List.getElem?_set_ne (by omega : (0 : Nat) ≠ p)]
            exact hz⟩
      have hmore' : (lo.set 0 a0).length < (dedupAdj (a0 :: xs)).length := by
        have hlenS : (lo.set 0 a0).length = lo.length := by
          simp [List.length_set]
        rw [hlenS]; exact hmore
      have hfwd := uniqueCopyFwd_err_of_overflow (a0 :: xs)
        (lo.set 0 a0) hlen1 hread hreadLo₁ hpre₁ hwlo₁ hmore'
      have herrV := evalProgFunc_vecUniqueCopy_err F (a0 :: xs) lo
        a0 o0 hla64 hlo64 hF hread hreadLo₀ ha0 ho0 hfwd
      have herrM := memEvalProgFunc_vecUniqueCopy_err F (a0 :: xs) lo
        a0 o0 hla64 hlo64 hF hread hreadLo₀ ha0 ho0 hfwd
      exact herrM
