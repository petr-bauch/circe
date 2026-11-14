/-
Circe.Transfer.VecMismatch — mem transfer for first-difference query
(`vec_mismatch`, the `std::mismatch` idiom; P2-M19).

Mem-level mirrors of the eval-level equations in
`Circe.Emit.VecMismatch`: the two `sharedBorrow` inputs pin reified
snapshots (length word up front, elements behind); inline `stdVecAt`
reads go through `memEvalExpr_stdVecAt_hit`, the `tif` guard through
`memEvalExpr_tif_true/false` over two `ult` agreements, and the cursor
bump through `memRevAssign`. Nothing writes memory, so the loop
re-inducts over `(ρ, m, π)` with `m`/`π` fixed and only the cursor
moving. Entries close against the forward contract; the closing spec
ties the `u64` result to the independent oracle (`firstDiff` in
`Circe.Emit.VecMismatch`).
-/
import Circe.Transfer.VecReverse
import Circe.Emit.VecMismatch

/-! ## Binding (closed form) -/

/-- Mismatch binding pins two snapshots: the two shared-borrow inputs
    at addrs `1`/`0` (tail-first allocation order). -/
theorem bindMemArgs_vecMismatch (la lb : List (BitVec 32)) :
    bindMemArgs vecMismatchFunc.args
      [.stdVecVal la, .stdVecVal lb] emptyMem =
      some ([("a", .stdVecVal la), ("b", .stdVecVal lb)],
        ⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 la.length) :: la⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lb.length) :: lb⟩)], []⟩,
        [("a", 1, 1), ("b", 0, 0)]) := by
  rfl

/-- Mismatch footprint is two pairwise-disjoint singletons. -/
theorem oracleNoalias_vecMismatch (la lb : List (BitVec 32)) :
    oracleNoalias vecMismatchFunc
      [.stdVecVal la, .stdVecVal lb] := by
  have hb := bindMemArgs_vecMismatch la lb
  have hn : LayoutNoAlias [("a", 1, 1), ("b", 0, 0)] := by
    simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-! ## Guard agreement (memory/eval) -/

/-- The `tif` guard agrees on memory: both `ult` legs read through
    their length words, and whichever branch the value side takes,
    the memory side follows. -/
theorem memMismatchGuard_agree
    (ρ : Env) (m : Mem) (π : Layout)
    (la lb : List (BitVec 32)) (i : Nat)
    (iB : BitVec 64)
    (aa ab : Nat) (ta tb : Nat) (na nb : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_b : layoutLookup π "b" = some (ab, tb))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nb :: lb⟩)
    (hna : na = BitVec.ofNat 32 la.length)
    (hnb : nb = BitVec.ofNat 32 lb.length)
    (hiN : iB.toNat = i)
    (hla64 : la.length < 2 ^ 64) (hlb64 : lb.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hi : envLookup ρ "i" = some (.u64 iB)) :
    memEvalExpr mismatchGuard ρ m π = evalExpr mismatchGuard ρ := by
  have hmemLenA : memLoad m aa ta 0 =
      .ok (BitVec.ofNat 32 la.length) := by
    rw [← hna]
    exact memLoad_cellsAt m aa ta 0 (na :: la) na hmem_a (by simp)
  have hmemLenB : memLoad m ab tb 0 =
      .ok (BitVec.ofNat 32 lb.length) := by
    rw [← hnb]
    exact memLoad_cellsAt m ab tb 0 (nb :: lb) nb hmem_b (by simp)
  have hagA : memEvalExpr (.ult (.var "i") (.stdVecLen "a")) ρ m π =
      evalExpr (.ult (.var "i") (.stdVecLen "a")) ρ :=
    memEvalExpr_ult_agree (.var "i") (.stdVecLen "a") ρ m π
      (memEvalExpr_var _ _ _ _)
      (memEvalExpr_stdVecLen_hit "a" ρ m π la aa ta
        hlay_a ha hmemLenA)
  have hagB : memEvalExpr (.ult (.var "i") (.stdVecLen "b")) ρ m π =
      evalExpr (.ult (.var "i") (.stdVecLen "b")) ρ :=
    memEvalExpr_ult_agree (.var "i") (.stdVecLen "b") ρ m π
      (memEvalExpr_var _ _ _ _)
      (memEvalExpr_stdVecLen_hit "b" ρ m π lb ab tb
        hlay_b hb hmemLenB)
  have hultA := evalExpr_ult_u64 (.var "i") (.stdVecLen "a") ρ iB
    (BitVec.ofNat 64 la.length)
    (evalExpr_var_hit _ _ _ hi)
    (evalExpr_stdVecLen_some _ _ _ ha)
  by_cases h1 : (iB.ult (BitVec.ofNat 64 la.length)) = true
  · have hvcA : evalExpr (.ult (.var "i") (.stdVecLen "a")) ρ =
        .ok (.b true) := by rwa [h1] at hultA
    exact memEvalExpr_tif_true _ _ _ _ _ _ hagA hvcA hagB
  · have hvcA : evalExpr (.ult (.var "i") (.stdVecLen "a")) ρ =
        .ok (.b false) := by
      have h1f : (iB.ult (BitVec.ofNat 64 la.length)) = false := by
        cases h : iB.ult (BitVec.ofNat 64 la.length) with
        | true => exact absurd h h1
        | false => rfl
      rwa [h1f] at hultA
    exact memEvalExpr_tif_false _ _ _ _ _ _ hagA hvcA
      (memEvalExpr_lit _ _ _ _)

/-! ## Memory body hits -/

/-- One body iteration on memory, equal-head leg: both reads agree
    with the value side, the `une` is false, and only the `i` cursor
    bumps (memory untouched). -/
theorem memMismatchBody_bump (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lb : List (BitVec 32)) (i : Nat)
    (iB : BitVec 64) (x y : BitVec 32)
    (aa ab ta tb : Nat) (na nb : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_b : layoutLookup π "b" = some (ab, tb))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nb :: lb⟩)
    (hna : na = BitVec.ofNat 32 la.length)
    (hnb : nb = BitVec.ofNat 32 lb.length)
    (hiN : iB.toNat = i)
    (hla64 : la.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hltA : i < la.length)
    (hgetA : la[i]? = some x) (hgetB : lb[i]? = some y)
    (hdrop : (x != y) = false) :
    ∃ ρ', memEvalProgStmt prog F vecMismatchBody ρ m π =
      .ok ((ρ', m, π), .fellThrough) ∧
      envLookup ρ' "i" = some (.u64 (iB + 1)) ∧
      (iB + 1).toNat = i + 1 ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "b" = some (.stdVecVal lb) := by
  have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have hiVarA : memEvalExpr (.var "i") ρ m π = evalExpr (.var "i") ρ :=
    memEvalExpr_var _ _ _ _
  have hgetA' : la[iB.toNat]? = some x := by rw [hiN]; exact hgetA
  have hgetB' : lb[iB.toNat]? = some y := by rw [hiN]; exact hgetB
  have hmemAi : memLoad m aa ta (iB.toNat + 1) = .ok x :=
    memLoad_cellsAt m aa ta (iB.toNat + 1) (na :: la) x hmem_a
      (by rw [List.getElem?_cons_succ]; exact hgetA')
  have hagA : memEvalExpr (.stdVecAt "a" (.var "i")) ρ m π =
      evalExpr (.stdVecAt "a" (.var "i")) ρ :=
    memEvalExpr_stdVecAt_hit "a" (.var "i") ρ m π la iB x aa ta
      hlay_a ha hiVarA hiVar hmemAi hgetA'
  have hatA : evalExpr (.stdVecAt "a" (.var "i")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hiVar hgetA'
  have hmemBi : memLoad m ab tb (iB.toNat + 1) = .ok y :=
    memLoad_cellsAt m ab tb (iB.toNat + 1) (nb :: lb) y hmem_b
      (by rw [List.getElem?_cons_succ]; exact hgetB')
  have hagB : memEvalExpr (.stdVecAt "b" (.var "i")) ρ m π =
      evalExpr (.stdVecAt "b" (.var "i")) ρ :=
    memEvalExpr_stdVecAt_hit "b" (.var "i") ρ m π lb iB y ab tb
      hlay_b hb hiVarA hiVar hmemBi hgetB'
  have hatB : evalExpr (.stdVecAt "b" (.var "i")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hb hiVar hgetB'
  have huneV : evalExpr
      (.une (.stdVecAt "a" (.var "i")) (.stdVecAt "b" (.var "i")))
      ρ = .ok (.b false) := by
    have e := evalExpr_une_i32 _ _ _ _ _ hatA hatB
    rwa [hdrop] at e
  have huneM : memEvalExpr
      (.une (.stdVecAt "a" (.var "i")) (.stdVecAt "b" (.var "i")))
      ρ m π = .ok (.b false) :=
    (memEvalExpr_une_agree _ _ _ _ _ hagA hagB).trans huneV
  have hskipM : memEvalProgStmt prog F .skip ρ m π =
      .ok ((ρ, m, π), .fellThrough) := by
    cases F <;> simp [memEvalProgStmt, memEvalStmtFuel,
      memEvalStmtZero, memEvalStmtWith]
  have hif : memEvalProgStmt prog F
      (.if_ (.une (.stdVecAt "a" (.var "i"))
        (.stdVecAt "b" (.var "i")))
        (.return_ (.var "i")) .skip) ρ m π =
      .ok ((ρ, m, π), .fellThrough) :=
    (memEvalProgStmt_if_false _ _ _ _ _ _ _ _ huneM).trans hskipM
  have hevI : evalExpr (.uadd (.var "i")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρ =
      .ok (.u64 (iB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hiVar (by simp [evalExpr, litVal])
  have hevIM : memEvalExpr
      (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ m π =
      .ok (.u64 (iB + 1)) :=
    (memEvalExpr_uadd_agree (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))
      ρ m π (memEvalExpr_var _ _ _ _)
      (memEvalExpr_lit _ _ _ _)).trans hevI
  obtain ⟨ρ', hu⟩ := envUpdate_some_of_lookup ρ "i"
    (.u64 iB) (.u64 (iB + 1)) hi
  have hstep := memRevAssign prog F "i"
    (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ m π
    (.u64 (iB + 1)) ρ' hevIM hevI hu
  have hiN' : (iB + 1).toNat = i + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hiN]
    exact Nat.mod_eq_of_lt (by omega)
  have hbody : memEvalProgStmt prog F vecMismatchBody ρ m π =
      .ok ((ρ', m, π), .fellThrough) := by
    simp only [vecMismatchBody]
    rw [memEvalProgStmt_seq_fallthrough prog F _ _ ρ m π ρ m π hif]
    exact hstep
  refine ⟨ρ', hbody, ?_, hiN', ?_, ?_⟩
  · rw [envLookup_update_hit _ _ _ _ hu]
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "i" by decide) hu]
    exact ha
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("b" : String) ≠ "i" by decide) hu]
    exact hb

/-- One body iteration on memory, unequal-head leg: both reads agree
    with the value side, the `une` is true, and the body returns the
    cursor; the trailing bump never runs. -/
theorem memMismatchBody_return (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lb : List (BitVec 32)) (i : Nat)
    (iB : BitVec 64) (x y : BitVec 32)
    (aa ab ta tb : Nat) (na nb : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_b : layoutLookup π "b" = some (ab, tb))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nb :: lb⟩)
    (hiN : iB.toNat = i)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hgetA : la[i]? = some x) (hgetB : lb[i]? = some y)
    (htru : (x != y) = true) :
    memEvalProgStmt prog F vecMismatchBody ρ m π =
      .ok ((ρ, m, π), .returned (.u64 iB)) := by
  have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have hiVarA : memEvalExpr (.var "i") ρ m π = evalExpr (.var "i") ρ :=
    memEvalExpr_var _ _ _ _
  have hgetA' : la[iB.toNat]? = some x := by rw [hiN]; exact hgetA
  have hgetB' : lb[iB.toNat]? = some y := by rw [hiN]; exact hgetB
  have hmemAi : memLoad m aa ta (iB.toNat + 1) = .ok x :=
    memLoad_cellsAt m aa ta (iB.toNat + 1) (na :: la) x hmem_a
      (by rw [List.getElem?_cons_succ]; exact hgetA')
  have hagA : memEvalExpr (.stdVecAt "a" (.var "i")) ρ m π =
      evalExpr (.stdVecAt "a" (.var "i")) ρ :=
    memEvalExpr_stdVecAt_hit "a" (.var "i") ρ m π la iB x aa ta
      hlay_a ha hiVarA hiVar hmemAi hgetA'
  have hatA : evalExpr (.stdVecAt "a" (.var "i")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hiVar hgetA'
  have hmemBi : memLoad m ab tb (iB.toNat + 1) = .ok y :=
    memLoad_cellsAt m ab tb (iB.toNat + 1) (nb :: lb) y hmem_b
      (by rw [List.getElem?_cons_succ]; exact hgetB')
  have hagB : memEvalExpr (.stdVecAt "b" (.var "i")) ρ m π =
      evalExpr (.stdVecAt "b" (.var "i")) ρ :=
    memEvalExpr_stdVecAt_hit "b" (.var "i") ρ m π lb iB y ab tb
      hlay_b hb hiVarA hiVar hmemBi hgetB'
  have hatB : evalExpr (.stdVecAt "b" (.var "i")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hb hiVar hgetB'
  have huneV : evalExpr
      (.une (.stdVecAt "a" (.var "i")) (.stdVecAt "b" (.var "i")))
      ρ = .ok (.b true) := by
    have e := evalExpr_une_i32 _ _ _ _ _ hatA hatB
    rwa [htru] at e
  have huneM : memEvalExpr
      (.une (.stdVecAt "a" (.var "i")) (.stdVecAt "b" (.var "i")))
      ρ m π = .ok (.b true) :=
    (memEvalExpr_une_agree _ _ _ _ _ hagA hagB).trans huneV
  have hiVarM : memEvalExpr (.var "i") ρ m π = .ok (.u64 iB) := by
    rw [hiVarA]; exact hiVar
  have hretM : memEvalProgStmt prog F (.return_ (.var "i")) ρ m π =
      .ok ((ρ, m, π), .returned (.u64 iB)) :=
    memEvalProgStmt_return prog F _ ρ m π _ hiVarM
  have hifM : memEvalProgStmt prog F
      (.if_ (.une (.stdVecAt "a" (.var "i"))
        (.stdVecAt "b" (.var "i")))
        (.return_ (.var "i")) .skip) ρ m π =
      .ok ((ρ, m, π), .returned (.u64 iB)) :=
    (memEvalProgStmt_if_true _ _ _ _ _ _ _ _ huneM).trans hretM
  have hseq : memEvalProgStmt prog F vecMismatchBody ρ m π =
      .ok ((ρ, m, π), .returned (.u64 iB)) := by
    simp only [vecMismatchBody]
    exact memEvalProgStmt_seq_returned prog F _ _ ρ m π
      ρ m π (.u64 iB) hifM
  exact hseq

/-! ## Memory loop agreement -/

/-- Memory loop agreement: the loop either falls through having
    advanced the cursor, or returns the position early. Memory is
    untouched throughout. -/
theorem memMismatchLoop_ok (prog : Prog) (F G : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lb : List (BitVec 32)) (i r : Nat) (iB : BitVec 64)
    (aa ab ta tb : Nat) (na nb : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_b : layoutLookup π "b" = some (ab, tb))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nb :: lb⟩)
    (hna : na = BitVec.ofNat 32 la.length)
    (hnb : nb = BitVec.ofNat 32 lb.length)
    (hiN : iB.toNat = i)
    (hla64 : la.length < 2 ^ 64) (hlb64 : lb.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hF : (la.length - i) + (lb.length - i) ≤ F)
    (hG : (la.length - i) + (lb.length - i) ≤ G)
    (hfwd : mismatchFwd la lb G i = .ok r) :
    ∃ ρ' m' out, memEvalProgStmt prog F vecMismatchLoop ρ m π =
      .ok ((ρ', m', π), out) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "b" = some (.stdVecVal lb) ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = r ∧
        (out = .fellThrough ∨ out = .returned (.u64 iB'))) ∧
      memFind m' aa = some ⟨ta, true, na :: la⟩ ∧
      memFind m' ab = some ⟨tb, true, nb :: lb⟩ := by
  induction F generalizing G ρ m i iB r with
  | zero =>
    have hgeA : la.length ≤ i := by omega
    have hgeB : lb.length ≤ i := by omega
    have hguardV : evalExpr mismatchGuard ρ = .ok (.b false) :=
      mismatchGuard_eval_falseA ρ la lb i iB hiN ha hi hla64 hgeA
    have hguardM : memEvalExpr mismatchGuard ρ m π = .ok (.b false) :=
      (memMismatchGuard_agree ρ m π la lb i iB aa ab ta tb na nb
        hlay_a hlay_b hmem_a hmem_b hna hnb hiN hla64 hlb64
        ha hb hi).trans hguardV
    have hexit : memEvalProgStmt prog 0 vecMismatchLoop ρ m π =
        .ok ((ρ, m, π), .fellThrough) :=
      memEvalProgStmt_while_false prog 0 _ _ _ _ _ hguardM
    have hdropA : la.drop i = [] := by
      rw [List.drop_eq_nil_of_le]
      omega
    have e1 := mismatchFwd_eq la lb G i
      (by simp only [List.length_drop]; exact hG)
    rw [hdropA, firstDiff_nil_left] at e1
    have hir : r = i := by
      have h := hfwd.symm.trans e1
      simpa using h
    exact ⟨ρ, m, .fellThrough, hexit, ha, hb, ⟨iB, hi, by omega, Or.inl rfl⟩, hmem_a, hmem_b⟩
  | succ F ih =>
    by_cases hltA : i < la.length
    · by_cases hltB : i < lb.length
      · obtain ⟨x, hgetA⟩ : ∃ x, la[i]? = some x :=
          ⟨la[i]'hltA, List.getElem?_eq_getElem hltA⟩
        obtain ⟨y, hgetB⟩ : ∃ y, lb[i]? = some y :=
          ⟨lb[i]'hltB, List.getElem?_eq_getElem hltB⟩
        have hguardV : evalExpr mismatchGuard ρ = .ok (.b true) :=
          mismatchGuard_eval_true ρ la lb i iB hiN ha hb hi
            hla64 hlb64 hltA hltB
        have hguardM : memEvalExpr mismatchGuard ρ m π =
            .ok (.b true) :=
          (memMismatchGuard_agree ρ m π la lb i iB aa ab ta tb na nb
            hlay_a hlay_b hmem_a hmem_b hna hnb hiN hla64 hlb64
            ha hb hi).trans hguardV
        by_cases hne : x != y
        · -- Unequal heads: return the cursor.
          have htru : (x != y) = true := hne
          have hbodyret : memEvalProgStmt prog F vecMismatchBody ρ m π =
              .ok ((ρ, m, π), .returned (.u64 iB)) :=
            memMismatchBody_return prog F ρ m π la lb i iB x y
              aa ab ta tb na nb hlay_a hlay_b hmem_a hmem_b hiN
              ha hb hi hgetA hgetB htru
          have hdone : memEvalProgStmt prog (F + 1) vecMismatchLoop
              ρ m π = .ok ((ρ, m, π), .returned (.u64 iB)) := by
            cir_unfold_prog (vecMismatchLoop, prog, F, hguardM, hbodyret)
          have e1 := mismatchFwd_eq la lb G i
            (by simp only [List.length_drop]; exact hG)
          rw [drop_eq_cons_of_getElem hgetA, drop_eq_cons_of_getElem hgetB,
            firstDiff_cons, ite_eq_left hne] at e1
          have hir : r = i := by
            have h := hfwd.symm.trans e1
            simpa using h
          exact ⟨ρ, m, .returned (.u64 iB), hdone, ha, hb, ⟨iB, hi, by omega, Or.inr rfl⟩, hmem_a, hmem_b⟩
        · -- Equal heads: bump and continue.
          have hdrop : (x != y) = false := by simpa using hne
          cir_fuel_step (F, G,
            (la.length - (i + 1)) + (lb.length - (i + 1)))
          obtain ⟨ρ₁, hbody, hiB₁, hiN₁, ha₁, hb₁⟩ :=
            memMismatchBody_bump prog F ρ m π la lb i iB x y
              aa ab ta tb na nb hlay_a hlay_b hmem_a hmem_b hna hnb
              hiN hla64 ha hb hi hltA hgetA hgetB hdrop
          have e1 := mismatchFwd_eq la lb (G' + 1) i
            (by simp only [List.length_drop]; exact hG)
          rw [drop_eq_cons_of_getElem hgetA, drop_eq_cons_of_getElem hgetB,
            firstDiff_cons, ite_eq_right hne] at e1
          have e2 := mismatchFwd_eq la lb G' (i + 1)
            (by simp only [List.length_drop]; exact hG')
          have hfwd' : mismatchFwd la lb G' (i + 1) = .ok r := by
            rw [e2]
            have h := hfwd.symm.trans e1
            have hrr : r = (i + 1) +
                firstDiff (la.drop (i + 1)) (lb.drop (i + 1)) := by
              simpa [Nat.add_assoc, Nat.add_comm,
                Nat.add_left_comm] using h
            rw [hrr]
          have ihapp :=
            ih G' ρ₁ m (i + 1) r (iB + 1)
              hmem_a hmem_b hiN₁ ha₁ hb₁ hiB₁ hF' hG' hfwd'
          obtain ⟨ρ', ih1⟩ := ihapp
          obtain ⟨m', ih2⟩ := ih1
          obtain ⟨out, hloop, ha', hb', ih3, hmem_a', hmem_b'⟩ := ih2
          cases ih3 with
          | intro iB' ih4 =>
            cases ih4 with
            | intro hiB' ih5 =>
              cases ih5 with
              | intro hr' hout =>
          refine ⟨ρ', m', out, ?_, ha', hb',
            ⟨iB', hiB', hr', hout⟩, hmem_a', hmem_b'⟩
          have hwhile : memEvalProgStmt prog (F + 1) vecMismatchLoop
              ρ m π =
              memEvalProgStmt prog F vecMismatchLoop ρ₁ m π := by
            cir_unfold_prog (vecMismatchLoop, prog, F, hguardM, hbody)
          rw [hwhile]
          exact hloop
      · -- `b` exhausted: exit, tail returns `i`.
        have hgeB : lb.length ≤ i := by omega
        have hguardV : evalExpr mismatchGuard ρ = .ok (.b false) :=
          mismatchGuard_eval_falseB ρ la lb i iB hiN ha hb hi
            hla64 hlb64 hltA hgeB
        have hguardM : memEvalExpr mismatchGuard ρ m π =
            .ok (.b false) :=
          (memMismatchGuard_agree ρ m π la lb i iB aa ab ta tb na nb
            hlay_a hlay_b hmem_a hmem_b hna hnb hiN hla64 hlb64
            ha hb hi).trans hguardV
        have hexit : memEvalProgStmt prog (F + 1) vecMismatchLoop ρ m π =
            .ok ((ρ, m, π), .fellThrough) :=
          memEvalProgStmt_while_false prog (F + 1) _ _ _ _ _ hguardM
        obtain ⟨x, hgetA⟩ : ∃ x, la[i]? = some x :=
          ⟨la[i]'hltA, List.getElem?_eq_getElem hltA⟩
        have hdropB : lb.drop i = [] := by
          rw [List.drop_eq_nil_of_le]
          omega
        have e1 := mismatchFwd_eq la lb G i
          (by simp only [List.length_drop]; exact hG)
        rw [hdropB, firstDiff_nil_right] at e1
        have hir : r = i := by
          have h := hfwd.symm.trans e1
          simpa using h
        exact ⟨ρ, m, .fellThrough, hexit, ha, hb, ⟨iB, hi, by omega, Or.inl rfl⟩, hmem_a, hmem_b⟩
    · -- `a` exhausted: exit, tail returns `i`.
      have hgeA : la.length ≤ i := by omega
      have hguardV : evalExpr mismatchGuard ρ = .ok (.b false) :=
        mismatchGuard_eval_falseA ρ la lb i iB hiN ha hi hla64 hgeA
      have hguardM : memEvalExpr mismatchGuard ρ m π =
          .ok (.b false) :=
        (memMismatchGuard_agree ρ m π la lb i iB aa ab ta tb na nb
          hlay_a hlay_b hmem_a hmem_b hna hnb hiN hla64 hlb64
          ha hb hi).trans hguardV
      have hexit : memEvalProgStmt prog (F + 1) vecMismatchLoop ρ m π =
          .ok ((ρ, m, π), .fellThrough) :=
        memEvalProgStmt_while_false prog (F + 1) _ _ _ _ _ hguardM
      have hdropA : la.drop i = [] := by
        rw [List.drop_eq_nil_of_le]
        omega
      have e1 := mismatchFwd_eq la lb G i
        (by simp only [List.length_drop]; exact hG)
      rw [hdropA, firstDiff_nil_left] at e1
      have hir : r = i := by
        have h := hfwd.symm.trans e1
        simpa using h
      exact ⟨ρ, m, .fellThrough, hexit, ha, hb, ⟨iB, hi, by omega, Or.inl rfl⟩, hmem_a, hmem_b⟩

/-! ## Value entry -/

/-- Value entry: prelude binds the cursor, the loop runs, and either
    the tail return or the early return delivers the forward value. -/
theorem evalProgFunc_vecMismatch_ok (F : Nat)
    (la lb : List (BitVec 32)) (r : Nat)
    (hla64 : la.length < 2 ^ 64) (hlb64 : lb.length < 2 ^ 64)
    (hF : la.length + lb.length + 1 ≤ F)
    (hfwd : mismatchFwd la lb (la.length + lb.length + 1) 0 = .ok r) :
    evalProgFunc vecMismatchProg F vecMismatchFunc
      [.stdVecVal la, .stdVecVal lb] =
      .ok (.u64 (BitVec.ofNat 64 r)) := by
  have hbind : bindArgs vecMismatchFunc.args
      [.stdVecVal la, .stdVecVal lb] =
      some [("a", .stdVecVal la), ("b", .stdVecVal lb)] := rfl
  have hbody : vecMismatchFunc.body =
      (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq vecMismatchLoop
          (.return_ (.var "i")))) := rfl
  have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal la), ("b", .stdVecVal lb)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletI := revLet vecMismatchProg F "i" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("a", .stdVecVal la), ("b", .stdVecVal lb)]
    (.u64 (BitVec.ofNat 64 0)) hlitV
  have henv : envExtend [("a", .stdVecVal la), ("b", .stdVecVal lb)]
      "i" (.u64 (BitVec.ofNat 64 0)) =
      mkMismatchEnv la lb (BitVec.ofNat 64 0) := rfl
  have hv0N : (BitVec.ofNat 64 0).toNat = 0 := by
    rw [BitVec.toNat_ofNat]
  have ha₃ : envLookup (envExtend [("a", .stdVecVal la),
      ("b", .stdVecVal lb)] "i" (.u64 (BitVec.ofNat 64 0))) "a" =
      some (.stdVecVal la) := by
    rw [henv]; exact mkMismatchEnv_a _ _ _
  have hb₃ : envLookup (envExtend [("a", .stdVecVal la),
      ("b", .stdVecVal lb)] "i" (.u64 (BitVec.ofNat 64 0))) "b" =
      some (.stdVecVal lb) := by
    rw [henv]; exact mkMismatchEnv_b _ _ _
  have hi₃ : envLookup (envExtend [("a", .stdVecVal la),
      ("b", .stdVecVal lb)] "i" (.u64 (BitVec.ofNat 64 0))) "i" =
      some (.u64 (BitVec.ofNat 64 0)) := by
    rw [henv]; exact mkMismatchEnv_i _ _ _
  have hF' : (la.length - 0) + (lb.length - 0) ≤ F := by omega
  have hG' : (la.length - 0) + (lb.length - 0) ≤
      la.length + lb.length + 1 := by omega
  obtain ⟨ρ', out, hloop, ha', hb', iB', hiB', hr', hout⟩ :=
    vecMismatchLoop_ok F (la.length + lb.length + 1) vecMismatchProg
      (envExtend [("a", .stdVecVal la), ("b", .stdVecVal lb)]
        "i" (.u64 (BitVec.ofNat 64 0)))
      la lb 0 r (BitVec.ofNat 64 0) hv0N hla64 hlb64
      ha₃ hb₃ hi₃ hF' hG' hfwd
  have hrw : r = firstDiff la lb := by
    have e1 := mismatchFwd_eq la lb (la.length + lb.length + 1) 0
      (by simp only [List.length_drop]; omega)
    have h := hfwd.symm.trans e1
    simpa using h
  have hr64 : r < 2 ^ 64 := by
    have hle := firstDiff_le_left la lb
    omega
  have hiB'eq : iB' = BitVec.ofNat 64 r := by
    apply BitVec.eq_of_toNat_eq
    rw [hr', BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt hr64).symm
  subst hiB'eq
  have hevI' : evalExpr (.var "i") ρ' =
      .ok (.u64 (BitVec.ofNat 64 r)) :=
    evalExpr_var_hit _ _ _ hiB'
  simp only [evalProgFunc, hbind, hbody]
  rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletI]
  cases hout with
  | inl hfall =>
    rw [hfall] at hloop
    have hret := evalProgStmt_return vecMismatchProg F (.var "i") ρ'
      (.u64 (BitVec.ofNat 64 r)) hevI'
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hloop, hret]
  | inr hret' =>
    rw [hret'] at hloop
    have hseq : evalProgStmt vecMismatchProg F
        (.seq vecMismatchLoop (.return_ (.var "i")))
        (envExtend [("a", .stdVecVal la), ("b", .stdVecVal lb)]
          "i" (.u64 (BitVec.ofNat 64 0))) =
        .ok (ρ', .returned (.u64 (BitVec.ofNat 64 r))) :=
      evalProgStmt_seq_returned vecMismatchProg F _ _ _ _ _ hloop
    rw [hseq]

/-! ## Memory entry -/

/-- Memory entry: same prelude on the two pinned blocks, the memory
    loop, and the `i` return. -/
theorem memEvalProgFunc_vecMismatch_ok (F : Nat)
    (la lb : List (BitVec 32)) (r : Nat)
    (hla64 : la.length < 2 ^ 64) (hlb64 : lb.length < 2 ^ 64)
    (hF : la.length + lb.length + 1 ≤ F)
    (hfwd : mismatchFwd la lb (la.length + lb.length + 1) 0 = .ok r) :
    memEvalProgFunc vecMismatchProg F vecMismatchFunc
      [.stdVecVal la, .stdVecVal lb] =
      .ok (.u64 (BitVec.ofNat 64 r)) := by
  have hbind := bindMemArgs_vecMismatch la lb
  have hbody : vecMismatchFunc.body =
      (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq vecMismatchLoop
          (.return_ (.var "i")))) := rfl
  have hmem_a₀ : memFind
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lb.length) :: lb⟩)], []⟩ 1 =
      some ⟨1, true, (BitVec.ofNat 32 la.length) :: la⟩ :=
    memFind_cons_hit _ _ _ _ _
  have hmem_b₀ : memFind
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lb.length) :: lb⟩)], []⟩ 0 =
      some ⟨0, true, (BitVec.ofNat 32 lb.length) :: lb⟩ := by
    rw [memFind_cons_miss _ _ _ _ _ _ (by decide : (0 : Nat) ≠ 1)]
    exact memFind_cons_hit _ _ _ _ _
  have hlay_a₀ : layoutLookup [("a", 1, 1), ("b", 0, 0)]
      "a" = some (1, 1) := by simp [layoutLookup]
  have hlay_b₀ : layoutLookup [("a", 1, 1), ("b", 0, 0)]
      "b" = some (0, 0) := by simp [layoutLookup]
  have hlitM : memEvalExpr
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal la), ("b", .stdVecVal lb)]
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lb.length) :: lb⟩)], []⟩
      [("a", 1, 1), ("b", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal la), ("b", .stdVecVal lb)] :=
    memEvalExpr_lit _ _ _ _
  have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal la), ("b", .stdVecVal lb)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletI := memRevLet vecMismatchProg F "i" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("a", .stdVecVal la), ("b", .stdVecVal lb)]
    ⟨2, [(1, ⟨1, true,
      (BitVec.ofNat 32 la.length) :: la⟩),
      (0, ⟨0, true,
      (BitVec.ofNat 32 lb.length) :: lb⟩)], []⟩
    [("a", 1, 1), ("b", 0, 0)]
    (.u64 (BitVec.ofNat 64 0))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) (by intro h; cases h) hlitM hlitV
  have henv : envExtend [("a", .stdVecVal la), ("b", .stdVecVal lb)]
      "i" (.u64 (BitVec.ofNat 64 0)) =
      mkMismatchEnv la lb (BitVec.ofNat 64 0) := rfl
  have hv0N : (BitVec.ofNat 64 0).toNat = 0 := by
    rw [BitVec.toNat_ofNat]
  have ha₃ : envLookup (envExtend [("a", .stdVecVal la),
      ("b", .stdVecVal lb)] "i" (.u64 (BitVec.ofNat 64 0))) "a" =
      some (.stdVecVal la) := by
    rw [henv]; exact mkMismatchEnv_a _ _ _
  have hb₃ : envLookup (envExtend [("a", .stdVecVal la),
      ("b", .stdVecVal lb)] "i" (.u64 (BitVec.ofNat 64 0))) "b" =
      some (.stdVecVal lb) := by
    rw [henv]; exact mkMismatchEnv_b _ _ _
  have hi₃ : envLookup (envExtend [("a", .stdVecVal la),
      ("b", .stdVecVal lb)] "i" (.u64 (BitVec.ofNat 64 0))) "i" =
      some (.u64 (BitVec.ofNat 64 0)) := by
    rw [henv]; exact mkMismatchEnv_i _ _ _
  have hF' : (la.length - 0) + (lb.length - 0) ≤ F := by omega
  have hG' : (la.length - 0) + (lb.length - 0) ≤
      la.length + lb.length + 1 := by omega
  have ihapp :=
    memMismatchLoop_ok vecMismatchProg F (la.length + lb.length + 1)
      (envExtend [("a", .stdVecVal la), ("b", .stdVecVal lb)]
        "i" (.u64 (BitVec.ofNat 64 0)))
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lb.length) :: lb⟩)], []⟩
      [("a", 1, 1), ("b", 0, 0)]
      la lb 0 r (BitVec.ofNat 64 0) 1 0 1 0
      (BitVec.ofNat 32 la.length) (BitVec.ofNat 32 lb.length)
      hlay_a₀ hlay_b₀ hmem_a₀ hmem_b₀ rfl rfl hv0N hla64 hlb64
      ha₃ hb₃ hi₃ hF' hG' hfwd
  obtain ⟨ρ', m', out, hloop, ha', hb',
      ⟨iB', hiB', hr', hout⟩, hmem_a', hmem_b'⟩ := ihapp
  have hrw : r = firstDiff la lb := by
    have e1 := mismatchFwd_eq la lb (la.length + lb.length + 1) 0
      (by simp only [List.length_drop]; omega)
    have h := hfwd.symm.trans e1
    simpa using h
  have hr64 : r < 2 ^ 64 := by
    have hle := firstDiff_le_left la lb
    omega
  have hiB'eq : iB' = BitVec.ofNat 64 r := by
    apply BitVec.eq_of_toNat_eq
    rw [hr', BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt hr64).symm
  subst hiB'eq
  have hevI'V : evalExpr (.var "i") ρ' =
      .ok (.u64 (BitVec.ofNat 64 r)) :=
    evalExpr_var_hit _ _ _ hiB'
  have hevI' : memEvalExpr (.var "i") ρ' m' [("a", 1, 1), ("b", 0, 0)] =
      .ok (.u64 (BitVec.ofNat 64 r)) :=
    (memEvalExpr_var _ _ _ _).trans hevI'V
  have hret := memEvalProgStmt_return vecMismatchProg F
    (.var "i") ρ' m' [("a", 1, 1), ("b", 0, 0)]
    (.u64 (BitVec.ofNat 64 r)) hevI'
  simp only [memEvalProgFunc, hbind, hbody]
  rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletI]
  cases hout with
  | inl hfall =>
    rw [hfall] at hloop
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hloop,
      hret]
  | inr hret' =>
    rw [hret'] at hloop
    have hseq : memEvalProgStmt vecMismatchProg F
        (.seq vecMismatchLoop (.return_ (.var "i")))
        (envExtend [("a", .stdVecVal la), ("b", .stdVecVal lb)]
          "i" (.u64 (BitVec.ofNat 64 0)))
        ⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 la.length) :: la⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lb.length) :: lb⟩)], []⟩
        [("a", 1, 1), ("b", 0, 0)] =
        .ok ((ρ', m', [("a", 1, 1), ("b", 0, 0)]),
          .returned (.u64 (BitVec.ofNat 64 r))) :=
      memEvalProgStmt_seq_returned vecMismatchProg F _ _ _ _ _ _ _ _
        (.u64 (BitVec.ofNat 64 r)) hloop
    rw [hseq]

/-! ## Transfer (`memEval = Eval`) -/

/-- Transfer for `vec_mismatch`: memory evaluation agrees with value
    evaluation on a successful scan. -/
theorem memTransferProg_vecMismatch_ok (F : Nat)
    (la lb : List (BitVec 32)) (r : Nat)
    (hla64 : la.length < 2 ^ 64) (hlb64 : lb.length < 2 ^ 64)
    (hF : la.length + lb.length + 1 ≤ F)
    (hfwd : mismatchFwd la lb (la.length + lb.length + 1) 0 = .ok r)
    (_h : oracleNoalias vecMismatchFunc
      [.stdVecVal la, .stdVecVal lb]) :
    memEvalProgFunc vecMismatchProg F vecMismatchFunc
      [.stdVecVal la, .stdVecVal lb] =
      evalProgFunc vecMismatchProg F vecMismatchFunc
        [.stdVecVal la, .stdVecVal lb] := by
  rw [memEvalProgFunc_vecMismatch_ok F la lb r
    hla64 hlb64 hF hfwd,
    evalProgFunc_vecMismatch_ok F la lb r
    hla64 hlb64 hF hfwd]

/-! ## Closing spec (against the independent oracle) -/

/-- Closing mismatch contract (P2-M19): a successful run returns the
    oracle position — the first index where the inputs differ, or the
    shorter length when one is a prefix of the other. -/
theorem evalProgFunc_vecMismatch_spec_ok (F : Nat)
    (la lb : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hlb64 : lb.length < 2 ^ 64)
    (hF : la.length + lb.length + 1 ≤ F) :
    evalProgFunc vecMismatchProg F vecMismatchFunc
      [.stdVecVal la, .stdVecVal lb] =
      .ok (.u64 (BitVec.ofNat 64 (firstDiff la lb))) := by
  have hfwd := mismatchFwd_eq la lb (la.length + lb.length + 1) 0
    (by simp only [List.length_drop]; omega)
  have heval := evalProgFunc_vecMismatch_ok F la lb _ hla64 hlb64 hF hfwd
  simpa using heval
