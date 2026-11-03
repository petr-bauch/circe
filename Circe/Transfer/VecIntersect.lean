/-
Circe.Transfer.VecIntersect — mem transfer for sorted-range intersection
(`vec_intersect`, the `std::set_intersection` idiom; P2-M11).

Mem-level mirrors of the eval-level body equations in
`Circe.Emit.VecIntersect`: inline `stdVecAt` reads go through
`memEvalExpr_stdVecAt_hit` (length-word-skipping loads), the `tif`
guard through `memEvalExpr_tif_true/false` over two `ult` agreements,
the write store through `memRevVecSet`, and cursor bumps through
`memRevAssign`. The three blocks (two `sharedBorrow` inputs + one
`mutBorrow` record) pin reified snapshots; the loop re-inducts over
`(ρ, m, π)` with the forward equation threading (two fuels: program
fuel and forward fuel) plus the capacity invariant. Entries close
against the forward contract; the closing spec ties the `u64`
survivor count to the independent sorted-merge oracle
(`intersectOracle` in `Circe.Specs`: min-count multiplicity).
-/
import Circe.Transfer.VecReverse
import Circe.Emit.VecIntersect
import Circe.Specs

/-! ## Binding (closed form) -/

/-- Intersection binding pins three snapshots: the two shared-borrow
    inputs at addrs `2`/`1`, the mut-borrow record at addr `0`
    (tail-first allocation order). -/
theorem bindMemArgs_vecIntersect (la lb lo : List (BitVec 32)) :
    bindMemArgs vecIntersectFunc.args
      [.stdVecVal la, .stdVecVal lb, .stdVecVal lo] emptyMem =
      some ([("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)],
        ⟨3, [(2, ⟨2, true,
          (BitVec.ofNat 32 la.length) :: la⟩),
          (1, ⟨1, true,
          (BitVec.ofNat 32 lb.length) :: lb⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩,
        [("a", 2, 2), ("b", 1, 1), ("out", 0, 0)]) := by
  rfl

/-- Intersection footprint is three pairwise-disjoint singletons. -/
theorem oracleNoalias_vecIntersect (la lb lo : List (BitVec 32)) :
    oracleNoalias vecIntersectFunc
      [.stdVecVal la, .stdVecVal lb, .stdVecVal lo] := by
  have hb := bindMemArgs_vecIntersect la lb lo
  have hn : LayoutNoAlias [("a", 2, 2), ("b", 1, 1), ("out", 0, 0)] := by
    simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-! ## Guard agreement (memory/eval) -/

/-- The `tif` guard agrees on memory: both `ult` legs read through
    their length words, and whichever branch the value side takes,
    the memory side follows. -/
theorem memIntersectGuard_agree
    (ρ : Env) (m : Mem) (π : Layout)
    (la lb : List (BitVec 32)) (i j : Nat)
    (iB jB : BitVec 64)
    (aa ab : Nat) (ta tb : Nat) (na nb : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_b : layoutLookup π "b" = some (ab, tb))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nb :: lb⟩)
    (hna : na = BitVec.ofNat 32 la.length)
    (hnb : nb = BitVec.ofNat 32 lb.length)
    (hiN : iB.toNat = i) (hjN : jB.toNat = j)
    (hla64 : la.length < 2 ^ 64) (hlb64 : lb.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hj : envLookup ρ "j" = some (.u64 jB)) :
    memEvalExpr intersectGuard ρ m π = evalExpr intersectGuard ρ := by
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
  have hagB : memEvalExpr (.ult (.var "j") (.stdVecLen "b")) ρ m π =
      evalExpr (.ult (.var "j") (.stdVecLen "b")) ρ :=
    memEvalExpr_ult_agree (.var "j") (.stdVecLen "b") ρ m π
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

/-- One body iteration on memory, advance-`i` branch: both reads
    agree with the value side, the first comparison holds, and only
    the `i` cursor bumps (memory untouched). -/
theorem memIntersectBody_advI (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lb lo : List (BitVec 32)) (i j w : Nat)
    (iB jB wB : BitVec 64) (x y : BitVec 32)
    (aa ab ao ta tb to : Nat) (na nb no : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_b : layoutLookup π "b" = some (ab, tb))
    (hlay_o : layoutLookup π "out" = some (ao, to))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nb :: lb⟩)
    (hmem_o : memFind m ao = some ⟨to, true, no :: lo⟩)
    (hna : na = BitVec.ofNat 32 la.length)
    (hnb : nb = BitVec.ofNat 32 lb.length)
    (hno : no = BitVec.ofNat 32 lo.length)
    (hiN : iB.toNat = i) (hjN : jB.toNat = j) (hwN : wB.toNat = w)
    (hla64 : la.length < 2 ^ 64) (hlb64 : lb.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hgetA : la[i]? = some x) (hgetB : lb[j]? = some y)
    (hltA : i < la.length) (hltB : j < lb.length)
    (hlt : (x.slt y) = true) :
    ∃ ρ', memEvalProgStmt prog F vecIntersectBody ρ m π =
      .ok ((ρ', m, π), .fellThrough) ∧
      envLookup ρ' "i" = some (.u64 (iB + 1)) ∧
      (iB + 1).toNat = i + 1 ∧
      envLookup ρ' "j" = some (.u64 jB) ∧
      envLookup ρ' "w" = some (.u64 wB) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "b" = some (.stdVecVal lb) ∧
      envLookup ρ' "out" = some (.stdVecVal lo) := by
  have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have hiVarA : memEvalExpr (.var "i") ρ m π = evalExpr (.var "i") ρ :=
    memEvalExpr_var _ _ _ _
  have hgetA' : la[iB.toNat]? = some x := by rw [hiN]; exact hgetA
  have hjVar : evalExpr (.var "j") ρ = .ok (.u64 jB) :=
    evalExpr_var_hit _ _ _ hj
  have hjVarA : memEvalExpr (.var "j") ρ m π = evalExpr (.var "j") ρ :=
    memEvalExpr_var _ _ _ _
  have hgetB' : lb[jB.toNat]? = some y := by rw [hjN]; exact hgetB
  have hmemAi : memLoad m aa ta (iB.toNat + 1) = .ok x :=
    memLoad_cellsAt m aa ta (iB.toNat + 1) (na :: la) x hmem_a
      (by rw [List.getElem?_cons_succ]; exact hgetA')
  have hagA : memEvalExpr (.stdVecAt "a" (.var "i")) ρ m π =
      evalExpr (.stdVecAt "a" (.var "i")) ρ :=
    memEvalExpr_stdVecAt_hit "a" (.var "i") ρ m π la iB x aa ta
      hlay_a ha hiVarA hiVar hmemAi hgetA'
  have hatA : evalExpr (.stdVecAt "a" (.var "i")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hiVar hgetA'
  have hmemBj : memLoad m ab tb (jB.toNat + 1) = .ok y :=
    memLoad_cellsAt m ab tb (jB.toNat + 1) (nb :: lb) y hmem_b
      (by rw [List.getElem?_cons_succ]; exact hgetB')
  have hagB : memEvalExpr (.stdVecAt "b" (.var "j")) ρ m π =
      evalExpr (.stdVecAt "b" (.var "j")) ρ :=
    memEvalExpr_stdVecAt_hit "b" (.var "j") ρ m π lb jB y ab tb
      hlay_b hb hjVarA hjVar hmemBj hgetB'
  have hatB : evalExpr (.stdVecAt "b" (.var "j")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hb hjVar hgetB'
  have hcmpV : evalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "b" (.var "j")))
      ρ = .ok (.b true) := by
    have e := evalExpr_slt_i32 _ _ _ _ _ hatA hatB
    rwa [hlt] at e
  have hcmpM : memEvalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "b" (.var "j")))
      ρ m π = .ok (.b true) :=
    (memEvalExpr_slt_agree _ _ _ _ _ hagA hagB).trans hcmpV
  have hevI : evalExpr (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ =
      .ok (.u64 (iB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hi) (by simp [evalExpr, litVal])
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
  have hifM : memEvalProgStmt prog F vecIntersectBody ρ m π =
      memEvalProgStmt prog F
        (.assign "i" (.uadd (.var "i")
          (.lit (.u64 (BitVec.ofNat 64 1))))) ρ m π := by
    simp only [vecIntersectBody]
    exact memEvalProgStmt_if_true _ _ _ _ _ _ _ _ hcmpM
  refine ⟨ρ', ?_, ?_, hiN', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hifM]; exact hstep
  · rw [envLookup_update_hit _ _ _ _ hu]
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("j" : String) ≠ "i" by decide) hu]
    exact hj
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "i" by decide) hu]
    exact hw
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "i" by decide) hu]
    exact ha
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("b" : String) ≠ "i" by decide) hu]
    exact hb
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "i" by decide) hu]
    exact hout

/-- One body iteration on memory, advance-`j` branch: the first
    comparison fails but the second holds, so only the `j` cursor
    bumps (memory untouched). -/
theorem memIntersectBody_advJ (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lb lo : List (BitVec 32)) (i j w : Nat)
    (iB jB wB : BitVec 64) (x y : BitVec 32)
    (aa ab ao ta tb to : Nat) (na nb no : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_b : layoutLookup π "b" = some (ab, tb))
    (hlay_o : layoutLookup π "out" = some (ao, to))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nb :: lb⟩)
    (hmem_o : memFind m ao = some ⟨to, true, no :: lo⟩)
    (hna : na = BitVec.ofNat 32 la.length)
    (hnb : nb = BitVec.ofNat 32 lb.length)
    (hno : no = BitVec.ofNat 32 lo.length)
    (hiN : iB.toNat = i) (hjN : jB.toNat = j) (hwN : wB.toNat = w)
    (hla64 : la.length < 2 ^ 64) (hlb64 : lb.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hgetA : la[i]? = some x) (hgetB : lb[j]? = some y)
    (hltA : i < la.length) (hltB : j < lb.length)
    (hge1 : (x.slt y) = false) (hlt2 : (y.slt x) = true) :
    ∃ ρ', memEvalProgStmt prog F vecIntersectBody ρ m π =
      .ok ((ρ', m, π), .fellThrough) ∧
      envLookup ρ' "i" = some (.u64 iB) ∧
      envLookup ρ' "j" = some (.u64 (jB + 1)) ∧
      (jB + 1).toNat = j + 1 ∧
      envLookup ρ' "w" = some (.u64 wB) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "b" = some (.stdVecVal lb) ∧
      envLookup ρ' "out" = some (.stdVecVal lo) := by
  have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have hiVarA : memEvalExpr (.var "i") ρ m π = evalExpr (.var "i") ρ :=
    memEvalExpr_var _ _ _ _
  have hgetA' : la[iB.toNat]? = some x := by rw [hiN]; exact hgetA
  have hjVar : evalExpr (.var "j") ρ = .ok (.u64 jB) :=
    evalExpr_var_hit _ _ _ hj
  have hjVarA : memEvalExpr (.var "j") ρ m π = evalExpr (.var "j") ρ :=
    memEvalExpr_var _ _ _ _
  have hgetB' : lb[jB.toNat]? = some y := by rw [hjN]; exact hgetB
  have hmemAi : memLoad m aa ta (iB.toNat + 1) = .ok x :=
    memLoad_cellsAt m aa ta (iB.toNat + 1) (na :: la) x hmem_a
      (by rw [List.getElem?_cons_succ]; exact hgetA')
  have hagA : memEvalExpr (.stdVecAt "a" (.var "i")) ρ m π =
      evalExpr (.stdVecAt "a" (.var "i")) ρ :=
    memEvalExpr_stdVecAt_hit "a" (.var "i") ρ m π la iB x aa ta
      hlay_a ha hiVarA hiVar hmemAi hgetA'
  have hatA : evalExpr (.stdVecAt "a" (.var "i")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hiVar hgetA'
  have hmemBj : memLoad m ab tb (jB.toNat + 1) = .ok y :=
    memLoad_cellsAt m ab tb (jB.toNat + 1) (nb :: lb) y hmem_b
      (by rw [List.getElem?_cons_succ]; exact hgetB')
  have hagB : memEvalExpr (.stdVecAt "b" (.var "j")) ρ m π =
      evalExpr (.stdVecAt "b" (.var "j")) ρ :=
    memEvalExpr_stdVecAt_hit "b" (.var "j") ρ m π lb jB y ab tb
      hlay_b hb hjVarA hjVar hmemBj hgetB'
  have hatB : evalExpr (.stdVecAt "b" (.var "j")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hb hjVar hgetB'
  have hcmp1V : evalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "b" (.var "j")))
      ρ = .ok (.b false) := by
    have e := evalExpr_slt_i32 _ _ _ _ _ hatA hatB
    rwa [hge1] at e
  have hcmp1M : memEvalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "b" (.var "j")))
      ρ m π = .ok (.b false) :=
    (memEvalExpr_slt_agree _ _ _ _ _ hagA hagB).trans hcmp1V
  have hcmp2V : evalExpr
      (.slt (.stdVecAt "b" (.var "j")) (.stdVecAt "a" (.var "i")))
      ρ = .ok (.b true) := by
    have e := evalExpr_slt_i32 _ _ _ _ _ hatB hatA
    rwa [hlt2] at e
  have hcmp2M : memEvalExpr
      (.slt (.stdVecAt "b" (.var "j")) (.stdVecAt "a" (.var "i")))
      ρ m π = .ok (.b true) :=
    (memEvalExpr_slt_agree _ _ _ _ _ hagB hagA).trans hcmp2V
  have hevJ : evalExpr (.uadd (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ =
      .ok (.u64 (jB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hj) (by simp [evalExpr, litVal])
  have hevJM : memEvalExpr
      (.uadd (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ m π =
      .ok (.u64 (jB + 1)) :=
    (memEvalExpr_uadd_agree (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))
      ρ m π (memEvalExpr_var _ _ _ _)
      (memEvalExpr_lit _ _ _ _)).trans hevJ
  obtain ⟨ρ', hu⟩ := envUpdate_some_of_lookup ρ "j"
    (.u64 jB) (.u64 (jB + 1)) hj
  have hstep := memRevAssign prog F "j"
    (.uadd (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ m π
    (.u64 (jB + 1)) ρ' hevJM hevJ hu
  have hjN' : (jB + 1).toNat = j + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hjN]
    exact Nat.mod_eq_of_lt (by omega)
  have hifM : memEvalProgStmt prog F vecIntersectBody ρ m π =
      memEvalProgStmt prog F
        (.assign "j" (.uadd (.var "j")
          (.lit (.u64 (BitVec.ofNat 64 1))))) ρ m π := by
    simp only [vecIntersectBody]
    rw [memEvalProgStmt_if_false _ _ _ _ _ _ _ _ hcmp1M,
      memEvalProgStmt_if_true _ _ _ _ _ _ _ _ hcmp2M]
  refine ⟨ρ', ?_, ?_, ?_, hjN', ?_, ?_, ?_, ?_⟩
  · rw [hifM]; exact hstep
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "j" by decide) hu]
    exact hi
  · rw [envLookup_update_hit _ _ _ _ hu]
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "j" by decide) hu]
    exact hw
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "j" by decide) hu]
    exact ha
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("b" : String) ≠ "j" by decide) hu]
    exact hb
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "j" by decide) hu]
    exact hout

/-- One body iteration on memory, write branch: neither head is
    smaller, so the common head records into `out` (lockstepped
    store) and all three cursors bump. -/
theorem memIntersectBody_write (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lb lo : List (BitVec 32)) (i j w : Nat)
    (iB jB wB : BitVec 64) (x y : BitVec 32)
    (aa ab ao ta tb to : Nat) (na nb no : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_b : layoutLookup π "b" = some (ab, tb))
    (hlay_o : layoutLookup π "out" = some (ao, to))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nb :: lb⟩)
    (hmem_o : memFind m ao = some ⟨to, true, no :: lo⟩)
    (hna : na = BitVec.ofNat 32 la.length)
    (hnb : nb = BitVec.ofNat 32 lb.length)
    (hno : no = BitVec.ofNat 32 lo.length)
    (haa : aa ≠ ao) (hab : ab ≠ ao)
    (hiN : iB.toNat = i) (hjN : jB.toNat = j) (hwN : wB.toNat = w)
    (hla64 : la.length < 2 ^ 64) (hlb64 : lb.length < 2 ^ 64)
    (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hgetA : la[i]? = some x) (hgetB : lb[j]? = some y)
    (hltA : i < la.length) (hltB : j < lb.length)
    (xO : BitVec 32) (hgetO : lo[w]? = some xO) (hwlt : w < lo.length)
    (hge1 : (x.slt y) = false) (hge2 : (y.slt x) = false) :
    ∃ ρ' m', memEvalProgStmt prog F vecIntersectBody ρ m π =
      .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "i" = some (.u64 (iB + 1)) ∧
      (iB + 1).toNat = i + 1 ∧
      envLookup ρ' "j" = some (.u64 (jB + 1)) ∧
      (jB + 1).toNat = j + 1 ∧
      envLookup ρ' "w" = some (.u64 (wB + 1)) ∧
      (wB + 1).toNat = w + 1 ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "b" = some (.stdVecVal lb) ∧
      envLookup ρ' "out" = some (.stdVecVal (lo.set w x)) ∧
      memFind m' aa = some ⟨ta, true, na :: la⟩ ∧
      memFind m' ab = some ⟨tb, true, nb :: lb⟩ ∧
      memFind m' ao = some ⟨to, true, no :: (lo.set w x)⟩ := by
  have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have hiVarA : memEvalExpr (.var "i") ρ m π = evalExpr (.var "i") ρ :=
    memEvalExpr_var _ _ _ _
  have hgetA' : la[iB.toNat]? = some x := by rw [hiN]; exact hgetA
  have hjVar : evalExpr (.var "j") ρ = .ok (.u64 jB) :=
    evalExpr_var_hit _ _ _ hj
  have hjVarA : memEvalExpr (.var "j") ρ m π = evalExpr (.var "j") ρ :=
    memEvalExpr_var _ _ _ _
  have hgetB' : lb[jB.toNat]? = some y := by rw [hjN]; exact hgetB
  have hmemAi : memLoad m aa ta (iB.toNat + 1) = .ok x :=
    memLoad_cellsAt m aa ta (iB.toNat + 1) (na :: la) x hmem_a
      (by rw [List.getElem?_cons_succ]; exact hgetA')
  have hagA : memEvalExpr (.stdVecAt "a" (.var "i")) ρ m π =
      evalExpr (.stdVecAt "a" (.var "i")) ρ :=
    memEvalExpr_stdVecAt_hit "a" (.var "i") ρ m π la iB x aa ta
      hlay_a ha hiVarA hiVar hmemAi hgetA'
  have hatA : evalExpr (.stdVecAt "a" (.var "i")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hiVar hgetA'
  have hatM : memEvalExpr (.stdVecAt "a" (.var "i")) ρ m π =
      .ok (.i32 x) := hagA.trans hatA
  have hmemBj : memLoad m ab tb (jB.toNat + 1) = .ok y :=
    memLoad_cellsAt m ab tb (jB.toNat + 1) (nb :: lb) y hmem_b
      (by rw [List.getElem?_cons_succ]; exact hgetB')
  have hagB : memEvalExpr (.stdVecAt "b" (.var "j")) ρ m π =
      evalExpr (.stdVecAt "b" (.var "j")) ρ :=
    memEvalExpr_stdVecAt_hit "b" (.var "j") ρ m π lb jB y ab tb
      hlay_b hb hjVarA hjVar hmemBj hgetB'
  have hatB : evalExpr (.stdVecAt "b" (.var "j")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hb hjVar hgetB'
  have hcmp1V : evalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "b" (.var "j")))
      ρ = .ok (.b false) := by
    have e := evalExpr_slt_i32 _ _ _ _ _ hatA hatB
    rwa [hge1] at e
  have hcmp1M : memEvalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "b" (.var "j")))
      ρ m π = .ok (.b false) :=
    (memEvalExpr_slt_agree _ _ _ _ _ hagA hagB).trans hcmp1V
  have hcmp2V : evalExpr
      (.slt (.stdVecAt "b" (.var "j")) (.stdVecAt "a" (.var "i")))
      ρ = .ok (.b false) := by
    have e := evalExpr_slt_i32 _ _ _ _ _ hatB hatA
    rwa [hge2] at e
  have hcmp2M : memEvalExpr
      (.slt (.stdVecAt "b" (.var "j")) (.stdVecAt "a" (.var "i")))
      ρ m π = .ok (.b false) :=
    (memEvalExpr_slt_agree _ _ _ _ _ hagB hagA).trans hcmp2V
  have hwVar : evalExpr (.var "w") ρ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw
  have hwVarA : memEvalExpr (.var "w") ρ m π = evalExpr (.var "w") ρ :=
    memEvalExpr_var _ _ _ _
  have hwVarM : memEvalExpr (.var "w") ρ m π = .ok (.u64 wB) :=
    hwVarA.trans hwVar
  have hgetO' : lo[wB.toNat]? = some xO := by rw [hwN]; exact hgetO
  have hlt' : wB.toNat + 1 < (no :: lo).length := by
    simp only [List.length_cons]
    omega
  obtain ⟨m₁, hmstore⟩ : ∃ m', memStore m ao to (wB.toNat + 1) x =
      .ok m' :=
    ⟨_, memStore_cellsAt m ao to (wB.toNat + 1) (no :: lo) x
      hmem_o hlt'⟩
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "out"
    (.stdVecVal lo) (.stdVecVal (lo.set wB.toNat x)) hout
  have hstep_set := memRevVecSet prog F "out" (.var "w")
    (.stdVecAt "a" (.var "i")) ρ m π wB x ao to lo xO m₁ ρ₁
    hwVarM hatM hout hlay_o hgetO' hmstore hu₁
  have hcells₁ : cellsAt m₁ ao to ((no :: lo).set (wB.toNat + 1) x) :=
    memFind_cellsAt_store m ao to (wB.toNat + 1) (no :: lo) x m₁
      hmem_o hlt' hmstore
  have hsetB : lo.set wB.toNat x = lo.set w x := by rw [hwN]
  have hmem_o₁ : memFind m₁ ao =
      some ⟨to, true, no :: (lo.set w x)⟩ := by
    have e : (no :: lo).set (wB.toNat + 1) x =
        no :: (lo.set wB.toNat x) :=
      List.set_cons_succ
    rw [e, hsetB] at hcells₁
    exact hcells₁
  have hmem_a₁ : memFind m₁ aa = some ⟨ta, true, na :: la⟩ := by
    have h := memFind_memStore_other m m₁ ao aa to (wB.toNat + 1) x
      hmstore haa
    rw [h]; exact hmem_a
  have hmem_b₁ : memFind m₁ ab = some ⟨tb, true, nb :: lb⟩ := by
    have h := memFind_memStore_other m m₁ ao ab to (wB.toNat + 1) x
      hmstore hab
    rw [h]; exact hmem_b
  have hi₁ : envLookup ρ₁ "i" = some (.u64 iB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "out" by decide) hu₁]
    exact hi
  have hj₁ : envLookup ρ₁ "j" = some (.u64 jB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("j" : String) ≠ "out" by decide) hu₁]
    exact hj
  have hw₁ : envLookup ρ₁ "w" = some (.u64 wB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "out" by decide) hu₁]
    exact hw
  have ha₁ : envLookup ρ₁ "a" = some (.stdVecVal la) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "out" by decide) hu₁]
    exact ha
  have hb₁ : envLookup ρ₁ "b" = some (.stdVecVal lb) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("b" : String) ≠ "out" by decide) hu₁]
    exact hb
  have hevI : evalExpr
      (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁ =
      .ok (.u64 (iB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hi₁) (by simp [evalExpr, litVal])
  have hevIM : memEvalExpr
      (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁ m₁ π =
      .ok (.u64 (iB + 1)) :=
    (memEvalExpr_uadd_agree (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))
      ρ₁ m₁ π (memEvalExpr_var _ _ _ _)
      (memEvalExpr_lit _ _ _ _)).trans hevI
  obtain ⟨ρ₂, hu₂⟩ := envUpdate_some_of_lookup ρ₁ "i"
    (.u64 iB) (.u64 (iB + 1)) hi₁
  have hstepI := memRevAssign prog F "i"
    (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁ m₁ π
    (.u64 (iB + 1)) ρ₂ hevIM hevI hu₂
  have hj₂ : envLookup ρ₂ "j" = some (.u64 jB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("j" : String) ≠ "i" by decide) hu₂]
    exact hj₁
  have hw₂ : envLookup ρ₂ "w" = some (.u64 wB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "i" by decide) hu₂]
    exact hw₁
  have hout₂ : envLookup ρ₂ "out" =
      some (.stdVecVal (lo.set wB.toNat x)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "i" by decide) hu₂]
    exact envLookup_update_hit _ _ _ _ hu₁
  have hevJ : evalExpr
      (.uadd (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ =
      .ok (.u64 (jB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hj₂) (by simp [evalExpr, litVal])
  have hevJM : memEvalExpr
      (.uadd (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ m₁ π =
      .ok (.u64 (jB + 1)) :=
    (memEvalExpr_uadd_agree (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))
      ρ₂ m₁ π (memEvalExpr_var _ _ _ _)
      (memEvalExpr_lit _ _ _ _)).trans hevJ
  obtain ⟨ρ₃, hu₃⟩ := envUpdate_some_of_lookup ρ₂ "j"
    (.u64 jB) (.u64 (jB + 1)) hj₂
  have hstepJ := memRevAssign prog F "j"
    (.uadd (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ m₁ π
    (.u64 (jB + 1)) ρ₃ hevJM hevJ hu₃
  have hw₃ : envLookup ρ₃ "w" = some (.u64 wB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "j" by decide) hu₃]
    exact hw₂
  have hout₃ : envLookup ρ₃ "out" =
      some (.stdVecVal (lo.set wB.toNat x)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "j" by decide) hu₃]
    exact hout₂
  have hevW : evalExpr
      (.uadd (.var "w") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₃ =
      .ok (.u64 (wB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hw₃) (by simp [evalExpr, litVal])
  have hevWM : memEvalExpr
      (.uadd (.var "w") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₃ m₁ π =
      .ok (.u64 (wB + 1)) :=
    (memEvalExpr_uadd_agree (.var "w") (.lit (.u64 (BitVec.ofNat 64 1)))
      ρ₃ m₁ π (memEvalExpr_var _ _ _ _)
      (memEvalExpr_lit _ _ _ _)).trans hevW
  obtain ⟨ρ₄, hu₄⟩ := envUpdate_some_of_lookup ρ₃ "w"
    (.u64 wB) (.u64 (wB + 1)) hw₃
  have hstepW := memRevAssign prog F "w"
    (.uadd (.var "w") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₃ m₁ π
    (.u64 (wB + 1)) ρ₄ hevWM hevW hu₄
  have hiN' : (iB + 1).toNat = i + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hiN]
    exact Nat.mod_eq_of_lt (by omega)
  have hjN' : (jB + 1).toNat = j + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hjN]
    exact Nat.mod_eq_of_lt (by omega)
  have hwN' : (wB + 1).toNat = w + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hwN]
    exact Nat.mod_eq_of_lt (by omega)
  have hifM : memEvalProgStmt prog F vecIntersectBody ρ m π =
      memEvalProgStmt prog F
        (.seq (.vecSet "out" (.var "w")
                 (.stdVecAt "a" (.var "i")))
          (.seq (.assign "i" (.uadd (.var "i")
                    (.lit (.u64 (BitVec.ofNat 64 1)))))
            (.seq (.assign "j" (.uadd (.var "j")
                      (.lit (.u64 (BitVec.ofNat 64 1)))))
              (.assign "w" (.uadd (.var "w")
                        (.lit (.u64 (BitVec.ofNat 64 1)))))))) ρ m π := by
    simp only [vecIntersectBody]
    rw [memEvalProgStmt_if_false _ _ _ _ _ _ _ _ hcmp1M,
      memEvalProgStmt_if_false _ _ _ _ _ _ _ _ hcmp2M]
  refine ⟨ρ₄, m₁, ?_, ?_, hiN', ?_, hjN', ?_, hwN', ?_, ?_, ?_,
    hmem_a₁, hmem_b₁, hmem_o₁⟩
  · rw [hifM,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep_set,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepI,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepJ,
      hstepW]
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "w" by decide) hu₄,
      envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "j" by decide) hu₃]
    exact envLookup_update_hit _ _ _ _ hu₂
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("j" : String) ≠ "w" by decide) hu₄]
    exact envLookup_update_hit _ _ _ _ hu₃
  · rw [envLookup_update_hit _ _ _ _ hu₄]
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "w" by decide) hu₄,
      envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "j" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "i" by decide) hu₂]
    exact ha₁
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("b" : String) ≠ "w" by decide) hu₄,
      envLookup_update_miss _ _ _ _ _
      (show ("b" : String) ≠ "j" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("b" : String) ≠ "i" by decide) hu₂]
    exact hb₁
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "w" by decide) hu₄,
      ← hsetB]
    exact hout₃

/-! ## Memory loop -/

/-- Memory loop: the scan runs to cursor exhaustion on memory, the
    environment matches the forward model, capacity is preserved,
    and all three blocks pin their snapshots (the record block
    locksteps writes). Fuel induction threading the body mirrors. -/
theorem memIntersectLoop_ok (prog : Prog) (F G : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (la lb lo : List (BitVec 32))
    (i j w : Nat) (iB jB wB : BitVec 64)
    (i' j' w' : Nat) (lo' : List (BitVec 32))
    (aa ab ao ta tb to : Nat) (na nb no : BitVec 32)
    (hlay_a : layoutLookup π "a" = some (aa, ta))
    (hlay_b : layoutLookup π "b" = some (ab, tb))
    (hlay_o : layoutLookup π "out" = some (ao, to))
    (hmem_a : memFind m aa = some ⟨ta, true, na :: la⟩)
    (hmem_b : memFind m ab = some ⟨tb, true, nb :: lb⟩)
    (hmem_o : memFind m ao = some ⟨to, true, no :: lo⟩)
    (hna : na = BitVec.ofNat 32 la.length)
    (hnb : nb = BitVec.ofNat 32 lb.length)
    (hno : no = BitVec.ofNat 32 lo.length)
    (haa : aa ≠ ao) (hab : ab ≠ ao)
    (hiN : iB.toNat = i) (hjN : jB.toNat = j) (hwN : wB.toNat = w)
    (hla64 : la.length < 2 ^ 64) (hlb64 : lb.length < 2 ^ 64)
    (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hile : i ≤ la.length) (hjle : j ≤ lb.length)
    (hF : (la.length - i) + (lb.length - j) ≤ F)
    (hG : (la.length - i) + (lb.length - j) ≤ G)
    (hcap : w + min (la.length - i) (lb.length - j) ≤ lo.length)
    (hreadA : ∀ p, p < la.length → ∃ x, la[p]? = some x)
    (hreadB : ∀ p, p < lb.length → ∃ x, lb[p]? = some x)
    (hreadO : ∀ p, p < lo.length → ∃ x, lo[p]? = some x)
    (hfwd : intersectFwd la lb lo G i j w = .ok (i', j', w', lo')) :
    ∃ ρ' m', memEvalProgStmt prog F vecIntersectLoop ρ m π =
      .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "b" = some (.stdVecVal lb) ∧
      envLookup ρ' "out" = some (.stdVecVal lo') ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = i') ∧
      (∃ jB', envLookup ρ' "j" = some (.u64 jB') ∧ jB'.toNat = j') ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w') ∧
      w' + min (la.length - i') (lb.length - j') ≤ lo'.length ∧
      memFind m' aa = some ⟨ta, true, na :: la⟩ ∧
      memFind m' ab = some ⟨tb, true, nb :: lb⟩ ∧
      memFind m' ao = some ⟨to, true, no :: lo'⟩ := by
  induction F generalizing G ρ m la lb lo i j w iB jB wB with
  | zero =>
    have hgeA : la.length ≤ i := by omega
    have hguardV : evalExpr intersectGuard ρ = .ok (.b false) :=
      intersectGuard_eval_falseA ρ la lb i j iB jB hiN ha hi hla64 hgeA
    have hguardM : memEvalExpr intersectGuard ρ m π = .ok (.b false) :=
      (memIntersectGuard_agree ρ m π la lb i j iB jB aa ab ta tb na nb
        hlay_a hlay_b hmem_a hmem_b hna hnb hiN hjN hla64 hlb64
        ha hb hi hj).trans hguardV
    have hexit : memEvalProgStmt prog 0 vecIntersectLoop ρ m π =
        .ok ((ρ, m, π), .fellThrough) :=
      memEvalProgStmt_while_false prog 0 _ _ _ _ _ hguardM
    have hpair : (i, j, w, lo) = (i', j', w', lo') := by
      cases G with
      | zero => simpa [intersectFwd] using hfwd
      | succ G =>
        have hnegA : ¬ i < la.length := by omega
        simpa [intersectFwd, dite_eq_right hnegA] using hfwd
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
    exact ⟨ρ, m, hexit, ha, hb, hout, ⟨iB, hi, hiN⟩, ⟨jB, hj, hjN⟩,
      ⟨wB, hw, hwN⟩, hcap, hmem_a, hmem_b, hmem_o⟩
  | succ F ih =>
    by_cases hltA : i < la.length
    · by_cases hltB : j < lb.length
      · obtain ⟨x, hgetA⟩ := hreadA i hltA
        obtain ⟨y, hgetB⟩ := hreadB j hltB
        have hguardV : evalExpr intersectGuard ρ = .ok (.b true) :=
          intersectGuard_eval_true ρ la lb i j iB jB hiN hjN ha hb hi hj
            hla64 hlb64 hltA hltB
        have hguardM : memEvalExpr intersectGuard ρ m π =
            .ok (.b true) :=
          (memIntersectGuard_agree ρ m π la lb i j iB jB aa ab ta tb
            na nb hlay_a hlay_b hmem_a hmem_b hna hnb hiN hjN hla64
            hlb64 ha hb hi hj).trans hguardV
        by_cases hlt : (x.slt y) = true
        · cir_fuel_step (F, G, (la.length - (i + 1)) + (lb.length - j))
          obtain ⟨ρ₁, hbody, hiB₁, hiN₁, hjB₁, hwB₁, ha₁, hb₁,
              hout₁⟩ :=
            memIntersectBody_advI prog F ρ m π la lb lo i j w iB jB wB
              x y aa ab ao ta tb to na nb no
              hlay_a hlay_b hlay_o hmem_a hmem_b hmem_o
              hna hnb hno hiN hjN hwN hla64 hlb64
              ha hb hout hi hj hw hgetA hgetB hltA hltB hlt
          have hfwd' : intersectFwd la lb lo G' (i + 1) j w =
              .ok (i', j', w', lo') := by
            simpa [intersectFwd, dite_eq_left hltA, dite_eq_left hltB,
              hgetA, hgetB, hlt] using hfwd
          have hcap' : w + min (la.length - (i + 1)) (lb.length - j) ≤
              lo.length := by
            omega
          obtain ⟨ρ', m', hloop, ha', hb', hout', ⟨iB', hiB', hiN'⟩,
              ⟨jB', hjB', hjN'⟩, ⟨wB', hwB', hwN'⟩, hcapI,
              hmem_a', hmem_b', hmem_o'⟩ :=
            ih (G := G') (ρ := ρ₁) (m := m) (la := la) (lb := lb)
              (lo := lo) (i := i + 1) (j := j) (w := w)
              (iB := iB + 1) (jB := jB) (wB := wB)
              (hiN := hiN₁) (hjN := hjN) (hwN := hwN)
              (hla64 := hla64) (hlb64 := hlb64) (hlo64 := hlo64)
              (ha := ha₁) (hb := hb₁) (hout := hout₁)
              (hi := hiB₁) (hj := hjB₁) (hw := hwB₁)
              (hmem_a := hmem_a) (hmem_b := hmem_b) (hmem_o := hmem_o)
              (hna := hna) (hnb := hnb) (hno := hno)
              (hile := by omega) (hjle := hjle)
              (hF := hF') (hG := hG') (hcap := hcap')
              (hreadA := hreadA) (hreadB := hreadB) (hreadO := hreadO)
              (hfwd := hfwd')
          refine ⟨ρ', m', ?_, ha', hb', hout', ⟨iB', hiB', hiN'⟩,
            ⟨jB', hjB', hjN'⟩, ⟨wB', hwB', hwN'⟩, hcapI,
            hmem_a', hmem_b', hmem_o'⟩
          have hwhile :
              memEvalProgStmt prog (F + 1) vecIntersectLoop ρ m π =
              memEvalProgStmt prog F vecIntersectLoop ρ₁ m π := by
            cir_unfold_prog (vecIntersectLoop, prog, F, hguardM, hbody)
          rw [hwhile]
          exact hloop
        · by_cases hgt : (y.slt x) = true
          · have hne : (x.slt y) = false := by
              cases hxy : x.slt y with
              | true => exact absurd hxy hlt
              | false => rfl
            cir_fuel_step (F, G, (la.length - i) + (lb.length - (j + 1)))
            obtain ⟨ρ₁, hbody, hiB₁, hjB₁, hjN₁, hwB₁, ha₁, hb₁,
                hout₁⟩ :=
              memIntersectBody_advJ prog F ρ m π la lb lo i j w iB jB
                wB x y aa ab ao ta tb to na nb no
                hlay_a hlay_b hlay_o hmem_a hmem_b hmem_o
                hna hnb hno hiN hjN hwN hla64 hlb64
                ha hb hout hi hj hw hgetA hgetB hltA hltB hne hgt
            have hfwd' : intersectFwd la lb lo G' i (j + 1) w =
                .ok (i', j', w', lo') := by
              simpa [intersectFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hne, hgt] using hfwd
            have hcap' : w + min (la.length - i) (lb.length - (j + 1)) ≤
                lo.length := by
              omega
            obtain ⟨ρ', m', hloop, ha', hb', hout', ⟨iB', hiB', hiN'⟩,
                ⟨jB', hjB', hjN'⟩, ⟨wB', hwB', hwN'⟩, hcapI,
                hmem_a', hmem_b', hmem_o'⟩ :=
              ih (G := G') (ρ := ρ₁) (m := m) (la := la) (lb := lb)
                (lo := lo) (i := i) (j := j + 1) (w := w)
                (iB := iB) (jB := jB + 1) (wB := wB)
                (hiN := hiN) (hjN := hjN₁) (hwN := hwN)
                (hla64 := hla64) (hlb64 := hlb64) (hlo64 := hlo64)
                (ha := ha₁) (hb := hb₁) (hout := hout₁)
                (hi := hiB₁) (hj := hjB₁) (hw := hwB₁)
                (hmem_a := hmem_a) (hmem_b := hmem_b) (hmem_o := hmem_o)
                (hna := hna) (hnb := hnb) (hno := hno)
                (hile := hile) (hjle := by omega)
                (hF := hF') (hG := hG') (hcap := hcap')
                (hreadA := hreadA) (hreadB := hreadB) (hreadO := hreadO)
                (hfwd := hfwd')
            refine ⟨ρ', m', ?_, ha', hb', hout', ⟨iB', hiB', hiN'⟩,
              ⟨jB', hjB', hjN'⟩, ⟨wB', hwB', hwN'⟩, hcapI,
              hmem_a', hmem_b', hmem_o'⟩
            have hwhile :
                memEvalProgStmt prog (F + 1) vecIntersectLoop ρ m π =
                memEvalProgStmt prog F vecIntersectLoop ρ₁ m π := by
              cir_unfold_prog (vecIntersectLoop, prog, F, hguardM, hbody)
            rw [hwhile]
            exact hloop
          · have hge1 : (x.slt y) = false := by
              cases hxy : x.slt y with
              | true => exact absurd hxy hlt
              | false => rfl
            have hge2 : (y.slt x) = false := by
              cases hyx : y.slt x with
              | true => exact absurd hyx hgt
              | false => rfl
            have hwlt : w < lo.length := by omega
            obtain ⟨xO, hgetO⟩ := hreadO w hwlt
            cir_fuel_step (F, G,
              (la.length - (i + 1)) + (lb.length - (j + 1)))
            obtain ⟨ρ₁, m₁, hbody, hiB₁, hiN₁, hjB₁, hjN₁, hwB₁, hwN₁,
                ha₁, hb₁, hout₁, hmem_a₁, hmem_b₁, hmem_o₁⟩ :=
              memIntersectBody_write prog F ρ m π la lb lo i j w iB jB
                wB x y aa ab ao ta tb to na nb no
                hlay_a hlay_b hlay_o hmem_a hmem_b hmem_o
                hna hnb hno haa hab hiN hjN hwN hla64 hlb64 hlo64
                ha hb hout hi hj hw hgetA hgetB hltA hltB
                xO hgetO hwlt hge1 hge2
            have hfwd' : intersectFwd la lb (lo.set w x) G' (i + 1)
                (j + 1) (w + 1) = .ok (i', j', w', lo') := by
              simpa [intersectFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hge1, hge2] using hfwd
            have hlenSet : (lo.set w x).length = lo.length :=
              List.length_set
            have hcap' : (w + 1) +
                min (la.length - (i + 1)) (lb.length - (j + 1)) ≤
                (lo.set w x).length := by
              rw [hlenSet]; omega
            have hlo64' : (lo.set w x).length < 2 ^ 64 := by
              rw [hlenSet]; exact hlo64
            have hno₁ : no = BitVec.ofNat 32 (lo.set w x).length := by
              rw [List.length_set]; exact hno
            have hreadO' : ∀ p, p < (lo.set w x).length →
                ∃ z, (lo.set w x)[p]? = some z := by
              intro p hp
              have hplen : p < lo.length := by
                have hlen : (lo.set w x).length = lo.length :=
                  List.length_set
                omega
              obtain ⟨z, hz⟩ := hreadO p hplen
              by_cases hpi : p = w
              · subst hpi
                exact ⟨x, by
                  rw [List.getElem?_set_self (by omega : p < lo.length)]⟩
              · exact ⟨z, by
                  rw [List.getElem?_set_ne (show w ≠ p by omega)]
                  exact hz⟩
            obtain ⟨ρ', m', hloop, ha', hb', hout', ⟨iB', hiB', hiN'⟩,
                ⟨jB', hjB', hjN'⟩, ⟨wB', hwB', hwN'⟩, hcapI,
                hmem_a', hmem_b', hmem_o'⟩ :=
              ih (G := G') (ρ := ρ₁) (m := m₁) (la := la) (lb := lb)
                (lo := (lo.set w x))
                (i := i + 1) (j := j + 1) (w := w + 1)
                (iB := iB + 1) (jB := jB + 1) (wB := wB + 1)
                (hiN := hiN₁) (hjN := hjN₁) (hwN := hwN₁)
                (hla64 := hla64) (hlb64 := hlb64) (hlo64 := hlo64')
                (ha := ha₁) (hb := hb₁) (hout := hout₁)
                (hi := hiB₁) (hj := hjB₁) (hw := hwB₁)
                (hmem_a := hmem_a₁) (hmem_b := hmem_b₁) (hmem_o := hmem_o₁)
                (hna := hna) (hnb := hnb) (hno := hno₁)
                (hile := by omega) (hjle := by omega)
                (hF := hF') (hG := hG') (hcap := hcap')
                (hreadA := hreadA) (hreadB := hreadB) (hreadO := hreadO')
                (hfwd := hfwd')
            refine ⟨ρ', m', ?_, ha', hb', hout', ⟨iB', hiB', hiN'⟩,
              ⟨jB', hjB', hjN'⟩, ⟨wB', hwB', hwN'⟩, hcapI,
              hmem_a', hmem_b', hmem_o'⟩
            have hwhile :
                memEvalProgStmt prog (F + 1) vecIntersectLoop ρ m π =
                memEvalProgStmt prog F vecIntersectLoop ρ₁ m₁ π := by
              cir_unfold_prog (vecIntersectLoop, prog, F, hguardM, hbody)
            rw [hwhile]
            exact hloop
      · have hgeB : lb.length ≤ j := by omega
        have hguardV : evalExpr intersectGuard ρ = .ok (.b false) :=
          intersectGuard_eval_falseB ρ la lb i j iB jB hiN hjN ha hb
            hi hj hla64 hlb64 hltA hgeB
        have hguardM : memEvalExpr intersectGuard ρ m π =
            .ok (.b false) :=
          (memIntersectGuard_agree ρ m π la lb i j iB jB aa ab ta tb
            na nb hlay_a hlay_b hmem_a hmem_b hna hnb hiN hjN hla64
            hlb64 ha hb hi hj).trans hguardV
        have hexit : memEvalProgStmt prog (F + 1) vecIntersectLoop ρ m π =
            .ok ((ρ, m, π), .fellThrough) :=
          memEvalProgStmt_while_false prog (F + 1) _ _ _ _ _ hguardM
        have hpair : (i, j, w, lo) = (i', j', w', lo') := by
          cases G with
          | zero => simpa [intersectFwd] using hfwd
          | succ G =>
            have hnegB : ¬ j < lb.length := by omega
            simpa [intersectFwd, dite_eq_left hltA,
              dite_eq_right hnegB] using hfwd
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
        exact ⟨ρ, m, hexit, ha, hb, hout, ⟨iB, hi, hiN⟩, ⟨jB, hj, hjN⟩,
          ⟨wB, hw, hwN⟩, hcap, hmem_a, hmem_b, hmem_o⟩
    · have hgeA : la.length ≤ i := by omega
      have hguardV : evalExpr intersectGuard ρ = .ok (.b false) :=
        intersectGuard_eval_falseA ρ la lb i j iB jB hiN ha hi hla64 hgeA
      have hguardM : memEvalExpr intersectGuard ρ m π =
          .ok (.b false) :=
        (memIntersectGuard_agree ρ m π la lb i j iB jB aa ab ta tb na nb
          hlay_a hlay_b hmem_a hmem_b hna hnb hiN hjN hla64 hlb64
          ha hb hi hj).trans hguardV
      have hexit : memEvalProgStmt prog (F + 1) vecIntersectLoop ρ m π =
          .ok ((ρ, m, π), .fellThrough) :=
        memEvalProgStmt_while_false prog (F + 1) _ _ _ _ _ hguardM
      have hpair : (i, j, w, lo) = (i', j', w', lo') := by
        cases G with
        | zero => simpa [intersectFwd] using hfwd
        | succ G =>
          have hnegA : ¬ i < la.length := by omega
          simpa [intersectFwd, dite_eq_right hnegA] using hfwd
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
      exact ⟨ρ, m, hexit, ha, hb, hout, ⟨iB, hi, hiN⟩, ⟨jB, hj, hjN⟩,
        ⟨wB, hw, hwN⟩, hcap, hmem_a, hmem_b, hmem_o⟩

/-! ## Value entry -/

/-- Value entry: three cursor binders, the loop from the empty
    record, and the `w` return. The prelude cons order matches
    `mkIntersectEnv`, so the entry bridge is `rfl`. -/
theorem evalProgFunc_vecIntersect_ok (F : Nat)
    (la lb lo : List (BitVec 32))
    (i' j' w' : Nat) (lo' : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hlb64 : lb.length < 2 ^ 64)
    (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length + lb.length + 1 ≤ F)
    (hreadA : ∀ p, p < la.length → ∃ x, la[p]? = some x)
    (hreadB : ∀ p, p < lb.length → ∃ x, lb[p]? = some x)
    (hreadO : ∀ p, p < lo.length → ∃ x, lo[p]? = some x)
    (hcap0 : min la.length lb.length ≤ lo.length)
    (hfwd : intersectFwd la lb lo (la.length + lb.length + 1) 0 0 0 =
      .ok (i', j', w', lo')) :
    evalProgFunc vecIntersectProg F vecIntersectFunc
      [.stdVecVal la, .stdVecVal lb, .stdVecVal lo] =
      .ok (.u64 (BitVec.ofNat 64 w')) := by
  have hbind : bindArgs vecIntersectFunc.args
      [.stdVecVal la, .stdVecVal lb, .stdVecVal lo] =
      some [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)] := rfl
  have hbody : vecIntersectFunc.body =
      (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq (.let_ "j" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
            (.seq vecIntersectLoop
              (.return_ (.var "w")))))) := rfl
  have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletI := revLet vecIntersectProg F "i" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("a", .stdVecVal la), ("b", .stdVecVal lb),
      ("out", .stdVecVal lo)]
    (.u64 (BitVec.ofNat 64 0)) hlitV
  have hlitVJ : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0))) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletJ := revLet vecIntersectProg F "j" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (envExtend [("a", .stdVecVal la), ("b", .stdVecVal lb),
      ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0)))
    (.u64 (BitVec.ofNat 64 0)) hlitVJ
  have hlitVW : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend (envExtend [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 0))) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletW := revLet vecIntersectProg F "w" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (envExtend (envExtend [("a", .stdVecVal la), ("b", .stdVecVal lb),
      ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0)))
      "j" (.u64 (BitVec.ofNat 64 0)))
    (.u64 (BitVec.ofNat 64 0)) hlitVW
  have henv : envExtend (envExtend (envExtend
      [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0)) =
      mkIntersectEnv la lb lo (BitVec.ofNat 64 0)
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) := rfl
  have hv0N : (BitVec.ofNat 64 0).toNat = 0 := by
    rw [BitVec.toNat_ofNat]
  have ha₃ : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "a" =
      some (.stdVecVal la) := by
    rw [henv]; exact mkIntersectEnv_a _ _ _ _ _ _
  have hb₃ : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "b" =
      some (.stdVecVal lb) := by
    rw [henv]; exact mkIntersectEnv_b _ _ _ _ _ _
  have hout₃ : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "out" =
      some (.stdVecVal lo) := by
    rw [henv]; exact mkIntersectEnv_out _ _ _ _ _ _
  have hi₃ : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "i" =
      some (.u64 (BitVec.ofNat 64 0)) := by
    rw [henv]; exact mkIntersectEnv_i _ _ _ _ _ _
  have hj₃ : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "j" =
      some (.u64 (BitVec.ofNat 64 0)) := by
    rw [henv]; exact mkIntersectEnv_j _ _ _ _ _ _
  have hw₃ : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "w" =
      some (.u64 (BitVec.ofNat 64 0)) := by
    rw [henv]; exact mkIntersectEnv_w _ _ _ _ _ _
  have hcap : 0 + min (la.length - 0) (lb.length - 0) ≤ lo.length := by
    simpa using hcap0
  obtain ⟨ρ', hloop, ha', hb', hout', ⟨iB', hiB', hiN'⟩,
      ⟨jB', hjB', hjN'⟩, ⟨wB', hwB', hwN'⟩, hcapI⟩ :=
    valIntersectLoop_ok vecIntersectProg F (la.length + lb.length + 1)
      (envExtend (envExtend (envExtend
        [("a", .stdVecVal la), ("b", .stdVecVal lb),
          ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0)))
          "j" (.u64 (BitVec.ofNat 64 0)))
          "w" (.u64 (BitVec.ofNat 64 0)))
      la lb lo 0 0 0
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
      i' j' w' lo' hv0N hv0N hv0N hla64 hlb64 hlo64
      ha₃ hb₃ hout₃ hi₃ hj₃ hw₃ (Nat.zero_le _) (Nat.zero_le _)
      (by omega) (by omega) hcap hreadA hreadB hreadO hfwd
  have hlen : lo'.length = lo.length :=
    intersectFwd_length _ _ _ _ _ _ _ _ _ _ _ hfwd
  have hw'lt : w' < 2 ^ 64 := by omega
  have hwB'eq : wB' = BitVec.ofNat 64 w' := by
    apply BitVec.eq_of_toNat_eq
    rw [hwN', BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt hw'lt).symm
  have hevW' : evalExpr (.var "w") ρ' =
      .ok (.u64 (BitVec.ofNat 64 w')) := by
    rw [← hwB'eq]; exact evalExpr_var_hit _ _ _ hwB'
  have hret := evalProgStmt_return vecIntersectProg F (.var "w") ρ'
    (.u64 (BitVec.ofNat 64 w')) hevW'
  simp only [evalProgFunc, hbind, hbody]
  rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletI,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletJ,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletW,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hloop,
    hret]

/-! ## Memory entry -/

/-- Memory entry: same prelude on the three pinned blocks, the
    memory loop, and the `w` return. -/
theorem memEvalProgFunc_vecIntersect_ok (F : Nat)
    (la lb lo : List (BitVec 32))
    (i' j' w' : Nat) (lo' : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hlb64 : lb.length < 2 ^ 64)
    (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length + lb.length + 1 ≤ F)
    (hreadA : ∀ p, p < la.length → ∃ x, la[p]? = some x)
    (hreadB : ∀ p, p < lb.length → ∃ x, lb[p]? = some x)
    (hreadO : ∀ p, p < lo.length → ∃ x, lo[p]? = some x)
    (hcap0 : min la.length lb.length ≤ lo.length)
    (hfwd : intersectFwd la lb lo (la.length + lb.length + 1) 0 0 0 =
      .ok (i', j', w', lo')) :
    memEvalProgFunc vecIntersectProg F vecIntersectFunc
      [.stdVecVal la, .stdVecVal lb, .stdVecVal lo] =
      .ok (.u64 (BitVec.ofNat 64 w')) := by
  have hbind := bindMemArgs_vecIntersect la lb lo
  have hbody : vecIntersectFunc.body =
      (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq (.let_ "j" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
            (.seq vecIntersectLoop
              (.return_ (.var "w")))))) := rfl
  have hmem_a₀ : memFind
      ⟨3, [(2, ⟨2, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (1, ⟨1, true,
        (BitVec.ofNat 32 lb.length) :: lb⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ 2 =
      some ⟨2, true, (BitVec.ofNat 32 la.length) :: la⟩ :=
    memFind_cons_hit _ _ _ _ _
  have hmem_b₀ : memFind
      ⟨3, [(2, ⟨2, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (1, ⟨1, true,
        (BitVec.ofNat 32 lb.length) :: lb⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ 1 =
      some ⟨1, true, (BitVec.ofNat 32 lb.length) :: lb⟩ := by
    rw [memFind_cons_miss _ _ _ _ _ _ (by decide : (1 : Nat) ≠ 2)]
    exact memFind_cons_hit _ _ _ _ _
  have hmem_o₀ : memFind
      ⟨3, [(2, ⟨2, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (1, ⟨1, true,
        (BitVec.ofNat 32 lb.length) :: lb⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ 0 =
      some ⟨0, true, (BitVec.ofNat 32 lo.length) :: lo⟩ := by
    rw [memFind_cons_miss _ _ _ _ _ _ (by decide : (0 : Nat) ≠ 2),
      memFind_cons_miss _ _ _ _ _ _ (by decide : (0 : Nat) ≠ 1)]
    exact memFind_cons_hit _ _ _ _ _
  have hlay_a₀ : layoutLookup [("a", 2, 2), ("b", 1, 1), ("out", 0, 0)]
      "a" = some (2, 2) := by simp [layoutLookup]
  have hlay_b₀ : layoutLookup [("a", 2, 2), ("b", 1, 1), ("out", 0, 0)]
      "b" = some (1, 1) := by simp [layoutLookup]
  have hlay_o₀ : layoutLookup [("a", 2, 2), ("b", 1, 1), ("out", 0, 0)]
      "out" = some (0, 0) := by simp [layoutLookup]
  have haa₀ : (2 : Nat) ≠ 0 := by decide
  have hab₀ : (1 : Nat) ≠ 0 := by decide
  have hlitM : memEvalExpr
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)]
      ⟨3, [(2, ⟨2, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (1, ⟨1, true,
        (BitVec.ofNat 32 lb.length) :: lb⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
      [("a", 2, 2), ("b", 1, 1), ("out", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("a", .stdVecVal la), ("b", .stdVecVal lb),
          ("out", .stdVecVal lo)] :=
    memEvalExpr_lit _ _ _ _
  have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletI := memRevLet vecIntersectProg F "i" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("a", .stdVecVal la), ("b", .stdVecVal lb),
      ("out", .stdVecVal lo)]
    ⟨3, [(2, ⟨2, true,
      (BitVec.ofNat 32 la.length) :: la⟩),
      (1, ⟨1, true,
      (BitVec.ofNat 32 lb.length) :: lb⟩),
      (0, ⟨0, true,
      (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
    [("a", 2, 2), ("b", 1, 1), ("out", 0, 0)]
    (.u64 (BitVec.ofNat 64 0))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) (by intro h; cases h) hlitM hlitV
  have hlitMJ : memEvalExpr
      (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0)))
      ⟨3, [(2, ⟨2, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (1, ⟨1, true,
        (BitVec.ofNat 32 lb.length) :: lb⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
      [("a", 2, 2), ("b", 1, 1), ("out", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend [("a", .stdVecVal la), ("b", .stdVecVal lb),
          ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0))) :=
    memEvalExpr_lit _ _ _ _
  have hlitVJ : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0))) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletJ := memRevLet vecIntersectProg F "j" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (envExtend [("a", .stdVecVal la), ("b", .stdVecVal lb),
      ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0)))
    ⟨3, [(2, ⟨2, true,
      (BitVec.ofNat 32 la.length) :: la⟩),
      (1, ⟨1, true,
      (BitVec.ofNat 32 lb.length) :: lb⟩),
      (0, ⟨0, true,
      (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
    [("a", 2, 2), ("b", 1, 1), ("out", 0, 0)]
    (.u64 (BitVec.ofNat 64 0))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) (by intro h; cases h) hlitMJ hlitVJ
  have hlitMW : memEvalExpr
      (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend (envExtend [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 0)))
      ⟨3, [(2, ⟨2, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (1, ⟨1, true,
        (BitVec.ofNat 32 lb.length) :: lb⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
      [("a", 2, 2), ("b", 1, 1), ("out", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend (envExtend [("a", .stdVecVal la), ("b", .stdVecVal lb),
          ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0)))
          "j" (.u64 (BitVec.ofNat 64 0))) :=
    memEvalExpr_lit _ _ _ _
  have hlitVW : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend (envExtend [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 0))) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletW := memRevLet vecIntersectProg F "w" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (envExtend (envExtend [("a", .stdVecVal la), ("b", .stdVecVal lb),
      ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0)))
      "j" (.u64 (BitVec.ofNat 64 0)))
    ⟨3, [(2, ⟨2, true,
      (BitVec.ofNat 32 la.length) :: la⟩),
      (1, ⟨1, true,
      (BitVec.ofNat 32 lb.length) :: lb⟩),
      (0, ⟨0, true,
      (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
    [("a", 2, 2), ("b", 1, 1), ("out", 0, 0)]
    (.u64 (BitVec.ofNat 64 0))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) (by intro h; cases h) hlitMW hlitVW
  have henv : envExtend (envExtend (envExtend
      [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0)) =
      mkIntersectEnv la lb lo (BitVec.ofNat 64 0)
        (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) := rfl
  have hv0N : (BitVec.ofNat 64 0).toNat = 0 := by
    rw [BitVec.toNat_ofNat]
  have ha₃ : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "a" =
      some (.stdVecVal la) := by
    rw [henv]; exact mkIntersectEnv_a _ _ _ _ _ _
  have hb₃ : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "b" =
      some (.stdVecVal lb) := by
    rw [henv]; exact mkIntersectEnv_b _ _ _ _ _ _
  have hout₃ : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "out" =
      some (.stdVecVal lo) := by
    rw [henv]; exact mkIntersectEnv_out _ _ _ _ _ _
  have hi₃ : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "i" =
      some (.u64 (BitVec.ofNat 64 0)) := by
    rw [henv]; exact mkIntersectEnv_i _ _ _ _ _ _
  have hj₃ : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "j" =
      some (.u64 (BitVec.ofNat 64 0)) := by
    rw [henv]; exact mkIntersectEnv_j _ _ _ _ _ _
  have hw₃ : envLookup (envExtend (envExtend (envExtend
      [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0)))
        "j" (.u64 (BitVec.ofNat 64 0)))
        "w" (.u64 (BitVec.ofNat 64 0))) "w" =
      some (.u64 (BitVec.ofNat 64 0)) := by
    rw [henv]; exact mkIntersectEnv_w _ _ _ _ _ _
  have hcap : 0 + min (la.length - 0) (lb.length - 0) ≤ lo.length := by
    simpa using hcap0
  obtain ⟨ρ', m', hloop, ha', hb', hout', ⟨iB', hiB', hiN'⟩,
      ⟨jB', hjB', hjN'⟩, ⟨wB', hwB', hwN'⟩, hcapI,
      hmem_a', hmem_b', hmem_o'⟩ :=
    memIntersectLoop_ok vecIntersectProg F (la.length + lb.length + 1)
      (envExtend (envExtend (envExtend
        [("a", .stdVecVal la), ("b", .stdVecVal lb),
          ("out", .stdVecVal lo)] "i" (.u64 (BitVec.ofNat 64 0)))
          "j" (.u64 (BitVec.ofNat 64 0)))
          "w" (.u64 (BitVec.ofNat 64 0)))
      ⟨3, [(2, ⟨2, true,
        (BitVec.ofNat 32 la.length) :: la⟩),
        (1, ⟨1, true,
        (BitVec.ofNat 32 lb.length) :: lb⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
      [("a", 2, 2), ("b", 1, 1), ("out", 0, 0)]
      la lb lo 0 0 0
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
      i' j' w' lo' 2 1 0 2 1 0
      (BitVec.ofNat 32 la.length) (BitVec.ofNat 32 lb.length)
      (BitVec.ofNat 32 lo.length)
      (hlay_a := hlay_a₀) (hlay_b := hlay_b₀) (hlay_o := hlay_o₀)
      (hmem_a := hmem_a₀) (hmem_b := hmem_b₀) (hmem_o := hmem_o₀)
      (hna := rfl) (hnb := rfl) (hno := rfl)
      (haa := haa₀) (hab := hab₀)
      (hiN := hv0N) (hjN := hv0N) (hwN := hv0N)
      (hla64 := hla64) (hlb64 := hlb64) (hlo64 := hlo64)
      (ha := ha₃) (hb := hb₃) (hout := hout₃)
      (hi := hi₃) (hj := hj₃) (hw := hw₃)
      (hile := Nat.zero_le _) (hjle := Nat.zero_le _)
      (hF := by omega) (hG := by omega) (hcap := hcap)
      (hreadA := hreadA) (hreadB := hreadB) (hreadO := hreadO)
      (hfwd := hfwd)
  have hlen : lo'.length = lo.length :=
    intersectFwd_length _ _ _ _ _ _ _ _ _ _ _ hfwd
  have hw'lt : w' < 2 ^ 64 := by omega
  have hwB'eq : wB' = BitVec.ofNat 64 w' := by
    apply BitVec.eq_of_toNat_eq
    rw [hwN', BitVec.toNat_ofNat]
    exact (Nat.mod_eq_of_lt hw'lt).symm
  have hevW'V : evalExpr (.var "w") ρ' =
      .ok (.u64 (BitVec.ofNat 64 w')) := by
    rw [← hwB'eq]; exact evalExpr_var_hit _ _ _ hwB'
  have hevW' : memEvalExpr (.var "w") ρ' m'
      [("a", 2, 2), ("b", 1, 1), ("out", 0, 0)] =
      .ok (.u64 (BitVec.ofNat 64 w')) :=
    (memEvalExpr_var _ _ _ _).trans hevW'V
  have hret := memEvalProgStmt_return vecIntersectProg F
    (.var "w") ρ' m' [("a", 2, 2), ("b", 1, 1), ("out", 0, 0)]
    (.u64 (BitVec.ofNat 64 w')) hevW'
  simp only [memEvalProgFunc, hbind, hbody]
  rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletI,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletJ,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletW,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hloop,
    hret]

/-! ## Transfer (`memEval = Eval`) -/

/-- Transfer for `vec_intersect`: memory evaluation agrees with
    value evaluation on a successful scan. -/
theorem memTransferProg_vecIntersect_ok (F : Nat)
    (la lb lo : List (BitVec 32))
    (i' j' w' : Nat) (lo' : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hlb64 : lb.length < 2 ^ 64)
    (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length + lb.length + 1 ≤ F)
    (hreadA : ∀ p, p < la.length → ∃ x, la[p]? = some x)
    (hreadB : ∀ p, p < lb.length → ∃ x, lb[p]? = some x)
    (hreadO : ∀ p, p < lo.length → ∃ x, lo[p]? = some x)
    (hcap0 : min la.length lb.length ≤ lo.length)
    (hfwd : intersectFwd la lb lo (la.length + lb.length + 1) 0 0 0 =
      .ok (i', j', w', lo'))
    (_h : oracleNoalias vecIntersectFunc
      [.stdVecVal la, .stdVecVal lb, .stdVecVal lo]) :
    memEvalProgFunc vecIntersectProg F vecIntersectFunc
      [.stdVecVal la, .stdVecVal lb, .stdVecVal lo] =
      evalProgFunc vecIntersectProg F vecIntersectFunc
        [.stdVecVal la, .stdVecVal lb, .stdVecVal lo] := by
  rw [memEvalProgFunc_vecIntersect_ok F la lb lo i' j' w' lo'
    hla64 hlb64 hlo64 hF hreadA hreadB hreadO hcap0 hfwd,
    evalProgFunc_vecIntersect_ok F la lb lo i' j' w' lo'
    hla64 hlb64 hlo64 hF hreadA hreadB hreadO hcap0 hfwd]

/-! ## Closing spec (against the independent oracle) -/

/-- Closing intersection contract (P2-M11): a successful run
    returns the survivor count, which is exactly the independent
    sorted-merge oracle length. -/
theorem evalProgFunc_vecIntersect_spec_ok (F : Nat)
    (la lb lo : List (BitVec 32))
    (hla64 : la.length < 2 ^ 64) (hlb64 : lb.length < 2 ^ 64)
    (hlo64 : lo.length < 2 ^ 64)
    (hF : la.length + lb.length + 1 ≤ F)
    (hsA : SortedSeg la 0 la.length) (hsB : SortedSeg lb 0 lb.length)
    (hcap0 : min la.length lb.length ≤ lo.length) :
    ∃ w', evalProgFunc vecIntersectProg F vecIntersectFunc
      [.stdVecVal la, .stdVecVal lb, .stdVecVal lo] =
      .ok (.u64 (BitVec.ofNat 64 w')) ∧
      w' = (intersectOracle la lb).length := by
  have hreadA : ∀ p, p < la.length → ∃ x, la[p]? = some x :=
    fun p hp => ⟨_, List.getElem?_eq_getElem hp⟩
  have hreadB : ∀ p, p < lb.length → ∃ x, lb[p]? = some x :=
    fun p hp => ⟨_, List.getElem?_eq_getElem hp⟩
  have hreadO : ∀ p, p < lo.length → ∃ x, lo[p]? = some x :=
    fun p hp => ⟨_, List.getElem?_eq_getElem hp⟩
  obtain ⟨i', j', w', lo', hfwd⟩ :=
    intersectFwd_noFail la lb lo (la.length + lb.length + 1) 0 0 0
      (by omega) (by omega) (by omega)
  have heval := evalProgFunc_vecIntersect_ok F la lb lo i' j' w' lo'
    hla64 hlb64 hlo64 hF hreadA hreadB hreadO hcap0 hfwd
  have hlen := (intersectFwd_correct la lb lo hsA hsB hcap0 i' j' w' lo'
    hfwd).2.2
  exact ⟨w', heval, hlen⟩
