/-
Circe.Transfer.VecSelectionSort — M4c mem transfer for iterative
selection sort (`vec_selection_sort` + `min_index` leaf).

The leaf is proved at fuel level (`evalStmtFuel` /
`memEvalStmtFuel`, the `ArraySort` precedent): it takes no stores,
so the memory side only threads reads through `memLoad` agrees
while the env extends. The outer entry is proved at program level
(`evalProgStmt` / `memEvalProgStmt`, the M3c kit): each iteration
dispatches the leaf by value (`callRet` re-spends the same fuel in
the callee — the S1 discipline, caller `(m, π)` threads through
unchanged) and the unconditional swap stores thread through
`memStore` in lockstep on the single `v` block. The outer loop
re-inducts over `(ρ, m, π)` with the forward equation threading
(three fuels: outer program fuel, inner budget re-spent whole by
every leaf call, forward fuel). One leg per function — both
kernels are total (every access is guard-justified).
Entries close against the M4b contracts.
-/
import Circe.Transfer.VecReverse
import Circe.Emit.VecSelectionSort
import Circe.Specs

open VecSelectionSort

/-! ## Binding (closed form) -/

/-- Leaf binding pins one snapshot: the shared-borrow vector at
    addr `0`; the owned bound binds by value only. -/
theorem bindMemArgs_minIndex (l : List (BitVec 32)) (loB : BitVec 64) :
    bindMemArgs minIndexFunc.args
      [.stdVecVal l, .u64 loB] emptyMem =
      some ([("a", .stdVecVal l), ("lo", .u64 loB)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("a", 0, 0)]) := by
  rfl

/-- Leaf footprint is a single singleton. -/
theorem oracleNoalias_minIndex (l : List (BitVec 32)) (loB : BitVec 64) :
    oracleNoalias minIndexFunc
      [.stdVecVal l, .u64 loB] := by
  have hb := bindMemArgs_minIndex l loB
  have hn : LayoutNoAlias [("a", 0, 0)] := by
    simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- Entry binding pins one snapshot: the single `mutBorrow` vector
    at addr `0`. -/
theorem bindMemArgs_vecSelectionSort (l : List (BitVec 32)) :
    bindMemArgs vecSelectionSortFunc.args
      [.stdVecVal l] emptyMem =
      some ([("v", .stdVecVal l)],
        ⟨1, [(0, ⟨0, true,
          (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("v", 0, 0)]) := by
  rfl

/-- Entry footprint is a single singleton. -/
theorem oracleNoalias_vecSelectionSort (l : List (BitVec 32)) :
    oracleNoalias vecSelectionSortFunc
      [.stdVecVal l] := by
  have hb := bindMemArgs_vecSelectionSort l
  have hn : LayoutNoAlias [("v", 0, 0)] := by
    simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-! ## Leaf value proofs (fuel level) -/

/-- One leaf step (value level), take branch: the scan test fires,
    `m` takes the scan index, `j` advances. -/
theorem valMinIndexBody_take (F : Nat)
    (ρ : Env) (l : List (BitVec 32))
    (j m : Nat) (jB mB : BitVec 64) (x y : BitVec 32)
    (hjN : jB.toNat = j) (hmN : mB.toNat = m)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "a" = some (.stdVecVal l))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hm : envLookup ρ "m" = some (.u64 mB))
    (hlt : j < l.length)
    (hx : l[j]? = some x) (hy : l[m]? = some y)
    (htake : (x.slt y) = true) :
    ∃ ρ', evalStmtFuel F minIndexStep ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "m" = some (.u64 jB) ∧
      envLookup ρ' "a" = some (.stdVecVal l) ∧
      (∃ jB', envLookup ρ' "j" = some (.u64 jB') ∧
        jB'.toNat = j + 1) := by
  have hjVar : evalExpr (.var "j") ρ = .ok (.u64 jB) :=
    evalExpr_var_hit _ _ _ hj
  have hmVar : evalExpr (.var "m") ρ = .ok (.u64 mB) :=
    evalExpr_var_hit _ _ _ hm
  have hgetB : l[jB.toNat]? = some x := by rw [hjN]; exact hx
  have hgetM : l[mB.toNat]? = some y := by rw [hmN]; exact hy
  have hatJ : evalExpr (.stdVecAt "a" (.var "j")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hjVar hgetB
  have hatM : evalExpr (.stdVecAt "a" (.var "m")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hmVar hgetM
  have hsltV : evalExpr (.slt (.stdVecAt "a" (.var "j"))
      (.stdVecAt "a" (.var "m"))) ρ = .ok (.b true) := by
    have h := evalExpr_slt_i32 (.stdVecAt "a" (.var "j"))
      (.stdVecAt "a" (.var "m")) ρ x y hatJ hatM
    rwa [htake] at h
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "m"
    (.u64 mB) (.u64 jB) hm
  have hstep_m := evalStmtFuel_assign F "m" (.var "j") ρ
    (.u64 jB) ρ₁ hjVar hu₁
  have hm₁ : envLookup ρ₁ "m" = some (.u64 jB) :=
    envLookup_update_hit _ _ _ _ hu₁
  have hj₁ : envLookup ρ₁ "j" = some (.u64 jB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("j" : String) ≠ "m" by decide) hu₁]
    exact hj
  have hevJ : evalExpr (.uadd (.var "j") (.lit (.u64 1))) ρ₁ =
      .ok (.u64 (jB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hj₁) (by simp [evalExpr, litVal])
  obtain ⟨ρ', hu₂⟩ := envUpdate_some_of_lookup ρ₁ "j"
    (.u64 jB) (.u64 (jB + 1)) hj₁
  have hstep_j := evalStmtFuel_assign F "j"
    (.uadd (.var "j") (.lit (.u64 1))) ρ₁ (.u64 (jB + 1)) ρ'
    hevJ hu₂
  have hm' : envLookup ρ' "m" = some (.u64 jB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("m" : String) ≠ "j" by decide) hu₂]
    exact hm₁
  have ha₁ : envLookup ρ₁ "a" = some (.stdVecVal l) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "m" by decide) hu₁]
    exact hv
  have ha' : envLookup ρ' "a" = some (.stdVecVal l) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "j" by decide) hu₂]
    exact ha₁
  have hjN' : (jB + 1).toNat = j + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hjN]
    exact Nat.mod_eq_of_lt (by omega)
  have hj' : envLookup ρ' "j" = some (.u64 (jB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₂
  have hif : evalStmtFuel F
      (.if_ (.slt (.stdVecAt "a" (.var "j"))
              (.stdVecAt "a" (.var "m")))
        (.assign "m" (.var "j"))
        .skip) ρ = .ok (ρ₁, .fellThrough) :=
    (evalStmtFuel_if_true F _ _ _ _ hsltV).trans hstep_m
  have hbody : minIndexStep =
      (.seq (.if_ (.slt (.stdVecAt "a" (.var "j"))
                    (.stdVecAt "a" (.var "m")))
              (.assign "m" (.var "j"))
              .skip)
        (.assign "j"
          (.uadd (.var "j") (.lit (.u64 1))))) := rfl
  have heval : evalStmtFuel F minIndexStep ρ =
      .ok (ρ', .fellThrough) := by
    rw [hbody,
      evalStmtFuel_seq_fallthrough F _ _ _ _ hif,
      hstep_j]
  exact ⟨ρ', heval, hm', ha', ⟨(jB + 1), hj', hjN'⟩⟩

/-- One leaf step (value level), skip branch: the scan test fails,
    `m` holds, `j` advances. -/
theorem valMinIndexBody_skip (F : Nat)
    (ρ : Env) (l : List (BitVec 32))
    (j m : Nat) (jB mB : BitVec 64) (x y : BitVec 32)
    (hjN : jB.toNat = j) (hmN : mB.toNat = m)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "a" = some (.stdVecVal l))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hm : envLookup ρ "m" = some (.u64 mB))
    (hlt : j < l.length)
    (hx : l[j]? = some x) (hy : l[m]? = some y)
    (hskip : (x.slt y) = false) :
    ∃ ρ', evalStmtFuel F minIndexStep ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "m" = some (.u64 mB) ∧
      envLookup ρ' "a" = some (.stdVecVal l) ∧
      (∃ jB', envLookup ρ' "j" = some (.u64 jB') ∧
        jB'.toNat = j + 1) := by
  have hjVar : evalExpr (.var "j") ρ = .ok (.u64 jB) :=
    evalExpr_var_hit _ _ _ hj
  have hmVar : evalExpr (.var "m") ρ = .ok (.u64 mB) :=
    evalExpr_var_hit _ _ _ hm
  have hgetB : l[jB.toNat]? = some x := by rw [hjN]; exact hx
  have hgetM : l[mB.toNat]? = some y := by rw [hmN]; exact hy
  have hatJ : evalExpr (.stdVecAt "a" (.var "j")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hjVar hgetB
  have hatM : evalExpr (.stdVecAt "a" (.var "m")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hmVar hgetM
  have hsltV : evalExpr (.slt (.stdVecAt "a" (.var "j"))
      (.stdVecAt "a" (.var "m"))) ρ = .ok (.b false) := by
    have h := evalExpr_slt_i32 (.stdVecAt "a" (.var "j"))
      (.stdVecAt "a" (.var "m")) ρ x y hatJ hatM
    rwa [hskip] at h
  have hskipV : evalStmtFuel F .skip ρ = .ok (ρ, .fellThrough) := by
    cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith]
  have hif : evalStmtFuel F
      (.if_ (.slt (.stdVecAt "a" (.var "j"))
              (.stdVecAt "a" (.var "m")))
        (.assign "m" (.var "j"))
        .skip) ρ = .ok (ρ, .fellThrough) :=
    (evalStmtFuel_if_false F _ _ _ _ hsltV).trans hskipV
  have hevJ : evalExpr (.uadd (.var "j") (.lit (.u64 1))) ρ =
      .ok (.u64 (jB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      hjVar (by simp [evalExpr, litVal])
  obtain ⟨ρ', hu⟩ := envUpdate_some_of_lookup ρ "j"
    (.u64 jB) (.u64 (jB + 1)) hj
  have hstep_j := evalStmtFuel_assign F "j"
    (.uadd (.var "j") (.lit (.u64 1))) ρ (.u64 (jB + 1)) ρ'
    hevJ hu
  have hm' : envLookup ρ' "m" = some (.u64 mB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("m" : String) ≠ "j" by decide) hu]
    exact hm
  have ha' : envLookup ρ' "a" = some (.stdVecVal l) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "j" by decide) hu]
    exact hv
  have hjN' : (jB + 1).toNat = j + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hjN]
    exact Nat.mod_eq_of_lt (by omega)
  have hj' : envLookup ρ' "j" = some (.u64 (jB + 1)) :=
    envLookup_update_hit _ _ _ _ hu
  have hbody : minIndexStep =
      (.seq (.if_ (.slt (.stdVecAt "a" (.var "j"))
                    (.stdVecAt "a" (.var "m")))
              (.assign "m" (.var "j"))
              .skip)
        (.assign "j"
          (.uadd (.var "j") (.lit (.u64 1))))) := rfl
  have heval : evalStmtFuel F minIndexStep ρ =
      .ok (ρ', .fellThrough) := by
    rw [hbody,
      evalStmtFuel_seq_fallthrough F _ _ _ _ hif,
      hstep_j]
  exact ⟨ρ', heval, hm', ha', ⟨(jB + 1), hj', hjN'⟩⟩

/-- Leaf loop, ok leg: the scan runs to `l.length` and the minimum
    index is the forward-model result (fuel induction threading the
    body hits; the forward equation unfolds one step per
    iteration). Two fuels: evaluation fuel and forward fuel. -/
theorem valMinIndexLoop_ok (F G : Nat)
    (ρ : Env) (l : List (BitVec 32))
    (j m : Nat) (jB mB : BitVec 64)
    (m' j' : Nat)
    (hjN : jB.toNat = j) (hmN : mB.toNat = m)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "a" = some (.stdVecVal l))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hm : envLookup ρ "m" = some (.u64 mB))
    (hmlt : m < l.length) (hle : j ≤ l.length)
    (hF : l.length - j ≤ F) (hG : l.length - j ≤ G)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (hfwd : minIndexFwd l G j m = .ok (m', j')) :
    ∃ ρ', evalStmtFuel F minIndexLoop ρ =
        .ok (ρ', .fellThrough) ∧
      (∃ mB', envLookup ρ' "m" = some (.u64 mB') ∧ mB'.toNat = m') ∧
      (∃ jB', envLookup ρ' "j" = some (.u64 jB') ∧ jB'.toNat = j') := by
  induction F generalizing G ρ l j m jB mB with
  | zero =>
    have him : j = l.length := by omega
    have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
    have hvLen : evalExpr (.stdVecLen "a") ρ =
        .ok (.u64 (BitVec.ofNat 64 l.length)) :=
      evalExpr_stdVecLen_some _ _ _ hv
    have hguardF : evalExpr (.ult (.var "j") (.stdVecLen "a")) ρ =
        .ok (.b false) := by
      have hult := evalExpr_ult_u64 (.var "j") (.stdVecLen "a")
        ρ jB (BitVec.ofNat 64 l.length)
        (evalExpr_var_hit _ _ _ hj) hvLen
      have hfb : (jB.ult (BitVec.ofNat 64 l.length)) = false := by
        rw [BitVec.ult_eq_decide]
        exact decide_eq_false (by omega)
      rwa [hfb] at hult
    have hexit : evalStmtFuel 0 minIndexLoop ρ =
        .ok (ρ, .fellThrough) :=
      evalStmtFuel_zero_while_exit _ _ _ hguardF
    have hpair : (m, j) = (m', j') := by
      cases G with
      | zero => simpa [minIndexFwd] using hfwd
      | succ G =>
        have hneg : ¬ j < l.length := by omega
        simpa [minIndexFwd, dite_eq_right hneg] using hfwd
    obtain ⟨rfl, rfl⟩ := hpair
    exact ⟨ρ, hexit, ⟨mB, hm, hmN⟩, ⟨jB, hj, hjN⟩⟩
  | succ F ih =>
    by_cases hlt : j < l.length
    · have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
      have hvLen : evalExpr (.stdVecLen "a") ρ =
          .ok (.u64 (BitVec.ofNat 64 l.length)) :=
        evalExpr_stdVecLen_some _ _ _ hv
      have hguardT : evalExpr (.ult (.var "j") (.stdVecLen "a")) ρ =
          .ok (.b true) := by
        have hult := evalExpr_ult_u64 (.var "j") (.stdVecLen "a")
          ρ jB (BitVec.ofNat 64 l.length)
          (evalExpr_var_hit _ _ _ hj) hvLen
        have htb : (jB.ult (BitVec.ofNat 64 l.length)) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true (by omega)
        rwa [htb] at hult
      obtain ⟨x, hx⟩ := hread j hlt
      obtain ⟨y, hy⟩ := hread m hmlt
      cir_fuel_step (F, G, l.length - (j + 1))
      by_cases htake : (x.slt y) = true
      · obtain ⟨ρ₁, hbody, hm₁, hva₁, ⟨jB₁, hjB₁, hjN₁⟩⟩ :=
          valMinIndexBody_take F ρ l j m jB mB x y
            hjN hmN hl64 hv hj hm hlt hx hy htake
        have hF'' : l.length - (j + 1) ≤ F := by omega
        have hG'' : l.length - (j + 1) ≤ G' := by omega
        have hfwd' : minIndexFwd l G' (j + 1) j = .ok (m', j') := by
          have h := hfwd
          simp only [minIndexFwd, dite_eq_left hlt, hx, hy, htake] at h
          exact h
        obtain ⟨ρ', hloop, ⟨mB', hmB', hmN'⟩, ⟨jB', hjB', hjN'⟩⟩ :=
          ih (G := G') (ρ := ρ₁) (l := l)
            (j := j + 1) (m := j) (jB := jB₁) (mB := jB)
            (hjN := hjN₁) (hmN := hjN) (hl64 := hl64)
            (hv := hva₁)
            (hj := hjB₁) (hm := hm₁)
            (hmlt := hlt) (hle := by omega)
            (hF := hF'') (hG := hG'')
            (hread := hread) (hfwd := hfwd')
        refine ⟨ρ', ?_, ⟨mB', hmB', hmN'⟩, ⟨jB', hjB', hjN'⟩⟩
        have hwhile : evalStmtFuel (F + 1) minIndexLoop ρ =
            evalStmtFuel F minIndexLoop ρ₁ := by
          cir_unfold_leaf (minIndexLoop, hguardT, hbody)
        rw [hwhile]
        exact hloop
      · have hskip : (x.slt y) = false := by
          cases h : x.slt y with
          | true => exact absurd h htake
          | false => rfl
        obtain ⟨ρ₁, hbody, hm₁, hva₁, ⟨jB₁, hjB₁, hjN₁⟩⟩ :=
          valMinIndexBody_skip F ρ l j m jB mB x y
            hjN hmN hl64 hv hj hm hlt hx hy hskip
        have hfwd' : minIndexFwd l G' (j + 1) m = .ok (m', j') := by
          have h := hfwd
          simp only [minIndexFwd, dite_eq_left hlt, hx, hy, hskip] at h
          exact h
        obtain ⟨ρ', hloop, ⟨mB', hmB', hmN'⟩, ⟨jB', hjB', hjN'⟩⟩ :=
          ih (G := G') (ρ := ρ₁) (l := l)
            (j := j + 1) (m := m) (jB := jB₁) (mB := mB)
            (hjN := hjN₁) (hmN := hmN) (hl64 := hl64)
            (hv := hva₁)
            (hj := hjB₁) (hm := hm₁)
            (hmlt := hmlt) (hle := by omega)
            (hF := hF') (hG := hG')
            (hread := hread) (hfwd := hfwd')
        refine ⟨ρ', ?_, ⟨mB', hmB', hmN'⟩, ⟨jB', hjB', hjN'⟩⟩
        have hwhile : evalStmtFuel (F + 1) minIndexLoop ρ =
            evalStmtFuel F minIndexLoop ρ₁ := by
          cir_unfold_leaf (minIndexLoop, hguardT, hbody)
        rw [hwhile]
        exact hloop
    · have him : j = l.length := by omega
      subst him
      have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
      have hvLen : evalExpr (.stdVecLen "a") ρ =
          .ok (.u64 (BitVec.ofNat 64 l.length)) :=
        evalExpr_stdVecLen_some _ _ _ hv
      have hguardF : evalExpr (.ult (.var "j") (.stdVecLen "a")) ρ =
          .ok (.b false) := by
        have hult := evalExpr_ult_u64 (.var "j") (.stdVecLen "a")
          ρ jB (BitVec.ofNat 64 l.length)
          (evalExpr_var_hit _ _ _ hj) hvLen
        have hfb : (jB.ult (BitVec.ofNat 64 l.length)) = false := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_false (by omega)
        rwa [hfb] at hult
      have hexit : evalStmtFuel (F + 1) minIndexLoop ρ =
          .ok (ρ, .fellThrough) := by
        simp [minIndexLoop, evalStmtFuel, evalStmtSuccHandler,
          evalStmtWith, hguardF]
      have hpair : (m, l.length) = (m', j') := by
        cases G with
        | zero => simpa [minIndexFwd] using hfwd
        | succ G =>
          have hneg : ¬ l.length < l.length := by omega
          simpa [minIndexFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl⟩ := hpair
      exact ⟨ρ, hexit, ⟨mB, hm, hmN⟩, ⟨jB, hj, hjN⟩⟩

/-- Leaf entry: the `m`/`j` prelude runs, the loop closes against
    the forward model, the minimum index word returns. -/
theorem evalFuncFuel_minIndex_ok (F G : Nat)
    (l : List (BitVec 32)) (lo : Nat) (loB : BitVec 64)
    (m j' : Nat)
    (hloN : loB.toNat = lo)
    (hl64 : l.length < 2 ^ 64)
    (hlo : lo < l.length)
    (hF : l.length - (lo + 1) ≤ F)
    (hG : l.length - (lo + 1) ≤ G)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (hfwd : minIndexFwd l G (lo + 1) lo = .ok (m, j')) :
    evalFuncFuel F minIndexFunc [.stdVecVal l, .u64 loB] =
      .ok (.u64 (BitVec.ofNat 64 m)) := by
  obtain ⟨m₀, j₀, heq, hm₀⟩ := minIndexFwd_ok l G (lo + 1) lo
    hlo (by omega) hG hread
  have hpair : (m₀, j₀) = (m, j') := by
    have h : (Except.ok (m₀, j₀) : Result (Nat × Nat)) =
        Except.ok (m, j') := by
      rw [← heq]; exact hfwd
    simpa using h
  have hm_eq : m₀ = m := congrArg Prod.fst hpair
  have hm : m < l.length := by rw [← hm_eq]; exact hm₀
  have hbind : bindArgs minIndexFunc.args
      [.stdVecVal l, .u64 loB] =
      some [("a", .stdVecVal l), ("lo", .u64 loB)] := rfl
  have hbody : minIndexFunc.body =
      (.seq (.let_ "m" (.u 64) (.var "lo"))
        (.seq (.let_ "j" (.u 64)
                (.uadd (.var "lo") (.lit (.u64 (BitVec.ofNat 64 1)))))
          (.seq minIndexLoop
            (.return_ (.var "m"))))) := rfl
  have hloV : evalExpr (.var "lo")
      [("a", .stdVecVal l), ("lo", .u64 loB)] =
      .ok (.u64 loB) := by
    simp [evalExpr, envLookup]
  have hletM := evalStmtFuel_let_ F "m" (.u 64) (.var "lo")
    [("a", .stdVecVal l), ("lo", .u64 loB)] (.u64 loB) hloV
  have hevJ : evalExpr
      (.uadd (.var "lo") (.lit (.u64 (BitVec.ofNat 64 1))))
      (envExtend [("a", .stdVecVal l), ("lo", .u64 loB)]
        "m" (.u64 loB)) =
      .ok (.u64 (loB + 1)) := by
    have h1 : evalExpr (.var "lo")
        (envExtend [("a", .stdVecVal l), ("lo", .u64 loB)]
          "m" (.u64 loB)) =
        .ok (.u64 loB) := by
      simp [evalExpr, envExtend, envLookup,
        show ("lo" : String) ≠ "m" by decide]
    exact evalExpr_uadd_u64 _ _ _ _ _
      h1 (by simp [evalExpr, litVal])
  have hletJ := evalStmtFuel_let_ F "j" (.u 64)
    (.uadd (.var "lo") (.lit (.u64 (BitVec.ofNat 64 1))))
    (envExtend [("a", .stdVecVal l), ("lo", .u64 loB)]
      "m" (.u64 loB)) (.u64 (loB + 1)) hevJ
  have hiN : (loB + 1).toNat = lo + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hloN]
    exact Nat.mod_eq_of_lt (by omega)
  have hv₁ : envLookup (envExtend (envExtend
      [("a", .stdVecVal l), ("lo", .u64 loB)]
      "m" (.u64 loB)) "j" (.u64 (loB + 1))) "a" =
      some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("a" : String) ≠ "j" by decide),
      envExtend_miss _ _ _ _
      (show ("a" : String) ≠ "m" by decide)]
    simp [envLookup]
  have hm₁ : envLookup (envExtend (envExtend
      [("a", .stdVecVal l), ("lo", .u64 loB)]
      "m" (.u64 loB)) "j" (.u64 (loB + 1))) "m" =
      some (.u64 loB) := by
    rw [envExtend_miss _ _ _ _
      (show ("m" : String) ≠ "j" by decide)]
    exact envExtend_hit _ _ _
  have hj₁ : envLookup (envExtend (envExtend
      [("a", .stdVecVal l), ("lo", .u64 loB)]
      "m" (.u64 loB)) "j" (.u64 (loB + 1))) "j" =
      some (.u64 (loB + 1)) :=
    envExtend_hit _ _ _
  obtain ⟨ρ', hloop, ⟨mB', hmB', hmN'⟩, ⟨jB', hjB', hjN'⟩⟩ :=
    valMinIndexLoop_ok F G
      (envExtend (envExtend [("a", .stdVecVal l), ("lo", .u64 loB)]
        "m" (.u64 loB)) "j" (.u64 (loB + 1)))
      l (lo + 1) lo (loB + 1) loB m j'
      hiN hloN hl64 hv₁ hj₁ hm₁ hlo (by omega) hF hG hread hfwd
  have hm64 : m < 2 ^ 64 := by omega
  have hword : mB' = BitVec.ofNat 64 m := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, hmN']
    exact (Nat.mod_eq_of_lt hm64).symm
  have hretV : evalExpr (.var "m") ρ' =
      .ok (.u64 (BitVec.ofNat 64 m)) := by
    rw [← hword]
    exact evalExpr_var_hit _ _ _ hmB'
  have hret := evalStmtFuel_return F (.var "m") ρ'
    (.u64 (BitVec.ofNat 64 m)) hretV
  simp only [evalFuncFuel, hbind, hbody]
  rw [evalStmtFuel_seq_fallthrough F _ _ _ _ hletM,
    evalStmtFuel_seq_fallthrough F _ _ _ _ hletJ,
    evalStmtFuel_seq_fallthrough F _ _ _ _ hloop,
    hret]

/-! ## Leaf memory proofs (fuel level) -/

/-- One leaf step on memory, take branch: the env threads exactly
    as on the value side (memory untouched — the leaf never
    stores). -/
theorem memMinIndexBody_take (F : Nat)
    (ρ : Env) (mm : Mem) (π : Layout)
    (l : List (BitVec 32))
    (j m : Nat) (jB mB : BitVec 64) (x y : BitVec 32)
    (a t : Nat) (n : BitVec 32)
    (hjN : jB.toNat = j) (hmN : mB.toNat = m)
    (hl64 : l.length < 2 ^ 64)
    (hlay : layoutLookup π "a" = some (a, t))
    (hmem : memFind mm a = some ⟨t, true, n :: l⟩)
    (hv : envLookup ρ "a" = some (.stdVecVal l))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hm : envLookup ρ "m" = some (.u64 mB))
    (hlt : j < l.length)
    (hx : l[j]? = some x) (hy : l[m]? = some y)
    (htake : (x.slt y) = true) :
    ∃ ρ', memEvalStmtFuel F minIndexStep ρ mm π =
        .ok ((ρ', mm, π), .fellThrough) ∧
      envLookup ρ' "m" = some (.u64 jB) ∧
      envLookup ρ' "a" = some (.stdVecVal l) ∧
      (∃ jB', envLookup ρ' "j" = some (.u64 jB') ∧
        jB'.toNat = j + 1) ∧
      memFind mm a = some ⟨t, true, n :: l⟩ := by
  have hjVarA : memEvalExpr (.var "j") ρ mm π =
      evalExpr (.var "j") ρ :=
    memEvalExpr_var _ _ _ _
  have hmVarA : memEvalExpr (.var "m") ρ mm π =
      evalExpr (.var "m") ρ :=
    memEvalExpr_var _ _ _ _
  have hjVar : evalExpr (.var "j") ρ = .ok (.u64 jB) :=
    evalExpr_var_hit _ _ _ hj
  have hmVar : evalExpr (.var "m") ρ = .ok (.u64 mB) :=
    evalExpr_var_hit _ _ _ hm
  have hgetB : l[jB.toNat]? = some x := by rw [hjN]; exact hx
  have hgetM : l[mB.toNat]? = some y := by rw [hmN]; exact hy
  have hmemA : memLoad mm a t (jB.toNat + 1) = .ok x :=
    memLoad_cellsAt mm a t (jB.toNat + 1) (n :: l) x
      hmem (by rw [List.getElem?_cons_succ]; exact hgetB)
  have hmemM : memLoad mm a t (mB.toNat + 1) = .ok y :=
    memLoad_cellsAt mm a t (mB.toNat + 1) (n :: l) y
      hmem (by rw [List.getElem?_cons_succ]; exact hgetM)
  have hatM_ag : memEvalExpr (.stdVecAt "a" (.var "j")) ρ mm π =
      evalExpr (.stdVecAt "a" (.var "j")) ρ :=
    memEvalExpr_stdVecAt_hit "a" (.var "j") ρ mm π l jB x a t
      hlay hv hjVarA hjVar hmemA hgetB
  have hmM_ag : memEvalExpr (.stdVecAt "a" (.var "m")) ρ mm π =
      evalExpr (.stdVecAt "a" (.var "m")) ρ :=
    memEvalExpr_stdVecAt_hit "a" (.var "m") ρ mm π l mB y a t
      hlay hv hmVarA hmVar hmemM hgetM
  have hatJ : evalExpr (.stdVecAt "a" (.var "j")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hjVar hgetB
  have hatM : evalExpr (.stdVecAt "a" (.var "m")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hmVar hgetM
  have hsltV : evalExpr (.slt (.stdVecAt "a" (.var "j"))
      (.stdVecAt "a" (.var "m"))) ρ = .ok (.b true) := by
    have h := evalExpr_slt_i32 (.stdVecAt "a" (.var "j"))
      (.stdVecAt "a" (.var "m")) ρ x y hatJ hatM
    rwa [htake] at h
  have hsltM : memEvalExpr (.slt (.stdVecAt "a" (.var "j"))
      (.stdVecAt "a" (.var "m"))) ρ mm π = .ok (.b true) :=
    (memEvalExpr_slt_agree (.stdVecAt "a" (.var "j"))
      (.stdVecAt "a" (.var "m")) ρ mm π hatM_ag hmM_ag).trans hsltV
  have hjVarM : memEvalExpr (.var "j") ρ mm π = .ok (.u64 jB) :=
    hjVarA.trans hjVar
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "m"
    (.u64 mB) (.u64 jB) hm
  have hstep_m := memEvalStmtFuel_assign F "m" (.var "j")
    ρ mm π (.u64 jB) ρ₁ hjVarA hjVar hu₁
  have hm₁ : envLookup ρ₁ "m" = some (.u64 jB) :=
    envLookup_update_hit _ _ _ _ hu₁
  have hj₁ : envLookup ρ₁ "j" = some (.u64 jB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("j" : String) ≠ "m" by decide) hu₁]
    exact hj
  have ha₁ : envLookup ρ₁ "a" = some (.stdVecVal l) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "m" by decide) hu₁]
    exact hv
  have hjVarA₁ : memEvalExpr (.var "j") ρ₁ mm π =
      evalExpr (.var "j") ρ₁ :=
    memEvalExpr_var _ _ _ _
  have hevJ : evalExpr (.uadd (.var "j") (.lit (.u64 1))) ρ₁ =
      .ok (.u64 (jB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hj₁) (by simp [evalExpr, litVal])
  have hevJM_ag : memEvalExpr
      (.uadd (.var "j") (.lit (.u64 1))) ρ₁ mm π =
      evalExpr (.uadd (.var "j") (.lit (.u64 1))) ρ₁ :=
    memEvalExpr_uadd_agree (.var "j") (.lit (.u64 1))
      ρ₁ mm π hjVarA₁ (memEvalExpr_lit _ _ _ _)
  have hevJM : memEvalExpr
      (.uadd (.var "j") (.lit (.u64 1))) ρ₁ mm π =
      .ok (.u64 (jB + 1)) :=
    hevJM_ag.trans hevJ
  obtain ⟨ρ', hu₂⟩ := envUpdate_some_of_lookup ρ₁ "j"
    (.u64 jB) (.u64 (jB + 1)) hj₁
  have hstep_j := memEvalStmtFuel_assign F "j"
    (.uadd (.var "j") (.lit (.u64 1))) ρ₁ mm π (.u64 (jB + 1)) ρ'
    hevJM_ag hevJ hu₂
  have hm' : envLookup ρ' "m" = some (.u64 jB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("m" : String) ≠ "j" by decide) hu₂]
    exact hm₁
  have ha' : envLookup ρ' "a" = some (.stdVecVal l) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "j" by decide) hu₂]
    exact ha₁
  have hjN' : (jB + 1).toNat = j + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hjN]
    exact Nat.mod_eq_of_lt (by omega)
  have hj' : envLookup ρ' "j" = some (.u64 (jB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₂
  have hif : memEvalStmtFuel F
      (.if_ (.slt (.stdVecAt "a" (.var "j"))
              (.stdVecAt "a" (.var "m")))
        (.assign "m" (.var "j"))
        .skip) ρ mm π = .ok ((ρ₁, mm, π), .fellThrough) :=
    (memEvalStmtFuel_if_true F _ _ _ _ _ _ hsltM).trans hstep_m
  have hbody : minIndexStep =
      (.seq (.if_ (.slt (.stdVecAt "a" (.var "j"))
                    (.stdVecAt "a" (.var "m")))
              (.assign "m" (.var "j"))
              .skip)
        (.assign "j"
          (.uadd (.var "j") (.lit (.u64 1))))) := rfl
  have heval : memEvalStmtFuel F minIndexStep ρ mm π =
      .ok ((ρ', mm, π), .fellThrough) := by
    rw [hbody,
      memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _ hif,
      hstep_j]
  exact ⟨ρ', heval, hm', ha', ⟨(jB + 1), hj', hjN'⟩, hmem⟩

/-- One leaf step on memory, skip branch. -/
theorem memMinIndexBody_skip (F : Nat)
    (ρ : Env) (mm : Mem) (π : Layout)
    (l : List (BitVec 32))
    (j m : Nat) (jB mB : BitVec 64) (x y : BitVec 32)
    (a t : Nat) (n : BitVec 32)
    (hjN : jB.toNat = j) (hmN : mB.toNat = m)
    (hl64 : l.length < 2 ^ 64)
    (hlay : layoutLookup π "a" = some (a, t))
    (hmem : memFind mm a = some ⟨t, true, n :: l⟩)
    (hv : envLookup ρ "a" = some (.stdVecVal l))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hm : envLookup ρ "m" = some (.u64 mB))
    (hlt : j < l.length)
    (hx : l[j]? = some x) (hy : l[m]? = some y)
    (hskip : (x.slt y) = false) :
    ∃ ρ', memEvalStmtFuel F minIndexStep ρ mm π =
        .ok ((ρ', mm, π), .fellThrough) ∧
      envLookup ρ' "m" = some (.u64 mB) ∧
      envLookup ρ' "a" = some (.stdVecVal l) ∧
      (∃ jB', envLookup ρ' "j" = some (.u64 jB') ∧
        jB'.toNat = j + 1) ∧
      memFind mm a = some ⟨t, true, n :: l⟩ := by
  have hjVarA : memEvalExpr (.var "j") ρ mm π =
      evalExpr (.var "j") ρ :=
    memEvalExpr_var _ _ _ _
  have hmVarA : memEvalExpr (.var "m") ρ mm π =
      evalExpr (.var "m") ρ :=
    memEvalExpr_var _ _ _ _
  have hjVar : evalExpr (.var "j") ρ = .ok (.u64 jB) :=
    evalExpr_var_hit _ _ _ hj
  have hmVar : evalExpr (.var "m") ρ = .ok (.u64 mB) :=
    evalExpr_var_hit _ _ _ hm
  have hgetB : l[jB.toNat]? = some x := by rw [hjN]; exact hx
  have hgetM : l[mB.toNat]? = some y := by rw [hmN]; exact hy
  have hmemA : memLoad mm a t (jB.toNat + 1) = .ok x :=
    memLoad_cellsAt mm a t (jB.toNat + 1) (n :: l) x
      hmem (by rw [List.getElem?_cons_succ]; exact hgetB)
  have hmemM : memLoad mm a t (mB.toNat + 1) = .ok y :=
    memLoad_cellsAt mm a t (mB.toNat + 1) (n :: l) y
      hmem (by rw [List.getElem?_cons_succ]; exact hgetM)
  have hatM_ag : memEvalExpr (.stdVecAt "a" (.var "j")) ρ mm π =
      evalExpr (.stdVecAt "a" (.var "j")) ρ :=
    memEvalExpr_stdVecAt_hit "a" (.var "j") ρ mm π l jB x a t
      hlay hv hjVarA hjVar hmemA hgetB
  have hmM_ag : memEvalExpr (.stdVecAt "a" (.var "m")) ρ mm π =
      evalExpr (.stdVecAt "a" (.var "m")) ρ :=
    memEvalExpr_stdVecAt_hit "a" (.var "m") ρ mm π l mB y a t
      hlay hv hmVarA hmVar hmemM hgetM
  have hatJ : evalExpr (.stdVecAt "a" (.var "j")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hjVar hgetB
  have hatM : evalExpr (.stdVecAt "a" (.var "m")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hmVar hgetM
  have hsltV : evalExpr (.slt (.stdVecAt "a" (.var "j"))
      (.stdVecAt "a" (.var "m"))) ρ = .ok (.b false) := by
    have h := evalExpr_slt_i32 (.stdVecAt "a" (.var "j"))
      (.stdVecAt "a" (.var "m")) ρ x y hatJ hatM
    rwa [hskip] at h
  have hsltM : memEvalExpr (.slt (.stdVecAt "a" (.var "j"))
      (.stdVecAt "a" (.var "m"))) ρ mm π = .ok (.b false) :=
    (memEvalExpr_slt_agree (.stdVecAt "a" (.var "j"))
      (.stdVecAt "a" (.var "m")) ρ mm π hatM_ag hmM_ag).trans hsltV
  have hskipV : memEvalStmtFuel F .skip ρ mm π =
      .ok ((ρ, mm, π), .fellThrough) := by
    cases F <;> simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith]
  have hif : memEvalStmtFuel F
      (.if_ (.slt (.stdVecAt "a" (.var "j"))
              (.stdVecAt "a" (.var "m")))
        (.assign "m" (.var "j"))
        .skip) ρ mm π = .ok ((ρ, mm, π), .fellThrough) :=
    (memEvalStmtFuel_if_false F _ _ _ _ _ _ hsltM).trans hskipV
  have hevJ : evalExpr (.uadd (.var "j") (.lit (.u64 1))) ρ =
      .ok (.u64 (jB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      hjVar (by simp [evalExpr, litVal])
  have hjVarA' : memEvalExpr (.var "j") ρ mm π =
      evalExpr (.var "j") ρ :=
    memEvalExpr_var _ _ _ _
  obtain ⟨ρ', hu⟩ := envUpdate_some_of_lookup ρ "j"
    (.u64 jB) (.u64 (jB + 1)) hj
  have hevJM_ag : memEvalExpr
      (.uadd (.var "j") (.lit (.u64 1))) ρ mm π =
      evalExpr (.uadd (.var "j") (.lit (.u64 1))) ρ :=
    memEvalExpr_uadd_agree (.var "j") (.lit (.u64 1))
      ρ mm π hjVarA' (memEvalExpr_lit _ _ _ _)
  have hstep_j := memEvalStmtFuel_assign F "j"
    (.uadd (.var "j") (.lit (.u64 1))) ρ mm π (.u64 (jB + 1)) ρ'
    hevJM_ag hevJ hu
  have hm' : envLookup ρ' "m" = some (.u64 mB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("m" : String) ≠ "j" by decide) hu]
    exact hm
  have ha' : envLookup ρ' "a" = some (.stdVecVal l) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "j" by decide) hu]
    exact hv
  have hjN' : (jB + 1).toNat = j + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hjN]
    exact Nat.mod_eq_of_lt (by omega)
  have hj' : envLookup ρ' "j" = some (.u64 (jB + 1)) :=
    envLookup_update_hit _ _ _ _ hu
  have hbody : minIndexStep =
      (.seq (.if_ (.slt (.stdVecAt "a" (.var "j"))
                    (.stdVecAt "a" (.var "m")))
              (.assign "m" (.var "j"))
              .skip)
        (.assign "j"
          (.uadd (.var "j") (.lit (.u64 1))))) := rfl
  have heval : memEvalStmtFuel F minIndexStep ρ mm π =
      .ok ((ρ', mm, π), .fellThrough) := by
    rw [hbody,
      memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _ hif,
      hstep_j]
  exact ⟨ρ', heval, hm', ha', ⟨(jB + 1), hj', hjN'⟩, hmem⟩

/-- Leaf memory loop, ok leg. -/
theorem memMinIndexLoop_ok (F G : Nat)
    (ρ : Env) (mm : Mem) (π : Layout)
    (l : List (BitVec 32))
    (j m : Nat) (jB mB : BitVec 64)
    (m' j' : Nat)
    (a t : Nat) (n : BitVec 32)
    (hjN : jB.toNat = j) (hmN : mB.toNat = m)
    (hl64 : l.length < 2 ^ 64)
    (hlay : layoutLookup π "a" = some (a, t))
    (hmem : memFind mm a = some ⟨t, true, n :: l⟩)
    (hn : n = BitVec.ofNat 32 l.length)
    (hv : envLookup ρ "a" = some (.stdVecVal l))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hm : envLookup ρ "m" = some (.u64 mB))
    (hmlt : m < l.length) (hle : j ≤ l.length)
    (hF : l.length - j ≤ F) (hG : l.length - j ≤ G)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (hfwd : minIndexFwd l G j m = .ok (m', j')) :
    ∃ ρ', memEvalStmtFuel F minIndexLoop ρ mm π =
        .ok ((ρ', mm, π), .fellThrough) ∧
      (∃ mB', envLookup ρ' "m" = some (.u64 mB') ∧ mB'.toNat = m') ∧
      (∃ jB', envLookup ρ' "j" = some (.u64 jB') ∧ jB'.toNat = j') ∧
      memFind mm a = some ⟨t, true, n :: l⟩ := by
  induction F generalizing G ρ mm l j m jB mB with
  | zero =>
    have him : j = l.length := by omega
    have hmemLen : memLoad mm a t 0 =
        .ok (BitVec.ofNat 32 l.length) := by
      rw [← hn]
      exact memLoad_cellsAt mm a t 0 (n :: l) n hmem (by simp)
    have hguardF : memEvalExpr
        (.ult (.var "j") (.stdVecLen "a")) ρ mm π =
        .ok (.b false) := by
      have hag : memEvalExpr
          (.ult (.var "j") (.stdVecLen "a")) ρ mm π =
          evalExpr (.ult (.var "j") (.stdVecLen "a")) ρ :=
        memEvalExpr_ult_agree (.var "j") (.stdVecLen "a") ρ mm π
          (memEvalExpr_var _ _ _ _)
          (memEvalExpr_stdVecLen_hit "a" ρ mm π l a t
            hlay hv hmemLen)
      have hval : evalExpr (.ult (.var "j") (.stdVecLen "a")) ρ =
          .ok (.b false) := by
        have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
          rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
        have hvLen : evalExpr (.stdVecLen "a") ρ =
            .ok (.u64 (BitVec.ofNat 64 l.length)) :=
          evalExpr_stdVecLen_some _ _ _ hv
        have hjVar : evalExpr (.var "j") ρ = .ok (.u64 jB) :=
          evalExpr_var_hit _ _ _ hj
        have hult := evalExpr_ult_u64 (.var "j") (.stdVecLen "a")
          ρ jB (BitVec.ofNat 64 l.length) hjVar hvLen
        have hfb : (jB.ult (BitVec.ofNat 64 l.length)) = false := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_false (by omega)
        rwa [hfb] at hult
      rw [hag]; exact hval
    have hexit : memEvalStmtFuel 0 minIndexLoop ρ mm π =
        .ok ((ρ, mm, π), .fellThrough) :=
      memEvalStmtFuel_while_false 0 _ _ ρ mm π hguardF
    have hpair : (m, j) = (m', j') := by
      cases G with
      | zero => simpa [minIndexFwd] using hfwd
      | succ G =>
        have hneg : ¬ j < l.length := by omega
        simpa [minIndexFwd, dite_eq_right hneg] using hfwd
    obtain ⟨rfl, rfl⟩ := hpair
    exact ⟨ρ, hexit, ⟨mB, hm, hmN⟩, ⟨jB, hj, hjN⟩, hmem⟩
  | succ F ih =>
    by_cases hlt : j < l.length
    · have hmemLen : memLoad mm a t 0 =
          .ok (BitVec.ofNat 32 l.length) := by
        rw [← hn]
        exact memLoad_cellsAt mm a t 0 (n :: l) n hmem (by simp)
      have hguardT : memEvalExpr
          (.ult (.var "j") (.stdVecLen "a")) ρ mm π =
          .ok (.b true) := by
        have hag : memEvalExpr
            (.ult (.var "j") (.stdVecLen "a")) ρ mm π =
            evalExpr (.ult (.var "j") (.stdVecLen "a")) ρ :=
          memEvalExpr_ult_agree (.var "j") (.stdVecLen "a") ρ mm π
            (memEvalExpr_var _ _ _ _)
            (memEvalExpr_stdVecLen_hit "a" ρ mm π l a t
              hlay hv hmemLen)
        have hval : evalExpr (.ult (.var "j") (.stdVecLen "a")) ρ =
            .ok (.b true) := by
          have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
            rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
          have hvLen : evalExpr (.stdVecLen "a") ρ =
              .ok (.u64 (BitVec.ofNat 64 l.length)) :=
            evalExpr_stdVecLen_some _ _ _ hv
          have hjVar : evalExpr (.var "j") ρ = .ok (.u64 jB) :=
            evalExpr_var_hit _ _ _ hj
          have hult := evalExpr_ult_u64 (.var "j") (.stdVecLen "a")
            ρ jB (BitVec.ofNat 64 l.length) hjVar hvLen
          have htb : (jB.ult (BitVec.ofNat 64 l.length)) = true := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_true (by omega)
          rwa [htb] at hult
        rw [hag]; exact hval
      obtain ⟨x, hx⟩ := hread j hlt
      obtain ⟨y, hy⟩ := hread m hmlt
      cir_fuel_step (F, G, l.length - (j + 1))
      by_cases htake : (x.slt y) = true
      · obtain ⟨ρ₁, hbody, hm₁, hva₁, ⟨jB₁, hjB₁, hjN₁⟩,
            hmem₁⟩ :=
          memMinIndexBody_take F ρ mm π l j m jB mB x y
            a t n hjN hmN hl64 hlay hmem hv hj hm
            hlt hx hy htake
        have hF'' : l.length - (j + 1) ≤ F := by omega
        have hG'' : l.length - (j + 1) ≤ G' := by omega
        have hfwd' : minIndexFwd l G' (j + 1) j = .ok (m', j') := by
          have h := hfwd
          simp only [minIndexFwd, dite_eq_left hlt, hx, hy, htake] at h
          exact h
        obtain ⟨ρ', hloop, ⟨mB', hmB', hmN'⟩, ⟨jB', hjB', hjN'⟩,
            hmem'⟩ :=
          ih (G := G') (ρ := ρ₁) (mm := mm) (l := l)
            (j := j + 1) (m := j) (jB := jB₁) (mB := jB)
            (hjN := hjN₁) (hmN := hjN) (hl64 := hl64)
            (hmem := hmem) (hn := hn)
            (hv := hva₁)
            (hj := hjB₁) (hm := hm₁)
            (hmlt := hlt) (hle := by omega)
            (hF := hF'') (hG := hG'')
            (hread := hread) (hfwd := hfwd')
        refine ⟨ρ', ?_, ⟨mB', hmB', hmN'⟩, ⟨jB', hjB', hjN'⟩, hmem'⟩
        have hwhile : memEvalStmtFuel (F + 1) minIndexLoop
            ρ mm π =
            memEvalStmtFuel F minIndexLoop ρ₁ mm π := by
          simp only [minIndexLoop,
            memEvalStmtFuel_while_true F _ _ ρ mm π hguardT,
            hbody]
        rw [hwhile]
        exact hloop
      · have hskip : (x.slt y) = false := by
          cases h : x.slt y with
          | true => exact absurd h htake
          | false => rfl
        obtain ⟨ρ₁, hbody, hm₁, hva₁, ⟨jB₁, hjB₁, hjN₁⟩,
            hmem₁⟩ :=
          memMinIndexBody_skip F ρ mm π l j m jB mB x y
            a t n hjN hmN hl64 hlay hmem hv hj hm
            hlt hx hy hskip
        have hfwd' : minIndexFwd l G' (j + 1) m = .ok (m', j') := by
          have h := hfwd
          simp only [minIndexFwd, dite_eq_left hlt, hx, hy, hskip] at h
          exact h
        obtain ⟨ρ', hloop, ⟨mB', hmB', hmN'⟩, ⟨jB', hjB', hjN'⟩,
            hmem'⟩ :=
          ih (G := G') (ρ := ρ₁) (mm := mm) (l := l)
            (j := j + 1) (m := m) (jB := jB₁) (mB := mB)
            (hjN := hjN₁) (hmN := hmN) (hl64 := hl64)
            (hmem := hmem) (hn := hn)
            (hv := hva₁)
            (hj := hjB₁) (hm := hm₁)
            (hmlt := hmlt) (hle := by omega)
            (hF := hF') (hG := hG')
            (hread := hread) (hfwd := hfwd')
        refine ⟨ρ', ?_, ⟨mB', hmB', hmN'⟩, ⟨jB', hjB', hjN'⟩, hmem'⟩
        have hwhile : memEvalStmtFuel (F + 1) minIndexLoop
            ρ mm π =
            memEvalStmtFuel F minIndexLoop ρ₁ mm π := by
          simp only [minIndexLoop,
            memEvalStmtFuel_while_true F _ _ ρ mm π hguardT,
            hbody]
        rw [hwhile]
        exact hloop
    · have him : j = l.length := by omega
      subst him
      have hmemLen : memLoad mm a t 0 =
          .ok (BitVec.ofNat 32 l.length) := by
        rw [← hn]
        exact memLoad_cellsAt mm a t 0 (n :: l) n hmem (by simp)
      have hguardF : memEvalExpr
          (.ult (.var "j") (.stdVecLen "a")) ρ mm π =
          .ok (.b false) := by
        have hag : memEvalExpr
            (.ult (.var "j") (.stdVecLen "a")) ρ mm π =
            evalExpr (.ult (.var "j") (.stdVecLen "a")) ρ :=
          memEvalExpr_ult_agree (.var "j") (.stdVecLen "a") ρ mm π
            (memEvalExpr_var _ _ _ _)
            (memEvalExpr_stdVecLen_hit "a" ρ mm π l a t
              hlay hv hmemLen)
        have hval : evalExpr (.ult (.var "j") (.stdVecLen "a")) ρ =
            .ok (.b false) := by
          have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
            rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
          have hvLen : evalExpr (.stdVecLen "a") ρ =
              .ok (.u64 (BitVec.ofNat 64 l.length)) :=
            evalExpr_stdVecLen_some _ _ _ hv
          have hjVar : evalExpr (.var "j") ρ = .ok (.u64 jB) :=
            evalExpr_var_hit _ _ _ hj
          have hult := evalExpr_ult_u64 (.var "j") (.stdVecLen "a")
            ρ jB (BitVec.ofNat 64 l.length) hjVar hvLen
          have hfb : (jB.ult (BitVec.ofNat 64 l.length)) = false := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_false (by omega)
          rwa [hfb] at hult
        rw [hag]; exact hval
      have hexit : memEvalStmtFuel (F + 1) minIndexLoop
          ρ mm π =
          .ok ((ρ, mm, π), .fellThrough) :=
        memEvalStmtFuel_while_false (F + 1) _ _ ρ mm π hguardF
      have hpair : (m, l.length) = (m', j') := by
        cases G with
        | zero => simpa [minIndexFwd] using hfwd
        | succ G =>
          have hneg : ¬ l.length < l.length := by omega
          simpa [minIndexFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl⟩ := hpair
      exact ⟨ρ, hexit, ⟨mB, hm, hmN⟩, ⟨jB, hj, hjN⟩, hmem⟩

/-- Leaf memory entry: the `m`/`j` prelude runs on memory, the loop
    closes against the forward model, the minimum index word
    returns. -/
theorem memEvalFuncFuel_minIndex_ok (F G : Nat)
    (l : List (BitVec 32)) (lo : Nat) (loB : BitVec 64)
    (m j' : Nat)
    (hloN : loB.toNat = lo)
    (hl64 : l.length < 2 ^ 64)
    (hlo : lo < l.length)
    (hF : l.length - (lo + 1) ≤ F)
    (hG : l.length - (lo + 1) ≤ G)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (hfwd : minIndexFwd l G (lo + 1) lo = .ok (m, j')) :
    memEvalFuncFuel F minIndexFunc [.stdVecVal l, .u64 loB] =
      .ok (.u64 (BitVec.ofNat 64 m)) := by
  obtain ⟨m₀, j₀, heq, hm₀⟩ := minIndexFwd_ok l G (lo + 1) lo
    hlo (by omega) hG hread
  have hpair : (m₀, j₀) = (m, j') := by
    have h : (Except.ok (m₀, j₀) : Result (Nat × Nat)) =
        Except.ok (m, j') := by
      rw [← heq]; exact hfwd
    simpa using h
  have hm_eq : m₀ = m := congrArg Prod.fst hpair
  have hm : m < l.length := by rw [← hm_eq]; exact hm₀
  have hbind := bindMemArgs_minIndex l loB
  have hbody : minIndexFunc.body =
      (.seq (.let_ "m" (.u 64) (.var "lo"))
        (.seq (.let_ "j" (.u 64)
                (.uadd (.var "lo") (.lit (.u64 (BitVec.ofNat 64 1)))))
          (.seq minIndexLoop
            (.return_ (.var "m"))))) := rfl
  have hmem : memFind
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ 0 =
      some ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩ :=
    memFind_cons_hit _ _ _ _ _
  have hlay : layoutLookup [("a", 0, 0)] "a" =
      some (0, 0) := by simp [layoutLookup]
  have hloV : evalExpr (.var "lo")
      [("a", .stdVecVal l), ("lo", .u64 loB)] =
      .ok (.u64 loB) := by
    simp [evalExpr, envLookup]
  have hloA : memEvalExpr (.var "lo")
      [("a", .stdVecVal l), ("lo", .u64 loB)]
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("a", 0, 0)] =
      evalExpr (.var "lo")
        [("a", .stdVecVal l), ("lo", .u64 loB)] :=
    memEvalExpr_var _ _ _ _
  have hletM := memEvalStmtFuel_let_pure F "m" (.u 64) (.var "lo")
    [("a", .stdVecVal l), ("lo", .u64 loB)]
    ⟨1, [(0, ⟨0, true,
      (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
    [("a", 0, 0)] (.u64 loB)
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) hloA hloV
  have hevJ : evalExpr
      (.uadd (.var "lo") (.lit (.u64 (BitVec.ofNat 64 1))))
      (envExtend [("a", .stdVecVal l), ("lo", .u64 loB)]
        "m" (.u64 loB)) =
      .ok (.u64 (loB + 1)) := by
    have h1 : evalExpr (.var "lo")
        (envExtend [("a", .stdVecVal l), ("lo", .u64 loB)]
          "m" (.u64 loB)) =
        .ok (.u64 loB) := by
      simp [evalExpr, envExtend, envLookup,
        show ("lo" : String) ≠ "m" by decide]
    exact evalExpr_uadd_u64 _ _ _ _ _
      h1 (by simp [evalExpr, litVal])
  have hevJA : memEvalExpr
      (.uadd (.var "lo") (.lit (.u64 (BitVec.ofNat 64 1))))
      (envExtend [("a", .stdVecVal l), ("lo", .u64 loB)]
        "m" (.u64 loB))
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("a", 0, 0)] =
      evalExpr
        (.uadd (.var "lo") (.lit (.u64 (BitVec.ofNat 64 1))))
        (envExtend [("a", .stdVecVal l), ("lo", .u64 loB)]
          "m" (.u64 loB)) :=
    memEvalExpr_uadd_agree (.var "lo") (.lit (.u64 (BitVec.ofNat 64 1)))
      (envExtend [("a", .stdVecVal l), ("lo", .u64 loB)]
        "m" (.u64 loB))
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("a", 0, 0)]
      (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)
  have hletJ := memEvalStmtFuel_let_pure F "j" (.u 64)
    (.uadd (.var "lo") (.lit (.u64 (BitVec.ofNat 64 1))))
    (envExtend [("a", .stdVecVal l), ("lo", .u64 loB)]
      "m" (.u64 loB))
    ⟨1, [(0, ⟨0, true,
      (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
    [("a", 0, 0)] (.u64 (loB + 1))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) hevJA hevJ
  have hiN : (loB + 1).toNat = lo + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hloN]
    exact Nat.mod_eq_of_lt (by omega)
  have hv₁ : envLookup (envExtend (envExtend
      [("a", .stdVecVal l), ("lo", .u64 loB)]
      "m" (.u64 loB)) "j" (.u64 (loB + 1))) "a" =
      some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("a" : String) ≠ "j" by decide),
      envExtend_miss _ _ _ _
      (show ("a" : String) ≠ "m" by decide)]
    simp [envLookup]
  have hm₁ : envLookup (envExtend (envExtend
      [("a", .stdVecVal l), ("lo", .u64 loB)]
      "m" (.u64 loB)) "j" (.u64 (loB + 1))) "m" =
      some (.u64 loB) := by
    rw [envExtend_miss _ _ _ _
      (show ("m" : String) ≠ "j" by decide)]
    exact envExtend_hit _ _ _
  have hj₁ : envLookup (envExtend (envExtend
      [("a", .stdVecVal l), ("lo", .u64 loB)]
      "m" (.u64 loB)) "j" (.u64 (loB + 1))) "j" =
      some (.u64 (loB + 1)) :=
    envExtend_hit _ _ _
  obtain ⟨ρ', hloop, ⟨mB', hmB', hmN'⟩, ⟨jB', hjB', hjN'⟩,
      _hmem'⟩ :=
    memMinIndexLoop_ok F G
      (envExtend (envExtend [("a", .stdVecVal l), ("lo", .u64 loB)]
        "m" (.u64 loB)) "j" (.u64 (loB + 1)))
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("a", 0, 0)]
      l (lo + 1) lo (loB + 1) loB m j' 0 0
      (BitVec.ofNat 32 l.length)
      hiN hloN hl64 hlay hmem rfl hv₁ hj₁ hm₁
      hlo (by omega) hF hG hread hfwd
  have hm64 : m < 2 ^ 64 := by omega
  have hword : mB' = BitVec.ofNat 64 m := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, hmN']
    exact (Nat.mod_eq_of_lt hm64).symm
  have hretV : evalExpr (.var "m") ρ' =
      .ok (.u64 (BitVec.ofNat 64 m)) := by
    rw [← hword]
    exact evalExpr_var_hit _ _ _ hmB'
  have hretA : memEvalExpr (.var "m") ρ'
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("a", 0, 0)] = evalExpr (.var "m") ρ' :=
    memEvalExpr_var _ _ _ _
  have hret := memEvalStmtFuel_return F (.var "m") ρ'
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("a", 0, 0)] (.u64 (BitVec.ofNat 64 m)) hretA hretV
  -- `let_pure` concludes cons-form envs; fold to `envExtend` form
  -- (definitionally equal) for the rewrite chain.
  have hletM' : memEvalStmtFuel F (.let_ "m" (.u 64) (.var "lo"))
      [("a", .stdVecVal l), ("lo", .u64 loB)]
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("a", 0, 0)] =
      .ok ((envExtend [("a", .stdVecVal l), ("lo", .u64 loB)]
        "m" (.u64 loB), ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("a", 0, 0)]), .fellThrough) := hletM
  have hletJ' : memEvalStmtFuel F
      (.let_ "j" (.u 64)
        (.uadd (.var "lo") (.lit (.u64 (BitVec.ofNat 64 1)))))
      (envExtend [("a", .stdVecVal l), ("lo", .u64 loB)]
        "m" (.u64 loB))
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("a", 0, 0)] =
      .ok ((envExtend (envExtend [("a", .stdVecVal l), ("lo", .u64 loB)]
        "m" (.u64 loB)) "j" (.u64 (loB + 1)),
        ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("a", 0, 0)]), .fellThrough) := hletJ
  simp only [memEvalFuncFuel, hbind, hbody]
  rw [memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _ hletM',
    memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _ hletJ',
    memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _ hloop,
    hret]

/-! ## Outer value proofs (program level) -/

/-- One outer iteration (value level): the leaf call returns the
    minimum word, the unconditional swap writes through, `i`
    advances. The leaf runs at the current program fuel; its model
    shares the fixed inner budget `G`. -/
theorem valSelectionSortBody_ok (F G : Nat)
    (ρ : Env) (l : List (BitVec 32))
    (i : Nat) (iB : BitVec 64)
    (m j' : Nat) (x y : BitVec 32)
    (hiN : iB.toNat = i)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hn : envLookup ρ "n" = some (.u64 (BitVec.ofNat 64 l.length)))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hlt : i < l.length)
    (hF : l.length - (i + 1) ≤ F)
    (hG : l.length - (i + 1) ≤ G)
    (hread : ∀ p, p < l.length → ∃ z, l[p]? = some z)
    (hx : l[i]? = some x)
    (hmin : minIndexFwd l G (i + 1) i = .ok (m, j'))
    (hm' : m < l.length)
    (hy : l[m]? = some y) :
    ∃ ρ', evalProgStmt vecSelectionSortProg F selectionSortStep ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "v" =
        some (.stdVecVal ((l.set i y).set m x)) ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = i + 1) ∧
      envLookup ρ' "n" =
        some (.u64 (BitVec.ofNat 64 l.length)) := by
  have hargs : lookupArgs ρ ["v", "i"] =
      some [.stdVecVal l, .u64 iB] := by
    simp [lookupArgs, hv, hi]
  have hfind : findFunc vecSelectionSortProg minIndexName =
      some minIndexFunc := by
    exact findFunc_hit _ _
  have hcall := evalFuncFuel_minIndex_ok F G l i iB m j'
    hiN hl64 hlt hF hG hread hmin
  have hm64 : m < 2 ^ 64 := by omega
  have hmN : (BitVec.ofNat 64 m).toNat = m := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hm64
  have hstep_call := evalProgStmt_callRet_ok vecSelectionSortProg F
    "m" minIndexName ["v", "i"] ρ [.stdVecVal l, .u64 iB]
    minIndexFunc (.u64 (BitVec.ofNat 64 m)) hargs hfind hcall
  have hm₁ : envLookup (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
      "m" = some (.u64 (BitVec.ofNat 64 m)) :=
    envExtend_hit _ _ _
  have hi₁ : envLookup (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
      "i" = some (.u64 iB) := by
    rw [envExtend_miss _ _ _ _
      (show ("i" : String) ≠ "m" by decide)]
    exact hi
  have hv₁ : envLookup (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
      "v" = some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "m" by decide)]
    exact hv
  have hn₁ : envLookup (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
      "n" = some (.u64 (BitVec.ofNat 64 l.length)) := by
    rw [envExtend_miss _ _ _ _
      (show ("n" : String) ≠ "m" by decide)]
    exact hn
  have hiVar₁ : evalExpr (.var "i")
      (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m))) =
      .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi₁
  have hgetB : l[iB.toNat]? = some x := by rw [hiN]; exact hx
  have hsetB : l.set iB.toNat y = l.set i y := by rw [hiN]
  have hset : ((l.set iB.toNat y).set (BitVec.ofNat 64 m).toNat x) =
      ((l.set i y).set m x) := by
    rw [hiN, hmN]
  have hat : evalExpr (.stdVecAt "v" (.var "i"))
      (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m))) = .ok (.i32 x) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv₁ hiVar₁ hgetB
  have hlet := revLet vecSelectionSortProg F "t" (.i 32)
    (.stdVecAt "v" (.var "i"))
    (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m))) (.i32 x) hat
  have hm₂ : envLookup (envExtend (envExtend ρ "m"
      (.u64 (BitVec.ofNat 64 m))) "t" (.i32 x)) "m" =
      some (.u64 (BitVec.ofNat 64 m)) := by
    rw [envExtend_miss _ _ _ _
      (show ("m" : String) ≠ "t" by decide)]
    exact hm₁
  have hi₂ : envLookup (envExtend (envExtend ρ "m"
      (.u64 (BitVec.ofNat 64 m))) "t" (.i32 x)) "i" =
      some (.u64 iB) := by
    rw [envExtend_miss _ _ _ _
      (show ("i" : String) ≠ "t" by decide)]
    exact hi₁
  have hn₂ : envLookup (envExtend (envExtend ρ "m"
      (.u64 (BitVec.ofNat 64 m))) "t" (.i32 x)) "n" =
      some (.u64 (BitVec.ofNat 64 l.length)) := by
    rw [envExtend_miss _ _ _ _
      (show ("n" : String) ≠ "t" by decide)]
    exact hn₁
  have hiVar₂ : evalExpr (.var "i")
      (envExtend (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
        "t" (.i32 x)) = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi₂
  have hmVar₂ : evalExpr (.var "m")
      (envExtend (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
        "t" (.i32 x)) = .ok (.u64 (BitVec.ofNat 64 m)) :=
    evalExpr_var_hit _ _ _ hm₂
  have hgetM : l[(BitVec.ofNat 64 m).toNat]? = some y := by
    rw [hmN]; exact hy
  have hv₂ : envLookup (envExtend (envExtend ρ "m"
      (.u64 (BitVec.ofNat 64 m))) "t" (.i32 x)) "v" =
      some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "t" by decide)]
    exact hv₁
  have hatM : evalExpr (.stdVecAt "v" (.var "m"))
      (envExtend (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
        "t" (.i32 x)) = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv₂ hmVar₂ hgetM
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup
    (envExtend (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
      "t" (.i32 x)) "v"
    (.stdVecVal l) (.stdVecVal (l.set iB.toNat y)) hv₂
  have hstep_set1 := revVecSet vecSelectionSortProg F "v"
    (.var "i") (.stdVecAt "v" (.var "m"))
    (envExtend (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
      "t" (.i32 x)) iB y l x ρ₁
    hiVar₂ hatM hv₂ hgetB hu₁
  have hm₃ : envLookup ρ₁ "m" = some (.u64 (BitVec.ofNat 64 m)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("m" : String) ≠ "v" by decide) hu₁]
    exact hm₂
  have hi₃ : envLookup ρ₁ "i" = some (.u64 iB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "v" by decide) hu₁]
    exact hi₂
  have hn₃ : envLookup ρ₁ "n" =
      some (.u64 (BitVec.ofNat 64 l.length)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("n" : String) ≠ "v" by decide) hu₁]
    exact hn₂
  have ht₁ : envLookup ρ₁ "t" = some (.i32 x) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("t" : String) ≠ "v" by decide) hu₁]
    exact envExtend_hit _ _ _
  have hout₁ : envLookup ρ₁ "v" =
      some (.stdVecVal (l.set i y)) := by
    have h := envLookup_update_hit _ _ _ _ hu₁
    rwa [hsetB] at h
  have hmVar₃ : evalExpr (.var "m") ρ₁ =
      .ok (.u64 (BitVec.ofNat 64 m)) :=
    evalExpr_var_hit _ _ _ hm₃
  have htVar₃ : evalExpr (.var "t") ρ₁ = .ok (.i32 x) :=
    evalExpr_var_hit _ _ _ ht₁
  have hgetM₁ : (l.set i y)[m]? = some y := by
    by_cases hmi : m = i
    · rw [hmi]; exact List.getElem?_set_self hlt
    · rw [List.getElem?_set_ne (show i ≠ m by omega)]
      exact hy
  have hgetM₁' : (l.set i y)[(BitVec.ofNat 64 m).toNat]? =
      some y := by
    rw [hmN]; exact hgetM₁
  have hgetM₁B : (l.set iB.toNat y)[(BitVec.ofNat 64 m).toNat]? =
      some y := by
    rw [hsetB]; exact hgetM₁'
  have hout₁B : envLookup ρ₁ "v" =
      some (.stdVecVal (l.set iB.toNat y)) :=
    envLookup_update_hit _ _ _ _ hu₁
  obtain ⟨ρ₂, hu₂⟩ := envUpdate_some_of_lookup ρ₁ "v"
    (.stdVecVal (l.set iB.toNat y))
    (.stdVecVal ((l.set iB.toNat y).set (BitVec.ofNat 64 m).toNat x))
    hout₁B
  have hstep_set2 := revVecSet vecSelectionSortProg F "v"
    (.var "m") (.var "t") ρ₁ (BitVec.ofNat 64 m) x
    (l.set iB.toNat y) y ρ₂ hmVar₃ htVar₃ hout₁B hgetM₁B hu₂
  have hm₄ : envLookup ρ₂ "m" = some (.u64 (BitVec.ofNat 64 m)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("m" : String) ≠ "v" by decide) hu₂]
    exact hm₃
  have hi₄ : envLookup ρ₂ "i" = some (.u64 iB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "v" by decide) hu₂]
    exact hi₃
  have hn₄ : envLookup ρ₂ "n" =
      some (.u64 (BitVec.ofNat 64 l.length)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("n" : String) ≠ "v" by decide) hu₂]
    exact hn₃
  have hout₂ : envLookup ρ₂ "v" =
      some (.stdVecVal ((l.set i y).set m x)) := by
    have h := envLookup_update_hit _ _ _ _ hu₂
    rwa [hset] at h
  have hiVar₄ : evalExpr (.var "i") ρ₂ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi₄
  have hevI : evalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ₂ =
      .ok (.u64 (iB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      hiVar₄ (by simp [evalExpr, litVal])
  obtain ⟨ρ₃, hu₃⟩ := envUpdate_some_of_lookup ρ₂ "i"
    (.u64 iB) (.u64 (iB + 1)) hi₄
  have hstep_i := revAssign vecSelectionSortProg F "i"
    (.uadd (.var "i") (.lit (.u64 1))) ρ₂ (.u64 (iB + 1)) ρ₃
    hevI hu₃
  have hout₃ : envLookup ρ₃ "v" =
      some (.stdVecVal ((l.set i y).set m x)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("v" : String) ≠ "i" by decide) hu₃]
    exact hout₂
  have hn' : envLookup ρ₃ "n" =
      some (.u64 (BitVec.ofNat 64 l.length)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("n" : String) ≠ "i" by decide) hu₃]
    exact hn₄
  have hiN' : (iB + 1).toNat = i + 1 := by
    have h := revU64_succ_toNat iB l.length (by rw [hiN]; exact hlt) hl64
    omega
  have hi' : envLookup ρ₃ "i" = some (.u64 (iB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₃
  have hbody : selectionSortStep =
      (.seq (.callRet "m" minIndexName ["v", "i"])
        (.seq (.let_ "t" (.i 32) (.stdVecAt "v" (.var "i")))
          (.seq (.vecSet "v" (.var "i") (.stdVecAt "v" (.var "m")))
            (.seq (.vecSet "v" (.var "m") (.var "t"))
              (.assign "i"
                (.uadd (.var "i") (.lit (.u64 1)))))))) := rfl
  have heval : evalProgStmt vecSelectionSortProg F
      selectionSortStep ρ = .ok (ρ₃, .fellThrough) := by
    rw [hbody,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_call,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hlet,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_set1,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_set2,
      hstep_i]
  exact ⟨ρ₃, heval, hout₃, ⟨(iB + 1), hi', hiN'⟩, hn'⟩

/-- Outer loop, ok leg: the index scan runs to `l.length` and the
    words are the forward-model result (fuel induction threading
    the body hit; the forward equation unfolds one step per
    iteration). Two fuels: the program fuel threads the `callRet`
    steps while the inner budget stays fixed (leaf self-contained).
    The guard reads the `n` snapshot, never the live length. -/
theorem valSelectionSortLoop_ok (F G : Nat)
    (ρ : Env) (l : List (BitVec 32))
    (i : Nat) (iB : BitVec 64)
    (l' : List (BitVec 32)) (i' : Nat)
    (hiN : iB.toNat = i)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hn : envLookup ρ "n" = some (.u64 (BitVec.ofNat 64 l.length)))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hle : i ≤ l.length)
    (hF : l.length - i ≤ F)
    (hG : l.length - (i + 1) ≤ G)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (hfwd : selectionSortFwd l F G i = .ok (i', l')) :
    ∃ ρ', evalProgStmt vecSelectionSortProg F selectionSortLoop ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "v" = some (.stdVecVal l') ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = i') := by
  induction F generalizing G ρ l i iB with
  | zero =>
    have him : i = l.length := by omega
    have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
    have hguardF : evalExpr (.ult (.var "i") (.var "n")) ρ =
        .ok (.b false) := by
      have hult := evalExpr_ult_u64 (.var "i") (.var "n")
        ρ iB (BitVec.ofNat 64 l.length)
        (evalExpr_var_hit _ _ _ hi)
        (evalExpr_var_hit _ _ _ hn)
      have hfb : (iB.ult (BitVec.ofNat 64 l.length)) = false := by
        rw [BitVec.ult_eq_decide]
        exact decide_eq_false (by omega)
      rwa [hfb] at hult
    have hexit : evalProgStmt vecSelectionSortProg 0
        selectionSortLoop ρ = .ok (ρ, .fellThrough) :=
      evalProgStmt_while_false vecSelectionSortProg 0 _ _ _ hguardF
    have hpair : (i, l) = (i', l') := by
      simpa [selectionSortFwd] using hfwd
    obtain ⟨rfl, rfl⟩ := hpair
    exact ⟨ρ, hexit, hv, ⟨iB, hi, hiN⟩⟩
  | succ F ih =>
    by_cases hlt : i < l.length
    · have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
      have hguardT : evalExpr (.ult (.var "i") (.var "n")) ρ =
          .ok (.b true) := by
        have hult := evalExpr_ult_u64 (.var "i") (.var "n")
          ρ iB (BitVec.ofNat 64 l.length)
          (evalExpr_var_hit _ _ _ hi)
          (evalExpr_var_hit _ _ _ hn)
        have htb : (iB.ult (BitVec.ofNat 64 l.length)) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true (by omega)
        rwa [htb] at hult
      obtain ⟨x, hx⟩ := hread i hlt
      have hF' : l.length - (i + 1) ≤ F := by omega
      obtain ⟨m, j₀, hmin, hm'⟩ :=
        minIndexFwd_ok l G (i + 1) i hlt (by omega) hG hread
      obtain ⟨y, hy⟩ := hread m hm'
      obtain ⟨ρ₁, hbody, hout₁, ⟨iB₁, hiB₁, hiN₁⟩, hn₁⟩ :=
        valSelectionSortBody_ok F G ρ l i iB m j₀ x y
          hiN hl64 hv hn hi hlt hF' hG hread hx hmin hm' hy
      have hlen : ((l.set i y).set m x).length = l.length := by
        simp [List.length_set]
      have hle' : i + 1 ≤ ((l.set i y).set m x).length := by omega
      have hF'' : ((l.set i y).set m x).length - (i + 1) ≤ F := by omega
      have hG' : ((l.set i y).set m x).length - (i + 1 + 1) ≤ G := by
        omega
      have hread' : ∀ p, p < ((l.set i y).set m x).length →
          ∃ z, ((l.set i y).set m x)[p]? = some z := by
        intro p hp
        have hplen : p < l.length := by omega
        by_cases hpi : p = i
        · rw [hpi]
          by_cases hmi : m = i
          · rw [hmi]; exact ⟨x, List.getElem?_set_self (by
            rw [List.length_set]; exact hlt)⟩
          · exact ⟨y, by
              rw [List.getElem?_set_ne (show m ≠ i by omega)]
              exact List.getElem?_set_self hlt⟩
        · by_cases hpm : p = m
          · rw [hpm]
            exact ⟨x, List.getElem?_set_self (by
              rw [List.length_set]; exact hm')⟩
          · obtain ⟨z, hz⟩ := hread p hplen
            exact ⟨z, by
              rw [List.getElem?_set_ne (show m ≠ p by omega),
                List.getElem?_set_ne (show i ≠ p by omega)]
              exact hz⟩
      have hfwd' : selectionSortFwd ((l.set i y).set m x) F G
          (i + 1) = .ok (i', l') := by
        have h := hfwd
        simp only [selectionSortFwd, dite_eq_left hlt, hmin, hx, hy] at h
        exact h
      have hn₁' : envLookup ρ₁ "n" =
          some (.u64 (BitVec.ofNat 64 ((l.set i y).set m x).length)) := by
        rw [hlen]; exact hn₁
      have hl64' : ((l.set i y).set m x).length < 2 ^ 64 := by
        rw [hlen]; exact hl64
      obtain ⟨ρ', hloop, hout', ⟨iB', hiB', hiN'⟩⟩ :=
        ih (G := G) (ρ := ρ₁) (l := (l.set i y).set m x)
          (i := i + 1) (iB := iB₁)
          (hiN := hiN₁) (hl64 := hl64')
          (hv := hout₁) (hn := hn₁') (hi := hiB₁)
          (hle := hle') (hF := hF'') (hG := hG')
          (hread := hread') (hfwd := hfwd')
      refine ⟨ρ', ?_, hout', ⟨iB', hiB', hiN'⟩⟩
      have hwhile : evalProgStmt vecSelectionSortProg (F + 1)
          selectionSortLoop ρ =
          evalProgStmt vecSelectionSortProg F selectionSortLoop ρ₁ := by
        cir_unfold_prog (selectionSortLoop, vecSelectionSortProg, F, hguardT, hbody)
      rw [hwhile]
      exact hloop
    · have him : i = l.length := by omega
      subst him
      have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
      have hguardF : evalExpr (.ult (.var "i") (.var "n")) ρ =
          .ok (.b false) := by
        have hult := evalExpr_ult_u64 (.var "i") (.var "n")
          ρ iB (BitVec.ofNat 64 l.length)
          (evalExpr_var_hit _ _ _ hi)
          (evalExpr_var_hit _ _ _ hn)
        have hfb : (iB.ult (BitVec.ofNat 64 l.length)) = false := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_false (by omega)
        rwa [hfb] at hult
      have hexit : evalProgStmt vecSelectionSortProg (F + 1)
          selectionSortLoop ρ = .ok (ρ, .fellThrough) :=
        evalProgStmt_while_false vecSelectionSortProg (F + 1) _ _ _
          hguardF
      have hpair : (l.length, l) = (i', l') := by
        have hneg : ¬ l.length < l.length := by omega
        simpa [selectionSortFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl⟩ := hpair
      refine ⟨ρ, hexit, hv, ⟨iB, hi, ?_⟩⟩
      simpa using hiN

/-! ## Outer memory proofs (program level) -/

/-- One outer iteration on memory: the leaf call returns by value
    (caller memory threads through unchanged — the S1 discipline),
    the unconditional swap stores thread through `memStore` in
    lockstep on the single `v` block, `i` advances. -/
theorem memSelectionSortBody_ok (F G : Nat)
    (ρ : Env) (mm : Mem) (π : Layout)
    (l : List (BitVec 32))
    (i : Nat) (iB : BitVec 64)
    (m j' : Nat) (x y : BitVec 32)
    (a t : Nat) (n : BitVec 32)
    (hiN : iB.toNat = i)
    (hl64 : l.length < 2 ^ 64)
    (hlay : layoutLookup π "v" = some (a, t))
    (hmem : memFind mm a = some ⟨t, true, n :: l⟩)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hnw : envLookup ρ "n" = some (.u64 (BitVec.ofNat 64 l.length)))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hlt : i < l.length)
    (hF : l.length - (i + 1) ≤ F)
    (hG : l.length - (i + 1) ≤ G)
    (hread : ∀ p, p < l.length → ∃ z, l[p]? = some z)
    (hx : l[i]? = some x)
    (hmin : minIndexFwd l G (i + 1) i = .ok (m, j'))
    (hm' : m < l.length)
    (hy : l[m]? = some y) :
    ∃ ρ' mm', memEvalProgStmt vecSelectionSortProg F
        selectionSortStep ρ mm π =
        .ok ((ρ', mm', π), .fellThrough) ∧
      envLookup ρ' "v" =
        some (.stdVecVal ((l.set i y).set m x)) ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = i + 1) ∧
      envLookup ρ' "n" =
        some (.u64 (BitVec.ofNat 64 l.length)) ∧
      memFind mm' a = some ⟨t, true, n :: ((l.set i y).set m x)⟩ := by
  have hargs : lookupArgs ρ ["v", "i"] =
      some [.stdVecVal l, .u64 iB] := by
    simp [lookupArgs, hv, hi]
  have hfind : findFunc vecSelectionSortProg minIndexName =
      some minIndexFunc := by
    exact findFunc_hit _ _
  have hcall := memEvalFuncFuel_minIndex_ok F G l i iB m j'
    hiN hl64 hlt hF hG hread hmin
  have hm64 : m < 2 ^ 64 := by omega
  have hmN : (BitVec.ofNat 64 m).toNat = m := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hm64
  have hstep_call := memEvalProgStmt_callRet_ok vecSelectionSortProg F
    "m" minIndexName ["v", "i"] ρ mm π
    [.stdVecVal l, .u64 iB] minIndexFunc
    (.u64 (BitVec.ofNat 64 m)) hargs hfind hcall
  have hgetB : l[iB.toNat]? = some x := by rw [hiN]; exact hx
  have hsetB : l.set iB.toNat y = l.set i y := by rw [hiN]
  have hset : ((l.set iB.toNat y).set (BitVec.ofNat 64 m).toNat x) =
      ((l.set i y).set m x) := by
    rw [hiN, hmN]
  have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have hiVarA : memEvalExpr (.var "i") ρ mm π =
      evalExpr (.var "i") ρ :=
    memEvalExpr_var _ _ _ _
  have hmemA : memLoad mm a t (iB.toNat + 1) = .ok x :=
    memLoad_cellsAt mm a t (iB.toNat + 1) (n :: l) x
      hmem (by rw [List.getElem?_cons_succ]; exact hgetB)
  have hm₁ : envLookup (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
      "m" = some (.u64 (BitVec.ofNat 64 m)) :=
    envExtend_hit _ _ _
  have hi₁ : envLookup (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
      "i" = some (.u64 iB) := by
    rw [envExtend_miss _ _ _ _
      (show ("i" : String) ≠ "m" by decide)]
    exact hi
  have hv₁ : envLookup (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
      "v" = some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "m" by decide)]
    exact hv
  have hn₁ : envLookup (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
      "n" = some (.u64 (BitVec.ofNat 64 l.length)) := by
    rw [envExtend_miss _ _ _ _
      (show ("n" : String) ≠ "m" by decide)]
    exact hnw

  have hiVar₁ : evalExpr (.var "i")
      (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m))) =
      .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi₁
  have hiVarA₁ : memEvalExpr (.var "i")
      (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m))) mm π =
      evalExpr (.var "i")
        (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m))) :=
    memEvalExpr_var _ _ _ _

  have hatM_ag : memEvalExpr (.stdVecAt "v" (.var "i"))
      (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m))) mm π =
      evalExpr (.stdVecAt "v" (.var "i"))
        (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m))) := by
    exact memEvalExpr_stdVecAt_hit "v" (.var "i")
      (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m))) mm π l iB x a t
      hlay hv₁ hiVarA₁ hiVar₁ hmemA hgetB
  have hat : evalExpr (.stdVecAt "v" (.var "i"))
      (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m))) =
      .ok (.i32 x) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv₁ hiVar₁ hgetB
  have hatM : memEvalExpr (.stdVecAt "v" (.var "i"))
      (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m))) mm π =
      .ok (.i32 x) := by rw [hatM_ag]; exact hat
  have hiVarM₁ : memEvalExpr (.var "i")
      (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m))) mm π =
      .ok (.u64 iB) :=
    hiVarA₁.trans hiVar₁
  have hmVarA₁ : memEvalExpr (.var "m")
      (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m))) mm π =
      evalExpr (.var "m")
        (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m))) :=
    memEvalExpr_var _ _ _ _
  have hmVar₁ : evalExpr (.var "m")
      (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m))) =
      .ok (.u64 (BitVec.ofNat 64 m)) :=
    evalExpr_var_hit _ _ _ hm₁
  have hmVarM₁ : memEvalExpr (.var "m")
      (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m))) mm π =
      .ok (.u64 (BitVec.ofNat 64 m)) :=
    hmVarA₁.trans hmVar₁
  have hgetM : l[(BitVec.ofNat 64 m).toNat]? = some y := by
    rw [hmN]; exact hy
  have hmemM : memLoad mm a t ((BitVec.ofNat 64 m).toNat + 1) =
      .ok y :=
    memLoad_cellsAt mm a t ((BitVec.ofNat 64 m).toNat + 1)
      (n :: l) y hmem
      (by rw [List.getElem?_cons_succ]; exact hgetM)
  -- NOTE: the at-reads happen before the `t` let binds, so threading
  -- here goes through the post-call env (no `t` yet); the let then
  -- extends with `t` exactly as on the value side.
  have hletT := memRevLet vecSelectionSortProg F "t" (.i 32)
    (.stdVecAt "v" (.var "i"))
    (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m))) mm π (.i32 x)
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) hatM_ag hat
  have ht₁ : envLookup (envExtend (envExtend ρ "m"
      (.u64 (BitVec.ofNat 64 m))) "t" (.i32 x)) "t" =
      some (.i32 x) :=
    envExtend_hit _ _ _
  have hm₂ : envLookup (envExtend (envExtend ρ "m"
      (.u64 (BitVec.ofNat 64 m))) "t" (.i32 x)) "m" =
      some (.u64 (BitVec.ofNat 64 m)) := by
    rw [envExtend_miss _ _ _ _
      (show ("m" : String) ≠ "t" by decide)]
    exact hm₁
  have hi₂ : envLookup (envExtend (envExtend ρ "m"
      (.u64 (BitVec.ofNat 64 m))) "t" (.i32 x)) "i" =
      some (.u64 iB) := by
    rw [envExtend_miss _ _ _ _
      (show ("i" : String) ≠ "t" by decide)]
    exact hi₁
  have hv₂ : envLookup (envExtend (envExtend ρ "m"
      (.u64 (BitVec.ofNat 64 m))) "t" (.i32 x)) "v" =
      some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "t" by decide)]
    exact hv₁
  have hn₂ : envLookup (envExtend (envExtend ρ "m"
      (.u64 (BitVec.ofNat 64 m))) "t" (.i32 x)) "n" =
      some (.u64 (BitVec.ofNat 64 l.length)) := by
    rw [envExtend_miss _ _ _ _
      (show ("n" : String) ≠ "t" by decide)]
    exact hn₁
  have hiVar₂T : evalExpr (.var "i")
      (envExtend (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
        "t" (.i32 x)) = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi₂
  have hiVarA₂T : memEvalExpr (.var "i")
      (envExtend (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
        "t" (.i32 x)) mm π =
      evalExpr (.var "i")
        (envExtend (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
          "t" (.i32 x)) :=
    memEvalExpr_var _ _ _ _
  have hiVarM₂T : memEvalExpr (.var "i")
      (envExtend (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
        "t" (.i32 x)) mm π = .ok (.u64 iB) :=
    hiVarA₂T.trans hiVar₂T
  have hmVar₂T : evalExpr (.var "m")
      (envExtend (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
        "t" (.i32 x)) = .ok (.u64 (BitVec.ofNat 64 m)) :=
    evalExpr_var_hit _ _ _ hm₂
  have hmVarA₂T : memEvalExpr (.var "m")
      (envExtend (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
        "t" (.i32 x)) mm π =
      evalExpr (.var "m")
        (envExtend (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
          "t" (.i32 x)) :=
    memEvalExpr_var _ _ _ _
  have hatS₂T : evalExpr (.stdVecAt "v" (.var "m"))
      (envExtend (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
        "t" (.i32 x)) = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv₂ hmVar₂T hgetM
  have hatSM₂T_ag : memEvalExpr (.stdVecAt "v" (.var "m"))
      (envExtend (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
        "t" (.i32 x)) mm π =
      evalExpr (.stdVecAt "v" (.var "m"))
        (envExtend (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
          "t" (.i32 x)) :=
    memEvalExpr_stdVecAt_hit "v" (.var "m")
      (envExtend (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
        "t" (.i32 x)) mm π l (BitVec.ofNat 64 m) y a t
      hlay hv₂ hmVarA₂T hmVar₂T hmemM hgetM
  have hatSM₂T : memEvalExpr (.stdVecAt "v" (.var "m"))
      (envExtend (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
        "t" (.i32 x)) mm π = .ok (.i32 y) := by
    rw [hatSM₂T_ag]; exact hatS₂T
  have hlt₁ : iB.toNat + 1 < (n :: l).length := by
    simp only [List.length_cons]
    omega
  obtain ⟨mm₁, hmstore⟩ : ∃ mm', memStore mm a t (iB.toNat + 1) y =
      .ok mm' :=
    ⟨_, memStore_cellsAt mm a t (iB.toNat + 1) (n :: l) y
      hmem hlt₁⟩
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup
    (envExtend (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
      "t" (.i32 x)) "v"
    (.stdVecVal l) (.stdVecVal (l.set iB.toNat y)) hv₂
  have hstep_set1 := memRevVecSet vecSelectionSortProg F "v"
    (.var "i") (.stdVecAt "v" (.var "m"))
    (envExtend (envExtend ρ "m" (.u64 (BitVec.ofNat 64 m)))
      "t" (.i32 x)) mm π
    iB y a t l x mm₁ ρ₁ hiVarM₂T hatSM₂T hv₂ hlay hgetB hmstore hu₁
  have hcells₁ : cellsAt mm₁ a t ((n :: l).set (iB.toNat + 1) y) :=
    memFind_cellsAt_store mm a t (iB.toNat + 1) (n :: l) y mm₁
      hmem hlt₁ hmstore
  have hmem₁ : memFind mm₁ a =
      some ⟨t, true, n :: (l.set iB.toNat y)⟩ := by
    have e : (n :: l).set (iB.toNat + 1) y =
        n :: (l.set iB.toNat y) :=
      List.set_cons_succ
    rw [e] at hcells₁
    exact hcells₁
  have hm₃ : envLookup ρ₁ "m" = some (.u64 (BitVec.ofNat 64 m)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("m" : String) ≠ "v" by decide) hu₁]
    exact hm₂
  have hi₃ : envLookup ρ₁ "i" = some (.u64 iB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "v" by decide) hu₁]
    exact hi₂
  have hn₃ : envLookup ρ₁ "n" =
      some (.u64 (BitVec.ofNat 64 l.length)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("n" : String) ≠ "v" by decide) hu₁]
    exact hn₂
  have ht₃ : envLookup ρ₁ "t" = some (.i32 x) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("t" : String) ≠ "v" by decide) hu₁]
    exact ht₁
  have hout₁ : envLookup ρ₁ "v" =
      some (.stdVecVal (l.set iB.toNat y)) :=
    envLookup_update_hit _ _ _ _ hu₁
  have hmVarA₃ : memEvalExpr (.var "m") ρ₁ mm₁ π =
      evalExpr (.var "m") ρ₁ :=
    memEvalExpr_var _ _ _ _
  have hmVar₃ : evalExpr (.var "m") ρ₁ =
      .ok (.u64 (BitVec.ofNat 64 m)) :=
    evalExpr_var_hit _ _ _ hm₃
  have hmVarM₃ : memEvalExpr (.var "m") ρ₁ mm₁ π =
      .ok (.u64 (BitVec.ofNat 64 m)) :=
    hmVarA₃.trans hmVar₃
  have htVarA₃ : memEvalExpr (.var "t") ρ₁ mm₁ π =
      evalExpr (.var "t") ρ₁ :=
    memEvalExpr_var _ _ _ _
  have htVar₃ : evalExpr (.var "t") ρ₁ = .ok (.i32 x) :=
    evalExpr_var_hit _ _ _ ht₃
  have htVarM₃ : memEvalExpr (.var "t") ρ₁ mm₁ π =
      .ok (.i32 x) :=
    htVarA₃.trans htVar₃
  have hgetM₁ : (l.set iB.toNat y)[(BitVec.ofNat 64 m).toNat]? =
      some y := by
    rw [hsetB, hmN]
    by_cases hmi : m = i
    · rw [hmi]; exact List.getElem?_set_self hlt
    · rw [List.getElem?_set_ne (show i ≠ m by omega)]
      exact hy
  obtain ⟨ρ₂, hu₂⟩ := envUpdate_some_of_lookup ρ₁ "v"
    (.stdVecVal (l.set iB.toNat y))
    (.stdVecVal ((l.set iB.toNat y).set (BitVec.ofNat 64 m).toNat x))
    hout₁
  have hlt₂ : (BitVec.ofNat 64 m).toNat + 1 <
      (n :: (l.set iB.toNat y)).length := by
    simp only [List.length_cons, List.length_set]
    omega
  obtain ⟨mm₂, hmstore₂⟩ : ∃ mm', memStore mm₁ a t
      ((BitVec.ofNat 64 m).toNat + 1) x = .ok mm' :=
    ⟨_, memStore_cellsAt mm₁ a t ((BitVec.ofNat 64 m).toNat + 1)
      (n :: (l.set iB.toNat y)) x hmem₁ hlt₂⟩
  have hstep_set2 := memRevVecSet vecSelectionSortProg F "v"
    (.var "m") (.var "t") ρ₁ mm₁ π (BitVec.ofNat 64 m) x
    a t (l.set iB.toNat y) y mm₂ ρ₂
    hmVarM₃ htVarM₃ hout₁ hlay hgetM₁ hmstore₂ hu₂
  have hcells₂ : cellsAt mm₂ a t
      ((n :: (l.set iB.toNat y)).set
        ((BitVec.ofNat 64 m).toNat + 1) x) :=
    memFind_cellsAt_store mm₁ a t ((BitVec.ofNat 64 m).toNat + 1)
      (n :: (l.set iB.toNat y)) x mm₂ hmem₁ hlt₂ hmstore₂
  have hmem₂ : memFind mm₂ a =
      some ⟨t, true, n :: ((l.set i y).set m x)⟩ := by
    have e : (n :: (l.set iB.toNat y)).set
        ((BitVec.ofNat 64 m).toNat + 1) x =
        n :: ((l.set iB.toNat y).set (BitVec.ofNat 64 m).toNat x) :=
      List.set_cons_succ
    rw [e, hset] at hcells₂
    exact hcells₂
  have hm₄ : envLookup ρ₂ "m" = some (.u64 (BitVec.ofNat 64 m)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("m" : String) ≠ "v" by decide) hu₂]
    exact hm₃
  have hi₄ : envLookup ρ₂ "i" = some (.u64 iB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "v" by decide) hu₂]
    exact hi₃
  have hn₄ : envLookup ρ₂ "n" =
      some (.u64 (BitVec.ofNat 64 l.length)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("n" : String) ≠ "v" by decide) hu₂]
    exact hn₃
  have hout₂ : envLookup ρ₂ "v" =
      some (.stdVecVal ((l.set i y).set m x)) := by
    have h := envLookup_update_hit _ _ _ _ hu₂
    rwa [hset] at h
  have hiVarA₄ : memEvalExpr (.var "i") ρ₂ mm₂ π =
      evalExpr (.var "i") ρ₂ :=
    memEvalExpr_var _ _ _ _
  have hiVar₄ : evalExpr (.var "i") ρ₂ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi₄
  have hevI : evalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ₂ =
      .ok (.u64 (iB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      hiVar₄ (by simp [evalExpr, litVal])
  have hevIM : memEvalExpr
      (.uadd (.var "i") (.lit (.u64 1))) ρ₂ mm₂ π =
      .ok (.u64 (iB + 1)) :=
    (memEvalExpr_uadd_agree (.var "i") (.lit (.u64 1))
      ρ₂ mm₂ π hiVarA₄ (memEvalExpr_lit _ _ _ _)).trans hevI
  obtain ⟨ρ₃, hu₃⟩ := envUpdate_some_of_lookup ρ₂ "i"
    (.u64 iB) (.u64 (iB + 1)) hi₄
  have hstep_i := memRevAssign vecSelectionSortProg F "i"
    (.uadd (.var "i") (.lit (.u64 1))) ρ₂ mm₂ π (.u64 (iB + 1)) ρ₃
    hevIM hevI hu₃
  have hout₃ : envLookup ρ₃ "v" =
      some (.stdVecVal ((l.set i y).set m x)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("v" : String) ≠ "i" by decide) hu₃]
    exact hout₂
  have hn' : envLookup ρ₃ "n" =
      some (.u64 (BitVec.ofNat 64 l.length)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("n" : String) ≠ "i" by decide) hu₃]
    exact hn₄
  have hiN' : (iB + 1).toNat = i + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hiN]
    exact Nat.mod_eq_of_lt (by omega)
  have hi' : envLookup ρ₃ "i" = some (.u64 (iB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₃
  have hthen : memEvalProgStmt vecSelectionSortProg F
      (.seq (.callRet "m" minIndexName ["v", "i"])
        (.seq (.let_ "t" (.i 32) (.stdVecAt "v" (.var "i")))
          (.seq (.vecSet "v" (.var "i") (.stdVecAt "v" (.var "m")))
            (.seq (.vecSet "v" (.var "m") (.var "t"))
              (.assign "i"
                (.uadd (.var "i") (.lit (.u64 1))))))))
      ρ mm π = .ok ((ρ₃, mm₂, π), .fellThrough) := by
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
      hstep_call,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletT,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
        hstep_set1,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
        hstep_set2,
      hstep_i]
  have hbody : selectionSortStep =
      (.seq (.callRet "m" minIndexName ["v", "i"])
        (.seq (.let_ "t" (.i 32) (.stdVecAt "v" (.var "i")))
          (.seq (.vecSet "v" (.var "i") (.stdVecAt "v" (.var "m")))
            (.seq (.vecSet "v" (.var "m") (.var "t"))
              (.assign "i"
                (.uadd (.var "i") (.lit (.u64 1)))))))) := rfl
  have heval : memEvalProgStmt vecSelectionSortProg F
      selectionSortStep ρ mm π =
      .ok ((ρ₃, mm₂, π), .fellThrough) := by
    rw [hbody, hthen]
  exact ⟨ρ₃, mm₂, heval, hout₃, ⟨(iB + 1), hi', hiN'⟩, hn', hmem₂⟩

/-- Outer memory loop, ok leg: the scan runs to `l.length`, the
    block holds the forward-model words (fuel induction threading
    the memory body hit; the forward equation unfolds one step per
    iteration). -/
theorem memSelectionSortLoop_ok (F G : Nat)
    (ρ : Env) (mm : Mem) (π : Layout)
    (l : List (BitVec 32))
    (i : Nat) (iB : BitVec 64)
    (l' : List (BitVec 32)) (i' : Nat)
    (a t : Nat) (n : BitVec 32)
    (hiN : iB.toNat = i)
    (hl64 : l.length < 2 ^ 64)
    (hlay : layoutLookup π "v" = some (a, t))
    (hmem : memFind mm a = some ⟨t, true, n :: l⟩)
    (hn : n = BitVec.ofNat 32 l.length)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hnw : envLookup ρ "n" = some (.u64 (BitVec.ofNat 64 l.length)))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hle : i ≤ l.length)
    (hF : l.length - i ≤ F)
    (hG : l.length - (i + 1) ≤ G)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (hfwd : selectionSortFwd l F G i = .ok (i', l')) :
    ∃ ρ' mm', memEvalProgStmt vecSelectionSortProg F
        selectionSortLoop ρ mm π =
        .ok ((ρ', mm', π), .fellThrough) ∧
      envLookup ρ' "v" = some (.stdVecVal l') ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = i') ∧
      memFind mm' a = some ⟨t, true, n :: l'⟩ := by
  induction F generalizing G ρ mm l i iB with
  | zero =>
    have him : i = l.length := by omega
    have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
    have hguardF : memEvalExpr
        (.ult (.var "i") (.var "n")) ρ mm π =
        .ok (.b false) := by
      have hag : memEvalExpr
          (.ult (.var "i") (.var "n")) ρ mm π =
          evalExpr (.ult (.var "i") (.var "n")) ρ :=
        memEvalExpr_ult_agree (.var "i") (.var "n") ρ mm π
          (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _)
      have hval : evalExpr (.ult (.var "i") (.var "n")) ρ =
          .ok (.b false) := by
        have hult := evalExpr_ult_u64 (.var "i") (.var "n")
          ρ iB (BitVec.ofNat 64 l.length)
          (evalExpr_var_hit _ _ _ hi)
          (evalExpr_var_hit _ _ _ hnw)
        have hfb : (iB.ult (BitVec.ofNat 64 l.length)) = false := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_false (by omega)
        rwa [hfb] at hult
      rw [hag]; exact hval
    have hexit : memEvalProgStmt vecSelectionSortProg 0
        selectionSortLoop ρ mm π =
        .ok ((ρ, mm, π), .fellThrough) :=
      memEvalProgStmt_while_false vecSelectionSortProg 0 _ _ _
        _ _ hguardF
    have hpair : (i, l) = (i', l') := by
      simpa [selectionSortFwd] using hfwd
    obtain ⟨rfl, rfl⟩ := hpair
    exact ⟨ρ, mm, hexit, hv, ⟨iB, hi, hiN⟩, hmem⟩
  | succ F ih =>
    by_cases hlt : i < l.length
    · have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
      have hguardT : memEvalExpr
          (.ult (.var "i") (.var "n")) ρ mm π =
          .ok (.b true) := by
        have hag : memEvalExpr
            (.ult (.var "i") (.var "n")) ρ mm π =
            evalExpr (.ult (.var "i") (.var "n")) ρ :=
          memEvalExpr_ult_agree (.var "i") (.var "n") ρ mm π
            (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _)
        have hval : evalExpr (.ult (.var "i") (.var "n")) ρ =
            .ok (.b true) := by
          have hult := evalExpr_ult_u64 (.var "i") (.var "n")
            ρ iB (BitVec.ofNat 64 l.length)
            (evalExpr_var_hit _ _ _ hi)
            (evalExpr_var_hit _ _ _ hnw)
          have htb : (iB.ult (BitVec.ofNat 64 l.length)) = true := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_true (by omega)
          rwa [htb] at hult
        rw [hag]; exact hval
      obtain ⟨x, hx⟩ := hread i hlt
      have hF' : l.length - (i + 1) ≤ F := by omega
      obtain ⟨m, j₀, hmin, hm'⟩ :=
        minIndexFwd_ok l G (i + 1) i hlt (by omega) hG hread
      obtain ⟨y, hy⟩ := hread m hm'
      obtain ⟨ρ₁, mm₁, hbody, hout₁, ⟨iB₁, hiB₁, hiN₁⟩, hn₁,
          hmem₁⟩ :=
        memSelectionSortBody_ok F G ρ mm π l i iB m j₀ x y
          a t n hiN hl64 hlay hmem hv hnw hi hlt hF' hG
          hread hx hmin hm' hy
      have hlen : ((l.set i y).set m x).length = l.length := by
        simp [List.length_set]
      have hle' : i + 1 ≤ ((l.set i y).set m x).length := by omega
      have hF'' : ((l.set i y).set m x).length - (i + 1) ≤ F := by omega
      have hG' : ((l.set i y).set m x).length - (i + 1 + 1) ≤ G := by
        omega
      have hread' : ∀ p, p < ((l.set i y).set m x).length →
          ∃ z, ((l.set i y).set m x)[p]? = some z := by
        intro p hp
        have hplen : p < l.length := by omega
        by_cases hpi : p = i
        · rw [hpi]
          by_cases hmi : m = i
          · rw [hmi]; exact ⟨x, List.getElem?_set_self (by
            rw [List.length_set]; exact hlt)⟩
          · exact ⟨y, by
              rw [List.getElem?_set_ne (show m ≠ i by omega)]
              exact List.getElem?_set_self hlt⟩
        · by_cases hpm : p = m
          · rw [hpm]
            exact ⟨x, List.getElem?_set_self (by
              rw [List.length_set]; exact hm')⟩
          · obtain ⟨z, hz⟩ := hread p hplen
            exact ⟨z, by
              rw [List.getElem?_set_ne (show m ≠ p by omega),
                List.getElem?_set_ne (show i ≠ p by omega)]
              exact hz⟩
      have hfwd' : selectionSortFwd ((l.set i y).set m x) F G
          (i + 1) = .ok (i', l') := by
        have h := hfwd
        simp only [selectionSortFwd, dite_eq_left hlt, hmin, hx, hy] at h
        exact h
      have hn₁' : envLookup ρ₁ "n" =
          some (.u64 (BitVec.ofNat 64 ((l.set i y).set m x).length)) := by
        rw [hlen]; exact hn₁
      have hn' : n = BitVec.ofNat 32 ((l.set i y).set m x).length := by
        rw [hlen]; exact hn
      obtain ⟨ρ', mm', hloop, hout', ⟨iB', hiB', hiN'⟩, hmem'⟩ :=
        ih (G := G) (ρ := ρ₁) (mm := mm₁)
          (l := (l.set i y).set m x)
          (i := i + 1) (iB := iB₁)
          (hiN := hiN₁) (hl64 := by rw [hlen]; exact hl64)
          (hmem := hmem₁) (hn := hn')
          (hv := hout₁) (hnw := hn₁') (hi := hiB₁)
          (hle := hle') (hF := hF'') (hG := hG')
          (hread := hread') (hfwd := hfwd')
      refine ⟨ρ', mm', ?_, hout', ⟨iB', hiB', hiN'⟩, hmem'⟩
      have hwhile : memEvalProgStmt vecSelectionSortProg (F + 1)
          selectionSortLoop ρ mm π =
          memEvalProgStmt vecSelectionSortProg F selectionSortLoop
            ρ₁ mm₁ π := by
        cir_unfold_prog (selectionSortLoop, vecSelectionSortProg, F, hguardT, hbody)
      rw [hwhile]
      exact hloop
    · have him : i = l.length := by omega
      subst him
      have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
      have hguardF : memEvalExpr
          (.ult (.var "i") (.var "n")) ρ mm π =
          .ok (.b false) := by
        have hag : memEvalExpr
            (.ult (.var "i") (.var "n")) ρ mm π =
            evalExpr (.ult (.var "i") (.var "n")) ρ :=
          memEvalExpr_ult_agree (.var "i") (.var "n") ρ mm π
            (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _)
        have hval : evalExpr (.ult (.var "i") (.var "n")) ρ =
            .ok (.b false) := by
          have hult := evalExpr_ult_u64 (.var "i") (.var "n")
            ρ iB (BitVec.ofNat 64 l.length)
            (evalExpr_var_hit _ _ _ hi)
            (evalExpr_var_hit _ _ _ hnw)
          have hfb : (iB.ult (BitVec.ofNat 64 l.length)) = false := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_false (by omega)
          rwa [hfb] at hult
        rw [hag]; exact hval
      have hexit : memEvalProgStmt vecSelectionSortProg (F + 1)
          selectionSortLoop ρ mm π =
          .ok ((ρ, mm, π), .fellThrough) :=
        memEvalProgStmt_while_false vecSelectionSortProg (F + 1) _ _ _ _ _
          hguardF
      have hpair : (l.length, l) = (i', l') := by
        have hneg : ¬ l.length < l.length := by omega
        simpa [selectionSortFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl⟩ := hpair
      refine ⟨ρ, mm, hexit, hv, ⟨iB, hi, ?_⟩, hmem⟩
      simpa using hiN

/-! ## Entries and transfer -/

/-- Value entry: the `n`/`i` prelude runs, the loop closes against
    the forward model, the updated words return. -/
theorem evalProgFunc_vecSelectionSort_ok (F G : Nat)
    (l l' : List (BitVec 32)) (i' : Nat)
    (hl64 : l.length < 2 ^ 64)
    (hF : l.length ≤ F)
    (hG : l.length - 1 ≤ G)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (hfwd : selectionSortFwd l F G 0 = .ok (i', l')) :
    evalProgFunc vecSelectionSortProg F vecSelectionSortFunc
      [.stdVecVal l] =
      .ok (.stdVecVal l') := by
  have hbind : bindArgs vecSelectionSortFunc.args
      [.stdVecVal l] =
      some [("v", .stdVecVal l)] := rfl
  have hbody : vecSelectionSortFunc.body =
      (.seq (.let_ "n" (.u 64) (.stdVecLen "v"))
        (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq selectionSortLoop
            (.return_ (.var "v"))))) := rfl
  have hlen : evalExpr (.stdVecLen "v") [("v", .stdVecVal l)] =
      .ok (.u64 (BitVec.ofNat 64 l.length)) :=
    evalExpr_stdVecLen_some _ _ _ (by simp [envLookup])
  have hletN := revLet vecSelectionSortProg F "n" (.u 64)
    (.stdVecLen "v") [("v", .stdVecVal l)]
    (.u64 (BitVec.ofNat 64 l.length)) hlen
  have hlit : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("v", .stdVecVal l)]
        "n" (.u64 (BitVec.ofNat 64 l.length))) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletI := revLet vecSelectionSortProg F "i" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (envExtend [("v", .stdVecVal l)]
      "n" (.u64 (BitVec.ofNat 64 l.length)))
    (.u64 (BitVec.ofNat 64 0)) hlit
  have hiN : (BitVec.ofNat 64 0).toNat = 0 := by
    simp [BitVec.toNat_ofNat]
  have hv₁ : envLookup (envExtend (envExtend
      [("v", .stdVecVal l)]
      "n" (.u64 (BitVec.ofNat 64 l.length)))
      "i" (.u64 (BitVec.ofNat 64 0))) "v" =
      some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "i" by decide),
      envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "n" by decide)]
    simp [envLookup]
  have hn₁ : envLookup (envExtend (envExtend
      [("v", .stdVecVal l)]
      "n" (.u64 (BitVec.ofNat 64 l.length)))
      "i" (.u64 (BitVec.ofNat 64 0))) "n" =
      some (.u64 (BitVec.ofNat 64 l.length)) := by
    rw [envExtend_miss _ _ _ _
      (show ("n" : String) ≠ "i" by decide)]
    exact envExtend_hit _ _ _
  have hi₁ : envLookup (envExtend (envExtend
      [("v", .stdVecVal l)]
      "n" (.u64 (BitVec.ofNat 64 l.length)))
      "i" (.u64 (BitVec.ofNat 64 0))) "i" =
      some (.u64 (BitVec.ofNat 64 0)) :=
    envExtend_hit _ _ _
  obtain ⟨ρ', hloop, hout', ⟨iB', hiB', hiN'⟩⟩ :=
    valSelectionSortLoop_ok F G
      (envExtend (envExtend [("v", .stdVecVal l)]
        "n" (.u64 (BitVec.ofNat 64 l.length)))
        "i" (.u64 (BitVec.ofNat 64 0)))
      l 0 (BitVec.ofNat 64 0) l' i'
      hiN hl64 hv₁ hn₁ hi₁ (Nat.zero_le _)
      (by omega) (by omega) hread hfwd
  have hret := evalProgStmt_return vecSelectionSortProg F
    (.var "v") ρ' (.stdVecVal l')
    (evalExpr_var_hit _ _ _ hout')
  simp only [evalProgFunc, hbind, hbody]
  rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletN,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hletI,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hloop,
    hret]

/-- Memory entry: the `n`/`i` prelude runs on memory, the loop
    closes against the forward model, the updated words return. -/
theorem memEvalProgFunc_vecSelectionSort_ok (F G : Nat)
    (l l' : List (BitVec 32)) (i' : Nat)
    (hl64 : l.length < 2 ^ 64)
    (hF : l.length ≤ F)
    (hG : l.length - 1 ≤ G)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (hfwd : selectionSortFwd l F G 0 = .ok (i', l')) :
    memEvalProgFunc vecSelectionSortProg F vecSelectionSortFunc
      [.stdVecVal l] =
      .ok (.stdVecVal l') := by
  have hbind := bindMemArgs_vecSelectionSort l
  have hbody : vecSelectionSortFunc.body =
      (.seq (.let_ "n" (.u 64) (.stdVecLen "v"))
        (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq selectionSortLoop
            (.return_ (.var "v"))))) := rfl
  have hmem : memFind
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ 0 =
      some ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩ :=
    memFind_cons_hit _ _ _ _ _
  have hlay : layoutLookup [("v", 0, 0)] "v" =
      some (0, 0) := by simp [layoutLookup]
  have hmemLen : memLoad
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ 0 0 0 =
      .ok (BitVec.ofNat 32 l.length) :=
    memLoad_cellsAt _ _ _ _ _ _ hmem (by simp)
  have hlenM : memEvalExpr (.stdVecLen "v")
      [("v", .stdVecVal l)]
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("v", 0, 0)] =
      evalExpr (.stdVecLen "v") [("v", .stdVecVal l)] :=
    memEvalExpr_stdVecLen_hit "v" _ _ _ _ _ _
      hlay (by simp [envLookup]) hmemLen
  have hlenV : evalExpr (.stdVecLen "v") [("v", .stdVecVal l)] =
      .ok (.u64 (BitVec.ofNat 64 l.length)) :=
    evalExpr_stdVecLen_some _ _ _ (by simp [envLookup])
  have hletN := memRevLet vecSelectionSortProg F "n" (.u 64)
    (.stdVecLen "v")
    [("v", .stdVecVal l)]
    ⟨1, [(0, ⟨0, true,
      (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
    [("v", 0, 0)] (.u64 (BitVec.ofNat 64 l.length))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) hlenM hlenV
  have hlitM : memEvalExpr
      (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("v", .stdVecVal l)]
        "n" (.u64 (BitVec.ofNat 64 l.length)))
      ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("v", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend [("v", .stdVecVal l)]
          "n" (.u64 (BitVec.ofNat 64 l.length))) :=
    memEvalExpr_lit _ _ _ _
  have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("v", .stdVecVal l)]
        "n" (.u64 (BitVec.ofNat 64 l.length))) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hletI := memRevLet vecSelectionSortProg F "i" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (envExtend [("v", .stdVecVal l)]
      "n" (.u64 (BitVec.ofNat 64 l.length)))
    ⟨1, [(0, ⟨0, true,
      (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
    [("v", 0, 0)] (.u64 (BitVec.ofNat 64 0))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) hlitM hlitV
  have hiN : (BitVec.ofNat 64 0).toNat = 0 := by
    simp [BitVec.toNat_ofNat]
  have hv₁ : envLookup (envExtend (envExtend
      [("v", .stdVecVal l)]
      "n" (.u64 (BitVec.ofNat 64 l.length)))
      "i" (.u64 (BitVec.ofNat 64 0))) "v" =
      some (.stdVecVal l) := by
    rw [envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "i" by decide),
      envExtend_miss _ _ _ _
      (show ("v" : String) ≠ "n" by decide)]
    simp [envLookup]
  have hn₁ : envLookup (envExtend (envExtend
      [("v", .stdVecVal l)]
      "n" (.u64 (BitVec.ofNat 64 l.length)))
      "i" (.u64 (BitVec.ofNat 64 0))) "n" =
      some (.u64 (BitVec.ofNat 64 l.length)) := by
    rw [envExtend_miss _ _ _ _
      (show ("n" : String) ≠ "i" by decide)]
    exact envExtend_hit _ _ _
  have hi₁ : envLookup (envExtend (envExtend
      [("v", .stdVecVal l)]
      "n" (.u64 (BitVec.ofNat 64 l.length)))
      "i" (.u64 (BitVec.ofNat 64 0))) "i" =
      some (.u64 (BitVec.ofNat 64 0)) :=
    envExtend_hit _ _ _
  obtain ⟨ρ', mm', hloop, hout', ⟨iB', hiB', hiN'⟩, hmem'⟩ :=
    memSelectionSortLoop_ok F G
      (ρ := envExtend (envExtend [("v", .stdVecVal l)]
        "n" (.u64 (BitVec.ofNat 64 l.length)))
        "i" (.u64 (BitVec.ofNat 64 0)))
      (mm := ⟨1, [(0, ⟨0, true,
        (BitVec.ofNat 32 l.length) :: l⟩)], []⟩)
      (π := [("v", 0, 0)])
      (l := l) (i := 0) (iB := BitVec.ofNat 64 0)
      (l' := l') (i' := i')
      (a := 0) (t := 0) (n := BitVec.ofNat 32 l.length)
      (hiN := hiN) (hl64 := hl64)
      (hlay := hlay) (hmem := hmem) (hn := rfl)
      (hv := hv₁) (hnw := hn₁) (hi := hi₁)
      (hle := Nat.zero_le _)
      (hF := by omega) (hG := by omega)
      (hread := hread) (hfwd := hfwd)
  have hret := memEvalProgStmt_return vecSelectionSortProg F
    (.var "v") ρ' mm' [("v", 0, 0)]
    (.stdVecVal l')
    ((memEvalExpr_var _ _ _ _).trans
      (evalExpr_var_hit _ _ _ hout'))
  simp only [memEvalProgFunc, hbind, hbody]
  rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletN,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hletI,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hloop,
    hret]

/-- Transfer for `vec_selection_sort`: memory evaluation agrees
    with value evaluation (single ok leg per function — both
    kernels are total). -/
theorem memTransferProg_vecSelectionSort_ok (F G : Nat)
    (l : List (BitVec 32))
    (hl64 : l.length < 2 ^ 64)
    (hF : l.length ≤ F)
    (hG : l.length - 1 ≤ G)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (_h : oracleNoalias vecSelectionSortFunc
      [.stdVecVal l]) :
    memEvalProgFunc vecSelectionSortProg F vecSelectionSortFunc
      [.stdVecVal l] =
      evalProgFunc vecSelectionSortProg F vecSelectionSortFunc
        [.stdVecVal l] := by
  obtain ⟨i', l', heq⟩ :=
    selectionSortFwd_ok l F G 0 (Nat.zero_le _) (by omega)
      (by omega) hread
  rw [memEvalProgFunc_vecSelectionSort_ok F G l l' i' hl64 hF hG
    hread heq,
    evalProgFunc_vecSelectionSort_ok F G l l' i' hl64 hF hG hread heq]
