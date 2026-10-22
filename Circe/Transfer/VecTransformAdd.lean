/-
Circe.Transfer.VecTransformAdd — M2c mem transfer for out-of-place
checked transform (`vec_transform_add`).

Mirrors the value loop (`valTransformLoop_*` in
`Circe.Emit.VecTransformAdd`) step for step on the memory layer:
the `in`/`out` blocks pin reified snapshots (`cellsAt` framed by
find; the length word shifts offsets by one), `out` stores thread
through `memStore` in lockstep while `memFind_memStore_other` keeps
the `in` pin, and the loop re-inducts over `(ρ, m, π)` with the
forward equation threading (two fuels: program fuel and forward
fuel). Entries close per leg against the M2b contracts.
-/
import Circe.Transfer.VecReverse
import Circe.Emit.VecTransformAdd
import Circe.Specs

/-! ## Binding (closed form) -/

/-- Transform binding pins two snapshots: `out` first (addr `0`),
    `in` second (addr `1`) — `bindMemArgs` recurses tail-first, so
    the later-listed vector binds first; the owned `c` binds by
    value only (env entry, no block, no layout — the `stdVecIndex`
    precedent). -/
theorem bindMemArgs_vecTransformAdd (li lo : List (BitVec 32))
    (c : BitVec 32) :
    bindMemArgs vecTransformAddFunc.args
      [.stdVecVal li, .stdVecVal lo, .i32 c] emptyMem =
      some ([("in", .stdVecVal li), ("out", .stdVecVal lo),
        ("c", .i32 c)],
        ⟨2, [(1, ⟨1, true,
          (BitVec.ofNat 32 li.length) :: li⟩),
          (0, ⟨0, true,
          (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩,
        [("in", 1, 1), ("out", 0, 0)]) := by
  rfl

/-- Transform footprints are two disjoint singletons (the owned `c`
    never touches memory). -/
theorem oracleNoalias_vecTransformAdd (li lo : List (BitVec 32))
    (c : BitVec 32) :
    oracleNoalias vecTransformAddFunc
      [.stdVecVal li, .stdVecVal lo, .i32 c] := by
  have hb := bindMemArgs_vecTransformAdd li lo c
  have hn : LayoutNoAlias [("in", 1, 1), ("out", 0, 0)] := by
    simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-! ## Memory body hit -/

/-- One body iteration on memory, ok step: the env threads exactly as
    on the value side while the `out` store prepends a shadowing
    snapshot block (layout stays pinned; the `in` block is framed by
    `memFind_memStore_other`). -/
theorem memTransformBody_ok (prog : Prog) (F : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (li lo : List (BitVec 32)) (c : BitVec 32)
    (i : Nat) (iB : BitVec 64) (x y z : BitVec 32)
    (aa ab ta tb : Nat) (nA nB : BitVec 32)
    (haa : aa ≠ ab)
    (hlay_in : layoutLookup π "in" = some (aa, ta))
    (hlay_out : layoutLookup π "out" = some (ab, tb))
    (hmem_in : memFind m aa = some ⟨ta, true, nA :: li⟩)
    (hmem_out : memFind m ab = some ⟨tb, true, nB :: lo⟩)
    (hnB : nB = BitVec.ofNat 32 lo.length)
    (hiN : iB.toNat = i)
    (hlo64 : lo.length < 2 ^ 64)
    (hin : envLookup ρ "in" = some (.stdVecVal li))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hc : envLookup ρ "c" = some (.i32 c))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hz : lo[i]? = some z)
    (hx : li[i]? = some x)
    (hy : checkedAddI32 x c = .ok y) :
    ∃ ρ' m', memEvalProgStmt prog F vecTransformBody ρ m π =
      .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "out" = some (.stdVecVal (lo.set i y)) ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = i + 1) ∧
      envLookup ρ' "in" = some (.stdVecVal li) ∧
      envLookup ρ' "c" = some (.i32 c) ∧
      memFind m' aa = some ⟨ta, true, nA :: li⟩ ∧
      memFind m' ab = some ⟨tb, true, nB :: (lo.set i y)⟩ := by
  have hblt : i < lo.length := transformRead_lt lo i z hz
  have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have hiVarA : memEvalExpr (.var "i") ρ m π =
      evalExpr (.var "i") ρ :=
    memEvalExpr_var _ _ _ _
  have hiVarM : memEvalExpr (.var "i") ρ m π = .ok (.u64 iB) :=
    hiVarA.trans hiVar
  have hoLenV : evalExpr (.stdVecLen "out") ρ =
      .ok (.u64 (BitVec.ofNat 64 lo.length)) :=
    evalExpr_stdVecLen_some _ _ _ hout
  have hlenN : (BitVec.ofNat 64 lo.length).toNat = lo.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlo64
  have hmemLenOut : memLoad m ab tb 0 =
      .ok (BitVec.ofNat 32 lo.length) := by
    rw [← hnB]
    exact memLoad_cellsAt m ab tb 0 (nB :: lo) nB hmem_out (by simp)
  have hoLenM : memEvalExpr (.stdVecLen "out") ρ m π =
      evalExpr (.stdVecLen "out") ρ :=
    memEvalExpr_stdVecLen_hit "out" ρ m π lo ab tb
      hlay_out hout hmemLenOut
  have hguardT : evalExpr (.ult (.var "i") (.stdVecLen "out")) ρ =
      .ok (.b true) := by
    have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "out") ρ iB
      (BitVec.ofNat 64 lo.length) hiVar hoLenV
    have htb : (iB.ult (BitVec.ofNat 64 lo.length)) = true := by
      rw [BitVec.ult_eq_decide]
      exact decide_eq_true (by omega)
    rwa [htb] at hult
  have hagT : memEvalExpr (.ult (.var "i") (.stdVecLen "out")) ρ m π =
      .ok (.b true) :=
    (memEvalExpr_ult_agree (.var "i") (.stdVecLen "out")
      ρ m π hiVarA hoLenM).trans hguardT
  have hgetB : lo[iB.toNat]? = some z := by rw [hiN]; exact hz
  have hgetA : li[iB.toNat]? = some x := by rw [hiN]; exact hx
  have hat : evalExpr (.stdVecAt "in" (.var "i")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hin hiVar hgetA
  have hcV : evalExpr (.var "c") ρ = .ok (.i32 c) :=
    evalExpr_var_hit _ _ _ hc
  have hcA : memEvalExpr (.var "c") ρ m π = evalExpr (.var "c") ρ :=
    memEvalExpr_var _ _ _ _
  have hcM : memEvalExpr (.var "c") ρ m π = .ok (.i32 c) :=
    hcA.trans hcV
  have hmemA : memLoad m aa ta (iB.toNat + 1) = .ok x :=
    memLoad_cellsAt m aa ta (iB.toNat + 1) (nA :: li) x
      hmem_in (by rw [List.getElem?_cons_succ]; exact hgetA)
  have hatM_ag : memEvalExpr (.stdVecAt "in" (.var "i")) ρ m π =
      evalExpr (.stdVecAt "in" (.var "i")) ρ :=
    memEvalExpr_stdVecAt_hit "in" (.var "i") ρ m π li iB x aa ta
      hlay_in hin hiVarA hiVar hmemA hgetA
  have hatM : memEvalExpr (.stdVecAt "in" (.var "i")) ρ m π =
      .ok (.i32 x) := by rw [hatM_ag]; exact hat
  have haddV : evalExpr
      (.add (.stdVecAt "in" (.var "i")) (.var "c")) ρ =
      .ok (.i32 y) := by
    have e : evalExpr
        (.add (.stdVecAt "in" (.var "i")) (.var "c")) ρ =
        (checkedAddI32 x c).map .i32 := by
      unfold evalExpr
      rw [hat, hcV]
    rw [e, hy,
      show (Except.ok y).map Value.i32 = Except.ok (Value.i32 y) from rfl]
  have haddVM : memEvalExpr
      (.add (.stdVecAt "in" (.var "i")) (.var "c")) ρ m π =
      .ok (.i32 y) :=
    (memEvalExpr_add_agree
      (.stdVecAt "in" (.var "i")) (.var "c") ρ m π hatM_ag
      hcA).trans haddV
  have hlt' : iB.toNat + 1 < (nB :: lo).length := by
    simp only [List.length_cons]
    omega
  obtain ⟨m₁, hmstore⟩ : ∃ m', memStore m ab tb (iB.toNat + 1) y =
      .ok m' :=
    ⟨_, memStore_cellsAt m ab tb (iB.toNat + 1) (nB :: lo) y
      hmem_out hlt'⟩
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "out"
    (.stdVecVal lo) (.stdVecVal (lo.set iB.toNat y)) hout
  have hstep_set := memRevVecSet prog F "out" (.var "i")
    (.add (.stdVecAt "in" (.var "i")) (.var "c")) ρ m π
    iB y ab tb lo z m₁ ρ₁
    hiVarM haddVM hout hlay_out hgetB hmstore hu₁
  have hcells : cellsAt m₁ ab tb ((nB :: lo).set (iB.toNat + 1) y) :=
    memFind_cellsAt_store m ab tb (iB.toNat + 1) (nB :: lo) y m₁
      hmem_out hlt' hmstore
  have hmem_out' : memFind m₁ ab =
      some ⟨tb, true, nB :: (lo.set i y)⟩ := by
    have e : (nB :: lo).set (iB.toNat + 1) y = nB :: (lo.set i y) := by
      rw [List.set_cons_succ, hiN]
    rw [e] at hcells
    exact hcells
  have hmem_in' : memFind m₁ aa = some ⟨ta, true, nA :: li⟩ := by
    have h := memFind_memStore_other m m₁ ab aa tb (iB.toNat + 1) y
      hmstore haa
    rw [h]; exact hmem_in
  have hi₁ : envLookup ρ₁ "i" = some (.u64 iB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "out" by decide) hu₁]
    exact hi
  have hin₁ : envLookup ρ₁ "in" = some (.stdVecVal li) := by
    have h := envLookup_update_miss ρ "in" "out" _ ρ₁
      (show ("in" : String) ≠ "out" by decide) hu₁
    rw [h]; exact hin
  have hc₁ : envLookup ρ₁ "c" = some (.i32 c) := by
    have h := envLookup_update_miss ρ "c" "out" _ ρ₁
      (show ("c" : String) ≠ "out" by decide) hu₁
    rw [h]; exact hc
  have hiVarA₁ : memEvalExpr (.var "i") ρ₁ m₁ π =
      evalExpr (.var "i") ρ₁ :=
    memEvalExpr_var _ _ _ _
  have hevU : evalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ₁ =
      .ok (.u64 (iB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hi₁) (by simp [evalExpr, litVal])
  have hevUM : memEvalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ₁ m₁ π =
      .ok (.u64 (iB + 1)) :=
    (memEvalExpr_uadd_agree (.var "i") (.lit (.u64 1))
      ρ₁ m₁ π hiVarA₁ (memEvalExpr_lit _ _ _ _)).trans hevU
  obtain ⟨ρ', hu₂⟩ := envUpdate_some_of_lookup ρ₁ "i"
    (.u64 iB) (.u64 (iB + 1)) hi₁
  have hstep_i := memRevAssign prog F "i"
    (.uadd (.var "i") (.lit (.u64 1))) ρ₁ m₁ π (.u64 (iB + 1)) ρ'
    hevUM hevU hu₂
  have hset : lo.set iB.toNat y = lo.set i y := by rw [hiN]
  have hout' : envLookup ρ' "out" =
      some (.stdVecVal (lo.set i y)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "i" by decide) hu₂]
    have : envLookup ρ₁ "out" =
        some (.stdVecVal (lo.set iB.toNat y)) :=
      envLookup_update_hit _ _ _ _ hu₁
    rw [hset] at this
    exact this
  have hi' : envLookup ρ' "i" = some (.u64 (iB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₂
  have hiN' : (iB + 1).toNat = i + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hiN]
    exact Nat.mod_eq_of_lt (by omega)
  have hin' : envLookup ρ' "in" = some (.stdVecVal li) := by
    have h := envLookup_update_miss ρ₁ "in" "i" _ ρ'
      (show ("in" : String) ≠ "i" by decide) hu₂
    rw [h]; exact hin₁
  have hc' : envLookup ρ' "c" = some (.i32 c) := by
    have h := envLookup_update_miss ρ₁ "c" "i" _ ρ'
      (show ("c" : String) ≠ "i" by decide) hu₂
    rw [h]; exact hc₁
  have hif := (memEvalProgStmt_if_true prog F
    (.ult (.var "i") (.stdVecLen "out"))
    (.vecSet "out" (.var "i")
      (.add (.stdVecAt "in" (.var "i")) (.var "c")))
    .fail ρ m π hagT).trans hstep_set
  have hbody : vecTransformBody =
      (.seq (.if_ (.ult (.var "i") (.stdVecLen "out"))
        (.vecSet "out" (.var "i")
          (.add (.stdVecAt "in" (.var "i")) (.var "c")))
        .fail)
        (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))) := rfl
  have heval : memEvalProgStmt prog F vecTransformBody ρ m π =
      .ok ((ρ', m₁, π), .fellThrough) := by
    rw [hbody,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hif,
      hstep_i]
  exact ⟨ρ', m₁, heval, hout', ⟨(iB + 1), hi', hiN'⟩, hin', hc',
    hmem_in', hmem_out'⟩

/-! ## Memory loop inductions -/

/-- Memory loop, ok leg: the loop runs to `li.length`, the `out`
    block holds the forward-model words, the `in` block is untouched
    (fuel induction threading the memory body hit; the forward
    equation unfolds one step per iteration). -/
theorem memTransformLoop_ok (prog : Prog) (F G : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (li lo : List (BitVec 32)) (c : BitVec 32)
    (i : Nat) (iB : BitVec 64) (lo' : List (BitVec 32)) (i' : Nat)
    (aa ab ta tb : Nat) (nA nB : BitVec 32)
    (haa : aa ≠ ab)
    (hlay_in : layoutLookup π "in" = some (aa, ta))
    (hlay_out : layoutLookup π "out" = some (ab, tb))
    (hnA : nA = BitVec.ofNat 32 li.length)
    (hnB : nB = BitVec.ofNat 32 lo.length)
    (hiN : iB.toNat = i)
    (hli64 : li.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hin : envLookup ρ "in" = some (.stdVecVal li))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hc : envLookup ρ "c" = some (.i32 c))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hmem_in : memFind m aa = some ⟨ta, true, nA :: li⟩)
    (hmem_out : memFind m ab = some ⟨tb, true, nB :: lo⟩)
    (hle : i ≤ li.length)
    (hF : li.length - i ≤ F) (hG : li.length - i ≤ G)
    (hread_lo : ∀ p, p < li.length → ∃ z, lo[p]? = some z)
    (hadd : ∀ p, i ≤ p → p < li.length →
      ∃ x y, li[p]? = some x ∧ checkedAddI32 x c = .ok y)
    (hfwd : transformAddFwd li c lo G i = .ok (i', lo')) :
    ∃ ρ' m', memEvalProgStmt prog F vecTransformLoop ρ m π =
        .ok ((ρ', m', π), .fellThrough) ∧
      envLookup ρ' "out" = some (.stdVecVal lo') ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = i') ∧
      memFind m' aa = some ⟨ta, true, nA :: li⟩ ∧
      memFind m' ab = some ⟨tb, true, nB :: lo'⟩ := by
  induction F generalizing G ρ m lo i iB with
  | zero =>
    have him : i = li.length := by omega
    have hlenN : (BitVec.ofNat 64 li.length).toNat = li.length := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hli64
    have hmemLenIn : memLoad m aa ta 0 =
        .ok (BitVec.ofNat 32 li.length) := by
      rw [← hnA]
      exact memLoad_cellsAt m aa ta 0 (nA :: li) nA hmem_in (by simp)
    have hguardF : memEvalExpr
        (.ult (.var "i") (.stdVecLen "in")) ρ m π =
        .ok (.b false) := by
      have hag : memEvalExpr (.ult (.var "i") (.stdVecLen "in")) ρ m π =
          evalExpr (.ult (.var "i") (.stdVecLen "in")) ρ :=
        memEvalExpr_ult_agree (.var "i") (.stdVecLen "in") ρ m π
          (memEvalExpr_var _ _ _ _)
          (memEvalExpr_stdVecLen_hit "in" ρ m π li aa ta
            hlay_in hin hmemLenIn)
      have hval : evalExpr (.ult (.var "i") (.stdVecLen "in")) ρ =
          .ok (.b false) := by
        have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "in") ρ iB
          (BitVec.ofNat 64 li.length)
          (evalExpr_var_hit _ _ _ hi)
          (evalExpr_stdVecLen_some _ _ _ hin)
        have hfb : (iB.ult (BitVec.ofNat 64 li.length)) = false := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_false (by omega)
        rwa [hfb] at hult
      rw [hag]; exact hval
    have hexit : memEvalProgStmt prog 0 vecTransformLoop ρ m π =
        .ok ((ρ, m, π), .fellThrough) :=
      memEvalProgStmt_while_false prog 0 _ _ _ _ _ hguardF
    have hpair : (i, lo) = (i', lo') := by
      cases G with
      | zero => simpa [transformAddFwd] using hfwd
      | succ G =>
        have hneg : ¬ i < li.length := by omega
        simpa [transformAddFwd, dite_eq_right hneg] using hfwd
    obtain ⟨rfl, rfl⟩ := hpair
    exact ⟨ρ, m, hexit, hout, ⟨iB, hi, hiN⟩, hmem_in, hmem_out⟩
  | succ F ih =>
    by_cases hlt : i < li.length
    · have hlenN : (BitVec.ofNat 64 li.length).toNat = li.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hli64
      have hmemLenIn : memLoad m aa ta 0 =
          .ok (BitVec.ofNat 32 li.length) := by
        rw [← hnA]
        exact memLoad_cellsAt m aa ta 0 (nA :: li) nA hmem_in
          (by simp)
      have hguardT : memEvalExpr
          (.ult (.var "i") (.stdVecLen "in")) ρ m π =
          .ok (.b true) := by
        have hag : memEvalExpr
            (.ult (.var "i") (.stdVecLen "in")) ρ m π =
            evalExpr (.ult (.var "i") (.stdVecLen "in")) ρ :=
          memEvalExpr_ult_agree (.var "i") (.stdVecLen "in") ρ m π
            (memEvalExpr_var _ _ _ _)
            (memEvalExpr_stdVecLen_hit "in" ρ m π li aa ta
              hlay_in hin hmemLenIn)
        have hval : evalExpr (.ult (.var "i") (.stdVecLen "in")) ρ =
            .ok (.b true) := by
          have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "in")
            ρ iB (BitVec.ofNat 64 li.length)
            (evalExpr_var_hit _ _ _ hi)
            (evalExpr_stdVecLen_some _ _ _ hin)
          have htb : (iB.ult (BitVec.ofNat 64 li.length)) = true := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_true (by omega)
          rwa [htb] at hult
        rw [hag]; exact hval
      obtain ⟨z, hz⟩ := hread_lo i hlt
      obtain ⟨x, y, hx, hy⟩ := hadd i (Nat.le_refl _) hlt
      have hF' : li.length - (i + 1) ≤ F := by omega
      obtain ⟨G', rfl, hG'⟩ :=
        fuel_step_down (F := G) (li.length - (i + 1)) (by omega)
      have hlo64' : (lo.set i y).length < 2 ^ 64 := by
        rw [List.length_set]; exact hlo64
      have hread_lo' : ∀ p, p < li.length →
          ∃ z, ((lo.set i y)[p]? = some z) := by
        intro p hp
        by_cases hpi : p = i
        · rw [hpi]
          have hblt : i < lo.length := transformRead_lt lo i z hz
          exact ⟨y, List.getElem?_set_self hblt⟩
        · obtain ⟨z, hz⟩ := hread_lo p hp
          exact ⟨z, by
            rw [List.getElem?_set_ne (show i ≠ p by omega)]
            exact hz⟩
      have hadd' : ∀ p, i + 1 ≤ p → p < li.length →
          ∃ x y, li[p]? = some x ∧ checkedAddI32 x c = .ok y := by
        intro p h1 h2
        exact hadd p (by omega) h2
      obtain ⟨ρ₁, m₁, hbody, hout₁, ⟨iB₁, hiB₁, hiN₁⟩, hin₁, hc₁,
          hmem_in₁, hmem_out₁⟩ :=
        memTransformBody_ok prog F ρ m π li lo c i iB x y z
          aa ab ta tb nA nB haa hlay_in hlay_out hmem_in hmem_out
          hnB hiN hlo64 hin hout hc hi hz hx hy
      have hfwd' : transformAddFwd li c (lo.set i y) G' (i + 1) =
          .ok (i', lo') := by
        have h := hfwd
        simp only [transformAddFwd, dite_eq_left hlt, hz, hx, hy] at h
        exact h
      obtain ⟨ρ', m', hloop, hout', ⟨iB', hiB', hiN'⟩, hmem_in',
          hmem_out'⟩ :=
        ih (G := G') (ρ := ρ₁) (m := m₁) (lo := lo.set i y)
          (i := i + 1) (iB := iB₁)
          (hiN := hiN₁) (hlo64 := hlo64')
          (hin := hin₁) (hout := hout₁) (hc := hc₁) (hi := hiB₁)
          (hmem_in := hmem_in₁) (hmem_out := hmem_out₁)
          (hnB := by rw [List.length_set]; exact hnB)
          (hle := by omega) (hF := hF') (hG := hG')
          (hread_lo := hread_lo') (hadd := hadd') (hfwd := hfwd')
      refine ⟨ρ', m', ?_, hout', ⟨iB', hiB', hiN'⟩, hmem_in',
        hmem_out'⟩
      have hwhile : memEvalProgStmt prog (F + 1) vecTransformLoop
          ρ m π =
          memEvalProgStmt prog F vecTransformLoop ρ₁ m₁ π := by
        simp only [vecTransformLoop,
          memEvalProgStmt_while_true prog F _ _ _ _ _ hguardT,
          hbody]
      rw [hwhile]
      exact hloop
    · have him : i = li.length := by omega
      have hlenN : (BitVec.ofNat 64 li.length).toNat = li.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hli64
      have hmemLenIn : memLoad m aa ta 0 =
          .ok (BitVec.ofNat 32 li.length) := by
        rw [← hnA]
        exact memLoad_cellsAt m aa ta 0 (nA :: li) nA hmem_in
          (by simp)
      have hguardF : memEvalExpr
          (.ult (.var "i") (.stdVecLen "in")) ρ m π =
          .ok (.b false) := by
        have hag : memEvalExpr
            (.ult (.var "i") (.stdVecLen "in")) ρ m π =
            evalExpr (.ult (.var "i") (.stdVecLen "in")) ρ :=
          memEvalExpr_ult_agree (.var "i") (.stdVecLen "in") ρ m π
            (memEvalExpr_var _ _ _ _)
            (memEvalExpr_stdVecLen_hit "in" ρ m π li aa ta
              hlay_in hin hmemLenIn)
        have hval : evalExpr (.ult (.var "i") (.stdVecLen "in")) ρ =
            .ok (.b false) := by
          have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "in")
            ρ iB (BitVec.ofNat 64 li.length)
            (evalExpr_var_hit _ _ _ hi)
            (evalExpr_stdVecLen_some _ _ _ hin)
          have hfb : (iB.ult (BitVec.ofNat 64 li.length)) = false := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_false (by omega)
          rwa [hfb] at hult
        rw [hag]; exact hval
      have hexit : memEvalProgStmt prog (F + 1) vecTransformLoop ρ m π =
          .ok ((ρ, m, π), .fellThrough) :=
        memEvalProgStmt_while_false prog (F + 1) _ _ _ _ _ hguardF
      have hpair : (i, lo) = (i', lo') := by
        cases G with
        | zero => simpa [transformAddFwd] using hfwd
        | succ G =>
          have hneg : ¬ i < li.length := by omega
          simpa [transformAddFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl⟩ := hpair
      exact ⟨ρ, m, hexit, hout, ⟨iB, hi, hiN⟩, hmem_in, hmem_out⟩

/-- Memory loop, short-`out` error leg: the first missing write
    aborts loudly (fuel induction; the forward equation threads). -/
theorem memTransformLoop_err_short (prog : Prog) (F G : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (li lo : List (BitVec 32)) (c : BitVec 32)
    (i j : Nat) (iB : BitVec 64)
    (aa ab ta tb : Nat) (nA nB : BitVec 32)
    (haa : aa ≠ ab)
    (hlay_in : layoutLookup π "in" = some (aa, ta))
    (hlay_out : layoutLookup π "out" = some (ab, tb))
    (hnA : nA = BitVec.ofNat 32 li.length)
    (hnB : nB = BitVec.ofNat 32 lo.length)
    (hiN : iB.toNat = i)
    (hli64 : li.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hj : j < li.length)
    (hin : envLookup ρ "in" = some (.stdVecVal li))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hc : envLookup ρ "c" = some (.i32 c))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hmem_in : memFind m aa = some ⟨ta, true, nA :: li⟩)
    (hmem_out : memFind m ab = some ⟨tb, true, nB :: lo⟩)
    (hle : i ≤ j) (hF : j - i + 1 ≤ F) (hG : j - i + 1 ≤ G)
    (hreads : ∀ p, i ≤ p → p < j → ∃ z, lo[p]? = some z)
    (hadds : ∀ p, i ≤ p → p < j →
      ∃ x y, li[p]? = some x ∧ checkedAddI32 x c = .ok y)
    (hmiss : lo[j]? = none)
    (hfwd : transformAddFwd li c lo G i = .error .AssertFail) :
    memEvalProgStmt prog F vecTransformLoop ρ m π =
      .error .AssertFail := by
  induction F generalizing G ρ m lo i iB with
  | zero => exact (by omega : False).elim
  | succ F ih =>
    by_cases hij : i = j
    · subst hij
      have hnl : ¬ i < lo.length := by
        intro h
        have hsome : lo[i]? = some lo[i] := List.getElem?_eq_getElem h
        rw [hsome] at hmiss
        simp at hmiss
      have hlenN : (BitVec.ofNat 64 lo.length).toNat = lo.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlo64
      have hmemLenOut : memLoad m ab tb 0 =
          .ok (BitVec.ofNat 32 lo.length) := by
        rw [← hnB]
        exact memLoad_cellsAt m ab tb 0 (nB :: lo) nB hmem_out
          (by simp)
      have hguardF : memEvalExpr
          (.ult (.var "i") (.stdVecLen "out")) ρ m π =
          .ok (.b false) := by
        have hag : memEvalExpr
            (.ult (.var "i") (.stdVecLen "out")) ρ m π =
            evalExpr (.ult (.var "i") (.stdVecLen "out")) ρ :=
          memEvalExpr_ult_agree (.var "i") (.stdVecLen "out") ρ m π
            (memEvalExpr_var _ _ _ _)
            (memEvalExpr_stdVecLen_hit "out" ρ m π lo ab tb
              hlay_out hout hmemLenOut)
        have hval : evalExpr
            (.ult (.var "i") (.stdVecLen "out")) ρ =
            .ok (.b false) := by
          have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "out")
            ρ iB (BitVec.ofNat 64 lo.length)
            (evalExpr_var_hit _ _ _ hi)
            (evalExpr_stdVecLen_some _ _ _ hout)
          have hfb : (iB.ult (BitVec.ofNat 64 lo.length)) = false := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_false (by omega)
          rwa [hfb] at hult
        rw [hag]; exact hval
      have hlenIN : (BitVec.ofNat 64 li.length).toNat = li.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hli64
      have hmemLenIn : memLoad m aa ta 0 =
          .ok (BitVec.ofNat 32 li.length) := by
        rw [← hnA]
        exact memLoad_cellsAt m aa ta 0 (nA :: li) nA hmem_in
          (by simp)
      have hguardT : memEvalExpr
          (.ult (.var "i") (.stdVecLen "in")) ρ m π =
          .ok (.b true) := by
        have hag : memEvalExpr
            (.ult (.var "i") (.stdVecLen "in")) ρ m π =
            evalExpr (.ult (.var "i") (.stdVecLen "in")) ρ :=
          memEvalExpr_ult_agree (.var "i") (.stdVecLen "in") ρ m π
            (memEvalExpr_var _ _ _ _)
            (memEvalExpr_stdVecLen_hit "in" ρ m π li aa ta
              hlay_in hin hmemLenIn)
        have hval : evalExpr (.ult (.var "i") (.stdVecLen "in")) ρ =
            .ok (.b true) := by
          have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "in")
            ρ iB (BitVec.ofNat 64 li.length)
            (evalExpr_var_hit _ _ _ hi)
            (evalExpr_stdVecLen_some _ _ _ hin)
          have htb : (iB.ult (BitVec.ofNat 64 li.length)) = true := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_true (by omega)
          rwa [htb] at hult
        rw [hag]; exact hval
      have hfail : memEvalProgStmt prog F .fail ρ m π =
          .error .AssertFail := by
        simpa [memEvalProgStmt] using (memEvalStmtFuel_fail F ρ m π)
      have hif : memEvalProgStmt prog F
          (.if_ (.ult (.var "i") (.stdVecLen "out"))
            (.vecSet "out" (.var "i")
              (.add (.stdVecAt "in" (.var "i")) (.var "c")))
            .fail) ρ m π = .error .AssertFail :=
        (memEvalProgStmt_if_false _ _ _ _ _ _ _ _ hguardF).trans hfail
      have hbody : vecTransformBody =
          (.seq (.if_ (.ult (.var "i") (.stdVecLen "out"))
            (.vecSet "out" (.var "i")
              (.add (.stdVecAt "in" (.var "i")) (.var "c")))
            .fail)
            (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))) := rfl
      have hbodyval : memEvalProgStmt prog F vecTransformBody ρ m π =
          .error .AssertFail := by
        rw [hbody]
        exact memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hif
      simp only [vecTransformLoop,
        memEvalProgStmt_while_true prog F _ _ _ _ _ hguardT, hbodyval]
    · have hlt : i < j := by omega
      have hlt_len : i < li.length := by omega
      have hF' : j - (i + 1) + 1 ≤ F := by omega
      obtain ⟨G', rfl, hG'⟩ :=
        fuel_step_down (F := G) (j - (i + 1) + 1) (by omega)
      obtain ⟨z, hz⟩ := hreads i (Nat.le_refl _) hlt
      obtain ⟨x, y, hx, hy⟩ := hadds i (Nat.le_refl _) hlt
      have hlo64' : (lo.set i y).length < 2 ^ 64 := by
        rw [List.length_set]; exact hlo64
      have hlenN : (BitVec.ofNat 64 li.length).toNat = li.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hli64
      have hmemLenIn : memLoad m aa ta 0 =
          .ok (BitVec.ofNat 32 li.length) := by
        rw [← hnA]
        exact memLoad_cellsAt m aa ta 0 (nA :: li) nA hmem_in
          (by simp)
      have hguardT : memEvalExpr
          (.ult (.var "i") (.stdVecLen "in")) ρ m π =
          .ok (.b true) := by
        have hag : memEvalExpr
            (.ult (.var "i") (.stdVecLen "in")) ρ m π =
            evalExpr (.ult (.var "i") (.stdVecLen "in")) ρ :=
          memEvalExpr_ult_agree (.var "i") (.stdVecLen "in") ρ m π
            (memEvalExpr_var _ _ _ _)
            (memEvalExpr_stdVecLen_hit "in" ρ m π li aa ta
              hlay_in hin hmemLenIn)
        have hval : evalExpr (.ult (.var "i") (.stdVecLen "in")) ρ =
            .ok (.b true) := by
          have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "in")
            ρ iB (BitVec.ofNat 64 li.length)
            (evalExpr_var_hit _ _ _ hi)
            (evalExpr_stdVecLen_some _ _ _ hin)
          have htb : (iB.ult (BitVec.ofNat 64 li.length)) = true := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_true (by omega)
          rwa [htb] at hult
        rw [hag]; exact hval
      have hreads' : ∀ p, i + 1 ≤ p → p < j →
          ∃ z, ((lo.set i y)[p]? = some z) := by
        intro p h1 h2
        obtain ⟨z, hz⟩ := hreads p (by omega) h2
        exact ⟨z, by
          rw [List.getElem?_set_ne (show i ≠ p by omega)]
          exact hz⟩
      have hadds' : ∀ p, i + 1 ≤ p → p < j →
          ∃ x y, li[p]? = some x ∧ checkedAddI32 x c = .ok y := by
        intro p h1 h2
        exact hadds p (by omega) h2
      obtain ⟨ρ₁, m₁, hbodyval, hout₁, ⟨iB₁, hiB₁, hiN₁⟩, hin₁, hc₁,
          hmem_in₁, hmem_out₁⟩ :=
        memTransformBody_ok prog F ρ m π li lo c i iB x y z
          aa ab ta tb nA nB haa hlay_in hlay_out hmem_in hmem_out
          hnB hiN hlo64 hin hout hc hi hz hx hy
      have hfwd' : transformAddFwd li c (lo.set i y) G' (i + 1) =
          .error .AssertFail := by
        have h := hfwd
        simp only [transformAddFwd, dite_eq_left hlt_len, hz, hx, hy] at h
        exact h
      have hmiss' : (lo.set i y)[j]? = none := by
        rw [List.getElem?_set_ne (show i ≠ j by omega)]
        exact hmiss
      have hnB' : nB = BitVec.ofNat 32 (lo.set i y).length := by
        rw [List.length_set]; exact hnB
      have hloop :=
        ih (G := G') (ρ := ρ₁) (m := m₁) (lo := lo.set i y)
          (i := i + 1) (iB := iB₁)
          (hiN := hiN₁) (hlo64 := hlo64')
          (hin := hin₁) (hout := hout₁) (hc := hc₁) (hi := hiB₁)
          (hmem_in := hmem_in₁) (hmem_out := hmem_out₁)
          (hnB := hnB')
          (hle := by omega) (hF := hF') (hG := hG')
          (hreads := hreads') (hadds := hadds') (hmiss := hmiss')
          (hfwd := hfwd')
      have hwhile : memEvalProgStmt prog (F + 1) vecTransformLoop
          ρ m π =
          memEvalProgStmt prog F vecTransformLoop ρ₁ m₁ π := by
        simp only [vecTransformLoop,
          memEvalProgStmt_while_true prog F _ _ _ _ _ hguardT,
          hbodyval]
      rw [hwhile]
      exact hloop

/-- Memory loop, checked-add error leg: the first failing add
    propagates (fuel induction; the forward equation threads). -/
theorem memTransformLoop_err_add (prog : Prog) (F G : Nat)
    (ρ : Env) (m : Mem) (π : Layout)
    (li lo : List (BitVec 32)) (c : BitVec 32)
    (i j : Nat) (iB : BitVec 64) (e : Panic)
    (aa ab ta tb : Nat) (nA nB : BitVec 32)
    (haa : aa ≠ ab)
    (hlay_in : layoutLookup π "in" = some (aa, ta))
    (hlay_out : layoutLookup π "out" = some (ab, tb))
    (hnA : nA = BitVec.ofNat 32 li.length)
    (hnB : nB = BitVec.ofNat 32 lo.length)
    (hiN : iB.toNat = i)
    (hli64 : li.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hj : j < li.length)
    (hin : envLookup ρ "in" = some (.stdVecVal li))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hc : envLookup ρ "c" = some (.i32 c))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hmem_in : memFind m aa = some ⟨ta, true, nA :: li⟩)
    (hmem_out : memFind m ab = some ⟨tb, true, nB :: lo⟩)
    (hle : i ≤ j) (hF : j - i + 1 ≤ F) (hG : j - i + 1 ≤ G)
    (hreads : ∀ p, i ≤ p → p ≤ j → ∃ z, lo[p]? = some z)
    (hadds : ∀ p, i ≤ p → p < j →
      ∃ x y, li[p]? = some x ∧ checkedAddI32 x c = .ok y)
    (hx : ∃ x, li[j]? = some x)
    (herr : ∀ x, li[j]? = some x → checkedAddI32 x c = .error e)
    (hfwd : transformAddFwd li c lo G i = .error e) :
    memEvalProgStmt prog F vecTransformLoop ρ m π = .error e := by
  induction F generalizing G ρ m lo i iB with
  | zero => exact (by omega : False).elim
  | succ F ih =>
    by_cases hij : i = j
    · subst hij
      obtain ⟨x, hx'⟩ := hx
      obtain ⟨z, hz⟩ := hreads i (Nat.le_refl _) (Nat.le_refl _)
      have hblt : i < lo.length := transformRead_lt lo i z hz
      have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
        evalExpr_var_hit _ _ _ hi
      have hiVarA : memEvalExpr (.var "i") ρ m π =
          evalExpr (.var "i") ρ :=
        memEvalExpr_var _ _ _ _
      have hiVarM : memEvalExpr (.var "i") ρ m π = .ok (.u64 iB) :=
        hiVarA.trans hiVar
      have hlenN : (BitVec.ofNat 64 lo.length).toNat = lo.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlo64
      have hmemLenOut : memLoad m ab tb 0 =
          .ok (BitVec.ofNat 32 lo.length) := by
        rw [← hnB]
        exact memLoad_cellsAt m ab tb 0 (nB :: lo) nB hmem_out
          (by simp)
      have hguardT : memEvalExpr
          (.ult (.var "i") (.stdVecLen "out")) ρ m π =
          .ok (.b true) := by
        have hag : memEvalExpr
            (.ult (.var "i") (.stdVecLen "out")) ρ m π =
            evalExpr (.ult (.var "i") (.stdVecLen "out")) ρ :=
          memEvalExpr_ult_agree (.var "i") (.stdVecLen "out") ρ m π
            hiVarA
            (memEvalExpr_stdVecLen_hit "out" ρ m π lo ab tb
              hlay_out hout hmemLenOut)
        have hval : evalExpr
            (.ult (.var "i") (.stdVecLen "out")) ρ =
            .ok (.b true) := by
          have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "out")
            ρ iB (BitVec.ofNat 64 lo.length) hiVar
            (evalExpr_stdVecLen_some _ _ _ hout)
          have htb : (iB.ult (BitVec.ofNat 64 lo.length)) = true := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_true (by omega)
          rwa [htb] at hult
        rw [hag]; exact hval
      have hlenIN : (BitVec.ofNat 64 li.length).toNat = li.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hli64
      have hmemLenIn : memLoad m aa ta 0 =
          .ok (BitVec.ofNat 32 li.length) := by
        rw [← hnA]
        exact memLoad_cellsAt m aa ta 0 (nA :: li) nA hmem_in
          (by simp)
      have hguardLoop : memEvalExpr
          (.ult (.var "i") (.stdVecLen "in")) ρ m π =
          .ok (.b true) := by
        have hag : memEvalExpr
            (.ult (.var "i") (.stdVecLen "in")) ρ m π =
            evalExpr (.ult (.var "i") (.stdVecLen "in")) ρ :=
          memEvalExpr_ult_agree (.var "i") (.stdVecLen "in") ρ m π
            hiVarA
            (memEvalExpr_stdVecLen_hit "in" ρ m π li aa ta
              hlay_in hin hmemLenIn)
        have hval : evalExpr (.ult (.var "i") (.stdVecLen "in")) ρ =
            .ok (.b true) := by
          have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "in")
            ρ iB (BitVec.ofNat 64 li.length) hiVar
            (evalExpr_stdVecLen_some _ _ _ hin)
          have htb : (iB.ult (BitVec.ofNat 64 li.length)) = true := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_true (by omega)
          rwa [htb] at hult
        rw [hag]; exact hval
      have hgetA : li[iB.toNat]? = some x := by rw [hiN]; exact hx'
      have hat : evalExpr (.stdVecAt "in" (.var "i")) ρ =
          .ok (.i32 x) :=
        evalExpr_stdVecAt_some _ _ _ _ _ _ hin hiVar hgetA
      have hcV : evalExpr (.var "c") ρ = .ok (.i32 c) :=
        evalExpr_var_hit _ _ _ hc
      have haddV_err : evalExpr
          (.add (.stdVecAt "in" (.var "i")) (.var "c")) ρ =
          .error e := by
        have h := herr x hx'
        have e2 : evalExpr
            (.add (.stdVecAt "in" (.var "i")) (.var "c")) ρ =
            (checkedAddI32 x c).map .i32 := by
          unfold evalExpr
          rw [hat, hcV]
        rw [e2, h,
          show (Except.error e).map Value.i32 = Except.error e from rfl]
      have hmemA : memLoad m aa ta (iB.toNat + 1) = .ok x := by
        have hgetA' : (nA :: li)[iB.toNat + 1]? = some x := by
          rw [List.getElem?_cons_succ]; exact hgetA
        exact memLoad_cellsAt m aa ta (iB.toNat + 1) (nA :: li) x
          hmem_in hgetA'
      have hatM_ag : memEvalExpr (.stdVecAt "in" (.var "i")) ρ m π =
          evalExpr (.stdVecAt "in" (.var "i")) ρ :=
        memEvalExpr_stdVecAt_hit "in" (.var "i") ρ m π li iB x aa ta
          hlay_in hin hiVarA hiVar hmemA hgetA
      have hcA : memEvalExpr (.var "c") ρ m π =
          evalExpr (.var "c") ρ :=
        memEvalExpr_var _ _ _ _
      have haddVM_err : memEvalExpr
          (.add (.stdVecAt "in" (.var "i")) (.var "c")) ρ m π =
          .error e := by
        have hag := memEvalExpr_add_agree
          (.stdVecAt "in" (.var "i")) (.var "c") ρ m π hatM_ag hcA
        rw [hag]; exact haddV_err
      have hset : memEvalProgStmt prog F
          (.vecSet "out" (.var "i")
            (.add (.stdVecAt "in" (.var "i")) (.var "c"))) ρ m π =
            .error e := by
        have hfuel : memEvalStmtFuel F
            (.vecSet "out" (.var "i")
              (.add (.stdVecAt "in" (.var "i")) (.var "c"))) ρ m π =
            .error e := by
          cases F <;> simp [memEvalStmtFuel, memEvalStmtZero,
            memEvalStmtWith, hiVarM, haddVM_err]
        simpa [memEvalProgStmt] using hfuel
      have hif : memEvalProgStmt prog F
          (.if_ (.ult (.var "i") (.stdVecLen "out"))
            (.vecSet "out" (.var "i")
              (.add (.stdVecAt "in" (.var "i")) (.var "c")))
            .fail) ρ m π = .error e :=
        (memEvalProgStmt_if_true _ _ _ _ _ _ _ _ hguardT).trans hset
      have hbody : vecTransformBody =
          (.seq (.if_ (.ult (.var "i") (.stdVecLen "out"))
            (.vecSet "out" (.var "i")
              (.add (.stdVecAt "in" (.var "i")) (.var "c")))
            .fail)
            (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))) := rfl
      have hbodyval : memEvalProgStmt prog F vecTransformBody ρ m π =
          .error e := by
        rw [hbody]
        exact memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hif
      simp only [vecTransformLoop,
        memEvalProgStmt_while_true prog F _ _ _ _ _ hguardLoop,
        hbodyval]
    · have hlt : i < j := by omega
      have hlt_len : i < li.length := by omega
      have hF' : j - (i + 1) + 1 ≤ F := by omega
      obtain ⟨G', rfl, hG'⟩ :=
        fuel_step_down (F := G) (j - (i + 1) + 1) (by omega)
      obtain ⟨z, hz⟩ := hreads i (Nat.le_refl _) (by omega)
      obtain ⟨x, y, hx, hy⟩ := hadds i (Nat.le_refl _) hlt
      have hlo64' : (lo.set i y).length < 2 ^ 64 := by
        rw [List.length_set]; exact hlo64
      have hlenN : (BitVec.ofNat 64 li.length).toNat = li.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hli64
      have hmemLenIn : memLoad m aa ta 0 =
          .ok (BitVec.ofNat 32 li.length) := by
        rw [← hnA]
        exact memLoad_cellsAt m aa ta 0 (nA :: li) nA hmem_in
          (by simp)
      have hguardT : memEvalExpr
          (.ult (.var "i") (.stdVecLen "in")) ρ m π =
          .ok (.b true) := by
        have hag : memEvalExpr
            (.ult (.var "i") (.stdVecLen "in")) ρ m π =
            evalExpr (.ult (.var "i") (.stdVecLen "in")) ρ :=
          memEvalExpr_ult_agree (.var "i") (.stdVecLen "in") ρ m π
            (memEvalExpr_var _ _ _ _)
            (memEvalExpr_stdVecLen_hit "in" ρ m π li aa ta
              hlay_in hin hmemLenIn)
        have hval : evalExpr (.ult (.var "i") (.stdVecLen "in")) ρ =
            .ok (.b true) := by
          have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "in")
            ρ iB (BitVec.ofNat 64 li.length)
            (evalExpr_var_hit _ _ _ hi)
            (evalExpr_stdVecLen_some _ _ _ hin)
          have htb : (iB.ult (BitVec.ofNat 64 li.length)) = true := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_true (by omega)
          rwa [htb] at hult
        rw [hag]; exact hval
      have hreads' : ∀ p, i + 1 ≤ p → p ≤ j →
          ∃ z, ((lo.set i y)[p]? = some z) := by
        intro p h1 h2
        obtain ⟨z, hz⟩ := hreads p (by omega) h2
        exact ⟨z, by
          rw [List.getElem?_set_ne (show i ≠ p by omega)]
          exact hz⟩
      have hadds' : ∀ p, i + 1 ≤ p → p < j →
          ∃ x y, li[p]? = some x ∧ checkedAddI32 x c = .ok y := by
        intro p h1 h2
        exact hadds p (by omega) h2
      obtain ⟨ρ₁, m₁, hbodyval, hout₁, ⟨iB₁, hiB₁, hiN₁⟩, hin₁, hc₁,
          hmem_in₁, hmem_out₁⟩ :=
        memTransformBody_ok prog F ρ m π li lo c i iB x y z
          aa ab ta tb nA nB haa hlay_in hlay_out hmem_in hmem_out
          hnB hiN hlo64 hin hout hc hi hz hx hy
      have hfwd' : transformAddFwd li c (lo.set i y) G' (i + 1) =
          .error e := by
        have h := hfwd
        simp only [transformAddFwd, dite_eq_left hlt_len, hz, hx, hy] at h
        exact h
      have hnB' : nB = BitVec.ofNat 32 (lo.set i y).length := by
        rw [List.length_set]; exact hnB
      have hloop :=
        ih (G := G') (ρ := ρ₁) (m := m₁) (lo := lo.set i y)
          (i := i + 1) (iB := iB₁)
          (hiN := hiN₁) (hlo64 := hlo64')
          (hin := hin₁) (hout := hout₁) (hc := hc₁) (hi := hiB₁)
          (hmem_in := hmem_in₁) (hmem_out := hmem_out₁)
          (hnB := hnB')
          (hle := by omega) (hF := hF') (hG := hG')
          (hreads := hreads') (hadds := hadds') (hfwd := hfwd')
      have hwhile : memEvalProgStmt prog (F + 1) vecTransformLoop
          ρ m π =
          memEvalProgStmt prog F vecTransformLoop ρ₁ m₁ π := by
        simp only [vecTransformLoop,
          memEvalProgStmt_while_true prog F _ _ _ _ _ hguardT,
          hbodyval]
      rw [hwhile]
      exact hloop

/-! ## Entry bridges (`evalProgFunc` per leg) -/

/-- Value entry, ok leg: binding, `i ← 0`, the loop, and `return out`
    compute the forward-model words (the `hfwd` equation comes from
    the M2b ok contract). -/
theorem evalProgFunc_vecTransformAdd_ok (F : Nat)
    (li lo lo' : List (BitVec 32)) (c : BitVec 32)
    (hli64 : li.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : li.length ≤ F)
    (hread_lo : ∀ p, p < li.length → ∃ z, lo[p]? = some z)
    (hadd : ∀ p, 0 ≤ p → p < li.length →
      ∃ x y, li[p]? = some x ∧ checkedAddI32 x c = .ok y)
    (hfwd : transformAddFwd li c lo li.length 0 =
      .ok (li.length, lo')) :
    evalProgFunc vecTransformAddProg F vecTransformAddFunc
      [.stdVecVal li, .stdVecVal lo, .i32 c] =
      .ok (.stdVecVal lo') := by
  have hbind : bindArgs vecTransformAddFunc.args
      [.stdVecVal li, .stdVecVal lo, .i32 c] =
      some [("in", .stdVecVal li), ("out", .stdVecVal lo),
        ("c", .i32 c)] := rfl
  have hbody : vecTransformAddFunc.body =
      (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq vecTransformLoop
          (.return_ (.var "out")))) := rfl
  have hlit : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("in", .stdVecVal li), ("out", .stdVecVal lo),
        ("c", .i32 c)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hlet := revLet vecTransformAddProg F "i" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
    (.u64 (BitVec.ofNat 64 0)) hlit
  have hiN : (BitVec.ofNat 64 0).toNat = 0 := by
    simp [BitVec.toNat_ofNat]
  have hin₁ : envLookup (envExtend
      [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
      "i" (.u64 (BitVec.ofNat 64 0))) "in" =
      some (.stdVecVal li) := by
    rw [envExtend_miss _ _ _ _
      (show ("in" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hout₁ : envLookup (envExtend
      [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
      "i" (.u64 (BitVec.ofNat 64 0))) "out" =
      some (.stdVecVal lo) := by
    rw [envExtend_miss _ _ _ _
      (show ("out" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hc₁ : envLookup (envExtend
      [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
      "i" (.u64 (BitVec.ofNat 64 0))) "c" =
      some (.i32 c) := by
    rw [envExtend_miss _ _ _ _
      (show ("c" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hi₁ : envLookup (envExtend
      [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
      "i" (.u64 (BitVec.ofNat 64 0))) "i" =
      some (.u64 (BitVec.ofNat 64 0)) :=
    envExtend_hit _ _ _
  obtain ⟨ρ', hloop, hout', ⟨iB', hiB', hiN'⟩⟩ :=
    valTransformLoop_ok vecTransformAddProg F li.length
      (envExtend [("in", .stdVecVal li), ("out", .stdVecVal lo),
        ("c", .i32 c)] "i" (.u64 (BitVec.ofNat 64 0)))
      li lo c 0 (BitVec.ofNat 64 0) lo' li.length
      hiN hli64 hlo64 hin₁ hout₁ hc₁ hi₁ (Nat.zero_le _)
      (by omega) (by omega) hread_lo hadd hfwd
  have hret := evalProgStmt_return vecTransformAddProg F
    (.var "out") ρ' (.stdVecVal lo')
    (evalExpr_var_hit _ _ _ hout')
  simp only [evalProgFunc, hbind, hbody]
  rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hlet,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hloop,
    hret]

/-- Value entry, short-`out` error leg. -/
theorem evalProgFunc_vecTransformAdd_err_short (F : Nat)
    (li lo : List (BitVec 32)) (c : BitVec 32)
    (j : Nat)
    (hli64 : li.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hj : j < li.length)
    (hF : j + 1 ≤ F)
    (hreads : ∀ p, 0 ≤ p → p < j → ∃ z, lo[p]? = some z)
    (hadds : ∀ p, 0 ≤ p → p < j →
      ∃ x y, li[p]? = some x ∧ checkedAddI32 x c = .ok y)
    (hmiss : lo[j]? = none)
    (hfwd : transformAddFwd li c lo li.length 0 = .error .AssertFail) :
    evalProgFunc vecTransformAddProg F vecTransformAddFunc
      [.stdVecVal li, .stdVecVal lo, .i32 c] = .error .AssertFail := by
  have hbind : bindArgs vecTransformAddFunc.args
      [.stdVecVal li, .stdVecVal lo, .i32 c] =
      some [("in", .stdVecVal li), ("out", .stdVecVal lo),
        ("c", .i32 c)] := rfl
  have hbody : vecTransformAddFunc.body =
      (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq vecTransformLoop
          (.return_ (.var "out")))) := rfl
  have hlit : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("in", .stdVecVal li), ("out", .stdVecVal lo),
        ("c", .i32 c)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hlet := revLet vecTransformAddProg F "i" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
    (.u64 (BitVec.ofNat 64 0)) hlit
  have hiN : (BitVec.ofNat 64 0).toNat = 0 := by
    simp [BitVec.toNat_ofNat]
  have hin₁ : envLookup (envExtend
      [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
      "i" (.u64 (BitVec.ofNat 64 0))) "in" =
      some (.stdVecVal li) := by
    rw [envExtend_miss _ _ _ _
      (show ("in" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hout₁ : envLookup (envExtend
      [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
      "i" (.u64 (BitVec.ofNat 64 0))) "out" =
      some (.stdVecVal lo) := by
    rw [envExtend_miss _ _ _ _
      (show ("out" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hc₁ : envLookup (envExtend
      [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
      "i" (.u64 (BitVec.ofNat 64 0))) "c" =
      some (.i32 c) := by
    rw [envExtend_miss _ _ _ _
      (show ("c" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hi₁ : envLookup (envExtend
      [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
      "i" (.u64 (BitVec.ofNat 64 0))) "i" =
      some (.u64 (BitVec.ofNat 64 0)) :=
    envExtend_hit _ _ _
  have hloop :=
    valTransformLoop_err_short vecTransformAddProg F li.length
      (envExtend [("in", .stdVecVal li), ("out", .stdVecVal lo),
        ("c", .i32 c)] "i" (.u64 (BitVec.ofNat 64 0)))
      li lo c 0 j (BitVec.ofNat 64 0)
      hiN hli64 hlo64 hj hin₁ hout₁ hc₁ hi₁ (Nat.zero_le _)
      (by omega) (by omega) hreads hadds hmiss hfwd
  simp only [evalProgFunc, hbind, hbody]
  rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hlet,
    evalProgStmt_seq_err _ _ _ _ _ _ hloop]

/-- Value entry, checked-add error leg. -/
theorem evalProgFunc_vecTransformAdd_err_add (F : Nat)
    (li lo : List (BitVec 32)) (c : BitVec 32)
    (j : Nat) (e : Panic)
    (hli64 : li.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hj : j < li.length)
    (hF : j + 1 ≤ F)
    (hreads : ∀ p, 0 ≤ p → p ≤ j → ∃ z, lo[p]? = some z)
    (hadds : ∀ p, 0 ≤ p → p < j →
      ∃ x y, li[p]? = some x ∧ checkedAddI32 x c = .ok y)
    (hx : ∃ x, li[j]? = some x)
    (herr : ∀ x, li[j]? = some x → checkedAddI32 x c = .error e)
    (hfwd : transformAddFwd li c lo li.length 0 = .error e) :
    evalProgFunc vecTransformAddProg F vecTransformAddFunc
      [.stdVecVal li, .stdVecVal lo, .i32 c] = .error e := by
  have hbind : bindArgs vecTransformAddFunc.args
      [.stdVecVal li, .stdVecVal lo, .i32 c] =
      some [("in", .stdVecVal li), ("out", .stdVecVal lo),
        ("c", .i32 c)] := rfl
  have hbody : vecTransformAddFunc.body =
      (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq vecTransformLoop
          (.return_ (.var "out")))) := rfl
  have hlit : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("in", .stdVecVal li), ("out", .stdVecVal lo),
        ("c", .i32 c)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hlet := revLet vecTransformAddProg F "i" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
    (.u64 (BitVec.ofNat 64 0)) hlit
  have hiN : (BitVec.ofNat 64 0).toNat = 0 := by
    simp [BitVec.toNat_ofNat]
  have hin₁ : envLookup (envExtend
      [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
      "i" (.u64 (BitVec.ofNat 64 0))) "in" =
      some (.stdVecVal li) := by
    rw [envExtend_miss _ _ _ _
      (show ("in" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hout₁ : envLookup (envExtend
      [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
      "i" (.u64 (BitVec.ofNat 64 0))) "out" =
      some (.stdVecVal lo) := by
    rw [envExtend_miss _ _ _ _
      (show ("out" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hc₁ : envLookup (envExtend
      [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
      "i" (.u64 (BitVec.ofNat 64 0))) "c" =
      some (.i32 c) := by
    rw [envExtend_miss _ _ _ _
      (show ("c" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hi₁ : envLookup (envExtend
      [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
      "i" (.u64 (BitVec.ofNat 64 0))) "i" =
      some (.u64 (BitVec.ofNat 64 0)) :=
    envExtend_hit _ _ _
  have hloop :=
    valTransformLoop_err_add vecTransformAddProg F li.length
      (envExtend [("in", .stdVecVal li), ("out", .stdVecVal lo),
        ("c", .i32 c)] "i" (.u64 (BitVec.ofNat 64 0)))
      li lo c 0 j (BitVec.ofNat 64 0) e
      hiN hli64 hlo64 hj hin₁ hout₁ hc₁ hi₁ (Nat.zero_le _)
      (by omega) (by omega) hreads hadds hx herr hfwd
  simp only [evalProgFunc, hbind, hbody]
  rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hlet,
    evalProgStmt_seq_err _ _ _ _ _ _ hloop]

/-! ## Entry bridges (`memEvalProgFunc` per leg) -/

/-- Memory entry, ok leg. -/
theorem memEvalProgFunc_vecTransformAdd_ok (F : Nat)
    (li lo lo' : List (BitVec 32)) (c : BitVec 32)
    (hli64 : li.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : li.length ≤ F)
    (hread_lo : ∀ p, p < li.length → ∃ z, lo[p]? = some z)
    (hadd : ∀ p, 0 ≤ p → p < li.length →
      ∃ x y, li[p]? = some x ∧ checkedAddI32 x c = .ok y)
    (hfwd : transformAddFwd li c lo li.length 0 =
      .ok (li.length, lo')) :
    memEvalProgFunc vecTransformAddProg F vecTransformAddFunc
      [.stdVecVal li, .stdVecVal lo, .i32 c] =
      .ok (.stdVecVal lo') := by
  have hbind := bindMemArgs_vecTransformAdd li lo c
  have hbody : vecTransformAddFunc.body =
      (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq vecTransformLoop
          (.return_ (.var "out")))) := rfl
  have hmem_in : memFind
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 li.length) :: li⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ 1 =
      some ⟨1, true, (BitVec.ofNat 32 li.length) :: li⟩ :=
    memFind_cons_hit _ _ _ _ _
  have hmem_out : memFind
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 li.length) :: li⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ 0 =
      some ⟨0, true, (BitVec.ofNat 32 lo.length) :: lo⟩ := by
    rw [memFind_cons_miss _ _ _ _ _ _ (by decide : (0 : Addr) ≠ 1)]
    exact memFind_cons_hit _ _ _ _ _
  have hlay_in : layoutLookup [("in", 1, 1), ("out", 0, 0)] "in" =
      some (1, 1) := by simp [layoutLookup]
  have hlay_out : layoutLookup [("in", 1, 1), ("out", 0, 0)] "out" =
      some (0, 0) := by simp [layoutLookup]
  have hlitM : memEvalExpr
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("in", .stdVecVal li), ("out", .stdVecVal lo),
        ("c", .i32 c)]
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 li.length) :: li⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
      [("in", 1, 1), ("out", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("in", .stdVecVal li), ("out", .stdVecVal lo),
          ("c", .i32 c)] :=
    memEvalExpr_lit _ _ _ _
  have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("in", .stdVecVal li), ("out", .stdVecVal lo),
        ("c", .i32 c)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hlet := memRevLet vecTransformAddProg F "i" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
    ⟨2, [(1, ⟨1, true,
      (BitVec.ofNat 32 li.length) :: li⟩),
      (0, ⟨0, true,
      (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
    [("in", 1, 1), ("out", 0, 0)] (.u64 (BitVec.ofNat 64 0))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) hlitM hlitV
  have hiN : (BitVec.ofNat 64 0).toNat = 0 := by
    simp [BitVec.toNat_ofNat]
  have hin₁ : envLookup (envExtend
      [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
      "i" (.u64 (BitVec.ofNat 64 0))) "in" =
      some (.stdVecVal li) := by
    rw [envExtend_miss _ _ _ _
      (show ("in" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hout₁ : envLookup (envExtend
      [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
      "i" (.u64 (BitVec.ofNat 64 0))) "out" =
      some (.stdVecVal lo) := by
    rw [envExtend_miss _ _ _ _
      (show ("out" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hc₁ : envLookup (envExtend
      [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
      "i" (.u64 (BitVec.ofNat 64 0))) "c" =
      some (.i32 c) := by
    rw [envExtend_miss _ _ _ _
      (show ("c" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hi₁ : envLookup (envExtend
      [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
      "i" (.u64 (BitVec.ofNat 64 0))) "i" =
      some (.u64 (BitVec.ofNat 64 0)) :=
    envExtend_hit _ _ _
  obtain ⟨ρ', m', hloop, hout', ⟨iB', hiB', hiN'⟩, hmem_in',
      hmem_out'⟩ :=
    memTransformLoop_ok vecTransformAddProg F li.length
      (envExtend [("in", .stdVecVal li), ("out", .stdVecVal lo),
        ("c", .i32 c)] "i" (.u64 (BitVec.ofNat 64 0)))
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 li.length) :: li⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
      [("in", 1, 1), ("out", 0, 0)]
      li lo c 0 (BitVec.ofNat 64 0) lo' li.length
      1 0 1 0 _ _ (by decide) hlay_in hlay_out rfl rfl
      hiN hli64 hlo64 hin₁ hout₁ hc₁ hi₁ hmem_in hmem_out
      (Nat.zero_le _) (by omega) (by omega) hread_lo hadd hfwd
  have hret := memEvalProgStmt_return vecTransformAddProg F
    (.var "out") ρ' m' [("in", 1, 1), ("out", 0, 0)]
    (.stdVecVal lo')
    ((memEvalExpr_var _ _ _ _).trans
      (evalExpr_var_hit _ _ _ hout'))
  simp only [memEvalProgFunc, hbind, hbody]
  rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hlet,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hloop,
    hret]

/-- Memory entry, short-`out` error leg. -/
theorem memEvalProgFunc_vecTransformAdd_err_short (F : Nat)
    (li lo : List (BitVec 32)) (c : BitVec 32)
    (j : Nat)
    (hli64 : li.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hj : j < li.length)
    (hF : j + 1 ≤ F)
    (hreads : ∀ p, 0 ≤ p → p < j → ∃ z, lo[p]? = some z)
    (hadds : ∀ p, 0 ≤ p → p < j →
      ∃ x y, li[p]? = some x ∧ checkedAddI32 x c = .ok y)
    (hmiss : lo[j]? = none)
    (hfwd : transformAddFwd li c lo li.length 0 = .error .AssertFail) :
    memEvalProgFunc vecTransformAddProg F vecTransformAddFunc
      [.stdVecVal li, .stdVecVal lo, .i32 c] = .error .AssertFail := by
  have hbind := bindMemArgs_vecTransformAdd li lo c
  have hbody : vecTransformAddFunc.body =
      (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq vecTransformLoop
          (.return_ (.var "out")))) := rfl
  have hmem_in : memFind
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 li.length) :: li⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ 1 =
      some ⟨1, true, (BitVec.ofNat 32 li.length) :: li⟩ :=
    memFind_cons_hit _ _ _ _ _
  have hmem_out : memFind
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 li.length) :: li⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ 0 =
      some ⟨0, true, (BitVec.ofNat 32 lo.length) :: lo⟩ := by
    rw [memFind_cons_miss _ _ _ _ _ _ (by decide : (0 : Addr) ≠ 1)]
    exact memFind_cons_hit _ _ _ _ _
  have hlay_in : layoutLookup [("in", 1, 1), ("out", 0, 0)] "in" =
      some (1, 1) := by simp [layoutLookup]
  have hlay_out : layoutLookup [("in", 1, 1), ("out", 0, 0)] "out" =
      some (0, 0) := by simp [layoutLookup]
  have hlitM : memEvalExpr
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("in", .stdVecVal li), ("out", .stdVecVal lo),
        ("c", .i32 c)]
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 li.length) :: li⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
      [("in", 1, 1), ("out", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("in", .stdVecVal li), ("out", .stdVecVal lo),
          ("c", .i32 c)] :=
    memEvalExpr_lit _ _ _ _
  have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("in", .stdVecVal li), ("out", .stdVecVal lo),
        ("c", .i32 c)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hlet := memRevLet vecTransformAddProg F "i" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
    ⟨2, [(1, ⟨1, true,
      (BitVec.ofNat 32 li.length) :: li⟩),
      (0, ⟨0, true,
      (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
    [("in", 1, 1), ("out", 0, 0)] (.u64 (BitVec.ofNat 64 0))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) hlitM hlitV
  have hiN : (BitVec.ofNat 64 0).toNat = 0 := by
    simp [BitVec.toNat_ofNat]
  have hin₁ : envLookup (envExtend
      [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
      "i" (.u64 (BitVec.ofNat 64 0))) "in" =
      some (.stdVecVal li) := by
    rw [envExtend_miss _ _ _ _
      (show ("in" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hout₁ : envLookup (envExtend
      [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
      "i" (.u64 (BitVec.ofNat 64 0))) "out" =
      some (.stdVecVal lo) := by
    rw [envExtend_miss _ _ _ _
      (show ("out" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hc₁ : envLookup (envExtend
      [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
      "i" (.u64 (BitVec.ofNat 64 0))) "c" =
      some (.i32 c) := by
    rw [envExtend_miss _ _ _ _
      (show ("c" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hi₁ : envLookup (envExtend
      [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
      "i" (.u64 (BitVec.ofNat 64 0))) "i" =
      some (.u64 (BitVec.ofNat 64 0)) :=
    envExtend_hit _ _ _
  have hloop :=
    memTransformLoop_err_short vecTransformAddProg F li.length
      (envExtend [("in", .stdVecVal li), ("out", .stdVecVal lo),
        ("c", .i32 c)] "i" (.u64 (BitVec.ofNat 64 0)))
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 li.length) :: li⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
      [("in", 1, 1), ("out", 0, 0)]
      li lo c 0 j (BitVec.ofNat 64 0)
      1 0 1 0 _ _ (by decide) hlay_in hlay_out rfl rfl
      hiN hli64 hlo64 hj hin₁ hout₁ hc₁ hi₁ hmem_in hmem_out
      (Nat.zero_le _) (by omega) (by omega) hreads hadds hmiss hfwd
  simp only [memEvalProgFunc, hbind, hbody]
  rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hlet,
    memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hloop]

/-- Memory entry, checked-add error leg. -/
theorem memEvalProgFunc_vecTransformAdd_err_add (F : Nat)
    (li lo : List (BitVec 32)) (c : BitVec 32)
    (j : Nat) (e : Panic)
    (hli64 : li.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hj : j < li.length)
    (hF : j + 1 ≤ F)
    (hreads : ∀ p, 0 ≤ p → p ≤ j → ∃ z, lo[p]? = some z)
    (hadds : ∀ p, 0 ≤ p → p < j →
      ∃ x y, li[p]? = some x ∧ checkedAddI32 x c = .ok y)
    (hx : ∃ x, li[j]? = some x)
    (herr : ∀ x, li[j]? = some x → checkedAddI32 x c = .error e)
    (hfwd : transformAddFwd li c lo li.length 0 = .error e) :
    memEvalProgFunc vecTransformAddProg F vecTransformAddFunc
      [.stdVecVal li, .stdVecVal lo, .i32 c] = .error e := by
  have hbind := bindMemArgs_vecTransformAdd li lo c
  have hbody : vecTransformAddFunc.body =
      (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq vecTransformLoop
          (.return_ (.var "out")))) := rfl
  have hmem_in : memFind
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 li.length) :: li⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ 1 =
      some ⟨1, true, (BitVec.ofNat 32 li.length) :: li⟩ :=
    memFind_cons_hit _ _ _ _ _
  have hmem_out : memFind
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 li.length) :: li⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩ 0 =
      some ⟨0, true, (BitVec.ofNat 32 lo.length) :: lo⟩ := by
    rw [memFind_cons_miss _ _ _ _ _ _ (by decide : (0 : Addr) ≠ 1)]
    exact memFind_cons_hit _ _ _ _ _
  have hlay_in : layoutLookup [("in", 1, 1), ("out", 0, 0)] "in" =
      some (1, 1) := by simp [layoutLookup]
  have hlay_out : layoutLookup [("in", 1, 1), ("out", 0, 0)] "out" =
      some (0, 0) := by simp [layoutLookup]
  have hlitM : memEvalExpr
      (.lit (.u64 (BitVec.ofNat 64 0)))
      [("in", .stdVecVal li), ("out", .stdVecVal lo),
        ("c", .i32 c)]
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 li.length) :: li⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
      [("in", 1, 1), ("out", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("in", .stdVecVal li), ("out", .stdVecVal lo),
          ("c", .i32 c)] :=
    memEvalExpr_lit _ _ _ _
  have hlitV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("in", .stdVecVal li), ("out", .stdVecVal lo),
        ("c", .i32 c)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by simp [evalExpr, litVal]
  have hlet := memRevLet vecTransformAddProg F "i" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0)))
    [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
    ⟨2, [(1, ⟨1, true,
      (BitVec.ofNat 32 li.length) :: li⟩),
      (0, ⟨0, true,
      (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
    [("in", 1, 1), ("out", 0, 0)] (.u64 (BitVec.ofNat 64 0))
    (by intro se h; cases h) (by intro se h; cases h)
    (by intro ce h; cases h) hlitM hlitV
  have hiN : (BitVec.ofNat 64 0).toNat = 0 := by
    simp [BitVec.toNat_ofNat]
  have hin₁ : envLookup (envExtend
      [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
      "i" (.u64 (BitVec.ofNat 64 0))) "in" =
      some (.stdVecVal li) := by
    rw [envExtend_miss _ _ _ _
      (show ("in" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hout₁ : envLookup (envExtend
      [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
      "i" (.u64 (BitVec.ofNat 64 0))) "out" =
      some (.stdVecVal lo) := by
    rw [envExtend_miss _ _ _ _
      (show ("out" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hc₁ : envLookup (envExtend
      [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
      "i" (.u64 (BitVec.ofNat 64 0))) "c" =
      some (.i32 c) := by
    rw [envExtend_miss _ _ _ _
      (show ("c" : String) ≠ "i" by decide)]
    simp [envLookup]
  have hi₁ : envLookup (envExtend
      [("in", .stdVecVal li), ("out", .stdVecVal lo), ("c", .i32 c)]
      "i" (.u64 (BitVec.ofNat 64 0))) "i" =
      some (.u64 (BitVec.ofNat 64 0)) :=
    envExtend_hit _ _ _
  have hloop :=
    memTransformLoop_err_add vecTransformAddProg F li.length
      (envExtend [("in", .stdVecVal li), ("out", .stdVecVal lo),
        ("c", .i32 c)] "i" (.u64 (BitVec.ofNat 64 0)))
      ⟨2, [(1, ⟨1, true,
        (BitVec.ofNat 32 li.length) :: li⟩),
        (0, ⟨0, true,
        (BitVec.ofNat 32 lo.length) :: lo⟩)], []⟩
      [("in", 1, 1), ("out", 0, 0)]
      li lo c 0 j (BitVec.ofNat 64 0) e
      1 0 1 0 _ _ (by decide) hlay_in hlay_out rfl rfl
      hiN hli64 hlo64 hj hin₁ hout₁ hc₁ hi₁ hmem_in hmem_out
      (Nat.zero_le _) (by omega) (by omega) hreads hadds hx herr hfwd
  simp only [memEvalProgFunc, hbind, hbody]
  rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hlet,
    memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hloop]

/-! ## Transfer (`memEvalProgFunc` agrees with `evalProgFunc`) -/

/-- Transfer for `vec_transform_add`, ok leg: both layers compute
    the same words (the M2b ok contract supplies the shared forward
    equation). -/
theorem memTransferProg_vecTransformAdd_ok (F : Nat)
    (li lo : List (BitVec 32)) (c : BitVec 32)
    (hli64 : li.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hF : li.length ≤ F)
    (hread_lo : ∀ p, p < li.length → ∃ z, lo[p]? = some z)
    (hadd : ∀ p, 0 ≤ p → p < li.length →
      ∃ x y, li[p]? = some x ∧ checkedAddI32 x c = .ok y)
    (_h : oracleNoalias vecTransformAddFunc
      [.stdVecVal li, .stdVecVal lo, .i32 c]) :
    memEvalProgFunc vecTransformAddProg F vecTransformAddFunc
      [.stdVecVal li, .stdVecVal lo, .i32 c] =
      evalProgFunc vecTransformAddProg F vecTransformAddFunc
        [.stdVecVal li, .stdVecVal lo, .i32 c] := by
  obtain ⟨lo', heq, hlen', hframe', hele'⟩ :=
    transformAddFwd_ok li lo c li.length 0 (Nat.zero_le _)
      (by omega) hread_lo hadd
  rw [memEvalProgFunc_vecTransformAdd_ok F li lo lo' c hli64 hlo64 hF
    hread_lo hadd heq,
    evalProgFunc_vecTransformAdd_ok F li lo lo' c hli64 hlo64 hF
      hread_lo hadd heq]

/-- Transfer for `vec_transform_add`, short-`out` leg. -/
theorem memTransferProg_vecTransformAdd_err_short (F : Nat)
    (li lo : List (BitVec 32)) (c : BitVec 32)
    (j : Nat)
    (hli64 : li.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hj : j < li.length)
    (hF : j + 1 ≤ F)
    (hreads : ∀ p, 0 ≤ p → p < j → ∃ z, lo[p]? = some z)
    (hadds : ∀ p, 0 ≤ p → p < j →
      ∃ x y, li[p]? = some x ∧ checkedAddI32 x c = .ok y)
    (hmiss : lo[j]? = none)
    (_h : oracleNoalias vecTransformAddFunc
      [.stdVecVal li, .stdVecVal lo, .i32 c]) :
    memEvalProgFunc vecTransformAddProg F vecTransformAddFunc
      [.stdVecVal li, .stdVecVal lo, .i32 c] =
      evalProgFunc vecTransformAddProg F vecTransformAddFunc
        [.stdVecVal li, .stdVecVal lo, .i32 c] := by
  have heq : transformAddFwd li c lo li.length 0 =
      .error .AssertFail :=
    transformAddFwd_err_short li lo c li.length 0 j hj (Nat.zero_le _)
      (by omega) hreads hadds hmiss
  rw [memEvalProgFunc_vecTransformAdd_err_short F li lo c j hli64 hlo64
    hj hF hreads hadds hmiss heq,
    evalProgFunc_vecTransformAdd_err_short F li lo c j hli64 hlo64
      hj hF hreads hadds hmiss heq]

/-- Transfer for `vec_transform_add`, checked-add error leg. -/
theorem memTransferProg_vecTransformAdd_err_add (F : Nat)
    (li lo : List (BitVec 32)) (c : BitVec 32)
    (j : Nat) (e : Panic)
    (hli64 : li.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hj : j < li.length)
    (hF : j + 1 ≤ F)
    (hreads : ∀ p, 0 ≤ p → p ≤ j → ∃ z, lo[p]? = some z)
    (hadds : ∀ p, 0 ≤ p → p < j →
      ∃ x y, li[p]? = some x ∧ checkedAddI32 x c = .ok y)
    (hx : ∃ x, li[j]? = some x)
    (herr : ∀ x, li[j]? = some x → checkedAddI32 x c = .error e)
    (_h : oracleNoalias vecTransformAddFunc
      [.stdVecVal li, .stdVecVal lo, .i32 c]) :
    memEvalProgFunc vecTransformAddProg F vecTransformAddFunc
      [.stdVecVal li, .stdVecVal lo, .i32 c] =
      evalProgFunc vecTransformAddProg F vecTransformAddFunc
        [.stdVecVal li, .stdVecVal lo, .i32 c] := by
  have heq : transformAddFwd li c lo li.length 0 = .error e :=
    transformAddFwd_err_add li lo c li.length 0 j e hj (Nat.zero_le _)
      (by omega) hreads hadds hx herr
  rw [memEvalProgFunc_vecTransformAdd_err_add F li lo c j e hli64 hlo64
    hj hF hreads hadds hx herr heq,
    evalProgFunc_vecTransformAdd_err_add F li lo c j e hli64 hlo64
      hj hF hreads hadds hx herr heq]
