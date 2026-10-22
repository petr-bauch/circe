/-
M2 out-of-place checked transform over `std::vector<int>`.

Corpus: `tests/cpp/vec_transform_add.cpp` →
`tests/cir/vec_transform_add.cir` (entry
`_Z17vec_transform_addRKSt6vectorIiSaIiEERS1_i`: one `sharedBorrow`
input + one `mutBorrow` output pre-sized by the caller + one owned
`i32` constant, `void` out; a single `cir.while` loop).

Model (the `vecAt`/`vecAtSet` fusion precedents): the const `at()`
read fuses into the pure read (`stdVecAt`); the write carries its
own `if i < len` / `fail` (short `out` aborts loudly, the
`vec_at_set` miss precedent). The `nsw` `cir.add` on `s32` maps to
the checked `.add` (overflow is loud); the `u64` counter bump is the
plain `.uadd` (exact below `2 ^ 64` by the length bound, the
`bv64_succ_toNat` idiom).
-/
import Circe.Emit.VecAtSet
import Circe.Emit.VecReverse

/-- Function name (Itanium mangling of a `vec_transform_add` free
    function taking `const vector<int>&` + `vector<int>&` + `int`,
    returning `void`). -/
def vecTransformAddName : String :=
  "_Z17vec_transform_addRKSt6vectorIiSaIiEERS1_i"

/-- Loop body: guarded store of `in[i] + c`, advance. -/
def vecTransformBody : CStmt :=
  (.seq (.if_ (.ult (.var "i") (.stdVecLen "out"))
            (.vecSet "out" (.var "i")
              (.add (.stdVecAt "in" (.var "i")) (.var "c")))
            .fail)
    (.assign "i" (.uadd (.var "i") (.lit (.u64 1)))))

/-- Loop `while (i < n) body`. -/
def vecTransformLoop : CStmt :=
  (.while_ (.ult (.var "i") (.stdVecLen "in")) vecTransformBody)

/-- Whole function: `let_`-prelude binds `i`, the loop, then the
    updated `out` words return (`xor_n` out-param idiom). -/
def vecTransformAddFunc : Func :=
  ⟨vecTransformAddName,
   [{ name := "in", ty := stdVecObjTy, role := .sharedBorrow },
    { name := "out", ty := stdVecObjTy, role := .mutBorrow 0 },
    { name := "c", ty := .i 32, role := .owned }],
   stdVecObjTy,
   (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
     (.seq vecTransformLoop
       (.return_ (.var "out"))))⟩

/-- Loop environment (borrowed words + owned constant + `u64` index),
    in prelude `let_` cons order (`i` bound over
    `[in, out, c]`, so the entry bridge is `rfl`). -/
def mkTransformEnv (li lo : List (BitVec 32)) (c : BitVec 32)
    (i : BitVec 64) : Env :=
  [("i", .u64 i), ("c", .i32 c),
   ("in", .stdVecVal li), ("out", .stdVecVal lo)]

theorem mkTransformEnv_in (li lo : List (BitVec 32)) (c : BitVec 32)
    (i : BitVec 64) :
    envLookup (mkTransformEnv li lo c i) "in" =
      some (.stdVecVal li) := by
  simp [mkTransformEnv, envLookup, show ("in" : String) ≠ "i" by decide,
    show ("in" : String) ≠ "c" by decide]

theorem mkTransformEnv_out (li lo : List (BitVec 32)) (c : BitVec 32)
    (i : BitVec 64) :
    envLookup (mkTransformEnv li lo c i) "out" =
      some (.stdVecVal lo) := by
  simp [mkTransformEnv, envLookup, show ("out" : String) ≠ "i" by decide,
    show ("out" : String) ≠ "c" by decide,
    show ("out" : String) ≠ "in" by decide]

theorem mkTransformEnv_c (li lo : List (BitVec 32)) (c : BitVec 32)
    (i : BitVec 64) :
    envLookup (mkTransformEnv li lo c i) "c" = some (.i32 c) := by
  simp [mkTransformEnv, envLookup, show ("c" : String) ≠ "i" by decide]

theorem mkTransformEnv_i (li lo : List (BitVec 32)) (c : BitVec 32)
    (i : BitVec 64) :
    envLookup (mkTransformEnv li lo c i) "i" = some (.u64 i) := by
  simp [mkTransformEnv, envLookup]

/-! ## Forward model (fuel-threaded, mirroring the loop) -/

/-- Loop model: fuel + current `out` words + index. Fuel 0 returns
    the words so far (no more progress — the V1 miss-default idiom);
    short `out` aborts loudly; the checked add propagates. -/
def transformAddFwd (li : List (BitVec 32)) (c : BitVec 32) :
    List (BitVec 32) → Nat → Nat → Result (Nat × List (BitVec 32))
  | lo, 0, i => .ok (i, lo)
  | lo, fuel + 1, i =>
    if _ : i < li.length then
      match lo[i]? with
      | none => .error .AssertFail
      | some _ =>
        match li[i]? with
        | some x =>
          match checkedAddI32 x c with
          | .error e => .error e
          | .ok y => transformAddFwd li c (lo.set i y) fuel (i + 1)
        | none => .error .AssertFail
    else .ok (i, lo)

/-- Whole-function forward: the loop at measure-exact fuel, then the
    words. -/
def vecTransformAddFwd (li lo : List (BitVec 32)) (c : BitVec 32) :
    Result Value :=
  match transformAddFwd li c lo li.length 0 with
  | .error e => .error e
  | .ok (_, lo') => .ok (.stdVecVal lo')

/-- Program over which the entry evaluates (no callees: the body is
    straight-line `if` / `vecSet` / `assign`). -/
abbrev vecTransformAddProg : Prog := [vecTransformAddFunc]

/-! ## M2c: value loop (bridges `evalProgStmt` to `transformAddFwd`) -/

/-- A successful read pins the index below the length (the M2b
    `hread_lo'` idiom as a first-order helper: third use). -/
theorem transformRead_lt (l : List (BitVec 32)) (i : Nat)
    (z : BitVec 32) (h : l[i]? = some z) : i < l.length := by
  by_cases hl : i < l.length
  · exact hl
  · have hle : l.length ≤ i := by omega
    have hnone : l[i]? = none := List.getElem?_eq_none hle
    rw [hnone] at h
    simp at h

/-- One body iteration (value level), ok step: the `out` guard reads,
    the checked add succeeds, the store and bump thread. -/
theorem valTransformBody_ok (prog : Prog) (F : Nat)
    (ρ : Env) (li lo : List (BitVec 32)) (c : BitVec 32)
    (i : Nat) (iB : BitVec 64) (x y z : BitVec 32)
    (hiN : iB.toNat = i)
    (hli64 : li.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hin : envLookup ρ "in" = some (.stdVecVal li))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hc : envLookup ρ "c" = some (.i32 c))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hilt : i < li.length)
    (hz : lo[i]? = some z)
    (hx : li[i]? = some x)
    (hy : checkedAddI32 x c = .ok y) :
    ∃ ρ', evalProgStmt prog F vecTransformBody ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "out" = some (.stdVecVal (lo.set i y)) ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = i + 1) ∧
      envLookup ρ' "in" = some (.stdVecVal li) ∧
      envLookup ρ' "c" = some (.i32 c) := by
  have hblt : i < lo.length := transformRead_lt lo i z hz
  have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have hoLen : evalExpr (.stdVecLen "out") ρ =
      .ok (.u64 (BitVec.ofNat 64 lo.length)) :=
    evalExpr_stdVecLen_some _ _ _ hout
  have hlenN : (BitVec.ofNat 64 lo.length).toNat = lo.length := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlo64
  have hguardT : evalExpr (.ult (.var "i") (.stdVecLen "out")) ρ =
      .ok (.b true) := by
    have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "out") ρ iB
      (BitVec.ofNat 64 lo.length) hiVar hoLen
    have htb : (iB.ult (BitVec.ofNat 64 lo.length)) = true := by
      rw [BitVec.ult_eq_decide]
      exact decide_eq_true (by omega)
    rwa [htb] at hult
  have hgetB : lo[iB.toNat]? = some z := by rw [hiN]; exact hz
  have hgetA : li[iB.toNat]? = some x := by rw [hiN]; exact hx
  have hat : evalExpr (.stdVecAt "in" (.var "i")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hin hiVar hgetA
  have hcV : evalExpr (.var "c") ρ = .ok (.i32 c) :=
    evalExpr_var_hit _ _ _ hc
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
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "out"
    (.stdVecVal lo) (.stdVecVal (lo.set iB.toNat y)) hout
  have hstep_set := revVecSet prog F "out" (.var "i")
    (.add (.stdVecAt "in" (.var "i")) (.var "c")) ρ iB y lo z ρ₁
    hiVar haddV hout hgetB hu₁
  have hi₁ : envLookup ρ₁ "i" = some (.u64 iB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "out" by decide) hu₁]
    exact hi
  have hiVar₁ : evalExpr (.var "i") ρ₁ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi₁
  have hevU : evalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ₁ =
      .ok (.u64 (iB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hiVar₁ (by simp [evalExpr, litVal])
  obtain ⟨ρ', hu₂⟩ := envUpdate_some_of_lookup ρ₁ "i"
    (.u64 iB) (.u64 (iB + 1)) hi₁
  have hstep_i := revAssign prog F "i"
    (.uadd (.var "i") (.lit (.u64 1))) ρ₁ (.u64 (iB + 1)) ρ' hevU hu₂
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
  have hin₁ : envLookup ρ₁ "in" = some (.stdVecVal li) := by
    have h := envLookup_update_miss ρ "in" "out" _ ρ₁
      (show ("in" : String) ≠ "out" by decide) hu₁
    rw [h]; exact hin
  have hc₁ : envLookup ρ₁ "c" = some (.i32 c) := by
    have h := envLookup_update_miss ρ "c" "out" _ ρ₁
      (show ("c" : String) ≠ "out" by decide) hu₁
    rw [h]; exact hc
  have hin' : envLookup ρ' "in" = some (.stdVecVal li) := by
    have h := envLookup_update_miss ρ₁ "in" "i" _ ρ'
      (show ("in" : String) ≠ "i" by decide) hu₂
    rw [h]; exact hin₁
  have hc' : envLookup ρ' "c" = some (.i32 c) := by
    have h := envLookup_update_miss ρ₁ "c" "i" _ ρ'
      (show ("c" : String) ≠ "i" by decide) hu₂
    rw [h]; exact hc₁
  have hi' : envLookup ρ' "i" = some (.u64 (iB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₂
  have hiN' : (iB + 1).toNat = i + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hiN]
    exact Nat.mod_eq_of_lt (by omega)
  have hbody : vecTransformBody =
      (.seq (.if_ (.ult (.var "i") (.stdVecLen "out"))
        (.vecSet "out" (.var "i")
          (.add (.stdVecAt "in" (.var "i")) (.var "c")))
        .fail)
        (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))) := rfl
  have heval : evalProgStmt prog F vecTransformBody ρ =
      .ok (ρ', .fellThrough) := by
    rw [hbody,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _
        ((evalProgStmt_if_true _ _ _ _ _ _ hguardT).trans hstep_set),
      hstep_i]
  exact ⟨ρ', heval, hout', ⟨(iB + 1), hi', hiN'⟩, hin', hc'⟩

/-- Value loop, ok leg: the loop runs to `li.length` and the `out`
    words are the forward-model result (fuel induction threading the
    body hit; the forward equation unfolds one step per iteration). -/
theorem valTransformLoop_ok (prog : Prog) (F G : Nat)
    (ρ : Env) (li lo : List (BitVec 32)) (c : BitVec 32)
    (i : Nat) (iB : BitVec 64) (lo' : List (BitVec 32)) (i' : Nat)
    (hiN : iB.toNat = i)
    (hli64 : li.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hin : envLookup ρ "in" = some (.stdVecVal li))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hc : envLookup ρ "c" = some (.i32 c))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hle : i ≤ li.length)
    (hF : li.length - i ≤ F) (hG : li.length - i ≤ G)
    (hread_lo : ∀ p, p < li.length → ∃ z, lo[p]? = some z)
    (hadd : ∀ p, i ≤ p → p < li.length →
      ∃ x y, li[p]? = some x ∧ checkedAddI32 x c = .ok y)
    (hfwd : transformAddFwd li c lo G i = .ok (i', lo')) :
    ∃ ρ', evalProgStmt prog F vecTransformLoop ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "out" = some (.stdVecVal lo') ∧
      ∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = i' := by
  induction F generalizing G ρ lo i iB with
  | zero =>
    have him : i = li.length := by omega
    have hlenN : (BitVec.ofNat 64 li.length).toNat = li.length := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hli64
    have hguardF : evalExpr (.ult (.var "i") (.stdVecLen "in")) ρ =
        .ok (.b false) := by
      have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "in") ρ iB
        (BitVec.ofNat 64 li.length)
        (evalExpr_var_hit _ _ _ hi)
        (evalExpr_stdVecLen_some _ _ _ hin)
      have hfb : (iB.ult (BitVec.ofNat 64 li.length)) = false := by
        rw [BitVec.ult_eq_decide]
        exact decide_eq_false (by omega)
      rwa [hfb] at hult
    have hexit : evalProgStmt prog 0 vecTransformLoop ρ =
        .ok (ρ, .fellThrough) := by
      simp only [vecTransformLoop,
        evalProgStmt_while_false prog 0 _ _ _ hguardF]
    have hpair : (i, lo) = (i', lo') := by
      cases G with
      | zero => simpa [transformAddFwd] using hfwd
      | succ G =>
        have hneg : ¬ i < li.length := by omega
        simpa [transformAddFwd, dite_eq_right hneg] using hfwd
    obtain ⟨rfl, rfl⟩ := hpair
    exact ⟨ρ, hexit, hout, iB, hi, hiN⟩
  | succ F ih =>
    by_cases hlt : i < li.length
    · have hlenN : (BitVec.ofNat 64 li.length).toNat = li.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hli64
      have hguardT : evalExpr (.ult (.var "i") (.stdVecLen "in")) ρ =
          .ok (.b true) := by
        have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "in") ρ iB
          (BitVec.ofNat 64 li.length)
          (evalExpr_var_hit _ _ _ hi)
          (evalExpr_stdVecLen_some _ _ _ hin)
        have htb : (iB.ult (BitVec.ofNat 64 li.length)) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true (by omega)
        rwa [htb] at hult
      obtain ⟨z, hz⟩ := hread_lo i hlt
      obtain ⟨x, y, hx, hy⟩ := hadd i (Nat.le_refl _) hlt
      cir_fuel_step (F, G, li.length - (i + 1))
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
      obtain ⟨ρ₁, hbody, hout₁, ⟨iB₁, hiB₁, hiN₁⟩, hin₁, hc₁⟩ :=
        valTransformBody_ok prog F ρ li lo c i iB x y z
          hiN hli64 hlo64 hin hout hc hi hlt hz hx hy
      have hfwd' : transformAddFwd li c (lo.set i y) G' (i + 1) =
          .ok (i', lo') := by
        have h := hfwd
        simp only [transformAddFwd, dite_eq_left hlt, hz, hx, hy] at h
        exact h
      obtain ⟨ρ', hloop, hout', iB', hiB', hiN'⟩ :=
        ih (G := G') (ρ := ρ₁) (lo := lo.set i y) (i := i + 1) (iB := iB₁)
          (hiN := hiN₁) (hlo64 := hlo64')
          (hin := hin₁) (hout := hout₁) (hc := hc₁) (hi := hiB₁)
          (hle := by omega) (hF := hF') (hG := hG')
          (hread_lo := hread_lo') (hadd := hadd') (hfwd := hfwd')
      refine ⟨ρ', ?_, hout', iB', hiB', hiN'⟩
      have hwhile : evalProgStmt prog (F + 1) vecTransformLoop ρ =
          evalProgStmt prog F vecTransformLoop ρ₁ := by
        cir_unfold_prog (vecTransformLoop, prog, F, hguardT, hbody)
      rw [hwhile]
      exact hloop
    · have him : i = li.length := by omega
      have hlenN : (BitVec.ofNat 64 li.length).toNat = li.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hli64
      have hguardF : evalExpr (.ult (.var "i") (.stdVecLen "in")) ρ =
          .ok (.b false) := by
        have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "in") ρ iB
          (BitVec.ofNat 64 li.length)
          (evalExpr_var_hit _ _ _ hi)
          (evalExpr_stdVecLen_some _ _ _ hin)
        have hfb : (iB.ult (BitVec.ofNat 64 li.length)) = false := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_false (by omega)
        rwa [hfb] at hult
      have hexit : evalProgStmt prog (F + 1) vecTransformLoop ρ =
          .ok (ρ, .fellThrough) :=
        evalProgStmt_while_false prog (F + 1) _ _ _ hguardF
      have hpair : (i, lo) = (i', lo') := by
        cases G with
        | zero => simpa [transformAddFwd] using hfwd
        | succ G =>
          have hneg : ¬ i < li.length := by omega
          simpa [transformAddFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl⟩ := hpair
      exact ⟨ρ, hexit, hout, iB, hi, hiN⟩

/-- Value loop, short-`out` error leg: the first missing write aborts
    loudly (fuel induction; the forward equation threads). -/
theorem valTransformLoop_err_short (prog : Prog) (F G : Nat)
    (ρ : Env) (li lo : List (BitVec 32)) (c : BitVec 32)
    (i j : Nat) (iB : BitVec 64)
    (hiN : iB.toNat = i)
    (hli64 : li.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hj : j < li.length)
    (hin : envLookup ρ "in" = some (.stdVecVal li))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hc : envLookup ρ "c" = some (.i32 c))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hle : i ≤ j) (hF : j - i + 1 ≤ F) (hG : j - i + 1 ≤ G)
    (hreads : ∀ p, i ≤ p → p < j → ∃ z, lo[p]? = some z)
    (hadds : ∀ p, i ≤ p → p < j →
      ∃ x y, li[p]? = some x ∧ checkedAddI32 x c = .ok y)
    (hmiss : lo[j]? = none)
    (hfwd : transformAddFwd li c lo G i = .error .AssertFail) :
    evalProgStmt prog F vecTransformLoop ρ = .error .AssertFail := by
  induction F generalizing G ρ lo i iB with
  | zero => exact (by omega : False).elim
  | succ F ih =>
    by_cases hij : i = j
    · subst hij
      have hlenN : (BitVec.ofNat 64 lo.length).toNat = lo.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlo64
      have hnl : ¬ i < lo.length := by
        intro h
        have hsome : lo[i]? = some lo[i] := List.getElem?_eq_getElem h
        rw [hsome] at hmiss
        simp at hmiss
      have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
        evalExpr_var_hit _ _ _ hi
      have hguardF : evalExpr
          (.ult (.var "i") (.stdVecLen "out")) ρ = .ok (.b false) := by
        have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "out") ρ
          iB (BitVec.ofNat 64 lo.length) hiVar
          (evalExpr_stdVecLen_some _ _ _ hout)
        have hfb : (iB.ult (BitVec.ofNat 64 lo.length)) = false := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_false (by omega)
        rwa [hfb] at hult
      have hlenIN : (BitVec.ofNat 64 li.length).toNat = li.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hli64
      have hguardT : evalExpr (.ult (.var "i") (.stdVecLen "in")) ρ =
          .ok (.b true) := by
        have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "in") ρ
          iB (BitVec.ofNat 64 li.length) hiVar
          (evalExpr_stdVecLen_some _ _ _ hin)
        have htb : (iB.ult (BitVec.ofNat 64 li.length)) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true (by omega)
        rwa [htb] at hult
      have hfail : evalProgStmt prog F .fail ρ = .error .AssertFail := by
        simpa [evalProgStmt] using (evalStmtFuel_fail F ρ)
      have hif : evalProgStmt prog F
          (.if_ (.ult (.var "i") (.stdVecLen "out"))
            (.vecSet "out" (.var "i")
              (.add (.stdVecAt "in" (.var "i")) (.var "c")))
            .fail) ρ = .error .AssertFail :=
        (evalProgStmt_if_false _ _ _ _ _ _ hguardF).trans hfail
      have hbody : vecTransformBody =
          (.seq (.if_ (.ult (.var "i") (.stdVecLen "out"))
            (.vecSet "out" (.var "i")
              (.add (.stdVecAt "in" (.var "i")) (.var "c")))
            .fail)
            (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))) := rfl
      have hbodyval : evalProgStmt prog F vecTransformBody ρ =
          .error .AssertFail := by
        rw [hbody]
        exact evalProgStmt_seq_err _ _ _ _ _ _ hif
      cir_unfold_prog (vecTransformLoop, prog, F, hguardT, hbodyval)
    · have hlt : i < j := by omega
      have hlt_len : i < li.length := by omega
      have hlenN : (BitVec.ofNat 64 li.length).toNat = li.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hli64
      have hguardT : evalExpr (.ult (.var "i") (.stdVecLen "in")) ρ =
          .ok (.b true) := by
        have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "in") ρ
          iB (BitVec.ofNat 64 li.length)
          (evalExpr_var_hit _ _ _ hi)
          (evalExpr_stdVecLen_some _ _ _ hin)
        have htb : (iB.ult (BitVec.ofNat 64 li.length)) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true (by omega)
        rwa [htb] at hult
      obtain ⟨z, hz⟩ := hreads i (Nat.le_refl _) hlt
      obtain ⟨x, y, hx, hy⟩ := hadds i (Nat.le_refl _) hlt
      cir_fuel_step (F, G, j - (i + 1) + 1)
      have hlo64' : (lo.set i y).length < 2 ^ 64 := by
        rw [List.length_set]; exact hlo64
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
      obtain ⟨ρ₁, hbodyval, hout₁, ⟨iB₁, hiB₁, hiN₁⟩, hin₁, hc₁⟩ :=
        valTransformBody_ok prog F ρ li lo c i iB x y z
          hiN hli64 hlo64 hin hout hc hi hlt_len hz hx hy
      have hfwd' : transformAddFwd li c (lo.set i y) G' (i + 1) =
          .error .AssertFail := by
        have h := hfwd
        simp only [transformAddFwd, dite_eq_left hlt_len, hz, hx, hy] at h
        exact h
      have hmiss' : (lo.set i y)[j]? = none := by
        rw [List.getElem?_set_ne (show i ≠ j by omega)]
        exact hmiss
      have hloop :=
        ih (G := G') (ρ := ρ₁) (lo := lo.set i y) (i := i + 1) (iB := iB₁)
          (hiN := hiN₁) (hlo64 := hlo64')
          (hin := hin₁) (hout := hout₁) (hc := hc₁) (hi := hiB₁)
          (hle := by omega) (hF := hF') (hG := hG')
          (hreads := hreads') (hadds := hadds') (hmiss := hmiss')
          (hfwd := hfwd')
      have hwhile : evalProgStmt prog (F + 1) vecTransformLoop ρ =
          evalProgStmt prog F vecTransformLoop ρ₁ := by
        cir_unfold_prog (vecTransformLoop, prog, F, hguardT, hbodyval)
      rw [hwhile]
      exact hloop

/-- Value loop, checked-add error leg: the first failing add
    propagates (fuel induction; the forward equation threads). -/
theorem valTransformLoop_err_add (prog : Prog) (F G : Nat)
    (ρ : Env) (li lo : List (BitVec 32)) (c : BitVec 32)
    (i j : Nat) (iB : BitVec 64) (e : Panic)
    (hiN : iB.toNat = i)
    (hli64 : li.length < 2 ^ 64) (hlo64 : lo.length < 2 ^ 64)
    (hj : j < li.length)
    (hin : envLookup ρ "in" = some (.stdVecVal li))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hc : envLookup ρ "c" = some (.i32 c))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hle : i ≤ j) (hF : j - i + 1 ≤ F) (hG : j - i + 1 ≤ G)
    (hreads : ∀ p, i ≤ p → p ≤ j → ∃ z, lo[p]? = some z)
    (hadds : ∀ p, i ≤ p → p < j →
      ∃ x y, li[p]? = some x ∧ checkedAddI32 x c = .ok y)
    (hx : ∃ x, li[j]? = some x)
    (herr : ∀ x, li[j]? = some x → checkedAddI32 x c = .error e)
    (hfwd : transformAddFwd li c lo G i = .error e) :
    evalProgStmt prog F vecTransformLoop ρ = .error e := by
  induction F generalizing G ρ lo i iB with
  | zero => exact (by omega : False).elim
  | succ F ih =>
    by_cases hij : i = j
    · subst hij
      obtain ⟨x, hx'⟩ := hx
      obtain ⟨z, hz⟩ := hreads i (Nat.le_refl _) (Nat.le_refl _)
      have hblt : i < lo.length := transformRead_lt lo i z hz
      have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
        evalExpr_var_hit _ _ _ hi
      have hlenN : (BitVec.ofNat 64 lo.length).toNat = lo.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hlo64
      have hguardT : evalExpr
          (.ult (.var "i") (.stdVecLen "out")) ρ = .ok (.b true) := by
        have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "out") ρ
          iB (BitVec.ofNat 64 lo.length) hiVar
          (evalExpr_stdVecLen_some _ _ _ hout)
        have htb : (iB.ult (BitVec.ofNat 64 lo.length)) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true (by omega)
        rwa [htb] at hult
      have hlenIN : (BitVec.ofNat 64 li.length).toNat = li.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hli64
      have hguardLoop : evalExpr (.ult (.var "i") (.stdVecLen "in")) ρ =
          .ok (.b true) := by
        have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "in") ρ
          iB (BitVec.ofNat 64 li.length) hiVar
          (evalExpr_stdVecLen_some _ _ _ hin)
        have htb : (iB.ult (BitVec.ofNat 64 li.length)) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true (by omega)
        rwa [htb] at hult
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
      have hset : evalProgStmt prog F
          (.vecSet "out" (.var "i")
            (.add (.stdVecAt "in" (.var "i")) (.var "c"))) ρ =
            .error e := by
        have hfuel : evalStmtFuel F
            (.vecSet "out" (.var "i")
              (.add (.stdVecAt "in" (.var "i")) (.var "c"))) ρ =
            .error e := by
          cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith,
            hiVar, haddV_err]
        simpa [evalProgStmt] using hfuel
      have hif : evalProgStmt prog F
          (.if_ (.ult (.var "i") (.stdVecLen "out"))
            (.vecSet "out" (.var "i")
              (.add (.stdVecAt "in" (.var "i")) (.var "c")))
            .fail) ρ = .error e :=
        (evalProgStmt_if_true _ _ _ _ _ _ hguardT).trans hset
      have hbody : vecTransformBody =
          (.seq (.if_ (.ult (.var "i") (.stdVecLen "out"))
            (.vecSet "out" (.var "i")
              (.add (.stdVecAt "in" (.var "i")) (.var "c")))
            .fail)
            (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))) := rfl
      have hbodyval : evalProgStmt prog F vecTransformBody ρ =
          .error e := by
        rw [hbody]
        exact evalProgStmt_seq_err _ _ _ _ _ _ hif
      cir_unfold_prog (vecTransformLoop, prog, F, hguardLoop, hbodyval)
    · have hlt : i < j := by omega
      have hlt_len : i < li.length := by omega
      have hlenN : (BitVec.ofNat 64 li.length).toNat = li.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hli64
      have hguardT : evalExpr (.ult (.var "i") (.stdVecLen "in")) ρ =
          .ok (.b true) := by
        have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "in") ρ
          iB (BitVec.ofNat 64 li.length)
          (evalExpr_var_hit _ _ _ hi)
          (evalExpr_stdVecLen_some _ _ _ hin)
        have htb : (iB.ult (BitVec.ofNat 64 li.length)) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true (by omega)
        rwa [htb] at hult
      obtain ⟨z, hz⟩ := hreads i (Nat.le_refl _) (by omega)
      obtain ⟨x, y, hx, hy⟩ := hadds i (Nat.le_refl _) hlt
      cir_fuel_step (F, G, j - (i + 1) + 1)
      have hlo64' : (lo.set i y).length < 2 ^ 64 := by
        rw [List.length_set]; exact hlo64
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
      obtain ⟨ρ₁, hbodyval, hout₁, ⟨iB₁, hiB₁, hiN₁⟩, hin₁, hc₁⟩ :=
        valTransformBody_ok prog F ρ li lo c i iB x y z
          hiN hli64 hlo64 hin hout hc hi hlt_len hz hx hy
      have hfwd' : transformAddFwd li c (lo.set i y) G' (i + 1) =
          .error e := by
        have h := hfwd
        simp only [transformAddFwd, dite_eq_left hlt_len, hz, hx, hy] at h
        exact h
      have hloop :=
        ih (G := G') (ρ := ρ₁) (lo := lo.set i y) (i := i + 1) (iB := iB₁)
          (hiN := hiN₁) (hlo64 := hlo64')
          (hin := hin₁) (hout := hout₁) (hc := hc₁) (hi := hiB₁)
          (hle := by omega) (hF := hF') (hG := hG')
          (hreads := hreads') (hadds := hadds') (hfwd := hfwd')
      have hwhile : evalProgStmt prog (F + 1) vecTransformLoop ρ =
          evalProgStmt prog F vecTransformLoop ρ₁ := by
        cir_unfold_prog (vecTransformLoop, prog, F, hguardT, hbodyval)
      rw [hwhile]
      exact hloop
