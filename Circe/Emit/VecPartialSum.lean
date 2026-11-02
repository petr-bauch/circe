/-
Prefix-sum scan (`std::partial_sum` idiom) over `std::vector<int>` —
the first read-after-write dependency through the vector (pillar-2
proposed goal, P2-M10).

Corpus: `tests/cpp/vec_partial_sum.cpp` →
`tests/cir/vec_partial_sum.cir` (entry
`_Z15vec_partial_sumRSt6vectorIiSaIiEE`: one `mutBorrow` vector,
`void` out; a single `cir.while` scan starting at index 1 with
one `nsw` checked add and one `u64` subtraction).

Model: the read cursor starts at 1. At step `i`, the current read
`v.at(i)` still holds the original value, while the
previous-output read `v.at(i - 1)` holds the already computed
running sum; the checked `i32` add stores the next prefix sum.
Unlike partition/remove, the scan has an overflow leg: a failed
checked add aborts with `Overflow` (the V2/transform checked-add
precedent). Entries follow the partition idiom: the non-loop legs
of the transfer are admitted, and the entry returns the rewritten
words.
-/
import Circe.Emit.VecTransformAdd

/-- Function name (Itanium mangling of a `vec_partial_sum` free
    function taking `vector<int>&`). -/
def vecPartialSumName : String :=
  "_Z15vec_partial_sumRSt6vectorIiSaIiEE"

/-- Loop body: rewrite `v[i]` as the checked sum of the current
    value and the previous output, then advance the cursor. -/
def vecPartialSumBody : CStmt :=
  (.seq (.vecSet "v" (.var "i")
          (.add (.stdVecAt "v" (.var "i"))
            (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 1))))))
    (.assign "i" (.uadd (.var "i") (.lit (.u64 1)))))

/-- Loop `while (i < n) body`, entered with `i = 1`. -/
def vecPartialSumLoop : CStmt :=
  (.while_ (.ult (.var "i") (.stdVecLen "v")) vecPartialSumBody)

/-- Whole function: `let_`-prelude binds the cursor at 1, the
    loop scans, then the rewritten vector returns. -/
def vecPartialSumFunc : Func :=
  ⟨vecPartialSumName,
   [{ name := "v", ty := stdVecObjTy, role := .mutBorrow 0 }],
   stdVecObjTy,
   (.seq (.let_ "i" (.u 64) (.lit (.u64 1)))
     (.seq vecPartialSumLoop
       (.return_ (.var "v"))))⟩

/-- Loop environment (borrowed words + `u64` cursor). -/
def mkPartialSumEnv (l : List (BitVec 32)) (i : BitVec 64) : Env :=
  [("i", .u64 i), ("v", .stdVecVal l)]

theorem mkPartialSumEnv_v (l : List (BitVec 32)) (i : BitVec 64) :
    envLookup (mkPartialSumEnv l i) "v" =
      some (.stdVecVal l) := by
  simp [mkPartialSumEnv, envLookup, show ("v" : String) ≠ "i" by decide]

theorem mkPartialSumEnv_i (l : List (BitVec 32)) (i : BitVec 64) :
    envLookup (mkPartialSumEnv l i) "i" = some (.u64 i) := by
  simp [mkPartialSumEnv, envLookup]

/-! ## Forward model (fuel-threaded, mirroring the loop) -/

/-- Loop model: fuel + current words + read cursor. Fuel 0 returns
    the state so far; the `none` arms are unreachable in-loop
    (every index is guard-justified: `i < len` from the guard and
    `i - 1 < len` from `i ≥ 1`). A checked-add failure aborts the
    whole scan. -/
def partialSumFwd :
    List (BitVec 32) → Nat → Nat →
      Result (Nat × List (BitVec 32))
  | l, 0, i => .ok (i, l)
  | l, fuel + 1, i =>
    if _ : i < l.length then
      match l[i]?, l[i - 1]? with
      | some cur, some prev =>
        match checkedAddI32 cur prev with
        | .error e => .error e
        | .ok sum => partialSumFwd (l.set i sum) fuel (i + 1)
      | _, _ => .error .AssertFail
    else .ok (i, l)

/-- Whole-function forward: the loop at measure-exact fuel from
    cursor 1, then the rewritten words. -/
def vecPartialSumFwd (l : List (BitVec 32)) : Result Value :=
  match partialSumFwd l l.length 1 with
  | .error e => .error e
  | .ok (_, l') => .ok (.stdVecVal l')

/-- Program over which the entry evaluates (no callees: the body
    is straight-line `vecSet` / `assign`). -/
abbrev vecPartialSumProg : Prog := [vecPartialSumFunc]

/-! ## Value loop (bridges `evalProgStmt` to `partialSumFwd`) -/

/-- One body iteration (value level), success branch: the two
    reads deliver the current value and the already computed
    previous output, the checked add succeeds, the prefix sum
    stores at `i`, and the cursor advances. -/
theorem valPartialSumBody_ok (prog : Prog) (F : Nat)
    (ρ : Env) (l : List (BitVec 32)) (i : Nat) (iB : BitVec 64)
    (cur prev sum : BitVec 32)
    (hiN : iB.toNat = i)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hilt : i < l.length) (hi1 : 1 ≤ i)
    (hgetC : l[i]? = some cur) (hgetP : l[i - 1]? = some prev)
    (hadd : checkedAddI32 cur prev = .ok sum) :
    ∃ ρ', evalProgStmt prog F vecPartialSumBody ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "v" = some (.stdVecVal (l.set i sum)) ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = i + 1) := by
  have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have h1lit : evalExpr (.lit (.u64 (1 : BitVec 64))) ρ =
      .ok (.u64 1) := by simp [evalExpr, litVal]
  have hsub : evalExpr (.usub (.var "i") (.lit (.u64 (1 : BitVec 64)))) ρ =
      .ok (.u64 (iB - 1)) :=
    evalExpr_u64_usub iB 1 (.var "i") ρ hiVar
  have hsubN : (iB - 1).toNat = i - 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    have hno : ¬ BitVec.usubOverflow iB 1 := by
      rw [BitVec.usubOverflow, decide_eq_true_eq, hiN, h1]
      omega
    rw [BitVec.toNat_sub_of_not_usubOverflow hno, hiN, h1]
  have hgetI : l[iB.toNat]? = some cur := by rw [hiN]; exact hgetC
  have hgetIMinus : l[(iB - 1).toNat]? = some prev := by
    rw [hsubN]; exact hgetP
  have hatC : evalExpr (.stdVecAt "v" (.var "i")) ρ = .ok (.i32 cur) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hiVar hgetI
  have hatP : evalExpr
      (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 (1 : BitVec 64)))))
      ρ = .ok (.i32 prev) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hsub hgetIMinus
  have haddV : evalExpr
      (.add (.stdVecAt "v" (.var "i"))
        (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 (1 : BitVec 64))))))
      ρ = .ok (.i32 sum) := by
    have e : evalExpr
        (.add (.stdVecAt "v" (.var "i"))
          (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 (1 : BitVec 64))))))
        ρ = (checkedAddI32 cur prev).map .i32 := by
      unfold evalExpr
      rw [hatC, hatP]
    rw [e, hadd,
      show (Except.ok sum).map Value.i32 = Except.ok (Value.i32 sum) from rfl]
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "v"
    (.stdVecVal l) (.stdVecVal (l.set iB.toNat sum)) hv
  have hstep_set := revVecSet prog F "v" (.var "i")
    (.add (.stdVecAt "v" (.var "i"))
      (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 (1 : BitVec 64))))))
    ρ iB sum l cur ρ₁ hiVar haddV hv hgetI hu₁
  have hi₁ : envLookup ρ₁ "i" = some (.u64 iB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "v" by decide) hu₁]
    exact hi
  have hiVar₁ : evalExpr (.var "i") ρ₁ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi₁
  have hevI : evalExpr (.uadd (.var "i") (.lit (.u64 1))) ρ₁ =
      .ok (.u64 (iB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      hiVar₁ (by simp [evalExpr, litVal])
  obtain ⟨ρ', hu₂⟩ := envUpdate_some_of_lookup ρ₁ "i"
    (.u64 iB) (.u64 (iB + 1)) hi₁
  have hstep_i := revAssign prog F "i"
    (.uadd (.var "i") (.lit (.u64 1))) ρ₁ (.u64 (iB + 1)) ρ' hevI hu₂
  have hsetB : l.set iB.toNat sum = l.set i sum := by rw [hiN]
  have hout' : envLookup ρ' "v" =
      some (.stdVecVal (l.set i sum)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("v" : String) ≠ "i" by decide) hu₂]
    have h := envLookup_update_hit _ _ _ _ hu₁
    rwa [hsetB] at h
  have hiN' : (iB + 1).toNat = i + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hiN]
    exact Nat.mod_eq_of_lt (by omega)
  have hi' : envLookup ρ' "i" = some (.u64 (iB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₂
  have hbody : vecPartialSumBody =
      (.seq (.vecSet "v" (.var "i")
          (.add (.stdVecAt "v" (.var "i"))
            (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 (1 : BitVec 64)))))))
        (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))) := rfl
  have heval : evalProgStmt prog F vecPartialSumBody ρ =
      .ok (ρ', .fellThrough) := by
    rw [hbody,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep_set,
      hstep_i]
  exact ⟨ρ', heval, hout', ⟨(iB + 1), hi', hiN'⟩⟩

/-- One body iteration (value level), overflow branch: the two
    reads deliver the current value and the previous output, but
    the checked add fails, so the store aborts with the same
    panic and the state is unchanged. -/
theorem valPartialSumBody_overflow (prog : Prog) (F : Nat)
    (ρ : Env) (l : List (BitVec 32)) (i : Nat) (iB : BitVec 64)
    (cur prev : BitVec 32) (err : Panic)
    (hiN : iB.toNat = i)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hilt : i < l.length) (hi1 : 1 ≤ i)
    (hgetC : l[i]? = some cur) (hgetP : l[i - 1]? = some prev)
    (herr : checkedAddI32 cur prev = .error err) :
    evalProgStmt prog F vecPartialSumBody ρ = .error err := by
  have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have h1lit : evalExpr (.lit (.u64 (1 : BitVec 64))) ρ =
      .ok (.u64 1) := by simp [evalExpr, litVal]
  have hsub : evalExpr (.usub (.var "i") (.lit (.u64 (1 : BitVec 64)))) ρ =
      .ok (.u64 (iB - 1)) :=
    evalExpr_u64_usub iB 1 (.var "i") ρ hiVar
  have hsubN : (iB - 1).toNat = i - 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    have hno : ¬ BitVec.usubOverflow iB 1 := by
      rw [BitVec.usubOverflow, decide_eq_true_eq, hiN, h1]
      omega
    rw [BitVec.toNat_sub_of_not_usubOverflow hno, hiN, h1]
  have hgetI : l[iB.toNat]? = some cur := by rw [hiN]; exact hgetC
  have hgetIMinus : l[(iB - 1).toNat]? = some prev := by
    rw [hsubN]; exact hgetP
  have hatC : evalExpr (.stdVecAt "v" (.var "i")) ρ = .ok (.i32 cur) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hiVar hgetI
  have hatP : evalExpr
      (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 (1 : BitVec 64)))))
      ρ = .ok (.i32 prev) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hv hsub hgetIMinus
  have haddV : evalExpr
      (.add (.stdVecAt "v" (.var "i"))
        (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 (1 : BitVec 64))))))
      ρ = .error err := by
    have e : evalExpr
        (.add (.stdVecAt "v" (.var "i"))
          (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 (1 : BitVec 64))))))
        ρ = (checkedAddI32 cur prev).map .i32 := by
      unfold evalExpr
      rw [hatC, hatP]
    have hmap : (checkedAddI32 cur prev).map Value.i32 = .error err := by
      rw [herr]; rfl
    rw [e, hmap]
  have hvecSetErr : evalProgStmt prog F
      (.vecSet "v" (.var "i")
        (.add (.stdVecAt "v" (.var "i"))
          (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 (1 : BitVec 64)))))))
      ρ = .error err := by
    simp only [evalProgStmt]
    cases F with
    | zero =>
      simp only [evalStmtFuel, evalStmtZero, evalStmtWith]
      rw [hiVar, haddV]
    | succ _ =>
      simp only [evalStmtFuel, evalStmtWith]
      rw [hiVar, haddV]
  have hbody : vecPartialSumBody =
      (.seq (.vecSet "v" (.var "i")
          (.add (.stdVecAt "v" (.var "i"))
            (.stdVecAt "v" (.usub (.var "i") (.lit (.u64 (1 : BitVec 64)))))))
        (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))) := rfl
  simp only [hbody, evalProgStmt, hvecSetErr]

/-- Value loop, ok leg: the scan runs to `l.length` and the words
    are the forward-model result (fuel induction threading the
    body hits; the forward equation unfolds one step per
    iteration). -/
theorem valPartialSumLoop_ok (prog : Prog) (F G : Nat)
    (ρ : Env) (l : List (BitVec 32)) (i : Nat) (iB : BitVec 64)
    (l' : List (BitVec 32)) (i' : Nat)
    (hiN : iB.toNat = i)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hle : i ≤ l.length) (hi1 : 1 ≤ i)
    (hF : l.length - i ≤ F) (hG : l.length - i ≤ G)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (hfwd : partialSumFwd l G i = .ok (i', l')) :
    ∃ ρ', evalProgStmt prog F vecPartialSumLoop ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "v" = some (.stdVecVal l') ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = i') := by
  induction F generalizing G ρ l i iB with
  | zero =>
    have him : i = l.length := by omega
    have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
    have hguardF : evalExpr (.ult (.var "i") (.stdVecLen "v")) ρ =
        .ok (.b false) := by
      have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "v") ρ iB
        (BitVec.ofNat 64 l.length)
        (evalExpr_var_hit _ _ _ hi)
        (evalExpr_stdVecLen_some _ _ _ hv)
      have hfb : (iB.ult (BitVec.ofNat 64 l.length)) = false := by
        rw [BitVec.ult_eq_decide]
        exact decide_eq_false (by omega)
      rwa [hfb] at hult
    have hexit : evalProgStmt prog 0 vecPartialSumLoop ρ =
        .ok (ρ, .fellThrough) :=
      evalProgStmt_while_false prog 0 _ _ _ hguardF
    have hpair : (i, l) = (i', l') := by
      cases G with
      | zero => simpa [partialSumFwd] using hfwd
      | succ G =>
        have hneg : ¬ i < l.length := by omega
        simpa [partialSumFwd, dite_eq_right hneg] using hfwd
    obtain ⟨rfl, rfl⟩ := hpair
    exact ⟨ρ, hexit, hv, ⟨iB, hi, hiN⟩⟩
  | succ F ih =>
    by_cases hlt : i < l.length
    · have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
      have hguardT : evalExpr (.ult (.var "i") (.stdVecLen "v")) ρ =
          .ok (.b true) := by
        have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "v") ρ iB
          (BitVec.ofNat 64 l.length)
          (evalExpr_var_hit _ _ _ hi)
          (evalExpr_stdVecLen_some _ _ _ hv)
        have htb : (iB.ult (BitVec.ofNat 64 l.length)) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true (by omega)
        rwa [htb] at hult
      obtain ⟨cur, hgetC⟩ := hread i hlt
      have hprevlt : i - 1 < l.length := by omega
      obtain ⟨prev, hgetP⟩ := hread (i - 1) hprevlt
      cir_fuel_step (F, G, l.length - (i + 1))
      match hadd : checkedAddI32 cur prev with
      | .ok sum =>
        obtain ⟨ρ₁, hbody, hout₁, ⟨iB₁, hiB₁, hiN₁⟩⟩ :=
          valPartialSumBody_ok prog F ρ l i iB cur prev sum
            hiN hl64 hv hi hlt hi1 hgetC hgetP hadd
        have hlen : (l.set i sum).length = l.length := by
          simp [List.length_set]
        have hle' : i + 1 ≤ (l.set i sum).length := by omega
        have hi1' : 1 ≤ i + 1 := by omega
        have hlo64' : (l.set i sum).length < 2 ^ 64 := by
          rw [hlen]; exact hl64
        have hF'' : (l.set i sum).length - (i + 1) ≤ F := by omega
        have hG'' : (l.set i sum).length - (i + 1) ≤ G' := by omega
        have hread' : ∀ p, p < (l.set i sum).length →
            ∃ x, (l.set i sum)[p]? = some x := by
          intro p hp
          have hplen : p < l.length := by
            have : (l.set i sum).length = l.length := by
              simp [List.length_set]
            omega
          obtain ⟨x, hx⟩ := hread p hplen
          by_cases hpi : p = i
          · rw [hpi]
            exact ⟨sum, by
              rw [List.getElem?_set_self (by omega : i < l.length)]⟩
          · exact ⟨x, by
              rw [List.getElem?_set_ne (show i ≠ p by omega)]
              exact hx⟩
        have hfwd' : partialSumFwd (l.set i sum) G' (i + 1) =
            .ok (i', l') := by
          have h := hfwd
          simpa [partialSumFwd, dite_eq_left hlt, hgetC, hgetP, hadd]
            using h
        obtain ⟨ρ', hloop, hout', ⟨iB', hiB', hiN'⟩⟩ :=
          ih (G := G') (ρ := ρ₁) (l := l.set i sum)
            (i := i + 1) (iB := iB₁)
            (hiN := hiN₁) (hl64 := hlo64')
            (hv := hout₁) (hi := hiB₁)
            (hle := hle') (hi1 := hi1')
            (hF := hF'') (hG := hG'')
            (hread := hread') (hfwd := hfwd')
        refine ⟨ρ', ?_, hout', ⟨iB', hiB', hiN'⟩⟩
        have hwhile : evalProgStmt prog (F + 1) vecPartialSumLoop ρ =
            evalProgStmt prog F vecPartialSumLoop ρ₁ := by
          cir_unfold_prog (vecPartialSumLoop, prog, F, hguardT, hbody)
        rw [hwhile]
        exact hloop
      | .error e =>
        have h := hfwd
        simp only [partialSumFwd, dite_eq_left hlt, hgetC, hgetP, hadd]
          at h
        exact absurd h (by simp)
    · have him : i = l.length := by omega
      subst him
      have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
      have hguardF : evalExpr (.ult (.var "i") (.stdVecLen "v")) ρ =
          .ok (.b false) := by
        have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "v") ρ iB
          (BitVec.ofNat 64 l.length)
          (evalExpr_var_hit _ _ _ hi)
          (evalExpr_stdVecLen_some _ _ _ hv)
        have hfb : (iB.ult (BitVec.ofNat 64 l.length)) = false := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_false (by omega)
        rwa [hfb] at hult
      have hexit : evalProgStmt prog (F + 1) vecPartialSumLoop ρ =
          .ok (ρ, .fellThrough) :=
        evalProgStmt_while_false prog (F + 1) _ _ _ hguardF
      have hpair : (l.length, l) = (i', l') := by
        cases G with
        | zero => simpa [partialSumFwd] using hfwd
        | succ G =>
          have hneg : ¬ l.length < l.length := by omega
          simpa [partialSumFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl⟩ := hpair
      exact ⟨ρ, hexit, hv, ⟨iB, hi, hiN⟩⟩

/-- Value loop, overflow leg: the first failing checked add
    aborts the whole scan (the guard-false exits are impossible
    under an error equation). -/
theorem valPartialSumLoop_overflow (prog : Prog) (F G : Nat)
    (ρ : Env) (l : List (BitVec 32)) (i : Nat) (iB : BitVec 64)
    (err : Panic)
    (hiN : iB.toNat = i)
    (hl64 : l.length < 2 ^ 64)
    (hv : envLookup ρ "v" = some (.stdVecVal l))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hle : i ≤ l.length) (hi1 : 1 ≤ i)
    (hF : l.length - i ≤ F) (hG : l.length - i ≤ G)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (hfwd : partialSumFwd l G i = .error err) :
    evalProgStmt prog F vecPartialSumLoop ρ = .error err := by
  induction F generalizing G ρ l i iB with
  | zero =>
    have him : i = l.length := by omega
    subst him
    cases G with
    | zero => exact absurd hfwd (by simp [partialSumFwd])
    | succ _ =>
      have hneg : ¬ l.length < l.length := by omega
      have hcon := hfwd
      simp only [partialSumFwd, dite_eq_right hneg] at hcon
      exact absurd hcon (by simp)
  | succ F ih =>
    by_cases hlt : i < l.length
    · have hlenN : (BitVec.ofNat 64 l.length).toNat = l.length := by
        rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hl64
      have hguardT : evalExpr (.ult (.var "i") (.stdVecLen "v")) ρ =
          .ok (.b true) := by
        have hult := evalExpr_ult_u64 (.var "i") (.stdVecLen "v") ρ iB
          (BitVec.ofNat 64 l.length)
          (evalExpr_var_hit _ _ _ hi)
          (evalExpr_stdVecLen_some _ _ _ hv)
        have htb : (iB.ult (BitVec.ofNat 64 l.length)) = true := by
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true (by omega)
        rwa [htb] at hult
      obtain ⟨cur, hgetC⟩ := hread i hlt
      have hprevlt : i - 1 < l.length := by omega
      obtain ⟨prev, hgetP⟩ := hread (i - 1) hprevlt
      cir_fuel_step (F, G, l.length - (i + 1))
      match hadd : checkedAddI32 cur prev with
      | .ok sum =>
        obtain ⟨ρ₁, hbody, hout₁, ⟨iB₁, hiB₁, hiN₁⟩⟩ :=
          valPartialSumBody_ok prog F ρ l i iB cur prev sum
            hiN hl64 hv hi hlt hi1 hgetC hgetP hadd
        have hlen : (l.set i sum).length = l.length := by
          simp [List.length_set]
        have hle' : i + 1 ≤ (l.set i sum).length := by omega
        have hi1' : 1 ≤ i + 1 := by omega
        have hlo64' : (l.set i sum).length < 2 ^ 64 := by
          rw [hlen]; exact hl64
        have hF'' : (l.set i sum).length - (i + 1) ≤ F := by omega
        have hG'' : (l.set i sum).length - (i + 1) ≤ G' := by omega
        have hread' : ∀ p, p < (l.set i sum).length →
            ∃ x, (l.set i sum)[p]? = some x := by
          intro p hp
          have hplen : p < l.length := by
            have : (l.set i sum).length = l.length := by
              simp [List.length_set]
            omega
          obtain ⟨x, hx⟩ := hread p hplen
          by_cases hpi : p = i
          · rw [hpi]
            exact ⟨sum, by
              rw [List.getElem?_set_self (by omega : i < l.length)]⟩
          · exact ⟨x, by
              rw [List.getElem?_set_ne (show i ≠ p by omega)]
              exact hx⟩
        have hfwd' : partialSumFwd (l.set i sum) G' (i + 1) =
            .error err := by
          have h := hfwd
          simpa [partialSumFwd, dite_eq_left hlt, hgetC, hgetP, hadd]
            using h
        have hloop : evalProgStmt prog F vecPartialSumLoop ρ₁ =
            .error err :=
          ih (G := G') (ρ := ρ₁) (l := l.set i sum)
            (i := i + 1) (iB := iB₁)
            (hiN := hiN₁) (hl64 := hlo64')
            (hv := hout₁) (hi := hiB₁)
            (hle := hle') (hi1 := hi1')
            (hF := hF'') (hG := hG'')
            (hread := hread') (hfwd := hfwd')
        have hwhile : evalProgStmt prog (F + 1) vecPartialSumLoop ρ =
            .error err := by
          cir_unfold_prog (vecPartialSumLoop, prog, F, hguardT, hbody)
          exact hloop
        exact hwhile
      | .error e =>
        have heq : e = err := by
          have h := hfwd
          simpa [partialSumFwd, dite_eq_left hlt, hgetC, hgetP, hadd]
            using h
        have hbody :=
          valPartialSumBody_overflow prog F ρ l i iB cur prev e
            hiN hl64 hv hi hlt hi1 hgetC hgetP hadd
        have hwhile : evalProgStmt prog (F + 1) vecPartialSumLoop ρ =
            .error e := by
          have hloop : vecPartialSumLoop =
              (.while_ (.ult (.var "i") (.stdVecLen "v"))
                vecPartialSumBody) := rfl
          rw [hloop, evalProgStmt_while_true prog F _ _ _ hguardT,
            hbody]
        rw [heq] at hwhile
        exact hwhile
    · have him : i = l.length := by omega
      subst him
      cases G with
      | zero => exact absurd hfwd (by simp [partialSumFwd])
      | succ _ =>
        have hneg : ¬ l.length < l.length := by omega
        have hcon := hfwd
        simp only [partialSumFwd, dite_eq_right hneg] at hcon
        exact absurd hcon (by simp)
