import Circe.Emit.VecRead

/-! P2-M19: first-index-of-difference over two read-only
`std::vector<int>` (`std::mismatch` idiom) — the first dual-read
query returning a position. Single cursor `i` walks both
inputs under the short-circuit `&&` guard; the first unequal
pair returns `i`, exhaustion returns the shorter length. No
writes, no records, no loud leg on valid input. -/

/-- Mismatch entry name (mangled, as captured). -/
def vecMismatchName : String :=
  "_Z12vec_mismatchRKSt6vectorIiSaIiEES3_"

/-- Loop guard: `i < a.size() && i < b.size()`, lowered by CIRGen
    as a short-circuit `cir.ternary` over the two `ult`s. -/
def mismatchGuard : CExpr :=
  .tif (.ult (.var "i") (.stdVecLen "a"))
    (.ult (.var "i") (.stdVecLen "b"))
    (.lit (.b false))

/-- Loop body: unequal heads return the position at once;
    otherwise the single cursor bumps. -/
def vecMismatchBody : CStmt :=
  (.seq (.if_ (.une (.stdVecAt "a" (.var "i"))
                  (.stdVecAt "b" (.var "i")))
            (.return_ (.var "i"))
            .skip)
    (.assign "i" (.uadd (.var "i")
      (.lit (.u64 (BitVec.ofNat 64 1))))))

/-- The mismatch scan loop. -/
def vecMismatchLoop : CStmt :=
  .while_ mismatchGuard vecMismatchBody

/-- Whole function: cursor from zero, tail returns `i`. -/
def vecMismatchFunc : Func :=
  ⟨vecMismatchName,
   [{ name := "a", ty := stdVecObjTy, role := .sharedBorrow },
    { name := "b", ty := stdVecObjTy, role := .sharedBorrow }],
   .u 64,
   (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
     (.seq vecMismatchLoop
       (.return_ (.var "i"))))⟩

/-- Program over which the entry evaluates (no callees). -/
abbrev vecMismatchProg : Prog := [vecMismatchFunc]

/-! ## Loop environment -/

/-- Loop environment (borrowed words + `u64` cursor), in prelude
    `let_` cons order (`i` over `[a, b]`, so the entry bridge
    is `rfl`). -/
def mkMismatchEnv (la lb : List (BitVec 32)) (i : BitVec 64) : Env :=
  [("i", .u64 i),
   ("a", .stdVecVal la), ("b", .stdVecVal lb)]

theorem mkMismatchEnv_a (la lb : List (BitVec 32)) (i : BitVec 64) :
    envLookup (mkMismatchEnv la lb i) "a" = some (.stdVecVal la) := by
  simp [mkMismatchEnv, envLookup]

theorem mkMismatchEnv_b (la lb : List (BitVec 32)) (i : BitVec 64) :
    envLookup (mkMismatchEnv la lb i) "b" = some (.stdVecVal lb) := by
  simp [mkMismatchEnv, envLookup]

theorem mkMismatchEnv_i (la lb : List (BitVec 32)) (i : BitVec 64) :
    envLookup (mkMismatchEnv la lb i) "i" = some (.u64 i) := by
  simp [mkMismatchEnv, envLookup]

theorem mismatchEnv_update_i (la lb : List (BitVec 32)) (i i' : BitVec 64) :
    envUpdate (mkMismatchEnv la lb i) "i" (.u64 i') =
      some (mkMismatchEnv la lb i') := by
  simp [mkMismatchEnv, envUpdate]

/-! ## Oracle: first index of difference -/

/-- First index where the two words differ, or the shorter
    length when one list is a prefix of the other. Stated with
    `!=` so the loop's `une` leg rewrites directly. -/
def firstDiff : List (BitVec 32) → List (BitVec 32) → Nat
  | [], _ => 0
  | _, [] => 0
  | x :: xs, y :: ys => if x != y then 0 else 1 + firstDiff xs ys

theorem firstDiff_nil_left (l : List (BitVec 32)) :
    firstDiff [] l = 0 := by
  rfl

theorem firstDiff_nil_right (l : List (BitVec 32)) :
    firstDiff l [] = 0 := by
  cases l with
  | nil => rfl
  | cons _ _ => rfl

theorem firstDiff_cons (x y : BitVec 32)
    (xs ys : List (BitVec 32)) :
    firstDiff (x :: xs) (y :: ys) =
      if x != y then (0 : Nat) else 1 + firstDiff xs ys := by
  rfl

/-- Dropping one more head from both sides consumes fuel. -/
theorem drop_succ_length_le {l l' : List (BitVec 32)} {i F : Nat}
    (hla : i < l.length) (hlb : i < l'.length)
    (hF : (l.drop i).length + (l'.drop i).length ≤ F + 1) :
    (l.drop (i + 1)).length + (l'.drop (i + 1)).length ≤ F := by
  have e1 : (l.drop i).length = l.length - i := List.length_drop
  have e2 : (l'.drop i).length = l'.length - i := List.length_drop
  have e3 : (l.drop (i + 1)).length = l.length - (i + 1) :=
    List.length_drop
  have e4 : (l'.drop (i + 1)).length = l'.length - (i + 1) :=
    List.length_drop
  omega

theorem drop_eq_cons_of_getElem {l : List (BitVec 32)} {i : Nat}
    {x : BitVec 32} (h : l[i]? = some x) :
    l.drop i = x :: l.drop (i + 1) := by
  have hlt : i < l.length := by
    by_cases hm : i < l.length
    · exact hm
    · have hle : l.length ≤ i := by omega
      rw [List.getElem?_eq_none_iff.mpr hle] at h
      cases h
  have hval : l[i]'hlt = x := by
    have h2 := List.getElem?_eq_getElem hlt
    rw [h] at h2
    exact (Option.some.inj h2).symm
  have e := List.drop_eq_getElem_cons hlt
  simpa [hval] using e

/-! ## Forward model (value level) -/

/-- Forward scan: single cursor walks both inputs; the first
    unequal pair returns the position, exhaustion returns the
    cursor. Total: every read is guarded, so the only error arm
    is the unreachable `AssertFail`. -/
def mismatchFwd (la lb : List (BitVec 32)) : Nat → Nat → Result Nat
  | 0, i => .ok i
  | fuel + 1, i =>
    if i < la.length then
      if i < lb.length then
        match la[i]?, lb[i]? with
        | some x, some y =>
          if x != y then .ok i else mismatchFwd la lb fuel (i + 1)
        | _, _ => .error .AssertFail
      else .ok i
    else .ok i

/-- Whole-function forward: cursor from zero. -/
def vecMismatchFwd (la lb : List (BitVec 32)) : Result Value :=
  match mismatchFwd la lb (la.length + lb.length + 1) 0 with
  | .error e => .error e
  | .ok n => .ok (.u64 (BitVec.ofNat 64 n))

/-- The forward scan from `i` returns `i` plus the oracle on
    the drops (fuel covers both remaining suffixes). -/
theorem mismatchFwd_eq (la lb : List (BitVec 32)) (F i : Nat)
    (hF : (la.drop i).length + (lb.drop i).length ≤ F) :
    mismatchFwd la lb F i =
      .ok (i + firstDiff (la.drop i) (lb.drop i)) := by
  induction F generalizing i with
  | zero =>
    have h0a : la.drop i = [] := by
      rw [List.drop_eq_nil_of_le]
      simp only [List.length_drop] at hF
      omega
    have h0b : lb.drop i = [] := by
      rw [List.drop_eq_nil_of_le]
      simp only [List.length_drop] at hF
      omega
    rw [h0a, h0b, firstDiff_nil_left]
    rfl
  | succ F ih =>
    -- Unfold one step; the guard and reads decide the leg.
    simp only [mismatchFwd]
    by_cases hla : i < la.length
    · by_cases hlb : i < lb.length
      · rw [ite_eq_left hla, ite_eq_left hlb]
        have hgetA : la[i]? = some (la[i]'hla) :=
          List.getElem?_eq_getElem hla
        have hgetB : lb[i]? = some (lb[i]'hlb) :=
          List.getElem?_eq_getElem hlb
        rw [hgetA, hgetB]
        rw [drop_eq_cons_of_getElem hgetA,
          drop_eq_cons_of_getElem hgetB, firstDiff_cons]
        have hlen : (la.drop (i + 1)).length +
            (lb.drop (i + 1)).length ≤ F :=
          drop_succ_length_le hla hlb hF
        by_cases hne : (la[i]'hla) != (lb[i]'hlb)
        · simp [hne]
        · simp only [hne]
          have hIH := ih (i + 1) hlen
          rw [hIH]
          simp [Nat.add_assoc]
      · rw [ite_eq_right hlb]
        have hdrop : lb.drop i = [] := by
          rw [List.drop_eq_nil_of_le]
          omega
        rw [hdrop, firstDiff_nil_right]
        simp [hla]
    · rw [ite_eq_right hla]
      have hdrop : la.drop i = [] := by
        rw [List.drop_eq_nil_of_le]
        omega
      rw [hdrop, firstDiff_nil_left]
      simp

/-! ## Loop agreement -/

/-- The guard reads `true` when the cursor is in bounds on both
    sides: `tif` takes the then-branch. -/
theorem mismatchGuard_eval_true (ρ : Env)
    (la lb : List (BitVec 32)) (i : Nat) (iB : BitVec 64)
    (hiN : iB.toNat = i)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hla64 : la.length < 2 ^ 64) (hlb64 : lb.length < 2 ^ 64)
    (hltA : i < la.length) (hltB : i < lb.length) :
    evalExpr mismatchGuard ρ = .ok (.b true) := by
  have hlenA : (BitVec.ofNat 64 la.length).toNat = la.length :=
    ofNat64_toNat _ (by omega)
  have hlenB : (BitVec.ofNat 64 lb.length).toNat = lb.length :=
    ofNat64_toNat _ (by omega)
  have hoLenA : evalExpr (.stdVecLen "a") ρ =
      .ok (.u64 (BitVec.ofNat 64 la.length)) :=
    evalExpr_stdVecLen_some _ _ _ ha
  have hoLenB : evalExpr (.stdVecLen "b") ρ =
      .ok (.u64 (BitVec.ofNat 64 lb.length)) :=
    evalExpr_stdVecLen_some _ _ _ hb
  have hevI : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have e1 : evalExpr (.ult (.var "i") (.stdVecLen "a")) ρ =
      .ok (.b true) := by
    have h := evalExpr_ult_u64 (.var "i") (.stdVecLen "a") ρ iB
      (BitVec.ofNat 64 la.length) hevI hoLenA
    have htb : (iB.ult (BitVec.ofNat 64 la.length)) = true := by
      rw [BitVec.ult_eq_decide, hiN, hlenA]
      exact decide_eq_true hltA
    rwa [htb] at h
  have e2 : evalExpr (.ult (.var "i") (.stdVecLen "b")) ρ =
      .ok (.b true) := by
    have h := evalExpr_ult_u64 (.var "i") (.stdVecLen "b") ρ iB
      (BitVec.ofNat 64 lb.length) hevI hoLenB
    have htb : (iB.ult (BitVec.ofNat 64 lb.length)) = true := by
      rw [BitVec.ult_eq_decide, hiN, hlenB]
      exact decide_eq_true hltB
    rwa [htb] at h
  simp only [mismatchGuard]
  rw [evalExpr_tif_true _ _ _ _ e1]
  exact e2

/-- The guard fails when `a` is exhausted: `tif` takes the else
    branch without touching `b`. -/
theorem mismatchGuard_eval_falseA (ρ : Env)
    (la _lb : List (BitVec 32)) (i : Nat) (iB : BitVec 64)
    (hiN : iB.toNat = i)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hla64 : la.length < 2 ^ 64)
    (hgeA : la.length ≤ i) :
    evalExpr mismatchGuard ρ = .ok (.b false) := by
  have hlenA : (BitVec.ofNat 64 la.length).toNat = la.length :=
    ofNat64_toNat _ (by omega)
  have hoLenA : evalExpr (.stdVecLen "a") ρ =
      .ok (.u64 (BitVec.ofNat 64 la.length)) :=
    evalExpr_stdVecLen_some _ _ _ ha
  have hevI : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have e1 : evalExpr (.ult (.var "i") (.stdVecLen "a")) ρ =
      .ok (.b false) := by
    have h := evalExpr_ult_u64 (.var "i") (.stdVecLen "a") ρ iB
      (BitVec.ofNat 64 la.length) hevI hoLenA
    have hfb : (iB.ult (BitVec.ofNat 64 la.length)) = false := by
      rw [BitVec.ult_eq_decide, hiN, hlenA]
      exact decide_eq_false (by omega)
    rwa [hfb] at h
  simp only [mismatchGuard]
  rw [evalExpr_tif_false _ _ _ _ e1]
  exact evalExpr_lit _ _

/-- The guard fails when `b` is exhausted but `a` is not: `tif`
    runs the second `ult` and takes the else branch. -/
theorem mismatchGuard_eval_falseB (ρ : Env)
    (la lb : List (BitVec 32)) (i : Nat) (iB : BitVec 64)
    (hiN : iB.toNat = i)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hla64 : la.length < 2 ^ 64) (hlb64 : lb.length < 2 ^ 64)
    (hltA : i < la.length) (hgeB : lb.length ≤ i) :
    evalExpr mismatchGuard ρ = .ok (.b false) := by
  have hlenA : (BitVec.ofNat 64 la.length).toNat = la.length :=
    ofNat64_toNat _ (by omega)
  have hlenB : (BitVec.ofNat 64 lb.length).toNat = lb.length :=
    ofNat64_toNat _ (by omega)
  have hoLenA : evalExpr (.stdVecLen "a") ρ =
      .ok (.u64 (BitVec.ofNat 64 la.length)) :=
    evalExpr_stdVecLen_some _ _ _ ha
  have hoLenB : evalExpr (.stdVecLen "b") ρ =
      .ok (.u64 (BitVec.ofNat 64 lb.length)) :=
    evalExpr_stdVecLen_some _ _ _ hb
  have hevI : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have e1 : evalExpr (.ult (.var "i") (.stdVecLen "a")) ρ =
      .ok (.b true) := by
    have h := evalExpr_ult_u64 (.var "i") (.stdVecLen "a") ρ iB
      (BitVec.ofNat 64 la.length) hevI hoLenA
    have htb : (iB.ult (BitVec.ofNat 64 la.length)) = true := by
      rw [BitVec.ult_eq_decide, hiN, hlenA]
      exact decide_eq_true hltA
    rwa [htb] at h
  have e2 : evalExpr (.ult (.var "i") (.stdVecLen "b")) ρ =
      .ok (.b false) := by
    have h := evalExpr_ult_u64 (.var "i") (.stdVecLen "b") ρ iB
      (BitVec.ofNat 64 lb.length) hevI hoLenB
    have hfb : (iB.ult (BitVec.ofNat 64 lb.length)) = false := by
      rw [BitVec.ult_eq_decide, hiN, hlenB]
      exact decide_eq_false (by omega)
    rwa [hfb] at h
  simp only [mismatchGuard]
  rw [evalExpr_tif_true _ _ _ _ e1]
  exact e2

/-- Body step, equal-head leg: the `une` is false, the `if` falls
    to `skip`, and the cursor bumps by one. -/
theorem mismatchBody_bump (prog : Prog) (F : Nat) (ρ : Env)
    (la lb : List (BitVec 32)) (i : Nat) (iB : BitVec 64)
    (x y : BitVec 32)
    (hiN : iB.toNat = i)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hla64 : la.length < 2 ^ 64)
    (hltA : i < la.length)
    (hgetA : la[i]? = some x) (hgetB : lb[i]? = some y)
    (hdrop : (x != y) = false) :
    ∃ ρ₁, evalProgStmt prog F vecMismatchBody ρ =
        .ok (ρ₁, .fellThrough) ∧
      envLookup ρ₁ "a" = some (.stdVecVal la) ∧
      envLookup ρ₁ "b" = some (.stdVecVal lb) ∧
      envLookup ρ₁ "i" = some (.u64 (iB + 1)) ∧
      (iB + 1).toNat = i + 1 := by
  have hevVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have hgetA' : la[iB.toNat]? = some x := by rw [hiN]; exact hgetA
  have hgetB' : lb[iB.toNat]? = some y := by rw [hiN]; exact hgetB
  have hatA : evalExpr (.stdVecAt "a" (.var "i")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hevVar hgetA'
  have hatB : evalExpr (.stdVecAt "b" (.var "i")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hb hevVar hgetB'
  have hune : evalExpr (.une (.stdVecAt "a" (.var "i"))
      (.stdVecAt "b" (.var "i"))) ρ = .ok (.b false) := by
    have h := evalExpr_une_i32 (.stdVecAt "a" (.var "i"))
      (.stdVecAt "b" (.var "i")) ρ x y hatA hatB
    rwa [hdrop] at h
  have hskipV : evalProgStmt prog F .skip ρ =
      .ok (ρ, .fellThrough) := by
    simpa [evalProgStmt] using
      (show evalStmtFuel F .skip ρ = .ok (ρ, .fellThrough) by
        cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith])
  have hif : evalProgStmt prog F
      (.if_ (.une (.stdVecAt "a" (.var "i"))
        (.stdVecAt "b" (.var "i")))
        (.return_ (.var "i")) .skip) ρ = .ok (ρ, .fellThrough) :=
    (evalProgStmt_if_false _ _ _ _ _ _ hune).trans hskipV
  have hevI : evalExpr (.uadd (.var "i")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρ = .ok (.u64 (iB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hevVar (by simp [evalExpr, litVal])
  obtain ⟨ρ₁, hu⟩ := envUpdate_some_of_lookup ρ "i"
    (.u64 iB) (.u64 (iB + 1)) hi
  have hstep : evalProgStmt prog F
      (.assign "i" (.uadd (.var "i")
        (.lit (.u64 (BitVec.ofNat 64 1))))) ρ =
      .ok (ρ₁, .fellThrough) := by
    simpa [evalProgStmt] using
      (evalStmtFuel_assign F "i"
        (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1))))
        ρ (.u64 (iB + 1)) ρ₁ hevI hu)
  have hbody : evalProgStmt prog F vecMismatchBody ρ =
      .ok (ρ₁, .fellThrough) := by
    simp only [vecMismatchBody]
    exact evalProgStmt_seq_fallthrough_trans prog F _ _ ρ ρ _ hif hstep
  have hiN' : (iB + 1).toNat = i + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hiN]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨ρ₁, hbody, ?_, ?_, ?_, hiN'⟩
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "i" by decide) hu]
    exact ha
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("b" : String) ≠ "i" by decide) hu]
    exact hb
  · rw [envLookup_update_hit _ _ _ _ hu]

/-- Body step, unequal-head leg: the `une` is true and the body
    returns the cursor; the trailing bump never runs. -/
theorem mismatchBody_return (prog : Prog) (F : Nat) (ρ : Env)
    (la lb : List (BitVec 32)) (i : Nat) (iB : BitVec 64)
    (x y : BitVec 32)
    (hiN : iB.toNat = i)
    (hi : envLookup ρ "i" = some (.u64 iB))
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hgetA : la[i]? = some x) (hgetB : lb[i]? = some y)
    (htru : (x != y) = true) :
    evalProgStmt prog F vecMismatchBody ρ =
      .ok (ρ, .returned (.u64 iB)) := by
  have hevVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have hgetA' : la[iB.toNat]? = some x := by rw [hiN]; exact hgetA
  have hgetB' : lb[iB.toNat]? = some y := by rw [hiN]; exact hgetB
  have hatA : evalExpr (.stdVecAt "a" (.var "i")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hevVar hgetA'
  have hatB : evalExpr (.stdVecAt "b" (.var "i")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hb hevVar hgetB'
  have hune : evalExpr (.une (.stdVecAt "a" (.var "i"))
      (.stdVecAt "b" (.var "i"))) ρ = .ok (.b true) := by
    have h := evalExpr_une_i32 (.stdVecAt "a" (.var "i"))
      (.stdVecAt "b" (.var "i")) ρ x y hatA hatB
    rwa [htru] at h
  have hret : evalProgStmt prog F (.return_ (.var "i")) ρ =
      .ok (ρ, .returned (.u64 iB)) :=
    evalProgStmt_return prog F _ ρ _ hevVar
  have hif : evalProgStmt prog F
      (.if_ (.une (.stdVecAt "a" (.var "i"))
        (.stdVecAt "b" (.var "i")))
        (.return_ (.var "i")) .skip) ρ =
      .ok (ρ, .returned (.u64 iB)) :=
    (evalProgStmt_if_true _ _ _ _ _ _ hune).trans hret
  have hseq : evalProgStmt prog F vecMismatchBody ρ =
      .ok (ρ, .returned (.u64 iB)) := by
    simp only [vecMismatchBody]
    exact evalProgStmt_seq_returned prog F _ _ ρ ρ (.u64 iB) hif
  exact hseq

/-- Loop agreement: the loop either falls through having advanced
    the cursor, or returns the position early. In both cases the
    cursor value agrees with the forward model. Fuel covers both
    remaining suffixes (value fuel `F`, forward fuel `G`). -/
theorem vecMismatchLoop_ok (F G : Nat) (prog : Prog) (ρ : Env)
    (la lb : List (BitVec 32)) (i r : Nat) (iB : BitVec 64)
    (hiN : iB.toNat = i)
    (hla64 : la.length < 2 ^ 64) (hlb64 : lb.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hF : (la.length - i) + (lb.length - i) ≤ F)
    (hG : (la.length - i) + (lb.length - i) ≤ G)
    (hfwd : mismatchFwd la lb G i = .ok r) :
    ∃ ρ' out, evalProgStmt prog F vecMismatchLoop ρ = .ok (ρ', out) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "b" = some (.stdVecVal lb) ∧
      ∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = r ∧
        (out = .fellThrough ∨ out = .returned (.u64 iB')) := by
  induction F generalizing G ρ i iB r with
  | zero =>
    have hgeA : la.length ≤ i := by omega
    have hgeB : lb.length ≤ i := by omega
    have hguardF : evalExpr mismatchGuard ρ = .ok (.b false) :=
      mismatchGuard_eval_falseA ρ la lb i iB hiN ha hi hla64 hgeA
    have hexit : evalProgStmt prog 0 vecMismatchLoop ρ =
        .ok (ρ, .fellThrough) :=
      evalProgStmt_while_false prog 0 _ _ _ hguardF
    have hdropA : la.drop i = [] := by
      rw [List.drop_eq_nil_of_le]
      omega
    have e1 := mismatchFwd_eq la lb G i
      (by simp only [List.length_drop]; exact hG)
    rw [hdropA, firstDiff_nil_left] at e1
    have hir : r = i := by
      have h := hfwd.symm.trans e1
      simpa using h
    exact ⟨ρ, .fellThrough, hexit, ha, hb, iB, hi,
      by omega, Or.inl rfl⟩
  | succ F ih =>
    by_cases hltA : i < la.length
    · by_cases hltB : i < lb.length
      · obtain ⟨x, hgetA⟩ : ∃ x, la[i]? = some x :=
          ⟨la[i]'hltA, List.getElem?_eq_getElem hltA⟩
        obtain ⟨y, hgetB⟩ : ∃ y, lb[i]? = some y :=
          ⟨lb[i]'hltB, List.getElem?_eq_getElem hltB⟩
        have hguardT : evalExpr mismatchGuard ρ = .ok (.b true) :=
          mismatchGuard_eval_true ρ la lb i iB hiN ha hb hi
            hla64 hlb64 hltA hltB
        by_cases hne : x != y
        · -- Unequal heads: return the cursor.
          have htru : (x != y) = true := hne
          have hbodyret : evalProgStmt prog F vecMismatchBody ρ =
              .ok (ρ, .returned (.u64 iB)) :=
            mismatchBody_return prog F ρ la lb i iB x y hiN hi ha hb
              hgetA hgetB htru
          have hdone : evalProgStmt prog (F + 1) vecMismatchLoop ρ =
              .ok (ρ, .returned (.u64 iB)) := by
            cir_unfold_prog (vecMismatchLoop, prog, F, hguardT, hbodyret)
          have e1 := mismatchFwd_eq la lb G i
            (by simp only [List.length_drop]; exact hG)
          rw [drop_eq_cons_of_getElem hgetA, drop_eq_cons_of_getElem hgetB,
            firstDiff_cons, ite_eq_left hne] at e1
          have hir : r = i := by
            have h := hfwd.symm.trans e1
            simpa using h
          exact ⟨ρ, .returned (.u64 iB), hdone, ha, hb, iB, hi,
            by omega, Or.inr rfl⟩
        · -- Equal heads: bump and continue.
          have hdrop : (x != y) = false := by simpa using hne
          cir_fuel_step (F, G,
            (la.length - (i + 1)) + (lb.length - (i + 1)))
          obtain ⟨ρ₁, hbody, ha₁, hb₁, hiB₁, hiN₁⟩ :=
            mismatchBody_bump prog F ρ la lb i iB x y hiN ha hb hi
              hla64 hltA hgetA hgetB hdrop
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
          obtain ⟨ρ', out, hloop, ha', hb', iB', hiB', hr', hout⟩ :=
            ih (G := G') (ρ := ρ₁) (i := i + 1) (iB := iB + 1) (r := r)
              hiN₁ ha₁ hb₁ hiB₁ hF' hG' hfwd'
          refine ⟨ρ', out, ?_, ha', hb', iB', hiB', hr', hout⟩
          have hwhile : evalProgStmt prog (F + 1) vecMismatchLoop ρ =
              evalProgStmt prog F vecMismatchLoop ρ₁ := by
            cir_unfold_prog (vecMismatchLoop, prog, F, hguardT, hbody)
          rw [hwhile]
          exact hloop
      · -- `b` exhausted: exit, tail returns `i`.
        have hgeB : lb.length ≤ i := by omega
        have hguardF : evalExpr mismatchGuard ρ = .ok (.b false) :=
          mismatchGuard_eval_falseB ρ la lb i iB hiN ha hb hi
            hla64 hlb64 hltA hgeB
        have hexit : evalProgStmt prog (F + 1) vecMismatchLoop ρ =
            .ok (ρ, .fellThrough) :=
          evalProgStmt_while_false prog (F + 1) _ _ _ hguardF
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
        exact ⟨ρ, .fellThrough, hexit, ha, hb, iB, hi,
          by omega, Or.inl rfl⟩
    · -- `a` exhausted: exit, tail returns `i`.
      have hgeA : la.length ≤ i := by omega
      have hguardF : evalExpr mismatchGuard ρ = .ok (.b false) :=
        mismatchGuard_eval_falseA ρ la lb i iB hiN ha hi hla64 hgeA
      have hexit : evalProgStmt prog (F + 1) vecMismatchLoop ρ =
          .ok (ρ, .fellThrough) :=
        evalProgStmt_while_false prog (F + 1) _ _ _ hguardF
      have hdropA : la.drop i = [] := by
        rw [List.drop_eq_nil_of_le]
        omega
      have e1 := mismatchFwd_eq la lb G i
        (by simp only [List.length_drop]; exact hG)
      rw [hdropA, firstDiff_nil_left] at e1
      have hir : r = i := by
        have h := hfwd.symm.trans e1
        simpa using h
      exact ⟨ρ, .fellThrough, hexit, ha, hb, iB, hi,
        by omega, Or.inl rfl⟩

/-! ## Oracle bounds (entry support) -/

/-- The first-difference position never exceeds the left length. -/
theorem firstDiff_le_left (la lb : List (BitVec 32)) :
    firstDiff la lb ≤ la.length := by
  induction la generalizing lb with
  | nil => rw [firstDiff_nil_left]; exact Nat.zero_le _
  | cons x xs ih =>
    cases lb with
    | nil => rw [firstDiff_nil_right]; exact Nat.zero_le _
    | cons y ys =>
      rw [firstDiff_cons]
      by_cases hne : x != y
      · simp [hne]
      · rw [ite_eq_right hne]
        have h := ih ys
        simp only [List.length_cons]
        omega

/-- The first-difference position never exceeds the right length. -/
theorem firstDiff_le_right (la lb : List (BitVec 32)) :
    firstDiff la lb ≤ lb.length := by
  induction la generalizing lb with
  | nil => rw [firstDiff_nil_left]; simp
  | cons x xs ih =>
    cases lb with
    | nil => rw [firstDiff_nil_right]; simp
    | cons y ys =>
      rw [firstDiff_cons]
      by_cases hne : x != y
      · simp [hne]
      · rw [ite_eq_right hne]
        have h := ih ys
        simp only [List.length_cons]
        omega

/-- Whole-function forward agrees with the oracle. -/
theorem vecMismatchFwd_eq (la lb : List (BitVec 32))
    (_hla64 : la.length < 2 ^ 64) (_hlb64 : lb.length < 2 ^ 64) :
    vecMismatchFwd la lb =
      .ok (.u64 (BitVec.ofNat 64 (firstDiff la lb))) := by
  have hF : (la.drop 0).length + (lb.drop 0).length ≤
      la.length + lb.length + 1 := by
    simp only [List.drop_zero]
    omega
  have h := mismatchFwd_eq la lb (la.length + lb.length + 1) 0 hF
  simp only [List.drop_zero, Nat.zero_add] at h
  simp only [vecMismatchFwd, h]
