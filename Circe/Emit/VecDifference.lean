/-
Two-cursor sorted-range difference (`std::set_difference` idiom)
over `std::vector<int>` — the third two-input shape of the
pillar-2 run (P2-M15), completing the set-operation trio.

Corpus: `tests/cpp/vec_difference.cpp` →
`tests/cir/vec_difference.cir` (entry
`_Z14vec_differenceRSt6vectorIiSaIiEES2_S2_`: two single-ref
vectors plus one single-ref output vector in, `u64` count out;
one `cir.ternary` over the `&&` guard, two `cir.while` (the
main two-pointer loop plus the left-survivor drain — no
drain-`b`), two `cir.if` (the three-way branch: the outer `if`
plus the `else if` nested in its else region), five `lt`
compares, eleven `cir.call @` (three `size` + eight non-const
`at()`)).

Model: cursors `i`, `j` walk the sorted inputs, `w` records the
left-only heads into the caller-sized output. At each step the
heads are compared signed: a strictly smaller left head is
recorded and the `i` and `w` cursors bump; a strictly smaller
right head advances only `j`; equal heads advance both and
record nothing (extra left copies beyond the right count
survive — `set_difference` multiplicity). The left cursor
reaching its end stops the main scan; the drain copies the left
survivor suffix. The caller owes `a.size()` output slots. The
inputs are sorted (caller debt). Like union, every store is a
plain `vecSet` — the model is total; the record capacity is a
hypothesis, unreachable index failures stay loud `AssertFail`.
-/
import Circe.Emit.VecMergeInto
import Circe.Emit.VecReverse

/-- Function name (Itanium mangling of a `vec_difference` free
    function taking three `vector<int>&`). -/
def vecDifferenceName : String :=
  "_Z14vec_differenceRSt6vectorIiSaIiEES2_S2_"

/-- Main-loop guard: `i < a.size() && j < b.size()`, lowered by
    CIRGen as a short-circuit `cir.ternary` over the two
    `ult`s (the same `tif` shape as the union guard). -/
def differenceGuard : CExpr :=
  .tif (.ult (.var "i") (.stdVecLen "a"))
    (.ult (.var "j") (.stdVecLen "b"))
    (.lit (.b false))

/-- Main-loop body: three-way signed head compare — a strictly
    smaller left head is recorded and the `i` and `w` cursors
    bump; a strictly smaller right head advances only `j`;
    equal heads advance both and record nothing. -/
def vecDifferenceBody : CStmt :=
  (.if_ (.slt (.stdVecAt "a" (.var "i"))
              (.stdVecAt "b" (.var "j")))
    (.seq (.vecSet "out" (.var "w")
              (.stdVecAt "a" (.var "i")))
      (.seq (.assign "i" (.uadd (.var "i")
                (.lit (.u64 (BitVec.ofNat 64 1)))))
        (.assign "w" (.uadd (.var "w")
                (.lit (.u64 (BitVec.ofNat 64 1)))))))
    (.if_ (.slt (.stdVecAt "b" (.var "j"))
                (.stdVecAt "a" (.var "i")))
      (.assign "j" (.uadd (.var "j")
              (.lit (.u64 (BitVec.ofNat 64 1)))))
      (.seq (.assign "i" (.uadd (.var "i")
                (.lit (.u64 (BitVec.ofNat 64 1)))))
        (.assign "j" (.uadd (.var "j")
                (.lit (.u64 (BitVec.ofNat 64 1))))))))

/-- The main difference scan loop. -/
def vecDifferenceMain : CStmt :=
  .while_ differenceGuard vecDifferenceBody

/-- Drain body: copy the left survivor head, advance `i` and the
    record cursor (no branch — the survivor side is fixed). -/
def vecDifferenceDrainBody : CStmt :=
  (.seq (.vecSet "out" (.var "w")
            (.stdVecAt "a" (.var "i")))
    (.seq (.assign "i" (.uadd (.var "i")
              (.lit (.u64 (BitVec.ofNat 64 1)))))
      (.assign "w" (.uadd (.var "w")
              (.lit (.u64 (BitVec.ofNat 64 1)))))))

/-- Drain loop `while (i < a.size()) body` (no drain-`b`:
    leftover right elements are never recorded). -/
def vecDifferenceDrain : CStmt :=
  .while_ (.ult (.var "i") (.stdVecLen "a")) vecDifferenceDrainBody

/-- Entry: three `u64` seeds, the main scan, the left drain, and
    the survivor count out. -/
def vecDifferenceFunc : Func :=
  ⟨vecDifferenceName,
   [{ name := "a", ty := stdVecObjTy, role := .sharedBorrow },
    { name := "b", ty := stdVecObjTy, role := .sharedBorrow },
    { name := "out", ty := stdVecObjTy, role := .mutBorrow 0 }],
   .u 64,
   (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
     (.seq (.let_ "j" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
       (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
         (.seq vecDifferenceMain
           (.seq vecDifferenceDrain
             (.return_ (.var "w")))))))⟩

/-- Program over which the entry evaluates (no callees). -/
abbrev vecDifferenceProg : Prog := [vecDifferenceFunc]

/-! ## Forward model (value level) -/

/-- Main-loop forward: cursors `i`, `j` walk the sorted inputs,
    `w` records left-only heads into `lo`. Only the take-left
    leg writes; the other two legs advance silently. Either
    cursor reaching its end stops the scan. Total: every index
    failure is guarded away, so the only error arm is the
    unreachable `AssertFail`. -/
def differenceMainFwd :
    List (BitVec 32) → List (BitVec 32) → List (BitVec 32) →
    Nat → Nat → Nat → Nat → Result (Nat × Nat × Nat × List (BitVec 32))
  | la, lb, lo, 0, i, j, w => .ok (i, j, w, lo)
  | la, lb, lo, fuel + 1, i, j, w =>
    if _ : i < la.length then
      if _ : j < lb.length then
        match la[i]?, lb[j]? with
        | some x, some y =>
          if x.slt y then
            differenceMainFwd la lb (lo.set w x) fuel (i + 1) j (w + 1)
          else if y.slt x then
            differenceMainFwd la lb lo fuel i (j + 1) w
          else differenceMainFwd la lb lo fuel (i + 1) (j + 1) w
        | _, _ => .error .AssertFail
      else .ok (i, j, w, lo)
    else .ok (i, j, w, lo)

/-- Drain forward: copy the `a` survivor suffix into `lo`. -/
def differenceDrainFwd (la : List (BitVec 32)) : List (BitVec 32) →
    Nat → Nat → Nat → Result (Nat × Nat × List (BitVec 32))
  | lo, 0, i, w => .ok (i, w, lo)
  | lo, fuel + 1, i, w =>
    if _ : i < la.length then
      match la[i]? with
      | some x => differenceDrainFwd la (lo.set w x) fuel (i + 1) (w + 1)
      | none => .error .AssertFail
    else .ok (i, w, lo)

/-- Whole-function forward: main scan, then the left drain; the
    `u64` survivor count is the result. Model fuels are
    measure-exact (remaining iterations). -/
def vecDifferenceFwd (la lb : List (BitVec 32))
    (lo : List (BitVec 32)) : Result Value :=
  match differenceMainFwd la lb lo (la.length + lb.length + 1) 0 0 0 with
  | .error e => .error e
  | .ok (i, j, w, lo') =>
    match differenceDrainFwd la lo' (la.length - i) i w with
    | .error e => .error e
    | .ok (_, w', _) => .ok (.u64 (BitVec.ofNat 64 w'))

/-! ## Loop environment -/

/-- Loop environment (borrowed words + `u64` cursors), in prelude
    `let_` cons order (`w` over `j` over `i` over `[a, b, out]`,
    so the entry bridge is `rfl`). -/
def mkDifferenceEnv (la lb lo : List (BitVec 32))
    (i j w : BitVec 64) : Env :=
  [("w", .u64 w), ("j", .u64 j), ("i", .u64 i),
   ("a", .stdVecVal la), ("b", .stdVecVal lb),
   ("out", .stdVecVal lo)]

theorem mkDifferenceEnv_a (la lb lo : List (BitVec 32))
    (i j w : BitVec 64) :
    envLookup (mkDifferenceEnv la lb lo i j w) "a" =
      some (.stdVecVal la) := by
  simp [mkDifferenceEnv, envLookup]

theorem mkDifferenceEnv_b (la lb lo : List (BitVec 32))
    (i j w : BitVec 64) :
    envLookup (mkDifferenceEnv la lb lo i j w) "b" =
      some (.stdVecVal lb) := by
  simp [mkDifferenceEnv, envLookup]

theorem mkDifferenceEnv_out (la lb lo : List (BitVec 32))
    (i j w : BitVec 64) :
    envLookup (mkDifferenceEnv la lb lo i j w) "out" =
      some (.stdVecVal lo) := by
  simp [mkDifferenceEnv, envLookup]

theorem mkDifferenceEnv_i (la lb lo : List (BitVec 32))
    (i j w : BitVec 64) :
    envLookup (mkDifferenceEnv la lb lo i j w) "i" =
      some (.u64 i) := by
  simp [mkDifferenceEnv, envLookup]

theorem mkDifferenceEnv_j (la lb lo : List (BitVec 32))
    (i j w : BitVec 64) :
    envLookup (mkDifferenceEnv la lb lo i j w) "j" =
      some (.u64 j) := by
  simp [mkDifferenceEnv, envLookup]

theorem mkDifferenceEnv_w (la lb lo : List (BitVec 32))
    (i j w : BitVec 64) :
    envLookup (mkDifferenceEnv la lb lo i j w) "w" =
      some (.u64 w) := by
  simp [mkDifferenceEnv, envLookup]

/-! ## Guard evaluation -/

/-- The guard holds when both cursors are in bounds: `tif` takes
    the second `ult` without touching the vectors. -/
theorem differenceGuard_eval_true (ρ : Env)
    (la lb : List (BitVec 32)) (i j : Nat)
    (iB jB : BitVec 64)
    (hiN : iB.toNat = i) (hjN : jB.toNat = j)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hla64 : la.length < 2 ^ 64) (hlb64 : lb.length < 2 ^ 64)
    (hltA : i < la.length) (hltB : j < lb.length) :
    evalExpr differenceGuard ρ = .ok (.b true) := by
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
  have e1 : evalExpr (.ult (.var "i") (.stdVecLen "a")) ρ =
      .ok (.b true) := by
    have h := evalExpr_ult_u64 (.var "i") (.stdVecLen "a") ρ iB
      (BitVec.ofNat 64 la.length) (evalExpr_var_hit _ _ _ hi) hoLenA
    have htb : (iB.ult (BitVec.ofNat 64 la.length)) = true := by
      rw [BitVec.ult_eq_decide, hiN, hlenA]
      exact decide_eq_true hltA
    rwa [htb] at h
  have e2 : evalExpr (.ult (.var "j") (.stdVecLen "b")) ρ =
      .ok (.b true) := by
    have h := evalExpr_ult_u64 (.var "j") (.stdVecLen "b") ρ jB
      (BitVec.ofNat 64 lb.length) (evalExpr_var_hit _ _ _ hj) hoLenB
    have htb : (jB.ult (BitVec.ofNat 64 lb.length)) = true := by
      rw [BitVec.ult_eq_decide, hjN, hlenB]
      exact decide_eq_true hltB
    rwa [htb] at h
  simp only [differenceGuard]
  rw [evalExpr_tif_true _ _ _ _ e1]
  exact e2

/-- The guard fails when `i` is exhausted: `tif` takes the else
    branch without touching `b`. -/
theorem differenceGuard_eval_falseA (ρ : Env)
    (la lb : List (BitVec 32)) (i j : Nat)
    (iB jB : BitVec 64)
    (hiN : iB.toNat = i)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hla64 : la.length < 2 ^ 64)
    (hgeA : la.length ≤ i) :
    evalExpr differenceGuard ρ = .ok (.b false) := by
  have hlenA : (BitVec.ofNat 64 la.length).toNat = la.length :=
    ofNat64_toNat _ (by omega)
  have hoLenA : evalExpr (.stdVecLen "a") ρ =
      .ok (.u64 (BitVec.ofNat 64 la.length)) :=
    evalExpr_stdVecLen_some _ _ _ ha
  have e1 : evalExpr (.ult (.var "i") (.stdVecLen "a")) ρ =
      .ok (.b false) := by
    have h := evalExpr_ult_u64 (.var "i") (.stdVecLen "a") ρ iB
      (BitVec.ofNat 64 la.length) (evalExpr_var_hit _ _ _ hi) hoLenA
    have hfb : (iB.ult (BitVec.ofNat 64 la.length)) = false := by
      rw [BitVec.ult_eq_decide, hiN, hlenA]
      exact decide_eq_false (by omega)
    rwa [hfb] at h
  simp only [differenceGuard]
  rw [evalExpr_tif_false _ _ _ _ e1]
  exact evalExpr_lit _ _

/-- The guard fails when `j` is exhausted but `i` is not: `tif`
    runs the second `ult` and takes the else branch. -/
theorem differenceGuard_eval_falseB (ρ : Env)
    (la lb : List (BitVec 32)) (i j : Nat)
    (iB jB : BitVec 64)
    (hiN : iB.toNat = i) (hjN : jB.toNat = j)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hla64 : la.length < 2 ^ 64) (hlb64 : lb.length < 2 ^ 64)
    (hltA : i < la.length) (hgeB : lb.length ≤ j) :
    evalExpr differenceGuard ρ = .ok (.b false) := by
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
  have e1 : evalExpr (.ult (.var "i") (.stdVecLen "a")) ρ =
      .ok (.b true) := by
    have h := evalExpr_ult_u64 (.var "i") (.stdVecLen "a") ρ iB
      (BitVec.ofNat 64 la.length) (evalExpr_var_hit _ _ _ hi) hoLenA
    have htb : (iB.ult (BitVec.ofNat 64 la.length)) = true := by
      rw [BitVec.ult_eq_decide, hiN, hlenA]
      exact decide_eq_true hltA
    rwa [htb] at h
  have e2 : evalExpr (.ult (.var "j") (.stdVecLen "b")) ρ =
      .ok (.b false) := by
    have h := evalExpr_ult_u64 (.var "j") (.stdVecLen "b") ρ jB
      (BitVec.ofNat 64 lb.length) (evalExpr_var_hit _ _ _ hj) hoLenB
    have hfb : (jB.ult (BitVec.ofNat 64 lb.length)) = false := by
      rw [BitVec.ult_eq_decide, hjN, hlenB]
      exact decide_eq_false (by omega)
    rwa [hfb] at h
  simp only [differenceGuard]
  rw [evalExpr_tif_true _ _ _ _ e1]
  exact e2

/-! ## Value body steps -/

theorem valDifferenceMainBody_takeLeft (prog : Prog) (F : Nat)
    (ρ : Env) (la lb lo : List (BitVec 32)) (i j w : Nat)
    (iB jB wB : BitVec 64) (x y : BitVec 32)
    (hiN : iB.toNat = i) (hjN : jB.toNat = j) (hwN : wB.toNat = w)
    (hla64 : la.length < 2 ^ 64)
    (hlb64 : lb.length < 2 ^ 64)
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
    (hlt : (x.slt y) = true) :
    ∃ ρ', evalProgStmt prog F vecDifferenceBody ρ =
      .ok (ρ', .fellThrough) ∧
      envLookup ρ' "i" = some (.u64 (iB + 1)) ∧
      (iB + 1).toNat = i + 1 ∧
      envLookup ρ' "j" = some (.u64 jB) ∧
      envLookup ρ' "w" = some (.u64 (wB + 1)) ∧
      (wB + 1).toNat = w + 1 ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "b" = some (.stdVecVal lb) ∧
      envLookup ρ' "out" = some (.stdVecVal (lo.set w x)) := by
  have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have hgetA' : la[iB.toNat]? = some x := by rw [hiN]; exact hgetA
  have hgetB' : lb[jB.toNat]? = some y := by rw [hjN]; exact hgetB
  have hatA : evalExpr (.stdVecAt "a" (.var "i")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hiVar hgetA'
  have hjVar : evalExpr (.var "j") ρ = .ok (.u64 jB) :=
    evalExpr_var_hit _ _ _ hj
  have hatB : evalExpr (.stdVecAt "b" (.var "j")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hb hjVar hgetB'
  have hcmp : evalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "b" (.var "j")))
      ρ = .ok (.b true) := by
    rw [evalExpr_slt_i32 _ _ _ _ _ hatA hatB, hlt]
  have hwVar : evalExpr (.var "w") ρ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw
  have hgetO' : lo[wB.toNat]? = some xO := by rw [hwN]; exact hgetO
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "out"
    (.stdVecVal lo) (.stdVecVal (lo.set wB.toNat x)) hout
  have hset := revVecSet prog F "out" (.var "w")
    (.stdVecAt "a" (.var "i")) ρ wB x lo xO ρ₁
    hwVar hatA hout hgetO' hu₁
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
  obtain ⟨ρ₂, hu₂⟩ := envUpdate_some_of_lookup ρ₁ "i"
    (.u64 iB) (.u64 (iB + 1)) hi₁
  have hstepI := revAssign prog F "i"
    (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁
    (.u64 (iB + 1)) ρ₂ hevI hu₂
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
  have hevW : evalExpr
      (.uadd (.var "w") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ =
      .ok (.u64 (wB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hw₂) (by simp [evalExpr, litVal])
  obtain ⟨ρ₃, hu₃⟩ := envUpdate_some_of_lookup ρ₂ "w"
    (.u64 wB) (.u64 (wB + 1)) hw₂
  have hstepW := revAssign prog F "w"
    (.uadd (.var "w") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂
    (.u64 (wB + 1)) ρ₃ hevW hu₃
  have hiN' : (iB + 1).toNat = i + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hiN]
    exact Nat.mod_eq_of_lt (by omega)
  have hwN' : (wB + 1).toNat = w + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hwN]
    exact Nat.mod_eq_of_lt (by omega)
  have hif : evalProgStmt prog F vecDifferenceBody ρ =
      evalProgStmt prog F
        (.seq (.vecSet "out" (.var "w")
                 (.stdVecAt "a" (.var "i")))
          (.seq (.assign "i" (.uadd (.var "i")
                    (.lit (.u64 (BitVec.ofNat 64 1)))))
            (.assign "w" (.uadd (.var "w")
                      (.lit (.u64 (BitVec.ofNat 64 1))))))) ρ := by
    simp only [vecDifferenceBody]
    exact evalProgStmt_if_true _ _ _ _ _ _ hcmp
  have hsetW : lo.set wB.toNat x = lo.set w x := by rw [hwN]
  have hseq0 : evalProgStmt prog F
      (.seq (.assign "i" (.uadd (.var "i")
                (.lit (.u64 (BitVec.ofNat 64 1)))))
        (.assign "w" (.uadd (.var "w")
                  (.lit (.u64 (BitVec.ofNat 64 1)))))) ρ₁ =
      evalProgStmt prog F
        (.assign "w" (.uadd (.var "w")
                (.lit (.u64 (BitVec.ofNat 64 1))))) ρ₂ := by
    exact evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepI
  refine ⟨ρ₃, ?_, ?_, hiN', ?_, ?_, hwN', ?_, ?_, ?_⟩
  · rw [hif,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hset,
      hseq0]
    exact hstepW
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "w" by decide) hu₃]
    exact envLookup_update_hit _ _ _ _ hu₂
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("j" : String) ≠ "w" by decide) hu₃]
    exact hj₂
  · rw [envLookup_update_hit _ _ _ _ hu₃]
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "w" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "i" by decide) hu₂]
    exact ha₁
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("b" : String) ≠ "w" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("b" : String) ≠ "i" by decide) hu₂]
    exact hb₁
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "w" by decide) hu₃,
      ← hsetW]
    exact hout₂

/-- One main-body iteration, advance-`right` branch: `a[i] <
    b[j]` fails but `b[j] < a[i]` holds, so only the `j` cursor
    bumps (nothing is recorded). -/
theorem valDifferenceMainBody_advRight (prog : Prog) (F : Nat)
    (ρ : Env) (la lb lo : List (BitVec 32)) (i j w : Nat)
    (iB jB wB : BitVec 64) (x y : BitVec 32)
    (hiN : iB.toNat = i) (hjN : jB.toNat = j) (hwN : wB.toNat = w)
    (hla64 : la.length < 2 ^ 64)
    (hlb64 : lb.length < 2 ^ 64)
    (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hgetA : la[i]? = some x) (hgetB : lb[j]? = some y)
    (hltA : i < la.length) (hltB : j < lb.length)
    (hne : (x.slt y) = false) (hgt : (y.slt x) = true) :
    ∃ ρ', evalProgStmt prog F vecDifferenceBody ρ =
      .ok (ρ', .fellThrough) ∧
      envLookup ρ' "i" = some (.u64 iB) ∧
      envLookup ρ' "j" = some (.u64 (jB + 1)) ∧
      (jB + 1).toNat = j + 1 ∧
      envLookup ρ' "w" = some (.u64 wB) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "b" = some (.stdVecVal lb) ∧
      envLookup ρ' "out" = some (.stdVecVal lo) := by
  have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have hgetA' : la[iB.toNat]? = some x := by rw [hiN]; exact hgetA
  have hgetB' : lb[jB.toNat]? = some y := by rw [hjN]; exact hgetB
  have hatA : evalExpr (.stdVecAt "a" (.var "i")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hiVar hgetA'
  have hjVar : evalExpr (.var "j") ρ = .ok (.u64 jB) :=
    evalExpr_var_hit _ _ _ hj
  have hatB : evalExpr (.stdVecAt "b" (.var "j")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hb hjVar hgetB'
  have hcmp1 : evalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "b" (.var "j")))
      ρ = .ok (.b false) := by
    rw [evalExpr_slt_i32 _ _ _ _ _ hatA hatB, hne]
  have hcmp2 : evalExpr
      (.slt (.stdVecAt "b" (.var "j")) (.stdVecAt "a" (.var "i")))
      ρ = .ok (.b true) := by
    rw [evalExpr_slt_i32 _ _ _ _ _ hatB hatA, hgt]
  have hevJ : evalExpr
      (.uadd (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ =
      .ok (.u64 (jB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hj) (by simp [evalExpr, litVal])
  obtain ⟨ρ', hu⟩ := envUpdate_some_of_lookup ρ "j"
    (.u64 jB) (.u64 (jB + 1)) hj
  have hstepJ := revAssign prog F "j"
    (.uadd (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ
    (.u64 (jB + 1)) ρ' hevJ hu
  have hjN' : (jB + 1).toNat = j + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hjN]
    exact Nat.mod_eq_of_lt (by omega)
  have hif : evalProgStmt prog F vecDifferenceBody ρ =
      evalProgStmt prog F
        (.assign "j" (.uadd (.var "j")
                (.lit (.u64 (BitVec.ofNat 64 1))))) ρ := by
    simp only [vecDifferenceBody]
    rw [evalProgStmt_if_false _ _ _ _ _ _ hcmp1]
    exact evalProgStmt_if_true _ _ _ _ _ _ hcmp2
  refine ⟨ρ', ?_, ?_, ?_, hjN', ?_, ?_, ?_, ?_⟩
  · rw [hif]
    exact hstepJ
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

/-- One main-body iteration, skip-both branch: neither head is
    strictly smaller, so both cursors advance and nothing is
    recorded. -/
theorem valDifferenceMainBody_skipBoth (prog : Prog) (F : Nat)
    (ρ : Env) (la lb lo : List (BitVec 32)) (i j w : Nat)
    (iB jB wB : BitVec 64) (x y : BitVec 32)
    (hiN : iB.toNat = i) (hjN : jB.toNat = j) (hwN : wB.toNat = w)
    (hla64 : la.length < 2 ^ 64)
    (hlb64 : lb.length < 2 ^ 64)
    (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hgetA : la[i]? = some x) (hgetB : lb[j]? = some y)
    (hltA : i < la.length) (hltB : j < lb.length)
    (hge1 : (x.slt y) = false) (hge2 : (y.slt x) = false) :
    ∃ ρ', evalProgStmt prog F vecDifferenceBody ρ =
      .ok (ρ', .fellThrough) ∧
      envLookup ρ' "i" = some (.u64 (iB + 1)) ∧
      (iB + 1).toNat = i + 1 ∧
      envLookup ρ' "j" = some (.u64 (jB + 1)) ∧
      (jB + 1).toNat = j + 1 ∧
      envLookup ρ' "w" = some (.u64 wB) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "b" = some (.stdVecVal lb) ∧
      envLookup ρ' "out" = some (.stdVecVal lo) := by
  have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have hgetA' : la[iB.toNat]? = some x := by rw [hiN]; exact hgetA
  have hgetB' : lb[jB.toNat]? = some y := by rw [hjN]; exact hgetB
  have hatA : evalExpr (.stdVecAt "a" (.var "i")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hiVar hgetA'
  have hjVar : evalExpr (.var "j") ρ = .ok (.u64 jB) :=
    evalExpr_var_hit _ _ _ hj
  have hatB : evalExpr (.stdVecAt "b" (.var "j")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hb hjVar hgetB'
  have hcmp1 : evalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "b" (.var "j")))
      ρ = .ok (.b false) := by
    rw [evalExpr_slt_i32 _ _ _ _ _ hatA hatB, hge1]
  have hcmp2 : evalExpr
      (.slt (.stdVecAt "b" (.var "j")) (.stdVecAt "a" (.var "i")))
      ρ = .ok (.b false) := by
    rw [evalExpr_slt_i32 _ _ _ _ _ hatB hatA, hge2]
  have hevI : evalExpr
      (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ =
      .ok (.u64 (iB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hi) (by simp [evalExpr, litVal])
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "i"
    (.u64 iB) (.u64 (iB + 1)) hi
  have hstepI := revAssign prog F "i"
    (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ
    (.u64 (iB + 1)) ρ₁ hevI hu₁
  have hi₁ : envLookup ρ₁ "i" = some (.u64 (iB + 1)) :=
    envLookup_update_hit _ _ _ _ hu₁
  have hj₁ : envLookup ρ₁ "j" = some (.u64 jB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("j" : String) ≠ "i" by decide) hu₁]
    exact hj
  have hw₁ : envLookup ρ₁ "w" = some (.u64 wB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "i" by decide) hu₁]
    exact hw
  have ha₁ : envLookup ρ₁ "a" = some (.stdVecVal la) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "i" by decide) hu₁]
    exact ha
  have hb₁ : envLookup ρ₁ "b" = some (.stdVecVal lb) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("b" : String) ≠ "i" by decide) hu₁]
    exact hb
  have hout₁ : envLookup ρ₁ "out" = some (.stdVecVal lo) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "i" by decide) hu₁]
    exact hout
  have hjVar1 : evalExpr (.var "j") ρ₁ = .ok (.u64 jB) :=
    evalExpr_var_hit _ _ _ hj₁
  have hevJ : evalExpr
      (.uadd (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁ =
      .ok (.u64 (jB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hjVar1 (by simp [evalExpr, litVal])
  obtain ⟨ρ₂, hu₂⟩ := envUpdate_some_of_lookup ρ₁ "j"
    (.u64 jB) (.u64 (jB + 1)) hj₁
  have hstepJ := revAssign prog F "j"
    (.uadd (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁
    (.u64 (jB + 1)) ρ₂ hevJ hu₂
  have hiN' : (iB + 1).toNat = i + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hiN]
    exact Nat.mod_eq_of_lt (by omega)
  have hjN' : (jB + 1).toNat = j + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hjN]
    exact Nat.mod_eq_of_lt (by omega)
  have hif : evalProgStmt prog F vecDifferenceBody ρ =
      evalProgStmt prog F
        (.seq (.assign "i" (.uadd (.var "i")
                (.lit (.u64 (BitVec.ofNat 64 1)))))
          (.assign "j" (.uadd (.var "j")
                (.lit (.u64 (BitVec.ofNat 64 1)))))) ρ := by
    simp only [vecDifferenceBody]
    rw [evalProgStmt_if_false _ _ _ _ _ _ hcmp1]
    exact evalProgStmt_if_false _ _ _ _ _ _ hcmp2
  have hseq : evalProgStmt prog F
      (.seq (.assign "i" (.uadd (.var "i")
              (.lit (.u64 (BitVec.ofNat 64 1)))))
        (.assign "j" (.uadd (.var "j")
              (.lit (.u64 (BitVec.ofNat 64 1)))))) ρ =
      evalProgStmt prog F
        (.assign "j" (.uadd (.var "j")
                (.lit (.u64 (BitVec.ofNat 64 1))))) ρ₁ :=
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepI
  refine ⟨ρ₂, ?_, ?_, hiN', ?_, hjN', ?_, ?_, ?_, ?_⟩
  · rw [hif, hseq]
    exact hstepJ
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "j" by decide) hu₂]
    exact hi₁
  · rw [envLookup_update_hit _ _ _ _ hu₂]
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "j" by decide) hu₂,
      envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "i" by decide) hu₁]
    exact hw
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "j" by decide) hu₂,
      envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "i" by decide) hu₁]
    exact ha
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("b" : String) ≠ "j" by decide) hu₂,
      envLookup_update_miss _ _ _ _ _
      (show ("b" : String) ≠ "i" by decide) hu₁]
    exact hb
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "j" by decide) hu₂,
      envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "i" by decide) hu₁]
    exact hout

theorem valDifferenceDrainBody_hit (prog : Prog) (F : Nat)
    (ρ : Env) (la lb lo : List (BitVec 32)) (i w : Nat)
    (iB wB : BitVec 64) (x : BitVec 32) (jB : BitVec 64)
    (hiN : iB.toNat = i) (hwN : wB.toNat = w)
    (hla64 : la.length < 2 ^ 64)
    (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hgetA : la[i]? = some x)
    (hltA : i < la.length)
    (xO : BitVec 32) (hgetO : lo[w]? = some xO) (hwlt : w < lo.length) :
    ∃ ρ', evalProgStmt prog F vecDifferenceDrainBody ρ =
      .ok (ρ', .fellThrough) ∧
      envLookup ρ' "i" = some (.u64 (iB + 1)) ∧
      (iB + 1).toNat = i + 1 ∧
      envLookup ρ' "w" = some (.u64 (wB + 1)) ∧
      (wB + 1).toNat = w + 1 ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "b" = some (.stdVecVal lb) ∧
      envLookup ρ' "out" = some (.stdVecVal (lo.set w x)) ∧
      envLookup ρ' "j" = some (.u64 jB) := by
  have hiVar : evalExpr (.var "i") ρ = .ok (.u64 iB) :=
    evalExpr_var_hit _ _ _ hi
  have hgetA' : la[iB.toNat]? = some x := by rw [hiN]; exact hgetA
  have hatA : evalExpr (.stdVecAt "a" (.var "i")) ρ = .ok (.i32 x) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ ha hiVar hgetA'
  have hwVar : evalExpr (.var "w") ρ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw
  have hgetO' : lo[wB.toNat]? = some xO := by rw [hwN]; exact hgetO
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "out"
    (.stdVecVal lo) (.stdVecVal (lo.set wB.toNat x)) hout
  have hset := revVecSet prog F "out" (.var "w")
    (.stdVecAt "a" (.var "i")) ρ wB x lo xO ρ₁
    hwVar hatA hout hgetO' hu₁
  have hi₁ : envLookup ρ₁ "i" = some (.u64 iB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "out" by decide) hu₁]
    exact hi
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
  have hj₁ : envLookup ρ₁ "j" = some (.u64 jB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("j" : String) ≠ "out" by decide) hu₁]
    exact hj
  have hevI : evalExpr
      (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁ =
      .ok (.u64 (iB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hi₁) (by simp [evalExpr, litVal])
  obtain ⟨ρ₂, hu₂⟩ := envUpdate_some_of_lookup ρ₁ "i"
    (.u64 iB) (.u64 (iB + 1)) hi₁
  have hstepI := revAssign prog F "i"
    (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁
    (.u64 (iB + 1)) ρ₂ hevI hu₂
  have hw₂ : envLookup ρ₂ "w" = some (.u64 wB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "i" by decide) hu₂]
    exact hw₁
  have hj₂ : envLookup ρ₂ "j" = some (.u64 jB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("j" : String) ≠ "i" by decide) hu₂]
    exact hj₁
  have hout₂ : envLookup ρ₂ "out" =
      some (.stdVecVal (lo.set wB.toNat x)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "i" by decide) hu₂]
    exact envLookup_update_hit _ _ _ _ hu₁
  have hevW : evalExpr
      (.uadd (.var "w") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ =
      .ok (.u64 (wB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hw₂) (by simp [evalExpr, litVal])
  obtain ⟨ρ₃, hu₃⟩ := envUpdate_some_of_lookup ρ₂ "w"
    (.u64 wB) (.u64 (wB + 1)) hw₂
  have hstepW := revAssign prog F "w"
    (.uadd (.var "w") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂
    (.u64 (wB + 1)) ρ₃ hevW hu₃
  have hiN' : (iB + 1).toNat = i + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hiN]
    exact Nat.mod_eq_of_lt (by omega)
  have hwN' : (wB + 1).toNat = w + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hwN]
    exact Nat.mod_eq_of_lt (by omega)
  have hsetW : lo.set wB.toNat x = lo.set w x := by rw [hwN]
  have hseq0 : evalProgStmt prog F
      (.seq (.assign "i" (.uadd (.var "i")
                (.lit (.u64 (BitVec.ofNat 64 1)))))
        (.assign "w" (.uadd (.var "w")
                  (.lit (.u64 (BitVec.ofNat 64 1)))))) ρ₁ =
      evalProgStmt prog F
        (.assign "w" (.uadd (.var "w")
                (.lit (.u64 (BitVec.ofNat 64 1))))) ρ₂ := by
    exact evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepI
  refine ⟨ρ₃, ?_, ?_, hiN', ?_, hwN', ?_, ?_, ?_, ?_⟩
  · simp only [vecDifferenceDrainBody]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hset, hseq0]
    exact hstepW
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "w" by decide) hu₃]
    exact envLookup_update_hit _ _ _ _ hu₂
  · rw [envLookup_update_hit _ _ _ _ hu₃]
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "w" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "i" by decide) hu₂]
    exact ha₁
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("b" : String) ≠ "w" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("b" : String) ≠ "i" by decide) hu₂]
    exact hb₁
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "w" by decide) hu₃,
      ← hsetW]
    exact hout₂
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("j" : String) ≠ "w" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("j" : String) ≠ "i" by decide) hu₂]
    exact hj₁

/-! ## Value main loop -/

theorem valDifferenceMainLoop_ok (prog : Prog) (F G : Nat)
    (ρ : Env) (la lb lo : List (BitVec 32))
    (i j w : Nat) (iB jB wB : BitVec 64)
    (i' j' w' : Nat) (lo' : List (BitVec 32))
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
    (hcap : w + (la.length - i) ≤ lo.length)
    (hreadA : ∀ p, p < la.length → ∃ x, la[p]? = some x)
    (hreadB : ∀ p, p < lb.length → ∃ x, lb[p]? = some x)
    (hreadO : ∀ p, p < lo.length → ∃ x, lo[p]? = some x)
    (hfwd : differenceMainFwd la lb lo G i j w = .ok (i', j', w', lo')) :
    ∃ ρ', evalProgStmt prog F vecDifferenceMain ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "b" = some (.stdVecVal lb) ∧
      envLookup ρ' "out" = some (.stdVecVal lo') ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = i') ∧
      (∃ jB', envLookup ρ' "j" = some (.u64 jB') ∧ jB'.toNat = j') ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w') ∧
      w' + (la.length - i') ≤ lo'.length := by
  induction F generalizing G ρ la lb lo i j w iB jB wB with
  | zero =>
    have hgeA : la.length ≤ i := by omega
    have hguardF : evalExpr differenceGuard ρ = .ok (.b false) :=
      differenceGuard_eval_falseA ρ la lb i j iB jB hiN ha hi hla64 hgeA
    have hexit : evalProgStmt prog 0 vecDifferenceMain ρ =
        .ok (ρ, .fellThrough) :=
      evalProgStmt_while_false prog 0 _ _ _ hguardF
    have hpair : (i, j, w, lo) = (i', j', w', lo') := by
      cases G with
      | zero => simpa [differenceMainFwd] using hfwd
      | succ G =>
        have hnegA : ¬ i < la.length := by omega
        simpa [differenceMainFwd, dite_eq_right hnegA] using hfwd
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
    exact ⟨ρ, hexit, ha, hb, hout, ⟨iB, hi, hiN⟩, ⟨jB, hj, hjN⟩,
      ⟨wB, hw, hwN⟩, hcap⟩
  | succ F ih =>
    by_cases hltA : i < la.length
    · by_cases hltB : j < lb.length
      · obtain ⟨x, hgetA⟩ := hreadA i hltA
        obtain ⟨y, hgetB⟩ := hreadB j hltB
        have hguardT : evalExpr differenceGuard ρ = .ok (.b true) :=
          differenceGuard_eval_true ρ la lb i j iB jB hiN hjN ha hb hi hj
            hla64 hlb64 hltA hltB
        by_cases hlt : (x.slt y) = true
        · cir_fuel_step (F, G, (la.length - (i + 1)) + (lb.length - j))
          have hwlt : w < lo.length := by omega
          obtain ⟨xO, hgetO⟩ := hreadO w hwlt
          obtain ⟨ρ₁, hbody, hiB₁, hiN₁, hjB₁, hwB₁, hwN₁, ha₁, hb₁,
              hout₁⟩ :=
            valDifferenceMainBody_takeLeft prog F ρ la lb lo i j w iB jB wB x y
              hiN hjN hwN hla64 hlb64 hlo64 ha hb hout hi hj hw
              hgetA hgetB hltA hltB xO hgetO hwlt hlt
          have hfwd' : differenceMainFwd la lb (lo.set w x) G' (i + 1) j
              (w + 1) = .ok (i', j', w', lo') := by
            simpa [differenceMainFwd, dite_eq_left hltA, dite_eq_left hltB,
              hgetA, hgetB, hlt] using hfwd
          have hlenSet : (lo.set w x).length = lo.length :=
            List.length_set
          have hcap' : (w + 1) + (la.length - (i + 1)) ≤
              (lo.set w x).length := by
            rw [hlenSet]; omega
          have hlo64' : (lo.set w x).length < 2 ^ 64 := by
            rw [hlenSet]; exact hlo64
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
          obtain ⟨ρ', hloop, ha', hb', hout', ⟨iB', hiB', hiN'⟩,
              ⟨jB', hjB', hjN'⟩, ⟨wB', hwB', hwN'⟩, hcapI⟩ :=
            ih (G := G') (ρ := ρ₁) (la := la) (lb := lb)
              (lo := (lo.set w x))
              (i := i + 1) (j := j) (w := w + 1)
              (iB := iB + 1) (jB := jB) (wB := wB + 1)
              (hiN := hiN₁) (hjN := hjN) (hwN := hwN₁)
              (hla64 := hla64) (hlb64 := hlb64) (hlo64 := hlo64')
              (ha := ha₁) (hb := hb₁) (hout := hout₁)
              (hi := hiB₁) (hj := hjB₁) (hw := hwB₁)
              (hile := by omega) (hjle := hjle)
              (hF := hF') (hG := hG') (hcap := hcap')
              (hreadA := hreadA) (hreadB := hreadB) (hreadO := hreadO')
              (hfwd := hfwd')
          refine ⟨ρ', ?_, ha', hb', hout', ⟨iB', hiB', hiN'⟩,
            ⟨jB', hjB', hjN'⟩, ⟨wB', hwB', hwN'⟩, hcapI⟩
          have hwhile : evalProgStmt prog (F + 1) vecDifferenceMain ρ =
              evalProgStmt prog F vecDifferenceMain ρ₁ := by
            cir_unfold_prog (vecDifferenceMain, prog, F, hguardT, hbody)
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
              valDifferenceMainBody_advRight prog F ρ la lb lo i j w iB jB wB
                x y hiN hjN hwN hla64 hlb64 hlo64 ha hb hout hi hj hw
                hgetA hgetB hltA hltB hne hgt
            have hfwd' : differenceMainFwd la lb lo G' i (j + 1)
                w = .ok (i', j', w', lo') := by
              simpa [differenceMainFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hne, hgt] using hfwd
            obtain ⟨ρ', hloop, ha', hb', hout', ⟨iB', hiB', hiN'⟩,
                ⟨jB', hjB', hjN'⟩, ⟨wB', hwB', hwN'⟩, hcapI⟩ :=
              ih (G := G') (ρ := ρ₁) (la := la) (lb := lb)
                (lo := lo)
                (i := i) (j := j + 1) (w := w)
                (iB := iB) (jB := jB + 1) (wB := wB)
                (hiN := hiN) (hjN := hjN₁) (hwN := hwN)
                (hla64 := hla64) (hlb64 := hlb64) (hlo64 := hlo64)
                (ha := ha₁) (hb := hb₁) (hout := hout₁)
                (hi := hiB₁) (hj := hjB₁) (hw := hwB₁)
                (hile := hile) (hjle := by omega)
                (hF := hF') (hG := hG') (hcap := hcap)
                (hreadA := hreadA) (hreadB := hreadB) (hreadO := hreadO)
                (hfwd := hfwd')
            refine ⟨ρ', ?_, ha', hb', hout', ⟨iB', hiB', hiN'⟩,
              ⟨jB', hjB', hjN'⟩, ⟨wB', hwB', hwN'⟩, hcapI⟩
            have hwhile : evalProgStmt prog (F + 1) vecDifferenceMain ρ =
                evalProgStmt prog F vecDifferenceMain ρ₁ := by
              cir_unfold_prog (vecDifferenceMain, prog, F, hguardT, hbody)
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
            cir_fuel_step (F, G,
              (la.length - (i + 1)) + (lb.length - (j + 1)))
            obtain ⟨ρ₁, hbody, hiB₁, hiN₁, hjB₁, hjN₁, hwB₁,
                ha₁, hb₁, hout₁⟩ :=
              valDifferenceMainBody_skipBoth prog F ρ la lb lo i j w iB jB wB
                x y hiN hjN hwN hla64 hlb64 hlo64 ha hb hout hi hj hw
                hgetA hgetB hltA hltB hge1 hge2
            have hfwd' : differenceMainFwd la lb lo G' (i + 1) (j + 1)
                w = .ok (i', j', w', lo') := by
              simpa [differenceMainFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hge1, hge2] using hfwd
            have hcap' : w + (la.length - (i + 1)) ≤ lo.length := by
              omega
            obtain ⟨ρ', hloop, ha', hb', hout', ⟨iB', hiB', hiN'⟩,
                ⟨jB', hjB', hjN'⟩, ⟨wB', hwB', hwN'⟩, hcapI⟩ :=
              ih (G := G') (ρ := ρ₁) (la := la) (lb := lb)
                (lo := lo)
                (i := i + 1) (j := j + 1) (w := w)
                (iB := iB + 1) (jB := jB + 1) (wB := wB)
                (hiN := hiN₁) (hjN := hjN₁) (hwN := hwN)
                (hla64 := hla64) (hlb64 := hlb64) (hlo64 := hlo64)
                (ha := ha₁) (hb := hb₁) (hout := hout₁)
                (hi := hiB₁) (hj := hjB₁) (hw := hwB₁)
                (hile := by omega) (hjle := by omega)
                (hF := hF') (hG := hG') (hcap := hcap')
                (hreadA := hreadA) (hreadB := hreadB) (hreadO := hreadO)
                (hfwd := hfwd')
            refine ⟨ρ', ?_, ha', hb', hout', ⟨iB', hiB', hiN'⟩,
              ⟨jB', hjB', hjN'⟩, ⟨wB', hwB', hwN'⟩, hcapI⟩
            have hwhile : evalProgStmt prog (F + 1) vecDifferenceMain ρ =
                evalProgStmt prog F vecDifferenceMain ρ₁ := by
              cir_unfold_prog (vecDifferenceMain, prog, F, hguardT, hbody)
            rw [hwhile]
            exact hloop
      · have hgeB : lb.length ≤ j := by omega
        have hguardF : evalExpr differenceGuard ρ = .ok (.b false) :=
          differenceGuard_eval_falseB ρ la lb i j iB jB hiN hjN ha hb
            hi hj hla64 hlb64 hltA hgeB
        have hexit : evalProgStmt prog (F + 1) vecDifferenceMain ρ =
            .ok (ρ, .fellThrough) :=
          evalProgStmt_while_false prog (F + 1) _ _ _ hguardF
        have hpair : (i, j, w, lo) = (i', j', w', lo') := by
          cases G with
          | zero => simpa [differenceMainFwd] using hfwd
          | succ G =>
            have hnegB : ¬ j < lb.length := by omega
            simpa [differenceMainFwd, dite_eq_left hltA,
              dite_eq_right hnegB] using hfwd
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
        exact ⟨ρ, hexit, ha, hb, hout, ⟨iB, hi, hiN⟩, ⟨jB, hj, hjN⟩,
          ⟨wB, hw, hwN⟩, hcap⟩
    · have hgeA : la.length ≤ i := by omega
      have hguardF : evalExpr differenceGuard ρ = .ok (.b false) :=
        differenceGuard_eval_falseA ρ la lb i j iB jB hiN ha hi hla64 hgeA
      have hexit : evalProgStmt prog (F + 1) vecDifferenceMain ρ =
          .ok (ρ, .fellThrough) :=
        evalProgStmt_while_false prog (F + 1) _ _ _ hguardF
      have hpair : (i, j, w, lo) = (i', j', w', lo') := by
        cases G with
        | zero => simpa [differenceMainFwd] using hfwd
        | succ G =>
          have hnegA : ¬ i < la.length := by omega
          simpa [differenceMainFwd, dite_eq_right hnegA] using hfwd
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
      exact ⟨ρ, hexit, ha, hb, hout, ⟨iB, hi, hiN⟩, ⟨jB, hj, hjN⟩,
        ⟨wB, hw, hwN⟩, hcap⟩

/-! ## Value drain guard -/
/-- Drain-`a` guard evaluation: the `ult` reads the `a` length
    word and decides `i < a.size()`. -/
theorem differenceDrainGuard_eval (ρ : Env)
    (la : List (BitVec 32)) (i : Nat)
    (iB : BitVec 64)
    (hiN : iB.toNat = i)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hla64 : la.length < 2 ^ 64) :
    evalExpr (.ult (.var "i") (.stdVecLen "a")) ρ =
      .ok (.b (decide (i < la.length))) := by
  have hlenA : (BitVec.ofNat 64 la.length).toNat = la.length :=
    ofNat64_toNat _ (by omega)
  have hoLenA : evalExpr (.stdVecLen "a") ρ =
      .ok (.u64 (BitVec.ofNat 64 la.length)) :=
    evalExpr_stdVecLen_some _ _ _ ha
  have h := evalExpr_ult_u64 (.var "i") (.stdVecLen "a") ρ iB
    (BitVec.ofNat 64 la.length) (evalExpr_var_hit _ _ _ hi) hoLenA
  rw [BitVec.ult_eq_decide, hiN, hlenA] at h
  by_cases hlt : i < la.length
  · rw [decide_eq_true hlt] at h ⊢
    exact h
  · rw [decide_eq_false hlt] at h ⊢
    exact h

/-! ## Value drain loop -/
theorem valDifferenceDrainLoop_ok (prog : Prog) (F G : Nat)
    (ρ : Env) (la lb lo : List (BitVec 32))
    (i w : Nat) (iB wB : BitVec 64) (jB : BitVec 64)
    (i' w' : Nat) (lo' : List (BitVec 32))
    (hiN : iB.toNat = i) (hwN : wB.toNat = w)
    (hla64 : la.length < 2 ^ 64)
    (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hile : i ≤ la.length)
    (hF : la.length - i ≤ F)
    (hG : la.length - i ≤ G)
    (hcap : w + (la.length - i) ≤ lo.length)
    (hreadA : ∀ p, p < la.length → ∃ x, la[p]? = some x)
    (hreadO : ∀ p, p < lo.length → ∃ x, lo[p]? = some x)
    (hfwd : differenceDrainFwd la lo G i w = .ok (i', w', lo')) :
    ∃ ρ', evalProgStmt prog F vecDifferenceDrain ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "b" = some (.stdVecVal lb) ∧
      envLookup ρ' "out" = some (.stdVecVal lo') ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = i') ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w') ∧
      w' + (la.length - i') ≤ lo'.length ∧
      i ≤ i' ∧ w + (i' - i) = w' ∧
      envLookup ρ' "j" = some (.u64 jB) := by
  induction F generalizing G ρ la lb lo i w iB wB jB with
  | zero =>
    have hgeA : la.length ≤ i := by omega
    have hguardF : evalExpr (.ult (.var "i") (.stdVecLen "a")) ρ =
        .ok (.b false) := by
      have h := differenceDrainGuard_eval ρ la i iB hiN ha hi hla64
      rw [decide_eq_false (by omega : ¬ i < la.length)] at h
      exact h
    have hexit : evalProgStmt prog 0 vecDifferenceDrain ρ =
        .ok (ρ, .fellThrough) :=
      evalProgStmt_while_false prog 0 _ _ _ hguardF
    have hpair : (i, w, lo) = (i', w', lo') := by
      cases G with
      | zero => simpa [differenceDrainFwd] using hfwd
      | succ G =>
        have hnegA : ¬ i < la.length := by omega
        simpa [differenceDrainFwd, dite_eq_right hnegA] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    exact ⟨ρ, hexit, ha, hb, hout, ⟨iB, hi, hiN⟩, ⟨wB, hw, hwN⟩, hcap,
      by omega, by omega, hj⟩
  | succ F ih =>
    by_cases hltA : i < la.length
    · obtain ⟨x, hgetA⟩ := hreadA i hltA
      have hguardT : evalExpr (.ult (.var "i") (.stdVecLen "a")) ρ =
          .ok (.b true) := by
        have h := differenceDrainGuard_eval ρ la i iB hiN ha hi hla64
        rw [decide_eq_true hltA] at h
        exact h
      have hwlt : w < lo.length := by omega
      obtain ⟨xO, hgetO⟩ := hreadO w hwlt
      cir_fuel_step (F, G, la.length - (i + 1))
      obtain ⟨ρ₁, hbody, hiB₁, hiN₁, hwB₁, hwN₁, ha₁, hb₁, hout₁,
          hjbody⟩ :=
        valDifferenceDrainBody_hit prog F ρ la lb lo i w iB wB x jB
          hiN hwN hla64 hlo64 ha hb hout hi hw hj hgetA hltA
          xO hgetO hwlt
      have hfwd' : differenceDrainFwd la (lo.set w x) G' (i + 1) (w + 1) =
          .ok (i', w', lo') := by
        simpa [differenceDrainFwd, dite_eq_left hltA, hgetA] using hfwd
      have hlenSet : (lo.set w x).length = lo.length :=
        List.length_set
      have hcap' : (w + 1) + (la.length - (i + 1)) ≤
          (lo.set w x).length := by
        rw [hlenSet]; omega
      have hlo64' : (lo.set w x).length < 2 ^ 64 := by
        rw [hlenSet]; exact hlo64
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
      obtain ⟨ρ', hloop, ha', hb', hout', ⟨iB', hiB', hiN'⟩,
          ⟨wB', hwB', hwN'⟩, hcapI, hmonoI, hcntI, hj'⟩ :=
        ih (G := G') (ρ := ρ₁) (la := la) (lb := lb)
          (lo := (lo.set w x))
          (i := i + 1) (w := w + 1)
          (iB := iB + 1) (wB := wB + 1) (jB := jB)
          (hiN := hiN₁) (hwN := hwN₁)
          (hla64 := hla64) (hlo64 := hlo64')
          (ha := ha₁) (hb := hb₁) (hout := hout₁)
          (hi := hiB₁) (hw := hwB₁) (hj := hjbody)
          (hile := by omega)
          (hF := hF') (hG := hG') (hcap := hcap')
          (hreadA := hreadA) (hreadO := hreadO')
          (hfwd := hfwd')
      have hmono : i ≤ i' := by omega
      have hcnt : w + (i' - i) = w' := by omega
      refine ⟨ρ', ?_, ha', hb', hout', ⟨iB', hiB', hiN'⟩,
        ⟨wB', hwB', hwN'⟩, hcapI, hmono, hcnt, hj'⟩
      have hwhile : evalProgStmt prog (F + 1) vecDifferenceDrain ρ =
          evalProgStmt prog F vecDifferenceDrain ρ₁ := by
        cir_unfold_prog (vecDifferenceDrain, prog, F, hguardT, hbody)
      rw [hwhile]
      exact hloop
    · have hgeA : la.length ≤ i := by omega
      have hguardF : evalExpr (.ult (.var "i") (.stdVecLen "a")) ρ =
          .ok (.b false) := by
        have h := differenceDrainGuard_eval ρ la i iB hiN ha hi hla64
        rw [decide_eq_false (by omega : ¬ i < la.length)] at h
        exact h
      have hexit : evalProgStmt prog (F + 1) vecDifferenceDrain ρ =
          .ok (ρ, .fellThrough) :=
        evalProgStmt_while_false prog (F + 1) _ _ _ hguardF
      have hpair : (i, w, lo) = (i', w', lo') := by
        cases G with
        | zero => simpa [differenceDrainFwd] using hfwd
        | succ G =>
          have hnegA : ¬ i < la.length := by omega
          simpa [differenceDrainFwd, dite_eq_right hnegA] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      exact ⟨ρ, hexit, ha, hb, hout, ⟨iB, hi, hiN⟩, ⟨wB, hw, hwN⟩, hcap,
        by omega, by omega, hj⟩

/-! ## Forward model bounds -/


theorem differenceMainFwd_le (la lb : List (BitVec 32)) (F' i j w : Nat)
    (lo : List (BitVec 32)) (i' j' w' : Nat) (lo' : List (BitVec 32))
    (hi : i ≤ la.length) (hj : j ≤ lb.length)
    (hcap : w + (la.length - i) ≤ lo.length)
    (hfwd : differenceMainFwd la lb lo F' i j w = .ok (i', j', w', lo')) :
    i' ≤ la.length ∧ j' ≤ lb.length ∧ w' ≤ lo.length ∧
      lo'.length = lo.length := by
  induction F' generalizing lo i j w i' j' w' lo' with
  | zero =>
    simp only [differenceMainFwd, Except.ok.injEq, Prod.mk.injEq] at hfwd
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hfwd
    exact ⟨hi, hj, by omega, rfl⟩
  | succ F' ih =>
    by_cases hA : i < la.length
    · by_cases hB : j < lb.length
      · cases hAi : la[i]? with
        | none =>
          simp only [differenceMainFwd, dite_eq_left hA, dite_eq_left hB,
            hAi] at hfwd
          cases hfwd
        | some x =>
          cases hBj : lb[j]? with
          | none =>
            simp only [differenceMainFwd, dite_eq_left hA, dite_eq_left hB,
              hAi, hBj] at hfwd
            cases hfwd
          | some y =>
            have hset : (lo.set w x).length = lo.length :=
              List.length_set
            by_cases hlt : (x.slt y) = true
            · have h' : differenceMainFwd la lb (lo.set w x) F' (i + 1) j
                  (w + 1) = .ok (i', j', w', lo') := by
                simpa [differenceMainFwd, dite_eq_left hA, dite_eq_left hB,
                  hAi, hBj, hlt] using hfwd
              have hcapA : (w + 1) + (la.length - (i + 1)) ≤
                  (lo.set w x).length := by
                  rw [List.length_set]; omega
              obtain ⟨hi', hj', hw', hlen⟩ :=
                ih _ _ _ _ _ _ _ _ (by omega) hj hcapA h'
              exact ⟨hi', hj', hset ▸ hw', hlen.trans hset⟩
            · by_cases hgt : (y.slt x) = true
              · have hne : (x.slt y) = false := by
                  cases hxy : x.slt y with
                  | true => exact absurd hxy hlt
                  | false => rfl
                have h' : differenceMainFwd la lb lo F' i (j + 1)
                    w = .ok (i', j', w', lo') := by
                  simpa [differenceMainFwd, dite_eq_left hA, dite_eq_left hB,
                    hAi, hBj, hne, hgt] using hfwd
                obtain ⟨hi', hj', hw', hlen⟩ :=
                  ih _ _ _ _ _ _ _ _ hi (by omega) hcap h'
                exact ⟨hi', hj', hw', hlen⟩
              · have hne1 : (x.slt y) = false := by
                  cases hxy : x.slt y with
                  | true => exact absurd hxy hlt
                  | false => rfl
                have hne2 : (y.slt x) = false := by
                  cases hyx : y.slt x with
                  | true => exact absurd hyx hgt
                  | false => rfl
                have h' : differenceMainFwd la lb lo F' (i + 1)
                    (j + 1) w = .ok (i', j', w', lo') := by
                  simpa [differenceMainFwd, dite_eq_left hA, dite_eq_left hB,
                    hAi, hBj, hne1, hne2] using hfwd
                have hcapC : w + (la.length - (i + 1)) ≤ lo.length := by
                  omega
                obtain ⟨hi', hj', hw', hlen⟩ :=
                  ih _ _ _ _ _ _ _ _ (by omega) (by omega) hcapC h'
                exact ⟨hi', hj', hw', hlen⟩
      · simp only [differenceMainFwd, dite_eq_left hA,
          dite_eq_right hB] at hfwd
        simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hfwd
        exact ⟨hi, hj, by omega, rfl⟩
    · simp only [differenceMainFwd, dite_eq_right hA] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hfwd
      exact ⟨hi, hj, by omega, rfl⟩

/-- Drain-`a` model bounds. -/


theorem differenceDrainFwd_le (la : List (BitVec 32)) (F' i w : Nat)
    (lo : List (BitVec 32)) (i' w' : Nat) (lo' : List (BitVec 32))
    (hi : i ≤ la.length)
    (hcap : w + (la.length - i) ≤ lo.length)
    (hfwd : differenceDrainFwd la lo F' i w = .ok (i', w', lo')) :
    i' ≤ la.length ∧ w' ≤ lo.length ∧ lo'.length = lo.length := by
  induction F' generalizing lo i w i' w' lo' with
  | zero =>
    simp only [differenceDrainFwd, Except.ok.injEq, Prod.mk.injEq] at hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hfwd
    exact ⟨hi, by omega, rfl⟩
  | succ F' ih =>
    by_cases hA : i < la.length
    · cases hAi : la[i]? with
      | none =>
        simp only [differenceDrainFwd, dite_eq_left hA, hAi] at hfwd
        cases hfwd
      | some x =>
        have h' : differenceDrainFwd la (lo.set w x) F' (i + 1) (w + 1) =
            .ok (i', w', lo') := by
          simpa [differenceDrainFwd, dite_eq_left hA, hAi] using hfwd
        have hset : (lo.set w x).length = lo.length :=
          List.length_set
        have hcapA : (w + 1) + (la.length - (i + 1)) ≤
            (lo.set w x).length := by
            rw [List.length_set]; omega
        obtain ⟨hi', hw', hlen⟩ :=
          ih _ _ _ _ _ _ (by omega) hcapA h'
        exact ⟨hi', hset ▸ hw', hlen.trans hset⟩
    · simp only [differenceDrainFwd, dite_eq_right hA] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hfwd
      exact ⟨hi, by omega, rfl⟩

/-! ## Forward length preservation -/

theorem differenceMainFwd_length :
    ∀ (G : Nat) (la lb lo : List (BitVec 32)) (i j w i' j' w' : Nat)
      (lo' : List (BitVec 32)),
    differenceMainFwd la lb lo G i j w = .ok (i', j', w', lo') →
    lo'.length = lo.length := by
  intro G
  induction G with
  | zero =>
    intro la lb lo i j w i' j' w' lo' h
    have hpair : (i, j, w, lo) = (i', j', w', lo') := by
      simpa [differenceMainFwd] using h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
    rfl
  | succ G ih =>
    intro la lb lo i j w i' j' w' lo' h
    by_cases hltA : i < la.length
    · by_cases hltB : j < lb.length
      · obtain ⟨x, hgetA⟩ : ∃ x, la[i]? = some x :=
          ⟨la[i], List.getElem?_eq_getElem hltA⟩
        obtain ⟨y, hgetB⟩ : ∃ y, lb[j]? = some y :=
          ⟨lb[j], List.getElem?_eq_getElem hltB⟩
        by_cases hlt : (x.slt y) = true
        · have h' : differenceMainFwd la lb (lo.set w x) G (i + 1) j (w + 1) =
              .ok (i', j', w', lo') := by
            simpa [differenceMainFwd, dite_eq_left hltA, dite_eq_left hltB,
              hgetA, hgetB, hlt] using h
          have hlen := ih la lb (lo.set w x) (i + 1) j (w + 1)
            i' j' w' lo' h'
          rwa [List.length_set] at hlen
        · by_cases hgt : (y.slt x) = true
          · have h' : differenceMainFwd la lb lo G i (j + 1) w =
                .ok (i', j', w', lo') := by
              have hne : (x.slt y) = false := by
                cases hxy : x.slt y with
                | true => exact absurd hxy hlt
                | false => rfl
              simpa [differenceMainFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hne, hgt] using h
            exact ih la lb lo i (j + 1) w i' j' w' lo' h'
          · have h' : differenceMainFwd la lb lo G (i + 1) (j + 1) w =
                .ok (i', j', w', lo') := by
              have hne1 : (x.slt y) = false := by
                cases hxy : x.slt y with
                | true => exact absurd hxy hlt
                | false => rfl
              have hne2 : (y.slt x) = false := by
                cases hyx : y.slt x with
                | true => exact absurd hyx hgt
                | false => rfl
              simpa [differenceMainFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hne1, hne2] using h
            exact ih la lb lo (i + 1) (j + 1) w i' j' w' lo' h'
      · have hpair : (i, j, w, lo) = (i', j', w', lo') := by
          simpa [differenceMainFwd, dite_eq_left hltA,
            dite_eq_right hltB] using h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
        rfl
    · have hpair : (i, j, w, lo) = (i', j', w', lo') := by
        simpa [differenceMainFwd, dite_eq_right hltA] using h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
      rfl

/-- Drain-`a` length preservation: the survivor copy only ever
    `set`s inside `lo`. -/

theorem differenceDrainFwd_length :
    ∀ (G : Nat) (la lo : List (BitVec 32)) (i w i' w' : Nat)
      (lo' : List (BitVec 32)),
    differenceDrainFwd la lo G i w = .ok (i', w', lo') →
    lo'.length = lo.length := by
  intro G
  induction G with
  | zero =>
    intro la lo i w i' w' lo' h
    have hpair : (i, w, lo) = (i', w', lo') := by
      simpa [differenceDrainFwd] using h
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    rfl
  | succ G ih =>
    intro la lo i w i' w' lo' h
    by_cases hltA : i < la.length
    · obtain ⟨x, hgetA⟩ : ∃ x, la[i]? = some x :=
        ⟨la[i], List.getElem?_eq_getElem hltA⟩
      have h' : differenceDrainFwd la (lo.set w x) G (i + 1) (w + 1) =
          .ok (i', w', lo') := by
        simpa [differenceDrainFwd, dite_eq_left hltA, hgetA] using h
      have hlen := ih la (lo.set w x) (i + 1) (w + 1) i' w' lo' h'
      rwa [List.length_set] at hlen
    · have hpair : (i, w, lo) = (i', w', lo') := by
        simpa [differenceDrainFwd, dite_eq_right hltA] using h
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      rfl
