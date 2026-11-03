/-
Two-cursor sorted-range intersection (`std::set_intersection`
idiom) over `std::vector<int>` — the first two-input shape of the
pillar-2 run (P2-M11).

Corpus: `tests/cpp/vec_intersect.cpp` →
`tests/cir/vec_intersect.cir` (entry
`_Z13vec_intersectRSt6vectorIiSaIiEES2_S2_`: two single-ref
vectors plus one single-ref output vector in, `u64` count out;
a single `cir.while` whose guard is one `cir.ternary` over two
`lt` compares — the `&&` termination — with two `cir.if`
(the advance/equal three-way branch) and three non-const
`at()` call sites doubled by the guard reads).

Model: cursors `i`, `j` walk the sorted inputs, `w` records the
common words into the caller-sized output. At each step the
heads are compared signed: the smaller side advances, equal
heads write once and advance both (min-count multiplicity for
duplicates). Either cursor reaching the end stops the scan;
the inputs are sorted (caller debt). Unlike partial-sum, every
store is a plain `vecSet` — the model is total; unreachable
index failures stay loud `AssertFail`.
-/
import Circe.Emit.VecMergeInto
import Circe.Emit.VecReverse

/-- Function name (Itanium mangling of a `vec_intersect` free
    function taking three `vector<int>&`). -/
def vecIntersectName : String :=
  "_Z13vec_intersectRSt6vectorIiSaIiEES2_S2_"

/-- Loop guard: `i < a.size() && j < b.size()`, lowered by CIRGen
    as a short-circuit `cir.ternary` over the two `ult`s. -/
def intersectGuard : CExpr :=
  .tif (.ult (.var "i") (.stdVecLen "a"))
    (.ult (.var "j") (.stdVecLen "b"))
    (.lit (.b false))

/-- Loop body: three-way signed head compare — advance the smaller
    side, or write the common head once and advance both cursors
    plus the record cursor. -/
def vecIntersectBody : CStmt :=
  (.if_ (.slt (.stdVecAt "a" (.var "i"))
              (.stdVecAt "b" (.var "j")))
    (.assign "i" (.uadd (.var "i")
      (.lit (.u64 (BitVec.ofNat 64 1)))))
    (.if_ (.slt (.stdVecAt "b" (.var "j"))
                (.stdVecAt "a" (.var "i")))
      (.assign "j" (.uadd (.var "j")
        (.lit (.u64 (BitVec.ofNat 64 1)))))
      (.seq (.vecSet "out" (.var "w")
                (.stdVecAt "a" (.var "i")))
        (.seq (.assign "i" (.uadd (.var "i")
                  (.lit (.u64 (BitVec.ofNat 64 1)))))
          (.seq (.assign "j" (.uadd (.var "j")
                    (.lit (.u64 (BitVec.ofNat 64 1)))))
            (.assign "w" (.uadd (.var "w")
                      (.lit (.u64 (BitVec.ofNat 64 1))))))))))

/-- The intersection scan loop. -/
def vecIntersectLoop : CStmt :=
  .while_ intersectGuard vecIntersectBody

/-! ## Forward model (value level) -/

/-- Forward scan: cursors `i`, `j` walk the sorted inputs, `w`
    records common words into `lo`. Either cursor reaching its
    end stops the scan. Total: every index failure is guarded
    away, so the only error arm is the unreachable `AssertFail`. -/
def intersectFwd :
    List (BitVec 32) → List (BitVec 32) → List (BitVec 32) →
    Nat → Nat → Nat → Nat → Result (Nat × Nat × Nat × List (BitVec 32))
  | la, lb, lo, 0, i, j, w => .ok (i, j, w, lo)
  | la, lb, lo, fuel + 1, i, j, w =>
    if _ : i < la.length then
      if _ : j < lb.length then
        match la[i]?, lb[j]? with
        | some x, some y =>
          if x.slt y then intersectFwd la lb lo fuel (i + 1) j w
          else if y.slt x then intersectFwd la lb lo fuel i (j + 1) w
          else intersectFwd la lb (lo.set w x) fuel (i + 1) (j + 1) (w + 1)
        | _, _ => .error .AssertFail
      else .ok (i, j, w, lo)
    else .ok (i, j, w, lo)

/-- Whole-function forward: cursors from zero, empty record. -/
def vecIntersectFwd (la lb : List (BitVec 32))
    (lo : List (BitVec 32)) : Result Value :=
  match intersectFwd la lb lo (la.length + lb.length + 1) 0 0 0 with
  | .error e => .error e
  | .ok (_, _, w, _) => .ok (.u64 (BitVec.ofNat 64 w))

/-! ## Loop environment -/

/-- Loop environment (borrowed words + `u64` cursors), in prelude
    `let_` cons order (`w` over `j` over `i` over `[a, b, out]`,
    so the entry bridge is `rfl`). -/
def mkIntersectEnv (la lb lo : List (BitVec 32))
    (i j w : BitVec 64) : Env :=
  [("w", .u64 w), ("j", .u64 j), ("i", .u64 i),
   ("a", .stdVecVal la), ("b", .stdVecVal lb),
   ("out", .stdVecVal lo)]

theorem mkIntersectEnv_a (la lb lo : List (BitVec 32))
    (i j w : BitVec 64) :
    envLookup (mkIntersectEnv la lb lo i j w) "a" =
      some (.stdVecVal la) := by
  simp [mkIntersectEnv, envLookup]

theorem mkIntersectEnv_b (la lb lo : List (BitVec 32))
    (i j w : BitVec 64) :
    envLookup (mkIntersectEnv la lb lo i j w) "b" =
      some (.stdVecVal lb) := by
  simp [mkIntersectEnv, envLookup]

theorem mkIntersectEnv_out (la lb lo : List (BitVec 32))
    (i j w : BitVec 64) :
    envLookup (mkIntersectEnv la lb lo i j w) "out" =
      some (.stdVecVal lo) := by
  simp [mkIntersectEnv, envLookup]

theorem mkIntersectEnv_i (la lb lo : List (BitVec 32))
    (i j w : BitVec 64) :
    envLookup (mkIntersectEnv la lb lo i j w) "i" =
      some (.u64 i) := by
  simp [mkIntersectEnv, envLookup]

theorem mkIntersectEnv_j (la lb lo : List (BitVec 32))
    (i j w : BitVec 64) :
    envLookup (mkIntersectEnv la lb lo i j w) "j" =
      some (.u64 j) := by
  simp [mkIntersectEnv, envLookup]

theorem mkIntersectEnv_w (la lb lo : List (BitVec 32))
    (i j w : BitVec 64) :
    envLookup (mkIntersectEnv la lb lo i j w) "w" =
      some (.u64 w) := by
  simp [mkIntersectEnv, envLookup]

/-! ## Guard evaluation -/

/-- The guard holds when both cursors are in bounds: `tif` takes
    the second `ult` without touching the vectors. -/
theorem intersectGuard_eval_true (ρ : Env)
    (la lb : List (BitVec 32)) (i j : Nat)
    (iB jB : BitVec 64)
    (hiN : iB.toNat = i) (hjN : jB.toNat = j)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hla64 : la.length < 2 ^ 64) (hlb64 : lb.length < 2 ^ 64)
    (hltA : i < la.length) (hltB : j < lb.length) :
    evalExpr intersectGuard ρ = .ok (.b true) := by
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
  simp only [intersectGuard]
  rw [evalExpr_tif_true _ _ _ _ e1]
  exact e2

/-- The guard fails when `i` is exhausted: `tif` takes the else
    branch without touching `b`. -/
theorem intersectGuard_eval_falseA (ρ : Env)
    (la lb : List (BitVec 32)) (i j : Nat)
    (iB jB : BitVec 64)
    (hiN : iB.toNat = i)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hla64 : la.length < 2 ^ 64)
    (hgeA : la.length ≤ i) :
    evalExpr intersectGuard ρ = .ok (.b false) := by
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
  simp only [intersectGuard]
  rw [evalExpr_tif_false _ _ _ _ e1]
  exact evalExpr_lit _ _

/-- The guard fails when `j` is exhausted but `i` is not: `tif`
    runs the second `ult` and takes the else branch. -/
theorem intersectGuard_eval_falseB (ρ : Env)
    (la lb : List (BitVec 32)) (i j : Nat)
    (iB jB : BitVec 64)
    (hiN : iB.toNat = i) (hjN : jB.toNat = j)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hla64 : la.length < 2 ^ 64) (hlb64 : lb.length < 2 ^ 64)
    (hltA : i < la.length) (hgeB : lb.length ≤ j) :
    evalExpr intersectGuard ρ = .ok (.b false) := by
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
  simp only [intersectGuard]
  rw [evalExpr_tif_true _ _ _ _ e1]
  exact e2

/-- Canonical function: two shared-borrow inputs, one `mutBorrow`
    output, `u64` survivor count out. -/
def vecIntersectFunc : Func :=
  ⟨vecIntersectName,
   [{ name := "a", ty := stdVecObjTy, role := .sharedBorrow },
    { name := "b", ty := stdVecObjTy, role := .sharedBorrow },
    { name := "out", ty := stdVecObjTy, role := .mutBorrow 0 }],
   .u 64,
   (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
     (.seq (.let_ "j" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
       (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
         (.seq vecIntersectLoop
           (.return_ (.var "w"))))))⟩

/-- Program over which the entry evaluates (no callees). -/
abbrev vecIntersectProg : Prog := [vecIntersectFunc]

/-! ## Value body steps -/

/-- One body iteration, advance-`i` branch: `a[i] < b[j]` holds,
    so only the `i` cursor bumps. -/
theorem valIntersectBody_advI (prog : Prog) (F : Nat)
    (ρ : Env) (la lb lo : List (BitVec 32)) (i j w : Nat)
    (iB jB wB : BitVec 64) (x y : BitVec 32)
    (hiN : iB.toNat = i) (hjN : jB.toNat = j) (hwN : wB.toNat = w)
    (hla64 : la.length < 2 ^ 64)
    (hlb64 : lb.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hgetA : la[i]? = some x) (hgetB : lb[j]? = some y)
    (hltA : i < la.length) (hltB : j < lb.length)
    (hlt : (x.slt y) = true) :
    ∃ ρ', evalProgStmt prog F vecIntersectBody ρ =
      .ok (ρ', .fellThrough) ∧
      envLookup ρ' "i" = some (.u64 (iB + 1)) ∧
      (iB + 1).toNat = i + 1 ∧
      envLookup ρ' "j" = some (.u64 jB) ∧
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
  have hcmp : evalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "b" (.var "j")))
      ρ = .ok (.b true) := by
    rw [evalExpr_slt_i32 _ _ _ _ _ hatA hatB, hlt]
  have hevI : evalExpr
      (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ =
      .ok (.u64 (iB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hi) (by simp [evalExpr, litVal])
  obtain ⟨ρ', hu⟩ := envUpdate_some_of_lookup ρ "i"
    (.u64 iB) (.u64 (iB + 1)) hi
  have hstep := revAssign prog F "i"
    (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ
    (.u64 (iB + 1)) ρ' hevI hu
  have hif : evalProgStmt prog F vecIntersectBody ρ =
      evalProgStmt prog F
        (.assign "i" (.uadd (.var "i")
          (.lit (.u64 (BitVec.ofNat 64 1))))) ρ := by
    simp only [vecIntersectBody]
    exact evalProgStmt_if_true _ _ _ _ _ _ hcmp
  have hiN' : (iB + 1).toNat = i + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hiN]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨ρ', ?_, ?_, hiN', ?_, ?_, ?_, ?_, ?_⟩
  · rw [hif]; exact hstep
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

/-- One body iteration, advance-`j` branch: `a[i] < b[j]` fails
    but `b[j] < a[i]` holds, so only the `j` cursor bumps. -/
theorem valIntersectBody_advJ (prog : Prog) (F : Nat)
    (ρ : Env) (la lb lo : List (BitVec 32)) (i j w : Nat)
    (iB jB wB : BitVec 64) (x y : BitVec 32)
    (hiN : iB.toNat = i) (hjN : jB.toNat = j) (hwN : wB.toNat = w)
    (hlb64 : lb.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hgetA : la[i]? = some x) (hgetB : lb[j]? = some y)
    (hltA : i < la.length) (hltB : j < lb.length)
    (hge1 : (x.slt y) = false) (hlt2 : (y.slt x) = true) :
    ∃ ρ', evalProgStmt prog F vecIntersectBody ρ =
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
    rw [evalExpr_slt_i32 _ _ _ _ _ hatA hatB, hge1]
  have hcmp2 : evalExpr
      (.slt (.stdVecAt "b" (.var "j")) (.stdVecAt "a" (.var "i")))
      ρ = .ok (.b true) := by
    rw [evalExpr_slt_i32 _ _ _ _ _ hatB hatA, hlt2]
  have hevJ : evalExpr
      (.uadd (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ =
      .ok (.u64 (jB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hj) (by simp [evalExpr, litVal])
  obtain ⟨ρ', hu⟩ := envUpdate_some_of_lookup ρ "j"
    (.u64 jB) (.u64 (jB + 1)) hj
  have hstep := revAssign prog F "j"
    (.uadd (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ
    (.u64 (jB + 1)) ρ' hevJ hu
  have hif : evalProgStmt prog F vecIntersectBody ρ =
      evalProgStmt prog F
        (.assign "j" (.uadd (.var "j")
          (.lit (.u64 (BitVec.ofNat 64 1))))) ρ := by
    simp only [vecIntersectBody]
    rw [evalProgStmt_if_false _ _ _ _ _ _ hcmp1]
    exact evalProgStmt_if_true _ _ _ _ _ _ hcmp2
  have hjN' : (jB + 1).toNat = j + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hjN]
    exact Nat.mod_eq_of_lt (by omega)
  refine ⟨ρ', ?_, ?_, ?_, hjN', ?_, ?_, ?_, ?_⟩
  · rw [hif]; exact hstep
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

/-- One body iteration, write branch: neither head is smaller, so
    the common head is recorded once and all three cursors bump. -/
theorem valIntersectBody_write (prog : Prog) (F : Nat)
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
    (hge1 : (x.slt y) = false) (hge2 : (y.slt x) = false) :
    ∃ ρ', evalProgStmt prog F vecIntersectBody ρ =
      .ok (ρ', .fellThrough) ∧
      envLookup ρ' "i" = some (.u64 (iB + 1)) ∧
      (iB + 1).toNat = i + 1 ∧
      envLookup ρ' "j" = some (.u64 (jB + 1)) ∧
      (jB + 1).toNat = j + 1 ∧
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
  have hcmp1 : evalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "b" (.var "j")))
      ρ = .ok (.b false) := by
    rw [evalExpr_slt_i32 _ _ _ _ _ hatA hatB, hge1]
  have hcmp2 : evalExpr
      (.slt (.stdVecAt "b" (.var "j")) (.stdVecAt "a" (.var "i")))
      ρ = .ok (.b false) := by
    rw [evalExpr_slt_i32 _ _ _ _ _ hatB hatA, hge2]
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
  have hevJ : evalExpr
      (.uadd (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂ =
      .ok (.u64 (jB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hj₂) (by simp [evalExpr, litVal])
  obtain ⟨ρ₃, hu₃⟩ := envUpdate_some_of_lookup ρ₂ "j"
    (.u64 jB) (.u64 (jB + 1)) hj₂
  have hstepJ := revAssign prog F "j"
    (.uadd (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₂
    (.u64 (jB + 1)) ρ₃ hevJ hu₃
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
  obtain ⟨ρ₄, hu₄⟩ := envUpdate_some_of_lookup ρ₃ "w"
    (.u64 wB) (.u64 (wB + 1)) hw₃
  have hstepW := revAssign prog F "w"
    (.uadd (.var "w") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₃
    (.u64 (wB + 1)) ρ₄ hevW hu₄
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
  have hif : evalProgStmt prog F vecIntersectBody ρ =
      evalProgStmt prog F
        (.seq (.vecSet "out" (.var "w")
                 (.stdVecAt "a" (.var "i")))
          (.seq (.assign "i" (.uadd (.var "i")
                    (.lit (.u64 (BitVec.ofNat 64 1)))))
            (.seq (.assign "j" (.uadd (.var "j")
                      (.lit (.u64 (BitVec.ofNat 64 1)))))
              (.assign "w" (.uadd (.var "w")
                        (.lit (.u64 (BitVec.ofNat 64 1)))))))) ρ := by
    simp only [vecIntersectBody]
    rw [evalProgStmt_if_false _ _ _ _ _ _ hcmp1,
      evalProgStmt_if_false _ _ _ _ _ _ hcmp2]
  have hsetW : lo.set wB.toNat x = lo.set w x := by rw [hwN]
  have hseq1 : evalProgStmt prog F
      (.seq (.assign "j" (.uadd (.var "j")
                (.lit (.u64 (BitVec.ofNat 64 1)))))
        (.assign "w" (.uadd (.var "w")
                  (.lit (.u64 (BitVec.ofNat 64 1)))))) ρ₂ =
      evalProgStmt prog F
        (.assign "w" (.uadd (.var "w")
                (.lit (.u64 (BitVec.ofNat 64 1))))) ρ₃ := by
    exact evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepJ
  have hseq0 : evalProgStmt prog F
      (.seq (.assign "i" (.uadd (.var "i")
                (.lit (.u64 (BitVec.ofNat 64 1)))))
        (.seq (.assign "j" (.uadd (.var "j")
                  (.lit (.u64 (BitVec.ofNat 64 1)))))
          (.assign "w" (.uadd (.var "w")
                    (.lit (.u64 (BitVec.ofNat 64 1))))))) ρ₁ =
      evalProgStmt prog F
        (.assign "w" (.uadd (.var "w")
                (.lit (.u64 (BitVec.ofNat 64 1))))) ρ₃ := by
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepI]
    exact hseq1
  refine ⟨ρ₄, ?_, ?_, hiN', ?_, hjN', ?_, hwN', ?_, ?_, ?_⟩
  · rw [hif,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hset,
      hseq0]
    exact hstepW
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
      ← hsetW]
    exact hout₃

/-! ## Value loop -/

/-- Forward length preservation: the scan only ever `set`s inside
    `lo`, so the recorded list keeps its length on the ok path. -/
theorem intersectFwd_length :
    ∀ (G : Nat) (la lb lo : List (BitVec 32)) (i j w i' j' w' : Nat)
      (lo' : List (BitVec 32)),
    intersectFwd la lb lo G i j w = .ok (i', j', w', lo') →
    lo'.length = lo.length := by
  intro G
  induction G with
  | zero =>
    intro la lb lo i j w i' j' w' lo' h
    have hpair : (i, j, w, lo) = (i', j', w', lo') := by
      simpa [intersectFwd] using h
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
        · have h' : intersectFwd la lb lo G (i + 1) j w =
              .ok (i', j', w', lo') := by
            simpa [intersectFwd, dite_eq_left hltA, dite_eq_left hltB,
              hgetA, hgetB, hlt] using h
          exact ih la lb lo (i + 1) j w i' j' w' lo' h'
        · by_cases hgt : (y.slt x) = true
          · have h' : intersectFwd la lb lo G i (j + 1) w =
                .ok (i', j', w', lo') := by
              have hne : (x.slt y) = false := by
                cases hxy : x.slt y with
                | true => exact absurd hxy hlt
                | false => rfl
              simpa [intersectFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hne, hgt] using h
            exact ih la lb lo i (j + 1) w i' j' w' lo' h'
          · have h' : intersectFwd la lb (lo.set w x) G (i + 1) (j + 1) (w + 1) =
                .ok (i', j', w', lo') := by
              have hne1 : (x.slt y) = false := by
                cases hxy : x.slt y with
                | true => exact absurd hxy hlt
                | false => rfl
              have hne2 : (y.slt x) = false := by
                cases hyx : y.slt x with
                | true => exact absurd hyx hgt
                | false => rfl
              simpa [intersectFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hne1, hne2] using h
            have hlen := ih la lb (lo.set w x) (i + 1) (j + 1) (w + 1)
              i' j' w' lo' h'
            rwa [List.length_set] at hlen
      · have hpair : (i, j, w, lo) = (i', j', w', lo') := by
          simpa [intersectFwd, dite_eq_left hltA,
            dite_eq_right hltB] using h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
        rfl
    · have hpair : (i, j, w, lo) = (i', j', w', lo') := by
        simpa [intersectFwd, dite_eq_right hltA] using h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
      rfl

/-- Value loop: the scan runs to cursor exhaustion and the
    environment matches the forward model (fuel induction threading
    the body hits; the forward equation unfolds one step per
    branch). The capacity invariant `hcap` keeps one free slot in
    `lo` ahead of the worst case, so every write is in bounds. -/
theorem valIntersectLoop_ok (prog : Prog) (F G : Nat)
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
    (hcap : w + min (la.length - i) (lb.length - j) ≤ lo.length)
    (hreadA : ∀ p, p < la.length → ∃ x, la[p]? = some x)
    (hreadB : ∀ p, p < lb.length → ∃ x, lb[p]? = some x)
    (hreadO : ∀ p, p < lo.length → ∃ x, lo[p]? = some x)
    (hfwd : intersectFwd la lb lo G i j w = .ok (i', j', w', lo')) :
    ∃ ρ', evalProgStmt prog F vecIntersectLoop ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "b" = some (.stdVecVal lb) ∧
      envLookup ρ' "out" = some (.stdVecVal lo') ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = i') ∧
      (∃ jB', envLookup ρ' "j" = some (.u64 jB') ∧ jB'.toNat = j') ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w') ∧
      w' + min (la.length - i') (lb.length - j') ≤ lo'.length := by
  induction F generalizing G ρ la lb lo i j w iB jB wB with
  | zero =>
    have hgeA : la.length ≤ i := by omega
    have hguardF : evalExpr intersectGuard ρ = .ok (.b false) :=
      intersectGuard_eval_falseA ρ la lb i j iB jB hiN ha hi hla64 hgeA
    have hexit : evalProgStmt prog 0 vecIntersectLoop ρ =
        .ok (ρ, .fellThrough) :=
      evalProgStmt_while_false prog 0 _ _ _ hguardF
    have hpair : (i, j, w, lo) = (i', j', w', lo') := by
      cases G with
      | zero => simpa [intersectFwd] using hfwd
      | succ G =>
        have hnegA : ¬ i < la.length := by omega
        simpa [intersectFwd, dite_eq_right hnegA] using hfwd
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
    exact ⟨ρ, hexit, ha, hb, hout, ⟨iB, hi, hiN⟩, ⟨jB, hj, hjN⟩,
      ⟨wB, hw, hwN⟩, hcap⟩
  | succ F ih =>
    by_cases hltA : i < la.length
    · by_cases hltB : j < lb.length
      · obtain ⟨x, hgetA⟩ := hreadA i hltA
        obtain ⟨y, hgetB⟩ := hreadB j hltB
        have hguardT : evalExpr intersectGuard ρ = .ok (.b true) :=
          intersectGuard_eval_true ρ la lb i j iB jB hiN hjN ha hb hi hj
            hla64 hlb64 hltA hltB
        by_cases hlt : (x.slt y) = true
        · cir_fuel_step (F, G, (la.length - (i + 1)) + (lb.length - j))
          obtain ⟨ρ₁, hbody, hiB₁, hiN₁, hjB₁, hwB₁, ha₁, hb₁,
              hout₁⟩ :=
            valIntersectBody_advI prog F ρ la lb lo i j w iB jB wB x y
              hiN hjN hwN hla64 hlb64 ha hb hout hi hj hw
              hgetA hgetB hltA hltB hlt
          have hfwd' : intersectFwd la lb lo G' (i + 1) j w =
              .ok (i', j', w', lo') := by
            simpa [intersectFwd, dite_eq_left hltA, dite_eq_left hltB,
              hgetA, hgetB, hlt] using hfwd
          have hcap' : w + min (la.length - (i + 1)) (lb.length - j) ≤
              lo.length := by
            omega
          obtain ⟨ρ', hloop, ha', hb', hout', ⟨iB', hiB', hiN'⟩,
              ⟨jB', hjB', hjN'⟩, ⟨wB', hwB', hwN'⟩, hcapI⟩ :=
            ih (G := G') (ρ := ρ₁) (la := la) (lb := lb) (lo := lo)
              (i := i + 1) (j := j) (w := w)
              (iB := iB + 1) (jB := jB) (wB := wB)
              (hiN := hiN₁) (hjN := hjN) (hwN := hwN)
              (hla64 := hla64) (hlb64 := hlb64) (hlo64 := hlo64)
              (ha := ha₁) (hb := hb₁) (hout := hout₁)
              (hi := hiB₁) (hj := hjB₁) (hw := hwB₁)
              (hile := by omega) (hjle := hjle)
              (hF := hF') (hG := hG') (hcap := hcap')
              (hreadA := hreadA) (hreadB := hreadB) (hreadO := hreadO)
              (hfwd := hfwd')
          refine ⟨ρ', ?_, ha', hb', hout', ⟨iB', hiB', hiN'⟩,
            ⟨jB', hjB', hjN'⟩, ⟨wB', hwB', hwN'⟩, hcapI⟩
          have hwhile : evalProgStmt prog (F + 1) vecIntersectLoop ρ =
              evalProgStmt prog F vecIntersectLoop ρ₁ := by
            cir_unfold_prog (vecIntersectLoop, prog, F, hguardT, hbody)
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
              valIntersectBody_advJ prog F ρ la lb lo i j w iB jB wB x y
                hiN hjN hwN hlb64 ha hb hout hi hj hw
                hgetA hgetB hltA hltB hne hgt
            have hfwd' : intersectFwd la lb lo G' i (j + 1) w =
                .ok (i', j', w', lo') := by
              simpa [intersectFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hne, hgt] using hfwd
            have hcap' : w + min (la.length - i) (lb.length - (j + 1)) ≤
                lo.length := by
              omega
            obtain ⟨ρ', hloop, ha', hb', hout', ⟨iB', hiB', hiN'⟩,
                ⟨jB', hjB', hjN'⟩, ⟨wB', hwB', hwN'⟩, hcapI⟩ :=
              ih (G := G') (ρ := ρ₁) (la := la) (lb := lb) (lo := lo)
                (i := i) (j := j + 1) (w := w)
                (iB := iB) (jB := jB + 1) (wB := wB)
                (hiN := hiN) (hjN := hjN₁) (hwN := hwN)
                (hla64 := hla64) (hlb64 := hlb64) (hlo64 := hlo64)
                (ha := ha₁) (hb := hb₁) (hout := hout₁)
                (hi := hiB₁) (hj := hjB₁) (hw := hwB₁)
                (hile := hile) (hjle := by omega)
                (hF := hF') (hG := hG') (hcap := hcap')
                (hreadA := hreadA) (hreadB := hreadB) (hreadO := hreadO)
                (hfwd := hfwd')
            refine ⟨ρ', ?_, ha', hb', hout', ⟨iB', hiB', hiN'⟩,
              ⟨jB', hjB', hjN'⟩, ⟨wB', hwB', hwN'⟩, hcapI⟩
            have hwhile : evalProgStmt prog (F + 1) vecIntersectLoop ρ =
                evalProgStmt prog F vecIntersectLoop ρ₁ := by
              cir_unfold_prog (vecIntersectLoop, prog, F, hguardT, hbody)
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
            obtain ⟨ρ₁, hbody, hiB₁, hiN₁, hjB₁, hjN₁, hwB₁, hwN₁,
                ha₁, hb₁, hout₁⟩ :=
              valIntersectBody_write prog F ρ la lb lo i j w iB jB wB x y
                hiN hjN hwN hla64 hlb64 hlo64 ha hb hout hi hj hw
                hgetA hgetB hltA hltB xO hgetO hwlt hge1 hge2
            have hfwd' : intersectFwd la lb (lo.set w x) G' (i + 1) (j + 1)
                (w + 1) = .ok (i', j', w', lo') := by
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
                (i := i + 1) (j := j + 1) (w := w + 1)
                (iB := iB + 1) (jB := jB + 1) (wB := wB + 1)
                (hiN := hiN₁) (hjN := hjN₁) (hwN := hwN₁)
                (hla64 := hla64) (hlb64 := hlb64) (hlo64 := hlo64')
                (ha := ha₁) (hb := hb₁) (hout := hout₁)
                (hi := hiB₁) (hj := hjB₁) (hw := hwB₁)
                (hile := by omega) (hjle := by omega)
                (hF := hF') (hG := hG') (hcap := hcap')
                (hreadA := hreadA) (hreadB := hreadB) (hreadO := hreadO')
                (hfwd := hfwd')
            refine ⟨ρ', ?_, ha', hb', hout', ⟨iB', hiB', hiN'⟩,
              ⟨jB', hjB', hjN'⟩, ⟨wB', hwB', hwN'⟩, hcapI⟩
            have hwhile : evalProgStmt prog (F + 1) vecIntersectLoop ρ =
                evalProgStmt prog F vecIntersectLoop ρ₁ := by
              cir_unfold_prog (vecIntersectLoop, prog, F, hguardT, hbody)
            rw [hwhile]
            exact hloop
      · have hgeB : lb.length ≤ j := by omega
        have hguardF : evalExpr intersectGuard ρ = .ok (.b false) :=
          intersectGuard_eval_falseB ρ la lb i j iB jB hiN hjN ha hb
            hi hj hla64 hlb64 hltA hgeB
        have hexit : evalProgStmt prog (F + 1) vecIntersectLoop ρ =
            .ok (ρ, .fellThrough) :=
          evalProgStmt_while_false prog (F + 1) _ _ _ hguardF
        have hpair : (i, j, w, lo) = (i', j', w', lo') := by
          cases G with
          | zero => simpa [intersectFwd] using hfwd
          | succ G =>
            have hnegB : ¬ j < lb.length := by omega
            simpa [intersectFwd, dite_eq_left hltA,
              dite_eq_right hnegB] using hfwd
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
        exact ⟨ρ, hexit, ha, hb, hout, ⟨iB, hi, hiN⟩, ⟨jB, hj, hjN⟩,
          ⟨wB, hw, hwN⟩, hcap⟩
    · have hgeA : la.length ≤ i := by omega
      have hguardF : evalExpr intersectGuard ρ = .ok (.b false) :=
        intersectGuard_eval_falseA ρ la lb i j iB jB hiN ha hi hla64 hgeA
      have hexit : evalProgStmt prog (F + 1) vecIntersectLoop ρ =
          .ok (ρ, .fellThrough) :=
        evalProgStmt_while_false prog (F + 1) _ _ _ hguardF
      have hpair : (i, j, w, lo) = (i', j', w', lo') := by
        cases G with
        | zero => simpa [intersectFwd] using hfwd
        | succ G =>
          have hnegA : ¬ i < la.length := by omega
          simpa [intersectFwd, dite_eq_right hnegA] using hfwd
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
      exact ⟨ρ, hexit, ha, hb, hout, ⟨iB, hi, hiN⟩, ⟨jB, hj, hjN⟩,
        ⟨wB, hw, hwN⟩, hcap⟩
