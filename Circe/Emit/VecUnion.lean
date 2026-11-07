/-
Two-cursor sorted-range union (`std::set_union` idiom) over
`std::vector<int>` — the second two-input shape of the pillar-2
run (P2-M14).

Corpus: `tests/cpp/vec_union.cpp` →
`tests/cir/vec_union.cir` (entry
`_Z9vec_unionRSt6vectorIiSaIiEES2_S2_`: two single-ref
vectors plus one single-ref output vector in, `u64` count out;
one `cir.ternary` over the `&&` guard, three `cir.while` (the
main two-pointer loop plus the two survivor drains), two
`cir.if` (the three-way branch: the outer `if` plus the `else
if` nested in its else region), six `lt` compares, eighteen
`cir.call @` (four `size` + fourteen non-const `at()`)).

Model: cursors `i`, `j` walk the sorted inputs, `w` records the
union heads into the caller-sized output. At each step the
heads are compared signed: the strictly smaller head is
recorded and its side advances; equal heads record once and
advance both (max-count multiplicity for duplicates). Either
cursor reaching the end stops the main scan; each drain copies
its survivor suffix. The caller owes
`a.size() + b.size()` output slots. The inputs are sorted
(caller debt). Like intersection, every store is a plain
`vecSet` — the model is total; the record capacity is a
hypothesis, unreachable index failures stay loud `AssertFail`.
-/
import Circe.Emit.VecMergeInto
import Circe.Emit.VecReverse

/-- Function name (Itanium mangling of a `vec_union` free
    function taking three `vector<int>&`). -/
def vecUnionName : String :=
  "_Z9vec_unionRSt6vectorIiSaIiEES2_S2_"

/-- Main-loop guard: `i < a.size() && j < b.size()`, lowered by
    CIRGen as a short-circuit `cir.ternary` over the two
    `ult`s (the same `tif` shape as the intersection guard). -/
def unionGuard : CExpr :=
  .tif (.ult (.var "i") (.stdVecLen "a"))
    (.ult (.var "j") (.stdVecLen "b"))
    (.lit (.b false))

/-- Main-loop body: three-way signed head compare — record the
    strictly smaller head and advance its side plus the record
    cursor, or record once and advance both sides plus the
    record cursor on equal heads. -/
def vecUnionBody : CStmt :=
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
      (.seq (.vecSet "out" (.var "w")
                (.stdVecAt "b" (.var "j")))
        (.seq (.assign "j" (.uadd (.var "j")
                  (.lit (.u64 (BitVec.ofNat 64 1)))))
          (.assign "w" (.uadd (.var "w")
                  (.lit (.u64 (BitVec.ofNat 64 1)))))))
      (.seq (.vecSet "out" (.var "w")
                (.stdVecAt "a" (.var "i")))
        (.seq (.assign "i" (.uadd (.var "i")
                  (.lit (.u64 (BitVec.ofNat 64 1)))))
          (.seq (.assign "j" (.uadd (.var "j")
                    (.lit (.u64 (BitVec.ofNat 64 1)))))
            (.assign "w" (.uadd (.var "w")
                      (.lit (.u64 (BitVec.ofNat 64 1))))))))))

/-- The main union scan loop. -/
def vecUnionMain : CStmt :=
  .while_ unionGuard vecUnionBody

/-- Drain-`a` body: copy the survivor head, advance `i` and the
    record cursor (no branch — the survivor side is fixed). -/
def vecUnionDrainABody : CStmt :=
  (.seq (.vecSet "out" (.var "w")
            (.stdVecAt "a" (.var "i")))
    (.seq (.assign "i" (.uadd (.var "i")
              (.lit (.u64 (BitVec.ofNat 64 1)))))
      (.assign "w" (.uadd (.var "w")
              (.lit (.u64 (BitVec.ofNat 64 1)))))))

/-- Drain-`a` loop `while (i < a.size()) body`. -/
def vecUnionDrainA : CStmt :=
  .while_ (.ult (.var "i") (.stdVecLen "a")) vecUnionDrainABody

/-- Drain-`b` body: copy the survivor head, advance `j` and the
    record cursor. -/
def vecUnionDrainBBody : CStmt :=
  (.seq (.vecSet "out" (.var "w")
            (.stdVecAt "b" (.var "j")))
    (.seq (.assign "j" (.uadd (.var "j")
              (.lit (.u64 (BitVec.ofNat 64 1)))))
      (.assign "w" (.uadd (.var "w")
              (.lit (.u64 (BitVec.ofNat 64 1)))))))

/-- Drain-`b` loop `while (j < b.size()) body`. -/
def vecUnionDrainB : CStmt :=
  .while_ (.ult (.var "j") (.stdVecLen "b")) vecUnionDrainBBody

/-! ## Forward model (value level) -/

/-- Main-loop forward: cursors `i`, `j` walk the sorted inputs,
    `w` records union heads into `lo`. Either cursor reaching
    its end stops the scan. Total: every index failure is
    guarded away, so the only error arm is the unreachable
    `AssertFail`. -/
def unionMainFwd :
    List (BitVec 32) → List (BitVec 32) → List (BitVec 32) →
    Nat → Nat → Nat → Nat → Result (Nat × Nat × Nat × List (BitVec 32))
  | la, lb, lo, 0, i, j, w => .ok (i, j, w, lo)
  | la, lb, lo, fuel + 1, i, j, w =>
    if _ : i < la.length then
      if _ : j < lb.length then
        match la[i]?, lb[j]? with
        | some x, some y =>
          if x.slt y then
            unionMainFwd la lb (lo.set w x) fuel (i + 1) j (w + 1)
          else if y.slt x then
            unionMainFwd la lb (lo.set w y) fuel i (j + 1) (w + 1)
          else unionMainFwd la lb (lo.set w x) fuel (i + 1) (j + 1) (w + 1)
        | _, _ => .error .AssertFail
      else .ok (i, j, w, lo)
    else .ok (i, j, w, lo)

/-- Drain-`a` forward: copy the `a` survivor suffix into `lo`. -/
def unionDrainAFwd (la : List (BitVec 32)) : List (BitVec 32) →
    Nat → Nat → Nat → Result (Nat × Nat × List (BitVec 32))
  | lo, 0, i, w => .ok (i, w, lo)
  | lo, fuel + 1, i, w =>
    if _ : i < la.length then
      match la[i]? with
      | some x => unionDrainAFwd la (lo.set w x) fuel (i + 1) (w + 1)
      | none => .error .AssertFail
    else .ok (i, w, lo)

/-- Drain-`b` forward: copy the `b` survivor suffix into `lo`. -/
def unionDrainBFwd (lb : List (BitVec 32)) : List (BitVec 32) →
    Nat → Nat → Nat → Result (Nat × Nat × List (BitVec 32))
  | lo, 0, i, w => .ok (i, w, lo)
  | lo, fuel + 1, i, w =>
    if _ : i < lb.length then
      match lb[i]? with
      | some x => unionDrainBFwd lb (lo.set w x) fuel (i + 1) (w + 1)
      | none => .error .AssertFail
    else .ok (i, w, lo)

/-- Whole-function forward: main scan, then the two drains; the
    `u64` survivor count is the result. Model fuels are
    measure-exact (remaining iterations). -/
def vecUnionFwd (la lb : List (BitVec 32))
    (lo : List (BitVec 32)) : Result Value :=
  match unionMainFwd la lb lo (la.length + lb.length + 1) 0 0 0 with
  | .error e => .error e
  | .ok (i, j, w, lo') =>
    match unionDrainAFwd la lo' (la.length - i) i w with
    | .error e => .error e
    | .ok (_, w', lo'') =>
      match unionDrainBFwd lb lo'' (lb.length - j) j w' with
      | .error e => .error e
      | .ok (_, w'', _) => .ok (.u64 (BitVec.ofNat 64 w''))

/-! ## Loop environment -/

/-- Loop environment (borrowed words + `u64` cursors), in prelude
    `let_` cons order (`w` over `j` over `i` over `[a, b, out]`,
    so the entry bridge is `rfl`). -/
def mkUnionEnv (la lb lo : List (BitVec 32))
    (i j w : BitVec 64) : Env :=
  [("w", .u64 w), ("j", .u64 j), ("i", .u64 i),
   ("a", .stdVecVal la), ("b", .stdVecVal lb),
   ("out", .stdVecVal lo)]

theorem mkUnionEnv_a (la lb lo : List (BitVec 32))
    (i j w : BitVec 64) :
    envLookup (mkUnionEnv la lb lo i j w) "a" =
      some (.stdVecVal la) := by
  simp [mkUnionEnv, envLookup]

theorem mkUnionEnv_b (la lb lo : List (BitVec 32))
    (i j w : BitVec 64) :
    envLookup (mkUnionEnv la lb lo i j w) "b" =
      some (.stdVecVal lb) := by
  simp [mkUnionEnv, envLookup]

theorem mkUnionEnv_out (la lb lo : List (BitVec 32))
    (i j w : BitVec 64) :
    envLookup (mkUnionEnv la lb lo i j w) "out" =
      some (.stdVecVal lo) := by
  simp [mkUnionEnv, envLookup]

theorem mkUnionEnv_i (la lb lo : List (BitVec 32))
    (i j w : BitVec 64) :
    envLookup (mkUnionEnv la lb lo i j w) "i" =
      some (.u64 i) := by
  simp [mkUnionEnv, envLookup]

theorem mkUnionEnv_j (la lb lo : List (BitVec 32))
    (i j w : BitVec 64) :
    envLookup (mkUnionEnv la lb lo i j w) "j" =
      some (.u64 j) := by
  simp [mkUnionEnv, envLookup]

theorem mkUnionEnv_w (la lb lo : List (BitVec 32))
    (i j w : BitVec 64) :
    envLookup (mkUnionEnv la lb lo i j w) "w" =
      some (.u64 w) := by
  simp [mkUnionEnv, envLookup]

/-! ## Guard evaluation -/

/-- The guard holds when both cursors are in bounds: `tif` takes
    the second `ult` without touching the vectors. -/
theorem unionGuard_eval_true (ρ : Env)
    (la lb : List (BitVec 32)) (i j : Nat)
    (iB jB : BitVec 64)
    (hiN : iB.toNat = i) (hjN : jB.toNat = j)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hla64 : la.length < 2 ^ 64) (hlb64 : lb.length < 2 ^ 64)
    (hltA : i < la.length) (hltB : j < lb.length) :
    evalExpr unionGuard ρ = .ok (.b true) := by
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
  simp only [unionGuard]
  rw [evalExpr_tif_true _ _ _ _ e1]
  exact e2

/-- The guard fails when `i` is exhausted: `tif` takes the else
    branch without touching `b`. -/
theorem unionGuard_eval_falseA (ρ : Env)
    (la lb : List (BitVec 32)) (i j : Nat)
    (iB jB : BitVec 64)
    (hiN : iB.toNat = i)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hla64 : la.length < 2 ^ 64)
    (hgeA : la.length ≤ i) :
    evalExpr unionGuard ρ = .ok (.b false) := by
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
  simp only [unionGuard]
  rw [evalExpr_tif_false _ _ _ _ e1]
  exact evalExpr_lit _ _

/-- The guard fails when `j` is exhausted but `i` is not: `tif`
    runs the second `ult` and takes the else branch. -/
theorem unionGuard_eval_falseB (ρ : Env)
    (la lb : List (BitVec 32)) (i j : Nat)
    (iB jB : BitVec 64)
    (hiN : iB.toNat = i) (hjN : jB.toNat = j)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hi : envLookup ρ "i" = some (.u64 iB))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hla64 : la.length < 2 ^ 64) (hlb64 : lb.length < 2 ^ 64)
    (hltA : i < la.length) (hgeB : lb.length ≤ j) :
    evalExpr unionGuard ρ = .ok (.b false) := by
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
  simp only [unionGuard]
  rw [evalExpr_tif_true _ _ _ _ e1]
  exact e2

/-- Canonical function: two shared-borrow inputs, one `mutBorrow`
    output, `u64` survivor count out; prelude binds `i`/`j`/`w`,
    then the main scan, the two survivor drains, and the count
    return. -/
def vecUnionFunc : Func :=
  ⟨vecUnionName,
   [{ name := "a", ty := stdVecObjTy, role := .sharedBorrow },
    { name := "b", ty := stdVecObjTy, role := .sharedBorrow },
    { name := "out", ty := stdVecObjTy, role := .mutBorrow 0 }],
   .u 64,
   (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
     (.seq (.let_ "j" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
       (.seq (.let_ "w" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
         (.seq vecUnionMain
           (.seq vecUnionDrainA
             (.seq vecUnionDrainB
               (.return_ (.var "w"))))))))⟩

/-- Program over which the entry evaluates (no callees). -/
abbrev vecUnionProg : Prog := [vecUnionFunc]

/-! ## Value body steps -/

/-- One main-body iteration, take-`a` branch: `a[i] < b[j]`
    holds, so the `a` head is recorded and the `i` and `w`
    cursors bump. -/
theorem valUnionMainBody_takeA (prog : Prog) (F : Nat)
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
    ∃ ρ', evalProgStmt prog F vecUnionBody ρ =
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
  have hif : evalProgStmt prog F vecUnionBody ρ =
      evalProgStmt prog F
        (.seq (.vecSet "out" (.var "w")
                 (.stdVecAt "a" (.var "i")))
          (.seq (.assign "i" (.uadd (.var "i")
                    (.lit (.u64 (BitVec.ofNat 64 1)))))
            (.assign "w" (.uadd (.var "w")
                      (.lit (.u64 (BitVec.ofNat 64 1))))))) ρ := by
    simp only [vecUnionBody]
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

/-- One main-body iteration, take-`b` branch: `a[i] < b[j]`
    fails but `b[j] < a[i]` holds, so the `b` head is recorded
    and the `j` and `w` cursors bump. -/
theorem valUnionMainBody_takeB (prog : Prog) (F : Nat)
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
    (yO : BitVec 32) (hgetO : lo[w]? = some yO) (hwlt : w < lo.length)
    (hge1 : (x.slt y) = false) (hlt2 : (y.slt x) = true) :
    ∃ ρ', evalProgStmt prog F vecUnionBody ρ =
      .ok (ρ', .fellThrough) ∧
      envLookup ρ' "i" = some (.u64 iB) ∧
      envLookup ρ' "j" = some (.u64 (jB + 1)) ∧
      (jB + 1).toNat = j + 1 ∧
      envLookup ρ' "w" = some (.u64 (wB + 1)) ∧
      (wB + 1).toNat = w + 1 ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "b" = some (.stdVecVal lb) ∧
      envLookup ρ' "out" = some (.stdVecVal (lo.set w y)) := by
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
  have hwVar : evalExpr (.var "w") ρ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw
  have hgetO' : lo[wB.toNat]? = some yO := by rw [hwN]; exact hgetO
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "out"
    (.stdVecVal lo) (.stdVecVal (lo.set wB.toNat y)) hout
  have hset := revVecSet prog F "out" (.var "w")
    (.stdVecAt "b" (.var "j")) ρ wB y lo yO ρ₁
    hwVar hatB hout hgetO' hu₁
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
  have hevJ : evalExpr
      (.uadd (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁ =
      .ok (.u64 (jB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hj₁) (by simp [evalExpr, litVal])
  obtain ⟨ρ₂, hu₂⟩ := envUpdate_some_of_lookup ρ₁ "j"
    (.u64 jB) (.u64 (jB + 1)) hj₁
  have hstepJ := revAssign prog F "j"
    (.uadd (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁
    (.u64 (jB + 1)) ρ₂ hevJ hu₂
  have hi₂ : envLookup ρ₂ "i" = some (.u64 iB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "j" by decide) hu₂]
    exact hi₁
  have hw₂ : envLookup ρ₂ "w" = some (.u64 wB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "j" by decide) hu₂]
    exact hw₁
  have hout₂ : envLookup ρ₂ "out" =
      some (.stdVecVal (lo.set wB.toNat y)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "j" by decide) hu₂]
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
  have hjN' : (jB + 1).toNat = j + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hjN]
    exact Nat.mod_eq_of_lt (by omega)
  have hwN' : (wB + 1).toNat = w + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hwN]
    exact Nat.mod_eq_of_lt (by omega)
  have hif : evalProgStmt prog F vecUnionBody ρ =
      evalProgStmt prog F
        (.seq (.vecSet "out" (.var "w")
                 (.stdVecAt "b" (.var "j")))
          (.seq (.assign "j" (.uadd (.var "j")
                    (.lit (.u64 (BitVec.ofNat 64 1)))))
            (.assign "w" (.uadd (.var "w")
                      (.lit (.u64 (BitVec.ofNat 64 1))))))) ρ := by
    simp only [vecUnionBody]
    rw [evalProgStmt_if_false _ _ _ _ _ _ hcmp1]
    exact evalProgStmt_if_true _ _ _ _ _ _ hcmp2
  have hsetW : lo.set wB.toNat y = lo.set w y := by rw [hwN]
  have hseq0 : evalProgStmt prog F
      (.seq (.assign "j" (.uadd (.var "j")
                (.lit (.u64 (BitVec.ofNat 64 1)))))
        (.assign "w" (.uadd (.var "w")
                  (.lit (.u64 (BitVec.ofNat 64 1)))))) ρ₁ =
      evalProgStmt prog F
        (.assign "w" (.uadd (.var "w")
                (.lit (.u64 (BitVec.ofNat 64 1))))) ρ₂ := by
    exact evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepJ
  refine ⟨ρ₃, ?_, ?_, ?_, hjN', ?_, hwN', ?_, ?_, ?_⟩
  · rw [hif,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hset,
      hseq0]
    exact hstepW
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "w" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("i" : String) ≠ "j" by decide) hu₂]
    exact hi₁
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("j" : String) ≠ "w" by decide) hu₃]
    exact envLookup_update_hit _ _ _ _ hu₂
  · rw [envLookup_update_hit _ _ _ _ hu₃]
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "w" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "j" by decide) hu₂]
    exact ha₁
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("b" : String) ≠ "w" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("b" : String) ≠ "j" by decide) hu₂]
    exact hb₁
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "w" by decide) hu₃,
      ← hsetW]
    exact hout₂

/-- One main-body iteration, take-both branch: neither head is
    smaller, so the shared head is recorded once and all three
    cursors bump. -/
theorem valUnionMainBody_takeBoth (prog : Prog) (F : Nat)
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
    ∃ ρ', evalProgStmt prog F vecUnionBody ρ =
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
  have hif : evalProgStmt prog F vecUnionBody ρ =
      evalProgStmt prog F
        (.seq (.vecSet "out" (.var "w")
                 (.stdVecAt "a" (.var "i")))
          (.seq (.assign "i" (.uadd (.var "i")
                    (.lit (.u64 (BitVec.ofNat 64 1)))))
            (.seq (.assign "j" (.uadd (.var "j")
                      (.lit (.u64 (BitVec.ofNat 64 1)))))
              (.assign "w" (.uadd (.var "w")
                        (.lit (.u64 (BitVec.ofNat 64 1)))))))) ρ := by
    simp only [vecUnionBody]
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

/-! ## Value drain steps -/

/-- One drain-`a` iteration: the survivor head is copied and the
    `i` and `w` cursors bump (no branch — the survivor side is
    fixed). -/
theorem valUnionDrainABody_hit (prog : Prog) (F : Nat)
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
    ∃ ρ', evalProgStmt prog F vecUnionDrainABody ρ =
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
  · simp only [vecUnionDrainABody]
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

/-- One drain-`b` iteration: the survivor head is copied and the
    `j` and `w` cursors bump. -/
theorem valUnionDrainBBody_hit (prog : Prog) (F : Nat)
    (ρ : Env) (la lb lo : List (BitVec 32)) (j w : Nat)
    (jB wB : BitVec 64) (y : BitVec 32)
    (hjN : jB.toNat = j) (hwN : wB.toNat = w)
    (hlb64 : lb.length < 2 ^ 64)
    (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hgetB : lb[j]? = some y)
    (hltB : j < lb.length)
    (yO : BitVec 32) (hgetO : lo[w]? = some yO) (hwlt : w < lo.length) :
    ∃ ρ', evalProgStmt prog F vecUnionDrainBBody ρ =
      .ok (ρ', .fellThrough) ∧
      envLookup ρ' "j" = some (.u64 (jB + 1)) ∧
      (jB + 1).toNat = j + 1 ∧
      envLookup ρ' "w" = some (.u64 (wB + 1)) ∧
      (wB + 1).toNat = w + 1 ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "b" = some (.stdVecVal lb) ∧
      envLookup ρ' "out" = some (.stdVecVal (lo.set w y)) := by
  have hjVar : evalExpr (.var "j") ρ = .ok (.u64 jB) :=
    evalExpr_var_hit _ _ _ hj
  have hgetB' : lb[jB.toNat]? = some y := by rw [hjN]; exact hgetB
  have hatB : evalExpr (.stdVecAt "b" (.var "j")) ρ = .ok (.i32 y) :=
    evalExpr_stdVecAt_some _ _ _ _ _ _ hb hjVar hgetB'
  have hwVar : evalExpr (.var "w") ρ = .ok (.u64 wB) :=
    evalExpr_var_hit _ _ _ hw
  have hgetO' : lo[wB.toNat]? = some yO := by rw [hwN]; exact hgetO
  obtain ⟨ρ₁, hu₁⟩ := envUpdate_some_of_lookup ρ "out"
    (.stdVecVal lo) (.stdVecVal (lo.set wB.toNat y)) hout
  have hset := revVecSet prog F "out" (.var "w")
    (.stdVecAt "b" (.var "j")) ρ wB y lo yO ρ₁
    hwVar hatB hout hgetO' hu₁
  have ha₁ : envLookup ρ₁ "a" = some (.stdVecVal la) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "out" by decide) hu₁]
    exact ha
  have hj₁ : envLookup ρ₁ "j" = some (.u64 jB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("j" : String) ≠ "out" by decide) hu₁]
    exact hj
  have hw₁ : envLookup ρ₁ "w" = some (.u64 wB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "out" by decide) hu₁]
    exact hw
  have hb₁ : envLookup ρ₁ "b" = some (.stdVecVal lb) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("b" : String) ≠ "out" by decide) hu₁]
    exact hb
  have hevJ : evalExpr
      (.uadd (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁ =
      .ok (.u64 (jB + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ hj₁) (by simp [evalExpr, litVal])
  obtain ⟨ρ₂, hu₂⟩ := envUpdate_some_of_lookup ρ₁ "j"
    (.u64 jB) (.u64 (jB + 1)) hj₁
  have hstepJ := revAssign prog F "j"
    (.uadd (.var "j") (.lit (.u64 (BitVec.ofNat 64 1)))) ρ₁
    (.u64 (jB + 1)) ρ₂ hevJ hu₂
  have hw₂ : envLookup ρ₂ "w" = some (.u64 wB) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("w" : String) ≠ "j" by decide) hu₂]
    exact hw₁
  have hout₂ : envLookup ρ₂ "out" =
      some (.stdVecVal (lo.set wB.toNat y)) := by
    rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "j" by decide) hu₂]
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
  have hjN' : (jB + 1).toNat = j + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hjN]
    exact Nat.mod_eq_of_lt (by omega)
  have hwN' : (wB + 1).toNat = w + 1 := by
    have h1 : (1 : BitVec 64).toNat = 1 := rfl
    rw [BitVec.toNat_add, h1, hwN]
    exact Nat.mod_eq_of_lt (by omega)
  have hsetW : lo.set wB.toNat y = lo.set w y := by rw [hwN]
  have hseq0 : evalProgStmt prog F
      (.seq (.assign "j" (.uadd (.var "j")
                (.lit (.u64 (BitVec.ofNat 64 1)))))
        (.assign "w" (.uadd (.var "w")
                  (.lit (.u64 (BitVec.ofNat 64 1)))))) ρ₁ =
      evalProgStmt prog F
        (.assign "w" (.uadd (.var "w")
                (.lit (.u64 (BitVec.ofNat 64 1))))) ρ₂ := by
    exact evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepJ
  refine ⟨ρ₃, ?_, ?_, hjN', ?_, hwN', ?_, ?_, ?_⟩
  · simp only [vecUnionDrainBBody]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hset, hseq0]
    exact hstepW
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("j" : String) ≠ "w" by decide) hu₃]
    exact envLookup_update_hit _ _ _ _ hu₂
  · rw [envLookup_update_hit _ _ _ _ hu₃]
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "w" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("a" : String) ≠ "j" by decide) hu₂]
    exact ha₁
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("b" : String) ≠ "w" by decide) hu₃,
      envLookup_update_miss _ _ _ _ _
      (show ("b" : String) ≠ "j" by decide) hu₂]
    exact hb₁
  · rw [envLookup_update_miss _ _ _ _ _
      (show ("out" : String) ≠ "w" by decide) hu₃,
      ← hsetW]
    exact hout₂

/-! ## Value loop -/

/-- Forward length preservation: the scan only ever `set`s inside
    `lo`, so the recorded list keeps its length on the ok path. -/
theorem unionMainFwd_length :
    ∀ (G : Nat) (la lb lo : List (BitVec 32)) (i j w i' j' w' : Nat)
      (lo' : List (BitVec 32)),
    unionMainFwd la lb lo G i j w = .ok (i', j', w', lo') →
    lo'.length = lo.length := by
  intro G
  induction G with
  | zero =>
    intro la lb lo i j w i' j' w' lo' h
    have hpair : (i, j, w, lo) = (i', j', w', lo') := by
      simpa [unionMainFwd] using h
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
        · have h' : unionMainFwd la lb (lo.set w x) G (i + 1) j (w + 1) =
              .ok (i', j', w', lo') := by
            simpa [unionMainFwd, dite_eq_left hltA, dite_eq_left hltB,
              hgetA, hgetB, hlt] using h
          have hlen := ih la lb (lo.set w x) (i + 1) j (w + 1)
            i' j' w' lo' h'
          rwa [List.length_set] at hlen
        · by_cases hgt : (y.slt x) = true
          · have h' : unionMainFwd la lb (lo.set w y) G i (j + 1) (w + 1) =
                .ok (i', j', w', lo') := by
              have hne : (x.slt y) = false := by
                cases hxy : x.slt y with
                | true => exact absurd hxy hlt
                | false => rfl
              simpa [unionMainFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hne, hgt] using h
            have hlen := ih la lb (lo.set w y) i (j + 1) (w + 1)
              i' j' w' lo' h'
            rwa [List.length_set] at hlen
          · have h' : unionMainFwd la lb (lo.set w x) G (i + 1) (j + 1) (w + 1) =
                .ok (i', j', w', lo') := by
              have hne1 : (x.slt y) = false := by
                cases hxy : x.slt y with
                | true => exact absurd hxy hlt
                | false => rfl
              have hne2 : (y.slt x) = false := by
                cases hyx : y.slt x with
                | true => exact absurd hyx hgt
                | false => rfl
              simpa [unionMainFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hne1, hne2] using h
            have hlen := ih la lb (lo.set w x) (i + 1) (j + 1) (w + 1)
              i' j' w' lo' h'
            rwa [List.length_set] at hlen
      · have hpair : (i, j, w, lo) = (i', j', w', lo') := by
          simpa [unionMainFwd, dite_eq_left hltA,
            dite_eq_right hltB] using h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
        rfl
    · have hpair : (i, j, w, lo) = (i', j', w', lo') := by
        simpa [unionMainFwd, dite_eq_right hltA] using h
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
      rfl

/-- Drain-`a` length preservation: the survivor copy only ever
    `set`s inside `lo`. -/
theorem unionDrainAFwd_length :
    ∀ (G : Nat) (la lo : List (BitVec 32)) (i w i' w' : Nat)
      (lo' : List (BitVec 32)),
    unionDrainAFwd la lo G i w = .ok (i', w', lo') →
    lo'.length = lo.length := by
  intro G
  induction G with
  | zero =>
    intro la lo i w i' w' lo' h
    have hpair : (i, w, lo) = (i', w', lo') := by
      simpa [unionDrainAFwd] using h
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    rfl
  | succ G ih =>
    intro la lo i w i' w' lo' h
    by_cases hltA : i < la.length
    · obtain ⟨x, hgetA⟩ : ∃ x, la[i]? = some x :=
        ⟨la[i], List.getElem?_eq_getElem hltA⟩
      have h' : unionDrainAFwd la (lo.set w x) G (i + 1) (w + 1) =
          .ok (i', w', lo') := by
        simpa [unionDrainAFwd, dite_eq_left hltA, hgetA] using h
      have hlen := ih la (lo.set w x) (i + 1) (w + 1) i' w' lo' h'
      rwa [List.length_set] at hlen
    · have hpair : (i, w, lo) = (i', w', lo') := by
        simpa [unionDrainAFwd, dite_eq_right hltA] using h
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      rfl

/-- Drain-`b` length preservation: the survivor copy only ever
    `set`s inside `lo`. -/
theorem unionDrainBFwd_length :
    ∀ (G : Nat) (lb lo : List (BitVec 32)) (j w j' w' : Nat)
      (lo' : List (BitVec 32)),
    unionDrainBFwd lb lo G j w = .ok (j', w', lo') →
    lo'.length = lo.length := by
  intro G
  induction G with
  | zero =>
    intro lb lo j w j' w' lo' h
    have hpair : (j, w, lo) = (j', w', lo') := by
      simpa [unionDrainBFwd] using h
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    rfl
  | succ G ih =>
    intro lb lo j w j' w' lo' h
    by_cases hltB : j < lb.length
    · obtain ⟨y, hgetB⟩ : ∃ y, lb[j]? = some y :=
        ⟨lb[j], List.getElem?_eq_getElem hltB⟩
      have h' : unionDrainBFwd lb (lo.set w y) G (j + 1) (w + 1) =
          .ok (j', w', lo') := by
        simpa [unionDrainBFwd, dite_eq_left hltB, hgetB] using h
      have hlen := ih lb (lo.set w y) (j + 1) (w + 1) j' w' lo' h'
      rwa [List.length_set] at hlen
    · have hpair : (j, w, lo) = (j', w', lo') := by
        simpa [unionDrainBFwd, dite_eq_right hltB] using h
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      rfl

/-- Drain-`a` guard evaluation: the `ult` reads the `a` length
    word and decides `i < a.size()`. -/
theorem unionDrainAGuard_eval (ρ : Env)
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

/-- Drain-`b` guard evaluation: the `ult` reads the `b` length
    word and decides `j < b.size()`. -/
theorem unionDrainBGuard_eval (ρ : Env)
    (lb : List (BitVec 32)) (j : Nat)
    (jB : BitVec 64)
    (hjN : jB.toNat = j)
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hlb64 : lb.length < 2 ^ 64) :
    evalExpr (.ult (.var "j") (.stdVecLen "b")) ρ =
      .ok (.b (decide (j < lb.length))) := by
  have hlenB : (BitVec.ofNat 64 lb.length).toNat = lb.length :=
    ofNat64_toNat _ (by omega)
  have hoLenB : evalExpr (.stdVecLen "b") ρ =
      .ok (.u64 (BitVec.ofNat 64 lb.length)) :=
    evalExpr_stdVecLen_some _ _ _ hb
  have h := evalExpr_ult_u64 (.var "j") (.stdVecLen "b") ρ jB
    (BitVec.ofNat 64 lb.length) (evalExpr_var_hit _ _ _ hj) hoLenB
  rw [BitVec.ult_eq_decide, hjN, hlenB] at h
  by_cases hlt : j < lb.length
  · rw [decide_eq_true hlt] at h ⊢
    exact h
  · rw [decide_eq_false hlt] at h ⊢
    exact h

/-- Value main loop: the scan runs to cursor exhaustion and the
    environment matches the forward model (fuel induction threading
    the body hits; the forward equation unfolds one step per
    branch). The capacity invariant `hcap` keeps one free slot in
    `lo` ahead of the worst case, so every write is in bounds. -/
theorem valUnionMainLoop_ok (prog : Prog) (F G : Nat)
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
    (hcap : w + (la.length - i) + (lb.length - j) ≤ lo.length)
    (hreadA : ∀ p, p < la.length → ∃ x, la[p]? = some x)
    (hreadB : ∀ p, p < lb.length → ∃ x, lb[p]? = some x)
    (hreadO : ∀ p, p < lo.length → ∃ x, lo[p]? = some x)
    (hfwd : unionMainFwd la lb lo G i j w = .ok (i', j', w', lo')) :
    ∃ ρ', evalProgStmt prog F vecUnionMain ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "b" = some (.stdVecVal lb) ∧
      envLookup ρ' "out" = some (.stdVecVal lo') ∧
      (∃ iB', envLookup ρ' "i" = some (.u64 iB') ∧ iB'.toNat = i') ∧
      (∃ jB', envLookup ρ' "j" = some (.u64 jB') ∧ jB'.toNat = j') ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w') ∧
      w' + (la.length - i') + (lb.length - j') ≤ lo'.length := by
  induction F generalizing G ρ la lb lo i j w iB jB wB with
  | zero =>
    have hgeA : la.length ≤ i := by omega
    have hguardF : evalExpr unionGuard ρ = .ok (.b false) :=
      unionGuard_eval_falseA ρ la lb i j iB jB hiN ha hi hla64 hgeA
    have hexit : evalProgStmt prog 0 vecUnionMain ρ =
        .ok (ρ, .fellThrough) :=
      evalProgStmt_while_false prog 0 _ _ _ hguardF
    have hpair : (i, j, w, lo) = (i', j', w', lo') := by
      cases G with
      | zero => simpa [unionMainFwd] using hfwd
      | succ G =>
        have hnegA : ¬ i < la.length := by omega
        simpa [unionMainFwd, dite_eq_right hnegA] using hfwd
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
    exact ⟨ρ, hexit, ha, hb, hout, ⟨iB, hi, hiN⟩, ⟨jB, hj, hjN⟩,
      ⟨wB, hw, hwN⟩, hcap⟩
  | succ F ih =>
    by_cases hltA : i < la.length
    · by_cases hltB : j < lb.length
      · obtain ⟨x, hgetA⟩ := hreadA i hltA
        obtain ⟨y, hgetB⟩ := hreadB j hltB
        have hguardT : evalExpr unionGuard ρ = .ok (.b true) :=
          unionGuard_eval_true ρ la lb i j iB jB hiN hjN ha hb hi hj
            hla64 hlb64 hltA hltB
        by_cases hlt : (x.slt y) = true
        · cir_fuel_step (F, G, (la.length - (i + 1)) + (lb.length - j))
          have hwlt : w < lo.length := by omega
          obtain ⟨xO, hgetO⟩ := hreadO w hwlt
          obtain ⟨ρ₁, hbody, hiB₁, hiN₁, hjB₁, hwB₁, hwN₁, ha₁, hb₁,
              hout₁⟩ :=
            valUnionMainBody_takeA prog F ρ la lb lo i j w iB jB wB x y
              hiN hjN hwN hla64 hlb64 hlo64 ha hb hout hi hj hw
              hgetA hgetB hltA hltB xO hgetO hwlt hlt
          have hfwd' : unionMainFwd la lb (lo.set w x) G' (i + 1) j
              (w + 1) = .ok (i', j', w', lo') := by
            simpa [unionMainFwd, dite_eq_left hltA, dite_eq_left hltB,
              hgetA, hgetB, hlt] using hfwd
          have hlenSet : (lo.set w x).length = lo.length :=
            List.length_set
          have hcap' : (w + 1) + (la.length - (i + 1)) + (lb.length - j) ≤
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
          have hwhile : evalProgStmt prog (F + 1) vecUnionMain ρ =
              evalProgStmt prog F vecUnionMain ρ₁ := by
            cir_unfold_prog (vecUnionMain, prog, F, hguardT, hbody)
          rw [hwhile]
          exact hloop
        · by_cases hgt : (y.slt x) = true
          · have hne : (x.slt y) = false := by
              cases hxy : x.slt y with
              | true => exact absurd hxy hlt
              | false => rfl
            cir_fuel_step (F, G, (la.length - i) + (lb.length - (j + 1)))
            have hwlt : w < lo.length := by omega
            obtain ⟨yO, hgetO⟩ := hreadO w hwlt
            obtain ⟨ρ₁, hbody, hiB₁, hjB₁, hjN₁, hwB₁, hwN₁, ha₁, hb₁,
                hout₁⟩ :=
              valUnionMainBody_takeB prog F ρ la lb lo i j w iB jB wB x y
                hiN hjN hwN hla64 hlb64 hlo64 ha hb hout hi hj hw
                hgetA hgetB hltA hltB yO hgetO hwlt hne hgt
            have hfwd' : unionMainFwd la lb (lo.set w y) G' i (j + 1)
                (w + 1) = .ok (i', j', w', lo') := by
              simpa [unionMainFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hne, hgt] using hfwd
            have hlenSet : (lo.set w y).length = lo.length :=
              List.length_set
            have hcap' : (w + 1) + (la.length - i) + (lb.length - (j + 1)) ≤
                (lo.set w y).length := by
              rw [hlenSet]; omega
            have hlo64' : (lo.set w y).length < 2 ^ 64 := by
              rw [hlenSet]; exact hlo64
            have hreadO' : ∀ p, p < (lo.set w y).length →
                ∃ z, (lo.set w y)[p]? = some z := by
              intro p hp
              have hplen : p < lo.length := by
                have hlen : (lo.set w y).length = lo.length :=
                  List.length_set
                omega
              obtain ⟨z, hz⟩ := hreadO p hplen
              by_cases hpi : p = w
              · subst hpi
                exact ⟨y, by
                  rw [List.getElem?_set_self (by omega : p < lo.length)]⟩
              · exact ⟨z, by
                  rw [List.getElem?_set_ne (show w ≠ p by omega)]
                  exact hz⟩
            obtain ⟨ρ', hloop, ha', hb', hout', ⟨iB', hiB', hiN'⟩,
                ⟨jB', hjB', hjN'⟩, ⟨wB', hwB', hwN'⟩, hcapI⟩ :=
              ih (G := G') (ρ := ρ₁) (la := la) (lb := lb)
                (lo := (lo.set w y))
                (i := i) (j := j + 1) (w := w + 1)
                (iB := iB) (jB := jB + 1) (wB := wB + 1)
                (hiN := hiN) (hjN := hjN₁) (hwN := hwN₁)
                (hla64 := hla64) (hlb64 := hlb64) (hlo64 := hlo64')
                (ha := ha₁) (hb := hb₁) (hout := hout₁)
                (hi := hiB₁) (hj := hjB₁) (hw := hwB₁)
                (hile := hile) (hjle := by omega)
                (hF := hF') (hG := hG') (hcap := hcap')
                (hreadA := hreadA) (hreadB := hreadB) (hreadO := hreadO')
                (hfwd := hfwd')
            refine ⟨ρ', ?_, ha', hb', hout', ⟨iB', hiB', hiN'⟩,
              ⟨jB', hjB', hjN'⟩, ⟨wB', hwB', hwN'⟩, hcapI⟩
            have hwhile : evalProgStmt prog (F + 1) vecUnionMain ρ =
                evalProgStmt prog F vecUnionMain ρ₁ := by
              cir_unfold_prog (vecUnionMain, prog, F, hguardT, hbody)
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
              valUnionMainBody_takeBoth prog F ρ la lb lo i j w iB jB wB x y
                hiN hjN hwN hla64 hlb64 hlo64 ha hb hout hi hj hw
                hgetA hgetB hltA hltB xO hgetO hwlt hge1 hge2
            have hfwd' : unionMainFwd la lb (lo.set w x) G' (i + 1) (j + 1)
                (w + 1) = .ok (i', j', w', lo') := by
              simpa [unionMainFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hge1, hge2] using hfwd
            have hlenSet : (lo.set w x).length = lo.length :=
              List.length_set
            have hcap' : (w + 1) + (la.length - (i + 1)) +
                (lb.length - (j + 1)) ≤
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
            have hwhile : evalProgStmt prog (F + 1) vecUnionMain ρ =
                evalProgStmt prog F vecUnionMain ρ₁ := by
              cir_unfold_prog (vecUnionMain, prog, F, hguardT, hbody)
            rw [hwhile]
            exact hloop
      · have hgeB : lb.length ≤ j := by omega
        have hguardF : evalExpr unionGuard ρ = .ok (.b false) :=
          unionGuard_eval_falseB ρ la lb i j iB jB hiN hjN ha hb
            hi hj hla64 hlb64 hltA hgeB
        have hexit : evalProgStmt prog (F + 1) vecUnionMain ρ =
            .ok (ρ, .fellThrough) :=
          evalProgStmt_while_false prog (F + 1) _ _ _ hguardF
        have hpair : (i, j, w, lo) = (i', j', w', lo') := by
          cases G with
          | zero => simpa [unionMainFwd] using hfwd
          | succ G =>
            have hnegB : ¬ j < lb.length := by omega
            simpa [unionMainFwd, dite_eq_left hltA,
              dite_eq_right hnegB] using hfwd
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
        exact ⟨ρ, hexit, ha, hb, hout, ⟨iB, hi, hiN⟩, ⟨jB, hj, hjN⟩,
          ⟨wB, hw, hwN⟩, hcap⟩
    · have hgeA : la.length ≤ i := by omega
      have hguardF : evalExpr unionGuard ρ = .ok (.b false) :=
        unionGuard_eval_falseA ρ la lb i j iB jB hiN ha hi hla64 hgeA
      have hexit : evalProgStmt prog (F + 1) vecUnionMain ρ =
          .ok (ρ, .fellThrough) :=
        evalProgStmt_while_false prog (F + 1) _ _ _ hguardF
      have hpair : (i, j, w, lo) = (i', j', w', lo') := by
        cases G with
        | zero => simpa [unionMainFwd] using hfwd
        | succ G =>
          have hnegA : ¬ i < la.length := by omega
          simpa [unionMainFwd, dite_eq_right hnegA] using hfwd
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
      exact ⟨ρ, hexit, ha, hb, hout, ⟨iB, hi, hiN⟩, ⟨jB, hj, hjN⟩,
        ⟨wB, hw, hwN⟩, hcap⟩

/-! ## Value drain loops -/

/-- Value drain-`a` loop: the survivor copy runs to `i` exhaustion
    and the environment matches the forward model. -/
theorem valUnionDrainALoop_ok (prog : Prog) (F G : Nat)
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
    (hfwd : unionDrainAFwd la lo G i w = .ok (i', w', lo')) :
    ∃ ρ', evalProgStmt prog F vecUnionDrainA ρ =
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
      have h := unionDrainAGuard_eval ρ la i iB hiN ha hi hla64
      rw [decide_eq_false (by omega : ¬ i < la.length)] at h
      exact h
    have hexit : evalProgStmt prog 0 vecUnionDrainA ρ =
        .ok (ρ, .fellThrough) :=
      evalProgStmt_while_false prog 0 _ _ _ hguardF
    have hpair : (i, w, lo) = (i', w', lo') := by
      cases G with
      | zero => simpa [unionDrainAFwd] using hfwd
      | succ G =>
        have hnegA : ¬ i < la.length := by omega
        simpa [unionDrainAFwd, dite_eq_right hnegA] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    exact ⟨ρ, hexit, ha, hb, hout, ⟨iB, hi, hiN⟩, ⟨wB, hw, hwN⟩, hcap,
      by omega, by omega, hj⟩
  | succ F ih =>
    by_cases hltA : i < la.length
    · obtain ⟨x, hgetA⟩ := hreadA i hltA
      have hguardT : evalExpr (.ult (.var "i") (.stdVecLen "a")) ρ =
          .ok (.b true) := by
        have h := unionDrainAGuard_eval ρ la i iB hiN ha hi hla64
        rw [decide_eq_true hltA] at h
        exact h
      have hwlt : w < lo.length := by omega
      obtain ⟨xO, hgetO⟩ := hreadO w hwlt
      cir_fuel_step (F, G, la.length - (i + 1))
      obtain ⟨ρ₁, hbody, hiB₁, hiN₁, hwB₁, hwN₁, ha₁, hb₁, hout₁,
          hjbody⟩ :=
        valUnionDrainABody_hit prog F ρ la lb lo i w iB wB x jB
          hiN hwN hla64 hlo64 ha hb hout hi hw hj hgetA hltA
          xO hgetO hwlt
      have hfwd' : unionDrainAFwd la (lo.set w x) G' (i + 1) (w + 1) =
          .ok (i', w', lo') := by
        simpa [unionDrainAFwd, dite_eq_left hltA, hgetA] using hfwd
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
      have hwhile : evalProgStmt prog (F + 1) vecUnionDrainA ρ =
          evalProgStmt prog F vecUnionDrainA ρ₁ := by
        cir_unfold_prog (vecUnionDrainA, prog, F, hguardT, hbody)
      rw [hwhile]
      exact hloop
    · have hgeA : la.length ≤ i := by omega
      have hguardF : evalExpr (.ult (.var "i") (.stdVecLen "a")) ρ =
          .ok (.b false) := by
        have h := unionDrainAGuard_eval ρ la i iB hiN ha hi hla64
        rw [decide_eq_false (by omega : ¬ i < la.length)] at h
        exact h
      have hexit : evalProgStmt prog (F + 1) vecUnionDrainA ρ =
          .ok (ρ, .fellThrough) :=
        evalProgStmt_while_false prog (F + 1) _ _ _ hguardF
      have hpair : (i, w, lo) = (i', w', lo') := by
        cases G with
        | zero => simpa [unionDrainAFwd] using hfwd
        | succ G =>
          have hnegA : ¬ i < la.length := by omega
          simpa [unionDrainAFwd, dite_eq_right hnegA] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      exact ⟨ρ, hexit, ha, hb, hout, ⟨iB, hi, hiN⟩, ⟨wB, hw, hwN⟩, hcap,
        by omega, by omega, hj⟩

/-- Value drain-`b` loop: the survivor copy runs to `j` exhaustion
    and the environment matches the forward model. -/
theorem valUnionDrainBLoop_ok (prog : Prog) (F G : Nat)
    (ρ : Env) (la lb lo : List (BitVec 32))
    (j w : Nat) (jB wB : BitVec 64)
    (j' w' : Nat) (lo' : List (BitVec 32))
    (hjN : jB.toNat = j) (hwN : wB.toNat = w)
    (hlb64 : lb.length < 2 ^ 64)
    (hlo64 : lo.length < 2 ^ 64)
    (ha : envLookup ρ "a" = some (.stdVecVal la))
    (hb : envLookup ρ "b" = some (.stdVecVal lb))
    (hout : envLookup ρ "out" = some (.stdVecVal lo))
    (hj : envLookup ρ "j" = some (.u64 jB))
    (hw : envLookup ρ "w" = some (.u64 wB))
    (hjle : j ≤ lb.length)
    (hF : lb.length - j ≤ F)
    (hG : lb.length - j ≤ G)
    (hcap : w + (lb.length - j) ≤ lo.length)
    (hreadB : ∀ p, p < lb.length → ∃ x, lb[p]? = some x)
    (hreadO : ∀ p, p < lo.length → ∃ x, lo[p]? = some x)
    (hfwd : unionDrainBFwd lb lo G j w = .ok (j', w', lo')) :
    ∃ ρ', evalProgStmt prog F vecUnionDrainB ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "a" = some (.stdVecVal la) ∧
      envLookup ρ' "b" = some (.stdVecVal lb) ∧
      envLookup ρ' "out" = some (.stdVecVal lo') ∧
      (∃ jB', envLookup ρ' "j" = some (.u64 jB') ∧ jB'.toNat = j') ∧
      (∃ wB', envLookup ρ' "w" = some (.u64 wB') ∧ wB'.toNat = w') ∧
      w' + (lb.length - j') ≤ lo'.length ∧
      j ≤ j' ∧ w + (j' - j) = w' := by
  induction F generalizing G ρ la lb lo j w jB wB with
  | zero =>
    have hgeB : lb.length ≤ j := by omega
    have hguardF : evalExpr (.ult (.var "j") (.stdVecLen "b")) ρ =
        .ok (.b false) := by
      have h := unionDrainBGuard_eval ρ lb j jB hjN hb hj hlb64
      rw [decide_eq_false (by omega : ¬ j < lb.length)] at h
      exact h
    have hexit : evalProgStmt prog 0 vecUnionDrainB ρ =
        .ok (ρ, .fellThrough) :=
      evalProgStmt_while_false prog 0 _ _ _ hguardF
    have hpair : (j, w, lo) = (j', w', lo') := by
      cases G with
      | zero => simpa [unionDrainBFwd] using hfwd
      | succ G =>
        have hnegB : ¬ j < lb.length := by omega
        simpa [unionDrainBFwd, dite_eq_right hnegB] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    exact ⟨ρ, hexit, ha, hb, hout, ⟨jB, hj, hjN⟩, ⟨wB, hw, hwN⟩, hcap,
      by omega, by omega⟩
  | succ F ih =>
    by_cases hltB : j < lb.length
    · obtain ⟨y, hgetB⟩ := hreadB j hltB
      have hguardT : evalExpr (.ult (.var "j") (.stdVecLen "b")) ρ =
          .ok (.b true) := by
        have h := unionDrainBGuard_eval ρ lb j jB hjN hb hj hlb64
        rw [decide_eq_true hltB] at h
        exact h
      have hwlt : w < lo.length := by omega
      obtain ⟨yO, hgetO⟩ := hreadO w hwlt
      cir_fuel_step (F, G, lb.length - (j + 1))
      obtain ⟨ρ₁, hbody, hjB₁, hjN₁, hwB₁, hwN₁, ha₁, hb₁, hout₁⟩ :=
        valUnionDrainBBody_hit prog F ρ la lb lo j w jB wB y
          hjN hwN hlb64 hlo64 ha hb hout hj hw hgetB hltB
          yO hgetO hwlt
      have hfwd' : unionDrainBFwd lb (lo.set w y) G' (j + 1) (w + 1) =
          .ok (j', w', lo') := by
        simpa [unionDrainBFwd, dite_eq_left hltB, hgetB] using hfwd
      have hlenSet : (lo.set w y).length = lo.length :=
        List.length_set
      have hcap' : (w + 1) + (lb.length - (j + 1)) ≤
          (lo.set w y).length := by
        rw [hlenSet]; omega
      have hlo64' : (lo.set w y).length < 2 ^ 64 := by
        rw [hlenSet]; exact hlo64
      have hreadO' : ∀ p, p < (lo.set w y).length →
          ∃ z, (lo.set w y)[p]? = some z := by
        intro p hp
        have hplen : p < lo.length := by
          have hlen : (lo.set w y).length = lo.length :=
            List.length_set
          omega
        obtain ⟨z, hz⟩ := hreadO p hplen
        by_cases hpi : p = w
        · subst hpi
          exact ⟨y, by
            rw [List.getElem?_set_self (by omega : p < lo.length)]⟩
        · exact ⟨z, by
            rw [List.getElem?_set_ne (show w ≠ p by omega)]
            exact hz⟩
      obtain ⟨ρ', hloop, ha', hb', hout', ⟨jB', hjB', hjN'⟩,
          ⟨wB', hwB', hwN'⟩, hcapI, hmonoI, hcntI⟩ :=
        ih (G := G') (ρ := ρ₁) (la := la) (lb := lb)
          (lo := (lo.set w y))
          (j := j + 1) (w := w + 1)
          (jB := jB + 1) (wB := wB + 1)
          (hjN := hjN₁) (hwN := hwN₁)
          (hlb64 := hlb64) (hlo64 := hlo64')
          (ha := ha₁) (hb := hb₁) (hout := hout₁)
          (hj := hjB₁) (hw := hwB₁)
          (hjle := by omega)
          (hF := hF') (hG := hG') (hcap := hcap')
          (hreadB := hreadB) (hreadO := hreadO')
          (hfwd := hfwd')
      have hmono : j ≤ j' := by omega
      have hcnt : w + (j' - j) = w' := by omega
      refine ⟨ρ', ?_, ha', hb', hout', ⟨jB', hjB', hjN'⟩,
        ⟨wB', hwB', hwN'⟩, hcapI, hmono, hcnt⟩
      have hwhile : evalProgStmt prog (F + 1) vecUnionDrainB ρ =
          evalProgStmt prog F vecUnionDrainB ρ₁ := by
        cir_unfold_prog (vecUnionDrainB, prog, F, hguardT, hbody)
      rw [hwhile]
      exact hloop
    · have hgeB : lb.length ≤ j := by omega
      have hguardF : evalExpr (.ult (.var "j") (.stdVecLen "b")) ρ =
          .ok (.b false) := by
        have h := unionDrainBGuard_eval ρ lb j jB hjN hb hj hlb64
        rw [decide_eq_false (by omega : ¬ j < lb.length)] at h
        exact h
      have hexit : evalProgStmt prog (F + 1) vecUnionDrainB ρ =
          .ok (ρ, .fellThrough) :=
        evalProgStmt_while_false prog (F + 1) _ _ _ hguardF
      have hpair : (j, w, lo) = (j', w', lo') := by
        cases G with
        | zero => simpa [unionDrainBFwd] using hfwd
        | succ G =>
          have hnegB : ¬ j < lb.length := by omega
          simpa [unionDrainBFwd, dite_eq_right hnegB] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      exact ⟨ρ, hexit, ha, hb, hout, ⟨jB, hj, hjN⟩, ⟨wB, hw, hwN⟩, hcap,
        by omega, by omega⟩

/-! ## Whole-function evaluation -/

/-- Forward-model bounds (sequential chaining): cursors stay inside
    their lists and the record keeps its length. The record-count
    bound threads the sum-capacity invariant. -/
theorem unionMainFwd_le (la lb : List (BitVec 32)) (F' i j w : Nat)
    (lo : List (BitVec 32)) (i' j' w' : Nat) (lo' : List (BitVec 32))
    (hi : i ≤ la.length) (hj : j ≤ lb.length)
    (hcap : w + (la.length - i) + (lb.length - j) ≤ lo.length)
    (hfwd : unionMainFwd la lb lo F' i j w = .ok (i', j', w', lo')) :
    i' ≤ la.length ∧ j' ≤ lb.length ∧ w' ≤ lo.length ∧
      lo'.length = lo.length := by
  induction F' generalizing lo i j w i' j' w' lo' with
  | zero =>
    simp only [unionMainFwd, Except.ok.injEq, Prod.mk.injEq] at hfwd
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hfwd
    exact ⟨hi, hj, by omega, rfl⟩
  | succ F' ih =>
    by_cases hA : i < la.length
    · by_cases hB : j < lb.length
      · cases hAi : la[i]? with
        | none =>
          simp only [unionMainFwd, dite_eq_left hA, dite_eq_left hB,
            hAi] at hfwd
          cases hfwd
        | some x =>
          cases hBj : lb[j]? with
          | none =>
            simp only [unionMainFwd, dite_eq_left hA, dite_eq_left hB,
              hAi, hBj] at hfwd
            cases hfwd
          | some y =>
            have hset : (lo.set w x).length = lo.length :=
              List.length_set
            have hsety : (lo.set w y).length = lo.length :=
              List.length_set
            by_cases hlt : (x.slt y) = true
            · have h' : unionMainFwd la lb (lo.set w x) F' (i + 1) j
                  (w + 1) = .ok (i', j', w', lo') := by
                simpa [unionMainFwd, dite_eq_left hA, dite_eq_left hB,
                  hAi, hBj, hlt] using hfwd
              have hcapA : (w + 1) + (la.length - (i + 1)) +
                  (lb.length - j) ≤ (lo.set w x).length := by
                  rw [List.length_set]; omega
              obtain ⟨hi', hj', hw', hlen⟩ :=
                ih _ _ _ _ _ _ _ _ (by omega) hj hcapA h'
              exact ⟨hi', hj', hset ▸ hw', hlen.trans hset⟩
            · by_cases hgt : (y.slt x) = true
              · have hne : (x.slt y) = false := by
                  cases hxy : x.slt y with
                  | true => exact absurd hxy hlt
                  | false => rfl
                have h' : unionMainFwd la lb (lo.set w y) F' i (j + 1)
                    (w + 1) = .ok (i', j', w', lo') := by
                  simpa [unionMainFwd, dite_eq_left hA, dite_eq_left hB,
                    hAi, hBj, hne, hgt] using hfwd
                have hcapB : (w + 1) + (la.length - i) +
                    (lb.length - (j + 1)) ≤ (lo.set w y).length := by
                  rw [List.length_set]; omega
                obtain ⟨hi', hj', hw', hlen⟩ :=
                  ih _ _ _ _ _ _ _ _ hi (by omega) hcapB h'
                exact ⟨hi', hj', hsety ▸ hw', hlen.trans hsety⟩
              · have hne1 : (x.slt y) = false := by
                  cases hxy : x.slt y with
                  | true => exact absurd hxy hlt
                  | false => rfl
                have hne2 : (y.slt x) = false := by
                  cases hyx : y.slt x with
                  | true => exact absurd hyx hgt
                  | false => rfl
                have h' : unionMainFwd la lb (lo.set w x) F' (i + 1)
                    (j + 1) (w + 1) = .ok (i', j', w', lo') := by
                  simpa [unionMainFwd, dite_eq_left hA, dite_eq_left hB,
                    hAi, hBj, hne1, hne2] using hfwd
                have hcapC : (w + 1) + (la.length - (i + 1)) +
                    (lb.length - (j + 1)) ≤ (lo.set w x).length := by
                  rw [List.length_set]; omega
                obtain ⟨hi', hj', hw', hlen⟩ :=
                  ih _ _ _ _ _ _ _ _ (by omega) (by omega) hcapC h'
                exact ⟨hi', hj', hset ▸ hw', hlen.trans hset⟩
      · simp only [unionMainFwd, dite_eq_left hA,
          dite_eq_right hB] at hfwd
        simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hfwd
        exact ⟨hi, hj, by omega, rfl⟩
    · simp only [unionMainFwd, dite_eq_right hA] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hfwd
      exact ⟨hi, hj, by omega, rfl⟩

/-- Drain-`a` model bounds. -/
theorem unionDrainAFwd_le (la : List (BitVec 32)) (F' i w : Nat)
    (lo : List (BitVec 32)) (i' w' : Nat) (lo' : List (BitVec 32))
    (hi : i ≤ la.length)
    (hcap : w + (la.length - i) ≤ lo.length)
    (hfwd : unionDrainAFwd la lo F' i w = .ok (i', w', lo')) :
    i' ≤ la.length ∧ w' ≤ lo.length ∧ lo'.length = lo.length := by
  induction F' generalizing lo i w i' w' lo' with
  | zero =>
    simp only [unionDrainAFwd, Except.ok.injEq, Prod.mk.injEq] at hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hfwd
    exact ⟨hi, by omega, rfl⟩
  | succ F' ih =>
    by_cases hA : i < la.length
    · cases hAi : la[i]? with
      | none =>
        simp only [unionDrainAFwd, dite_eq_left hA, hAi] at hfwd
        cases hfwd
      | some x =>
        have h' : unionDrainAFwd la (lo.set w x) F' (i + 1) (w + 1) =
            .ok (i', w', lo') := by
          simpa [unionDrainAFwd, dite_eq_left hA, hAi] using hfwd
        have hset : (lo.set w x).length = lo.length :=
          List.length_set
        have hcapA : (w + 1) + (la.length - (i + 1)) ≤
            (lo.set w x).length := by
            rw [List.length_set]; omega
        obtain ⟨hi', hw', hlen⟩ :=
          ih _ _ _ _ _ _ (by omega) hcapA h'
        exact ⟨hi', hset ▸ hw', hlen.trans hset⟩
    · simp only [unionDrainAFwd, dite_eq_right hA] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hfwd
      exact ⟨hi, by omega, rfl⟩

/-- Drain-`b` model bounds. -/
theorem unionDrainBFwd_le (lb : List (BitVec 32)) (F' j w : Nat)
    (lo : List (BitVec 32)) (j' w' : Nat) (lo' : List (BitVec 32))
    (hj : j ≤ lb.length)
    (hcap : w + (lb.length - j) ≤ lo.length)
    (hfwd : unionDrainBFwd lb lo F' j w = .ok (j', w', lo')) :
    j' ≤ lb.length ∧ w' ≤ lo.length ∧ lo'.length = lo.length := by
  induction F' generalizing lo j w j' w' lo' with
  | zero =>
    simp only [unionDrainBFwd, Except.ok.injEq, Prod.mk.injEq] at hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hfwd
    exact ⟨hj, by omega, rfl⟩
  | succ F' ih =>
    by_cases hB : j < lb.length
    · cases hBj : lb[j]? with
      | none =>
        simp only [unionDrainBFwd, dite_eq_left hB, hBj] at hfwd
        cases hfwd
      | some y =>
        have h' : unionDrainBFwd lb (lo.set w y) F' (j + 1) (w + 1) =
            .ok (j', w', lo') := by
          simpa [unionDrainBFwd, dite_eq_left hB, hBj] using hfwd
        have hset : (lo.set w y).length = lo.length :=
          List.length_set
        have hcapB : (w + 1) + (lb.length - (j + 1)) ≤
            (lo.set w y).length := by
            rw [List.length_set]; omega
        obtain ⟨hj', hw', hlen⟩ :=
          ih _ _ _ _ _ _ (by omega) hcapB h'
        exact ⟨hj', hset ▸ hw', hlen.trans hset⟩
    · simp only [unionDrainBFwd, dite_eq_right hB] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hfwd
      exact ⟨hj, by omega, rfl⟩
