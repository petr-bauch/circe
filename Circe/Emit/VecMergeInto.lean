/-
M out-of-place two-pointer merge over `std::vector<int>` (merge-sort kernel).

Corpus: `tests/cpp/vec_merge_into.cpp` → `tests/cir/vec_merge_into.cir`
(entry `_Z14vec_merge_intoRKSt6vectorIiSaIiEES3_RS1_`: two
`sharedBorrow` inputs + one `mutBorrow` output pre-sized by the
caller, `void` out; three sequential `cir.while` loops — main
two-pointer loop with a short-circuit `&&` (`cir.ternary`) guard,
two drain loops; reads via const `at()`, writes via non-const
`at()`).

Model (the `vecAt`/`vecAtSet` fusion precedents): every `at()` call
fuses into its guard + pure read (`stdVecAt`) or borrowed store
(`vecSet`). The `&&` maps directly onto the existing pure ternary
(`tif` — short-circuit shape preserved, no new connective). Each
`out.at(k)` write carries its own `if k < len` / `fail` (the write
guard lives in the leaf per call — short `out` aborts loudly, the
`vec_at_set` miss precedent). The main loop advances `i` or `j`
(plus `k`); drains advance one input (plus `k`). Sortedness is
caller debt (agreement holds regardless, the V1 precedent).
-/
import Circe.Emit.VecAtSet

/-- Function name (Itanium mangling of a `vec_merge_into` free function
taking `const vector<int>&` + `const vector<int>&` + `vector<int>&`,
returning `void`). -/
def vecMergeIntoName : String :=
  "_Z14vec_merge_intoRKSt6vectorIiSaIiEES3_RS1_"

/-- Main-loop body: compare heads, store the smaller, advance. -/
def vecMergeMainBody : CStmt :=
  (.if_ (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "b" (.var "j")))
    (.seq (.if_ (.ult (.var "k") (.stdVecLen "out"))
              (.vecSet "out" (.var "k") (.stdVecAt "a" (.var "i")))
              .fail)
      (.seq (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))
        (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))))
    (.seq (.if_ (.ult (.var "k") (.stdVecLen "out"))
              (.vecSet "out" (.var "k") (.stdVecAt "b" (.var "j")))
              .fail)
      (.seq (.assign "j" (.uadd (.var "j") (.lit (.u64 1))))
        (.assign "k" (.uadd (.var "k") (.lit (.u64 1)))))))

/-- Main loop `while (i < na && j < nb) body` (short-circuit `&&` as
    the pure ternary). -/
def vecMergeMain : CStmt :=
  (.while_ (.tif (.ult (.var "i") (.stdVecLen "a"))
              (.ult (.var "j") (.stdVecLen "b"))
              (.lit (.b false)))
    vecMergeMainBody)

/-- Drain-`a` body: copy the head, advance. -/
def vecMergeDrainABody : CStmt :=
  (.seq (.if_ (.ult (.var "k") (.stdVecLen "out"))
            (.vecSet "out" (.var "k") (.stdVecAt "a" (.var "i")))
            .fail)
    (.seq (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))
      (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))))

/-- Drain-`a` loop `while (i < na) body`. -/
def vecMergeDrainA : CStmt :=
  (.while_ (.ult (.var "i") (.stdVecLen "a")) vecMergeDrainABody)

/-- Drain-`b` body: copy the head, advance. -/
def vecMergeDrainBBody : CStmt :=
  (.seq (.if_ (.ult (.var "k") (.stdVecLen "out"))
            (.vecSet "out" (.var "k") (.stdVecAt "b" (.var "j")))
            .fail)
    (.seq (.assign "j" (.uadd (.var "j") (.lit (.u64 1))))
      (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))))

/-- Drain-`b` loop `while (j < nb) body`. -/
def vecMergeDrainB : CStmt :=
  (.while_ (.ult (.var "j") (.stdVecLen "b")) vecMergeDrainBBody)

/-- Whole function: `let_`-prelude binds `i/j/k`, three sequential
    loops, the updated `out` words return (`xor_n` out-param idiom). -/
def vecMergeIntoFunc : Func :=
  ⟨vecMergeIntoName,
   [{ name := "a", ty := stdVecObjTy, role := .sharedBorrow },
    { name := "b", ty := stdVecObjTy, role := .sharedBorrow },
    { name := "out", ty := stdVecObjTy, role := .mutBorrow 0 }],
   stdVecObjTy,
   (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
     (.seq (.let_ "j" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
       (.seq (.let_ "k" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
         (.seq vecMergeMain
           (.seq vecMergeDrainA
             (.seq vecMergeDrainB
               (.return_ (.var "out"))))))))⟩

/-- Loop environment (borrowed words + `u64` indices), in prelude
    `let_` cons order (`i`, `j`, `k` bound in that order over
    `[a, b, out]`, so the entry bridge is `rfl` — the V2
    `mkTwoSumEnv` precedent). -/
def mkMergeEnv (la lb lo : List (BitVec 32)) (i j k : BitVec 64) : Env :=
  [("k", .u64 k), ("j", .u64 j), ("i", .u64 i),
   ("a", .stdVecVal la), ("b", .stdVecVal lb), ("out", .stdVecVal lo)]

theorem mkMergeEnv_a (la lb lo : List (BitVec 32)) (i j k : BitVec 64) :
    envLookup (mkMergeEnv la lb lo i j k) "a" = some (.stdVecVal la) := by
  simp [mkMergeEnv, envLookup, show ("a" : String) ≠ "k" by decide,
    show ("a" : String) ≠ "j" by decide,
    show ("a" : String) ≠ "i" by decide]

theorem mkMergeEnv_b (la lb lo : List (BitVec 32)) (i j k : BitVec 64) :
    envLookup (mkMergeEnv la lb lo i j k) "b" = some (.stdVecVal lb) := by
  simp [mkMergeEnv, envLookup, show ("b" : String) ≠ "k" by decide,
    show ("b" : String) ≠ "j" by decide,
    show ("b" : String) ≠ "i" by decide,
    show ("b" : String) ≠ "a" by decide]

theorem mkMergeEnv_out (la lb lo : List (BitVec 32)) (i j k : BitVec 64) :
    envLookup (mkMergeEnv la lb lo i j k) "out" =
      some (.stdVecVal lo) := by
  simp [mkMergeEnv, envLookup, show ("out" : String) ≠ "k" by decide,
    show ("out" : String) ≠ "j" by decide,
    show ("out" : String) ≠ "i" by decide,
    show ("out" : String) ≠ "a" by decide,
    show ("out" : String) ≠ "b" by decide]

theorem mkMergeEnv_i (la lb lo : List (BitVec 32)) (i j k : BitVec 64) :
    envLookup (mkMergeEnv la lb lo i j k) "i" = some (.u64 i) := by
  simp [mkMergeEnv, envLookup, show ("i" : String) ≠ "k" by decide,
    show ("i" : String) ≠ "j" by decide]

theorem mkMergeEnv_j (la lb lo : List (BitVec 32)) (i j k : BitVec 64) :
    envLookup (mkMergeEnv la lb lo i j k) "j" = some (.u64 j) := by
  simp [mkMergeEnv, envLookup, show ("j" : String) ≠ "k" by decide]

theorem mkMergeEnv_k (la lb lo : List (BitVec 32)) (i j k : BitVec 64) :
    envLookup (mkMergeEnv la lb lo i j k) "k" = some (.u64 k) := by
  simp [mkMergeEnv, envLookup]

/-! ## Forward models (fuel-threaded, mirroring the loops) -/

/-- Main-loop model: fuel + indices + current `out` words. Fuel 0
    returns the words so far (no more progress — the V1
    miss-default idiom); short `out` aborts loudly. -/
def mergeMainFwd (la lb : List (BitVec 32)) : List (BitVec 32) →
    Nat → Nat → Nat → Nat →
    Result (Nat × Nat × Nat × List (BitVec 32))
  | lo, 0, i, j, k => .ok (i, j, k, lo)
  | lo, fuel + 1, i, j, k =>
    if _ : i < la.length then
      if _ : j < lb.length then
        match lo[k]? with
        | none => .error .AssertFail
        | some _ =>
          match la[i]?, lb[j]? with
          | some x, some y =>
            if x.slt y then mergeMainFwd la lb (lo.set k x) fuel (i + 1) j (k + 1)
            else mergeMainFwd la lb (lo.set k y) fuel i (j + 1) (k + 1)
          | _, _ => .error .AssertFail
      else .ok (i, j, k, lo)
    else .ok (i, j, k, lo)

/-- Drain-`a` model. -/
def mergeDrainAFwd (la : List (BitVec 32)) : List (BitVec 32) →
    Nat → Nat → Nat → Result (Nat × Nat × List (BitVec 32))
  | lo, 0, i, k => .ok (i, k, lo)
  | lo, fuel + 1, i, k =>
    if _ : i < la.length then
      match lo[k]? with
      | none => .error .AssertFail
      | some _ =>
        match la[i]? with
        | some x => mergeDrainAFwd la (lo.set k x) fuel (i + 1) (k + 1)
        | none => .error .AssertFail
    else .ok (i, k, lo)

/-- Drain-`b` model. -/
def mergeDrainBFwd (lb : List (BitVec 32)) : List (BitVec 32) →
    Nat → Nat → Nat → Result (Nat × Nat × List (BitVec 32))
  | lo, 0, i, k => .ok (i, k, lo)
  | lo, fuel + 1, i, k =>
    if _ : i < lb.length then
      match lo[k]? with
      | none => .error .AssertFail
      | some _ =>
        match lb[i]? with
        | some x => mergeDrainBFwd lb (lo.set k x) fuel (i + 1) (k + 1)
        | none => .error .AssertFail
    else .ok (i, k, lo)

/-- Whole-function forward: main, then drains, then the words.
    Model fuels are measure-exact (remaining iterations), matching
    the induction hypotheses — no slack, no fuel-monotonicity side
    lemma. -/
def vecMergeIntoFwd (la lb lo : List (BitVec 32)) : Result Value :=
  match mergeMainFwd la lb lo (la.length + lb.length) 0 0 0 with
  | .error e => .error e
  | .ok (i, j, k, lo') =>
    match mergeDrainAFwd la lo' (la.length - i) i k with
    | .error e => .error e
    | .ok (_, k', lo'') =>
      match mergeDrainBFwd lb lo'' (lb.length - j) j k' with
      | .error e => .error e
      | .ok (_, _, lo''') => .ok (.stdVecVal lo''')

/-! ## Guard, read, and increment lemmas -/

/-- Wrapping increments stay exact below `2 ^ 64` (the V1 midpoint
    Nat-correctness idiom). -/
theorem bv64_succ_toNat (i : BitVec 64) (n : Nat)
    (h : i.toNat < n) (hn : n < 2 ^ 64) :
    (i + 1).toNat = i.toNat + 1 := by
  have h1 : (1 : BitVec 64).toNat = 1 := rfl
  rw [BitVec.toNat_add, h1]
  exact Nat.mod_eq_of_lt (by omega)

theorem mergeGuardI_eval (la lb lo : List (BitVec 32))
    (i j k : BitVec 64) (hlen : la.length < 2 ^ 64) :
    evalExpr (.ult (.var "i") (.stdVecLen "a"))
      (mkMergeEnv la lb lo i j k) =
      .ok (.b (decide (i.toNat < la.length))) := by
  have ha := mkMergeEnv_a la lb lo i j k
  have hi := mkMergeEnv_i la lb lo i j k
  have hsize : evalExpr (.stdVecLen "a")
      (mkMergeEnv la lb lo i j k) =
      .ok (.u64 (BitVec.ofNat 64 la.length)) :=
    evalExpr_stdVecLen_some "a" _ la ha
  have hnv : evalExpr (.var "i") (mkMergeEnv la lb lo i j k) =
      .ok (.u64 i) :=
    evalExpr_var_hit _ _ _ hi
  have hult := evalExpr_ult_u64 _ _ _ _ _ hnv hsize
  rw [ult_ofNat64_len i la.length hlen] at hult
  exact hult

theorem mergeGuardJ_eval (la lb lo : List (BitVec 32))
    (i j k : BitVec 64) (hlen : lb.length < 2 ^ 64) :
    evalExpr (.ult (.var "j") (.stdVecLen "b"))
      (mkMergeEnv la lb lo i j k) =
      .ok (.b (decide (j.toNat < lb.length))) := by
  have hb := mkMergeEnv_b la lb lo i j k
  have hj := mkMergeEnv_j la lb lo i j k
  have hsize : evalExpr (.stdVecLen "b")
      (mkMergeEnv la lb lo i j k) =
      .ok (.u64 (BitVec.ofNat 64 lb.length)) :=
    evalExpr_stdVecLen_some "b" _ lb hb
  have hnv : evalExpr (.var "j") (mkMergeEnv la lb lo i j k) =
      .ok (.u64 j) :=
    evalExpr_var_hit _ _ _ hj
  have hult := evalExpr_ult_u64 _ _ _ _ _ hnv hsize
  rw [ult_ofNat64_len j lb.length hlen] at hult
  exact hult

theorem mergeGuardK_eval (la lb lo : List (BitVec 32))
    (i j k : BitVec 64) (hlen : lo.length < 2 ^ 64) :
    evalExpr (.ult (.var "k") (.stdVecLen "out"))
      (mkMergeEnv la lb lo i j k) =
      .ok (.b (decide (k.toNat < lo.length))) := by
  have ho := mkMergeEnv_out la lb lo i j k
  have hk := mkMergeEnv_k la lb lo i j k
  have hsize : evalExpr (.stdVecLen "out")
      (mkMergeEnv la lb lo i j k) =
      .ok (.u64 (BitVec.ofNat 64 lo.length)) :=
    evalExpr_stdVecLen_some "out" _ lo ho
  have hnv : evalExpr (.var "k") (mkMergeEnv la lb lo i j k) =
      .ok (.u64 k) :=
    evalExpr_var_hit _ _ _ hk
  have hult := evalExpr_ult_u64 _ _ _ _ _ hnv hsize
  rw [ult_ofNat64_len k lo.length hlen] at hult
  exact hult

/-- The main-loop `&&` guard holds iff both indices are live. -/
theorem mergeMainGuard_true (la lb lo : List (BitVec 32))
    (i j k : BitVec 64)
    (hlena : la.length < 2 ^ 64) (hlenb : lb.length < 2 ^ 64)
    (hA : i.toNat < la.length) (hB : j.toNat < lb.length) :
    evalExpr (.tif (.ult (.var "i") (.stdVecLen "a"))
                (.ult (.var "j") (.stdVecLen "b"))
                (.lit (.b false)))
      (mkMergeEnv la lb lo i j k) = .ok (.b true) := by
  have hA' : evalExpr (.ult (.var "i") (.stdVecLen "a"))
      (mkMergeEnv la lb lo i j k) = .ok (.b true) := by
    have h := mergeGuardI_eval la lb lo i j k hlena
    rwa [decide_eq_true hA] at h
  have hB' : evalExpr (.ult (.var "j") (.stdVecLen "b"))
      (mkMergeEnv la lb lo i j k) = .ok (.b true) := by
    have h := mergeGuardJ_eval la lb lo i j k hlenb
    rwa [decide_eq_true hB] at h
  rw [evalExpr_tif_true _ _ _ _ hA']
  exact hB'

/-- The main-loop guard fails iff some index is spent. -/
theorem mergeMainGuard_false (la lb lo : List (BitVec 32))
    (i j k : BitVec 64)
    (hlena : la.length < 2 ^ 64) (hlenb : lb.length < 2 ^ 64)
    (h : ¬ (i.toNat < la.length ∧ j.toNat < lb.length)) :
    evalExpr (.tif (.ult (.var "i") (.stdVecLen "a"))
                (.ult (.var "j") (.stdVecLen "b"))
                (.lit (.b false)))
      (mkMergeEnv la lb lo i j k) = .ok (.b false) := by
  by_cases hA : i.toNat < la.length
  · have hnB : ¬ j.toNat < lb.length := fun hj => h ⟨hA, hj⟩
    have hA' : evalExpr (.ult (.var "i") (.stdVecLen "a"))
        (mkMergeEnv la lb lo i j k) = .ok (.b true) := by
      have h := mergeGuardI_eval la lb lo i j k hlena
      rwa [decide_eq_true hA] at h
    have hB' : evalExpr (.ult (.var "j") (.stdVecLen "b"))
        (mkMergeEnv la lb lo i j k) = .ok (.b false) := by
      have h := mergeGuardJ_eval la lb lo i j k hlenb
      rwa [decide_eq_false hnB] at h
    rw [evalExpr_tif_true _ _ _ _ hA']
    exact hB'
  · have hA' : evalExpr (.ult (.var "i") (.stdVecLen "a"))
        (mkMergeEnv la lb lo i j k) = .ok (.b false) := by
      have h := mergeGuardI_eval la lb lo i j k hlena
      rwa [decide_eq_false hA] at h
    have hlit : evalExpr (.lit (.b false)) (mkMergeEnv la lb lo i j k) =
        .ok (.b false) := by
      simp [evalExpr, litVal]
    rw [evalExpr_tif_false _ _ _ _ hA']
    exact hlit

theorem mergeReadA_hit (la lb lo : List (BitVec 32))
    (i j k : BitVec 64) (x : BitVec 32)
    (hget : la[i.toNat]? = some x) :
    evalExpr (.stdVecAt "a" (.var "i")) (mkMergeEnv la lb lo i j k) =
      .ok (.i32 x) :=
  evalExpr_stdVecAt_some "a" _ _ _ _ _
    (mkMergeEnv_a la lb lo i j k)
    (evalExpr_var_hit _ _ _ (mkMergeEnv_i la lb lo i j k)) hget

theorem mergeReadB_hit (la lb lo : List (BitVec 32))
    (i j k : BitVec 64) (y : BitVec 32)
    (hget : lb[j.toNat]? = some y) :
    evalExpr (.stdVecAt "b" (.var "j")) (mkMergeEnv la lb lo i j k) =
      .ok (.i32 y) :=
  evalExpr_stdVecAt_some "b" _ _ _ _ _
    (mkMergeEnv_b la lb lo i j k)
    (evalExpr_var_hit _ _ _ (mkMergeEnv_j la lb lo i j k)) hget

/-- Index increments (any fuel). -/
theorem mergeIncrI (F : Nat) (la lb lo : List (BitVec 32))
    (i j k : BitVec 64) :
    evalStmtFuel F
      (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))
      (mkMergeEnv la lb lo i j k) =
      .ok (mkMergeEnv la lb lo (i + 1) j k, .fellThrough) := by
  have hi : evalExpr (.uadd (.var "i") (.lit (.u64 1)))
      (mkMergeEnv la lb lo i j k) = .ok (.u64 (i + 1)) := by
    have h1 : evalExpr (.lit (.u64 1)) (mkMergeEnv la lb lo i j k) =
        .ok (.u64 1) := by
      simp [evalExpr, litVal]
    exact evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ (mkMergeEnv_i la lb lo i j k)) h1
  have hu : envUpdate (mkMergeEnv la lb lo i j k) "i" (.u64 (i + 1)) =
      some (mkMergeEnv la lb lo (i + 1) j k) := rfl
  exact evalStmtFuel_assign F _ _ _ _ _ hi hu

theorem mergeIncrJ (F : Nat) (la lb lo : List (BitVec 32))
    (i j k : BitVec 64) :
    evalStmtFuel F
      (.assign "j" (.uadd (.var "j") (.lit (.u64 1))))
      (mkMergeEnv la lb lo i j k) =
      .ok (mkMergeEnv la lb lo i (j + 1) k, .fellThrough) := by
  have hj : evalExpr (.uadd (.var "j") (.lit (.u64 1)))
      (mkMergeEnv la lb lo i j k) = .ok (.u64 (j + 1)) := by
    have h1 : evalExpr (.lit (.u64 1)) (mkMergeEnv la lb lo i j k) =
        .ok (.u64 1) := by
      simp [evalExpr, litVal]
    exact evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ (mkMergeEnv_j la lb lo i j k)) h1
  have hu : envUpdate (mkMergeEnv la lb lo i j k) "j" (.u64 (j + 1)) =
      some (mkMergeEnv la lb lo i (j + 1) k) := rfl
  exact evalStmtFuel_assign F _ _ _ _ _ hj hu

theorem mergeIncrK (F : Nat) (la lb lo : List (BitVec 32))
    (i j k : BitVec 64) :
    evalStmtFuel F
      (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))
      (mkMergeEnv la lb lo i j k) =
      .ok (mkMergeEnv la lb lo i j (k + 1), .fellThrough) := by
  have hk : evalExpr (.uadd (.var "k") (.lit (.u64 1)))
      (mkMergeEnv la lb lo i j k) = .ok (.u64 (k + 1)) := by
    have h1 : evalExpr (.lit (.u64 1)) (mkMergeEnv la lb lo i j k) =
        .ok (.u64 1) := by
      simp [evalExpr, litVal]
    exact evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ (mkMergeEnv_k la lb lo i j k)) h1
  have hu : envUpdate (mkMergeEnv la lb lo i j k) "k" (.u64 (k + 1)) =
      some (mkMergeEnv la lb lo i j (k + 1)) := rfl
  exact evalStmtFuel_assign F _ _ _ _ _ hk hu

/-! ## Body steps (loop-free) -/

/-- Main body, take-`a` hit: heads compare, `k` live, store + advance. -/
theorem vecMergeMainBody_hitA (F : Nat) (la lb lo : List (BitVec 32))
    (i j k : BitVec 64) (x y w : BitVec 32)
    (hleno : lo.length < 2 ^ 64)
    (hgetA : la[i.toNat]? = some x) (hgetB : lb[j.toNat]? = some y)
    (hltXY : (x.slt y) = true)
    (hltK : k.toNat < lo.length)
    (hgetK : lo[k.toNat]? = some w) :
    evalStmtFuel F vecMergeMainBody (mkMergeEnv la lb lo i j k) =
      .ok (mkMergeEnv la lb (lo.set k.toNat x) (i + 1) j (k + 1),
        .fellThrough) := by
  have hbody : vecMergeMainBody =
      (.if_ (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "b" (.var "j")))
        (.seq (.if_ (.ult (.var "k") (.stdVecLen "out"))
                  (.vecSet "out" (.var "k")
                    (.stdVecAt "a" (.var "i")))
                  .fail)
          (.seq (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))
            (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))))
        (.seq (.if_ (.ult (.var "k") (.stdVecLen "out"))
                  (.vecSet "out" (.var "k")
                    (.stdVecAt "b" (.var "j")))
                  .fail)
          (.seq (.assign "j" (.uadd (.var "j") (.lit (.u64 1))))
            (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))))) := rfl
  have hrA := mergeReadA_hit la lb lo i j k x hgetA
  have hrB := mergeReadB_hit la lb lo i j k y hgetB
  have hslt : evalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "b" (.var "j")))
      (mkMergeEnv la lb lo i j k) = .ok (.b true) := by
    have h := evalExpr_slt_i32 _ _ _ _ _ hrA hrB
    rwa [hltXY] at h
  have hcK : evalExpr (.ult (.var "k") (.stdVecLen "out"))
      (mkMergeEnv la lb lo i j k) = .ok (.b true) := by
    have h := mergeGuardK_eval la lb lo i j k hleno
    rwa [decide_eq_true hltK] at h
  have hvec := evalStmtFuel_vecSet F "out" (.var "k")
    (.stdVecAt "a" (.var "i")) (mkMergeEnv la lb lo i j k)
    k x lo w _ (evalExpr_var_hit _ _ _ (mkMergeEnv_k la lb lo i j k))
    hrA (mkMergeEnv_out la lb lo i j k) hgetK rfl
  have hincrI := mergeIncrI F la lb (lo.set k.toNat x) i j k
  have hincrK := mergeIncrK F la lb (lo.set k.toNat x) (i + 1) j k
  have hinner := (evalStmtFuel_seq_fallthrough F _ _ _ _ hincrI).trans hincrK
  have hwrite := ((evalStmtFuel_if_true F _ _ .fail _ hcK).trans hvec)
  have hseq := (evalStmtFuel_seq_fallthrough F _ _ _ _ hwrite).trans hinner
  rw [hbody]
  exact (evalStmtFuel_if_true F _ _ _ _ hslt).trans hseq

/-- Main body, take-`b` hit. -/
theorem vecMergeMainBody_hitB (F : Nat) (la lb lo : List (BitVec 32))
    (i j k : BitVec 64) (x y w : BitVec 32)
    (hleno : lo.length < 2 ^ 64)
    (hgetA : la[i.toNat]? = some x) (hgetB : lb[j.toNat]? = some y)
    (hltXY : (x.slt y) = false)
    (hltK : k.toNat < lo.length)
    (hgetK : lo[k.toNat]? = some w) :
    evalStmtFuel F vecMergeMainBody (mkMergeEnv la lb lo i j k) =
      .ok (mkMergeEnv la lb (lo.set k.toNat y) i (j + 1) (k + 1),
        .fellThrough) := by
  have hbody : vecMergeMainBody =
      (.if_ (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "b" (.var "j")))
        (.seq (.if_ (.ult (.var "k") (.stdVecLen "out"))
                  (.vecSet "out" (.var "k")
                    (.stdVecAt "a" (.var "i")))
                  .fail)
          (.seq (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))
            (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))))
        (.seq (.if_ (.ult (.var "k") (.stdVecLen "out"))
                  (.vecSet "out" (.var "k")
                    (.stdVecAt "b" (.var "j")))
                  .fail)
          (.seq (.assign "j" (.uadd (.var "j") (.lit (.u64 1))))
            (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))))) := rfl
  have hrA := mergeReadA_hit la lb lo i j k x hgetA
  have hrB := mergeReadB_hit la lb lo i j k y hgetB
  have hslt : evalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "b" (.var "j")))
      (mkMergeEnv la lb lo i j k) = .ok (.b false) := by
    have h := evalExpr_slt_i32 _ _ _ _ _ hrA hrB
    rwa [hltXY] at h
  have hcK : evalExpr (.ult (.var "k") (.stdVecLen "out"))
      (mkMergeEnv la lb lo i j k) = .ok (.b true) := by
    have h := mergeGuardK_eval la lb lo i j k hleno
    rwa [decide_eq_true hltK] at h
  have hvec := evalStmtFuel_vecSet F "out" (.var "k")
    (.stdVecAt "b" (.var "j")) (mkMergeEnv la lb lo i j k)
    k y lo w _ (evalExpr_var_hit _ _ _ (mkMergeEnv_k la lb lo i j k))
    hrB (mkMergeEnv_out la lb lo i j k) hgetK rfl
  have hincrJ := mergeIncrJ F la lb (lo.set k.toNat y) i j k
  have hincrK := mergeIncrK F la lb (lo.set k.toNat y) i (j + 1) k
  have hinner := (evalStmtFuel_seq_fallthrough F _ _ _ _ hincrJ).trans hincrK
  have hwrite := ((evalStmtFuel_if_true F _ _ .fail _ hcK).trans hvec)
  have hseq := (evalStmtFuel_seq_fallthrough F _ _ _ _ hwrite).trans hinner
  rw [hbody]
  exact (evalStmtFuel_if_false F _ _ _ _ hslt).trans hseq

/-- Main body, short-`out` miss (take-`a` side): loud abort. -/
theorem vecMergeMainBody_missA (F : Nat) (la lb lo : List (BitVec 32))
    (i j k : BitVec 64) (x y : BitVec 32)
    (hleno : lo.length < 2 ^ 64)
    (hgetA : la[i.toNat]? = some x) (hgetB : lb[j.toNat]? = some y)
    (hltXY : (x.slt y) = true)
    (hltK : ¬ k.toNat < lo.length) :
    evalStmtFuel F vecMergeMainBody (mkMergeEnv la lb lo i j k) =
      .error .AssertFail := by
  have hbody : vecMergeMainBody =
      (.if_ (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "b" (.var "j")))
        (.seq (.if_ (.ult (.var "k") (.stdVecLen "out"))
                  (.vecSet "out" (.var "k")
                    (.stdVecAt "a" (.var "i")))
                  .fail)
          (.seq (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))
            (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))))
        (.seq (.if_ (.ult (.var "k") (.stdVecLen "out"))
                  (.vecSet "out" (.var "k")
                    (.stdVecAt "b" (.var "j")))
                  .fail)
          (.seq (.assign "j" (.uadd (.var "j") (.lit (.u64 1))))
            (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))))) := rfl
  have hrA := mergeReadA_hit la lb lo i j k x hgetA
  have hrB := mergeReadB_hit la lb lo i j k y hgetB
  have hslt : evalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "b" (.var "j")))
      (mkMergeEnv la lb lo i j k) = .ok (.b true) := by
    have h := evalExpr_slt_i32 _ _ _ _ _ hrA hrB
    rwa [hltXY] at h
  have hcK : evalExpr (.ult (.var "k") (.stdVecLen "out"))
      (mkMergeEnv la lb lo i j k) = .ok (.b false) := by
    have h := mergeGuardK_eval la lb lo i j k hleno
    rwa [decide_eq_false hltK] at h
  have hfail := (evalStmtFuel_if_false F _
      (.vecSet "out" (.var "k") (.stdVecAt "a" (.var "i"))) _ _ hcK).trans
    (evalStmtFuel_fail F _)
  have hseq := evalStmtFuel_seq_err F _
      (.seq (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))
        (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))) _ _ hfail
  rw [hbody]
  exact (evalStmtFuel_if_true F _ _ _ _ hslt).trans hseq

/-- Main body, short-`out` miss (take-`b` side): loud abort. -/
theorem vecMergeMainBody_missB (F : Nat) (la lb lo : List (BitVec 32))
    (i j k : BitVec 64) (x y : BitVec 32)
    (hleno : lo.length < 2 ^ 64)
    (hgetA : la[i.toNat]? = some x) (hgetB : lb[j.toNat]? = some y)
    (hltXY : (x.slt y) = false)
    (hltK : ¬ k.toNat < lo.length) :
    evalStmtFuel F vecMergeMainBody (mkMergeEnv la lb lo i j k) =
      .error .AssertFail := by
  have hbody : vecMergeMainBody =
      (.if_ (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "b" (.var "j")))
        (.seq (.if_ (.ult (.var "k") (.stdVecLen "out"))
                  (.vecSet "out" (.var "k")
                    (.stdVecAt "a" (.var "i")))
                  .fail)
          (.seq (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))
            (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))))
        (.seq (.if_ (.ult (.var "k") (.stdVecLen "out"))
                  (.vecSet "out" (.var "k")
                    (.stdVecAt "b" (.var "j")))
                  .fail)
          (.seq (.assign "j" (.uadd (.var "j") (.lit (.u64 1))))
            (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))))) := rfl
  have hrA := mergeReadA_hit la lb lo i j k x hgetA
  have hrB := mergeReadB_hit la lb lo i j k y hgetB
  have hslt : evalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "b" (.var "j")))
      (mkMergeEnv la lb lo i j k) = .ok (.b false) := by
    have h := evalExpr_slt_i32 _ _ _ _ _ hrA hrB
    rwa [hltXY] at h
  have hcK : evalExpr (.ult (.var "k") (.stdVecLen "out"))
      (mkMergeEnv la lb lo i j k) = .ok (.b false) := by
    have h := mergeGuardK_eval la lb lo i j k hleno
    rwa [decide_eq_false hltK] at h
  have hfail := (evalStmtFuel_if_false F _
      (.vecSet "out" (.var "k") (.stdVecAt "b" (.var "j"))) _ _ hcK).trans
    (evalStmtFuel_fail F _)
  have hseq := evalStmtFuel_seq_err F _
      (.seq (.assign "j" (.uadd (.var "j") (.lit (.u64 1))))
        (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))) _ _ hfail
  rw [hbody]
  exact (evalStmtFuel_if_false F _ _ _ _ hslt).trans hseq

/-- Drain-`a` body hit: `k` live, store + advance. -/
theorem vecMergeDrainABody_hit (F : Nat) (la lb lo : List (BitVec 32))
    (i j k : BitVec 64) (x w : BitVec 32)
    (hleno : lo.length < 2 ^ 64)
    (hgetA : la[i.toNat]? = some x)
    (hltK : k.toNat < lo.length)
    (hgetK : lo[k.toNat]? = some w) :
    evalStmtFuel F vecMergeDrainABody (mkMergeEnv la lb lo i j k) =
      .ok (mkMergeEnv la lb (lo.set k.toNat x) (i + 1) j (k + 1),
        .fellThrough) := by
  have hbody : vecMergeDrainABody =
      (.seq (.if_ (.ult (.var "k") (.stdVecLen "out"))
                (.vecSet "out" (.var "k")
                  (.stdVecAt "a" (.var "i")))
                .fail)
        (.seq (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))
          (.assign "k" (.uadd (.var "k") (.lit (.u64 1)))))) := rfl
  have hrA := mergeReadA_hit la lb lo i j k x hgetA
  have hcK : evalExpr (.ult (.var "k") (.stdVecLen "out"))
      (mkMergeEnv la lb lo i j k) = .ok (.b true) := by
    have h := mergeGuardK_eval la lb lo i j k hleno
    rwa [decide_eq_true hltK] at h
  have hvec := evalStmtFuel_vecSet F "out" (.var "k")
    (.stdVecAt "a" (.var "i")) (mkMergeEnv la lb lo i j k)
    k x lo w _ (evalExpr_var_hit _ _ _ (mkMergeEnv_k la lb lo i j k))
    hrA (mkMergeEnv_out la lb lo i j k) hgetK rfl
  have hincrI := mergeIncrI F la lb (lo.set k.toNat x) i j k
  have hincrK := mergeIncrK F la lb (lo.set k.toNat x) (i + 1) j k
  have hinner := (evalStmtFuel_seq_fallthrough F _ _ _ _ hincrI).trans hincrK
  have hwrite := (evalStmtFuel_if_true F _ _ .fail _ hcK).trans hvec
  have hseq := (evalStmtFuel_seq_fallthrough F _ _ _ _ hwrite).trans hinner
  rw [hbody]
  exact hseq

/-- Drain-`a` body miss: loud abort. -/
theorem vecMergeDrainABody_miss (F : Nat) (la lb lo : List (BitVec 32))
    (i j k : BitVec 64)
    (hleno : lo.length < 2 ^ 64)
    (hltK : ¬ k.toNat < lo.length) :
    evalStmtFuel F vecMergeDrainABody (mkMergeEnv la lb lo i j k) =
      .error .AssertFail := by
  have hbody : vecMergeDrainABody =
      (.seq (.if_ (.ult (.var "k") (.stdVecLen "out"))
                (.vecSet "out" (.var "k")
                  (.stdVecAt "a" (.var "i")))
                .fail)
        (.seq (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))
          (.assign "k" (.uadd (.var "k") (.lit (.u64 1)))))) := rfl
  have hcK : evalExpr (.ult (.var "k") (.stdVecLen "out"))
      (mkMergeEnv la lb lo i j k) = .ok (.b false) := by
    have h := mergeGuardK_eval la lb lo i j k hleno
    rwa [decide_eq_false hltK] at h
  have hfail := (evalStmtFuel_if_false F _
      (.vecSet "out" (.var "k") (.stdVecAt "a" (.var "i"))) _ _ hcK).trans
    (evalStmtFuel_fail F _)
  have hseq := evalStmtFuel_seq_err F _
      (.seq (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))
        (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))) _ _ hfail
  rw [hbody]
  exact hseq

/-- Drain-`b` body hit: `k` live, store + advance. -/
theorem vecMergeDrainBBody_hit (F : Nat) (la lb lo : List (BitVec 32))
    (i j k : BitVec 64) (y w : BitVec 32)
    (hleno : lo.length < 2 ^ 64)
    (hgetB : lb[j.toNat]? = some y)
    (hltK : k.toNat < lo.length)
    (hgetK : lo[k.toNat]? = some w) :
    evalStmtFuel F vecMergeDrainBBody (mkMergeEnv la lb lo i j k) =
      .ok (mkMergeEnv la lb (lo.set k.toNat y) i (j + 1) (k + 1),
        .fellThrough) := by
  have hbody : vecMergeDrainBBody =
      (.seq (.if_ (.ult (.var "k") (.stdVecLen "out"))
                (.vecSet "out" (.var "k")
                  (.stdVecAt "b" (.var "j")))
                .fail)
        (.seq (.assign "j" (.uadd (.var "j") (.lit (.u64 1))))
          (.assign "k" (.uadd (.var "k") (.lit (.u64 1)))))) := rfl
  have hrB := mergeReadB_hit la lb lo i j k y hgetB
  have hcK : evalExpr (.ult (.var "k") (.stdVecLen "out"))
      (mkMergeEnv la lb lo i j k) = .ok (.b true) := by
    have h := mergeGuardK_eval la lb lo i j k hleno
    rwa [decide_eq_true hltK] at h
  have hvec := evalStmtFuel_vecSet F "out" (.var "k")
    (.stdVecAt "b" (.var "j")) (mkMergeEnv la lb lo i j k)
    k y lo w _ (evalExpr_var_hit _ _ _ (mkMergeEnv_k la lb lo i j k))
    hrB (mkMergeEnv_out la lb lo i j k) hgetK rfl
  have hincrJ := mergeIncrJ F la lb (lo.set k.toNat y) i j k
  have hincrK := mergeIncrK F la lb (lo.set k.toNat y) i (j + 1) k
  have hinner := (evalStmtFuel_seq_fallthrough F _ _ _ _ hincrJ).trans hincrK
  have hwrite := (evalStmtFuel_if_true F _ _ .fail _ hcK).trans hvec
  have hseq := (evalStmtFuel_seq_fallthrough F _ _ _ _ hwrite).trans hinner
  rw [hbody]
  exact hseq

/-- Drain-`b` body miss: loud abort. -/
theorem vecMergeDrainBBody_miss (F : Nat) (la lb lo : List (BitVec 32))
    (i j k : BitVec 64)
    (hleno : lo.length < 2 ^ 64)
    (hltK : ¬ k.toNat < lo.length) :
    evalStmtFuel F vecMergeDrainBBody (mkMergeEnv la lb lo i j k) =
      .error .AssertFail := by
  have hbody : vecMergeDrainBBody =
      (.seq (.if_ (.ult (.var "k") (.stdVecLen "out"))
                (.vecSet "out" (.var "k")
                  (.stdVecAt "b" (.var "j")))
                .fail)
        (.seq (.assign "j" (.uadd (.var "j") (.lit (.u64 1))))
          (.assign "k" (.uadd (.var "k") (.lit (.u64 1)))))) := rfl
  have hcK : evalExpr (.ult (.var "k") (.stdVecLen "out"))
      (mkMergeEnv la lb lo i j k) = .ok (.b false) := by
    have h := mergeGuardK_eval la lb lo i j k hleno
    rwa [decide_eq_false hltK] at h
  have hfail := (evalStmtFuel_if_false F _
      (.vecSet "out" (.var "k") (.stdVecAt "b" (.var "j"))) _ _ hcK).trans
    (evalStmtFuel_fail F _)
  have hseq := evalStmtFuel_seq_err F _
      (.seq (.assign "j" (.uadd (.var "j") (.lit (.u64 1))))
        (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))) _ _ hfail
  rw [hbody]
  exact hseq

/-! ## Loop inductions (fuel-generalized, model-driven) -/

theorem bv64_ofNat_toNat (i : BitVec 64) :
    BitVec.ofNat 64 i.toNat = i := by simp

/-- `some` lookup is live (contrapositive of the verified
    `getElem?_eq_none`). -/
theorem list_lt_of_getElem?_some (l : List (BitVec 32)) (n : Nat)
    (w : BitVec 32) (hget : l[n]? = some w) : n < l.length := by
  by_cases h : n < l.length
  · exact h
  · have hc' : l.length ≤ n := by omega
    have hnone := List.getElem?_eq_none hc'
    rw [hnone] at hget
    cases hget

/-- Main-loop ok soundness: the model outcome ⟹ evaluation agrees. -/
theorem mergeMain_ok (F : Nat) (la lb lo : List (BitVec 32))
    (i j k : BitVec 64) (i' j' k' : Nat) (lo' : List (BitVec 32))
    (hlena : la.length < 2 ^ 64) (hlenb : lb.length < 2 ^ 64)
    (hleno : lo.length < 2 ^ 64)
    (hF : (la.length - i.toNat) + (lb.length - j.toNat) + 1 ≤ F)
    (hfwd : mergeMainFwd la lb lo
      ((la.length - i.toNat) + (lb.length - j.toNat))
      i.toNat j.toNat k.toNat = .ok (i', j', k', lo')) :
    evalStmtFuel F vecMergeMain (mkMergeEnv la lb lo i j k) =
      .ok (mkMergeEnv la lb lo' (BitVec.ofNat 64 i')
        (BitVec.ofNat 64 j') (BitVec.ofNat 64 k'), .fellThrough) := by
  induction F generalizing la lb lo i j k i' j' k' lo' with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hguard : (i.toNat < la.length ∧ j.toNat < lb.length)
    · obtain ⟨hA, hB⟩ := hguard
      have hcond : evalExpr
          (.tif (.ult (.var "i") (.stdVecLen "a"))
            (.ult (.var "j") (.stdVecLen "b"))
            (.lit (.b false)))
          (mkMergeEnv la lb lo i j k) = .ok (.b true) :=
        mergeMainGuard_true la lb lo i j k hlena hlenb hA hB
      have hM : (la.length - i.toNat) + (lb.length - j.toNat) =
          ((la.length - i.toNat) + (lb.length - j.toNat) - 1) + 1 := by
        omega
      rw [hM] at hfwd
      have hgetA : la[i.toNat]? = some la[i.toNat] :=
        List.getElem?_eq_getElem hA
      have hgetB : lb[j.toNat]? = some lb[j.toNat] :=
        List.getElem?_eq_getElem hB
      cases hgetK : lo[k.toNat]? with
      | none =>
        have hcontra : mergeMainFwd la lb lo
            (((la.length - i.toNat) + (lb.length - j.toNat) - 1) + 1)
            i.toNat j.toNat k.toNat = .error .AssertFail := by
          simp only [mergeMainFwd, dite_eq_left hA, dite_eq_left hB, hgetK]
        rw [hcontra] at hfwd
        cases hfwd
      | some w =>
        have hltK : k.toNat < lo.length :=
          list_lt_of_getElem?_some lo k.toNat w hgetK
        by_cases hslt : (la[i.toNat].slt lb[j.toNat]) = true
        · have hfwdA : mergeMainFwd la lb (lo.set k.toNat la[i.toNat])
              ((la.length - i.toNat) + (lb.length - j.toNat) - 1)
              (i.toNat + 1) j.toNat (k.toNat + 1) =
              .ok (i', j', k', lo') := by
            have h := hfwd
            simp only [mergeMainFwd, dite_eq_left hA, dite_eq_left hB, hgetK, hgetA, hgetB,
              hslt] at h
            exact h
          have hstep : evalStmtFuel F vecMergeMainBody
              (mkMergeEnv la lb lo i j k) =
              .ok (mkMergeEnv la lb (lo.set k.toNat la[i.toNat])
                (i + 1) j (k + 1), .fellThrough) :=
            vecMergeMainBody_hitA F la lb lo i j k _ _ _
              hleno hgetA hgetB hslt hltK hgetK
          have hloop : evalStmtFuel (F + 1) vecMergeMain
              (mkMergeEnv la lb lo i j k) =
              evalStmtFuel F vecMergeMain
                (mkMergeEnv la lb (lo.set k.toNat la[i.toNat])
                  (i + 1) j (k + 1)) := by
            simp [vecMergeMain, evalStmtFuel, evalStmtSuccHandler,
              evalStmtWith, hcond, hstep]
          have h1i : (i + 1).toNat = i.toNat + 1 :=
            bv64_succ_toNat i _ hA hlena
          have h1k : (k + 1).toNat = k.toNat + 1 :=
            bv64_succ_toNat k _ hltK hleno
          have hleno' : (lo.set k.toNat la[i.toNat]).length < 2 ^ 64 := by
            rw [List.length_set]
            exact hleno
          have hF' : (la.length - (i + 1).toNat) +
              (lb.length - j.toNat) + 1 ≤ F := by omega
          have hfwd' : mergeMainFwd la lb (lo.set k.toNat la[i.toNat])
              ((la.length - (i + 1).toNat) + (lb.length - j.toNat))
              ((i + 1).toNat) j.toNat ((k + 1).toNat) =
              .ok (i', j', k', lo') := by
            have hM' : (la.length - i.toNat) + (lb.length - j.toNat) - 1 =
                (la.length - (i + 1).toNat) + (lb.length - j.toNat) := by
              omega
            rw [← h1i, ← h1k, hM'] at hfwdA
            exact hfwdA
          rw [hloop]
          exact ih _ _ _ _ _ _ _ _ _ _ hlena hlenb hleno'
            hF' hfwd'
        · have hsltF : (la[i.toNat].slt lb[j.toNat]) = false :=
            Bool.eq_false_of_ne_true hslt
          have hfwdB : mergeMainFwd la lb (lo.set k.toNat lb[j.toNat])
              ((la.length - i.toNat) + (lb.length - j.toNat) - 1)
              i.toNat (j.toNat + 1) (k.toNat + 1) =
              .ok (i', j', k', lo') := by
            have h := hfwd
            simp only [mergeMainFwd, dite_eq_left hA, dite_eq_left hB, hgetK, hgetA, hgetB,
              hsltF] at h
            exact h
          have hstep : evalStmtFuel F vecMergeMainBody
              (mkMergeEnv la lb lo i j k) =
              .ok (mkMergeEnv la lb (lo.set k.toNat lb[j.toNat])
                i (j + 1) (k + 1), .fellThrough) :=
            vecMergeMainBody_hitB F la lb lo i j k _ _ _
              hleno hgetA hgetB hsltF hltK hgetK
          have hloop : evalStmtFuel (F + 1) vecMergeMain
              (mkMergeEnv la lb lo i j k) =
              evalStmtFuel F vecMergeMain
                (mkMergeEnv la lb (lo.set k.toNat lb[j.toNat])
                  i (j + 1) (k + 1)) := by
            simp [vecMergeMain, evalStmtFuel, evalStmtSuccHandler,
              evalStmtWith, hcond, hstep]
          have h1j : (j + 1).toNat = j.toNat + 1 :=
            bv64_succ_toNat j _ hB hlenb
          have h1k : (k + 1).toNat = k.toNat + 1 :=
            bv64_succ_toNat k _ hltK hleno
          have hleno' : (lo.set k.toNat lb[j.toNat]).length < 2 ^ 64 := by
            rw [List.length_set]
            exact hleno
          have hF' : (la.length - i.toNat) +
              (lb.length - (j + 1).toNat) + 1 ≤ F := by omega
          have hfwd' : mergeMainFwd la lb (lo.set k.toNat lb[j.toNat])
              ((la.length - i.toNat) + (lb.length - (j + 1).toNat))
              i.toNat ((j + 1).toNat) ((k + 1).toNat) =
              .ok (i', j', k', lo') := by
            have hM' : (la.length - i.toNat) + (lb.length - j.toNat) - 1 =
                (la.length - i.toNat) + (lb.length - (j + 1).toNat) := by
              omega
            rw [← h1j, ← h1k, hM'] at hfwdB
            exact hfwdB
          rw [hloop]
          exact ih _ _ _ _ _ _ _ _ _ _ hlena hlenb hleno'
            hF' hfwd'
    · have hcond : evalExpr
          (.tif (.ult (.var "i") (.stdVecLen "a"))
            (.ult (.var "j") (.stdVecLen "b"))
            (.lit (.b false)))
          (mkMergeEnv la lb lo i j k) = .ok (.b false) :=
        mergeMainGuard_false la lb lo i j k hlena hlenb hguard
      have hfwd0 : mergeMainFwd la lb lo
          ((la.length - i.toNat) + (lb.length - j.toNat))
          i.toNat j.toNat k.toNat =
          .ok (i.toNat, j.toNat, k.toNat, lo) := by
        match hm : (la.length - i.toNat) + (lb.length - j.toNat) with
        | 0 => simp only [mergeMainFwd]
        | _ + 1 =>
          by_cases hA' : i.toNat < la.length
          · have hnB : ¬ j.toNat < lb.length :=
              fun hj => hguard ⟨hA', hj⟩
            simp only [mergeMainFwd, dite_eq_left hA', dite_eq_right hnB]
          · simp only [mergeMainFwd, dite_eq_right hA']
      rw [hfwd0] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hfwd
      have hexit : evalStmtFuel (F + 1) vecMergeMain
          (mkMergeEnv la lb lo i j k) =
          .ok (mkMergeEnv la lb lo i j k, .fellThrough) := by
        simp [vecMergeMain, evalStmtFuel, evalStmtSuccHandler,
          evalStmtWith, hcond]
      rw [hexit, bv64_ofNat_toNat i, bv64_ofNat_toNat j,
        bv64_ofNat_toNat k]

/-- Main-loop err soundness: the model abort ⟹ evaluation aborts. -/
theorem mergeMain_err (F : Nat) (la lb lo : List (BitVec 32))
    (i j k : BitVec 64) (e : Panic)
    (hlena : la.length < 2 ^ 64) (hlenb : lb.length < 2 ^ 64)
    (hleno : lo.length < 2 ^ 64)
    (hF : (la.length - i.toNat) + (lb.length - j.toNat) + 1 ≤ F)
    (hfwd : mergeMainFwd la lb lo
      ((la.length - i.toNat) + (lb.length - j.toNat))
      i.toNat j.toNat k.toNat = .error e) :
    evalStmtFuel F vecMergeMain (mkMergeEnv la lb lo i j k) =
      .error e := by
  induction F generalizing la lb lo i j k e with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hguard : (i.toNat < la.length ∧ j.toNat < lb.length)
    · obtain ⟨hA, hB⟩ := hguard
      have hcond : evalExpr
          (.tif (.ult (.var "i") (.stdVecLen "a"))
            (.ult (.var "j") (.stdVecLen "b"))
            (.lit (.b false)))
          (mkMergeEnv la lb lo i j k) = .ok (.b true) :=
        mergeMainGuard_true la lb lo i j k hlena hlenb hA hB
      have hM : (la.length - i.toNat) + (lb.length - j.toNat) =
          ((la.length - i.toNat) + (lb.length - j.toNat) - 1) + 1 := by
        omega
      rw [hM] at hfwd
      have hgetA : la[i.toNat]? = some la[i.toNat] :=
        List.getElem?_eq_getElem hA
      have hgetB : lb[j.toNat]? = some lb[j.toNat] :=
        List.getElem?_eq_getElem hB
      cases hgetK : lo[k.toNat]? with
      | none =>
        have hfwde : mergeMainFwd la lb lo
            (((la.length - i.toNat) + (lb.length - j.toNat) - 1) + 1)
            i.toNat j.toNat k.toNat = .error .AssertFail := by
          simp only [mergeMainFwd, dite_eq_left hA, dite_eq_left hB,
            hgetK]
        rw [hfwde] at hfwd
        cases hfwd
        have hltK : ¬ k.toNat < lo.length := by
          intro hc
          have hsome := List.getElem?_eq_getElem hc
          rw [hsome] at hgetK
          cases hgetK
        by_cases hslt : (la[i.toNat].slt lb[j.toNat]) = true
        · have hbody := vecMergeMainBody_missA F la lb lo i j k _ _
            hleno hgetA hgetB hslt hltK
          have herr : evalStmtFuel (F + 1) vecMergeMain
              (mkMergeEnv la lb lo i j k) = .error .AssertFail := by
            simp [vecMergeMain, evalStmtFuel, evalStmtSuccHandler,
              evalStmtWith, hcond, hbody]
          exact herr
        · have hsltF : (la[i.toNat].slt lb[j.toNat]) = false :=
            Bool.eq_false_of_ne_true hslt
          have hbody := vecMergeMainBody_missB F la lb lo i j k _ _
            hleno hgetA hgetB hsltF hltK
          have herr : evalStmtFuel (F + 1) vecMergeMain
              (mkMergeEnv la lb lo i j k) = .error .AssertFail := by
            simp [vecMergeMain, evalStmtFuel, evalStmtSuccHandler,
              evalStmtWith, hcond, hbody]
          exact herr
      | some w =>
        have hltK : k.toNat < lo.length :=
          list_lt_of_getElem?_some lo k.toNat w hgetK
        by_cases hslt : (la[i.toNat].slt lb[j.toNat]) = true
        · have hfwdA : mergeMainFwd la lb (lo.set k.toNat la[i.toNat])
              ((la.length - i.toNat) + (lb.length - j.toNat) - 1)
              (i.toNat + 1) j.toNat (k.toNat + 1) = .error e := by
            have h := hfwd
            simp only [mergeMainFwd, dite_eq_left hA, dite_eq_left hB,
              hgetK, hgetA, hgetB, hslt] at h
            exact h
          have hstep : evalStmtFuel F vecMergeMainBody
              (mkMergeEnv la lb lo i j k) =
              .ok (mkMergeEnv la lb (lo.set k.toNat la[i.toNat])
                (i + 1) j (k + 1), .fellThrough) :=
            vecMergeMainBody_hitA F la lb lo i j k _ _ _
              hleno hgetA hgetB hslt hltK hgetK
          have hloop : evalStmtFuel (F + 1) vecMergeMain
              (mkMergeEnv la lb lo i j k) =
              evalStmtFuel F vecMergeMain
                (mkMergeEnv la lb (lo.set k.toNat la[i.toNat])
                  (i + 1) j (k + 1)) := by
            simp [vecMergeMain, evalStmtFuel, evalStmtSuccHandler,
              evalStmtWith, hcond, hstep]
          have h1i : (i + 1).toNat = i.toNat + 1 :=
            bv64_succ_toNat i _ hA hlena
          have h1k : (k + 1).toNat = k.toNat + 1 :=
            bv64_succ_toNat k _ hltK hleno
          have hleno' : (lo.set k.toNat la[i.toNat]).length < 2 ^ 64 := by
            rw [List.length_set]
            exact hleno
          have hF' : (la.length - (i + 1).toNat) +
              (lb.length - j.toNat) + 1 ≤ F := by omega
          have hfwd' : mergeMainFwd la lb (lo.set k.toNat la[i.toNat])
              ((la.length - (i + 1).toNat) + (lb.length - j.toNat))
              ((i + 1).toNat) j.toNat ((k + 1).toNat) = .error e := by
            have hM' : (la.length - i.toNat) + (lb.length - j.toNat) - 1 =
                (la.length - (i + 1).toNat) + (lb.length - j.toNat) := by
              omega
            rw [← h1i, ← h1k, hM'] at hfwdA
            exact hfwdA
          rw [hloop]
          exact ih _ _ _ _ _ _ _ hlena hlenb hleno' hF' hfwd'
        · have hsltF : (la[i.toNat].slt lb[j.toNat]) = false :=
            Bool.eq_false_of_ne_true hslt
          have hfwdB : mergeMainFwd la lb (lo.set k.toNat lb[j.toNat])
              ((la.length - i.toNat) + (lb.length - j.toNat) - 1)
              i.toNat (j.toNat + 1) (k.toNat + 1) = .error e := by
            have h := hfwd
            simp only [mergeMainFwd, dite_eq_left hA, dite_eq_left hB,
              hgetK, hgetA, hgetB, hsltF] at h
            exact h
          have hstep : evalStmtFuel F vecMergeMainBody
              (mkMergeEnv la lb lo i j k) =
              .ok (mkMergeEnv la lb (lo.set k.toNat lb[j.toNat])
                i (j + 1) (k + 1), .fellThrough) :=
            vecMergeMainBody_hitB F la lb lo i j k _ _ _
              hleno hgetA hgetB hsltF hltK hgetK
          have hloop : evalStmtFuel (F + 1) vecMergeMain
              (mkMergeEnv la lb lo i j k) =
              evalStmtFuel F vecMergeMain
                (mkMergeEnv la lb (lo.set k.toNat lb[j.toNat])
                  i (j + 1) (k + 1)) := by
            simp [vecMergeMain, evalStmtFuel, evalStmtSuccHandler,
              evalStmtWith, hcond, hstep]
          have h1j : (j + 1).toNat = j.toNat + 1 :=
            bv64_succ_toNat j _ hB hlenb
          have h1k : (k + 1).toNat = k.toNat + 1 :=
            bv64_succ_toNat k _ hltK hleno
          have hleno' : (lo.set k.toNat lb[j.toNat]).length < 2 ^ 64 := by
            rw [List.length_set]
            exact hleno
          have hF' : (la.length - i.toNat) +
              (lb.length - (j + 1).toNat) + 1 ≤ F := by omega
          have hfwd' : mergeMainFwd la lb (lo.set k.toNat lb[j.toNat])
              ((la.length - i.toNat) + (lb.length - (j + 1).toNat))
              i.toNat ((j + 1).toNat) ((k + 1).toNat) = .error e := by
            have hM' : (la.length - i.toNat) + (lb.length - j.toNat) - 1 =
                (la.length - i.toNat) + (lb.length - (j + 1).toNat) := by
              omega
            rw [← h1j, ← h1k, hM'] at hfwdB
            exact hfwdB
          rw [hloop]
          exact ih _ _ _ _ _ _ _ hlena hlenb hleno' hF' hfwd'
    · have hcond : evalExpr
          (.tif (.ult (.var "i") (.stdVecLen "a"))
            (.ult (.var "j") (.stdVecLen "b"))
            (.lit (.b false)))
          (mkMergeEnv la lb lo i j k) = .ok (.b false) :=
        mergeMainGuard_false la lb lo i j k hlena hlenb hguard
      have hfwd0 : mergeMainFwd la lb lo
          ((la.length - i.toNat) + (lb.length - j.toNat))
          i.toNat j.toNat k.toNat =
          .ok (i.toNat, j.toNat, k.toNat, lo) := by
        match hm : (la.length - i.toNat) + (lb.length - j.toNat) with
        | 0 => simp only [mergeMainFwd]
        | _ + 1 =>
          by_cases hA' : i.toNat < la.length
          · have hnB : ¬ j.toNat < lb.length :=
              fun hj => hguard ⟨hA', hj⟩
            simp only [mergeMainFwd, dite_eq_left hA', dite_eq_right hnB]
          · simp only [mergeMainFwd, dite_eq_right hA']
      rw [hfwd0] at hfwd
      cases hfwd

/-- Drain-`a` ok soundness. -/
theorem mergeDrainA_ok (F : Nat) (la lb lo : List (BitVec 32))
    (i j k : BitVec 64) (i' k' : Nat) (lo' : List (BitVec 32))
    (hlena : la.length < 2 ^ 64) (hleno : lo.length < 2 ^ 64)
    (hF : (la.length - i.toNat) + 1 ≤ F)
    (hfwd : mergeDrainAFwd la lo (la.length - i.toNat) i.toNat k.toNat =
      .ok (i', k', lo')) :
    evalStmtFuel F vecMergeDrainA (mkMergeEnv la lb lo i j k) =
      .ok (mkMergeEnv la lb lo' (BitVec.ofNat 64 i') j
        (BitVec.ofNat 64 k'), .fellThrough) := by
  induction F generalizing la lb lo i j k i' k' lo' with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hA : i.toNat < la.length
    · have hcond : evalExpr (.ult (.var "i") (.stdVecLen "a"))
          (mkMergeEnv la lb lo i j k) = .ok (.b true) := by
        have h := mergeGuardI_eval la lb lo i j k hlena
        rwa [decide_eq_true hA] at h
      have hM : (la.length - i.toNat) =
          ((la.length - i.toNat) - 1) + 1 := by omega
      rw [hM] at hfwd
      have hgetA : la[i.toNat]? = some la[i.toNat] :=
        List.getElem?_eq_getElem hA
      cases hgetK : lo[k.toNat]? with
      | none =>
        have hcontra : mergeDrainAFwd la lo
            (((la.length - i.toNat) - 1) + 1)
            i.toNat k.toNat = .error .AssertFail := by
          simp only [mergeDrainAFwd, dite_eq_left hA, hgetK]
        rw [hcontra] at hfwd
        cases hfwd
      | some w =>
        have hltK : k.toNat < lo.length :=
          list_lt_of_getElem?_some lo k.toNat w hgetK
        have hfwdA : mergeDrainAFwd la (lo.set k.toNat la[i.toNat])
            ((la.length - i.toNat) - 1)
            (i.toNat + 1) (k.toNat + 1) = .ok (i', k', lo') := by
          have h := hfwd
          simp only [mergeDrainAFwd, dite_eq_left hA, hgetK, hgetA] at h
          exact h
        have hstep : evalStmtFuel F vecMergeDrainABody
            (mkMergeEnv la lb lo i j k) =
            .ok (mkMergeEnv la lb (lo.set k.toNat la[i.toNat])
              (i + 1) j (k + 1), .fellThrough) :=
          vecMergeDrainABody_hit F la lb lo i j k _ _
            hleno hgetA hltK hgetK
        have hloop : evalStmtFuel (F + 1) vecMergeDrainA
            (mkMergeEnv la lb lo i j k) =
            evalStmtFuel F vecMergeDrainA
              (mkMergeEnv la lb (lo.set k.toNat la[i.toNat])
                (i + 1) j (k + 1)) := by
          simp [vecMergeDrainA, evalStmtFuel, evalStmtSuccHandler,
            evalStmtWith, hcond, hstep]
        have h1i : (i + 1).toNat = i.toNat + 1 :=
          bv64_succ_toNat i _ hA hlena
        have h1k : (k + 1).toNat = k.toNat + 1 :=
          bv64_succ_toNat k _ hltK hleno
        have hleno' : (lo.set k.toNat la[i.toNat]).length < 2 ^ 64 := by
          rw [List.length_set]
          exact hleno
        have hF' : (la.length - (i + 1).toNat) + 1 ≤ F := by omega
        have hfwd' : mergeDrainAFwd la (lo.set k.toNat la[i.toNat])
            (la.length - (i + 1).toNat)
            ((i + 1).toNat) ((k + 1).toNat) = .ok (i', k', lo') := by
          have hM' : (la.length - i.toNat) - 1 =
              (la.length - (i + 1).toNat) := by
            omega
          rw [← h1i, ← h1k, hM'] at hfwdA
          exact hfwdA
        rw [hloop]
        exact ih _ _ _ _ _ _ _ _ _ hlena hleno' hF' hfwd'
    · have hcond : evalExpr (.ult (.var "i") (.stdVecLen "a"))
          (mkMergeEnv la lb lo i j k) = .ok (.b false) := by
        have h := mergeGuardI_eval la lb lo i j k hlena
        rwa [decide_eq_false hA] at h
      have hfwd0 : mergeDrainAFwd la lo (la.length - i.toNat)
          i.toNat k.toNat = .ok (i.toNat, k.toNat, lo) := by
        match hm : (la.length - i.toNat) with
        | 0 => simp only [mergeDrainAFwd]
        | _ + 1 =>
          simp only [mergeDrainAFwd, dite_eq_right hA]
      rw [hfwd0] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hfwd
      have hexit : evalStmtFuel (F + 1) vecMergeDrainA
          (mkMergeEnv la lb lo i j k) =
          .ok (mkMergeEnv la lb lo i j k, .fellThrough) := by
        simp [vecMergeDrainA, evalStmtFuel, evalStmtSuccHandler,
          evalStmtWith, hcond]
      rw [hexit, bv64_ofNat_toNat i, bv64_ofNat_toNat k]

/-- Drain-`a` err soundness. -/
theorem mergeDrainA_err (F : Nat) (la lb lo : List (BitVec 32))
    (i j k : BitVec 64) (e : Panic)
    (hlena : la.length < 2 ^ 64) (hleno : lo.length < 2 ^ 64)
    (hF : (la.length - i.toNat) + 1 ≤ F)
    (hfwd : mergeDrainAFwd la lo (la.length - i.toNat) i.toNat k.toNat =
      .error e) :
    evalStmtFuel F vecMergeDrainA (mkMergeEnv la lb lo i j k) =
      .error e := by
  induction F generalizing la lb lo i j k e with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hA : i.toNat < la.length
    · have hcond : evalExpr (.ult (.var "i") (.stdVecLen "a"))
          (mkMergeEnv la lb lo i j k) = .ok (.b true) := by
        have h := mergeGuardI_eval la lb lo i j k hlena
        rwa [decide_eq_true hA] at h
      have hM : (la.length - i.toNat) =
          ((la.length - i.toNat) - 1) + 1 := by omega
      rw [hM] at hfwd
      have hgetA : la[i.toNat]? = some la[i.toNat] :=
        List.getElem?_eq_getElem hA
      cases hgetK : lo[k.toNat]? with
      | none =>
        have hfwde : mergeDrainAFwd la lo
            (((la.length - i.toNat) - 1) + 1)
            i.toNat k.toNat = .error .AssertFail := by
          simp only [mergeDrainAFwd, dite_eq_left hA, hgetK]
        rw [hfwde] at hfwd
        cases hfwd
        have hltK : ¬ k.toNat < lo.length := by
          intro hc
          have hsome := List.getElem?_eq_getElem hc
          rw [hsome] at hgetK
          cases hgetK
        have hbody := vecMergeDrainABody_miss F la lb lo i j k
          hleno hltK
        have herr : evalStmtFuel (F + 1) vecMergeDrainA
            (mkMergeEnv la lb lo i j k) = .error .AssertFail := by
          simp [vecMergeDrainA, evalStmtFuel, evalStmtSuccHandler,
            evalStmtWith, hcond, hbody]
        exact herr
      | some w =>
        have hltK : k.toNat < lo.length :=
          list_lt_of_getElem?_some lo k.toNat w hgetK
        have hfwdA : mergeDrainAFwd la (lo.set k.toNat la[i.toNat])
            ((la.length - i.toNat) - 1)
            (i.toNat + 1) (k.toNat + 1) = .error e := by
          have h := hfwd
          simp only [mergeDrainAFwd, dite_eq_left hA, hgetK, hgetA] at h
          exact h
        have hstep : evalStmtFuel F vecMergeDrainABody
            (mkMergeEnv la lb lo i j k) =
            .ok (mkMergeEnv la lb (lo.set k.toNat la[i.toNat])
              (i + 1) j (k + 1), .fellThrough) :=
          vecMergeDrainABody_hit F la lb lo i j k _ _
            hleno hgetA hltK hgetK
        have hloop : evalStmtFuel (F + 1) vecMergeDrainA
            (mkMergeEnv la lb lo i j k) =
            evalStmtFuel F vecMergeDrainA
              (mkMergeEnv la lb (lo.set k.toNat la[i.toNat])
                (i + 1) j (k + 1)) := by
          simp [vecMergeDrainA, evalStmtFuel, evalStmtSuccHandler,
            evalStmtWith, hcond, hstep]
        have h1i : (i + 1).toNat = i.toNat + 1 :=
          bv64_succ_toNat i _ hA hlena
        have h1k : (k + 1).toNat = k.toNat + 1 :=
          bv64_succ_toNat k _ hltK hleno
        have hleno' : (lo.set k.toNat la[i.toNat]).length < 2 ^ 64 := by
          rw [List.length_set]
          exact hleno
        have hF' : (la.length - (i + 1).toNat) + 1 ≤ F := by omega
        have hfwd' : mergeDrainAFwd la (lo.set k.toNat la[i.toNat])
            (la.length - (i + 1).toNat)
            ((i + 1).toNat) ((k + 1).toNat) = .error e := by
          have hM' : (la.length - i.toNat) - 1 =
              (la.length - (i + 1).toNat) := by
            omega
          rw [← h1i, ← h1k, hM'] at hfwdA
          exact hfwdA
        rw [hloop]
        exact ih _ _ _ _ _ _ _ hlena hleno' hF' hfwd'
    · have hcond : evalExpr (.ult (.var "i") (.stdVecLen "a"))
          (mkMergeEnv la lb lo i j k) = .ok (.b false) := by
        have h := mergeGuardI_eval la lb lo i j k hlena
        rwa [decide_eq_false hA] at h
      have hfwd0 : mergeDrainAFwd la lo (la.length - i.toNat)
          i.toNat k.toNat = .ok (i.toNat, k.toNat, lo) := by
        match hm : (la.length - i.toNat) with
        | 0 => simp only [mergeDrainAFwd]
        | _ + 1 =>
          simp only [mergeDrainAFwd, dite_eq_right hA]
      rw [hfwd0] at hfwd
      cases hfwd

/-- Drain-`b` ok soundness. -/
theorem mergeDrainB_ok (F : Nat) (la lb lo : List (BitVec 32))
    (i j k : BitVec 64) (j' k' : Nat) (lo' : List (BitVec 32))
    (hlenb : lb.length < 2 ^ 64) (hleno : lo.length < 2 ^ 64)
    (hF : (lb.length - j.toNat) + 1 ≤ F)
    (hfwd : mergeDrainBFwd lb lo (lb.length - j.toNat) j.toNat k.toNat =
      .ok (j', k', lo')) :
    evalStmtFuel F vecMergeDrainB (mkMergeEnv la lb lo i j k) =
      .ok (mkMergeEnv la lb lo' i (BitVec.ofNat 64 j')
        (BitVec.ofNat 64 k'), .fellThrough) := by
  induction F generalizing la lb lo i j k j' k' lo' with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hB : j.toNat < lb.length
    · have hcond : evalExpr (.ult (.var "j") (.stdVecLen "b"))
          (mkMergeEnv la lb lo i j k) = .ok (.b true) := by
        have h := mergeGuardJ_eval la lb lo i j k hlenb
        rwa [decide_eq_true hB] at h
      have hM : (lb.length - j.toNat) =
          ((lb.length - j.toNat) - 1) + 1 := by omega
      rw [hM] at hfwd
      have hgetB : lb[j.toNat]? = some lb[j.toNat] :=
        List.getElem?_eq_getElem hB
      cases hgetK : lo[k.toNat]? with
      | none =>
        have hcontra : mergeDrainBFwd lb lo
            (((lb.length - j.toNat) - 1) + 1)
            j.toNat k.toNat = .error .AssertFail := by
          simp only [mergeDrainBFwd, dite_eq_left hB, hgetK]
        rw [hcontra] at hfwd
        cases hfwd
      | some w =>
        have hltK : k.toNat < lo.length :=
          list_lt_of_getElem?_some lo k.toNat w hgetK
        have hfwdB : mergeDrainBFwd lb (lo.set k.toNat lb[j.toNat])
            ((lb.length - j.toNat) - 1)
            (j.toNat + 1) (k.toNat + 1) = .ok (j', k', lo') := by
          have h := hfwd
          simp only [mergeDrainBFwd, dite_eq_left hB, hgetK, hgetB] at h
          exact h
        have hstep : evalStmtFuel F vecMergeDrainBBody
            (mkMergeEnv la lb lo i j k) =
            .ok (mkMergeEnv la lb (lo.set k.toNat lb[j.toNat])
              i (j + 1) (k + 1), .fellThrough) :=
          vecMergeDrainBBody_hit F la lb lo i j k _ _
            hleno hgetB hltK hgetK
        have hloop : evalStmtFuel (F + 1) vecMergeDrainB
            (mkMergeEnv la lb lo i j k) =
            evalStmtFuel F vecMergeDrainB
              (mkMergeEnv la lb (lo.set k.toNat lb[j.toNat])
                i (j + 1) (k + 1)) := by
          simp [vecMergeDrainB, evalStmtFuel, evalStmtSuccHandler,
            evalStmtWith, hcond, hstep]
        have h1j : (j + 1).toNat = j.toNat + 1 :=
          bv64_succ_toNat j _ hB hlenb
        have h1k : (k + 1).toNat = k.toNat + 1 :=
          bv64_succ_toNat k _ hltK hleno
        have hleno' : (lo.set k.toNat lb[j.toNat]).length < 2 ^ 64 := by
          rw [List.length_set]
          exact hleno
        have hF' : (lb.length - (j + 1).toNat) + 1 ≤ F := by omega
        have hfwd' : mergeDrainBFwd lb (lo.set k.toNat lb[j.toNat])
            (lb.length - (j + 1).toNat)
            ((j + 1).toNat) ((k + 1).toNat) = .ok (j', k', lo') := by
          have hM' : (lb.length - j.toNat) - 1 =
              (lb.length - (j + 1).toNat) := by
            omega
          rw [← h1j, ← h1k, hM'] at hfwdB
          exact hfwdB
        rw [hloop]
        exact ih _ _ _ _ _ _ _ _ _ hlenb hleno' hF' hfwd'
    · have hcond : evalExpr (.ult (.var "j") (.stdVecLen "b"))
          (mkMergeEnv la lb lo i j k) = .ok (.b false) := by
        have h := mergeGuardJ_eval la lb lo i j k hlenb
        rwa [decide_eq_false hB] at h
      have hfwd0 : mergeDrainBFwd lb lo (lb.length - j.toNat)
          j.toNat k.toNat = .ok (j.toNat, k.toNat, lo) := by
        match hm : (lb.length - j.toNat) with
        | 0 => simp only [mergeDrainBFwd]
        | _ + 1 =>
          simp only [mergeDrainBFwd, dite_eq_right hB]
      rw [hfwd0] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hfwd
      have hexit : evalStmtFuel (F + 1) vecMergeDrainB
          (mkMergeEnv la lb lo i j k) =
          .ok (mkMergeEnv la lb lo i j k, .fellThrough) := by
        simp [vecMergeDrainB, evalStmtFuel, evalStmtSuccHandler,
          evalStmtWith, hcond]
      rw [hexit, bv64_ofNat_toNat j, bv64_ofNat_toNat k]

/-- Drain-`b` err soundness. -/
theorem mergeDrainB_err (F : Nat) (la lb lo : List (BitVec 32))
    (i j k : BitVec 64) (e : Panic)
    (hlenb : lb.length < 2 ^ 64) (hleno : lo.length < 2 ^ 64)
    (hF : (lb.length - j.toNat) + 1 ≤ F)
    (hfwd : mergeDrainBFwd lb lo (lb.length - j.toNat) j.toNat k.toNat =
      .error e) :
    evalStmtFuel F vecMergeDrainB (mkMergeEnv la lb lo i j k) =
      .error e := by
  induction F generalizing la lb lo i j k e with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hB : j.toNat < lb.length
    · have hcond : evalExpr (.ult (.var "j") (.stdVecLen "b"))
          (mkMergeEnv la lb lo i j k) = .ok (.b true) := by
        have h := mergeGuardJ_eval la lb lo i j k hlenb
        rwa [decide_eq_true hB] at h
      have hM : (lb.length - j.toNat) =
          ((lb.length - j.toNat) - 1) + 1 := by omega
      rw [hM] at hfwd
      have hgetB : lb[j.toNat]? = some lb[j.toNat] :=
        List.getElem?_eq_getElem hB
      cases hgetK : lo[k.toNat]? with
      | none =>
        have hfwde : mergeDrainBFwd lb lo
            (((lb.length - j.toNat) - 1) + 1)
            j.toNat k.toNat = .error .AssertFail := by
          simp only [mergeDrainBFwd, dite_eq_left hB, hgetK]
        rw [hfwde] at hfwd
        cases hfwd
        have hltK : ¬ k.toNat < lo.length := by
          intro hc
          have hsome := List.getElem?_eq_getElem hc
          rw [hsome] at hgetK
          cases hgetK
        have hbody := vecMergeDrainBBody_miss F la lb lo i j k
          hleno hltK
        have herr : evalStmtFuel (F + 1) vecMergeDrainB
            (mkMergeEnv la lb lo i j k) = .error .AssertFail := by
          simp [vecMergeDrainB, evalStmtFuel, evalStmtSuccHandler,
            evalStmtWith, hcond, hbody]
        exact herr
      | some w =>
        have hltK : k.toNat < lo.length :=
          list_lt_of_getElem?_some lo k.toNat w hgetK
        have hfwdB : mergeDrainBFwd lb (lo.set k.toNat lb[j.toNat])
            ((lb.length - j.toNat) - 1)
            (j.toNat + 1) (k.toNat + 1) = .error e := by
          have h := hfwd
          simp only [mergeDrainBFwd, dite_eq_left hB, hgetK, hgetB] at h
          exact h
        have hstep : evalStmtFuel F vecMergeDrainBBody
            (mkMergeEnv la lb lo i j k) =
            .ok (mkMergeEnv la lb (lo.set k.toNat lb[j.toNat])
              i (j + 1) (k + 1), .fellThrough) :=
          vecMergeDrainBBody_hit F la lb lo i j k _ _
            hleno hgetB hltK hgetK
        have hloop : evalStmtFuel (F + 1) vecMergeDrainB
            (mkMergeEnv la lb lo i j k) =
            evalStmtFuel F vecMergeDrainB
              (mkMergeEnv la lb (lo.set k.toNat lb[j.toNat])
                i (j + 1) (k + 1)) := by
          simp [vecMergeDrainB, evalStmtFuel, evalStmtSuccHandler,
            evalStmtWith, hcond, hstep]
        have h1j : (j + 1).toNat = j.toNat + 1 :=
          bv64_succ_toNat j _ hB hlenb
        have h1k : (k + 1).toNat = k.toNat + 1 :=
          bv64_succ_toNat k _ hltK hleno
        have hleno' : (lo.set k.toNat lb[j.toNat]).length < 2 ^ 64 := by
          rw [List.length_set]
          exact hleno
        have hF' : (lb.length - (j + 1).toNat) + 1 ≤ F := by omega
        have hfwd' : mergeDrainBFwd lb (lo.set k.toNat lb[j.toNat])
            (lb.length - (j + 1).toNat)
            ((j + 1).toNat) ((k + 1).toNat) = .error e := by
          have hM' : (lb.length - j.toNat) - 1 =
              (lb.length - (j + 1).toNat) := by
            omega
          rw [← h1j, ← h1k, hM'] at hfwdB
          exact hfwdB
        rw [hloop]
        exact ih _ _ _ _ _ _ _ hlenb hleno' hF' hfwd'
    · have hcond : evalExpr (.ult (.var "j") (.stdVecLen "b"))
          (mkMergeEnv la lb lo i j k) = .ok (.b false) := by
        have h := mergeGuardJ_eval la lb lo i j k hlenb
        rwa [decide_eq_false hB] at h
      have hfwd0 : mergeDrainBFwd lb lo (lb.length - j.toNat)
          j.toNat k.toNat = .ok (j.toNat, k.toNat, lo) := by
        match hm : (lb.length - j.toNat) with
        | 0 => simp only [mergeDrainBFwd]
        | _ + 1 =>
          simp only [mergeDrainBFwd, dite_eq_right hB]
      rw [hfwd0] at hfwd
      cases hfwd

/-! ## Forward-model bounds (sequential chaining) -/

/-- `u64` literal round-trip under a vector-length bound (local copy of
    the V1 `ofNat64_toNat'` shape, avoiding a new import in `Emit`). -/
theorem bv64_toNat_ofNat (n : Nat) (hn : n < 2 ^ 64) :
    (BitVec.ofNat 64 n).toNat = n := by
  rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt hn

/-- Main-model results stay inside the inputs and preserve `out`
    length (fuel induction; every taken step checked its bounds). -/
theorem mergeMainFwd_le (la lb : List (BitVec 32)) (F' i j k : Nat)
    (lo : List (BitVec 32)) (i' j' k' : Nat) (lo' : List (BitVec 32))
    (hi : i ≤ la.length) (hj : j ≤ lb.length) (hk : k ≤ lo.length)
    (hfwd : mergeMainFwd la lb lo F' i j k = .ok (i', j', k', lo')) :
    i' ≤ la.length ∧ j' ≤ lb.length ∧ k' ≤ lo.length ∧
      lo'.length = lo.length := by
  induction F' generalizing lo i j k i' j' k' lo' with
  | zero =>
    simp only [mergeMainFwd, Except.ok.injEq, Prod.mk.injEq] at hfwd
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hfwd
    exact ⟨hi, hj, hk, rfl⟩
  | succ F' ih =>
    by_cases hA : i < la.length
    · by_cases hB : j < lb.length
      · cases hK : lo[k]? with
        | none =>
          simp only [mergeMainFwd, dite_eq_left hA, dite_eq_left hB,
            hK] at hfwd
          cases hfwd
        | some w =>
          have hklen : k < lo.length :=
            list_lt_of_getElem?_some lo k w hK
          cases hAi : la[i]? with
          | none =>
            cases hBj : lb[j]? with
            | none =>
              simp only [mergeMainFwd, dite_eq_left hA, dite_eq_left hB,
                hK, hAi, hBj] at hfwd
              cases hfwd
            | some y =>
              simp only [mergeMainFwd, dite_eq_left hA, dite_eq_left hB,
                hK, hAi, hBj] at hfwd
              cases hfwd
          | some x =>
            cases hBj : lb[j]? with
            | none =>
              simp only [mergeMainFwd, dite_eq_left hA, dite_eq_left hB,
                hK, hAi, hBj] at hfwd
              cases hfwd
            | some y =>
              have hset : (lo.set k x).length = lo.length :=
                List.length_set
              by_cases hslt : x.slt y
              · simp only [mergeMainFwd, dite_eq_left hA, dite_eq_left hB,
                  hK, hAi, hBj, hslt] at hfwd
                have hk1 : k + 1 ≤ (lo.set k x).length := by
                  rw [hset]; omega
                obtain ⟨hi', hj', hk', hlen⟩ :=
                  ih _ _ _ _ _ _ _ _ (by omega) hj hk1 hfwd
                exact ⟨hi', hj', hset ▸ hk', hlen.trans hset⟩
              · have hsltF : (x.slt y) = false :=
                  Bool.eq_false_of_ne_true hslt
                simp only [mergeMainFwd, dite_eq_left hA, dite_eq_left hB,
                  hK, hAi, hBj, hsltF] at hfwd
                have hsety : (lo.set k y).length = lo.length :=
                  List.length_set
                have hk1 : k + 1 ≤ (lo.set k y).length := by
                  rw [hsety]; omega
                obtain ⟨hi', hj', hk', hlen⟩ :=
                  ih _ _ _ _ _ _ _ _ hi (by omega) hk1 hfwd
                exact ⟨hi', hj', hsety ▸ hk', hlen.trans hsety⟩
      · simp only [mergeMainFwd, dite_eq_left hA,
          dite_eq_right hB] at hfwd
        simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hfwd
        exact ⟨hi, hj, hk, rfl⟩
    · simp only [mergeMainFwd, dite_eq_right hA] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hfwd
      exact ⟨hi, hj, hk, rfl⟩

/-- Drain-`a` model bounds. -/
theorem mergeDrainAFwd_le (la : List (BitVec 32)) (F' i k : Nat)
    (lo : List (BitVec 32)) (i' k' : Nat) (lo' : List (BitVec 32))
    (hi : i ≤ la.length) (hk : k ≤ lo.length)
    (hfwd : mergeDrainAFwd la lo F' i k = .ok (i', k', lo')) :
    i' ≤ la.length ∧ k' ≤ lo.length ∧ lo'.length = lo.length := by
  induction F' generalizing lo i k i' k' lo' with
  | zero =>
    simp only [mergeDrainAFwd, Except.ok.injEq, Prod.mk.injEq] at hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hfwd
    exact ⟨hi, hk, rfl⟩
  | succ F' ih =>
    by_cases hA : i < la.length
    · cases hK : lo[k]? with
      | none =>
        simp only [mergeDrainAFwd, dite_eq_left hA, hK] at hfwd
        cases hfwd
      | some w =>
        have hklen : k < lo.length :=
          list_lt_of_getElem?_some lo k w hK
        cases hAi : la[i]? with
        | none =>
          simp only [mergeDrainAFwd, dite_eq_left hA, hK, hAi] at hfwd
          cases hfwd
        | some x =>
          simp only [mergeDrainAFwd, dite_eq_left hA, hK, hAi] at hfwd
          have hset : (lo.set k x).length = lo.length :=
            List.length_set
          have hk1 : k + 1 ≤ (lo.set k x).length := by
            rw [hset]; omega
          obtain ⟨hi', hk', hlen⟩ :=
            ih _ _ _ _ _ _ (by omega) hk1 hfwd
          exact ⟨hi', hset ▸ hk', hlen.trans hset⟩
    · simp only [mergeDrainAFwd, dite_eq_right hA] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hfwd
      exact ⟨hi, hk, rfl⟩

/-- Drain-`b` model bounds. -/
theorem mergeDrainBFwd_le (lb : List (BitVec 32)) (F' j k : Nat)
    (lo : List (BitVec 32)) (j' k' : Nat) (lo' : List (BitVec 32))
    (hj : j ≤ lb.length) (hk : k ≤ lo.length)
    (hfwd : mergeDrainBFwd lb lo F' j k = .ok (j', k', lo')) :
    j' ≤ lb.length ∧ k' ≤ lo.length ∧ lo'.length = lo.length := by
  induction F' generalizing lo j k j' k' lo' with
  | zero =>
    simp only [mergeDrainBFwd, Except.ok.injEq, Prod.mk.injEq] at hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hfwd
    exact ⟨hj, hk, rfl⟩
  | succ F' ih =>
    by_cases hB : j < lb.length
    · cases hK : lo[k]? with
      | none =>
        simp only [mergeDrainBFwd, dite_eq_left hB, hK] at hfwd
        cases hfwd
      | some w =>
        have hklen : k < lo.length :=
          list_lt_of_getElem?_some lo k w hK
        cases hBj : lb[j]? with
        | none =>
          simp only [mergeDrainBFwd, dite_eq_left hB, hK, hBj] at hfwd
          cases hfwd
        | some x =>
          simp only [mergeDrainBFwd, dite_eq_left hB, hK, hBj] at hfwd
          have hset : (lo.set k x).length = lo.length :=
            List.length_set
          have hk1 : k + 1 ≤ (lo.set k x).length := by
            rw [hset]; omega
          obtain ⟨hj', hk', hlen⟩ :=
            ih _ _ _ _ _ _ (by omega) hk1 hfwd
          exact ⟨hj', hset ▸ hk', hlen.trans hset⟩
    · simp only [mergeDrainBFwd, dite_eq_right hB] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hfwd
      exact ⟨hj, hk, rfl⟩

/-! ## Entry bridge (`emit_correct`) -/

/-- `emit_correct` for `vec_merge_into`: three sequential loops chained
    at one model fuel (`seq` reuses fuel — no monotonicity side lemma),
    measure-exact model fuels throughout. -/
theorem evalFuncFuel_vecMergeInto (F : Nat) (la lb lo : List (BitVec 32))
    (hlena : la.length < 2 ^ 64) (hlenb : lb.length < 2 ^ 64)
    (hleno : lo.length < 2 ^ 64)
    (hF : (la.length + lb.length) + 1 ≤ F) :
    evalFuncFuel F vecMergeIntoFunc
      [.stdVecVal la, .stdVecVal lb, .stdVecVal lo] =
      vecMergeIntoFwd la lb lo := by
  have hz : (BitVec.ofNat 64 0).toNat = 0 := bv64_toNat_ofNat 0 (by simp)
  have hbind : bindArgs vecMergeIntoFunc.args
      [.stdVecVal la, .stdVecVal lb, .stdVecVal lo] =
      some [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)] := rfl
  have hbody : vecMergeIntoFunc.body =
      (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq (.let_ "j" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq (.let_ "k" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
            (.seq vecMergeMain
              (.seq vecMergeDrainA
                (.seq vecMergeDrainB
                  (.return_ (.var "out")))))))) := rfl
  have hlet_i : evalStmtFuel F
      (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      [("a", .stdVecVal la), ("b", .stdVecVal lb),
        ("out", .stdVecVal lo)] =
      .ok ([("i", .u64 (BitVec.ofNat 64 0)), ("a", .stdVecVal la),
        ("b", .stdVecVal lb), ("out", .stdVecVal lo)], .fellThrough) :=
    evalStmtFuel_let_ F _ _ _ _ _ (evalExpr_lit _ _)
  have hlet_j : evalStmtFuel F
      (.let_ "j" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      [("i", .u64 (BitVec.ofNat 64 0)), ("a", .stdVecVal la),
        ("b", .stdVecVal lb), ("out", .stdVecVal lo)] =
      .ok ([("j", .u64 (BitVec.ofNat 64 0)),
        ("i", .u64 (BitVec.ofNat 64 0)), ("a", .stdVecVal la),
        ("b", .stdVecVal lb), ("out", .stdVecVal lo)], .fellThrough) :=
    evalStmtFuel_let_ F _ _ _ _ _ (evalExpr_lit _ _)
  have hlet_k : evalStmtFuel F
      (.let_ "k" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      [("j", .u64 (BitVec.ofNat 64 0)),
        ("i", .u64 (BitVec.ofNat 64 0)), ("a", .stdVecVal la),
        ("b", .stdVecVal lb), ("out", .stdVecVal lo)] =
      .ok ([("k", .u64 (BitVec.ofNat 64 0)),
        ("j", .u64 (BitVec.ofNat 64 0)),
        ("i", .u64 (BitVec.ofNat 64 0)), ("a", .stdVecVal la),
        ("b", .stdVecVal lb), ("out", .stdVecVal lo)], .fellThrough) :=
    evalStmtFuel_let_ F _ _ _ _ _ (evalExpr_lit _ _)
  have henv : [("k", .u64 (BitVec.ofNat 64 0)),
        ("j", .u64 (BitVec.ofNat 64 0)),
        ("i", .u64 (BitVec.ofNat 64 0)), ("a", .stdVecVal la),
        ("b", .stdVecVal lb), ("out", .stdVecVal lo)] =
      mkMergeEnv la lb lo (BitVec.ofNat 64 0) (BitVec.ofNat 64 0)
        (BitVec.ofNat 64 0) := rfl
  match hmain : mergeMainFwd la lb lo (la.length + lb.length) 0 0 0 with
  | .error e =>
    have hM := mergeMain_err F la lb lo (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) e hlena hlenb hleno
      (by simpa [hz] using hF) (by simpa [hz] using hmain)
    have hfwd : vecMergeIntoFwd la lb lo = .error e := by
      simp [vecMergeIntoFwd, hmain]
    have hstmt : evalStmtFuel F vecMergeIntoFunc.body
        [("a", .stdVecVal la), ("b", .stdVecVal lb),
          ("out", .stdVecVal lo)] = .error e := by
      rw [hbody,
        evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_i,
        evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_j,
        evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_k, henv,
        evalStmtFuel_seq_err F _ _ _ _ hM]
    simp [evalFuncFuel, hbind, hstmt, hfwd]
  | .ok (i₁, j₁, k₁, lo₁) =>
    obtain ⟨hi₁, hj₁, hk₁, hlen₁⟩ := mergeMainFwd_le la lb _ _ _ _ _ _ _ _ _
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) hmain
    have hleno₁ : lo₁.length < 2 ^ 64 := by
      rw [hlen₁]; exact hleno
    have hk₁' : k₁ ≤ lo₁.length := by
      rw [hlen₁]; exact hk₁
    have ti₁ : (BitVec.ofNat 64 i₁).toNat = i₁ :=
      bv64_toNat_ofNat i₁ (Nat.lt_of_le_of_lt hi₁ hlena)
    have tj₁ : (BitVec.ofNat 64 j₁).toNat = j₁ :=
      bv64_toNat_ofNat j₁ (Nat.lt_of_le_of_lt hj₁ hlenb)
    have tk₁ : (BitVec.ofNat 64 k₁).toNat = k₁ :=
      bv64_toNat_ofNat k₁ (Nat.lt_of_le_of_lt hk₁' hleno₁)
    have hM := mergeMain_ok F la lb lo (BitVec.ofNat 64 0)
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) i₁ j₁ k₁ lo₁ hlena hlenb
      hleno (by simpa [hz] using hF) (by simpa [hz] using hmain)
    match hdrainA : mergeDrainAFwd la lo₁ (la.length - i₁) i₁ k₁ with
    | .error e =>
      have hdrainA' : mergeDrainAFwd la lo₁
          (la.length - (BitVec.ofNat 64 i₁).toNat)
          (BitVec.ofNat 64 i₁).toNat (BitVec.ofNat 64 k₁).toNat =
          .error e := by
        rw [ti₁, tk₁]; exact hdrainA
      have hA := mergeDrainA_err F la lb lo₁ (BitVec.ofNat 64 i₁)
        (BitVec.ofNat 64 j₁) (BitVec.ofNat 64 k₁) e hlena hleno₁
        (by rw [ti₁]; omega) hdrainA'
      have hfwd : vecMergeIntoFwd la lb lo = .error e := by
        simp [vecMergeIntoFwd, hmain, hdrainA]
      have hstmt : evalStmtFuel F vecMergeIntoFunc.body
          [("a", .stdVecVal la), ("b", .stdVecVal lb),
            ("out", .stdVecVal lo)] = .error e := by
        rw [hbody,
          evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_i,
          evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_j,
          evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_k, henv,
          evalStmtFuel_seq_fallthrough F _ _ _ _ hM,
          evalStmtFuel_seq_err F _ _ _ _ hA]
      simp [evalFuncFuel, hbind, hstmt, hfwd]
    | .ok (i₂, k₂, lo₂) =>
      obtain ⟨hi₂, hk₂, hlen₂⟩ := mergeDrainAFwd_le la _ _ _ _ _ _ _
        hi₁ hk₁' hdrainA
      have hdrainA' : mergeDrainAFwd la lo₁
          (la.length - (BitVec.ofNat 64 i₁).toNat)
          (BitVec.ofNat 64 i₁).toNat (BitVec.ofNat 64 k₁).toNat =
          .ok (i₂, k₂, lo₂) := by
        rw [ti₁, tk₁]; exact hdrainA
      have hleno₂ : lo₂.length < 2 ^ 64 := by
        rw [hlen₂, hlen₁]; exact hleno
      have hA := mergeDrainA_ok F la lb lo₁ (BitVec.ofNat 64 i₁)
        (BitVec.ofNat 64 j₁) (BitVec.ofNat 64 k₁) i₂ k₂ lo₂ hlena hleno₁
        (by rw [ti₁]; omega) hdrainA'
      have hk₂' : k₂ ≤ lo₂.length := by
        rw [hlen₂]; exact hk₂
      have tk₂ : (BitVec.ofNat 64 k₂).toNat = k₂ :=
        bv64_toNat_ofNat k₂ (Nat.lt_of_le_of_lt hk₂' hleno₂)
      match hdrainB : mergeDrainBFwd lb lo₂ (lb.length - j₁) j₁ k₂ with
      | .error e =>
        have hdrainB' : mergeDrainBFwd lb lo₂
            (lb.length - (BitVec.ofNat 64 j₁).toNat)
            (BitVec.ofNat 64 j₁).toNat (BitVec.ofNat 64 k₂).toNat =
            .error e := by
          rw [tj₁, tk₂]; exact hdrainB
        have hB := mergeDrainB_err F la lb lo₂ (BitVec.ofNat 64 i₂)
          (BitVec.ofNat 64 j₁) (BitVec.ofNat 64 k₂) e hlenb hleno₂
          (by rw [tj₁]; omega) hdrainB'
        have hfwd : vecMergeIntoFwd la lb lo = .error e := by
          simp [vecMergeIntoFwd, hmain, hdrainA, hdrainB]
        have hstmt : evalStmtFuel F vecMergeIntoFunc.body
            [("a", .stdVecVal la), ("b", .stdVecVal lb),
              ("out", .stdVecVal lo)] = .error e := by
          rw [hbody,
            evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_i,
            evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_j,
            evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_k, henv,
            evalStmtFuel_seq_fallthrough F _ _ _ _ hM,
            evalStmtFuel_seq_fallthrough F _ _ _ _ hA,
            evalStmtFuel_seq_err F _ _ _ _ hB]
        simp [evalFuncFuel, hbind, hstmt, hfwd]
      | .ok (j₃, k₃, lo₃) =>
        obtain ⟨hj₃, hk₃, hlen₃⟩ := mergeDrainBFwd_le lb _ _ _ _ _ _ _
          hj₁ hk₂' hdrainB
        have hdrainB' : mergeDrainBFwd lb lo₂
            (lb.length - (BitVec.ofNat 64 j₁).toNat)
            (BitVec.ofNat 64 j₁).toNat (BitVec.ofNat 64 k₂).toNat =
            .ok (j₃, k₃, lo₃) := by
          rw [tj₁, tk₂]; exact hdrainB
        have hleno₃ : lo₃.length < 2 ^ 64 := by
          rw [hlen₃, hlen₂, hlen₁]; exact hleno
        have hB := mergeDrainB_ok F la lb lo₂ (BitVec.ofNat 64 i₂)
          (BitVec.ofNat 64 j₁) (BitVec.ofNat 64 k₂) j₃ k₃ lo₃ hlenb
          hleno₂ (by rw [tj₁]; omega) hdrainB'
        have heout : evalExpr (.var "out")
            (mkMergeEnv la lb lo₃ (BitVec.ofNat 64 i₂)
              (BitVec.ofNat 64 j₃) (BitVec.ofNat 64 k₃)) =
            .ok (.stdVecVal lo₃) :=
          evalExpr_var_hit _ _ _ (mkMergeEnv_out _ _ _ _ _ _)
        have hret : evalStmtFuel F (.return_ (.var "out"))
            (mkMergeEnv la lb lo₃ (BitVec.ofNat 64 i₂)
              (BitVec.ofNat 64 j₃) (BitVec.ofNat 64 k₃)) =
            .ok (mkMergeEnv la lb lo₃ (BitVec.ofNat 64 i₂)
              (BitVec.ofNat 64 j₃) (BitVec.ofNat 64 k₃),
              .returned (.stdVecVal lo₃)) :=
          evalStmtFuel_return F _ _ _ heout
        have hfwd : vecMergeIntoFwd la lb lo = .ok (.stdVecVal lo₃) := by
          simp [vecMergeIntoFwd, hmain, hdrainA, hdrainB]
        have hstmt : evalStmtFuel F vecMergeIntoFunc.body
            [("a", .stdVecVal la), ("b", .stdVecVal lb),
              ("out", .stdVecVal lo)] =
            .ok (mkMergeEnv la lb lo₃ (BitVec.ofNat 64 i₂)
              (BitVec.ofNat 64 j₃) (BitVec.ofNat 64 k₃),
              .returned (.stdVecVal lo₃)) := by
          rw [hbody,
            evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_i,
            evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_j,
            evalStmtFuel_seq_fallthrough F _ _ _ _ hlet_k, henv,
            evalStmtFuel_seq_fallthrough F _ _ _ _ hM,
            evalStmtFuel_seq_fallthrough F _ _ _ _ hA,
            evalStmtFuel_seq_fallthrough F _ _ _ _ hB]
          exact hret
        simp [evalFuncFuel, hbind, hstmt, hfwd]
