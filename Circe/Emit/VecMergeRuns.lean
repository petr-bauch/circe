/-
C2b ranged merge callee over `std::vector<int>` (merge-sort kernel twin).

Corpus: `tests/cpp/vec_merge_sort.cpp` → `tests/cir/vec_merge_sort.cir`
(entry `_Z10merge_runsRKSt6vectorIiSaIiEERS1_mmm`: one `sharedBorrow`
input + one `mutBorrow` temp pre-sized by the caller + three owned
`u64` bounds `lo/mid/hi`, `void` out; three sequential `cir.while`
loops — main two-pointer loop with a short-circuit `&&`
(`cir.ternary`) guard, two drain loops; reads via const `at()`,
writes via non-const `at()`).

Model (the `vec_merge_into` proof twin): every `at()` call fuses
into its guard + pure read (`stdVecAt`) or borrowed store
(`vecSet`). The `&&` maps onto the pure ternary (`tif`). Each
`tmp.at(k)` write carries its own `if k < len` / `fail`. The only
difference from the kernel is the guard shape: bounds are `u64`
variables (`mid`/`hi`), not lengths, so guards evaluate through
`BitVec.ult_eq_decide` (var/var) rather than `ult_ofNat64_len`.
All inductions are program-level (`evalProgStmt`, `prog`
generalized — the body is call-free so `prog` is never consulted)
so the sort entry discharges its `callProg` step directly.
-/
import Circe.Emit.VecMergeInto

namespace VecMergeRuns

/-- Function name (Itanium mangling of a `merge_runs` free function
taking `const vector<int>&` + `vector<int>&` + three
`unsigned long`, returning `void`). -/
def mergeRunsName : String :=
  "_Z10merge_runsRKSt6vectorIiSaIiEERS1_mmm"

/-- Main-loop body: compare the two heads, store the smaller, advance. -/
def mergeRunsMainBody : CStmt :=
  (.if_ (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "a" (.var "j")))
    (.seq (.if_ (.ult (.var "k") (.stdVecLen "tmp"))
              (.vecSet "tmp" (.var "k") (.stdVecAt "a" (.var "i")))
              .fail)
      (.seq (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))
        (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))))
    (.seq (.if_ (.ult (.var "k") (.stdVecLen "tmp"))
              (.vecSet "tmp" (.var "k") (.stdVecAt "a" (.var "j")))
              .fail)
      (.seq (.assign "j" (.uadd (.var "j") (.lit (.u64 1))))
        (.assign "k" (.uadd (.var "k") (.lit (.u64 1)))))))

/-- Main loop `while (i < mid && j < hi) body` (short-circuit `&&` as
    the pure ternary). -/
def mergeRunsMain : CStmt :=
  (.while_ (.tif (.ult (.var "i") (.var "mid"))
              (.ult (.var "j") (.var "hi"))
              (.lit (.b false)))
    mergeRunsMainBody)

/-- Drain-`i` body: copy the head, advance. -/
def mergeRunsDrainIBody : CStmt :=
  (.seq (.if_ (.ult (.var "k") (.stdVecLen "tmp"))
            (.vecSet "tmp" (.var "k") (.stdVecAt "a" (.var "i")))
            .fail)
    (.seq (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))
      (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))))

/-- Drain-`i` loop `while (i < mid) body`. -/
def mergeRunsDrainI : CStmt :=
  (.while_ (.ult (.var "i") (.var "mid")) mergeRunsDrainIBody)

/-- Drain-`j` body: copy the head, advance. -/
def mergeRunsDrainJBody : CStmt :=
  (.seq (.if_ (.ult (.var "k") (.stdVecLen "tmp"))
            (.vecSet "tmp" (.var "k") (.stdVecAt "a" (.var "j")))
            .fail)
    (.seq (.assign "j" (.uadd (.var "j") (.lit (.u64 1))))
      (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))))

/-- Drain-`j` loop `while (j < hi) body`. -/
def mergeRunsDrainJ : CStmt :=
  (.while_ (.ult (.var "j") (.var "hi")) mergeRunsDrainJBody)

/-- Whole function: `let_`-prelude binds `i←lo`, `j←mid`, `k←lo`,
    three sequential loops, the updated `tmp` words return (`xor_n`
    out-param idiom). -/
def mergeRunsFunc : Func :=
  ⟨mergeRunsName,
   [{ name := "a", ty := stdVecObjTy, role := .sharedBorrow },
    { name := "tmp", ty := stdVecObjTy, role := .mutBorrow 0 },
    { name := "lo", ty := .u 64, role := .owned },
    { name := "mid", ty := .u 64, role := .owned },
    { name := "hi", ty := .u 64, role := .owned }],
   stdVecObjTy,
   (.seq (.let_ "i" (.u 64) (.var "lo"))
     (.seq (.let_ "j" (.u 64) (.var "mid"))
       (.seq (.let_ "k" (.u 64) (.var "lo"))
         (.seq mergeRunsMain
           (.seq mergeRunsDrainI
             (.seq mergeRunsDrainJ
               (.return_ (.var "tmp"))))))))⟩

/-- Loop environment (borrowed words + `u64` bounds and indices), in
    prelude `let_` cons order, so the entry bridge is `rfl` — the
    `mkMergeEnv` precedent. -/
def mkRunsEnv (la lt : List (BitVec 32))
    (lo mid hi i j k : BitVec 64) : Env :=
  [("k", .u64 k), ("j", .u64 j), ("i", .u64 i),
   ("a", .stdVecVal la), ("tmp", .stdVecVal lt),
   ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)]

theorem mkRunsEnv_a (la lt : List (BitVec 32))
    (lo mid hi i j k : BitVec 64) :
    envLookup (mkRunsEnv la lt lo mid hi i j k) "a" =
      some (.stdVecVal la) := by
  simp [mkRunsEnv, envLookup, show ("a" : String) ≠ "k" by decide,
    show ("a" : String) ≠ "j" by decide,
    show ("a" : String) ≠ "i" by decide]

theorem mkRunsEnv_tmp (la lt : List (BitVec 32))
    (lo mid hi i j k : BitVec 64) :
    envLookup (mkRunsEnv la lt lo mid hi i j k) "tmp" =
      some (.stdVecVal lt) := by
  simp [mkRunsEnv, envLookup, show ("tmp" : String) ≠ "k" by decide,
    show ("tmp" : String) ≠ "j" by decide,
    show ("tmp" : String) ≠ "i" by decide,
    show ("tmp" : String) ≠ "a" by decide]

theorem mkRunsEnv_lo (la lt : List (BitVec 32))
    (lo mid hi i j k : BitVec 64) :
    envLookup (mkRunsEnv la lt lo mid hi i j k) "lo" =
      some (.u64 lo) := by
  simp [mkRunsEnv, envLookup, show ("lo" : String) ≠ "k" by decide,
    show ("lo" : String) ≠ "j" by decide,
    show ("lo" : String) ≠ "i" by decide,
    show ("lo" : String) ≠ "a" by decide,
    show ("lo" : String) ≠ "tmp" by decide]

theorem mkRunsEnv_mid (la lt : List (BitVec 32))
    (lo mid hi i j k : BitVec 64) :
    envLookup (mkRunsEnv la lt lo mid hi i j k) "mid" =
      some (.u64 mid) := by
  simp [mkRunsEnv, envLookup, show ("mid" : String) ≠ "k" by decide,
    show ("mid" : String) ≠ "j" by decide,
    show ("mid" : String) ≠ "i" by decide,
    show ("mid" : String) ≠ "a" by decide,
    show ("mid" : String) ≠ "tmp" by decide,
    show ("mid" : String) ≠ "lo" by decide]

theorem mkRunsEnv_hi (la lt : List (BitVec 32))
    (lo mid hi i j k : BitVec 64) :
    envLookup (mkRunsEnv la lt lo mid hi i j k) "hi" =
      some (.u64 hi) := by
  simp [mkRunsEnv, envLookup, show ("hi" : String) ≠ "k" by decide,
    show ("hi" : String) ≠ "j" by decide,
    show ("hi" : String) ≠ "i" by decide,
    show ("hi" : String) ≠ "a" by decide,
    show ("hi" : String) ≠ "tmp" by decide,
    show ("hi" : String) ≠ "lo" by decide,
    show ("hi" : String) ≠ "mid" by decide]

theorem mkRunsEnv_i (la lt : List (BitVec 32))
    (lo mid hi i j k : BitVec 64) :
    envLookup (mkRunsEnv la lt lo mid hi i j k) "i" =
      some (.u64 i) := by
  simp [mkRunsEnv, envLookup, show ("i" : String) ≠ "k" by decide,
    show ("i" : String) ≠ "j" by decide]

theorem mkRunsEnv_j (la lt : List (BitVec 32))
    (lo mid hi i j k : BitVec 64) :
    envLookup (mkRunsEnv la lt lo mid hi i j k) "j" =
      some (.u64 j) := by
  simp [mkRunsEnv, envLookup, show ("j" : String) ≠ "k" by decide]

theorem mkRunsEnv_k (la lt : List (BitVec 32))
    (lo mid hi i j k : BitVec 64) :
    envLookup (mkRunsEnv la lt lo mid hi i j k) "k" =
      some (.u64 k) := by
  simp [mkRunsEnv, envLookup]

/-! ## Forward models (fuel-threaded, mirroring the loops) -/

/-- Main-loop model: fuel + indices + current `tmp` words + Nat
    bounds. Fuel 0 returns the words so far; short `tmp` aborts
    loudly. -/
def mergeRunsMainFwd (la : List (BitVec 32)) : List (BitVec 32) →
    Nat → Nat → Nat → Nat → Nat → Nat →
    Result (Nat × Nat × Nat × List (BitVec 32))
  | lt, 0, i, j, k, _, _ => .ok (i, j, k, lt)
  | lt, fuel + 1, i, j, k, mid, hi =>
    if _ : i < mid then
      if _ : j < hi then
        match lt[k]? with
        | none => .error .AssertFail
        | some _ =>
          match la[i]?, la[j]? with
          | some x, some y =>
            if x.slt y then
              mergeRunsMainFwd la (lt.set k x) fuel (i + 1) j (k + 1) mid hi
            else
              mergeRunsMainFwd la (lt.set k y) fuel i (j + 1) (k + 1) mid hi
          | _, _ => .error .AssertFail
      else .ok (i, j, k, lt)
    else .ok (i, j, k, lt)

/-- Drain-`i` model. -/
def mergeRunsDrainIFwd (la : List (BitVec 32)) : List (BitVec 32) →
    Nat → Nat → Nat → Nat → Result (Nat × Nat × List (BitVec 32))
  | lt, 0, i, k, _ => .ok (i, k, lt)
  | lt, fuel + 1, i, k, mid =>
    if _ : i < mid then
      match lt[k]? with
      | none => .error .AssertFail
      | some _ =>
        match la[i]? with
        | some x => mergeRunsDrainIFwd la (lt.set k x) fuel (i + 1) (k + 1) mid
        | none => .error .AssertFail
    else .ok (i, k, lt)

/-- Drain-`j` model. -/
def mergeRunsDrainJFwd (la : List (BitVec 32)) : List (BitVec 32) →
    Nat → Nat → Nat → Nat → Result (Nat × Nat × List (BitVec 32))
  | lt, 0, j, k, _ => .ok (j, k, lt)
  | lt, fuel + 1, j, k, hi =>
    if _ : j < hi then
      match lt[k]? with
      | none => .error .AssertFail
      | some _ =>
        match la[j]? with
        | some x => mergeRunsDrainJFwd la (lt.set k x) fuel (j + 1) (k + 1) hi
        | none => .error .AssertFail
    else .ok (j, k, lt)

/-- Whole-function forward: main, then drains, then the words.
    Model fuels are measure-exact (remaining iterations). -/
def mergeRunsFwd (la lt : List (BitVec 32))
    (lo mid hi : Nat) : Result Value :=
  match mergeRunsMainFwd la lt ((mid - lo) + (hi - mid)) lo mid lo mid hi with
  | .error e => .error e
  | .ok (i, j, k, lt') =>
    match mergeRunsDrainIFwd la lt' (mid - i) i k mid with
    | .error e => .error e
    | .ok (_, k', lt'') =>
      match mergeRunsDrainJFwd la lt'' (hi - j) j k' hi with
      | .error e => .error e
      | .ok (_, _, lt''') => .ok (.stdVecVal lt''')

/-! ## Guard, read, and increment lemmas -/

/-- Var/var `ult` bridge (bounds are variables, not lengths). -/
theorem bv64_ult_toNat (x y : BitVec 64) :
    x.ult y = decide (x.toNat < y.toNat) :=
  BitVec.ult_eq_decide

theorem runsGuardI_eval (la lt : List (BitVec 32))
    (lo mid hi i j k : BitVec 64) :
    evalExpr (.ult (.var "i") (.var "mid"))
      (mkRunsEnv la lt lo mid hi i j k) =
      .ok (.b (decide (i.toNat < mid.toNat))) := by
  have hIv := mkRunsEnv_i la lt lo mid hi i j k
  have hmid := mkRunsEnv_mid la lt lo mid hi i j k
  have hnv : evalExpr (.var "i") (mkRunsEnv la lt lo mid hi i j k) =
      .ok (.u64 i) :=
    evalExpr_var_hit _ _ _ hIv
  have hmv : evalExpr (.var "mid") (mkRunsEnv la lt lo mid hi i j k) =
      .ok (.u64 mid) :=
    evalExpr_var_hit _ _ _ hmid
  have hult := evalExpr_ult_u64 _ _ _ _ _ hnv hmv
  rw [bv64_ult_toNat i mid] at hult
  exact hult

theorem runsGuardJ_eval (la lt : List (BitVec 32))
    (lo mid hi i j k : BitVec 64) :
    evalExpr (.ult (.var "j") (.var "hi"))
      (mkRunsEnv la lt lo mid hi i j k) =
      .ok (.b (decide (j.toNat < hi.toNat))) := by
  have hj := mkRunsEnv_j la lt lo mid hi i j k
  have hhi := mkRunsEnv_hi la lt lo mid hi i j k
  have hnv : evalExpr (.var "j") (mkRunsEnv la lt lo mid hi i j k) =
      .ok (.u64 j) :=
    evalExpr_var_hit _ _ _ hj
  have hmv : evalExpr (.var "hi") (mkRunsEnv la lt lo mid hi i j k) =
      .ok (.u64 hi) :=
    evalExpr_var_hit _ _ _ hhi
  have hult := evalExpr_ult_u64 _ _ _ _ _ hnv hmv
  rw [bv64_ult_toNat j hi] at hult
  exact hult

theorem runsGuardK_eval (la lt : List (BitVec 32))
    (lo mid hi i j k : BitVec 64) (hlent : lt.length < 2 ^ 64) :
    evalExpr (.ult (.var "k") (.stdVecLen "tmp"))
      (mkRunsEnv la lt lo mid hi i j k) =
      .ok (.b (decide (k.toNat < lt.length))) := by
  have ht := mkRunsEnv_tmp la lt lo mid hi i j k
  have hk := mkRunsEnv_k la lt lo mid hi i j k
  have hsize : evalExpr (.stdVecLen "tmp")
      (mkRunsEnv la lt lo mid hi i j k) =
      .ok (.u64 (BitVec.ofNat 64 lt.length)) :=
    evalExpr_stdVecLen_some "tmp" _ lt ht
  have hnv : evalExpr (.var "k") (mkRunsEnv la lt lo mid hi i j k) =
      .ok (.u64 k) :=
    evalExpr_var_hit _ _ _ hk
  have hult := evalExpr_ult_u64 _ _ _ _ _ hnv hsize
  rw [ult_ofNat64_len k lt.length hlent] at hult
  exact hult

/-- The main-loop `&&` guard holds iff both indices are live. -/
theorem runsMainGuard_true (la lt : List (BitVec 32))
    (lo mid hi i j k : BitVec 64)
    (hI : i.toNat < mid.toNat) (hJ : j.toNat < hi.toNat) :
    evalExpr (.tif (.ult (.var "i") (.var "mid"))
                (.ult (.var "j") (.var "hi"))
                (.lit (.b false)))
      (mkRunsEnv la lt lo mid hi i j k) = .ok (.b true) := by
  have hI' : evalExpr (.ult (.var "i") (.var "mid"))
      (mkRunsEnv la lt lo mid hi i j k) = .ok (.b true) := by
    have h := runsGuardI_eval la lt lo mid hi i j k
    rwa [decide_eq_true hI] at h
  have hJ' : evalExpr (.ult (.var "j") (.var "hi"))
      (mkRunsEnv la lt lo mid hi i j k) = .ok (.b true) := by
    have h := runsGuardJ_eval la lt lo mid hi i j k
    rwa [decide_eq_true hJ] at h
  rw [evalExpr_tif_true _ _ _ _ hI']
  exact hJ'

/-- The main-loop guard fails iff some index is spent. -/
theorem runsMainGuard_false (la lt : List (BitVec 32))
    (lo mid hi i j k : BitVec 64)
    (h : ¬ (i.toNat < mid.toNat ∧ j.toNat < hi.toNat)) :
    evalExpr (.tif (.ult (.var "i") (.var "mid"))
                (.ult (.var "j") (.var "hi"))
                (.lit (.b false)))
      (mkRunsEnv la lt lo mid hi i j k) = .ok (.b false) := by
  by_cases hI : i.toNat < mid.toNat
  · have hnJ : ¬ j.toNat < hi.toNat := fun hj => h ⟨hI, hj⟩
    have hI' : evalExpr (.ult (.var "i") (.var "mid"))
        (mkRunsEnv la lt lo mid hi i j k) = .ok (.b true) := by
      have h := runsGuardI_eval la lt lo mid hi i j k
      rwa [decide_eq_true hI] at h
    have hJ' : evalExpr (.ult (.var "j") (.var "hi"))
        (mkRunsEnv la lt lo mid hi i j k) = .ok (.b false) := by
      have h := runsGuardJ_eval la lt lo mid hi i j k
      rwa [decide_eq_false hnJ] at h
    rw [evalExpr_tif_true _ _ _ _ hI']
    exact hJ'
  · have hI' : evalExpr (.ult (.var "i") (.var "mid"))
        (mkRunsEnv la lt lo mid hi i j k) = .ok (.b false) := by
      have h := runsGuardI_eval la lt lo mid hi i j k
      rwa [decide_eq_false hI] at h
    have hlit : evalExpr (.lit (.b false))
        (mkRunsEnv la lt lo mid hi i j k) = .ok (.b false) := by
      simp [evalExpr, litVal]
    rw [evalExpr_tif_false _ _ _ _ hI']
    exact hlit

theorem runsReadI_hit (la lt : List (BitVec 32))
    (lo mid hi i j k : BitVec 64) (x : BitVec 32)
    (hget : la[i.toNat]? = some x) :
    evalExpr (.stdVecAt "a" (.var "i"))
      (mkRunsEnv la lt lo mid hi i j k) = .ok (.i32 x) :=
  evalExpr_stdVecAt_some "a" _ _ _ _ _
    (mkRunsEnv_a la lt lo mid hi i j k)
    (evalExpr_var_hit _ _ _ (mkRunsEnv_i la lt lo mid hi i j k)) hget

theorem runsReadJ_hit (la lt : List (BitVec 32))
    (lo mid hi i j k : BitVec 64) (y : BitVec 32)
    (hget : la[j.toNat]? = some y) :
    evalExpr (.stdVecAt "a" (.var "j"))
      (mkRunsEnv la lt lo mid hi i j k) = .ok (.i32 y) :=
  evalExpr_stdVecAt_some "a" _ _ _ _ _
    (mkRunsEnv_a la lt lo mid hi i j k)
    (evalExpr_var_hit _ _ _ (mkRunsEnv_j la lt lo mid hi i j k)) hget

/-- Index increments (any program, any fuel — leaves delegate to the
    call-free evaluator). -/
theorem runsIncrI (prog : Prog) (F : Nat) (la lt : List (BitVec 32))
    (lo mid hi i j k : BitVec 64) :
    evalProgStmt prog F
      (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))
      (mkRunsEnv la lt lo mid hi i j k) =
      .ok (mkRunsEnv la lt lo mid hi (i + 1) j k, .fellThrough) := by
  have hIv : evalExpr (.uadd (.var "i") (.lit (.u64 1)))
      (mkRunsEnv la lt lo mid hi i j k) = .ok (.u64 (i + 1)) := by
    have h1 : evalExpr (.lit (.u64 1))
        (mkRunsEnv la lt lo mid hi i j k) = .ok (.u64 1) := by
      simp [evalExpr, litVal]
    exact evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ (mkRunsEnv_i la lt lo mid hi i j k)) h1
  have hu : envUpdate (mkRunsEnv la lt lo mid hi i j k) "i"
      (.u64 (i + 1)) =
      some (mkRunsEnv la lt lo mid hi (i + 1) j k) := rfl
  have hstmt := evalStmtFuel_assign F _ _ _ _ _ hIv hu
  simpa [evalProgStmt] using hstmt

theorem runsIncrJ (prog : Prog) (F : Nat) (la lt : List (BitVec 32))
    (lo mid hi i j k : BitVec 64) :
    evalProgStmt prog F
      (.assign "j" (.uadd (.var "j") (.lit (.u64 1))))
      (mkRunsEnv la lt lo mid hi i j k) =
      .ok (mkRunsEnv la lt lo mid hi i (j + 1) k, .fellThrough) := by
  have hj : evalExpr (.uadd (.var "j") (.lit (.u64 1)))
      (mkRunsEnv la lt lo mid hi i j k) = .ok (.u64 (j + 1)) := by
    have h1 : evalExpr (.lit (.u64 1))
        (mkRunsEnv la lt lo mid hi i j k) = .ok (.u64 1) := by
      simp [evalExpr, litVal]
    exact evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ (mkRunsEnv_j la lt lo mid hi i j k)) h1
  have hu : envUpdate (mkRunsEnv la lt lo mid hi i j k) "j"
      (.u64 (j + 1)) =
      some (mkRunsEnv la lt lo mid hi i (j + 1) k) := rfl
  have hstmt := evalStmtFuel_assign F _ _ _ _ _ hj hu
  simpa [evalProgStmt] using hstmt

theorem runsIncrK (prog : Prog) (F : Nat) (la lt : List (BitVec 32))
    (lo mid hi i j k : BitVec 64) :
    evalProgStmt prog F
      (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))
      (mkRunsEnv la lt lo mid hi i j k) =
      .ok (mkRunsEnv la lt lo mid hi i j (k + 1), .fellThrough) := by
  have hk : evalExpr (.uadd (.var "k") (.lit (.u64 1)))
      (mkRunsEnv la lt lo mid hi i j k) = .ok (.u64 (k + 1)) := by
    have h1 : evalExpr (.lit (.u64 1))
        (mkRunsEnv la lt lo mid hi i j k) = .ok (.u64 1) := by
      simp [evalExpr, litVal]
    exact evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ _ _ (mkRunsEnv_k la lt lo mid hi i j k)) h1
  have hu : envUpdate (mkRunsEnv la lt lo mid hi i j k) "k"
      (.u64 (k + 1)) =
      some (mkRunsEnv la lt lo mid hi i j (k + 1)) := rfl
  have hstmt := evalStmtFuel_assign F _ _ _ _ _ hk hu
  simpa [evalProgStmt] using hstmt

/-! ## Body steps (loop-free) -/

/-- Program-level `fail` (noreturn-throw fusion, any program). -/
theorem evalProgStmt_fail (prog : Prog) (F : Nat) (ρ : Env) :
    evalProgStmt prog F .fail ρ = .error .AssertFail := by
  simpa [evalProgStmt] using (evalStmtFuel_fail F ρ)

/-- Program-level borrowed store (leaves delegate). -/
theorem evalProgStmt_vecSet (prog : Prog) (F : Nat) (x : String)
    (ie ve : CExpr) (ρ : Env) (i : BitVec 64) (xv : BitVec 32)
    (l : List (BitVec 32)) (w : BitVec 32) (ρ' : Env)
    (hi : evalExpr ie ρ = .ok (.u64 i))
    (hv : evalExpr ve ρ = .ok (.i32 xv))
    (hvec : envLookup ρ x = some (.stdVecVal l))
    (hget : l[i.toNat]? = some w)
    (hu : envUpdate ρ x (.stdVecVal (l.set i.toNat xv)) = some ρ') :
    evalProgStmt prog F (.vecSet x ie ve) ρ =
      .ok (ρ', .fellThrough) := by
  simpa [evalProgStmt] using
    (evalStmtFuel_vecSet F x ie ve ρ i xv l w ρ' hi hv hvec hget hu)

/-- Main body, take-`i` hit: heads compare, `k` live, store + advance. -/
theorem mergeRunsMainBody_hitI (prog : Prog) (F : Nat)
    (la lt : List (BitVec 32)) (lo mid hi i j k : BitVec 64)
    (x y w : BitVec 32)
    (hlent : lt.length < 2 ^ 64)
    (hgetI : la[i.toNat]? = some x) (hgetJ : la[j.toNat]? = some y)
    (hltXY : (x.slt y) = true)
    (hltK : k.toNat < lt.length)
    (hgetK : lt[k.toNat]? = some w) :
    evalProgStmt prog F mergeRunsMainBody
        (mkRunsEnv la lt lo mid hi i j k) =
      .ok (mkRunsEnv la (lt.set k.toNat x) lo mid hi (i + 1) j (k + 1),
        .fellThrough) := by
  have hbody : mergeRunsMainBody =
      (.if_ (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "a" (.var "j")))
        (.seq (.if_ (.ult (.var "k") (.stdVecLen "tmp"))
                  (.vecSet "tmp" (.var "k")
                    (.stdVecAt "a" (.var "i")))
                  .fail)
          (.seq (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))
            (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))))
        (.seq (.if_ (.ult (.var "k") (.stdVecLen "tmp"))
                  (.vecSet "tmp" (.var "k")
                    (.stdVecAt "a" (.var "j")))
                  .fail)
          (.seq (.assign "j" (.uadd (.var "j") (.lit (.u64 1))))
            (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))))) := rfl
  have hrI := runsReadI_hit la lt lo mid hi i j k x hgetI
  have hrJ := runsReadJ_hit la lt lo mid hi i j k y hgetJ
  have hslt : evalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "a" (.var "j")))
      (mkRunsEnv la lt lo mid hi i j k) = .ok (.b true) := by
    have h := evalExpr_slt_i32 _ _ _ _ _ hrI hrJ
    rwa [hltXY] at h
  have hcK : evalExpr (.ult (.var "k") (.stdVecLen "tmp"))
      (mkRunsEnv la lt lo mid hi i j k) = .ok (.b true) := by
    have h := runsGuardK_eval la lt lo mid hi i j k hlent
    rwa [decide_eq_true hltK] at h
  have hvec := evalProgStmt_vecSet prog F "tmp" (.var "k")
    (.stdVecAt "a" (.var "i")) (mkRunsEnv la lt lo mid hi i j k)
    k x lt w _ (evalExpr_var_hit _ _ _ (mkRunsEnv_k la lt lo mid hi i j k))
    hrI (mkRunsEnv_tmp la lt lo mid hi i j k) hgetK rfl
  have hincrI := runsIncrI prog F la (lt.set k.toNat x) lo mid hi i j k
  have hincrK := runsIncrK prog F la (lt.set k.toNat x) lo mid hi (i + 1) j k
  have hinner :=
    (evalProgStmt_seq_fallthrough prog F _ _ _ _ hincrI).trans hincrK
  have hwrite := ((evalProgStmt_if_true prog F _ _ .fail _ hcK).trans hvec)
  have hseq :=
    (evalProgStmt_seq_fallthrough prog F _ _ _ _ hwrite).trans hinner
  rw [hbody]
  exact (evalProgStmt_if_true prog F _ _ _ _ hslt).trans hseq

/-- Main body, take-`j` hit. -/
theorem mergeRunsMainBody_hitJ (prog : Prog) (F : Nat)
    (la lt : List (BitVec 32)) (lo mid hi i j k : BitVec 64)
    (x y w : BitVec 32)
    (hlent : lt.length < 2 ^ 64)
    (hgetI : la[i.toNat]? = some x) (hgetJ : la[j.toNat]? = some y)
    (hltXY : (x.slt y) = false)
    (hltK : k.toNat < lt.length)
    (hgetK : lt[k.toNat]? = some w) :
    evalProgStmt prog F mergeRunsMainBody
        (mkRunsEnv la lt lo mid hi i j k) =
      .ok (mkRunsEnv la (lt.set k.toNat y) lo mid hi i (j + 1) (k + 1),
        .fellThrough) := by
  have hbody : mergeRunsMainBody =
      (.if_ (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "a" (.var "j")))
        (.seq (.if_ (.ult (.var "k") (.stdVecLen "tmp"))
                  (.vecSet "tmp" (.var "k")
                    (.stdVecAt "a" (.var "i")))
                  .fail)
          (.seq (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))
            (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))))
        (.seq (.if_ (.ult (.var "k") (.stdVecLen "tmp"))
                  (.vecSet "tmp" (.var "k")
                    (.stdVecAt "a" (.var "j")))
                  .fail)
          (.seq (.assign "j" (.uadd (.var "j") (.lit (.u64 1))))
            (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))))) := rfl
  have hrI := runsReadI_hit la lt lo mid hi i j k x hgetI
  have hrJ := runsReadJ_hit la lt lo mid hi i j k y hgetJ
  have hslt : evalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "a" (.var "j")))
      (mkRunsEnv la lt lo mid hi i j k) = .ok (.b false) := by
    have h := evalExpr_slt_i32 _ _ _ _ _ hrI hrJ
    rwa [hltXY] at h
  have hcK : evalExpr (.ult (.var "k") (.stdVecLen "tmp"))
      (mkRunsEnv la lt lo mid hi i j k) = .ok (.b true) := by
    have h := runsGuardK_eval la lt lo mid hi i j k hlent
    rwa [decide_eq_true hltK] at h
  have hvec := evalProgStmt_vecSet prog F "tmp" (.var "k")
    (.stdVecAt "a" (.var "j")) (mkRunsEnv la lt lo mid hi i j k)
    k y lt w _ (evalExpr_var_hit _ _ _ (mkRunsEnv_k la lt lo mid hi i j k))
    hrJ (mkRunsEnv_tmp la lt lo mid hi i j k) hgetK rfl
  have hincrJ := runsIncrJ prog F la (lt.set k.toNat y) lo mid hi i j k
  have hincrK := runsIncrK prog F la (lt.set k.toNat y) lo mid hi i (j + 1) k
  have hinner :=
    (evalProgStmt_seq_fallthrough prog F _ _ _ _ hincrJ).trans hincrK
  have hwrite := ((evalProgStmt_if_true prog F _ _ .fail _ hcK).trans hvec)
  have hseq :=
    (evalProgStmt_seq_fallthrough prog F _ _ _ _ hwrite).trans hinner
  rw [hbody]
  exact (evalProgStmt_if_false prog F _ _ _ _ hslt).trans hseq

/-- Main body, short-`tmp` miss (take-`i` side): loud abort. -/
theorem mergeRunsMainBody_missI (prog : Prog) (F : Nat)
    (la lt : List (BitVec 32)) (lo mid hi i j k : BitVec 64)
    (x y : BitVec 32)
    (hlent : lt.length < 2 ^ 64)
    (hgetI : la[i.toNat]? = some x) (hgetJ : la[j.toNat]? = some y)
    (hltXY : (x.slt y) = true)
    (hltK : ¬ k.toNat < lt.length) :
    evalProgStmt prog F mergeRunsMainBody
      (mkRunsEnv la lt lo mid hi i j k) = .error .AssertFail := by
  have hbody : mergeRunsMainBody =
      (.if_ (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "a" (.var "j")))
        (.seq (.if_ (.ult (.var "k") (.stdVecLen "tmp"))
                  (.vecSet "tmp" (.var "k")
                    (.stdVecAt "a" (.var "i")))
                  .fail)
          (.seq (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))
            (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))))
        (.seq (.if_ (.ult (.var "k") (.stdVecLen "tmp"))
                  (.vecSet "tmp" (.var "k")
                    (.stdVecAt "a" (.var "j")))
                  .fail)
          (.seq (.assign "j" (.uadd (.var "j") (.lit (.u64 1))))
            (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))))) := rfl
  have hrI := runsReadI_hit la lt lo mid hi i j k x hgetI
  have hrJ := runsReadJ_hit la lt lo mid hi i j k y hgetJ
  have hslt : evalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "a" (.var "j")))
      (mkRunsEnv la lt lo mid hi i j k) = .ok (.b true) := by
    have h := evalExpr_slt_i32 _ _ _ _ _ hrI hrJ
    rwa [hltXY] at h
  have hcK : evalExpr (.ult (.var "k") (.stdVecLen "tmp"))
      (mkRunsEnv la lt lo mid hi i j k) = .ok (.b false) := by
    have h := runsGuardK_eval la lt lo mid hi i j k hlent
    rwa [decide_eq_false hltK] at h
  have hfail := (evalProgStmt_if_false prog F _
      (.vecSet "tmp" (.var "k") (.stdVecAt "a" (.var "i"))) _ _ hcK).trans
    (evalProgStmt_fail prog F _)
  have hseq := evalProgStmt_seq_err prog F _
      (.seq (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))
        (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))) _ _ hfail
  rw [hbody]
  exact (evalProgStmt_if_true prog F _ _ _ _ hslt).trans hseq

/-- Main body, short-`tmp` miss (take-`j` side): loud abort. -/
theorem mergeRunsMainBody_missJ (prog : Prog) (F : Nat)
    (la lt : List (BitVec 32)) (lo mid hi i j k : BitVec 64)
    (x y : BitVec 32)
    (hlent : lt.length < 2 ^ 64)
    (hgetI : la[i.toNat]? = some x) (hgetJ : la[j.toNat]? = some y)
    (hltXY : (x.slt y) = false)
    (hltK : ¬ k.toNat < lt.length) :
    evalProgStmt prog F mergeRunsMainBody
      (mkRunsEnv la lt lo mid hi i j k) = .error .AssertFail := by
  have hbody : mergeRunsMainBody =
      (.if_ (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "a" (.var "j")))
        (.seq (.if_ (.ult (.var "k") (.stdVecLen "tmp"))
                  (.vecSet "tmp" (.var "k")
                    (.stdVecAt "a" (.var "i")))
                  .fail)
          (.seq (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))
            (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))))
        (.seq (.if_ (.ult (.var "k") (.stdVecLen "tmp"))
                  (.vecSet "tmp" (.var "k")
                    (.stdVecAt "a" (.var "j")))
                  .fail)
          (.seq (.assign "j" (.uadd (.var "j") (.lit (.u64 1))))
            (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))))) := rfl
  have hrI := runsReadI_hit la lt lo mid hi i j k x hgetI
  have hrJ := runsReadJ_hit la lt lo mid hi i j k y hgetJ
  have hslt : evalExpr
      (.slt (.stdVecAt "a" (.var "i")) (.stdVecAt "a" (.var "j")))
      (mkRunsEnv la lt lo mid hi i j k) = .ok (.b false) := by
    have h := evalExpr_slt_i32 _ _ _ _ _ hrI hrJ
    rwa [hltXY] at h
  have hcK : evalExpr (.ult (.var "k") (.stdVecLen "tmp"))
      (mkRunsEnv la lt lo mid hi i j k) = .ok (.b false) := by
    have h := runsGuardK_eval la lt lo mid hi i j k hlent
    rwa [decide_eq_false hltK] at h
  have hfail := (evalProgStmt_if_false prog F _
      (.vecSet "tmp" (.var "k") (.stdVecAt "a" (.var "j"))) _ _ hcK).trans
    (evalProgStmt_fail prog F _)
  have hseq := evalProgStmt_seq_err prog F _
      (.seq (.assign "j" (.uadd (.var "j") (.lit (.u64 1))))
        (.assign "k" (.uadd (.var "k") (.lit (.u64 1))))) _ _ hfail
  rw [hbody]
  exact (evalProgStmt_if_false prog F _ _ _ _ hslt).trans hseq

/-- Drain-`i` body hit: `k` live, store + advance. -/
theorem mergeRunsDrainIBody_hit (prog : Prog) (F : Nat)
    (la lt : List (BitVec 32)) (lo mid hi i j k : BitVec 64)
    (x w : BitVec 32)
    (hlent : lt.length < 2 ^ 64)
    (hgetI : la[i.toNat]? = some x)
    (hltK : k.toNat < lt.length)
    (hgetK : lt[k.toNat]? = some w) :
    evalProgStmt prog F mergeRunsDrainIBody
        (mkRunsEnv la lt lo mid hi i j k) =
      .ok (mkRunsEnv la (lt.set k.toNat x) lo mid hi (i + 1) j (k + 1),
        .fellThrough) := by
  have hbody : mergeRunsDrainIBody =
      (.seq (.if_ (.ult (.var "k") (.stdVecLen "tmp"))
                (.vecSet "tmp" (.var "k") (.stdVecAt "a" (.var "i")))
                .fail)
        (.seq (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))
          (.assign "k" (.uadd (.var "k") (.lit (.u64 1)))))) := rfl
  have hrI := runsReadI_hit la lt lo mid hi i j k x hgetI
  have hcK : evalExpr (.ult (.var "k") (.stdVecLen "tmp"))
      (mkRunsEnv la lt lo mid hi i j k) = .ok (.b true) := by
    have h := runsGuardK_eval la lt lo mid hi i j k hlent
    rwa [decide_eq_true hltK] at h
  have hvec := evalProgStmt_vecSet prog F "tmp" (.var "k")
    (.stdVecAt "a" (.var "i")) (mkRunsEnv la lt lo mid hi i j k)
    k x lt w _ (evalExpr_var_hit _ _ _ (mkRunsEnv_k la lt lo mid hi i j k))
    hrI (mkRunsEnv_tmp la lt lo mid hi i j k) hgetK rfl
  have hincrI := runsIncrI prog F la (lt.set k.toNat x) lo mid hi i j k
  have hincrK := runsIncrK prog F la (lt.set k.toNat x) lo mid hi (i + 1) j k
  have hinner :=
    (evalProgStmt_seq_fallthrough prog F _ _ _ _ hincrI).trans hincrK
  have hwrite := ((evalProgStmt_if_true prog F _ _ .fail _ hcK).trans hvec)
  rw [hbody]
  exact (evalProgStmt_seq_fallthrough prog F _ _ _ _ hwrite).trans hinner

/-- Drain-`i` body miss: loud abort. -/
theorem mergeRunsDrainIBody_miss (prog : Prog) (F : Nat)
    (la lt : List (BitVec 32)) (lo mid hi i j k : BitVec 64)
    (hlent : lt.length < 2 ^ 64)
    (hltK : ¬ k.toNat < lt.length) :
    evalProgStmt prog F mergeRunsDrainIBody
      (mkRunsEnv la lt lo mid hi i j k) = .error .AssertFail := by
  have hbody : mergeRunsDrainIBody =
      (.seq (.if_ (.ult (.var "k") (.stdVecLen "tmp"))
                (.vecSet "tmp" (.var "k") (.stdVecAt "a" (.var "i")))
                .fail)
        (.seq (.assign "i" (.uadd (.var "i") (.lit (.u64 1))))
          (.assign "k" (.uadd (.var "k") (.lit (.u64 1)))))) := rfl
  have hcK : evalExpr (.ult (.var "k") (.stdVecLen "tmp"))
      (mkRunsEnv la lt lo mid hi i j k) = .ok (.b false) := by
    have h := runsGuardK_eval la lt lo mid hi i j k hlent
    rwa [decide_eq_false hltK] at h
  have hfail := (evalProgStmt_if_false prog F _
      (.vecSet "tmp" (.var "k") (.stdVecAt "a" (.var "i"))) _ _ hcK).trans
    (evalProgStmt_fail prog F _)
  rw [hbody]
  exact evalProgStmt_seq_err prog F _ _ _ _ hfail

/-- Drain-`j` body hit: `k` live, store + advance. -/
theorem mergeRunsDrainJBody_hit (prog : Prog) (F : Nat)
    (la lt : List (BitVec 32)) (lo mid hi i j k : BitVec 64)
    (y w : BitVec 32)
    (hlent : lt.length < 2 ^ 64)
    (hgetJ : la[j.toNat]? = some y)
    (hltK : k.toNat < lt.length)
    (hgetK : lt[k.toNat]? = some w) :
    evalProgStmt prog F mergeRunsDrainJBody
        (mkRunsEnv la lt lo mid hi i j k) =
      .ok (mkRunsEnv la (lt.set k.toNat y) lo mid hi i (j + 1) (k + 1),
        .fellThrough) := by
  have hbody : mergeRunsDrainJBody =
      (.seq (.if_ (.ult (.var "k") (.stdVecLen "tmp"))
                (.vecSet "tmp" (.var "k") (.stdVecAt "a" (.var "j")))
                .fail)
        (.seq (.assign "j" (.uadd (.var "j") (.lit (.u64 1))))
          (.assign "k" (.uadd (.var "k") (.lit (.u64 1)))))) := rfl
  have hrJ := runsReadJ_hit la lt lo mid hi i j k y hgetJ
  have hcK : evalExpr (.ult (.var "k") (.stdVecLen "tmp"))
      (mkRunsEnv la lt lo mid hi i j k) = .ok (.b true) := by
    have h := runsGuardK_eval la lt lo mid hi i j k hlent
    rwa [decide_eq_true hltK] at h
  have hvec := evalProgStmt_vecSet prog F "tmp" (.var "k")
    (.stdVecAt "a" (.var "j")) (mkRunsEnv la lt lo mid hi i j k)
    k y lt w _ (evalExpr_var_hit _ _ _ (mkRunsEnv_k la lt lo mid hi i j k))
    hrJ (mkRunsEnv_tmp la lt lo mid hi i j k) hgetK rfl
  have hincrJ := runsIncrJ prog F la (lt.set k.toNat y) lo mid hi i j k
  have hincrK := runsIncrK prog F la (lt.set k.toNat y) lo mid hi i (j + 1) k
  have hinner :=
    (evalProgStmt_seq_fallthrough prog F _ _ _ _ hincrJ).trans hincrK
  have hwrite := ((evalProgStmt_if_true prog F _ _ .fail _ hcK).trans hvec)
  rw [hbody]
  exact (evalProgStmt_seq_fallthrough prog F _ _ _ _ hwrite).trans hinner

/-- Drain-`j` body miss: loud abort. -/
theorem mergeRunsDrainJBody_miss (prog : Prog) (F : Nat)
    (la lt : List (BitVec 32)) (lo mid hi i j k : BitVec 64)
    (hlent : lt.length < 2 ^ 64)
    (hltK : ¬ k.toNat < lt.length) :
    evalProgStmt prog F mergeRunsDrainJBody
      (mkRunsEnv la lt lo mid hi i j k) = .error .AssertFail := by
  have hbody : mergeRunsDrainJBody =
      (.seq (.if_ (.ult (.var "k") (.stdVecLen "tmp"))
                (.vecSet "tmp" (.var "k") (.stdVecAt "a" (.var "j")))
                .fail)
        (.seq (.assign "j" (.uadd (.var "j") (.lit (.u64 1))))
          (.assign "k" (.uadd (.var "k") (.lit (.u64 1)))))) := rfl
  have hcK : evalExpr (.ult (.var "k") (.stdVecLen "tmp"))
      (mkRunsEnv la lt lo mid hi i j k) = .ok (.b false) := by
    have h := runsGuardK_eval la lt lo mid hi i j k hlent
    rwa [decide_eq_false hltK] at h
  have hfail := (evalProgStmt_if_false prog F _
      (.vecSet "tmp" (.var "k") (.stdVecAt "a" (.var "j"))) _ _ hcK).trans
    (evalProgStmt_fail prog F _)
  rw [hbody]
  exact evalProgStmt_seq_err prog F _ _ _ _ hfail

/-! ## Loop inductions (fuel-generalized, model-driven) -/

/-- Main-loop ok soundness: the model outcome ⟹ evaluation agrees. -/
theorem mergeRunsMain_ok (prog : Prog) (F : Nat)
    (la lt : List (BitVec 32)) (lo mid hi i j k : BitVec 64)
    (i' j' k' : Nat) (lt' : List (BitVec 32))
    (hlent : lt.length < 2 ^ 64)
    (hmid_le : mid.toNat ≤ la.length) (hhi_le : hi.toNat ≤ la.length)
    (hF : (mid.toNat - i.toNat) + (hi.toNat - j.toNat) + 1 ≤ F)
    (hfwd : mergeRunsMainFwd la lt
      ((mid.toNat - i.toNat) + (hi.toNat - j.toNat))
      i.toNat j.toNat k.toNat mid.toNat hi.toNat =
      .ok (i', j', k', lt')) :
    evalProgStmt prog F mergeRunsMain
        (mkRunsEnv la lt lo mid hi i j k) =
      .ok (mkRunsEnv la lt' lo mid hi (BitVec.ofNat 64 i')
        (BitVec.ofNat 64 j') (BitVec.ofNat 64 k'), .fellThrough) := by
  induction F generalizing la lt lo mid hi i j k i' j' k' lt' with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hguard : (i.toNat < mid.toNat ∧ j.toNat < hi.toNat)
    · obtain ⟨hI, hJ⟩ := hguard
      have hcond : evalExpr
          (.tif (.ult (.var "i") (.var "mid"))
            (.ult (.var "j") (.var "hi"))
            (.lit (.b false)))
          (mkRunsEnv la lt lo mid hi i j k) = .ok (.b true) :=
        runsMainGuard_true la lt lo mid hi i j k hI hJ
      have hM : (mid.toNat - i.toNat) + (hi.toNat - j.toNat) =
          ((mid.toNat - i.toNat) + (hi.toNat - j.toNat) - 1) + 1 := by
        omega
      rw [hM] at hfwd
      have hgetI : la[i.toNat]? = some la[i.toNat] :=
        List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hI hmid_le)
      have hgetJ : la[j.toNat]? = some la[j.toNat] :=
        List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hJ hhi_le)
      cases hgetK : lt[k.toNat]? with
      | none =>
        have hcontra : mergeRunsMainFwd la lt
            (((mid.toNat - i.toNat) + (hi.toNat - j.toNat) - 1) + 1)
            i.toNat j.toNat k.toNat mid.toNat hi.toNat =
            .error .AssertFail := by
          simp only [mergeRunsMainFwd, dite_eq_left hI, dite_eq_left hJ,
            hgetK]
        rw [hcontra] at hfwd
        cases hfwd
      | some w =>
        have hltK : k.toNat < lt.length :=
          list_lt_of_getElem?_some lt k.toNat w hgetK
        by_cases hslt : (la[i.toNat].slt la[j.toNat]) = true
        · have hfwdI : mergeRunsMainFwd la (lt.set k.toNat la[i.toNat])
              ((mid.toNat - i.toNat) + (hi.toNat - j.toNat) - 1)
              (i.toNat + 1) j.toNat (k.toNat + 1) mid.toNat hi.toNat =
              .ok (i', j', k', lt') := by
            have h := hfwd
            simp only [mergeRunsMainFwd, dite_eq_left hI, dite_eq_left hJ,
              hgetK, hgetI, hgetJ, hslt] at h
            exact h
          have hstep : evalProgStmt prog F mergeRunsMainBody
              (mkRunsEnv la lt lo mid hi i j k) =
              .ok (mkRunsEnv la (lt.set k.toNat la[i.toNat]) lo mid hi
                (i + 1) j (k + 1), .fellThrough) :=
            mergeRunsMainBody_hitI prog F la lt lo mid hi i j k _ _ _
              hlent hgetI hgetJ hslt hltK hgetK
          have hloop : evalProgStmt prog (F + 1) mergeRunsMain
              (mkRunsEnv la lt lo mid hi i j k) =
              evalProgStmt prog F mergeRunsMain
                (mkRunsEnv la (lt.set k.toNat la[i.toNat]) lo mid hi
                  (i + 1) j (k + 1)) := by
            cir_unfold_prog (mergeRunsMain, prog, F, hcond, hstep)
          have h1i : (i + 1).toNat = i.toNat + 1 :=
            bv64_succ_toNat i _ hI (by omega)
          have h1k : (k + 1).toNat = k.toNat + 1 :=
            bv64_succ_toNat k _ hltK hlent
          have hlent' : (lt.set k.toNat la[i.toNat]).length < 2 ^ 64 := by
            rw [List.length_set]
            exact hlent
          have hF' : (mid.toNat - (i + 1).toNat) +
              (hi.toNat - j.toNat) + 1 ≤ F := by omega
          have hfwd' : mergeRunsMainFwd la (lt.set k.toNat la[i.toNat])
              ((mid.toNat - (i + 1).toNat) + (hi.toNat - j.toNat))
              ((i + 1).toNat) j.toNat ((k + 1).toNat)
              mid.toNat hi.toNat =
              .ok (i', j', k', lt') := by
            have hM' : (mid.toNat - i.toNat) + (hi.toNat - j.toNat) - 1 =
                (mid.toNat - (i + 1).toNat) + (hi.toNat - j.toNat) := by
              omega
            rw [← h1i, ← h1k, hM'] at hfwdI
            exact hfwdI
          rw [hloop]
          exact ih _ _ _ _ _ _ _ _ _ _ _ _ hlent' hmid_le hhi_le hF' hfwd'
        · have hsltF : (la[i.toNat].slt la[j.toNat]) = false :=
            Bool.eq_false_of_ne_true hslt
          have hfwdJ : mergeRunsMainFwd la (lt.set k.toNat la[j.toNat])
              ((mid.toNat - i.toNat) + (hi.toNat - j.toNat) - 1)
              i.toNat (j.toNat + 1) (k.toNat + 1) mid.toNat hi.toNat =
              .ok (i', j', k', lt') := by
            have h := hfwd
            simp only [mergeRunsMainFwd, dite_eq_left hI, dite_eq_left hJ,
              hgetK, hgetI, hgetJ, hsltF] at h
            exact h
          have hstep : evalProgStmt prog F mergeRunsMainBody
              (mkRunsEnv la lt lo mid hi i j k) =
              .ok (mkRunsEnv la (lt.set k.toNat la[j.toNat]) lo mid hi
                i (j + 1) (k + 1), .fellThrough) :=
            mergeRunsMainBody_hitJ prog F la lt lo mid hi i j k _ _ _
              hlent hgetI hgetJ hsltF hltK hgetK
          have hloop : evalProgStmt prog (F + 1) mergeRunsMain
              (mkRunsEnv la lt lo mid hi i j k) =
              evalProgStmt prog F mergeRunsMain
                (mkRunsEnv la (lt.set k.toNat la[j.toNat]) lo mid hi
                  i (j + 1) (k + 1)) := by
            cir_unfold_prog (mergeRunsMain, prog, F, hcond, hstep)
          have h1j : (j + 1).toNat = j.toNat + 1 :=
            bv64_succ_toNat j _ hJ (by omega)
          have h1k : (k + 1).toNat = k.toNat + 1 :=
            bv64_succ_toNat k _ hltK hlent
          have hlent' : (lt.set k.toNat la[j.toNat]).length < 2 ^ 64 := by
            rw [List.length_set]
            exact hlent
          have hF' : (mid.toNat - i.toNat) +
              (hi.toNat - (j + 1).toNat) + 1 ≤ F := by omega
          have hfwd' : mergeRunsMainFwd la (lt.set k.toNat la[j.toNat])
              ((mid.toNat - i.toNat) + (hi.toNat - (j + 1).toNat))
              i.toNat ((j + 1).toNat) ((k + 1).toNat)
              mid.toNat hi.toNat =
              .ok (i', j', k', lt') := by
            have hM' : (mid.toNat - i.toNat) + (hi.toNat - j.toNat) - 1 =
                (mid.toNat - i.toNat) + (hi.toNat - (j + 1).toNat) := by
              omega
            rw [← h1j, ← h1k, hM'] at hfwdJ
            exact hfwdJ
          rw [hloop]
          exact ih _ _ _ _ _ _ _ _ _ _ _ _ hlent' hmid_le hhi_le hF' hfwd'
    · have hcond : evalExpr
          (.tif (.ult (.var "i") (.var "mid"))
            (.ult (.var "j") (.var "hi"))
            (.lit (.b false)))
          (mkRunsEnv la lt lo mid hi i j k) = .ok (.b false) :=
        runsMainGuard_false la lt lo mid hi i j k hguard
      have hfwd0 : mergeRunsMainFwd la lt
          ((mid.toNat - i.toNat) + (hi.toNat - j.toNat))
          i.toNat j.toNat k.toNat mid.toNat hi.toNat =
          .ok (i.toNat, j.toNat, k.toNat, lt) := by
        match hm : (mid.toNat - i.toNat) + (hi.toNat - j.toNat) with
        | 0 => simp only [mergeRunsMainFwd]
        | _ + 1 =>
          by_cases hI' : i.toNat < mid.toNat
          · have hnJ : ¬ j.toNat < hi.toNat :=
              fun hj => hguard ⟨hI', hj⟩
            simp only [mergeRunsMainFwd, dite_eq_left hI',
              dite_eq_right hnJ]
          · simp only [mergeRunsMainFwd, dite_eq_right hI']
      rw [hfwd0] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hfwd
      have hexit : evalProgStmt prog (F + 1) mergeRunsMain
          (mkRunsEnv la lt lo mid hi i j k) =
          .ok (mkRunsEnv la lt lo mid hi i j k, .fellThrough) :=
        evalProgStmt_while_false prog _ _ _ _ hcond
      rw [hexit, bv64_ofNat_toNat i, bv64_ofNat_toNat j,
        bv64_ofNat_toNat k]

/-- Main-loop err soundness: the model abort ⟹ evaluation aborts. -/
theorem mergeRunsMain_err (prog : Prog) (F : Nat)
    (la lt : List (BitVec 32)) (lo mid hi i j k : BitVec 64)
    (e : Panic)
    (hlent : lt.length < 2 ^ 64)
    (hmid_le : mid.toNat ≤ la.length) (hhi_le : hi.toNat ≤ la.length)
    (hF : (mid.toNat - i.toNat) + (hi.toNat - j.toNat) + 1 ≤ F)
    (hfwd : mergeRunsMainFwd la lt
      ((mid.toNat - i.toNat) + (hi.toNat - j.toNat))
      i.toNat j.toNat k.toNat mid.toNat hi.toNat = .error e) :
    evalProgStmt prog F mergeRunsMain
      (mkRunsEnv la lt lo mid hi i j k) = .error e := by
  induction F generalizing la lt lo mid hi i j k e with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hguard : (i.toNat < mid.toNat ∧ j.toNat < hi.toNat)
    · obtain ⟨hI, hJ⟩ := hguard
      have hcond : evalExpr
          (.tif (.ult (.var "i") (.var "mid"))
            (.ult (.var "j") (.var "hi"))
            (.lit (.b false)))
          (mkRunsEnv la lt lo mid hi i j k) = .ok (.b true) :=
        runsMainGuard_true la lt lo mid hi i j k hI hJ
      have hM : (mid.toNat - i.toNat) + (hi.toNat - j.toNat) =
          ((mid.toNat - i.toNat) + (hi.toNat - j.toNat) - 1) + 1 := by
        omega
      rw [hM] at hfwd
      have hgetI : la[i.toNat]? = some la[i.toNat] :=
        List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hI hmid_le)
      have hgetJ : la[j.toNat]? = some la[j.toNat] :=
        List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hJ hhi_le)
      cases hgetK : lt[k.toNat]? with
      | none =>
        have hfwde : mergeRunsMainFwd la lt
            (((mid.toNat - i.toNat) + (hi.toNat - j.toNat) - 1) + 1)
            i.toNat j.toNat k.toNat mid.toNat hi.toNat =
            .error .AssertFail := by
          simp only [mergeRunsMainFwd, dite_eq_left hI, dite_eq_left hJ,
            hgetK]
        rw [hfwde] at hfwd
        cases hfwd
        have hltK : ¬ k.toNat < lt.length := by
          intro hc
          have hsome := List.getElem?_eq_getElem hc
          rw [hsome] at hgetK
          cases hgetK
        by_cases hslt : (la[i.toNat].slt la[j.toNat]) = true
        · have hbody := mergeRunsMainBody_missI prog F la lt lo mid hi
            i j k _ _ hlent hgetI hgetJ hslt hltK
          have herr : evalProgStmt prog (F + 1) mergeRunsMain
              (mkRunsEnv la lt lo mid hi i j k) =
              .error .AssertFail := by
            cir_unfold_prog (mergeRunsMain, prog, F, hcond, hbody)
          exact herr
        · have hsltF : (la[i.toNat].slt la[j.toNat]) = false :=
            Bool.eq_false_of_ne_true hslt
          have hbody := mergeRunsMainBody_missJ prog F la lt lo mid hi
            i j k _ _ hlent hgetI hgetJ hsltF hltK
          have herr : evalProgStmt prog (F + 1) mergeRunsMain
              (mkRunsEnv la lt lo mid hi i j k) =
              .error .AssertFail := by
            cir_unfold_prog (mergeRunsMain, prog, F, hcond, hbody)
          exact herr
      | some w =>
        have hltK : k.toNat < lt.length :=
          list_lt_of_getElem?_some lt k.toNat w hgetK
        by_cases hslt : (la[i.toNat].slt la[j.toNat]) = true
        · have hfwdI : mergeRunsMainFwd la (lt.set k.toNat la[i.toNat])
              ((mid.toNat - i.toNat) + (hi.toNat - j.toNat) - 1)
              (i.toNat + 1) j.toNat (k.toNat + 1)
              mid.toNat hi.toNat = .error e := by
            have h := hfwd
            simp only [mergeRunsMainFwd, dite_eq_left hI, dite_eq_left hJ,
              hgetK, hgetI, hgetJ, hslt] at h
            exact h
          have hstep : evalProgStmt prog F mergeRunsMainBody
              (mkRunsEnv la lt lo mid hi i j k) =
              .ok (mkRunsEnv la (lt.set k.toNat la[i.toNat]) lo mid hi
                (i + 1) j (k + 1), .fellThrough) :=
            mergeRunsMainBody_hitI prog F la lt lo mid hi i j k _ _ _
              hlent hgetI hgetJ hslt hltK hgetK
          have hloop : evalProgStmt prog (F + 1) mergeRunsMain
              (mkRunsEnv la lt lo mid hi i j k) =
              evalProgStmt prog F mergeRunsMain
                (mkRunsEnv la (lt.set k.toNat la[i.toNat]) lo mid hi
                  (i + 1) j (k + 1)) := by
            cir_unfold_prog (mergeRunsMain, prog, F, hcond, hstep)
          have h1i : (i + 1).toNat = i.toNat + 1 :=
            bv64_succ_toNat i _ hI (by omega)
          have h1k : (k + 1).toNat = k.toNat + 1 :=
            bv64_succ_toNat k _ hltK hlent
          have hlent' : (lt.set k.toNat la[i.toNat]).length < 2 ^ 64 := by
            rw [List.length_set]
            exact hlent
          have hF' : (mid.toNat - (i + 1).toNat) +
              (hi.toNat - j.toNat) + 1 ≤ F := by omega
          have hfwd' : mergeRunsMainFwd la (lt.set k.toNat la[i.toNat])
              ((mid.toNat - (i + 1).toNat) + (hi.toNat - j.toNat))
              ((i + 1).toNat) j.toNat ((k + 1).toNat)
              mid.toNat hi.toNat = .error e := by
            have hM' : (mid.toNat - i.toNat) + (hi.toNat - j.toNat) - 1 =
                (mid.toNat - (i + 1).toNat) + (hi.toNat - j.toNat) := by
              omega
            rw [← h1i, ← h1k, hM'] at hfwdI
            exact hfwdI
          rw [hloop]
          exact ih _ _ _ _ _ _ _ _ _ hlent' hmid_le hhi_le hF' hfwd'
        · have hsltF : (la[i.toNat].slt la[j.toNat]) = false :=
            Bool.eq_false_of_ne_true hslt
          have hfwdJ : mergeRunsMainFwd la (lt.set k.toNat la[j.toNat])
              ((mid.toNat - i.toNat) + (hi.toNat - j.toNat) - 1)
              i.toNat (j.toNat + 1) (k.toNat + 1)
              mid.toNat hi.toNat = .error e := by
            have h := hfwd
            simp only [mergeRunsMainFwd, dite_eq_left hI, dite_eq_left hJ,
              hgetK, hgetI, hgetJ, hsltF] at h
            exact h
          have hstep : evalProgStmt prog F mergeRunsMainBody
              (mkRunsEnv la lt lo mid hi i j k) =
              .ok (mkRunsEnv la (lt.set k.toNat la[j.toNat]) lo mid hi
                i (j + 1) (k + 1), .fellThrough) :=
            mergeRunsMainBody_hitJ prog F la lt lo mid hi i j k _ _ _
              hlent hgetI hgetJ hsltF hltK hgetK
          have hloop : evalProgStmt prog (F + 1) mergeRunsMain
              (mkRunsEnv la lt lo mid hi i j k) =
              evalProgStmt prog F mergeRunsMain
                (mkRunsEnv la (lt.set k.toNat la[j.toNat]) lo mid hi
                  i (j + 1) (k + 1)) := by
            cir_unfold_prog (mergeRunsMain, prog, F, hcond, hstep)
          have h1j : (j + 1).toNat = j.toNat + 1 :=
            bv64_succ_toNat j _ hJ (by omega)
          have h1k : (k + 1).toNat = k.toNat + 1 :=
            bv64_succ_toNat k _ hltK hlent
          have hlent' : (lt.set k.toNat la[j.toNat]).length < 2 ^ 64 := by
            rw [List.length_set]
            exact hlent
          have hF' : (mid.toNat - i.toNat) +
              (hi.toNat - (j + 1).toNat) + 1 ≤ F := by omega
          have hfwd' : mergeRunsMainFwd la (lt.set k.toNat la[j.toNat])
              ((mid.toNat - i.toNat) + (hi.toNat - (j + 1).toNat))
              i.toNat ((j + 1).toNat) ((k + 1).toNat)
              mid.toNat hi.toNat = .error e := by
            have hM' : (mid.toNat - i.toNat) + (hi.toNat - j.toNat) - 1 =
                (mid.toNat - i.toNat) + (hi.toNat - (j + 1).toNat) := by
              omega
            rw [← h1j, ← h1k, hM'] at hfwdJ
            exact hfwdJ
          rw [hloop]
          exact ih _ _ _ _ _ _ _ _ _ hlent' hmid_le hhi_le hF' hfwd'
    · have hcond : evalExpr
          (.tif (.ult (.var "i") (.var "mid"))
            (.ult (.var "j") (.var "hi"))
            (.lit (.b false)))
          (mkRunsEnv la lt lo mid hi i j k) = .ok (.b false) :=
        runsMainGuard_false la lt lo mid hi i j k hguard
      have hfwd0 : mergeRunsMainFwd la lt
          ((mid.toNat - i.toNat) + (hi.toNat - j.toNat))
          i.toNat j.toNat k.toNat mid.toNat hi.toNat =
          .ok (i.toNat, j.toNat, k.toNat, lt) := by
        match hm : (mid.toNat - i.toNat) + (hi.toNat - j.toNat) with
        | 0 => simp only [mergeRunsMainFwd]
        | _ + 1 =>
          by_cases hI' : i.toNat < mid.toNat
          · have hnJ : ¬ j.toNat < hi.toNat :=
              fun hj => hguard ⟨hI', hj⟩
            simp only [mergeRunsMainFwd, dite_eq_left hI',
              dite_eq_right hnJ]
          · simp only [mergeRunsMainFwd, dite_eq_right hI']
      rw [hfwd0] at hfwd
      cases hfwd

/-- Drain-`i` ok soundness. -/
theorem mergeRunsDrainI_ok (prog : Prog) (F : Nat)
    (la lt : List (BitVec 32)) (lo mid hi i j k : BitVec 64)
    (i' k' : Nat) (lt' : List (BitVec 32))
    (hlent : lt.length < 2 ^ 64)
    (hmid_le : mid.toNat ≤ la.length)
    (hF : (mid.toNat - i.toNat) + 1 ≤ F)
    (hfwd : mergeRunsDrainIFwd la lt (mid.toNat - i.toNat)
      i.toNat k.toNat mid.toNat = .ok (i', k', lt')) :
    evalProgStmt prog F mergeRunsDrainI
        (mkRunsEnv la lt lo mid hi i j k) =
      .ok (mkRunsEnv la lt' lo mid hi (BitVec.ofNat 64 i') j
        (BitVec.ofNat 64 k'), .fellThrough) := by
  induction F generalizing la lt lo mid hi i j k i' k' lt' with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hI : i.toNat < mid.toNat
    · have hcond : evalExpr (.ult (.var "i") (.var "mid"))
          (mkRunsEnv la lt lo mid hi i j k) = .ok (.b true) := by
        have h := runsGuardI_eval la lt lo mid hi i j k
        rwa [decide_eq_true hI] at h
      have hM : (mid.toNat - i.toNat) =
          ((mid.toNat - i.toNat) - 1) + 1 := by omega
      rw [hM] at hfwd
      have hgetI : la[i.toNat]? = some la[i.toNat] :=
        List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hI hmid_le)
      cases hgetK : lt[k.toNat]? with
      | none =>
        have hcontra : mergeRunsDrainIFwd la lt
            (((mid.toNat - i.toNat) - 1) + 1)
            i.toNat k.toNat mid.toNat = .error .AssertFail := by
          simp only [mergeRunsDrainIFwd, dite_eq_left hI, hgetK]
        rw [hcontra] at hfwd
        cases hfwd
      | some w =>
        have hltK : k.toNat < lt.length :=
          list_lt_of_getElem?_some lt k.toNat w hgetK
        have hfwdI : mergeRunsDrainIFwd la (lt.set k.toNat la[i.toNat])
            ((mid.toNat - i.toNat) - 1)
            (i.toNat + 1) (k.toNat + 1) mid.toNat =
            .ok (i', k', lt') := by
          have h := hfwd
          simp only [mergeRunsDrainIFwd, dite_eq_left hI, hgetK,
            hgetI] at h
          exact h
        have hstep : evalProgStmt prog F mergeRunsDrainIBody
            (mkRunsEnv la lt lo mid hi i j k) =
            .ok (mkRunsEnv la (lt.set k.toNat la[i.toNat]) lo mid hi
              (i + 1) j (k + 1), .fellThrough) :=
          mergeRunsDrainIBody_hit prog F la lt lo mid hi i j k _ _
            hlent hgetI hltK hgetK
        have hloop : evalProgStmt prog (F + 1) mergeRunsDrainI
            (mkRunsEnv la lt lo mid hi i j k) =
            evalProgStmt prog F mergeRunsDrainI
              (mkRunsEnv la (lt.set k.toNat la[i.toNat]) lo mid hi
                (i + 1) j (k + 1)) := by
          cir_unfold_prog (mergeRunsDrainI, prog, F, hcond, hstep)
        have h1i : (i + 1).toNat = i.toNat + 1 :=
          bv64_succ_toNat i _ hI (by omega)
        have h1k : (k + 1).toNat = k.toNat + 1 :=
          bv64_succ_toNat k _ hltK hlent
        have hlent' : (lt.set k.toNat la[i.toNat]).length < 2 ^ 64 := by
          rw [List.length_set]
          exact hlent
        have hF' : (mid.toNat - (i + 1).toNat) + 1 ≤ F := by omega
        have hfwd' : mergeRunsDrainIFwd la (lt.set k.toNat la[i.toNat])
            (mid.toNat - (i + 1).toNat)
            ((i + 1).toNat) ((k + 1).toNat) mid.toNat =
            .ok (i', k', lt') := by
          have hM' : (mid.toNat - i.toNat) - 1 =
              (mid.toNat - (i + 1).toNat) := by
            omega
          rw [← h1i, ← h1k, hM'] at hfwdI
          exact hfwdI
        rw [hloop]
        exact ih _ _ _ _ _ _ _ _ _ _ _ hlent' hmid_le hF' hfwd'
    · have hcond : evalExpr (.ult (.var "i") (.var "mid"))
          (mkRunsEnv la lt lo mid hi i j k) = .ok (.b false) := by
        have h := runsGuardI_eval la lt lo mid hi i j k
        rwa [decide_eq_false hI] at h
      have hfwd0 : mergeRunsDrainIFwd la lt (mid.toNat - i.toNat)
          i.toNat k.toNat mid.toNat = .ok (i.toNat, k.toNat, lt) := by
        match hm : (mid.toNat - i.toNat) with
        | 0 => simp only [mergeRunsDrainIFwd]
        | _ + 1 =>
          simp only [mergeRunsDrainIFwd, dite_eq_right hI]
      rw [hfwd0] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hfwd
      have hexit : evalProgStmt prog (F + 1) mergeRunsDrainI
          (mkRunsEnv la lt lo mid hi i j k) =
          .ok (mkRunsEnv la lt lo mid hi i j k, .fellThrough) :=
        evalProgStmt_while_false prog _ _ _ _ hcond
      rw [hexit, bv64_ofNat_toNat i, bv64_ofNat_toNat k]

/-- Drain-`i` err soundness. -/
theorem mergeRunsDrainI_err (prog : Prog) (F : Nat)
    (la lt : List (BitVec 32)) (lo mid hi i j k : BitVec 64)
    (e : Panic)
    (hlent : lt.length < 2 ^ 64)
    (hmid_le : mid.toNat ≤ la.length)
    (hF : (mid.toNat - i.toNat) + 1 ≤ F)
    (hfwd : mergeRunsDrainIFwd la lt (mid.toNat - i.toNat)
      i.toNat k.toNat mid.toNat = .error e) :
    evalProgStmt prog F mergeRunsDrainI
      (mkRunsEnv la lt lo mid hi i j k) = .error e := by
  induction F generalizing la lt lo mid hi i j k e with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hI : i.toNat < mid.toNat
    · have hcond : evalExpr (.ult (.var "i") (.var "mid"))
          (mkRunsEnv la lt lo mid hi i j k) = .ok (.b true) := by
        have h := runsGuardI_eval la lt lo mid hi i j k
        rwa [decide_eq_true hI] at h
      have hM : (mid.toNat - i.toNat) =
          ((mid.toNat - i.toNat) - 1) + 1 := by omega
      rw [hM] at hfwd
      have hgetI : la[i.toNat]? = some la[i.toNat] :=
        List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hI hmid_le)
      cases hgetK : lt[k.toNat]? with
      | none =>
        have hfwde : mergeRunsDrainIFwd la lt
            (((mid.toNat - i.toNat) - 1) + 1)
            i.toNat k.toNat mid.toNat = .error .AssertFail := by
          simp only [mergeRunsDrainIFwd, dite_eq_left hI, hgetK]
        rw [hfwde] at hfwd
        cases hfwd
        have hltK : ¬ k.toNat < lt.length := by
          intro hc
          have hsome := List.getElem?_eq_getElem hc
          rw [hsome] at hgetK
          cases hgetK
        have hbody := mergeRunsDrainIBody_miss prog F la lt lo mid hi
          i j k hlent hltK
        have herr : evalProgStmt prog (F + 1) mergeRunsDrainI
            (mkRunsEnv la lt lo mid hi i j k) =
            .error .AssertFail := by
          cir_unfold_prog (mergeRunsDrainI, prog, F, hcond, hbody)
        exact herr
      | some w =>
        have hltK : k.toNat < lt.length :=
          list_lt_of_getElem?_some lt k.toNat w hgetK
        have hfwdI : mergeRunsDrainIFwd la (lt.set k.toNat la[i.toNat])
            ((mid.toNat - i.toNat) - 1)
            (i.toNat + 1) (k.toNat + 1) mid.toNat = .error e := by
          have h := hfwd
          simp only [mergeRunsDrainIFwd, dite_eq_left hI, hgetK,
            hgetI] at h
          exact h
        have hstep : evalProgStmt prog F mergeRunsDrainIBody
            (mkRunsEnv la lt lo mid hi i j k) =
            .ok (mkRunsEnv la (lt.set k.toNat la[i.toNat]) lo mid hi
              (i + 1) j (k + 1), .fellThrough) :=
          mergeRunsDrainIBody_hit prog F la lt lo mid hi i j k _ _
            hlent hgetI hltK hgetK
        have hloop : evalProgStmt prog (F + 1) mergeRunsDrainI
            (mkRunsEnv la lt lo mid hi i j k) =
            evalProgStmt prog F mergeRunsDrainI
              (mkRunsEnv la (lt.set k.toNat la[i.toNat]) lo mid hi
                (i + 1) j (k + 1)) := by
          cir_unfold_prog (mergeRunsDrainI, prog, F, hcond, hstep)
        have h1i : (i + 1).toNat = i.toNat + 1 :=
          bv64_succ_toNat i _ hI (by omega)
        have h1k : (k + 1).toNat = k.toNat + 1 :=
          bv64_succ_toNat k _ hltK hlent
        have hlent' : (lt.set k.toNat la[i.toNat]).length < 2 ^ 64 := by
          rw [List.length_set]
          exact hlent
        have hF' : (mid.toNat - (i + 1).toNat) + 1 ≤ F := by omega
        have hfwd' : mergeRunsDrainIFwd la (lt.set k.toNat la[i.toNat])
            (mid.toNat - (i + 1).toNat)
            ((i + 1).toNat) ((k + 1).toNat) mid.toNat = .error e := by
          have hM' : (mid.toNat - i.toNat) - 1 =
              (mid.toNat - (i + 1).toNat) := by
            omega
          rw [← h1i, ← h1k, hM'] at hfwdI
          exact hfwdI
        rw [hloop]
        exact ih _ _ _ _ _ _ _ _ _ hlent' hmid_le hF' hfwd'
    · have hcond : evalExpr (.ult (.var "i") (.var "mid"))
          (mkRunsEnv la lt lo mid hi i j k) = .ok (.b false) := by
        have h := runsGuardI_eval la lt lo mid hi i j k
        rwa [decide_eq_false hI] at h
      have hfwd0 : mergeRunsDrainIFwd la lt (mid.toNat - i.toNat)
          i.toNat k.toNat mid.toNat = .ok (i.toNat, k.toNat, lt) := by
        match hm : (mid.toNat - i.toNat) with
        | 0 => simp only [mergeRunsDrainIFwd]
        | _ + 1 =>
          simp only [mergeRunsDrainIFwd, dite_eq_right hI]
      rw [hfwd0] at hfwd
      cases hfwd

/-- Drain-`j` ok soundness. -/
theorem mergeRunsDrainJ_ok (prog : Prog) (F : Nat)
    (la lt : List (BitVec 32)) (lo mid hi i j k : BitVec 64)
    (j' k' : Nat) (lt' : List (BitVec 32))
    (hlent : lt.length < 2 ^ 64)
    (hhi_le : hi.toNat ≤ la.length)
    (hF : (hi.toNat - j.toNat) + 1 ≤ F)
    (hfwd : mergeRunsDrainJFwd la lt (hi.toNat - j.toNat)
      j.toNat k.toNat hi.toNat = .ok (j', k', lt')) :
    evalProgStmt prog F mergeRunsDrainJ
        (mkRunsEnv la lt lo mid hi i j k) =
      .ok (mkRunsEnv la lt' lo mid hi i (BitVec.ofNat 64 j')
        (BitVec.ofNat 64 k'), .fellThrough) := by
  induction F generalizing la lt lo mid hi i j k j' k' lt' with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hJ : j.toNat < hi.toNat
    · have hcond : evalExpr (.ult (.var "j") (.var "hi"))
          (mkRunsEnv la lt lo mid hi i j k) = .ok (.b true) := by
        have h := runsGuardJ_eval la lt lo mid hi i j k
        rwa [decide_eq_true hJ] at h
      have hM : (hi.toNat - j.toNat) =
          ((hi.toNat - j.toNat) - 1) + 1 := by omega
      rw [hM] at hfwd
      have hgetJ : la[j.toNat]? = some la[j.toNat] :=
        List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hJ hhi_le)
      cases hgetK : lt[k.toNat]? with
      | none =>
        have hcontra : mergeRunsDrainJFwd la lt
            (((hi.toNat - j.toNat) - 1) + 1)
            j.toNat k.toNat hi.toNat = .error .AssertFail := by
          simp only [mergeRunsDrainJFwd, dite_eq_left hJ, hgetK]
        rw [hcontra] at hfwd
        cases hfwd
      | some w =>
        have hltK : k.toNat < lt.length :=
          list_lt_of_getElem?_some lt k.toNat w hgetK
        have hfwdJ : mergeRunsDrainJFwd la (lt.set k.toNat la[j.toNat])
            ((hi.toNat - j.toNat) - 1)
            (j.toNat + 1) (k.toNat + 1) hi.toNat =
            .ok (j', k', lt') := by
          have h := hfwd
          simp only [mergeRunsDrainJFwd, dite_eq_left hJ, hgetK,
            hgetJ] at h
          exact h
        have hstep : evalProgStmt prog F mergeRunsDrainJBody
            (mkRunsEnv la lt lo mid hi i j k) =
            .ok (mkRunsEnv la (lt.set k.toNat la[j.toNat]) lo mid hi
              i (j + 1) (k + 1), .fellThrough) :=
          mergeRunsDrainJBody_hit prog F la lt lo mid hi i j k _ _
            hlent hgetJ hltK hgetK
        have hloop : evalProgStmt prog (F + 1) mergeRunsDrainJ
            (mkRunsEnv la lt lo mid hi i j k) =
            evalProgStmt prog F mergeRunsDrainJ
              (mkRunsEnv la (lt.set k.toNat la[j.toNat]) lo mid hi
                i (j + 1) (k + 1)) := by
          cir_unfold_prog (mergeRunsDrainJ, prog, F, hcond, hstep)
        have h1j : (j + 1).toNat = j.toNat + 1 :=
          bv64_succ_toNat j _ hJ (by omega)
        have h1k : (k + 1).toNat = k.toNat + 1 :=
          bv64_succ_toNat k _ hltK hlent
        have hlent' : (lt.set k.toNat la[j.toNat]).length < 2 ^ 64 := by
          rw [List.length_set]
          exact hlent
        have hF' : (hi.toNat - (j + 1).toNat) + 1 ≤ F := by omega
        have hfwd' : mergeRunsDrainJFwd la (lt.set k.toNat la[j.toNat])
            (hi.toNat - (j + 1).toNat)
            ((j + 1).toNat) ((k + 1).toNat) hi.toNat =
            .ok (j', k', lt') := by
          have hM' : (hi.toNat - j.toNat) - 1 =
              (hi.toNat - (j + 1).toNat) := by
            omega
          rw [← h1j, ← h1k, hM'] at hfwdJ
          exact hfwdJ
        rw [hloop]
        exact ih _ _ _ _ _ _ _ _ _ _ _ hlent' hhi_le hF' hfwd'
    · have hcond : evalExpr (.ult (.var "j") (.var "hi"))
          (mkRunsEnv la lt lo mid hi i j k) = .ok (.b false) := by
        have h := runsGuardJ_eval la lt lo mid hi i j k
        rwa [decide_eq_false hJ] at h
      have hfwd0 : mergeRunsDrainJFwd la lt (hi.toNat - j.toNat)
          j.toNat k.toNat hi.toNat = .ok (j.toNat, k.toNat, lt) := by
        match hm : (hi.toNat - j.toNat) with
        | 0 => simp only [mergeRunsDrainJFwd]
        | _ + 1 =>
          simp only [mergeRunsDrainJFwd, dite_eq_right hJ]
      rw [hfwd0] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hfwd
      have hexit : evalProgStmt prog (F + 1) mergeRunsDrainJ
          (mkRunsEnv la lt lo mid hi i j k) =
          .ok (mkRunsEnv la lt lo mid hi i j k, .fellThrough) :=
        evalProgStmt_while_false prog _ _ _ _ hcond
      rw [hexit, bv64_ofNat_toNat j, bv64_ofNat_toNat k]

/-- Drain-`j` err soundness. -/
theorem mergeRunsDrainJ_err (prog : Prog) (F : Nat)
    (la lt : List (BitVec 32)) (lo mid hi i j k : BitVec 64)
    (e : Panic)
    (hlent : lt.length < 2 ^ 64)
    (hhi_le : hi.toNat ≤ la.length)
    (hF : (hi.toNat - j.toNat) + 1 ≤ F)
    (hfwd : mergeRunsDrainJFwd la lt (hi.toNat - j.toNat)
      j.toNat k.toNat hi.toNat = .error e) :
    evalProgStmt prog F mergeRunsDrainJ
      (mkRunsEnv la lt lo mid hi i j k) = .error e := by
  induction F generalizing la lt lo mid hi i j k e with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F ih =>
    by_cases hJ : j.toNat < hi.toNat
    · have hcond : evalExpr (.ult (.var "j") (.var "hi"))
          (mkRunsEnv la lt lo mid hi i j k) = .ok (.b true) := by
        have h := runsGuardJ_eval la lt lo mid hi i j k
        rwa [decide_eq_true hJ] at h
      have hM : (hi.toNat - j.toNat) =
          ((hi.toNat - j.toNat) - 1) + 1 := by omega
      rw [hM] at hfwd
      have hgetJ : la[j.toNat]? = some la[j.toNat] :=
        List.getElem?_eq_getElem (Nat.lt_of_lt_of_le hJ hhi_le)
      cases hgetK : lt[k.toNat]? with
      | none =>
        have hfwde : mergeRunsDrainJFwd la lt
            (((hi.toNat - j.toNat) - 1) + 1)
            j.toNat k.toNat hi.toNat = .error .AssertFail := by
          simp only [mergeRunsDrainJFwd, dite_eq_left hJ, hgetK]
        rw [hfwde] at hfwd
        cases hfwd
        have hltK : ¬ k.toNat < lt.length := by
          intro hc
          have hsome := List.getElem?_eq_getElem hc
          rw [hsome] at hgetK
          cases hgetK
        have hbody := mergeRunsDrainJBody_miss prog F la lt lo mid hi
          i j k hlent hltK
        have herr : evalProgStmt prog (F + 1) mergeRunsDrainJ
            (mkRunsEnv la lt lo mid hi i j k) =
            .error .AssertFail := by
          cir_unfold_prog (mergeRunsDrainJ, prog, F, hcond, hbody)
        exact herr
      | some w =>
        have hltK : k.toNat < lt.length :=
          list_lt_of_getElem?_some lt k.toNat w hgetK
        have hfwdJ : mergeRunsDrainJFwd la (lt.set k.toNat la[j.toNat])
            ((hi.toNat - j.toNat) - 1)
            (j.toNat + 1) (k.toNat + 1) hi.toNat = .error e := by
          have h := hfwd
          simp only [mergeRunsDrainJFwd, dite_eq_left hJ, hgetK,
            hgetJ] at h
          exact h
        have hstep : evalProgStmt prog F mergeRunsDrainJBody
            (mkRunsEnv la lt lo mid hi i j k) =
            .ok (mkRunsEnv la (lt.set k.toNat la[j.toNat]) lo mid hi
              i (j + 1) (k + 1), .fellThrough) :=
          mergeRunsDrainJBody_hit prog F la lt lo mid hi i j k _ _
            hlent hgetJ hltK hgetK
        have hloop : evalProgStmt prog (F + 1) mergeRunsDrainJ
            (mkRunsEnv la lt lo mid hi i j k) =
            evalProgStmt prog F mergeRunsDrainJ
              (mkRunsEnv la (lt.set k.toNat la[j.toNat]) lo mid hi
                i (j + 1) (k + 1)) := by
          cir_unfold_prog (mergeRunsDrainJ, prog, F, hcond, hstep)
        have h1j : (j + 1).toNat = j.toNat + 1 :=
          bv64_succ_toNat j _ hJ (by omega)
        have h1k : (k + 1).toNat = k.toNat + 1 :=
          bv64_succ_toNat k _ hltK hlent
        have hlent' : (lt.set k.toNat la[j.toNat]).length < 2 ^ 64 := by
          rw [List.length_set]
          exact hlent
        have hF' : (hi.toNat - (j + 1).toNat) + 1 ≤ F := by omega
        have hfwd' : mergeRunsDrainJFwd la (lt.set k.toNat la[j.toNat])
            (hi.toNat - (j + 1).toNat)
            ((j + 1).toNat) ((k + 1).toNat) hi.toNat = .error e := by
          have hM' : (hi.toNat - j.toNat) - 1 =
              (hi.toNat - (j + 1).toNat) := by
            omega
          rw [← h1j, ← h1k, hM'] at hfwdJ
          exact hfwdJ
        rw [hloop]
        exact ih _ _ _ _ _ _ _ _ _ hlent' hhi_le hF' hfwd'
    · have hcond : evalExpr (.ult (.var "j") (.var "hi"))
          (mkRunsEnv la lt lo mid hi i j k) = .ok (.b false) := by
        have h := runsGuardJ_eval la lt lo mid hi i j k
        rwa [decide_eq_false hJ] at h
      have hfwd0 : mergeRunsDrainJFwd la lt (hi.toNat - j.toNat)
          j.toNat k.toNat hi.toNat = .ok (j.toNat, k.toNat, lt) := by
        match hm : (hi.toNat - j.toNat) with
        | 0 => simp only [mergeRunsDrainJFwd]
        | _ + 1 =>
          simp only [mergeRunsDrainJFwd, dite_eq_right hJ]
      rw [hfwd0] at hfwd
      cases hfwd

/-! ## Forward-model bounds (sequential chaining) -/

/-- Main-model results stay inside the bounds and preserve `tmp`
    length (fuel induction; every taken step checked its bounds). -/
theorem mergeRunsMainFwd_le (la : List (BitVec 32))
    (F' i j k mid hi : Nat)
    (lt : List (BitVec 32)) (i' j' k' : Nat) (lt' : List (BitVec 32))
    (hi_ : i ≤ mid) (hj_ : j ≤ hi) (hk : k ≤ lt.length)
    (hfwd : mergeRunsMainFwd la lt F' i j k mid hi =
      .ok (i', j', k', lt')) :
    i' ≤ mid ∧ j' ≤ hi ∧ k' ≤ lt.length ∧
      lt'.length = lt.length ∧ i ≤ i' ∧ j ≤ j' := by
  induction F' generalizing lt i j k mid hi i' j' k' lt' with
  | zero =>
    simp only [mergeRunsMainFwd, Except.ok.injEq, Prod.mk.injEq] at hfwd
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hfwd
    exact ⟨hi_, hj_, hk, rfl, Nat.le_refl _, Nat.le_refl _⟩
  | succ F' ih =>
    by_cases hI : i < mid
    · by_cases hJ : j < hi
      · cases hK : lt[k]? with
        | none =>
          simp only [mergeRunsMainFwd, dite_eq_left hI, dite_eq_left hJ,
            hK] at hfwd
          cases hfwd
        | some w =>
          have hklen : k < lt.length :=
            list_lt_of_getElem?_some lt k w hK
          cases hAi : la[i]? with
          | none =>
            cases hAj : la[j]? with
            | none =>
              simp only [mergeRunsMainFwd, dite_eq_left hI,
                dite_eq_left hJ, hK, hAi, hAj] at hfwd
              cases hfwd
            | some y =>
              simp only [mergeRunsMainFwd, dite_eq_left hI,
                dite_eq_left hJ, hK, hAi, hAj] at hfwd
              cases hfwd
          | some x =>
            cases hAj : la[j]? with
            | none =>
              simp only [mergeRunsMainFwd, dite_eq_left hI,
                dite_eq_left hJ, hK, hAi, hAj] at hfwd
              cases hfwd
            | some y =>
              have hset : (lt.set k x).length = lt.length :=
                List.length_set
              by_cases hslt : x.slt y
              · simp only [mergeRunsMainFwd, dite_eq_left hI,
                  dite_eq_left hJ, hK, hAi, hAj, hslt] at hfwd
                have hk1 : k + 1 ≤ (lt.set k x).length := by
                  rw [hset]; omega
                obtain ⟨hi', hj', hk', hlen, hloi, hloj⟩ :=
                  ih _ _ _ _ _ _ _ _ _ _ (by omega) hj_ hk1 hfwd
                exact ⟨hi', hj', hset ▸ hk', hlen.trans hset,
                  Nat.le_trans (by omega) hloi,
                  Nat.le_trans (Nat.le_refl _) hloj⟩
              · have hsltF : (x.slt y) = false :=
                  Bool.eq_false_of_ne_true hslt
                simp only [mergeRunsMainFwd, dite_eq_left hI,
                  dite_eq_left hJ, hK, hAi, hAj, hsltF] at hfwd
                have hsety : (lt.set k y).length = lt.length :=
                  List.length_set
                have hk1 : k + 1 ≤ (lt.set k y).length := by
                  rw [hsety]; omega
                obtain ⟨hi', hj', hk', hlen, hloi, hloj⟩ :=
                  ih _ _ _ _ _ _ _ _ _ _ hi_ (by omega) hk1 hfwd
                exact ⟨hi', hj', hsety ▸ hk', hlen.trans hsety,
                  Nat.le_trans (Nat.le_refl _) hloi,
                  Nat.le_trans (by omega) hloj⟩
      · simp only [mergeRunsMainFwd, dite_eq_left hI,
          dite_eq_right hJ] at hfwd
        simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hfwd
        exact ⟨hi_, hj_, hk, rfl, Nat.le_refl _, Nat.le_refl _⟩
    · simp only [mergeRunsMainFwd, dite_eq_right hI] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hfwd
      exact ⟨hi_, hj_, hk, rfl, Nat.le_refl _, Nat.le_refl _⟩

/-- Drain-`i` model bounds. -/
theorem mergeRunsDrainIFwd_le (la : List (BitVec 32))
    (F' i k mid : Nat)
    (lt : List (BitVec 32)) (i' k' : Nat) (lt' : List (BitVec 32))
    (hi_ : i ≤ mid) (hk : k ≤ lt.length)
    (hfwd : mergeRunsDrainIFwd la lt F' i k mid = .ok (i', k', lt')) :
    i' ≤ mid ∧ k' ≤ lt.length ∧ lt'.length = lt.length ∧ i ≤ i' := by
  induction F' generalizing lt i k mid i' k' lt' with
  | zero =>
    simp only [mergeRunsDrainIFwd, Except.ok.injEq, Prod.mk.injEq] at hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hfwd
    exact ⟨hi_, hk, rfl, Nat.le_refl _⟩
  | succ F' ih =>
    by_cases hI : i < mid
    · cases hK : lt[k]? with
      | none =>
        simp only [mergeRunsDrainIFwd, dite_eq_left hI, hK] at hfwd
        cases hfwd
      | some w =>
        have hklen : k < lt.length :=
          list_lt_of_getElem?_some lt k w hK
        cases hAi : la[i]? with
        | none =>
          simp only [mergeRunsDrainIFwd, dite_eq_left hI, hK,
            hAi] at hfwd
          cases hfwd
        | some x =>
          simp only [mergeRunsDrainIFwd, dite_eq_left hI, hK,
            hAi] at hfwd
          have hset : (lt.set k x).length = lt.length :=
            List.length_set
          have hk1 : k + 1 ≤ (lt.set k x).length := by
            rw [hset]; omega
          obtain ⟨hi', hk', hlen, hloi⟩ :=
            ih _ _ _ _ _ _ _ (by omega) hk1 hfwd
          exact ⟨hi', hset ▸ hk', hlen.trans hset,
            Nat.le_trans (by omega) hloi⟩
    · simp only [mergeRunsDrainIFwd, dite_eq_right hI] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hfwd
      exact ⟨hi_, hk, rfl, Nat.le_refl _⟩

/-- Drain-`j` model bounds. -/
theorem mergeRunsDrainJFwd_le (la : List (BitVec 32))
    (F' j k hi : Nat)
    (lt : List (BitVec 32)) (j' k' : Nat) (lt' : List (BitVec 32))
    (hj_ : j ≤ hi) (hk : k ≤ lt.length)
    (hfwd : mergeRunsDrainJFwd la lt F' j k hi = .ok (j', k', lt')) :
    j' ≤ hi ∧ k' ≤ lt.length ∧ lt'.length = lt.length ∧ j ≤ j' := by
  induction F' generalizing lt j k hi j' k' lt' with
  | zero =>
    simp only [mergeRunsDrainJFwd, Except.ok.injEq, Prod.mk.injEq] at hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hfwd
    exact ⟨hj_, hk, rfl, Nat.le_refl _⟩
  | succ F' ih =>
    by_cases hJ : j < hi
    · cases hK : lt[k]? with
      | none =>
        simp only [mergeRunsDrainJFwd, dite_eq_left hJ, hK] at hfwd
        cases hfwd
      | some w =>
        have hklen : k < lt.length :=
          list_lt_of_getElem?_some lt k w hK
        cases hAj : la[j]? with
        | none =>
          simp only [mergeRunsDrainJFwd, dite_eq_left hJ, hK,
            hAj] at hfwd
          cases hfwd
        | some x =>
          simp only [mergeRunsDrainJFwd, dite_eq_left hJ, hK,
            hAj] at hfwd
          have hset : (lt.set k x).length = lt.length :=
            List.length_set
          have hk1 : k + 1 ≤ (lt.set k x).length := by
            rw [hset]; omega
          obtain ⟨hj', hk', hlen, hloj⟩ :=
            ih _ _ _ _ _ _ _ (by omega) hk1 hfwd
          exact ⟨hj', hset ▸ hk', hlen.trans hset,
            Nat.le_trans (by omega) hloj⟩
    · simp only [mergeRunsDrainJFwd, dite_eq_right hJ] at hfwd
      simp only [Except.ok.injEq, Prod.mk.injEq] at hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hfwd
      exact ⟨hj_, hk, rfl, Nat.le_refl _⟩

/-! ## Entry bridge (`emit_correct`) -/

/-- `emit_correct` for `merge_runs`: prelude binds `i←lo`,
    `j←mid`, `k←lo`, three sequential loops chained at one model
    fuel (`seq` reuses fuel), measure-exact model fuels throughout.
    The caller supplies the segment discipline (`lo ≤ mid ≤ hi`
    inside `a`, `tmp` covering `lo`). -/
theorem evalProgFunc_mergeRuns (prog : Prog) (F : Nat)
    (la lt : List (BitVec 32)) (lo mid hi : BitVec 64)
    (hlent : lt.length < 2 ^ 64)
    (hlo_mid : lo.toNat ≤ mid.toNat) (hmid_hi : mid.toNat ≤ hi.toNat)
    (hmid_le : mid.toNat ≤ la.length) (hhi_le : hi.toNat ≤ la.length)
    (hlo_lt : lo.toNat ≤ lt.length)
    (hF : ((mid.toNat - lo.toNat) + (hi.toNat - lo.toNat)) + 1 ≤ F) :
    evalProgFunc prog F mergeRunsFunc
      [.stdVecVal la, .stdVecVal lt, .u64 lo, .u64 mid, .u64 hi] =
      mergeRunsFwd la lt lo.toNat mid.toNat hi.toNat := by
  have hbind : bindArgs mergeRunsFunc.args
      [.stdVecVal la, .stdVecVal lt, .u64 lo, .u64 mid, .u64 hi] =
      some [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
        ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)] := rfl
  have hbody : mergeRunsFunc.body =
      (.seq (.let_ "i" (.u 64) (.var "lo"))
        (.seq (.let_ "j" (.u 64) (.var "mid"))
          (.seq (.let_ "k" (.u 64) (.var "lo"))
            (.seq mergeRunsMain
              (.seq mergeRunsDrainI
                (.seq mergeRunsDrainJ
                  (.return_ (.var "tmp")))))))) := rfl
  have hvar_lo : evalExpr (.var "lo")
      [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
        ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)] =
      .ok (.u64 lo) :=
    evalExpr_var_hit _ _ _ rfl
  have hlet_i : evalProgStmt prog F
      (.let_ "i" (.u 64) (.var "lo"))
      [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
        ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)] =
      .ok ([("i", .u64 lo), ("a", .stdVecVal la),
        ("tmp", .stdVecVal lt), ("lo", .u64 lo), ("mid", .u64 mid),
        ("hi", .u64 hi)], .fellThrough) := by
    simpa [evalProgStmt, envExtend] using
      (evalStmtFuel_let_ F _ _ _ _ _ hvar_lo)
  have hvar_mid : evalExpr (.var "mid")
      [("i", .u64 lo), ("a", .stdVecVal la), ("tmp", .stdVecVal lt),
        ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)] =
      .ok (.u64 mid) :=
    evalExpr_var_hit _ _ _ rfl
  have hlet_j : evalProgStmt prog F
      (.let_ "j" (.u 64) (.var "mid"))
      [("i", .u64 lo), ("a", .stdVecVal la), ("tmp", .stdVecVal lt),
        ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)] =
      .ok ([("j", .u64 mid), ("i", .u64 lo), ("a", .stdVecVal la),
        ("tmp", .stdVecVal lt), ("lo", .u64 lo), ("mid", .u64 mid),
        ("hi", .u64 hi)], .fellThrough) := by
    simpa [evalProgStmt, envExtend] using
      (evalStmtFuel_let_ F _ _ _ _ _ hvar_mid)
  have hvar_lo2 : evalExpr (.var "lo")
      [("j", .u64 mid), ("i", .u64 lo), ("a", .stdVecVal la),
        ("tmp", .stdVecVal lt), ("lo", .u64 lo), ("mid", .u64 mid),
        ("hi", .u64 hi)] =
      .ok (.u64 lo) :=
    evalExpr_var_hit _ _ _ rfl
  have hlet_k : evalProgStmt prog F
      (.let_ "k" (.u 64) (.var "lo"))
      [("j", .u64 mid), ("i", .u64 lo), ("a", .stdVecVal la),
        ("tmp", .stdVecVal lt), ("lo", .u64 lo), ("mid", .u64 mid),
        ("hi", .u64 hi)] =
      .ok ([("k", .u64 lo), ("j", .u64 mid), ("i", .u64 lo),
        ("a", .stdVecVal la), ("tmp", .stdVecVal lt),
        ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)],
        .fellThrough) := by
    have h := evalStmtFuel_let_ F "k" (.u 64) _ _ _ hvar_lo2
    simpa [evalProgStmt, envExtend] using h
  have henv : [("k", .u64 lo), ("j", .u64 mid), ("i", .u64 lo),
        ("a", .stdVecVal la), ("tmp", .stdVecVal lt),
        ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)] =
      mkRunsEnv la lt lo mid hi lo mid lo := rfl
  match hmain : mergeRunsMainFwd la lt
      ((mid.toNat - lo.toNat) + (hi.toNat - mid.toNat))
      lo.toNat mid.toNat lo.toNat mid.toNat hi.toNat with
  | .error e =>
    have hM := mergeRunsMain_err prog F la lt lo mid hi lo mid lo
      e hlent hmid_le hhi_le (by omega) (by simpa using hmain)
    have hfwd : mergeRunsFwd la lt lo.toNat mid.toNat hi.toNat =
        .error e := by
      simp [mergeRunsFwd, hmain]
    have hstmt : evalProgStmt prog F mergeRunsFunc.body
        [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
          ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)] =
        .error e := by
      rw [hbody,
        evalProgStmt_seq_fallthrough prog F _ _ _ _ hlet_i,
        evalProgStmt_seq_fallthrough prog F _ _ _ _ hlet_j,
        evalProgStmt_seq_fallthrough prog F _ _ _ _ hlet_k, henv,
        evalProgStmt_seq_err prog F _ _ _ _ hM]
    simp [evalProgFunc, hbind, hstmt, hfwd]
  | .ok (i₁, j₁, k₁, lt₁) =>
    obtain ⟨hi₁, hj₁, hk₁, hlen₁, hloi₁, hloj₁⟩ :=
      mergeRunsMainFwd_le la _ _ _ _ _ _ _ _ _ _ _
        hlo_mid hmid_hi hlo_lt hmain
    have hleno₁ : lt₁.length < 2 ^ 64 := by
      rw [hlen₁]; exact hlent
    have hk₁' : k₁ ≤ lt₁.length := by
      rw [hlen₁]; exact hk₁
    have ti₁ : (BitVec.ofNat 64 i₁).toNat = i₁ :=
      bv64_toNat_ofNat i₁ (Nat.lt_of_le_of_lt hi₁ (by omega))
    have tj₁ : (BitVec.ofNat 64 j₁).toNat = j₁ :=
      bv64_toNat_ofNat j₁ (Nat.lt_of_le_of_lt hj₁ (by omega))
    have tk₁ : (BitVec.ofNat 64 k₁).toNat = k₁ :=
      bv64_toNat_ofNat k₁ (Nat.lt_of_le_of_lt hk₁' hleno₁)
    have hM := mergeRunsMain_ok prog F la lt lo mid hi lo mid lo
      i₁ j₁ k₁ lt₁ hlent hmid_le hhi_le (by omega)
      (by simpa using hmain)
    match hdrainI : mergeRunsDrainIFwd la lt₁ (mid.toNat - i₁)
        i₁ k₁ mid.toNat with
    | .error e =>
      have hdrainI' : mergeRunsDrainIFwd la lt₁
          (mid.toNat - (BitVec.ofNat 64 i₁).toNat)
          (BitVec.ofNat 64 i₁).toNat (BitVec.ofNat 64 k₁).toNat
          mid.toNat = .error e := by
        rw [ti₁, tk₁]; exact hdrainI
      have hI := mergeRunsDrainI_err prog F la lt₁ lo mid hi
        (BitVec.ofNat 64 i₁) (BitVec.ofNat 64 j₁)
        (BitVec.ofNat 64 k₁) e hleno₁ hmid_le
        (by rw [ti₁]; omega) hdrainI'
      have hfwd : mergeRunsFwd la lt lo.toNat mid.toNat hi.toNat =
          .error e := by
        simp [mergeRunsFwd, hmain, hdrainI]
      have hstmt : evalProgStmt prog F mergeRunsFunc.body
          [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
            ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)] =
          .error e := by
        rw [hbody,
          evalProgStmt_seq_fallthrough prog F _ _ _ _ hlet_i,
          evalProgStmt_seq_fallthrough prog F _ _ _ _ hlet_j,
          evalProgStmt_seq_fallthrough prog F _ _ _ _ hlet_k, henv,
          evalProgStmt_seq_fallthrough prog F _ _ _ _ hM,
          evalProgStmt_seq_err prog F _ _ _ _ hI]
      simp [evalProgFunc, hbind, hstmt, hfwd]
    | .ok (i₂, k₂, lt₂) =>
      obtain ⟨hi₂, hk₂, hlen₂, hloi₂⟩ :=
        mergeRunsDrainIFwd_le la _ _ _ _ _ _ _ _ hi₁ hk₁' hdrainI
      have hdrainI' : mergeRunsDrainIFwd la lt₁
          (mid.toNat - (BitVec.ofNat 64 i₁).toNat)
          (BitVec.ofNat 64 i₁).toNat (BitVec.ofNat 64 k₁).toNat
          mid.toNat = .ok (i₂, k₂, lt₂) := by
        rw [ti₁, tk₁]; exact hdrainI
      have hleno₂ : lt₂.length < 2 ^ 64 := by
        rw [hlen₂, hlen₁]; exact hlent
      have hI := mergeRunsDrainI_ok prog F la lt₁ lo mid hi
        (BitVec.ofNat 64 i₁) (BitVec.ofNat 64 j₁)
        (BitVec.ofNat 64 k₁) i₂ k₂ lt₂ hleno₁ hmid_le
        (by rw [ti₁]; omega) hdrainI'
      have hk₂' : k₂ ≤ lt₂.length := by
        rw [hlen₂]; exact hk₂
      have tk₂ : (BitVec.ofNat 64 k₂).toNat = k₂ :=
        bv64_toNat_ofNat k₂ (Nat.lt_of_le_of_lt hk₂' hleno₂)
      match hdrainJ : mergeRunsDrainJFwd la lt₂ (hi.toNat - j₁)
          j₁ k₂ hi.toNat with
      | .error e =>
        have hdrainJ' : mergeRunsDrainJFwd la lt₂
            (hi.toNat - (BitVec.ofNat 64 j₁).toNat)
            (BitVec.ofNat 64 j₁).toNat (BitVec.ofNat 64 k₂).toNat
            hi.toNat = .error e := by
          rw [tj₁, tk₂]; exact hdrainJ
        have hJ := mergeRunsDrainJ_err prog F la lt₂ lo mid hi
          (BitVec.ofNat 64 i₂) (BitVec.ofNat 64 j₁)
          (BitVec.ofNat 64 k₂) e hleno₂ hhi_le
          (by rw [tj₁]; omega) hdrainJ'
        have hfwd : mergeRunsFwd la lt lo.toNat mid.toNat hi.toNat =
            .error e := by
          simp [mergeRunsFwd, hmain, hdrainI, hdrainJ]
        have hstmt : evalProgStmt prog F mergeRunsFunc.body
            [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
              ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)] =
              .error e := by
          rw [hbody,
            evalProgStmt_seq_fallthrough prog F _ _ _ _ hlet_i,
            evalProgStmt_seq_fallthrough prog F _ _ _ _ hlet_j,
            evalProgStmt_seq_fallthrough prog F _ _ _ _ hlet_k, henv,
            evalProgStmt_seq_fallthrough prog F _ _ _ _ hM,
            evalProgStmt_seq_fallthrough prog F _ _ _ _ hI,
            evalProgStmt_seq_err prog F _ _ _ _ hJ]
        simp [evalProgFunc, hbind, hstmt, hfwd]
      | .ok (j₃, k₃, lt₃) =>
        obtain ⟨hj₃, hk₃, hlen₃, hloj₃⟩ :=
          mergeRunsDrainJFwd_le la _ _ _ _ _ _ _ _ hj₁ hk₂' hdrainJ
        have hdrainJ' : mergeRunsDrainJFwd la lt₂
            (hi.toNat - (BitVec.ofNat 64 j₁).toNat)
            (BitVec.ofNat 64 j₁).toNat (BitVec.ofNat 64 k₂).toNat
            hi.toNat = .ok (j₃, k₃, lt₃) := by
          rw [tj₁, tk₂]; exact hdrainJ
        have hleno₃ : lt₃.length < 2 ^ 64 := by
          rw [hlen₃, hlen₂, hlen₁]; exact hlent
        have hJ := mergeRunsDrainJ_ok prog F la lt₂ lo mid hi
          (BitVec.ofNat 64 i₂) (BitVec.ofNat 64 j₁)
          (BitVec.ofNat 64 k₂) j₃ k₃ lt₃ hleno₂ hhi_le
          (by rw [tj₁]; omega) hdrainJ'
        have heout : evalExpr (.var "tmp")
            (mkRunsEnv la lt₃ lo mid hi (BitVec.ofNat 64 i₂)
              (BitVec.ofNat 64 j₃) (BitVec.ofNat 64 k₃)) =
            .ok (.stdVecVal lt₃) :=
          evalExpr_var_hit _ _ _
            (mkRunsEnv_tmp _ _ _ _ _ _ _ _)
        have hret : evalProgStmt prog F (.return_ (.var "tmp"))
            (mkRunsEnv la lt₃ lo mid hi (BitVec.ofNat 64 i₂)
              (BitVec.ofNat 64 j₃) (BitVec.ofNat 64 k₃)) =
            .ok (mkRunsEnv la lt₃ lo mid hi (BitVec.ofNat 64 i₂)
              (BitVec.ofNat 64 j₃) (BitVec.ofNat 64 k₃),
              .returned (.stdVecVal lt₃)) :=
          evalProgStmt_return prog F _ _ _ heout
        have hfwd : mergeRunsFwd la lt lo.toNat mid.toNat hi.toNat =
            .ok (.stdVecVal lt₃) := by
          simp [mergeRunsFwd, hmain, hdrainI, hdrainJ]
        have hstmt : evalProgStmt prog F mergeRunsFunc.body
            [("a", .stdVecVal la), ("tmp", .stdVecVal lt),
              ("lo", .u64 lo), ("mid", .u64 mid), ("hi", .u64 hi)] =
            .ok (mkRunsEnv la lt₃ lo mid hi (BitVec.ofNat 64 i₂)
              (BitVec.ofNat 64 j₃) (BitVec.ofNat 64 k₃),
              .returned (.stdVecVal lt₃)) := by
          rw [hbody,
            evalProgStmt_seq_fallthrough prog F _ _ _ _ hlet_i,
            evalProgStmt_seq_fallthrough prog F _ _ _ _ hlet_j,
            evalProgStmt_seq_fallthrough prog F _ _ _ _ hlet_k, henv,
            evalProgStmt_seq_fallthrough prog F _ _ _ _ hM,
            evalProgStmt_seq_fallthrough prog F _ _ _ _ hI,
            evalProgStmt_seq_fallthrough prog F _ _ _ _ hJ]
          exact hret
        simp [evalProgFunc, hbind, hstmt, hfwd]

/-! ## Result-shape lemmas (entry support) -/

/-- A successful callee run returns `tmp` words (never a scalar). -/
theorem mergeRunsFwd_ok_shape (la lt : List (BitVec 32))
    (lo mid hi : Nat) (v : Value)
    (h : mergeRunsFwd la lt lo mid hi = .ok v) :
    ∃ lt', v = .stdVecVal lt' := by
  simp only [mergeRunsFwd] at h
  match h1 : mergeRunsMainFwd la lt ((mid - lo) + (hi - mid))
      lo mid lo mid hi with
  | .error e => simp [h1] at h
  | .ok (i, j, k, lt') =>
    simp only [h1] at h
    match h2 : mergeRunsDrainIFwd la lt' (mid - i) i k mid with
    | .error e => simp [h2] at h
    | .ok (i₂, k₂, lt'') =>
      simp only [h2] at h
      match h3 : mergeRunsDrainJFwd la lt'' (hi - j) j k₂ hi with
      | .error e => simp [h3] at h
      | .ok (_, _, lt''') =>
        simp only [h3, Except.ok.injEq] at h
        exact ⟨lt''', h.symm⟩

/-- A successful callee run preserves `tmp` length (sets only). -/
theorem mergeRunsFwd_length (la lt : List (BitVec 32))
    (lo mid hi : Nat) (lt' : List (BitVec 32))
    (hlo_mid : lo ≤ mid) (hmid_hi : mid ≤ hi)
    (hlo_lt : lo ≤ lt.length)
    (h : mergeRunsFwd la lt lo mid hi = .ok (.stdVecVal lt')) :
    lt'.length = lt.length := by
  simp only [mergeRunsFwd] at h
  match h1 : mergeRunsMainFwd la lt ((mid - lo) + (hi - mid))
      lo mid lo mid hi with
  | .error e => simp [h1] at h
  | .ok (i, j, k, lt') =>
    simp only [h1] at h
    obtain ⟨hi₁', hj₁', hk₁', hlen₁, _, _⟩ :=
      mergeRunsMainFwd_le la _ _ _ _ _ _ _ _ _ _ _
        hlo_mid hmid_hi hlo_lt h1
    match h2 : mergeRunsDrainIFwd la lt' (mid - i) i k mid with
    | .error e => simp [h2] at h
    | .ok (_, k₂, lt₂) =>
      simp only [h2] at h
      have hk₁'' : k ≤ lt'.length := by rwa [hlen₁]
      obtain ⟨_, hk₂', hlen₂, _⟩ :=
        mergeRunsDrainIFwd_le la _ _ _ _ lt' _ _ _
          hi₁' hk₁'' h2
      match h3 : mergeRunsDrainJFwd la lt₂ (hi - j) j k₂ hi with
      | .error e => simp [h3] at h
      | .ok (_, _, lt₃) =>
        simp only [h3, Except.ok.injEq] at h
        cases h
        have hk₂'' : k₂ ≤ lt₂.length := by rwa [hlen₂]
        obtain ⟨_, _, hlen₃, _⟩ :=
          mergeRunsDrainJFwd_le la _ _ _ _ lt₂ _ _ _
            hj₁' hk₂'' h3
        exact hlen₃.trans (hlen₂.trans hlen₁)

end VecMergeRuns
