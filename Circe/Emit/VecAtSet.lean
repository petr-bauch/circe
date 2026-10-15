/-
W single borrowed write over `std::vector<int>` (checked `at()` store).

Corpus: `tests/cpp/vec_at_set.cpp` → `tests/cir/vec_at_set.cir` (entry
`_Z10vec_at_setRSt6vectorIiSaIiEEmi`: mutable-borrow vector + `u64`
index + `i32` value in, `void` out; straight-line: three allocas,
`at()` call, store through the result, void return — the range check
lives inside the non-const `at()` leaf).

Model (the `vecAt` fusion precedent): the raw `at()` call fuses into
the guard + the borrowed store — `if i < len then vecSet else fail`,
returning the updated words by `var` (the `xor_n` out-param idiom).
The store itself is the new `CStmt.vecSet` (borrowed `stdVecVal`
in-env `List.set`, loud `OOB`, mirroring `arrSet` — deliberately
distinct from the entry-level `AssertFail`, and from `vgrowSet`,
which stays owned-triple-only).
-/
import Circe.Emit.VecAt

/-- Function name (Itanium mangling of a `vec_at_set` free function
taking `vector<int>&` + `unsigned long` + `int`, returning `void`). -/
def vecAtSetName : String := "_Z10vec_at_setRSt6vectorIiSaIiEEmi"

/-- Non-const `operator[]` leaf name (mutable twin of
    `stdVecIndexName`; identical fusion, admitted by the existing
    `isStdVecIndexShape`). -/
def stdVecIndexMutName : String := "_ZNSt6vectorIiSaIiEEixEm"

/-- Non-const `at()` leaf name (mutable twin of `stdVecAtName`; same
    `_M_range_check` + `operator[]` fusion over the mutable index
    leaf, admitted by the new `isStdVecAtMutShape`). -/
def stdVecAtMutName : String := "_ZNSt6vectorIiSaIiEE2atEm"

/-- Whole function: guard fused with the borrowed store, miss aborts,
    hit returns the updated words. -/
def vecAtSetFunc : Func :=
  ⟨vecAtSetName,
   [{ name := "v", ty := stdVecObjTy, role := .mutBorrow 0 },
    { name := "i", ty := .u 64, role := .owned },
    { name := "x", ty := .i 32, role := .owned }],
   stdVecObjTy,
   (.if_ (.ult (.var "i") (.stdVecLen "v"))
     (.seq (.vecSet "v" (.var "i") (.var "x"))
       (.return_ (.var "v")))
     .fail)⟩

/-- Loop environment (`u64` index, `i32` value, borrowed words). -/
def mkAtSetEnv (l : List (BitVec 32)) (n : BitVec 64)
    (x : BitVec 32) : Env :=
  [("v", .stdVecVal l), ("i", .u64 n), ("x", .i32 x)]

theorem mkAtSetEnv_v (l : List (BitVec 32)) (n : BitVec 64)
    (x : BitVec 32) :
    envLookup (mkAtSetEnv l n x) "v" = some (.stdVecVal l) := by
  simp [mkAtSetEnv, envLookup]

theorem mkAtSetEnv_i (l : List (BitVec 32)) (n : BitVec 64)
    (x : BitVec 32) :
    envLookup (mkAtSetEnv l n x) "i" = some (.u64 n) := by
  simp [mkAtSetEnv, envLookup, show ("i" : String) ≠ "v" by decide]

theorem mkAtSetEnv_x (l : List (BitVec 32)) (n : BitVec 64)
    (x : BitVec 32) :
    envLookup (mkAtSetEnv l n x) "x" = some (.i32 x) := by
  simp [mkAtSetEnv, envLookup, show ("x" : String) ≠ "v" by decide,
    show ("x" : String) ≠ "i" by decide]

/-- Value-level forward: `List.set` on hit, loud `AssertFail` past
    the end (the `vec_at_one` empty-read precedent). -/
def vecAtSetFwd (l : List (BitVec 32)) (n : BitVec 64)
    (x : BitVec 32) : Result Value :=
  match l[n.toNat]? with
  | some _ => .ok (.stdVecVal (l.set n.toNat x))
  | none => .error .AssertFail

theorem vecAtSetFwd_ok (l : List (BitVec 32)) (n : BitVec 64)
    (x : BitVec 32) (w : BitVec 32)
    (hget : l[n.toNat]? = some w) :
    vecAtSetFwd l n x = .ok (.stdVecVal (l.set n.toNat x)) := by
  simp [vecAtSetFwd, hget]

theorem vecAtSetFwd_fail (l : List (BitVec 32)) (n : BitVec 64)
    (x : BitVec 32)
    (hget : l[n.toNat]? = none) :
    vecAtSetFwd l n x = .error .AssertFail := by
  simp [vecAtSetFwd, hget]

/-- The guard reads the index against the reified length. -/
theorem vecAtSetGuard_eval (l : List (BitVec 32)) (n : BitVec 64)
    (x : BitVec 32) (hlen64 : l.length < 2 ^ 64) :
    evalExpr (.ult (.var "i") (.stdVecLen "v"))
      (mkAtSetEnv l n x) = .ok (.b (decide (n.toNat < l.length))) := by
  have hv := mkAtSetEnv_v l n x
  have hi := mkAtSetEnv_i l n x
  have hsize : evalExpr (.stdVecLen "v")
      (mkAtSetEnv l n x) =
      .ok (.u64 (BitVec.ofNat 64 l.length)) :=
    evalExpr_stdVecLen_some "v" _ l hv
  have hnv : evalExpr (.var "i") (mkAtSetEnv l n x) =
      .ok (.u64 n) :=
    evalExpr_var_hit _ _ _ hi
  have hult := evalExpr_ult_u64 _ _ _ _ _ hnv hsize
  rw [ult_ofNat64_len n l.length hlen64] at hult
  exact hult

/-! ## Body steps (loop-free, hit + miss) -/

/-- Hit step: guard holds, the store updates the words, the updated
    words return. -/
theorem vecAtSetBody_hit (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64) (x : BitVec 32)
    (hlen64 : l.length < 2 ^ 64) (w : BitVec 32)
    (hlt : n.toNat < l.length)
    (hget : l[n.toNat]? = some w) :
    evalStmtFuel F vecAtSetFunc.body (mkAtSetEnv l n x) =
      .ok ([("v", .stdVecVal (l.set n.toNat x)), ("i", .u64 n),
        ("x", .i32 x)],
        .returned (.stdVecVal (l.set n.toNat x))) := by
  have hbody : vecAtSetFunc.body =
      (.if_ (.ult (.var "i") (.stdVecLen "v"))
        (.seq (.vecSet "v" (.var "i") (.var "x"))
          (.return_ (.var "v")))
        .fail) := rfl
  have hc : evalExpr (.ult (.var "i") (.stdVecLen "v"))
      (mkAtSetEnv l n x) = .ok (.b true) := by
    have h := vecAtSetGuard_eval l n x hlen64
    simpa [hlt] using h
  have hi : evalExpr (.var "i") (mkAtSetEnv l n x) = .ok (.u64 n) :=
    evalExpr_var_hit _ _ _ (mkAtSetEnv_i l n x)
  have hx : evalExpr (.var "x") (mkAtSetEnv l n x) = .ok (.i32 x) :=
    evalExpr_var_hit _ _ _ (mkAtSetEnv_x l n x)
  have hu : envUpdate (mkAtSetEnv l n x) "v"
      (.stdVecVal (l.set n.toNat x)) =
      some [("v", .stdVecVal (l.set n.toNat x)), ("i", .u64 n),
        ("x", .i32 x)] := rfl
  have hset := evalStmtFuel_vecSet F "v" (.var "i") (.var "x")
    (mkAtSetEnv l n x) n x l w _ hi hx (mkAtSetEnv_v l n x) hget hu
  have hret : evalStmtFuel F (.return_ (.var "v"))
      [("v", .stdVecVal (l.set n.toNat x)), ("i", .u64 n),
        ("x", .i32 x)] =
      .ok ([("v", .stdVecVal (l.set n.toNat x)), ("i", .u64 n),
        ("x", .i32 x)],
        .returned (.stdVecVal (l.set n.toNat x))) :=
    evalStmtFuel_return F _ _ _
      (evalExpr_var_hit _ _ _ (by simp [envLookup]))
  have hseq := evalStmtFuel_seq_fallthrough F _
    (.return_ (.var "v")) _ _ hset
  rw [hbody]
  exact ((evalStmtFuel_if_true F _ _ _ _ hc).trans hseq).trans hret

/-- Miss step: past the end aborts loudly. -/
theorem vecAtSetBody_miss (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64) (x : BitVec 32)
    (hlen64 : l.length < 2 ^ 64)
    (hlt : ¬ n.toNat < l.length) :
    evalStmtFuel F vecAtSetFunc.body (mkAtSetEnv l n x) =
      .error .AssertFail := by
  have hbody : vecAtSetFunc.body =
      (.if_ (.ult (.var "i") (.stdVecLen "v"))
        (.seq (.vecSet "v" (.var "i") (.var "x"))
          (.return_ (.var "v")))
        .fail) := rfl
  have hc : evalExpr (.ult (.var "i") (.stdVecLen "v"))
      (mkAtSetEnv l n x) = .ok (.b false) := by
    have h := vecAtSetGuard_eval l n x hlen64
    simpa [hlt] using h
  rw [hbody]
  exact (evalStmtFuel_if_false F _ _ _ _ hc).trans
    (evalStmtFuel_fail F _)

/-- `emit_correct` for `vec_at_set` (all inputs, hit and abort;
    loop-free, any fuel). -/
theorem evalFuncFuel_vecAtSet (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64) (x : BitVec 32)
    (hlen64 : l.length < 2 ^ 64) :
    evalFuncFuel F vecAtSetFunc [.stdVecVal l, .u64 n, .i32 x] =
      vecAtSetFwd l n x := by
  have hbind : bindArgs vecAtSetFunc.args [.stdVecVal l, .u64 n, .i32 x] =
      some (mkAtSetEnv l n x) := rfl
  by_cases h : n.toNat < l.length
  · have hget : l[n.toNat]? = some l[n.toNat] :=
      List.getElem?_eq_getElem h
    have hfwd : vecAtSetFwd l n x =
        .ok (.stdVecVal (l.set n.toNat x)) :=
      vecAtSetFwd_ok l n x _ hget
    have hstmt := vecAtSetBody_hit F l n x hlen64 _ h hget
    simp [evalFuncFuel, hbind, hstmt, hfwd]
  · have hget : l[n.toNat]? = none :=
      List.getElem?_eq_none (Nat.le_of_not_gt h)
    have hfwd : vecAtSetFwd l n x = .error .AssertFail :=
      vecAtSetFwd_fail l n x hget
    have hstmt := vecAtSetBody_miss F l n x hlen64 h
    simp [evalFuncFuel, hbind, hstmt, hfwd]
