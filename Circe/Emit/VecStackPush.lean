/-
Circe.Emit.VecStackPush — G3 cursor-stack push kernel: the
`stack_push` entry over the N4d-iv-c mut-`at()` composer.

The corpus (`tests/cpp/stack_push.cpp`: `vector<int>&` workspace,
`u64` cursor, `i32` value, `u64` out) captures the entry + the
mut-`at()` composer + `_M_range_check` + `operator[]` + `size`.
The entry functionalizes to the fused `at()` guard (the
`vec_at_one` miss precedent: `AssertFail`) over the guarded
workspace store, returning the workspace itself — the
`vec_at_set` threading precedent (the proof skeleton here mirrors
`vecAtSetBody_hit` / `vecAtSetBody_miss` exactly). The C++
`return top + 1` is pure wrapping `u64` `uadd` (no model needed):
the emitted forward returns the `(workspace, cursor)` pair, the
spec edges pin both components, and the Diff asserts the cursor
against native directly. The loan story is the G1 `vecSet`
precedent (in-env update, no heap identity); the live arithmetic
is wrapping (no `nsw` anywhere).
-/
import Circe.Emit.VecAtSet

/-! ## G3: `stack_push` entry -/

/-- Mangled name of the push-kernel entry. -/
def stackPushName : String :=
  "_Z10stack_pushRSt6vectorIiSaIiEEmi"

/-- Canonical CoreIR for `stack_push`: the fused guard, the
    workspace store, and the workspace return (threaded state, the
    `vec_at_set` precedent — the cursor advance is pure `uadd`). -/
def stackPushFunc : Func :=
  ⟨stackPushName,
   [{ name := "st", ty := stdVecObjTy, role := .mutBorrow 0 },
    { name := "top", ty := .u 64, role := .owned },
    { name := "x", ty := .i 32, role := .owned }],
   stdVecObjTy,
   (.if_ (.ult (.var "top") (.stdVecLen "st"))
     (.seq (.vecSet "st" (.var "top") (.var "x"))
       (.return_ (.var "st")))
     .fail)⟩

/-- Push environment: borrowed words + `u64` cursor + `i32` value. -/
def mkStackEnv (l : List (BitVec 32)) (top : BitVec 64)
    (x : BitVec 32) : Env :=
  [("st", .stdVecVal l), ("top", .u64 top), ("x", .i32 x)]

theorem mkStackEnv_st (l : List (BitVec 32)) (top : BitVec 64)
    (x : BitVec 32) :
    envLookup (mkStackEnv l top x) "st" = some (.stdVecVal l) := by
  simp [mkStackEnv, envLookup]

theorem mkStackEnv_top (l : List (BitVec 32)) (top : BitVec 64)
    (x : BitVec 32) :
    envLookup (mkStackEnv l top x) "top" = some (.u64 top) := by
  simp [mkStackEnv, envLookup, show ("top" : String) ≠ "st" by decide]

theorem mkStackEnv_x (l : List (BitVec 32)) (top : BitVec 64)
    (x : BitVec 32) :
    envLookup (mkStackEnv l top x) "x" = some (.i32 x) := by
  simp [mkStackEnv, envLookup, show ("x" : String) ≠ "st" by decide,
    show ("x" : String) ≠ "top" by decide]

/-- Value-level forward: `List.set` on hit, loud `AssertFail` past
    the end (the `vec_at_one` empty-read precedent). -/
def stackPushFwd (l : List (BitVec 32)) (top : BitVec 64)
    (x : BitVec 32) : Result Value :=
  match l[top.toNat]? with
  | some _ => .ok (.stdVecVal (l.set top.toNat x))
  | none => .error .AssertFail

theorem stackPushFwd_ok (l : List (BitVec 32)) (top : BitVec 64)
    (x : BitVec 32) (w : BitVec 32)
    (h : l[top.toNat]? = some w) :
    stackPushFwd l top x = .ok (.stdVecVal (l.set top.toNat x)) := by
  simp [stackPushFwd, h]

theorem stackPushFwd_err (l : List (BitVec 32)) (top : BitVec 64)
    (x : BitVec 32) (h : l[top.toNat]? = none) :
    stackPushFwd l top x = .error .AssertFail := by
  simp [stackPushFwd, h]

/-- The cursor guard reads the cursor against the length. -/
theorem stackPushGuard_eval (l : List (BitVec 32)) (top : BitVec 64)
    (x : BitVec 32) (hlen64 : l.length < 2 ^ 64) :
    evalExpr (.ult (.var "top") (.stdVecLen "st"))
      (mkStackEnv l top x) =
      .ok (.b (decide (top.toNat < l.length))) := by
  have hst := mkStackEnv_st l top x
  have htop : evalExpr (.var "top") (mkStackEnv l top x) =
      .ok (.u64 top) :=
    evalExpr_var_hit _ _ _ (mkStackEnv_top l top x)
  have hlen : evalExpr (.stdVecLen "st") (mkStackEnv l top x) =
      .ok (.u64 (BitVec.ofNat 64 l.length)) :=
    evalExpr_stdVecLen_some "st" _ l hst
  have h := evalExpr_ult_u64 _ _ _ _ _ htop hlen
  rw [BitVec.ult_eq_decide, ofNat64_toNat l.length hlen64] at h
  exact h

/-- Hit step: the guarded store threads the workspace through. -/
theorem stackPushBody_hit (F : Nat) (l : List (BitVec 32))
    (top : BitVec 64) (x : BitVec 32)
    (hlen64 : l.length < 2 ^ 64)
    (hlt : top.toNat < l.length) :
    evalStmtFuel F stackPushFunc.body (mkStackEnv l top x) =
      .ok ([("st", .stdVecVal (l.set top.toNat x)),
        ("top", .u64 top), ("x", .i32 x)],
        .returned (.stdVecVal (l.set top.toNat x))) := by
  have hbody : stackPushFunc.body =
      (.if_ (.ult (.var "top") (.stdVecLen "st"))
        (.seq (.vecSet "st" (.var "top") (.var "x"))
          (.return_ (.var "st")))
        .fail) := rfl
  have hne : l[top.toNat]? ≠ none := by
    rw [ne_eq, List.getElem?_eq_none_iff]
    omega
  obtain ⟨w, hget⟩ := Option.ne_none_iff_exists.mp hne
  have hget : l[top.toNat]? = some w := hget.symm
  have hc : evalExpr (.ult (.var "top") (.stdVecLen "st"))
      (mkStackEnv l top x) = .ok (.b true) := by
    have h := stackPushGuard_eval l top x hlen64
    simpa [hlt] using h
  have htop : evalExpr (.var "top") (mkStackEnv l top x) =
      .ok (.u64 top) :=
    evalExpr_var_hit _ _ _ (mkStackEnv_top l top x)
  have hx : evalExpr (.var "x") (mkStackEnv l top x) =
      .ok (.i32 x) :=
    evalExpr_var_hit _ _ _ (mkStackEnv_x l top x)
  have hu : envUpdate (mkStackEnv l top x) "st"
      (.stdVecVal (l.set top.toNat x)) =
      some [("st", .stdVecVal (l.set top.toNat x)),
        ("top", .u64 top), ("x", .i32 x)] := rfl
  have hset := evalStmtFuel_vecSet F "st" (.var "top") (.var "x")
    (mkStackEnv l top x) top x l w _
    htop hx (mkStackEnv_st l top x) hget hu
  have hret : evalStmtFuel F (.return_ (.var "st"))
      [("st", .stdVecVal (l.set top.toNat x)),
        ("top", .u64 top), ("x", .i32 x)] =
      .ok ([("st", .stdVecVal (l.set top.toNat x)),
        ("top", .u64 top), ("x", .i32 x)],
        .returned (.stdVecVal (l.set top.toNat x))) :=
    evalStmtFuel_return F _ _ _
      (evalExpr_var_hit _ _ _ (by simp [envLookup]))
  have hseq := evalStmtFuel_seq_fallthrough F _ (.return_ (.var "st")) _ _ hset
  rw [hbody]
  exact ((evalStmtFuel_if_true F _ _ _ _ hc).trans hseq).trans hret

/-- Miss step: past the end aborts loudly. -/
theorem stackPushBody_miss (F : Nat) (l : List (BitVec 32))
    (top : BitVec 64) (x : BitVec 32)
    (hlen64 : l.length < 2 ^ 64)
    (hlt : ¬ top.toNat < l.length) :
    evalStmtFuel F stackPushFunc.body (mkStackEnv l top x) =
      .error .AssertFail := by
  have hbody : stackPushFunc.body =
      (.if_ (.ult (.var "top") (.stdVecLen "st"))
        (.seq (.vecSet "st" (.var "top") (.var "x"))
          (.return_ (.var "st")))
        .fail) := rfl
  have hc : evalExpr (.ult (.var "top") (.stdVecLen "st"))
      (mkStackEnv l top x) = .ok (.b false) := by
    have h := stackPushGuard_eval l top x hlen64
    simpa [hlt] using h
  rw [hbody]
  exact (evalStmtFuel_if_false F _ _ _ _ hc).trans
    (evalStmtFuel_fail F _)

/-- Entry theorem: evaluation agrees with the forward (hit threads
    the workspace, miss takes the fused `fail`). -/
theorem evalFuncFuel_stackPush (F : Nat) (l : List (BitVec 32))
    (top : BitVec 64) (x : BitVec 32)
    (hlen64 : l.length < 2 ^ 64) :
    evalFuncFuel F stackPushFunc [.stdVecVal l, .u64 top, .i32 x] =
      stackPushFwd l top x := by
  have hbind : bindArgs stackPushFunc.args
      [.stdVecVal l, .u64 top, .i32 x] =
      some [("st", .stdVecVal l), ("top", .u64 top),
        ("x", .i32 x)] := rfl
  have henv : (mkStackEnv l top x) =
      [("st", .stdVecVal l), ("top", .u64 top),
        ("x", .i32 x)] := rfl
  by_cases h : top.toNat < l.length
  · have hne : l[top.toNat]? ≠ none := by
      rw [ne_eq, List.getElem?_eq_none_iff]
      omega
    obtain ⟨w, hget'⟩ := Option.ne_none_iff_exists.mp hne
    have hget : l[top.toNat]? = some w := hget'.symm
    have hfwd : stackPushFwd l top x =
        .ok (.stdVecVal (l.set top.toNat x)) :=
      stackPushFwd_ok l top x w hget
    have hstmt := stackPushBody_hit F l top x hlen64 h
    rw [henv] at hstmt
    simp [evalFuncFuel, hbind, hstmt, hfwd]
  · have hget : l[top.toNat]? = none := by
      rw [List.getElem?_eq_none_iff]
      omega
    have hfwd : stackPushFwd l top x = .error .AssertFail :=
      stackPushFwd_err l top x hget
    have hstmt := stackPushBody_miss F l top x hlen64 h
    rw [henv] at hstmt
    simp [evalFuncFuel, hbind, hstmt, hfwd]
