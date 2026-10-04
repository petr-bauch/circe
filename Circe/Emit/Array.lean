/-
Circe.Emit.Array — N4d-i `std::array<int32_t, 4>` reads: the
`__array_traits::_S_ref` unchecked-index leaf + `operator[]` + the
`array_sum` entry.

The C++ call chain is depth-2 (`array_sum` → `operator[]` → `_S_ref`)
but `evalProgStmt` dispatches callees via `evalFuncFuel`, which only
evaluates call-free bodies (the S1 DAG discipline — deeper
composition would make cycles expressible). So functionalization
fuses one edge, exactly like the M2b leaf fusions (`accGet` fuses
`get_member` + `load`): `arrayAtFunc` returns the `idxi` read
directly, and the `operator[]` → `_S_ref` edge is pinned textually
by the gate (`isArrayAtShape` admits exactly one call site to the
`_S_ref` name) plus nominally by the goldens. `_S_ref` still
validates separately to `arrayRefFunc` (same value story), so
misshapen variants of either def reject loudly.
-/
import Circe.Emit.Fragment

/-! ## N4d-i: `std::array` index leaf, `operator[]`, `array_sum` entry -/

/-- Mangled callee names in `tests/cpp/array_sum.cpp`. -/
def arrayRefName : String := "_ZNSt14__array_traitsIiLm4EE6_S_refERA4_Kim"
def arrayAtName : String := "_ZNKSt5arrayIiLm4EEixEm"
def arraySumName : String := "_Z9array_sumRKSt5arrayIiLm4EE"

/-- Canonical CoreIR for the `_S_ref` leaf: unchecked `u64` index into
    the 4-word `i32` array (`cir.get_element`, OOB is UB so the model
    reports `OOB`). -/
def arrayRefFunc : Func :=
  ⟨arrayRefName,
   [{ name := "t", ty := .array (.i 32) 4, role := .sharedBorrow },
    { name := "n", ty := .u 64, role := .owned }],
   .i 32,
   .return_ (.idxi "t" (.var "n"))⟩

/-- Canonical CoreIR for `operator[]`: the `_M_elems` projection +
    `_S_ref` call fused into the `idxi` read (cf. `accGetFunc`). -/
def arrayAtFunc : Func :=
  ⟨arrayAtName,
   [{ name := "a", ty := .array (.i 32) 4, role := .sharedBorrow },
    { name := "n", ty := .u 64, role := .owned }],
   .i 32,
   .return_ (.idxi "a" (.var "n"))⟩

/-- Canonical CoreIR for `array_sum`: four const-index reads through
    `operator[]` (`cir.const` indices functionalized as `let_`-bound
    words, since `callRet` args are environment names) with three
    left-associated `nsw` adds, matching the C++ evaluation order. -/
def arraySumFunc : Func :=
  ⟨arraySumName,
   [{ name := "a", ty := .array (.i 32) 4, role := .sharedBorrow }],
   .i 32,
   .seq (.let_ "i0" (.u 64) (.lit (.u64 0)))
   (.seq (.callRet "e0" arrayAtName ["a", "i0"])
   (.seq (.let_ "i1" (.u 64) (.lit (.u64 1)))
   (.seq (.callRet "e1" arrayAtName ["a", "i1"])
   (.seq (.let_ "i2" (.u 64) (.lit (.u64 2)))
   (.seq (.callRet "e2" arrayAtName ["a", "i2"])
   (.seq (.let_ "i3" (.u 64) (.lit (.u64 3)))
   (.seq (.callRet "e3" arrayAtName ["a", "i3"])
          (.return_ (.add (.add (.add (.var "e0") (.var "e1"))
            (.var "e2")) (.var "e3"))))))))))⟩

/-- Value-level forward for `_S_ref`: the word at `u64` index `n`,
    `OOB` off the end. -/
def arrayRefFwd (l : List (BitVec 32)) (n : BitVec 64) : Result Value :=
  match l[n.toNat]? with
  | some x => .ok (.i32 x)
  | none => .error .OOB

/-- Value-level forward for `operator[]`: the same read (the call edge
    is fused, so the forward is the leaf forward by definition). -/
def arrayAtFwd (l : List (BitVec 32)) (n : BitVec 64) : Result Value :=
  arrayRefFwd l n

theorem arrayAtFwd_is_call (l : List (BitVec 32)) (n : BitVec 64) :
    arrayAtFwd l n = arrayRefFwd l n := rfl

/-- Value-level forward for `array_sum`: three threaded `nsw` adds
    over the four words (cf. rendered `array_sum_fwd`). -/
def arraySumFwd (a b c d : BitVec 32) : Result Value :=
  match checkedAddI32 a b with
  | .error e => .error e
  | .ok t =>
    match checkedAddI32 t c with
    | .error e => .error e
    | .ok u => .i32 <$> checkedAddI32 u d

/-- Env facts for the `_S_ref` shape. -/
theorem envLookup_arrayRef_t (l : List (BitVec 32)) (n : BitVec 64) :
    envLookup [("t", .arr32 l), ("n", .u64 n)] "t" =
      some (.arr32 l) := by
  simp [envLookup]

theorem envLookup_arrayRef_n (l : List (BitVec 32)) (n : BitVec 64) :
    envLookup [("t", .arr32 l), ("n", .u64 n)] "n" =
      some (.u64 n) := by
  simp [envLookup, show ("n" : String) ≠ "t" by decide]

/-- `emit_correct` for `_S_ref` (all inputs, hit and `OOB` paths). -/
theorem evalFuncFuel_arrayRef (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64) :
    evalFuncFuel F arrayRefFunc [.arr32 l, .u64 n] =
      arrayRefFwd l n := by
  have hbind : bindArgs arrayRefFunc.args [.arr32 l, .u64 n] =
      some [("t", .arr32 l), ("n", .u64 n)] := rfl
  have hbody : arrayRefFunc.body =
      .return_ (.idxi "t" (.var "n")) := rfl
  have ht := envLookup_arrayRef_t l n
  have hn := envLookup_arrayRef_n l n
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, arrayRefFwd, ht, hn] <;>
    (cases h : l[n.toNat]? <;> simp [h])

/-- Env facts for the `operator[]` shape. -/
theorem envLookup_arrayAt_a (l : List (BitVec 32)) (n : BitVec 64) :
    envLookup [("a", .arr32 l), ("n", .u64 n)] "a" =
      some (.arr32 l) := by
  simp [envLookup]

theorem envLookup_arrayAt_n (l : List (BitVec 32)) (n : BitVec 64) :
    envLookup [("a", .arr32 l), ("n", .u64 n)] "n" =
      some (.u64 n) := by
  simp [envLookup, show ("n" : String) ≠ "a" by decide]

/-- `emit_correct` for `operator[]` (same read, fused call edge). -/
theorem evalFuncFuel_arrayAt (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64) :
    evalFuncFuel F arrayAtFunc [.arr32 l, .u64 n] =
      arrayAtFwd l n := by
  have hbind : bindArgs arrayAtFunc.args [.arr32 l, .u64 n] =
      some [("a", .arr32 l), ("n", .u64 n)] := rfl
  have hbody : arrayAtFunc.body =
      .return_ (.idxi "a" (.var "n")) := rfl
  have ha := envLookup_arrayAt_a l n
  have hn := envLookup_arrayAt_n l n
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, arrayAtFwd, arrayRefFwd, ha, hn] <;>
    (cases h : l[n.toNat]? <;> simp [h])

/-- `emit_correct` for `array_sum`: program evaluation over
    `[arrayAtFunc]` agrees with the threaded-add forward (the four
    const-index reads hit on a 4-word array; the adds branch
    ok/err over the three `nsw` sites). -/
theorem evalProgFunc_arraySum (F : Nat) (a b c d : BitVec 32) :
    evalProgFunc [arrayAtFunc] F arraySumFunc [.arr32 [a, b, c, d]] =
      arraySumFwd a b c d := by
  have hbind : bindArgs arraySumFunc.args [.arr32 [a, b, c, d]] =
      some [("a", .arr32 [a, b, c, d])] := rfl
  have hbody : arraySumFunc.body =
      .seq (.let_ "i0" (.u 64) (.lit (.u64 0)))
      (.seq (.callRet "e0" arrayAtName ["a", "i0"])
      (.seq (.let_ "i1" (.u 64) (.lit (.u64 1)))
      (.seq (.callRet "e1" arrayAtName ["a", "i1"])
      (.seq (.let_ "i2" (.u 64) (.lit (.u64 2)))
      (.seq (.callRet "e2" arrayAtName ["a", "i2"])
      (.seq (.let_ "i3" (.u 64) (.lit (.u64 3)))
      (.seq (.callRet "e3" arrayAtName ["a", "i3"])
             (.return_ (.add (.add (.add (.var "e0") (.var "e1"))
               (.var "e2")) (.var "e3")))))))))) := rfl
  have hfind : findFunc [arrayAtFunc] arrayAtName = some arrayAtFunc :=
    findFunc_hit arrayAtFunc []
  have hlet0 : evalProgStmt [arrayAtFunc] F
      (.let_ "i0" (.u 64) (.lit (.u64 0)))
      [("a", .arr32 [a, b, c, d])] =
      .ok ((envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)),
        .fellThrough) := by
    simp only [evalProgStmt]
    exact evalStmtFuel_let_ F "i0" (.u 64) _ _
      (.u64 (0 : BitVec 64)) (by simp [evalExpr, litVal])
  have hargs0 : lookupArgs (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0))
      ["a", "i0"] = some [.arr32 [a, b, c, d], .u64 0] := by
    simp [lookupArgs, envExtend, envLookup]
  have hcall0 : evalFuncFuel F arrayAtFunc
      [.arr32 [a, b, c, d], .u64 0] = .ok (.i32 a) := by
    rw [evalFuncFuel_arrayAt]
    rfl
  have hstep0 := evalProgStmt_callRet_ok [arrayAtFunc]
    F "e0" arrayAtName ["a", "i0"]
    (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0))
    [.arr32 [a, b, c, d], .u64 0] arrayAtFunc (.i32 a)
    hargs0 hfind hcall0
  have hlet1 : evalProgStmt [arrayAtFunc] F
      (.let_ "i1" (.u 64) (.lit (.u64 1)))
      (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) =
      .ok ((envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)),
        .fellThrough) := by
    simp only [evalProgStmt]
    exact evalStmtFuel_let_ F "i1" (.u 64) _ _
      (.u64 (1 : BitVec 64)) (by simp [evalExpr, litVal])
  have hargs1 : lookupArgs (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1))
      ["a", "i1"] = some [.arr32 [a, b, c, d], .u64 1] := by
    simp [lookupArgs, envExtend, envLookup]
  have hcall1 : evalFuncFuel F arrayAtFunc
      [.arr32 [a, b, c, d], .u64 1] = .ok (.i32 b) := by
    rw [evalFuncFuel_arrayAt]
    rfl
  have hstep1 := evalProgStmt_callRet_ok [arrayAtFunc]
    F "e1" arrayAtName ["a", "i1"]
    (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1))
    [.arr32 [a, b, c, d], .u64 1] arrayAtFunc (.i32 b)
    hargs1 hfind hcall1
  have hlet2 : evalProgStmt [arrayAtFunc] F
      (.let_ "i2" (.u 64) (.lit (.u64 2)))
      (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) =
      .ok ((envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)),
        .fellThrough) := by
    simp only [evalProgStmt]
    exact evalStmtFuel_let_ F "i2" (.u 64) _ _
      (.u64 (2 : BitVec 64)) (by simp [evalExpr, litVal])
  have hargs2 : lookupArgs (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2))
      ["a", "i2"] = some [.arr32 [a, b, c, d], .u64 2] := by
    simp [lookupArgs, envExtend, envLookup]
  have hcall2 : evalFuncFuel F arrayAtFunc
      [.arr32 [a, b, c, d], .u64 2] = .ok (.i32 c) := by
    rw [evalFuncFuel_arrayAt]
    rfl
  have hstep2 := evalProgStmt_callRet_ok [arrayAtFunc]
    F "e2" arrayAtName ["a", "i2"]
    (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2))
    [.arr32 [a, b, c, d], .u64 2] arrayAtFunc (.i32 c)
    hargs2 hfind hcall2
  have hlet3 : evalProgStmt [arrayAtFunc] F
      (.let_ "i3" (.u 64) (.lit (.u64 3)))
      (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) =
      .ok ((envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) "i3" (.u64 3)),
        .fellThrough) := by
    simp only [evalProgStmt]
    exact evalStmtFuel_let_ F "i3" (.u 64) _ _
      (.u64 (3 : BitVec 64)) (by simp [evalExpr, litVal])
  have hargs3 : lookupArgs (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) "i3" (.u64 3))
      ["a", "i3"] = some [.arr32 [a, b, c, d], .u64 3] := by
    simp [lookupArgs, envExtend, envLookup]
  have hcall3 : evalFuncFuel F arrayAtFunc
      [.arr32 [a, b, c, d], .u64 3] = .ok (.i32 d) := by
    rw [evalFuncFuel_arrayAt]
    rfl
  have hstep3 := evalProgStmt_callRet_ok [arrayAtFunc]
    F "e3" arrayAtName ["a", "i3"]
    (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) "i3" (.u64 3))
    [.arr32 [a, b, c, d], .u64 3] arrayAtFunc (.i32 d)
    hargs3 hfind hcall3
  cases h1 : checkedAddI32 a b with
  | error e =>
    have hexpr : evalExpr
        (.add (.add (.add (.var "e0") (.var "e1")) (.var "e2"))
          (.var "e3"))
        (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) "i3" (.u64 3)) "e3" (.i32 d)) = .error e := by
      simp [evalExpr, envExtend, envLookup, h1, Except.map]
    have hret : evalProgStmt [arrayAtFunc] F
        (.return_ (.add (.add (.add (.var "e0") (.var "e1"))
          (.var "e2")) (.var "e3")))
        (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) "i3" (.u64 3)) "e3" (.i32 d)) = .error e :=
      evalStmtFuel_return_err F _ _ e hexpr
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hlet0,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep0,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hlet1,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep1,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hlet2,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep2,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hlet3,
      evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep3, hret]
    simp [arraySumFwd, h1]
  | ok t =>
    cases h2 : checkedAddI32 t c with
    | error e =>
      have hexpr : evalExpr
          (.add (.add (.add (.var "e0") (.var "e1")) (.var "e2"))
            (.var "e3"))
          (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) "i3" (.u64 3)) "e3" (.i32 d)) = .error e := by
        simp [evalExpr, envExtend, envLookup, h1, h2, Except.map]
      have hret : evalProgStmt [arrayAtFunc] F
          (.return_ (.add (.add (.add (.var "e0") (.var "e1"))
            (.var "e2")) (.var "e3")))
          (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) "i3" (.u64 3)) "e3" (.i32 d)) = .error e :=
        evalStmtFuel_return_err F _ _ e hexpr
      simp only [evalProgFunc, hbind, hbody]
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hlet0,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep0,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hlet1,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep1,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hlet2,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep2,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hlet3,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep3, hret]
      simp [arraySumFwd, h1, h2]
    | ok u =>
      cases h3 : checkedAddI32 u d with
      | error e =>
        have hexpr : evalExpr
            (.add (.add (.add (.var "e0") (.var "e1")) (.var "e2"))
              (.var "e3"))
            (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) "i3" (.u64 3)) "e3" (.i32 d)) = .error e := by
          simp [evalExpr, envExtend, envLookup, h1, h2, h3, Except.map]
        have hret : evalProgStmt [arrayAtFunc] F
            (.return_ (.add (.add (.add (.var "e0") (.var "e1"))
              (.var "e2")) (.var "e3")))
            (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) "i3" (.u64 3)) "e3" (.i32 d)) = .error e :=
          evalStmtFuel_return_err F _ _ e hexpr
        simp only [evalProgFunc, hbind, hbody]
        rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hlet0,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep0,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hlet1,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep1,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hlet2,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep2,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hlet3,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep3, hret]
        simp [arraySumFwd, h1, h2, h3, i32_map_error]
      | ok r =>
        have hexpr : evalExpr
            (.add (.add (.add (.var "e0") (.var "e1")) (.var "e2"))
              (.var "e3"))
            (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) "i3" (.u64 3)) "e3" (.i32 d)) = .ok (.i32 r) := by
          simp [evalExpr, envExtend, envLookup, h1, h2, h3, Except.map]
        have hret : evalProgStmt [arrayAtFunc] F
            (.return_ (.add (.add (.add (.var "e0") (.var "e1"))
              (.var "e2")) (.var "e3")))
            (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) "i3" (.u64 3)) "e3" (.i32 d)) =
            .ok ((envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) "i3" (.u64 3)) "e3" (.i32 d)), .returned (.i32 r)) :=
          evalProgStmt_return [arrayAtFunc] F _ _
            (.i32 r) hexpr
        simp only [evalProgFunc, hbind, hbody]
        rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hlet0,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep0,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hlet1,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep1,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hlet2,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep2,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hlet3,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep3, hret]
        simp [arraySumFwd, h1, h2, h3, i32_map_ok]
