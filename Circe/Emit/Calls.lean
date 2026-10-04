/-
Circe.Emit.Calls — S1 DAG calls: `add_caller` (two `@add` sites) and
`sum_caller` (one `@sum_array` site), over the call-free leaves.
-/
import Circe.Emit.Fragment
import Circe.Emit.Add
import Circe.Emit.Sum

/-! ## S1: DAG calls (`add_caller`, `sum_caller`) -/


/-- Canonical CoreIR for `tests/c/add_caller.c`: two DAG calls into `add`
    (`t = add(x,y); return add(t,z)`). Both call sites target the
    call-free leaf `addFunc` (matched by name in `evalProgStmt`). -/
def addCallerFunc : Func :=
  ⟨"add_caller",
   [{ name := "x", ty := .i 32, role := .owned },
    { name := "y", ty := .i 32, role := .owned },
    { name := "z", ty := .i 32, role := .owned }],
   .i 32,
   .seq (.callRet "t" "add" ["x", "y"])
   (.seq (.callRet "r" "add" ["t", "z"])
         (.return_ (.var "r")))⟩

/-- Canonical CoreIR for `tests/c/sum_caller.c`: single DAG call
    delegating to `sum_array`. -/
def sumCallerFunc : Func :=
  ⟨"sum_caller",
   [{ name := "a", ty := .array (.u 32) 4096, role := .sharedBorrow },
    { name := "n", ty := .u 32, role := .owned }],
   .u 32,
   .seq (.callRet "s" "sum_array" ["a", "n"])
        (.return_ (.var "s"))⟩



/-- Value-level forward for `add_caller`: sequential `Result` binds over
    the leaf op (cf. rendered `add_caller_fwd`). -/
def addCallerFwd (x y z : BitVec 32) : Result Value :=
  match checkedAddI32 x y with
  | .error e => .error e
  | .ok t => .i32 <$> checkedAddI32 t z

/-- Bridge: leaf ok-path is the checked add (for `cir_simp` coverage of
    the `_as_calls` normal form; mirrors `accAddFwd_ok`). -/
theorem addFwd_ok (a b r : BitVec 32)
    (h : checkedAddI32 a b = .ok r) :
    addFwd a b = .ok (.i32 r) := by
  simp [addFwd, h, i32_map_ok]

/-- Bridge: leaf error-path propagates (mirrors `accAddFwd_err`). -/
theorem addFwd_err (a b : BitVec 32) (e : Panic)
    (h : checkedAddI32 a b = .error e) :
    addFwd a b = .error e := by
  simp [addFwd, h, i32_map_error]

/-- The forward is literally two `add_fwd` calls sequenced (call structure
    explicit; the second match arm is unreachable since `addFwd` only
    produces `i32` values). -/
theorem addCallerFwd_as_calls (x y z : BitVec 32) :
    addCallerFwd x y z =
      match addFwd x y with
      | .error e => .error e
      | .ok (.i32 t) => .i32 <$> checkedAddI32 t z
      | .ok _ => .error .AssertFail := by
  cases h : checkedAddI32 x y <;>
    simp [addCallerFwd, addFwd, h, i32_map_error, i32_map_ok]

/-- Value-level forward for `sum_caller`: direct delegation to `sumFwd`
    (cf. rendered `sum_caller_fwd`). -/
def sumCallerFwd (l : List (BitVec 32)) (n : BitVec 32) : Result Value :=
  sumFwd l n

theorem sumCallerFwd_is_call (l : List (BitVec 32)) (n : BitVec 32) :
    sumCallerFwd l n = sumFwd l n := rfl

/-! ## N4a: overload / namespace callers (`use_add`, `use_ns_add`) -/

/-- Canonical CoreIR for `tests/cpp/overload_add.cpp:use_add`: single
    DAG call resolving to the 2-`i32` overload (`_Z3addii`). The callee
    is the renamed `add` leaf (matched by mangled name in
    `evalProgStmt`). -/
def useAddFunc : Func :=
  ⟨"_Z7use_addii",
   [{ name := "x", ty := .i 32, role := .owned },
    { name := "y", ty := .i 32, role := .owned }],
   .i 32,
   .seq (.callRet "s" "_Z3addii" ["x", "y"])
        (.return_ (.var "s"))⟩

/-- Canonical CoreIR for `tests/cpp/ns_add.cpp:use_ns_add`: single DAG
    call resolving to the namespaced leaf (`_ZN2ns3addEii`). -/
def useNsAddFunc : Func :=
  ⟨"_Z10use_ns_addii",
   [{ name := "x", ty := .i 32, role := .owned },
    { name := "y", ty := .i 32, role := .owned }],
   .i 32,
   .seq (.callRet "s" "_ZN2ns3addEii" ["x", "y"])
        (.return_ (.var "s"))⟩

/-- Value-level forward for `use_add`: direct delegation to the `add`
    leaf forward (cf. rendered `_Z7use_addii_fwd`). -/
def useAddFwd (x y : BitVec 32) : Result Value :=
  addFwd x y

theorem useAddFwd_is_call (x y : BitVec 32) :
    useAddFwd x y = addFwd x y := rfl

/-- Value-level forward for `use_ns_add`: same delegation at the
    namespaced leaf. -/
def useNsAddFwd (x y : BitVec 32) : Result Value :=
  addFwd x y

theorem useNsAddFwd_is_call (x y : BitVec 32) :
    useNsAddFwd x y = addFwd x y := rfl

/-- Env facts for the overload-caller shape (shared by both entries). -/
theorem envLookup_useAddCaller_x (x y : BitVec 32) :
    envLookup [("x", .i32 x), ("y", .i32 y)] "x" = some (.i32 x) := by
  simp [envLookup]

theorem envLookup_useAddCaller_y (x y : BitVec 32) :
    envLookup [("x", .i32 x), ("y", .i32 y)] "y" = some (.i32 y) := by
  simp [envLookup, show ("y" : String) ≠ "x" by decide]

/-- `emit_correct` for `use_add`: program evaluation over the renamed
    `add` leaf agrees with the delegating forward (loop-free leaf, so
    no fuel side conditions). -/
theorem evalProgFunc_useAdd (F : Nat) (x y : BitVec 32) :
    evalProgFunc [{ addFunc with name := "_Z3addii" }] F useAddFunc
      [.i32 x, .i32 y] = useAddFwd x y := by
  have hbind : bindArgs useAddFunc.args [.i32 x, .i32 y] =
      some [("x", .i32 x), ("y", .i32 y)] := rfl
  have hbody : useAddFunc.body =
      .seq (.callRet "s" "_Z3addii" ["x", "y"])
           (.return_ (.var "s")) := rfl
  have hx := envLookup_useAddCaller_x x y
  have hy := envLookup_useAddCaller_y x y
  have hfind : findFunc [{ addFunc with name := "_Z3addii" }] "_Z3addii" =
      some { addFunc with name := "_Z3addii" } :=
    findFunc_hit { addFunc with name := "_Z3addii" } []
  have hargs : lookupArgs [("x", .i32 x), ("y", .i32 y)] ["x", "y"] =
      some [.i32 x, .i32 y] := by
    simp [lookupArgs, hx, hy]
  have hcall := evalFuncFuel_addAt F "_Z3addii" x y
  cases hadd : addFwd x y with
  | error e =>
    have hcall' : evalFuncFuel F { addFunc with name := "_Z3addii" }
        [.i32 x, .i32 y] = .error e := by
      rw [hcall, hadd]
    have hstep := evalProgStmt_callRet_err [{ addFunc with name := "_Z3addii" }]
      F "s" "_Z3addii" ["x", "y"] [("x", .i32 x), ("y", .i32 y)]
      [.i32 x, .i32 y] { addFunc with name := "_Z3addii" } e hargs hfind hcall'
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_err _ _ _ _ _ _ hstep]
    simp [useAddFwd, hadd]
  | ok v =>
    have hcall' : evalFuncFuel F { addFunc with name := "_Z3addii" }
        [.i32 x, .i32 y] = .ok v := by
      rw [hcall, hadd]
    have hstep := evalProgStmt_callRet_ok [{ addFunc with name := "_Z3addii" }]
      F "s" "_Z3addii" ["x", "y"] [("x", .i32 x), ("y", .i32 y)]
      [.i32 x, .i32 y] { addFunc with name := "_Z3addii" } v hargs hfind hcall'
    have hret : evalProgStmt [{ addFunc with name := "_Z3addii" }] F
        (.return_ (.var "s")) (envExtend [("x", .i32 x), ("y", .i32 y)] "s" v) =
        .ok (envExtend [("x", .i32 x), ("y", .i32 y)] "s" v,
          .returned v) :=
      evalProgStmt_return [{ addFunc with name := "_Z3addii" }] F (.var "s") _
        v (evalExpr_var_hit _ _ _ (envExtend_hit _ _ _))
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep, hret]
    simp [useAddFwd, hadd]

/-- `emit_correct` for `use_ns_add`: same proof at the namespaced leaf. -/
theorem evalProgFunc_useNsAdd (F : Nat) (x y : BitVec 32) :
    evalProgFunc [{ addFunc with name := "_ZN2ns3addEii" }] F useNsAddFunc
      [.i32 x, .i32 y] = useNsAddFwd x y := by
  have hbind : bindArgs useNsAddFunc.args [.i32 x, .i32 y] =
      some [("x", .i32 x), ("y", .i32 y)] := rfl
  have hbody : useNsAddFunc.body =
      .seq (.callRet "s" "_ZN2ns3addEii" ["x", "y"])
           (.return_ (.var "s")) := rfl
  have hx := envLookup_useAddCaller_x x y
  have hy := envLookup_useAddCaller_y x y
  have hfind : findFunc [{ addFunc with name := "_ZN2ns3addEii" }] "_ZN2ns3addEii" =
      some { addFunc with name := "_ZN2ns3addEii" } :=
    findFunc_hit { addFunc with name := "_ZN2ns3addEii" } []
  have hargs : lookupArgs [("x", .i32 x), ("y", .i32 y)] ["x", "y"] =
      some [.i32 x, .i32 y] := by
    simp [lookupArgs, hx, hy]
  have hcall := evalFuncFuel_addAt F "_ZN2ns3addEii" x y
  cases hadd : addFwd x y with
  | error e =>
    have hcall' : evalFuncFuel F { addFunc with name := "_ZN2ns3addEii" }
        [.i32 x, .i32 y] = .error e := by
      rw [hcall, hadd]
    have hstep := evalProgStmt_callRet_err [{ addFunc with name := "_ZN2ns3addEii" }]
      F "s" "_ZN2ns3addEii" ["x", "y"] [("x", .i32 x), ("y", .i32 y)]
      [.i32 x, .i32 y] { addFunc with name := "_ZN2ns3addEii" } e hargs hfind hcall'
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_err _ _ _ _ _ _ hstep]
    simp [useNsAddFwd, hadd]
  | ok v =>
    have hcall' : evalFuncFuel F { addFunc with name := "_ZN2ns3addEii" }
        [.i32 x, .i32 y] = .ok v := by
      rw [hcall, hadd]
    have hstep := evalProgStmt_callRet_ok [{ addFunc with name := "_ZN2ns3addEii" }]
      F "s" "_ZN2ns3addEii" ["x", "y"] [("x", .i32 x), ("y", .i32 y)]
      [.i32 x, .i32 y] { addFunc with name := "_ZN2ns3addEii" } v hargs hfind hcall'
    have hret : evalProgStmt [{ addFunc with name := "_ZN2ns3addEii" }] F
        (.return_ (.var "s")) (envExtend [("x", .i32 x), ("y", .i32 y)] "s" v) =
        .ok (envExtend [("x", .i32 x), ("y", .i32 y)] "s" v,
          .returned v) :=
      evalProgStmt_return [{ addFunc with name := "_ZN2ns3addEii" }] F (.var "s") _
        v (evalExpr_var_hit _ _ _ (envExtend_hit _ _ _))
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep, hret]
    simp [useNsAddFwd, hadd]

/-- Env facts for the `add_caller` shape. -/
theorem envLookup_addCaller_x (x y z : BitVec 32) :
    envLookup [("x", .i32 x), ("y", .i32 y), ("z", .i32 z)] "x" =
      some (.i32 x) := by
  simp [envLookup]

theorem envLookup_addCaller_y (x y z : BitVec 32) :
    envLookup [("x", .i32 x), ("y", .i32 y), ("z", .i32 z)] "y" =
      some (.i32 y) := by
  simp [envLookup, show ("y" : String) ≠ "x" by decide]

theorem envLookup_addCaller_z (x y z : BitVec 32) :
    envLookup [("x", .i32 x), ("y", .i32 y), ("z", .i32 z)] "z" =
      some (.i32 z) := by
  simp [envLookup, show ("z" : String) ≠ "x" by decide,
    show ("z" : String) ≠ "y" by decide]

/-- Env facts for the `sum_caller` shape. -/
theorem envLookup_sumCaller_a (l : List (BitVec 32)) (nv : BitVec 32) :
    envLookup [("a", .arr32 l), ("n", .u32 nv)] "a" =
      some (.arr32 l) := by
  simp [envLookup]

theorem envLookup_sumCaller_n (l : List (BitVec 32)) (nv : BitVec 32) :
    envLookup [("a", .arr32 l), ("n", .u32 nv)] "n" = some (.u32 nv) := by
  simp [envLookup, show ("n" : String) ≠ "a" by decide]

/-- `emit_correct` for `add_caller`: program evaluation over `[addFunc]`
    agrees with the forward on all inputs (ok and error paths). -/
theorem evalProgFunc_addCaller (F : Nat) (x y z : BitVec 32) :
    evalProgFunc [addFunc] F addCallerFunc [.i32 x, .i32 y, .i32 z] =
      addCallerFwd x y z := by
  have hbind : bindArgs addCallerFunc.args [.i32 x, .i32 y, .i32 z] =
      some [("x", .i32 x), ("y", .i32 y), ("z", .i32 z)] := rfl
  have hbody : addCallerFunc.body =
      .seq (.callRet "t" "add" ["x", "y"])
      (.seq (.callRet "r" "add" ["t", "z"])
            (.return_ (.var "r"))) := rfl
  have hx := envLookup_addCaller_x x y z
  have hy := envLookup_addCaller_y x y z
  have hfind : findFunc [addFunc] "add" = some addFunc :=
    findFunc_hit addFunc []
  cases h1 : checkedAddI32 x y with
  | error e =>
    have hc1 : evalFuncFuel F addFunc [.i32 x, .i32 y] = .error e := by
      rw [evalFuncFuel_add]
      unfold addFwd
      rw [h1]
      exact i32_map_error e
    have hargs1 : lookupArgs [("x", .i32 x), ("y", .i32 y), ("z", .i32 z)]
        ["x", "y"] = some [.i32 x, .i32 y] := by
      simp [lookupArgs, hx, hy]
    have hstep1 := evalProgStmt_callRet_err [addFunc] F "t" "add" ["x", "y"]
      [("x", .i32 x), ("y", .i32 y), ("z", .i32 z)]
      [.i32 x, .i32 y] addFunc e hargs1 hfind hc1
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_err _ _ _ _ _ _ hstep1]
    simp [addCallerFwd, h1]
  | ok t =>
    have hc1 : evalFuncFuel F addFunc [.i32 x, .i32 y] =
        .ok (.i32 t) := by
      rw [evalFuncFuel_add]
      unfold addFwd
      rw [h1]
      exact i32_map_ok t
    have hargs1 : lookupArgs [("x", .i32 x), ("y", .i32 y), ("z", .i32 z)]
        ["x", "y"] = some [.i32 x, .i32 y] := by
      simp [lookupArgs, hx, hy]
    have hstep1 := evalProgStmt_callRet_ok [addFunc] F "t" "add" ["x", "y"]
      [("x", .i32 x), ("y", .i32 y), ("z", .i32 z)]
      [.i32 x, .i32 y] addFunc (.i32 t) hargs1 hfind hc1
    have htz : envLookup (envExtend [("x", .i32 x), ("y", .i32 y),
        ("z", .i32 z)] "t" (.i32 t)) "t" = some (.i32 t) :=
      envExtend_hit _ _ _
    have htz2 : envLookup (envExtend [("x", .i32 x), ("y", .i32 y),
        ("z", .i32 z)] "t" (.i32 t)) "z" = some (.i32 z) := by
      simp [envExtend, envLookup, show ("z" : String) ≠ "t" by decide]
    cases h2 : checkedAddI32 t z with
    | error e =>
      have hc2 : evalFuncFuel F addFunc [.i32 t, .i32 z] = .error e := by
        rw [evalFuncFuel_add]
        unfold addFwd
        rw [h2]
        exact i32_map_error e
      have hargs2 : lookupArgs (envExtend [("x", .i32 x), ("y", .i32 y),
          ("z", .i32 z)] "t" (.i32 t)) ["t", "z"] =
          some [.i32 t, .i32 z] := by
        simp [lookupArgs, htz, htz2]
      have hstep2 := evalProgStmt_callRet_err [addFunc] F "r" "add"
        ["t", "z"] (envExtend [("x", .i32 x), ("y", .i32 y),
          ("z", .i32 z)] "t" (.i32 t))
        [.i32 t, .i32 z] addFunc e hargs2 hfind hc2
      simp only [evalProgFunc, hbind, hbody]
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep1,
        evalProgStmt_seq_err _ _ _ _ _ _ hstep2]
      simp [addCallerFwd, h1, h2, i32_map_error]
    | ok r =>
      have hc2 : evalFuncFuel F addFunc [.i32 t, .i32 z] =
          .ok (.i32 r) := by
        rw [evalFuncFuel_add]
        unfold addFwd
        rw [h2]
        exact i32_map_ok r
      have hargs2 : lookupArgs (envExtend [("x", .i32 x), ("y", .i32 y),
          ("z", .i32 z)] "t" (.i32 t)) ["t", "z"] =
          some [.i32 t, .i32 z] := by
        simp [lookupArgs, htz, htz2]
      have hstep2 := evalProgStmt_callRet_ok [addFunc] F "r" "add"
        ["t", "z"] (envExtend [("x", .i32 x), ("y", .i32 y),
          ("z", .i32 z)] "t" (.i32 t))
        [.i32 t, .i32 z] addFunc (.i32 r) hargs2 hfind hc2
      have hret : evalProgStmt [addFunc] F (.return_ (.var "r"))
          (envExtend (envExtend [("x", .i32 x), ("y", .i32 y),
            ("z", .i32 z)] "t" (.i32 t)) "r" (.i32 r)) =
          .ok (envExtend (envExtend [("x", .i32 x), ("y", .i32 y),
            ("z", .i32 z)] "t" (.i32 t)) "r" (.i32 r),
            .returned (.i32 r)) :=
        evalProgStmt_return [addFunc] F (.var "r") _
          (.i32 r) (evalExpr_var_hit _ _ _ (envExtend_hit _ _ _))
      simp only [evalProgFunc, hbind, hbody]
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep1,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep2, hret]
      simp [addCallerFwd, h1, h2, i32_map_ok]

/-- `emit_correct` for `sum_caller`: program evaluation over `[sumFunc]`
    agrees with the delegating forward (fuel must cover `n`). -/
theorem evalProgFunc_sumCaller (F : Nat) (l : List (BitVec 32))
    (nv : BitVec 32)
    (hle : nv.toNat ≤ l.length) (h32 : nv.toNat < 2 ^ 32)
    (hF : nv.toNat ≤ F) :
    evalProgFunc [sumFunc] F sumCallerFunc [.arr32 l, .u32 nv] =
      sumCallerFwd l nv := by
  have hbind : bindArgs sumCallerFunc.args [.arr32 l, .u32 nv] =
      some [("a", .arr32 l), ("n", .u32 nv)] := rfl
  have hbody : sumCallerFunc.body =
      .seq (.callRet "s" "sum_array" ["a", "n"])
           (.return_ (.var "s")) := rfl
  have ha := envLookup_sumCaller_a l nv
  have hn := envLookup_sumCaller_n l nv
  have hfind : findFunc [sumFunc] "sum_array" = some sumFunc :=
    findFunc_hit sumFunc []
  have hargs : lookupArgs [("a", .arr32 l), ("n", .u32 nv)] ["a", "n"] =
      some [.arr32 l, .u32 nv] := by
    simp [lookupArgs, ha, hn]
  have hcall := evalFuncFuel_sum F l nv hle h32 hF
  cases hsum : sumFwd l nv with
  | error e =>
    have hcall' : evalFuncFuel F sumFunc [.arr32 l, .u32 nv] = .error e := by
      rw [hcall, hsum]
    have hstep := evalProgStmt_callRet_err [sumFunc] F "s" "sum_array"
      ["a", "n"] [("a", .arr32 l), ("n", .u32 nv)]
      [.arr32 l, .u32 nv] sumFunc e hargs hfind hcall'
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_err _ _ _ _ _ _ hstep]
    simp [sumCallerFwd, hsum]
  | ok v =>
    have hcall' : evalFuncFuel F sumFunc [.arr32 l, .u32 nv] = .ok v := by
      rw [hcall, hsum]
    have hstep := evalProgStmt_callRet_ok [sumFunc] F "s" "sum_array"
      ["a", "n"] [("a", .arr32 l), ("n", .u32 nv)]
      [.arr32 l, .u32 nv] sumFunc v hargs hfind hcall'
    have hret : evalProgStmt [sumFunc] F (.return_ (.var "s"))
        (envExtend [("a", .arr32 l), ("n", .u32 nv)] "s" v) =
        .ok (envExtend [("a", .arr32 l), ("n", .u32 nv)] "s" v,
          .returned v) :=
      evalProgStmt_return [sumFunc] F (.var "s") _
        v (evalExpr_var_hit _ _ _ (envExtend_hit _ _ _))
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep, hret]
    simp [sumCallerFwd, hsum]
