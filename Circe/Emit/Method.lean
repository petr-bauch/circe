/-
Circe.Emit.Method — M2a POD const-methods: the `_ZNK5Point3sumEv` leaf
(`this` + field reads + `nsw` add — the S2 body with a pointer param)
and the `_Z13point_sum_refRK5Point` entry (single DAG call into the
leaf via S1 `callRet`; no new CIR constructs).
-/
import Circe.Emit.Fragment

/-! ## M2a: POD const-methods (`point_sum_ref`) -/

/-- Canonical CoreIR for the `_ZNK5Point3sumEv` method leaf in
    `tests/cpp/point_sum_ref.cpp`: project both fields of `this`,
    checked-add them (`cir.get_member` + `cir.load` fused into `fget`,
    exactly as in S2 `translate`; `this` binds the `Point` value, copy
    semantics). -/
def methodSumFunc : Func :=
  ⟨"_ZNK5Point3sumEv",
   [{ name := "this", ty := .struct "Point" [.i 32, .i 32], role := .owned }],
   .i 32,
   .return_ (.add (.fget "this" "x") (.fget "this" "y"))⟩

/-- Canonical CoreIR for the `_Z13point_sum_refRK5Point` entry: single
    DAG call delegating to the method leaf (the call site targets the
    call-free `methodSumFunc`, matched by name in `evalProgStmt`). -/
def pointSumRefFunc : Func :=
  ⟨"_Z13point_sum_refRK5Point",
   [{ name := "p", ty := .struct "Point" [.i 32, .i 32], role := .owned }],
   .i 32,
   .seq (.callRet "s" "_ZNK5Point3sumEv" ["p"])
        (.return_ (.var "s"))⟩

/-- Value-level forward for the method leaf: checked field addition
    (cf. rendered `_ZNK5Point3sumEv_fwd`, which delegates to
    `pointSum`). -/
def methodSumFwd (px py : BitVec 32) : Result Value :=
  .i32 <$> checkedAddI32 px py

/-- Bridge: forward ok-path is the checked add. -/
theorem methodSumFwd_ok (px py s : BitVec 32)
    (h : checkedAddI32 px py = .ok s) :
    methodSumFwd px py = .ok (.i32 s) := by
  simp [methodSumFwd, h, i32_map_ok]

/-- Bridge: forward error-path propagates. -/
theorem methodSumFwd_err (px py : BitVec 32) (e : Panic)
    (h : checkedAddI32 px py = .error e) :
    methodSumFwd px py = .error e := by
  simp [methodSumFwd, h, i32_map_error]

/-- Value-level forward for the entry: direct delegation to the method
    forward (cf. rendered `_Z13point_sum_refRK5Point_fwd`). -/
def pointSumRefFwd (px py : BitVec 32) : Result Value :=
  methodSumFwd px py

theorem pointSumRefFwd_is_call (px py : BitVec 32) :
    pointSumRefFwd px py = methodSumFwd px py := rfl

/-- Env fact for the method shape. -/
theorem envLookup_methodSum_this (px py : BitVec 32) :
    envLookup [("this", .structVal "Point" [("x", px), ("y", py)])] "this" =
      some (.structVal "Point" [("x", px), ("y", py)]) := by
  simp [envLookup]

/-- Field facts for the bound `Point` value. -/
theorem fieldLookup_methodSum_x (px py : BitVec 32) :
    fieldLookup [("x", px), ("y", py)] "x" = some px :=
  fieldLookup_hit "x" px _

theorem fieldLookup_methodSum_y (px py : BitVec 32) :
    fieldLookup [("x", px), ("y", py)] "y" = some py := by
  rw [fieldLookup_miss "x" "y" px _ (by decide)]
  exact fieldLookup_hit "y" py _

/-- `add` of two projected fields forwards to `checkedAddI32` (the
    fget+fget combination; cf. `evalExpr_add_fget_var` in `Circe.Eval`
    for the fget+var combination used by `translate`). -/
theorem evalExpr_add_fget_fget (ρ : Env) (obj : String)
    (tag : String) (fields : List (String × BitVec 32))
    (px py : BitVec 32)
    (hobj : envLookup ρ obj = some (.structVal tag fields))
    (hfx : fieldLookup fields "x" = some px)
    (hfy : fieldLookup fields "y" = some py) :
    evalExpr (.add (.fget obj "x") (.fget obj "y")) ρ =
      (checkedAddI32 px py).map .i32 := by
  simp [evalExpr, hobj, hfx, hfy]

/-- `emit_correct` for the method leaf: evaluation agrees with the
    forward on all inputs (ok and error paths). Loop-free body, so
    every fuel agrees. -/
theorem evalFuncFuel_methodSum (F : Nat) (px py : BitVec 32) :
    evalFuncFuel F methodSumFunc
      [.structVal "Point" [("x", px), ("y", py)]] =
      methodSumFwd px py := by
  have hbind : bindArgs methodSumFunc.args
      [.structVal "Point" [("x", px), ("y", py)]] =
      some [("this", .structVal "Point" [("x", px), ("y", py)])] := rfl
  have hbody : methodSumFunc.body =
      .return_ (.add (.fget "this" "x") (.fget "this" "y")) := rfl
  have hthis := envLookup_methodSum_this px py
  have hfx := fieldLookup_methodSum_x px py
  have hfy := fieldLookup_methodSum_y px py
  have hadd : evalExpr (.add (.fget "this" "x") (.fget "this" "y"))
      [("this", .structVal "Point" [("x", px), ("y", py)])] =
      (checkedAddI32 px py).map .i32 :=
    evalExpr_add_fget_fget _ _ _ _ _ _ hthis hfx hfy
  cases h : checkedAddI32 px py with
  | error e =>
    have hadd' : evalExpr (.add (.fget "this" "x") (.fget "this" "y"))
        [("this", .structVal "Point" [("x", px), ("y", py)])] =
        .error e := by
      rw [hadd, h]
      exact i32_map_error e
    have hret : evalStmtFuel F
        (.return_ (.add (.fget "this" "x") (.fget "this" "y")))
        [("this", .structVal "Point" [("x", px), ("y", py)])] =
        .error e :=
      evalStmtFuel_return_err _ _ _ _ hadd'
    simp only [evalFuncFuel, hbind, hbody, hret, methodSumFwd, h,
      i32_map_error]
  | ok s =>
    have hadd' : evalExpr (.add (.fget "this" "x") (.fget "this" "y"))
        [("this", .structVal "Point" [("x", px), ("y", py)])] =
        .ok (.i32 s) := by
      rw [hadd, h]
      exact i32_map_ok s
    have hret : evalStmtFuel F
        (.return_ (.add (.fget "this" "x") (.fget "this" "y")))
        [("this", .structVal "Point" [("x", px), ("y", py)])] =
        .ok ([("this", .structVal "Point" [("x", px), ("y", py)])],
          .returned (.i32 s)) :=
      evalStmtFuel_return _ _ _ _ hadd'
    simp only [evalFuncFuel, hbind, hbody, hret, methodSumFwd, h,
      i32_map_ok]

/-- Env fact for the entry shape. -/
theorem envLookup_pointSumRef_p (px py : BitVec 32) :
    envLookup [("p", .structVal "Point" [("x", px), ("y", py)])] "p" =
      some (.structVal "Point" [("x", px), ("y", py)]) := by
  simp [envLookup]

/-- `emit_correct` for the entry: program evaluation over
    `[methodSumFunc]` agrees with the delegating forward (loop-free, so
    every fuel agrees). -/
theorem evalProgFunc_pointSumRef (F : Nat) (px py : BitVec 32) :
    evalProgFunc [methodSumFunc] F pointSumRefFunc
      [.structVal "Point" [("x", px), ("y", py)]] =
      pointSumRefFwd px py := by
  have hbind : bindArgs pointSumRefFunc.args
      [.structVal "Point" [("x", px), ("y", py)]] =
      some [("p", .structVal "Point" [("x", px), ("y", py)])] := rfl
  have hbody : pointSumRefFunc.body =
      .seq (.callRet "s" "_ZNK5Point3sumEv" ["p"])
           (.return_ (.var "s")) := rfl
  have hp := envLookup_pointSumRef_p px py
  have hfind : findFunc [methodSumFunc] "_ZNK5Point3sumEv" =
      some methodSumFunc :=
    findFunc_hit methodSumFunc []
  have hargs : lookupArgs [("p", .structVal "Point" [("x", px), ("y", py)])]
      ["p"] = some [.structVal "Point" [("x", px), ("y", py)]] := by
    simp [lookupArgs, hp]
  have hcall := evalFuncFuel_methodSum F px py
  cases hsum : methodSumFwd px py with
  | error e =>
    have hcall' : evalFuncFuel F methodSumFunc
        [.structVal "Point" [("x", px), ("y", py)]] = .error e := by
      rw [hcall, hsum]
    have hstep := evalProgStmt_callRet_err [methodSumFunc] F "s"
      "_ZNK5Point3sumEv" ["p"]
      [("p", .structVal "Point" [("x", px), ("y", py)])]
      [.structVal "Point" [("x", px), ("y", py)]] methodSumFunc e hargs
      hfind hcall'
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_err _ _ _ _ _ _ hstep]
    simp [pointSumRefFwd, hsum]
  | ok v =>
    have hcall' : evalFuncFuel F methodSumFunc
        [.structVal "Point" [("x", px), ("y", py)]] = .ok v := by
      rw [hcall, hsum]
    have hstep := evalProgStmt_callRet_ok [methodSumFunc] F "s"
      "_ZNK5Point3sumEv" ["p"]
      [("p", .structVal "Point" [("x", px), ("y", py)])]
      [.structVal "Point" [("x", px), ("y", py)]] methodSumFunc v hargs
      hfind hcall'
    have hret : evalProgStmt [methodSumFunc] F (.return_ (.var "s"))
        (envExtend [("p", .structVal "Point" [("x", px), ("y", py)])]
          "s" v) =
        .ok (envExtend [("p", .structVal "Point" [("x", px), ("y", py)])]
          "s" v, .returned v) :=
      evalProgStmt_return [methodSumFunc] F (.var "s") _
        v (evalExpr_var_hit _ _ _ (envExtend_hit _ _ _))
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep, hret]
    simp [pointSumRefFwd, hsum]
