/-
Circe.Emit.Acc — M2b value ctors + trivial dtors: the `Acc` accumulator.

`acc_two(a, b)` is int-only (the struct never crosses the boundary), so
the accumulator state is a single `i32` word threaded functionally
(mutating methods functionalized, as in `incr`): the ctor call is the
field-init (`s = 0`), each `add` call a checked `s += v`, `get` the
identity, and the trivial-dtor call a no-op (all erased at validation;
the `cleanup` scope sequences them, `cleanup normal` at exit).
-/
import Circe.Emit.Fragment
import Circe.Emit.M2Fwd

/-! ## M2b: value ctors + trivial dtors (`acc_two`) -/

/-- Canonical CoreIR for the `_ZN3AccC2Ev` ctor leaf in
    `tests/cpp/acc_two.cpp`: field-init (`s = 0`; `cir.get_member` +
    `cir.const 0` + store fused to the `0` literal). -/
def accCtorFunc : Func :=
  ⟨"_ZN3AccC2Ev", [], .i 32, .return_ (.lit (.i32 0))⟩

/-- Canonical CoreIR for the `_ZN3Acc3addEi` method leaf: checked
    `s += v` (`cir.get_member` + `cir.load` fused into the `s` var,
    store-back functionalized — the `incr` shape with an explicit delta). -/
def accAddFunc : Func :=
  ⟨"_ZN3Acc3addEi",
   [{ name := "s", ty := .i 32, role := .owned },
    { name := "v", ty := .i 32, role := .owned }],
   .i 32,
   .return_ (.add (.var "s") (.var "v"))⟩

/-- Canonical CoreIR for the `_ZNK3Acc3getEv` const-getter leaf: the
    identity (`cir.get_member` + `cir.load` fused into the `s` var). -/
def accGetFunc : Func :=
  ⟨"_ZNK3Acc3getEv",
   [{ name := "s", ty := .i 32, role := .owned }],
   .i 32,
   .return_ (.var "s")⟩

/-- Canonical CoreIR for the `_ZN3AccD2Ev` trivial-dtor leaf: a no-op
    (empty body; the identity carries the state through the `cleanup`
    scope so the sequencing is visible to `evalProgFunc`). -/
def accDtorFunc : Func :=
  ⟨"_ZN3AccD2Ev",
   [{ name := "t", ty := .i 32, role := .owned }],
   .i 32,
   .return_ (.var "t")⟩

/-- Canonical CoreIR for the `_Z7acc_twoii` entry: the `cleanup` scope
    sequences ctor → add → add → get → (no-op) dtor via S1 `callRet`
    (the call sites target the call-free leaves above, matched by
    (mangled) name in `evalProgStmt`). -/
def accTwoFunc : Func :=
  ⟨"_Z7acc_twoii",
   [{ name := "a", ty := .i 32, role := .owned },
    { name := "b", ty := .i 32, role := .owned }],
   .i 32,
   .cleanup
     (.seq (.callRet "s0" "_ZN3AccC2Ev" [])
     (.seq (.callRet "s1" "_ZN3Acc3addEi" ["s0", "a"])
     (.seq (.callRet "s2" "_ZN3Acc3addEi" ["s1", "b"])
     (.seq (.callRet "s3" "_ZNK3Acc3getEv" ["s2"])
     (.seq (.callRet "u" "_ZN3AccD2Ev" ["s3"])
           (.return_ (.var "s3")))))))⟩

/-- Value-level forward for the ctor leaf (cf. rendered
    `_ZN3AccC2Ev_fwd`, which delegates to `accCtor`). -/
def accCtorFwd : Result Value :=
  .ok (.i32 accCtor)

/-- Value-level forward for the add leaf. -/
def accAddFwd (s v : BitVec 32) : Result Value :=
  .i32 <$> checkedAddI32 s v

/-- Bridge: forward ok-path is the checked add. -/
theorem accAddFwd_ok (s v r : BitVec 32)
    (h : checkedAddI32 s v = .ok r) :
    accAddFwd s v = .ok (.i32 r) := by
  simp [accAddFwd, h, i32_map_ok]

/-- Bridge: forward error-path propagates. -/
theorem accAddFwd_err (s v : BitVec 32) (e : Panic)
    (h : checkedAddI32 s v = .error e) :
    accAddFwd s v = .error e := by
  simp [accAddFwd, h, i32_map_error]

/-- Value-level forward for the getter leaf (identity). -/
def accGetFwd (s : BitVec 32) : Result Value :=
  .ok (.i32 s)

/-- Value-level forward for the trivial-dtor leaf (no-op identity). -/
def accDtorFwd (t : BitVec 32) : Result Value :=
  .ok (.i32 t)

/-- Value-level forward for the entry: direct delegation to `accTwo`
    (cf. rendered `_Z7acc_twoii_fwd`). -/
def accTwoFwd (a b : BitVec 32) : Result Value :=
  .i32 <$> accTwo a b

theorem accTwoFwd_is_accTwo (a b : BitVec 32) :
    accTwoFwd a b = .i32 <$> accTwo a b := rfl

/-- `emit_correct` for the ctor leaf (loop-free, every fuel agrees). -/
theorem evalFuncFuel_accCtor (F : Nat) :
    evalFuncFuel F accCtorFunc [] = accCtorFwd := by
  have hbind : bindArgs accCtorFunc.args [] = some ([] : Env) := rfl
  have hbody : accCtorFunc.body = .return_ (.lit (.i32 0)) := rfl
  have hexpr : evalExpr (.lit (.i32 0)) ([] : Env) = .ok (.i32 0) := rfl
  have hret : evalStmtFuel F (.return_ (.lit (.i32 0))) ([] : Env) =
      .ok ([], .returned (.i32 0)) :=
    evalStmtFuel_return _ _ _ _ hexpr
  simp only [evalFuncFuel, hbind, hbody, hret, accCtorFwd, accCtor]

/-- `emit_correct` for the add leaf (ok and error paths). -/
theorem evalFuncFuel_accAdd (F : Nat) (s v : BitVec 32) :
    evalFuncFuel F accAddFunc [.i32 s, .i32 v] = accAddFwd s v := by
  have hbind : bindArgs accAddFunc.args [.i32 s, .i32 v] =
      some [("s", .i32 s), ("v", .i32 v)] := rfl
  have hbody : accAddFunc.body =
      .return_ (.add (.var "s") (.var "v")) := rfl
  have hs : envLookup ([("s", .i32 s), ("v", .i32 v)] : Env) "s" =
      some (.i32 s) := rfl
  have hv : envLookup ([("s", .i32 s), ("v", .i32 v)] : Env) "v" =
      some (.i32 v) := by
    simp [envLookup, show ("v" : String) ≠ "s" by decide]
  have hadd : evalExpr (.add (.var "s") (.var "v"))
      ([("s", .i32 s), ("v", .i32 v)] : Env) =
      (checkedAddI32 s v).map .i32 := by
    simp [evalExpr, hs, hv]
  cases h : checkedAddI32 s v with
  | error e =>
    have hadd' : evalExpr (.add (.var "s") (.var "v"))
        ([("s", .i32 s), ("v", .i32 v)] : Env) = .error e := by
      rw [hadd, h]
      exact i32_map_error e
    have hret : evalStmtFuel F (.return_ (.add (.var "s") (.var "v")))
        ([("s", .i32 s), ("v", .i32 v)] : Env) = .error e :=
      evalStmtFuel_return_err _ _ _ _ hadd'
    simp only [evalFuncFuel, hbind, hbody, hret, accAddFwd, h,
      i32_map_error]
  | ok r =>
    have hadd' : evalExpr (.add (.var "s") (.var "v"))
        ([("s", .i32 s), ("v", .i32 v)] : Env) = .ok (.i32 r) := by
      rw [hadd, h]
      exact i32_map_ok r
    have hret : evalStmtFuel F (.return_ (.add (.var "s") (.var "v")))
        ([("s", .i32 s), ("v", .i32 v)] : Env) =
        .ok ([("s", .i32 s), ("v", .i32 v)], .returned (.i32 r)) :=
      evalStmtFuel_return _ _ _ _ hadd'
    simp only [evalFuncFuel, hbind, hbody, hret, accAddFwd, h,
      i32_map_ok]

/-- `emit_correct` for the getter leaf (identity). -/
theorem evalFuncFuel_accGet (F : Nat) (s : BitVec 32) :
    evalFuncFuel F accGetFunc [.i32 s] = accGetFwd s := by
  have hbind : bindArgs accGetFunc.args [.i32 s] =
      some [("s", .i32 s)] := rfl
  have hbody : accGetFunc.body = .return_ (.var "s") := rfl
  have hexpr : evalExpr (.var "s") ([("s", .i32 s)] : Env) =
      .ok (.i32 s) := rfl
  have hret : evalStmtFuel F (.return_ (.var "s"))
      ([("s", .i32 s)] : Env) =
      .ok ([("s", .i32 s)], .returned (.i32 s)) :=
    evalStmtFuel_return _ _ _ _ hexpr
  simp only [evalFuncFuel, hbind, hbody, hret, accGetFwd]

/-- `emit_correct` for the trivial-dtor leaf (no-op identity). -/
theorem evalFuncFuel_accDtor (F : Nat) (t : BitVec 32) :
    evalFuncFuel F accDtorFunc [.i32 t] = accDtorFwd t := by
  have hbind : bindArgs accDtorFunc.args [.i32 t] =
      some [("t", .i32 t)] := rfl
  have hbody : accDtorFunc.body = .return_ (.var "t") := rfl
  have hexpr : evalExpr (.var "t") ([("t", .i32 t)] : Env) =
      .ok (.i32 t) := rfl
  have hret : evalStmtFuel F (.return_ (.var "t"))
      ([("t", .i32 t)] : Env) =
      .ok ([("t", .i32 t)], .returned (.i32 t)) :=
    evalStmtFuel_return _ _ _ _ hexpr
  simp only [evalFuncFuel, hbind, hbody, hret, accDtorFwd]

/-- The `Acc` program: the four call-free leaves the entry dispatches
    to (in file order). -/
abbrev accProg : Prog :=
  [accCtorFunc, accAddFunc, accGetFunc, accDtorFunc]

/-- `emit_correct` for the entry: program evaluation over `accProg`
    agrees with the delegating forward (loop-free, every fuel agrees). -/
theorem evalProgFunc_accTwo (F : Nat) (a b : BitVec 32) :
    evalProgFunc accProg F accTwoFunc [.i32 a, .i32 b] =
      accTwoFwd a b := by
  have hbind : bindArgs accTwoFunc.args [.i32 a, .i32 b] =
      some [("a", .i32 a), ("b", .i32 b)] := rfl
  have hbody : accTwoFunc.body =
      .cleanup
        (.seq (.callRet "s0" "_ZN3AccC2Ev" [])
        (.seq (.callRet "s1" "_ZN3Acc3addEi" ["s0", "a"])
        (.seq (.callRet "s2" "_ZN3Acc3addEi" ["s1", "b"])
        (.seq (.callRet "s3" "_ZNK3Acc3getEv" ["s2"])
        (.seq (.callRet "u" "_ZN3AccD2Ev" ["s3"])
              (.return_ (.var "s3"))))))) := rfl
  have hc0find : findFunc accProg "_ZN3AccC2Ev" = some accCtorFunc := rfl
  have ha1find : findFunc accProg "_ZN3Acc3addEi" = some accAddFunc := rfl
  have hgfind : findFunc accProg "_ZNK3Acc3getEv" = some accGetFunc := rfl
  have hdfind : findFunc accProg "_ZN3AccD2Ev" = some accDtorFunc := rfl
  have hargs0 : lookupArgs ([("a", .i32 a), ("b", .i32 b)] : Env) [] =
      some [] := rfl
  have hc0call := evalFuncFuel_accCtor F
  have hstep0 := evalProgStmt_callRet_ok accProg F "s0" "_ZN3AccC2Ev" []
    ([("a", .i32 a), ("b", .i32 b)] : Env) [] accCtorFunc (.i32 0)
    hargs0 hc0find hc0call
  have hargs1 : lookupArgs
      (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env) "s0" (.i32 0))
      ["s0", "a"] = some [.i32 0, .i32 a] := by
    simp [lookupArgs, envExtend, envLookup,
      show ("a" : String) ≠ "s0" by decide]
  have hadd1 := evalFuncFuel_accAdd F 0 a
  cases h1 : checkedAddI32 0 a with
  | error e =>
    have hcall1 : evalFuncFuel F accAddFunc [.i32 0, .i32 a] =
        .error e := by
      rw [hadd1]
      exact accAddFwd_err 0 a e h1
    have hstep1 := evalProgStmt_callRet_err accProg F "s1" "_ZN3Acc3addEi"
      ["s0", "a"]
      (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env) "s0" (.i32 0))
      [.i32 0, .i32 a] accAddFunc e hargs1 ha1find hcall1
    have hsum : accTwoFwd a b = .error e := by
      simp only [accTwoFwd_is_accTwo, accTwo_err_a a b e h1, i32_map_error]
    simp only [evalProgFunc, hbind, hbody, evalProgStmt_cleanup]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep0,
      evalProgStmt_seq_err _ _ _ _ _ _ hstep1]
    simp [hsum]
  | ok s1 =>
    have hcall1 : evalFuncFuel F accAddFunc [.i32 0, .i32 a] =
        .ok (.i32 s1) := by
      rw [hadd1]
      exact accAddFwd_ok 0 a s1 h1
    have hstep1 := evalProgStmt_callRet_ok accProg F "s1" "_ZN3Acc3addEi"
      ["s0", "a"]
      (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env) "s0" (.i32 0))
      [.i32 0, .i32 a] accAddFunc (.i32 s1) hargs1 ha1find hcall1
    have hargs2 : lookupArgs
        (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
          "s0" (.i32 0)) "s1" (.i32 s1))
        ["s1", "b"] = some [.i32 s1, .i32 b] := by
      simp [lookupArgs, envExtend, envLookup,
        show ("b" : String) ≠ "s1" by decide,
        show ("b" : String) ≠ "s0" by decide,
        show ("b" : String) ≠ "a" by decide]
    have hadd2 := evalFuncFuel_accAdd F s1 b
    cases h2 : checkedAddI32 s1 b with
    | error e =>
      have hcall2 : evalFuncFuel F accAddFunc [.i32 s1, .i32 b] =
          .error e := by
        rw [hadd2]
        exact accAddFwd_err s1 b e h2
      have hstep2 := evalProgStmt_callRet_err accProg F "s2" "_ZN3Acc3addEi"
        ["s1", "b"]
        (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
          "s0" (.i32 0)) "s1" (.i32 s1))
        [.i32 s1, .i32 b] accAddFunc e hargs2 ha1find hcall2
      have hsum : accTwoFwd a b = .error e := by
        simp only [accTwoFwd_is_accTwo, accTwo_err_b a b s1 e h1 h2,
          i32_map_error]
      simp only [evalProgFunc, hbind, hbody, evalProgStmt_cleanup]
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep0,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep1,
        evalProgStmt_seq_err _ _ _ _ _ _ hstep2]
      simp [hsum]
    | ok s2 =>
      have hcall2 : evalFuncFuel F accAddFunc [.i32 s1, .i32 b] =
          .ok (.i32 s2) := by
        rw [hadd2]
        exact accAddFwd_ok s1 b s2 h2
      have hstep2 := evalProgStmt_callRet_ok accProg F "s2" "_ZN3Acc3addEi"
        ["s1", "b"]
        (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
          "s0" (.i32 0)) "s1" (.i32 s1))
        [.i32 s1, .i32 b] accAddFunc (.i32 s2) hargs2 ha1find hcall2
      have hargs3 : lookupArgs
          (envExtend (envExtend (envExtend
            ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
          ["s2"] = some [.i32 s2] := rfl
      have hgetcall := evalFuncFuel_accGet F s2
      have hstep3 := evalProgStmt_callRet_ok accProg F "s3" "_ZNK3Acc3getEv"
        ["s2"]
        (envExtend (envExtend (envExtend
          ([("a", .i32 a), ("b", .i32 b)] : Env)
          "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
        [.i32 s2] accGetFunc (.i32 s2) hargs3 hgfind hgetcall
      have hargs4 : lookupArgs
          (envExtend (envExtend (envExtend (envExtend
            ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
            "s3" (.i32 s2))
          ["s3"] = some [.i32 s2] := rfl
      have hdtorcall := evalFuncFuel_accDtor F s2
      have hstep4 := evalProgStmt_callRet_ok accProg F "u" "_ZN3AccD2Ev"
        ["s3"]
        (envExtend (envExtend (envExtend (envExtend
          ([("a", .i32 a), ("b", .i32 b)] : Env)
          "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
          "s3" (.i32 s2))
        [.i32 s2] accDtorFunc (.i32 s2) hargs4 hdfind hdtorcall
      have hs3 : envLookup
          (envExtend (envExtend (envExtend (envExtend (envExtend
            ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
            "s3" (.i32 s2)) "u" (.i32 s2))
          "s3" = some (.i32 s2) := by
        simp [envExtend, envLookup,
          show ("s3" : String) ≠ "u" by decide]
      have hret : evalProgStmt accProg F (.return_ (.var "s3"))
          (envExtend (envExtend (envExtend (envExtend (envExtend
            ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
            "s3" (.i32 s2)) "u" (.i32 s2)) =
          .ok (envExtend (envExtend (envExtend (envExtend (envExtend
            ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
            "s3" (.i32 s2)) "u" (.i32 s2), .returned (.i32 s2)) :=
        evalProgStmt_return accProg F (.var "s3") _ _
          (evalExpr_var_hit _ _ _ hs3)
      simp only [evalProgFunc, hbind, hbody, evalProgStmt_cleanup]
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep0,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep1,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep2,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep3,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep4, hret]
      have hok : accTwoFwd a b = .ok (.i32 s2) := by
        simp only [accTwoFwd_is_accTwo, accTwo_ok a b s1 s2 h1 h2,
          i32_map_ok]
      simp [hok]
