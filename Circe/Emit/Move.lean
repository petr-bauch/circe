/-
Circe.Emit.Move — N4b move semantics + RAII: the `Acc` move ctor + entries.

`move_acc(a, b)` is int-only (the structs never cross the boundary), so
both accumulator states are `i32` words threaded functionally. The move
ctor call takes `(d, s)` (destination storage + source word) and returns
the source word (`s(o.s)` member-init; `d` is never read, mirroring that
the C++ ctor never reads the uninitialized destination). The
source-zeroing store (`o.s = 0`) is entry-level: `moveAccFunc` threads
it as an `assign` at the C++ sequence point, so post-move reads of the
source evaluate to the zeroed word (no textual no-read pin needed).
Both dtors are no-ops, so the nested `cleanup` scopes flatten to one
`.cleanup` with both dtor calls in C++ order (nesting only affects
unwinding paths, unobservable here since no dtor can fail).
-/
import Circe.Emit.Fragment
import Circe.Emit.Acc

/-! ## N4b: move ctor leaf + `move_acc` entry -/

/-- Canonical CoreIR for the `_ZN3AccC2EOS_` move-ctor leaf in
    `tests/cpp/move_acc.cpp`: destination takes the source word
    (`cir.get_member` reads fused to `s`, `d` ignored); the `o.s = 0`
    zeroing store is modeled at the call site (`moveAccFunc` `assign`). -/
def accMoveCtorFunc : Func :=
  ⟨"_ZN3AccC2EOS_",
   [{ name := "d", ty := .i 32, role := .owned },
    { name := "s", ty := .i 32, role := .owned }],
   .i 32,
   .return_ (.var "s")⟩

/-- Canonical CoreIR for the `_Z8move_accii` entry: the flattened
    `cleanup` scope sequences ctor → add → move-ctor → source-zeroing
    `assign` → add → get → two no-op dtors via S1 `callRet` (call sites
    target the `Acc` leaves, matched by (mangled) name). -/
def moveAccFunc : Func :=
  ⟨"_Z8move_accii",
   [{ name := "a", ty := .i 32, role := .owned },
    { name := "b", ty := .i 32, role := .owned }],
   .i 32,
   .cleanup
     (.seq (.callRet "s0" "_ZN3AccC2Ev" [])
     (.seq (.callRet "s1" "_ZN3Acc3addEi" ["s0", "a"])
     (.seq (.callRet "d1" "_ZN3AccC2EOS_" ["s0", "s1"])
     (.seq (.assign "s1" (.lit (.i32 0)))
     (.seq (.callRet "d2" "_ZN3Acc3addEi" ["d1", "b"])
     (.seq (.callRet "r" "_ZNK3Acc3getEv" ["d2"])
     (.seq (.callRet "u1" "_ZN3AccD2Ev" ["r"])
     (.seq (.callRet "u2" "_ZN3AccD2Ev" ["s1"])
           (.return_ (.var "r"))))))))))⟩

/-- Value-level forward for the move-ctor leaf (cf. rendered
    `_ZN3AccC2EOS__fwd`, which delegates to `accMoveCtor`). -/
def accMoveCtorFwd (d s : BitVec 32) : Result Value :=
  .i32 <$> accMoveCtor d s

theorem accMoveCtorFwd_is_ok (d s : BitVec 32) :
    accMoveCtorFwd d s = .ok (.i32 s) := rfl

/-- Value-level forward for the entry: direct delegation to `moveAcc`
    (cf. rendered `_Z8move_accii_fwd`). -/
def moveAccFwd (a b : BitVec 32) : Result Value :=
  .i32 <$> moveAcc a b

theorem moveAccFwd_is_moveAcc (a b : BitVec 32) :
    moveAccFwd a b = .i32 <$> moveAcc a b := rfl

/-- `emit_correct` for the move-ctor leaf (loop-free, every fuel agrees). -/
theorem evalFuncFuel_accMoveCtor (F : Nat) (d s : BitVec 32) :
    evalFuncFuel F accMoveCtorFunc [.i32 d, .i32 s] =
      accMoveCtorFwd d s := by
  have hbind : bindArgs accMoveCtorFunc.args [.i32 d, .i32 s] =
      some [("d", .i32 d), ("s", .i32 s)] := rfl
  have hbody : accMoveCtorFunc.body = .return_ (.var "s") := rfl
  have hs : envLookup ([("d", .i32 d), ("s", .i32 s)] : Env) "s" =
      some (.i32 s) := by
    simp [envLookup, show ("s" : String) ≠ "d" by decide]
  have hexpr : evalExpr (.var "s") ([("d", .i32 d), ("s", .i32 s)] : Env) =
      .ok (.i32 s) :=
    evalExpr_var_hit _ _ _ hs
  have hret : evalStmtFuel F (.return_ (.var "s"))
      ([("d", .i32 d), ("s", .i32 s)] : Env) =
      .ok ([("d", .i32 d), ("s", .i32 s)], .returned (.i32 s)) :=
    evalStmtFuel_return _ _ _ _ hexpr
  simp only [evalFuncFuel, hbind, hbody, hret, accMoveCtorFwd,
    accMoveCtor, i32_map_ok]

/-- The `Acc` move program: the ctor/add/move-ctor/get/dtor leaves the
    `move_acc` entry dispatches to (in file order). -/
abbrev moveProg : Prog :=
  [accCtorFunc, accAddFunc, accMoveCtorFunc, accGetFunc, accDtorFunc]

/-- The `Acc` early-return program: the ctor/add/get/dtor leaves the
    `scope_early` entry dispatches to (same leaves as `accProg`, in
    file order). -/
abbrev earlyProg : Prog :=
  [accCtorFunc, accAddFunc, accGetFunc, accDtorFunc]

/-- Canonical CoreIR for the `_Z11scope_earlyii` entry: the `cleanup`
    scope sequences ctor → add → an early-return `if_` over `ueq`
    (`a == b` on `i32` words, now defined since `ueq` is
    width-polymorphic bit equality) → add → get → no-op dtor. The
    early branch returns the first `get` directly (the scope-exit dtor
    is a no-op on every path). -/
def scopeEarlyFunc : Func :=
  ⟨"_Z11scope_earlyii",
   [{ name := "a", ty := .i 32, role := .owned },
    { name := "b", ty := .i 32, role := .owned }],
   .i 32,
   .cleanup
     (.seq (.callRet "s0" "_ZN3AccC2Ev" [])
     (.seq (.callRet "s1" "_ZN3Acc3addEi" ["s0", "a"])
     (.seq (.if_ (.ueq (.var "a") (.var "b"))
             (.seq (.callRet "r1" "_ZNK3Acc3getEv" ["s1"])
                   (.return_ (.var "r1")))
             .skip)
     (.seq (.callRet "s2" "_ZN3Acc3addEi" ["s1", "b"])
     (.seq (.callRet "r" "_ZNK3Acc3getEv" ["s2"])
     (.seq (.callRet "u" "_ZN3AccD2Ev" ["r"])
           (.return_ (.var "r"))))))))⟩

/-- Value-level forward for the entry: direct delegation to
    `scopeEarly` (cf. rendered `_Z11scope_earlyii_fwd`). -/
def scopeEarlyFwd (a b : BitVec 32) : Result Value :=
  .i32 <$> scopeEarly a b

theorem scopeEarlyFwd_is_scopeEarly (a b : BitVec 32) :
    scopeEarlyFwd a b = .i32 <$> scopeEarly a b := rfl

/-- `emit_correct` for the entry: program evaluation over `earlyProg`
    agrees with the delegating forward (loop-free, every fuel agrees).
    Case shape: first-add error propagates; on success the `ueq`
    condition splits the early return (`a == b`, `seq_returned`
    short-circuits the trailing adds) from the fallthrough (`else`
    `skip`, then the second add either fails or the get/dtor/return
    chain runs). -/
theorem evalProgFunc_scopeEarly (F : Nat) (a b : BitVec 32) :
    evalProgFunc earlyProg F scopeEarlyFunc [.i32 a, .i32 b] =
      scopeEarlyFwd a b := by
  have hbind : bindArgs scopeEarlyFunc.args [.i32 a, .i32 b] =
      some [("a", .i32 a), ("b", .i32 b)] := rfl
  have hbody : scopeEarlyFunc.body =
      .cleanup
        (.seq (.callRet "s0" "_ZN3AccC2Ev" [])
        (.seq (.callRet "s1" "_ZN3Acc3addEi" ["s0", "a"])
        (.seq (.if_ (.ueq (.var "a") (.var "b"))
                (.seq (.callRet "r1" "_ZNK3Acc3getEv" ["s1"])
                      (.return_ (.var "r1")))
                .skip)
        (.seq (.callRet "s2" "_ZN3Acc3addEi" ["s1", "b"])
        (.seq (.callRet "r" "_ZNK3Acc3getEv" ["s2"])
        (.seq (.callRet "u" "_ZN3AccD2Ev" ["r"])
              (.return_ (.var "r")))))))) := rfl
  have hc0find : findFunc earlyProg "_ZN3AccC2Ev" = some accCtorFunc := rfl
  have ha1find : findFunc earlyProg "_ZN3Acc3addEi" = some accAddFunc := rfl
  have hgfind : findFunc earlyProg "_ZNK3Acc3getEv" = some accGetFunc := rfl
  have hdfind : findFunc earlyProg "_ZN3AccD2Ev" = some accDtorFunc := rfl
  have hargs0 : lookupArgs ([("a", .i32 a), ("b", .i32 b)] : Env) [] =
      some [] := rfl
  have hc0call := evalFuncFuel_accCtor F
  have hstep0 := evalProgStmt_callRet_ok earlyProg F "s0" "_ZN3AccC2Ev" []
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
    have hstep1 := evalProgStmt_callRet_err earlyProg F "s1" "_ZN3Acc3addEi"
      ["s0", "a"]
      (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env) "s0" (.i32 0))
      [.i32 0, .i32 a] accAddFunc e hargs1 ha1find hcall1
    have hsum : scopeEarlyFwd a b = .error e := by
      simp only [scopeEarlyFwd_is_scopeEarly, scopeEarly_err_a a b e h1,
        i32_map_error]
    simp only [evalProgFunc, hbind, hbody, evalProgStmt_cleanup]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep0,
      evalProgStmt_seq_err _ _ _ _ _ _ hstep1]
    simp [hsum]
  | ok s1 =>
    have hcall1 : evalFuncFuel F accAddFunc [.i32 0, .i32 a] =
        .ok (.i32 s1) := by
      rw [hadd1]
      exact accAddFwd_ok 0 a s1 h1
    have hstep1 := evalProgStmt_callRet_ok earlyProg F "s1" "_ZN3Acc3addEi"
      ["s0", "a"]
      (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env) "s0" (.i32 0))
      [.i32 0, .i32 a] accAddFunc (.i32 s1) hargs1 ha1find hcall1
    have hne2 : ("a" : String) ≠ "s1" := by decide
    have hne3 : ("a" : String) ≠ "s0" := by decide
    have hne4 : ("b" : String) ≠ "s1" := by decide
    have hne5 : ("b" : String) ≠ "s0" := by decide
    have hcond : evalExpr (.ueq (.var "a") (.var "b"))
        (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
          "s0" (.i32 0)) "s1" (.i32 s1)) =
        .ok (.b (a == b)) := by
      simp [evalExpr, envLookup, envExtend, hne2, hne3, hne4, hne5]
    by_cases heq : a == b
    · have hcondT : evalExpr (.ueq (.var "a") (.var "b"))
          (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) = .ok (.b true) := by
        simp [evalExpr, envLookup, envExtend, hne2, hne3, hne4, hne5, heq]
      have hargsG1 : lookupArgs
          (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1))
          ["s1"] = some [.i32 s1] := rfl
      have hcallG1 := evalFuncFuel_accGet F s1
      have hstepG1 := evalProgStmt_callRet_ok earlyProg F "r1"
        "_ZNK3Acc3getEv" ["s1"]
        (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
          "s0" (.i32 0)) "s1" (.i32 s1))
        [.i32 s1] accGetFunc (.i32 s1) hargsG1 hgfind hcallG1
      have hexprR1 : evalExpr (.var "r1")
          (envExtend (envExtend (envExtend
            ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) "r1" (.i32 s1)) =
          .ok (.i32 s1) := by
        simp [evalExpr, envExtend, envLookup]
      have hstepR1 := evalProgStmt_return earlyProg F (.var "r1")
        (envExtend (envExtend (envExtend
          ([("a", .i32 a), ("b", .i32 b)] : Env)
          "s0" (.i32 0)) "s1" (.i32 s1)) "r1" (.i32 s1))
        (.i32 s1) hexprR1
      have hthen : evalProgStmt earlyProg F
          (.seq (.callRet "r1" "_ZNK3Acc3getEv" ["s1"])
            (.return_ (.var "r1")))
          (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) =
          .ok ((envExtend (envExtend (envExtend
            ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) "r1" (.i32 s1)),
            .returned (.i32 s1)) :=
        Eq.trans (evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepG1) hstepR1
      have hifT : evalProgStmt earlyProg F
          (.if_ (.ueq (.var "a") (.var "b"))
            (.seq (.callRet "r1" "_ZNK3Acc3getEv" ["s1"])
              (.return_ (.var "r1")))
            .skip)
          (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) =
          .ok ((envExtend (envExtend (envExtend
            ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) "r1" (.i32 s1)),
            .returned (.i32 s1)) :=
        Eq.trans (evalProgStmt_if_true _ _ _ _ _ _ hcondT) hthen
      have hsum : scopeEarlyFwd a b = .ok (.i32 s1) := by
        simp only [scopeEarlyFwd_is_scopeEarly,
          scopeEarly_ok_eq a b s1 h1 heq, i32_map_ok]
      simp only [evalProgFunc, hbind, hbody, evalProgStmt_cleanup]
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep0,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep1,
        evalProgStmt_seq_returned _ _ _ _ _ _ _ hifT]
      simp [hsum]
    · have hne : (a == b) = false := by
        simp [heq]
      have hcondF : evalExpr (.ueq (.var "a") (.var "b"))
          (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) = .ok (.b false) := by
        simp [evalExpr, envLookup, envExtend, hne2, hne3, hne4, hne5, hne]
      have hifF : evalProgStmt earlyProg F
          (.if_ (.ueq (.var "a") (.var "b"))
            (.seq (.callRet "r1" "_ZNK3Acc3getEv" ["s1"])
              (.return_ (.var "r1")))
            .skip)
          (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) =
          evalProgStmt earlyProg F .skip
            (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
              "s0" (.i32 0)) "s1" (.i32 s1)) :=
        evalProgStmt_if_false _ _ _ _ _ _ hcondF
      have hskip : evalProgStmt earlyProg F .skip
          (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) =
          .ok ((envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)), .fellThrough) := by
        cases F <;> rfl
      have hifF' : evalProgStmt earlyProg F
          (.if_ (.ueq (.var "a") (.var "b"))
            (.seq (.callRet "r1" "_ZNK3Acc3getEv" ["s1"])
              (.return_ (.var "r1")))
            .skip)
          (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) =
          .ok ((envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)), .fellThrough) :=
        Eq.trans hifF hskip
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
        have hstep2 := evalProgStmt_callRet_err earlyProg F "s2"
          "_ZN3Acc3addEi" ["s1", "b"]
          (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1))
          [.i32 s1, .i32 b] accAddFunc e hargs2 ha1find hcall2
        have hsum : scopeEarlyFwd a b = .error e := by
          simp only [scopeEarlyFwd_is_scopeEarly,
            scopeEarly_err_b a b s1 e h1 hne h2, i32_map_error]
        simp only [evalProgFunc, hbind, hbody, evalProgStmt_cleanup]
        rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep0,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep1,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hifF',
          evalProgStmt_seq_err _ _ _ _ _ _ hstep2]
        simp [hsum]
      | ok s2 =>
        have hcall2 : evalFuncFuel F accAddFunc [.i32 s1, .i32 b] =
            .ok (.i32 s2) := by
          rw [hadd2]
          exact accAddFwd_ok s1 b s2 h2
        have hstep2 := evalProgStmt_callRet_ok earlyProg F "s2"
          "_ZN3Acc3addEi" ["s1", "b"]
          (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1))
          [.i32 s1, .i32 b] accAddFunc (.i32 s2) hargs2 ha1find hcall2
        have hargsG : lookupArgs
            (envExtend (envExtend (envExtend
              ([("a", .i32 a), ("b", .i32 b)] : Env)
              "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
            ["s2"] = some [.i32 s2] := by
          simp [lookupArgs, envExtend, envLookup]
        have hcallG := evalFuncFuel_accGet F s2
        have hstepG := evalProgStmt_callRet_ok earlyProg F "r"
          "_ZNK3Acc3getEv" ["s2"]
          (envExtend (envExtend (envExtend
            ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
          [.i32 s2] accGetFunc (.i32 s2) hargsG hgfind hcallG
        have hargsD : lookupArgs
            (envExtend (envExtend (envExtend (envExtend
              ([("a", .i32 a), ("b", .i32 b)] : Env)
              "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
              "r" (.i32 s2))
            ["r"] = some [.i32 s2] := by
          simp [lookupArgs, envExtend, envLookup]
        have hcallD := evalFuncFuel_accDtor F s2
        have hstepD := evalProgStmt_callRet_ok earlyProg F "u"
          "_ZN3AccD2Ev" ["r"]
          (envExtend (envExtend (envExtend (envExtend
            ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
            "r" (.i32 s2))
          [.i32 s2] accDtorFunc (.i32 s2) hargsD hdfind hcallD
        have hexprR : evalExpr (.var "r")
            (envExtend (envExtend (envExtend (envExtend (envExtend
              ([("a", .i32 a), ("b", .i32 b)] : Env)
              "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
              "r" (.i32 s2)) "u" (.i32 s2)) =
            .ok (.i32 s2) := by
          simp [evalExpr, envExtend, envLookup]
        have hstepR := evalProgStmt_return earlyProg F (.var "r")
          (envExtend (envExtend (envExtend (envExtend (envExtend
            ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
            "r" (.i32 s2)) "u" (.i32 s2))
          (.i32 s2) hexprR
        have hsum : scopeEarlyFwd a b = .ok (.i32 s2) := by
          simp only [scopeEarlyFwd_is_scopeEarly,
            scopeEarly_ok_ne a b s1 s2 h1 hne h2, i32_map_ok]
        simp only [evalProgFunc, hbind, hbody, evalProgStmt_cleanup]
        rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep0,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep1,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hifF',
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep2,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepG,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepD,
          hstepR]
        simp [hsum]

/-- `emit_correct` for the entry: program evaluation over `moveProg`
    agrees with the delegating forward (loop-free, every fuel agrees).
    The `assign` step is the source-zeroing store (`o.s = 0`); the
    second dtor call therefore observes the zeroed word, exactly as
    the C++ scope-exit dtor does. -/
theorem evalProgFunc_moveAcc (F : Nat) (a b : BitVec 32) :
    evalProgFunc moveProg F moveAccFunc [.i32 a, .i32 b] =
      moveAccFwd a b := by
  have hbind : bindArgs moveAccFunc.args [.i32 a, .i32 b] =
      some [("a", .i32 a), ("b", .i32 b)] := rfl
  have hbody : moveAccFunc.body =
      .cleanup
        (.seq (.callRet "s0" "_ZN3AccC2Ev" [])
        (.seq (.callRet "s1" "_ZN3Acc3addEi" ["s0", "a"])
        (.seq (.callRet "d1" "_ZN3AccC2EOS_" ["s0", "s1"])
        (.seq (.assign "s1" (.lit (.i32 0)))
        (.seq (.callRet "d2" "_ZN3Acc3addEi" ["d1", "b"])
        (.seq (.callRet "r" "_ZNK3Acc3getEv" ["d2"])
        (.seq (.callRet "u1" "_ZN3AccD2Ev" ["r"])
        (.seq (.callRet "u2" "_ZN3AccD2Ev" ["s1"])
              (.return_ (.var "r")))))))))) := rfl
  have hc0find : findFunc moveProg "_ZN3AccC2Ev" = some accCtorFunc := rfl
  have ha1find : findFunc moveProg "_ZN3Acc3addEi" = some accAddFunc := rfl
  have hmfind : findFunc moveProg "_ZN3AccC2EOS_" = some accMoveCtorFunc := rfl
  have hgfind : findFunc moveProg "_ZNK3Acc3getEv" = some accGetFunc := rfl
  have hdfind : findFunc moveProg "_ZN3AccD2Ev" = some accDtorFunc := rfl
  have hargs0 : lookupArgs ([("a", .i32 a), ("b", .i32 b)] : Env) [] =
      some [] := rfl
  have hc0call := evalFuncFuel_accCtor F
  have hstep0 := evalProgStmt_callRet_ok moveProg F "s0" "_ZN3AccC2Ev" []
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
    have hstep1 := evalProgStmt_callRet_err moveProg F "s1" "_ZN3Acc3addEi"
      ["s0", "a"]
      (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env) "s0" (.i32 0))
      [.i32 0, .i32 a] accAddFunc e hargs1 ha1find hcall1
    have hsum : moveAccFwd a b = .error e := by
      simp only [moveAccFwd_is_moveAcc, moveAcc_err_a a b e h1, i32_map_error]
    simp only [evalProgFunc, hbind, hbody, evalProgStmt_cleanup]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep0,
      evalProgStmt_seq_err _ _ _ _ _ _ hstep1]
    simp [hsum]
  | ok s1 =>
    have hcall1 : evalFuncFuel F accAddFunc [.i32 0, .i32 a] =
        .ok (.i32 s1) := by
      rw [hadd1]
      exact accAddFwd_ok 0 a s1 h1
    have hstep1 := evalProgStmt_callRet_ok moveProg F "s1" "_ZN3Acc3addEi"
      ["s0", "a"]
      (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env) "s0" (.i32 0))
      [.i32 0, .i32 a] accAddFunc (.i32 s1) hargs1 ha1find hcall1
    have hargsM : lookupArgs
        (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
          "s0" (.i32 0)) "s1" (.i32 s1))
        ["s0", "s1"] = some [.i32 0, .i32 s1] := by
      simp [lookupArgs, envExtend, envLookup]
    have hcallM : evalFuncFuel F accMoveCtorFunc [.i32 0, .i32 s1] =
        .ok (.i32 s1) := by
      rw [evalFuncFuel_accMoveCtor F 0 s1]
      exact accMoveCtorFwd_is_ok 0 s1
    have hstepM := evalProgStmt_callRet_ok moveProg F "d1" "_ZN3AccC2EOS_"
      ["s0", "s1"]
      (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
        "s0" (.i32 0)) "s1" (.i32 s1))
      [.i32 0, .i32 s1] accMoveCtorFunc (.i32 s1) hargsM hmfind hcallM
    have hexpr0 : evalExpr (.lit (.i32 0))
        (envExtend (envExtend (envExtend
          ([("a", .i32 a), ("b", .i32 b)] : Env)
          "s0" (.i32 0)) "s1" (.i32 s1)) "d1" (.i32 s1)) =
        .ok (.i32 0) := rfl
    have hupd : envUpdate
        (envExtend (envExtend (envExtend
          ([("a", .i32 a), ("b", .i32 b)] : Env)
          "s0" (.i32 0)) "s1" (.i32 s1)) "d1" (.i32 s1))
        "s1" (.i32 0) =
        some ([("d1", .i32 s1), ("s1", .i32 0), ("s0", .i32 0),
          ("a", .i32 a), ("b", .i32 b)] : Env) := rfl
    have hstepA : evalProgStmt moveProg F
        (.assign "s1" (.lit (.i32 0)))
        (envExtend (envExtend (envExtend
          ([("a", .i32 a), ("b", .i32 b)] : Env)
          "s0" (.i32 0)) "s1" (.i32 s1)) "d1" (.i32 s1)) =
        .ok (([("d1", .i32 s1), ("s1", .i32 0), ("s0", .i32 0),
          ("a", .i32 a), ("b", .i32 b)] : Env), .fellThrough) :=
      evalStmtFuel_assign _ _ _ _ _ _ hexpr0 hupd
    have hargs2 : lookupArgs
        ([("d1", .i32 s1), ("s1", .i32 0), ("s0", .i32 0),
          ("a", .i32 a), ("b", .i32 b)] : Env)
        ["d1", "b"] = some [.i32 s1, .i32 b] := by
      simp [lookupArgs, envLookup,
        show ("b" : String) ≠ "d1" by decide,
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
      have hstep2 := evalProgStmt_callRet_err moveProg F "d2"
        "_ZN3Acc3addEi" ["d1", "b"]
        ([("d1", .i32 s1), ("s1", .i32 0), ("s0", .i32 0),
          ("a", .i32 a), ("b", .i32 b)] : Env)
        [.i32 s1, .i32 b] accAddFunc e hargs2 ha1find hcall2
      have hsum : moveAccFwd a b = .error e := by
        simp only [moveAccFwd_is_moveAcc, moveAcc_err_b a b s1 e h1 h2,
          i32_map_error]
      simp only [evalProgFunc, hbind, hbody, evalProgStmt_cleanup]
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep0,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep1,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepM,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepA,
        evalProgStmt_seq_err _ _ _ _ _ _ hstep2]
      simp [hsum]
    | ok s2 =>
      have hcall2 : evalFuncFuel F accAddFunc [.i32 s1, .i32 b] =
          .ok (.i32 s2) := by
        rw [hadd2]
        exact accAddFwd_ok s1 b s2 h2
      have hstep2 := evalProgStmt_callRet_ok moveProg F "d2"
        "_ZN3Acc3addEi" ["d1", "b"]
        ([("d1", .i32 s1), ("s1", .i32 0), ("s0", .i32 0),
          ("a", .i32 a), ("b", .i32 b)] : Env)
        [.i32 s1, .i32 b] accAddFunc (.i32 s2) hargs2 ha1find hcall2
      have hargsG : lookupArgs
          (envExtend ([("d1", .i32 s1), ("s1", .i32 0), ("s0", .i32 0),
            ("a", .i32 a), ("b", .i32 b)] : Env) "d2" (.i32 s2))
          ["d2"] = some [.i32 s2] := by
        simp [lookupArgs, envExtend, envLookup]
      have hcallG := evalFuncFuel_accGet F s2
      have hstepG := evalProgStmt_callRet_ok moveProg F "r"
        "_ZNK3Acc3getEv" ["d2"]
        (envExtend ([("d1", .i32 s1), ("s1", .i32 0), ("s0", .i32 0),
          ("a", .i32 a), ("b", .i32 b)] : Env) "d2" (.i32 s2))
        [.i32 s2] accGetFunc (.i32 s2) hargsG hgfind hcallG
      have hargsD1 : lookupArgs
          (envExtend (envExtend ([("d1", .i32 s1), ("s1", .i32 0),
            ("s0", .i32 0), ("a", .i32 a), ("b", .i32 b)] : Env)
            "d2" (.i32 s2)) "r" (.i32 s2))
          ["r"] = some [.i32 s2] := by
        simp [lookupArgs, envExtend, envLookup]
      have hcallD1 := evalFuncFuel_accDtor F s2
      have hstepD1 := evalProgStmt_callRet_ok moveProg F "u1"
        "_ZN3AccD2Ev" ["r"]
        (envExtend (envExtend ([("d1", .i32 s1), ("s1", .i32 0),
          ("s0", .i32 0), ("a", .i32 a), ("b", .i32 b)] : Env)
          "d2" (.i32 s2)) "r" (.i32 s2))
        [.i32 s2] accDtorFunc (.i32 s2) hargsD1 hdfind hcallD1
      have hargsD2 : lookupArgs
          (envExtend (envExtend (envExtend ([("d1", .i32 s1),
            ("s1", .i32 0), ("s0", .i32 0),
            ("a", .i32 a), ("b", .i32 b)] : Env)
            "d2" (.i32 s2)) "r" (.i32 s2)) "u1" (.i32 s2))
          ["s1"] = some [.i32 0] := by
        simp [lookupArgs, envExtend, envLookup,
          show ("s1" : String) ≠ "d1" by decide]
      have hcallD2 := evalFuncFuel_accDtor F 0
      have hstepD2 := evalProgStmt_callRet_ok moveProg F "u2"
        "_ZN3AccD2Ev" ["s1"]
        (envExtend (envExtend (envExtend ([("d1", .i32 s1),
          ("s1", .i32 0), ("s0", .i32 0),
          ("a", .i32 a), ("b", .i32 b)] : Env)
          "d2" (.i32 s2)) "r" (.i32 s2)) "u1" (.i32 s2))
        [.i32 0] accDtorFunc (.i32 0) hargsD2 hdfind hcallD2
      have hexprR : evalExpr (.var "r")
          (envExtend (envExtend (envExtend (envExtend
            ([("d1", .i32 s1), ("s1", .i32 0), ("s0", .i32 0),
              ("a", .i32 a), ("b", .i32 b)] : Env)
            "d2" (.i32 s2)) "r" (.i32 s2)) "u1" (.i32 s2))
            "u2" (.i32 0)) =
          .ok (.i32 s2) := by
        simp [evalExpr, envExtend, envLookup]
      have hstepR := evalProgStmt_return moveProg F (.var "r")
        (envExtend (envExtend (envExtend (envExtend
          ([("d1", .i32 s1), ("s1", .i32 0), ("s0", .i32 0),
            ("a", .i32 a), ("b", .i32 b)] : Env)
          "d2" (.i32 s2)) "r" (.i32 s2)) "u1" (.i32 s2))
          "u2" (.i32 0))
        (.i32 s2) hexprR
      have hsum : moveAccFwd a b = .ok (.i32 s2) := by
        simp only [moveAccFwd_is_moveAcc, moveAcc_ok a b s1 s2 h1 h2,
          i32_map_ok]
      simp only [evalProgFunc, hbind, hbody, evalProgStmt_cleanup]
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep0,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep1,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepM,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepA,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstep2,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepG,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepD1,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepD2,
        hstepR]
      simp [hsum]
