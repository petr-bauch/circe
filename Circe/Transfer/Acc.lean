/-
Circe.Transfer.Acc — M3d C++ transfers: `Acc` leaves and `box_through`.
Over `Circe.Transfer.Slice`.
-/
import Circe.Transfer.Slice

/-! ## M3d C++ transfers: `Acc` leaves (N1b) -/

/-- `memEval` for the ctor leaf (mirrors `evalFuncFuel_accCtor`). -/
theorem memEvalFuncFuel_accCtor (F : Nat) :
    memEvalFuncFuel F accCtorFunc [] = accCtorFwd := by
  have hbind : bindMemArgs accCtorFunc.args [] emptyMem =
      some (([] : Env), emptyMem, []) := rfl
  have hbody : accCtorFunc.body = .return_ (.lit (.i32 0)) := rfl
  have hexpr : memEvalExpr (.lit (.i32 0)) ([] : Env) emptyMem [] =
      .ok (.i32 0) := rfl
  have heval : evalExpr (.lit (.i32 0)) ([] : Env) = .ok (.i32 0) := rfl
  have hret : memEvalStmtFuel F (.return_ (.lit (.i32 0))) ([] : Env)
      emptyMem [] =
      .ok ((([] : Env), emptyMem, []), .returned (.i32 0)) :=
    memEvalStmtFuel_return _ _ _ _ _ _ hexpr heval
  simp only [memEvalFuncFuel, hbind, hbody, hret, accCtorFwd, accCtor]

/-- Transfer for the ctor leaf. -/
theorem memTransfer_accCtor (F : Nat) (_h : oracleNoalias accCtorFunc []) :
    memEvalFuncFuel F accCtorFunc [] =
      evalFuncFuel F accCtorFunc [] := by
  rw [memEvalFuncFuel_accCtor, evalFuncFuel_accCtor]

/-- `memEval` for the add leaf (mirrors `evalFuncFuel_accAdd`; ok and
    error paths). -/
theorem memEvalFuncFuel_accAdd (F : Nat) (s v : BitVec 32) :
    memEvalFuncFuel F accAddFunc [.i32 s, .i32 v] = accAddFwd s v := by
  have hbind : bindMemArgs accAddFunc.args [.i32 s, .i32 v] emptyMem =
      some ([("s", .i32 s), ("v", .i32 v)], emptyMem, []) := rfl
  have hbody : accAddFunc.body =
      .return_ (.add (.var "s") (.var "v")) := rfl
  have hs : envLookup ([("s", .i32 s), ("v", .i32 v)] : Env) "s" =
      some (.i32 s) := rfl
  have hv : envLookup ([("s", .i32 s), ("v", .i32 v)] : Env) "v" =
      some (.i32 v) := by
    simp [envLookup, show ("v" : String) ≠ "s" by decide]
  have hadd : memEvalExpr (.add (.var "s") (.var "v"))
      ([("s", .i32 s), ("v", .i32 v)] : Env) emptyMem [] =
      (checkedAddI32 s v).map .i32 := by
    simp only [memEvalExpr, hs, hv]
  have heval : evalExpr (.add (.var "s") (.var "v"))
      ([("s", .i32 s), ("v", .i32 v)] : Env) =
      (checkedAddI32 s v).map .i32 := by
    simp only [evalExpr, hs, hv]
  have hagree : memEvalExpr (.add (.var "s") (.var "v"))
      ([("s", .i32 s), ("v", .i32 v)] : Env) emptyMem [] =
      evalExpr (.add (.var "s") (.var "v"))
        ([("s", .i32 s), ("v", .i32 v)] : Env) := by
    rw [hadd, heval]
  cases h : checkedAddI32 s v with
  | error e =>
    have hadd' : memEvalExpr (.add (.var "s") (.var "v"))
        ([("s", .i32 s), ("v", .i32 v)] : Env) emptyMem [] =
        .error e := by
      rw [hadd, h]
      exact i32_map_error e
    have hret : memEvalStmtFuel F (.return_ (.add (.var "s") (.var "v")))
        ([("s", .i32 s), ("v", .i32 v)] : Env) emptyMem [] = .error e := by
      cases F <;>
        simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, hadd']
    simp only [memEvalFuncFuel, hbind, hbody, hret, accAddFwd, h,
      i32_map_error]
  | ok r =>
    have hv'' : evalExpr (.add (.var "s") (.var "v"))
        ([("s", .i32 s), ("v", .i32 v)] : Env) = .ok (.i32 r) := by
      rw [heval, h]
      exact i32_map_ok r
    have hret : memEvalStmtFuel F (.return_ (.add (.var "s") (.var "v")))
        ([("s", .i32 s), ("v", .i32 v)] : Env) emptyMem [] =
        .ok ((([("s", .i32 s), ("v", .i32 v)] : Env), emptyMem, []),
          .returned (.i32 r)) :=
      memEvalStmtFuel_return _ _ _ _ _ _ hagree hv''
    simp only [memEvalFuncFuel, hbind, hbody, hret, accAddFwd, h,
      i32_map_ok]

/-- Transfer for the add leaf. -/
theorem memTransfer_accAdd (F : Nat) (s v : BitVec 32)
    (_h : oracleNoalias accAddFunc [.i32 s, .i32 v]) :
    memEvalFuncFuel F accAddFunc [.i32 s, .i32 v] =
      evalFuncFuel F accAddFunc [.i32 s, .i32 v] := by
  rw [memEvalFuncFuel_accAdd, evalFuncFuel_accAdd]

/-- `memEval` for the getter leaf (mirrors `evalFuncFuel_accGet`). -/
theorem memEvalFuncFuel_accGet (F : Nat) (s : BitVec 32) :
    memEvalFuncFuel F accGetFunc [.i32 s] = accGetFwd s := by
  have hbind : bindMemArgs accGetFunc.args [.i32 s] emptyMem =
      some ([("s", .i32 s)], emptyMem, []) := rfl
  have hbody : accGetFunc.body = .return_ (.var "s") := rfl
  have hexpr : memEvalExpr (.var "s") ([("s", .i32 s)] : Env) emptyMem [] =
      .ok (.i32 s) := rfl
  have heval : evalExpr (.var "s") ([("s", .i32 s)] : Env) =
      .ok (.i32 s) := rfl
  have hret : memEvalStmtFuel F (.return_ (.var "s"))
      ([("s", .i32 s)] : Env) emptyMem [] =
      .ok ((([("s", .i32 s)] : Env), emptyMem, []), .returned (.i32 s)) :=
    memEvalStmtFuel_return _ _ _ _ _ _ hexpr heval
  simp only [memEvalFuncFuel, hbind, hbody, hret, accGetFwd]

/-- Transfer for the getter leaf. -/
theorem memTransfer_accGet (F : Nat) (s : BitVec 32)
    (_h : oracleNoalias accGetFunc [.i32 s]) :
    memEvalFuncFuel F accGetFunc [.i32 s] =
      evalFuncFuel F accGetFunc [.i32 s] := by
  rw [memEvalFuncFuel_accGet, evalFuncFuel_accGet]

/-- `memEval` for the trivial-dtor leaf (mirrors `evalFuncFuel_accDtor`;
    the no-op identity carries the state through). -/
theorem memEvalFuncFuel_accDtor (F : Nat) (t : BitVec 32) :
    memEvalFuncFuel F accDtorFunc [.i32 t] = accDtorFwd t := by
  have hbind : bindMemArgs accDtorFunc.args [.i32 t] emptyMem =
      some ([("t", .i32 t)], emptyMem, []) := rfl
  have hbody : accDtorFunc.body = .return_ (.var "t") := rfl
  have hexpr : memEvalExpr (.var "t") ([("t", .i32 t)] : Env) emptyMem [] =
      .ok (.i32 t) := rfl
  have heval : evalExpr (.var "t") ([("t", .i32 t)] : Env) =
      .ok (.i32 t) := rfl
  have hret : memEvalStmtFuel F (.return_ (.var "t"))
      ([("t", .i32 t)] : Env) emptyMem [] =
      .ok ((([("t", .i32 t)] : Env), emptyMem, []), .returned (.i32 t)) :=
    memEvalStmtFuel_return _ _ _ _ _ _ hexpr heval
  simp only [memEvalFuncFuel, hbind, hbody, hret, accDtorFwd]

/-- Transfer for the trivial-dtor leaf. -/
theorem memTransfer_accDtor (F : Nat) (t : BitVec 32)
    (_h : oracleNoalias accDtorFunc [.i32 t]) :
    memEvalFuncFuel F accDtorFunc [.i32 t] =
      evalFuncFuel F accDtorFunc [.i32 t] := by
  rw [memEvalFuncFuel_accDtor, evalFuncFuel_accDtor]

/-- `memEval` for the `acc_two` entry: program evaluation over `accProg`
    agrees with the delegating forward (mirrors `evalProgFunc_accTwo`;
    the `cleanup` scope sequences on the memory layer by
    `memEvalProgStmt_cleanup`; caller `Mem`/`Layout` stay
    `emptyMem`/`[]` — every leaf is scalar). -/
theorem memEvalProgFunc_accTwo (F : Nat) (a b : BitVec 32) :
    memEvalProgFunc accProg F accTwoFunc [.i32 a, .i32 b] =
      accTwoFwd a b := by
  have hbind : bindMemArgs accTwoFunc.args [.i32 a, .i32 b] emptyMem =
      some ([("a", .i32 a), ("b", .i32 b)], emptyMem, []) := rfl
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
  have hc0call := memEvalFuncFuel_accCtor F
  have hstep0 := memEvalProgStmt_callRet_ok accProg F "s0" "_ZN3AccC2Ev" []
    ([("a", .i32 a), ("b", .i32 b)] : Env) emptyMem [] [] accCtorFunc
    (.i32 0) hargs0 hc0find hc0call
  have hargs1 : lookupArgs
      (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env) "s0" (.i32 0))
      ["s0", "a"] = some [.i32 0, .i32 a] := by
    simp [lookupArgs, envExtend, envLookup,
      show ("a" : String) ≠ "s0" by decide]
  have hadd1 := memEvalFuncFuel_accAdd F 0 a
  cases h1 : checkedAddI32 0 a with
  | error e =>
    have hcall1 : memEvalFuncFuel F accAddFunc [.i32 0, .i32 a] =
        .error e := by
      rw [hadd1]
      exact accAddFwd_err 0 a e h1
    have hstep1 := memEvalProgStmt_callRet_err accProg F "s1" "_ZN3Acc3addEi"
      ["s0", "a"]
      (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env) "s0" (.i32 0))
      emptyMem []
      [.i32 0, .i32 a] accAddFunc e hargs1 ha1find hcall1
    have hsum : accTwoFwd a b = .error e := by
      simp only [accTwoFwd_is_accTwo, accTwo_err_a a b e h1, i32_map_error]
    simp only [memEvalProgFunc, hbind, hbody, memEvalProgStmt_cleanup]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep0,
      memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstep1]
    simp [hsum]
  | ok s1 =>
    have hcall1 : memEvalFuncFuel F accAddFunc [.i32 0, .i32 a] =
        .ok (.i32 s1) := by
      rw [hadd1]
      exact accAddFwd_ok 0 a s1 h1
    have hstep1 := memEvalProgStmt_callRet_ok accProg F "s1" "_ZN3Acc3addEi"
      ["s0", "a"]
      (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env) "s0" (.i32 0))
      emptyMem []
      [.i32 0, .i32 a] accAddFunc (.i32 s1) hargs1 ha1find hcall1
    have hargs2 : lookupArgs
        (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
          "s0" (.i32 0)) "s1" (.i32 s1))
        ["s1", "b"] = some [.i32 s1, .i32 b] := by
      simp [lookupArgs, envExtend, envLookup,
        show ("b" : String) ≠ "s1" by decide,
        show ("b" : String) ≠ "s0" by decide,
        show ("b" : String) ≠ "a" by decide]
    have hadd2 := memEvalFuncFuel_accAdd F s1 b
    cases h2 : checkedAddI32 s1 b with
    | error e =>
      have hcall2 : memEvalFuncFuel F accAddFunc [.i32 s1, .i32 b] =
          .error e := by
        rw [hadd2]
        exact accAddFwd_err s1 b e h2
      have hstep2 := memEvalProgStmt_callRet_err accProg F "s2" "_ZN3Acc3addEi"
        ["s1", "b"]
        (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
          "s0" (.i32 0)) "s1" (.i32 s1))
        emptyMem []
        [.i32 s1, .i32 b] accAddFunc e hargs2 ha1find hcall2
      have hsum : accTwoFwd a b = .error e := by
        simp only [accTwoFwd_is_accTwo, accTwo_err_b a b s1 e h1 h2,
          i32_map_error]
      simp only [memEvalProgFunc, hbind, hbody, memEvalProgStmt_cleanup]
      rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep0,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep1,
        memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstep2]
      simp [hsum]
    | ok s2 =>
      have hcall2 : memEvalFuncFuel F accAddFunc [.i32 s1, .i32 b] =
          .ok (.i32 s2) := by
        rw [hadd2]
        exact accAddFwd_ok s1 b s2 h2
      have hstep2 := memEvalProgStmt_callRet_ok accProg F "s2" "_ZN3Acc3addEi"
        ["s1", "b"]
        (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
          "s0" (.i32 0)) "s1" (.i32 s1))
        emptyMem []
        [.i32 s1, .i32 b] accAddFunc (.i32 s2) hargs2 ha1find hcall2
      have hargs3 : lookupArgs
          (envExtend (envExtend (envExtend
            ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
          ["s2"] = some [.i32 s2] := rfl
      have hgetcall := memEvalFuncFuel_accGet F s2
      have hstep3 := memEvalProgStmt_callRet_ok accProg F "s3" "_ZNK3Acc3getEv"
        ["s2"]
        (envExtend (envExtend (envExtend
          ([("a", .i32 a), ("b", .i32 b)] : Env)
          "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
        emptyMem []
        [.i32 s2] accGetFunc (.i32 s2) hargs3 hgfind hgetcall
      have hargs4 : lookupArgs
          (envExtend (envExtend (envExtend (envExtend
            ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
            "s3" (.i32 s2))
          ["s3"] = some [.i32 s2] := rfl
      have hdtorcall := memEvalFuncFuel_accDtor F s2
      have hstep4 := memEvalProgStmt_callRet_ok accProg F "u" "_ZN3AccD2Ev"
        ["s3"]
        (envExtend (envExtend (envExtend (envExtend
          ([("a", .i32 a), ("b", .i32 b)] : Env)
          "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
          "s3" (.i32 s2))
        emptyMem []
        [.i32 s2] accDtorFunc (.i32 s2) hargs4 hdfind hdtorcall
      have hs3 : memEvalExpr (.var "s3")
          (envExtend (envExtend (envExtend (envExtend (envExtend
            ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
            "s3" (.i32 s2)) "u" (.i32 s2))
          emptyMem [] =
          .ok (.i32 s2) := by
        simp [memEvalExpr, envExtend, envLookup,
          show ("s3" : String) ≠ "u" by decide]
      have hret : memEvalProgStmt accProg F (.return_ (.var "s3"))
          (envExtend (envExtend (envExtend (envExtend (envExtend
            ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
            "s3" (.i32 s2)) "u" (.i32 s2))
          emptyMem [] =
          .ok ((envExtend (envExtend (envExtend (envExtend (envExtend
            ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
            "s3" (.i32 s2)) "u" (.i32 s2),
            emptyMem, []), .returned (.i32 s2)) :=
        memEvalProgStmt_return accProg F (.var "s3") _ _ _ _ hs3
      simp only [memEvalProgFunc, hbind, hbody, memEvalProgStmt_cleanup]
      rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep0,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep1,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep2,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep3,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep4, hret]
      have hok : accTwoFwd a b = .ok (.i32 s2) := by
        simp only [accTwoFwd_is_accTwo, accTwo_ok a b s1 s2 h1 h2,
          i32_map_ok]
      simp [hok]

/-- Transfer for `acc_two` (program level): both sides equal
    `accTwoFwd`. -/
theorem memTransferProg_accTwo (F : Nat) (a b : BitVec 32)
    (_h : oracleNoalias accTwoFunc [.i32 a, .i32 b]) :
    memEvalProgFunc accProg F accTwoFunc [.i32 a, .i32 b] =
      evalProgFunc accProg F accTwoFunc [.i32 a, .i32 b] := by
  rw [memEvalProgFunc_accTwo, evalProgFunc_accTwo]

/-- `memEval` for the move-ctor leaf (mirrors `evalFuncFuel_accMoveCtor`). -/
theorem memEvalFuncFuel_accMoveCtor (F : Nat) (d s : BitVec 32) :
    memEvalFuncFuel F accMoveCtorFunc [.i32 d, .i32 s] =
      accMoveCtorFwd d s := by
  have hbind : bindMemArgs accMoveCtorFunc.args [.i32 d, .i32 s] emptyMem =
      some ([("d", .i32 d), ("s", .i32 s)], emptyMem, []) := rfl
  have hbody : accMoveCtorFunc.body = .return_ (.var "s") := rfl
  have hs : envLookup ([("d", .i32 d), ("s", .i32 s)] : Env) "s" =
      some (.i32 s) := by
    simp [envLookup, show ("s" : String) ≠ "d" by decide]
  have hexpr : memEvalExpr (.var "s") ([("d", .i32 d), ("s", .i32 s)] : Env)
      emptyMem [] = .ok (.i32 s) := by
    simp only [memEvalExpr, hs]
  have heval : evalExpr (.var "s") ([("d", .i32 d), ("s", .i32 s)] : Env) =
      .ok (.i32 s) := by
    simp only [evalExpr, hs]
  have hret : memEvalStmtFuel F (.return_ (.var "s"))
      ([("d", .i32 d), ("s", .i32 s)] : Env) emptyMem [] =
      .ok ((([("d", .i32 d), ("s", .i32 s)] : Env), emptyMem, []),
        .returned (.i32 s)) :=
    memEvalStmtFuel_return _ _ _ _ _ _ hexpr heval
  simp only [memEvalFuncFuel, hbind, hbody, hret, accMoveCtorFwd,
    accMoveCtor, i32_map_ok]

/-- Transfer for the move-ctor leaf. -/
theorem memTransfer_accMoveCtor (F : Nat) (d s : BitVec 32)
    (_h : oracleNoalias accMoveCtorFunc [.i32 d, .i32 s]) :
    memEvalFuncFuel F accMoveCtorFunc [.i32 d, .i32 s] =
      evalFuncFuel F accMoveCtorFunc [.i32 d, .i32 s] := by
  rw [memEvalFuncFuel_accMoveCtor, evalFuncFuel_accMoveCtor]

/-- `memEval` for the `move_acc` entry: program evaluation over
    `moveProg` agrees with the delegating forward (mirrors
    `evalProgFunc_moveAcc`; the source-zeroing `assign` steps on the
    memory layer by `memEvalStmtFuel_assign`, with the literal's
    layer agreement by `rfl`). -/
theorem memEvalProgFunc_moveAcc (F : Nat) (a b : BitVec 32) :
    memEvalProgFunc moveProg F moveAccFunc [.i32 a, .i32 b] =
      moveAccFwd a b := by
  have hbind : bindMemArgs moveAccFunc.args [.i32 a, .i32 b] emptyMem =
      some ([("a", .i32 a), ("b", .i32 b)], emptyMem, []) := rfl
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
  have hc0call := memEvalFuncFuel_accCtor F
  have hstep0 := memEvalProgStmt_callRet_ok moveProg F "s0" "_ZN3AccC2Ev" []
    ([("a", .i32 a), ("b", .i32 b)] : Env) emptyMem [] [] accCtorFunc
    (.i32 0) hargs0 hc0find hc0call
  have hargs1 : lookupArgs
      (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env) "s0" (.i32 0))
      ["s0", "a"] = some [.i32 0, .i32 a] := by
    simp [lookupArgs, envExtend, envLookup,
      show ("a" : String) ≠ "s0" by decide]
  have hadd1 := memEvalFuncFuel_accAdd F 0 a
  cases h1 : checkedAddI32 0 a with
  | error e =>
    have hcall1 : memEvalFuncFuel F accAddFunc [.i32 0, .i32 a] =
        .error e := by
      rw [hadd1]
      exact accAddFwd_err 0 a e h1
    have hstep1 := memEvalProgStmt_callRet_err moveProg F "s1" "_ZN3Acc3addEi"
      ["s0", "a"]
      (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env) "s0" (.i32 0))
      emptyMem []
      [.i32 0, .i32 a] accAddFunc e hargs1 ha1find hcall1
    have hsum : moveAccFwd a b = .error e := by
      simp only [moveAccFwd_is_moveAcc, moveAcc_err_a a b e h1, i32_map_error]
    simp only [memEvalProgFunc, hbind, hbody, memEvalProgStmt_cleanup]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep0,
      memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstep1]
    simp [hsum]
  | ok s1 =>
    have hcall1 : memEvalFuncFuel F accAddFunc [.i32 0, .i32 a] =
        .ok (.i32 s1) := by
      rw [hadd1]
      exact accAddFwd_ok 0 a s1 h1
    have hstep1 := memEvalProgStmt_callRet_ok moveProg F "s1" "_ZN3Acc3addEi"
      ["s0", "a"]
      (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env) "s0" (.i32 0))
      emptyMem []
      [.i32 0, .i32 a] accAddFunc (.i32 s1) hargs1 ha1find hcall1
    have hargsM : lookupArgs
        (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
          "s0" (.i32 0)) "s1" (.i32 s1))
        ["s0", "s1"] = some [.i32 0, .i32 s1] := by
      simp [lookupArgs, envExtend, envLookup]
    have hcallM : memEvalFuncFuel F accMoveCtorFunc [.i32 0, .i32 s1] =
        .ok (.i32 s1) := by
      rw [memEvalFuncFuel_accMoveCtor F 0 s1]
      exact accMoveCtorFwd_is_ok 0 s1
    have hstepM := memEvalProgStmt_callRet_ok moveProg F "d1" "_ZN3AccC2EOS_"
      ["s0", "s1"]
      (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
        "s0" (.i32 0)) "s1" (.i32 s1))
      emptyMem []
      [.i32 0, .i32 s1] accMoveCtorFunc (.i32 s1) hargsM hmfind hcallM
    have hagree0 : memEvalExpr (.lit (.i32 0))
        (envExtend (envExtend (envExtend
          ([("a", .i32 a), ("b", .i32 b)] : Env)
          "s0" (.i32 0)) "s1" (.i32 s1)) "d1" (.i32 s1))
        emptyMem [] =
        evalExpr (.lit (.i32 0))
        (envExtend (envExtend (envExtend
          ([("a", .i32 a), ("b", .i32 b)] : Env)
          "s0" (.i32 0)) "s1" (.i32 s1)) "d1" (.i32 s1)) := rfl
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
    have hstepA : memEvalProgStmt moveProg F
        (.assign "s1" (.lit (.i32 0)))
        (envExtend (envExtend (envExtend
          ([("a", .i32 a), ("b", .i32 b)] : Env)
          "s0" (.i32 0)) "s1" (.i32 s1)) "d1" (.i32 s1))
        emptyMem [] =
        .ok ((([("d1", .i32 s1), ("s1", .i32 0), ("s0", .i32 0),
          ("a", .i32 a), ("b", .i32 b)] : Env), emptyMem, []),
          .fellThrough) :=
      by simp only [memEvalProgStmt]; exact memEvalStmtFuel_assign _ _ _ _ _ _ _ _ hagree0 hexpr0 hupd
    have hargs2 : lookupArgs
        ([("d1", .i32 s1), ("s1", .i32 0), ("s0", .i32 0),
          ("a", .i32 a), ("b", .i32 b)] : Env)
        ["d1", "b"] = some [.i32 s1, .i32 b] := by
      simp [lookupArgs, envLookup,
        show ("b" : String) ≠ "d1" by decide,
        show ("b" : String) ≠ "s1" by decide,
        show ("b" : String) ≠ "s0" by decide,
        show ("b" : String) ≠ "a" by decide]
    have hadd2 := memEvalFuncFuel_accAdd F s1 b
    cases h2 : checkedAddI32 s1 b with
    | error e =>
      have hcall2 : memEvalFuncFuel F accAddFunc [.i32 s1, .i32 b] =
          .error e := by
        rw [hadd2]
        exact accAddFwd_err s1 b e h2
      have hstep2 := memEvalProgStmt_callRet_err moveProg F "d2"
        "_ZN3Acc3addEi" ["d1", "b"]
        ([("d1", .i32 s1), ("s1", .i32 0), ("s0", .i32 0),
          ("a", .i32 a), ("b", .i32 b)] : Env)
        emptyMem []
        [.i32 s1, .i32 b] accAddFunc e hargs2 ha1find hcall2
      have hsum : moveAccFwd a b = .error e := by
        simp only [moveAccFwd_is_moveAcc, moveAcc_err_b a b s1 e h1 h2,
          i32_map_error]
      simp only [memEvalProgFunc, hbind, hbody, memEvalProgStmt_cleanup]
      rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep0,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep1,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepM,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepA,
        memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstep2]
      simp [hsum]
    | ok s2 =>
      have hcall2 : memEvalFuncFuel F accAddFunc [.i32 s1, .i32 b] =
          .ok (.i32 s2) := by
        rw [hadd2]
        exact accAddFwd_ok s1 b s2 h2
      have hstep2 := memEvalProgStmt_callRet_ok moveProg F "d2"
        "_ZN3Acc3addEi" ["d1", "b"]
        ([("d1", .i32 s1), ("s1", .i32 0), ("s0", .i32 0),
          ("a", .i32 a), ("b", .i32 b)] : Env)
        emptyMem []
        [.i32 s1, .i32 b] accAddFunc (.i32 s2) hargs2 ha1find hcall2
      have hargsG : lookupArgs
          (envExtend ([("d1", .i32 s1), ("s1", .i32 0), ("s0", .i32 0),
            ("a", .i32 a), ("b", .i32 b)] : Env) "d2" (.i32 s2))
          ["d2"] = some [.i32 s2] := rfl
      have hgetcall := memEvalFuncFuel_accGet F s2
      have hstepG := memEvalProgStmt_callRet_ok moveProg F "r"
        "_ZNK3Acc3getEv" ["d2"]
        (envExtend ([("d1", .i32 s1), ("s1", .i32 0), ("s0", .i32 0),
          ("a", .i32 a), ("b", .i32 b)] : Env) "d2" (.i32 s2))
        emptyMem []
        [.i32 s2] accGetFunc (.i32 s2) hargsG hgfind hgetcall
      have hargsD1 : lookupArgs
          (envExtend (envExtend ([("d1", .i32 s1), ("s1", .i32 0),
            ("s0", .i32 0), ("a", .i32 a), ("b", .i32 b)] : Env)
            "d2" (.i32 s2)) "r" (.i32 s2))
          ["r"] = some [.i32 s2] := rfl
      have hdtorcall1 := memEvalFuncFuel_accDtor F s2
      have hstepD1 := memEvalProgStmt_callRet_ok moveProg F "u1"
        "_ZN3AccD2Ev" ["r"]
        (envExtend (envExtend ([("d1", .i32 s1), ("s1", .i32 0),
          ("s0", .i32 0), ("a", .i32 a), ("b", .i32 b)] : Env)
          "d2" (.i32 s2)) "r" (.i32 s2))
        emptyMem []
        [.i32 s2] accDtorFunc (.i32 s2) hargsD1 hdfind hdtorcall1
      have hargsD2 : lookupArgs
          (envExtend (envExtend (envExtend ([("d1", .i32 s1),
            ("s1", .i32 0), ("s0", .i32 0),
            ("a", .i32 a), ("b", .i32 b)] : Env)
            "d2" (.i32 s2)) "r" (.i32 s2)) "u1" (.i32 s2))
          ["s1"] = some [.i32 0] := by
        simp [lookupArgs, envExtend, envLookup,
          show ("s1" : String) ≠ "d1" by decide]
      have hdtorcall2 := memEvalFuncFuel_accDtor F 0
      have hstepD2 := memEvalProgStmt_callRet_ok moveProg F "u2"
        "_ZN3AccD2Ev" ["s1"]
        (envExtend (envExtend (envExtend ([("d1", .i32 s1),
          ("s1", .i32 0), ("s0", .i32 0),
          ("a", .i32 a), ("b", .i32 b)] : Env)
          "d2" (.i32 s2)) "r" (.i32 s2)) "u1" (.i32 s2))
        emptyMem []
        [.i32 0] accDtorFunc (.i32 0) hargsD2 hdfind hdtorcall2
      have hexprR : memEvalExpr (.var "r")
          (envExtend (envExtend (envExtend (envExtend
            ([("d1", .i32 s1), ("s1", .i32 0), ("s0", .i32 0),
              ("a", .i32 a), ("b", .i32 b)] : Env)
            "d2" (.i32 s2)) "r" (.i32 s2)) "u1" (.i32 s2))
            "u2" (.i32 0))
          emptyMem [] =
          .ok (.i32 s2) := by
        simp [memEvalExpr, envExtend, envLookup]
      have hstepR : memEvalProgStmt moveProg F (.return_ (.var "r"))
          (envExtend (envExtend (envExtend (envExtend
            ([("d1", .i32 s1), ("s1", .i32 0), ("s0", .i32 0),
              ("a", .i32 a), ("b", .i32 b)] : Env)
            "d2" (.i32 s2)) "r" (.i32 s2)) "u1" (.i32 s2))
            "u2" (.i32 0))
          emptyMem [] =
          .ok ((envExtend (envExtend (envExtend (envExtend
            ([("d1", .i32 s1), ("s1", .i32 0), ("s0", .i32 0),
              ("a", .i32 a), ("b", .i32 b)] : Env)
            "d2" (.i32 s2)) "r" (.i32 s2)) "u1" (.i32 s2))
            "u2" (.i32 0),
            emptyMem, []), .returned (.i32 s2)) :=
        memEvalProgStmt_return moveProg F (.var "r") _ _ _ _ hexprR
      simp only [memEvalProgFunc, hbind, hbody, memEvalProgStmt_cleanup]
      rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep0,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep1,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepM,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepA,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep2,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepG,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepD1,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepD2,
        hstepR]
      have hok : moveAccFwd a b = .ok (.i32 s2) := by
        simp only [moveAccFwd_is_moveAcc, moveAcc_ok a b s1 s2 h1 h2,
          i32_map_ok]
      simp [hok]

/-- Transfer for `move_acc` (program level): both sides equal
    `moveAccFwd`. -/
theorem memTransferProg_moveAcc (F : Nat) (a b : BitVec 32)
    (_h : oracleNoalias moveAccFunc [.i32 a, .i32 b]) :
    memEvalProgFunc moveProg F moveAccFunc [.i32 a, .i32 b] =
      evalProgFunc moveProg F moveAccFunc [.i32 a, .i32 b] := by
  rw [memEvalProgFunc_moveAcc, evalProgFunc_moveAcc]

/-- `memEval` for the `scope_early` entry: program evaluation over
    `earlyProg` agrees with the delegating forward (mirrors
    `evalProgFunc_scopeEarly`; the `if_` steps by
    `memEvalProgStmt_if_true/false` with the `ueq` condition computed
    by one `simp`, the early return short-circuits by
    `memEvalProgStmt_seq_returned`). -/
theorem memEvalProgFunc_scopeEarly (F : Nat) (a b : BitVec 32) :
    memEvalProgFunc earlyProg F scopeEarlyFunc [.i32 a, .i32 b] =
      scopeEarlyFwd a b := by
  have hbind : bindMemArgs scopeEarlyFunc.args [.i32 a, .i32 b] emptyMem =
      some ([("a", .i32 a), ("b", .i32 b)], emptyMem, []) := rfl
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
  have hc0call := memEvalFuncFuel_accCtor F
  have hstep0 := memEvalProgStmt_callRet_ok earlyProg F "s0" "_ZN3AccC2Ev" []
    ([("a", .i32 a), ("b", .i32 b)] : Env) emptyMem [] [] accCtorFunc
    (.i32 0) hargs0 hc0find hc0call
  have hargs1 : lookupArgs
      (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env) "s0" (.i32 0))
      ["s0", "a"] = some [.i32 0, .i32 a] := by
    simp [lookupArgs, envExtend, envLookup,
      show ("a" : String) ≠ "s0" by decide]
  have hadd1 := memEvalFuncFuel_accAdd F 0 a
  have hne2 : ("a" : String) ≠ "s1" := by decide
  have hne3 : ("a" : String) ≠ "s0" := by decide
  have hne4 : ("b" : String) ≠ "s1" := by decide
  have hne5 : ("b" : String) ≠ "s0" := by decide
  cases h1 : checkedAddI32 0 a with
  | error e =>
    have hcall1 : memEvalFuncFuel F accAddFunc [.i32 0, .i32 a] =
        .error e := by
      rw [hadd1]
      exact accAddFwd_err 0 a e h1
    have hstep1 := memEvalProgStmt_callRet_err earlyProg F "s1"
      "_ZN3Acc3addEi" ["s0", "a"]
      (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env) "s0" (.i32 0))
      emptyMem []
      [.i32 0, .i32 a] accAddFunc e hargs1 ha1find hcall1
    have hsum : scopeEarlyFwd a b = .error e := by
      simp only [scopeEarlyFwd_is_scopeEarly, scopeEarly_err_a a b e h1,
        i32_map_error]
    simp only [memEvalProgFunc, hbind, hbody, memEvalProgStmt_cleanup]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep0,
      memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstep1]
    simp [hsum]
  | ok s1 =>
    have hcall1 : memEvalFuncFuel F accAddFunc [.i32 0, .i32 a] =
        .ok (.i32 s1) := by
      rw [hadd1]
      exact accAddFwd_ok 0 a s1 h1
    have hstep1 := memEvalProgStmt_callRet_ok earlyProg F "s1"
      "_ZN3Acc3addEi" ["s0", "a"]
      (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env) "s0" (.i32 0))
      emptyMem []
      [.i32 0, .i32 a] accAddFunc (.i32 s1) hargs1 ha1find hcall1
    by_cases heq : a == b
    · have hcondT : memEvalExpr (.ueq (.var "a") (.var "b"))
          (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1))
          emptyMem [] = .ok (.b true) := by
        simp [memEvalExpr, envExtend, envLookup, hne2, hne3, hne4, hne5, heq]
      have hargsG1 : lookupArgs
          (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1))
          ["s1"] = some [.i32 s1] := rfl
      have hcallG1 := memEvalFuncFuel_accGet F s1
      have hstepG1 := memEvalProgStmt_callRet_ok earlyProg F "r1"
        "_ZNK3Acc3getEv" ["s1"]
        (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
          "s0" (.i32 0)) "s1" (.i32 s1))
        emptyMem []
        [.i32 s1] accGetFunc (.i32 s1) hargsG1 hgfind hcallG1
      have hexprR1 : memEvalExpr (.var "r1")
          (envExtend (envExtend (envExtend
            ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) "r1" (.i32 s1))
          emptyMem [] =
          .ok (.i32 s1) := by
        simp [memEvalExpr, envExtend, envLookup]
      have hstepR1 := memEvalProgStmt_return earlyProg F (.var "r1")
        (envExtend (envExtend (envExtend
          ([("a", .i32 a), ("b", .i32 b)] : Env)
          "s0" (.i32 0)) "s1" (.i32 s1)) "r1" (.i32 s1))
        emptyMem []
        (.i32 s1) hexprR1
      have hthen : memEvalProgStmt earlyProg F
          (.seq (.callRet "r1" "_ZNK3Acc3getEv" ["s1"])
            (.return_ (.var "r1")))
          (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1))
          emptyMem [] =
          .ok (((envExtend (envExtend (envExtend
            ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) "r1" (.i32 s1)),
            emptyMem, []), .returned (.i32 s1)) :=
        Eq.trans (memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
          hstepG1) hstepR1
      have hifT : memEvalProgStmt earlyProg F
          (.if_ (.ueq (.var "a") (.var "b"))
            (.seq (.callRet "r1" "_ZNK3Acc3getEv" ["s1"])
              (.return_ (.var "r1")))
            .skip)
          (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1))
          emptyMem [] =
          .ok (((envExtend (envExtend (envExtend
            ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) "r1" (.i32 s1)),
            emptyMem, []), .returned (.i32 s1)) :=
        Eq.trans (memEvalProgStmt_if_true _ _ _ _ _ _ _ _ hcondT) hthen
      have hsum : scopeEarlyFwd a b = .ok (.i32 s1) := by
        simp only [scopeEarlyFwd_is_scopeEarly,
          scopeEarly_ok_eq a b s1 h1 heq, i32_map_ok]
      simp only [memEvalProgFunc, hbind, hbody, memEvalProgStmt_cleanup]
      rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep0,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep1,
        memEvalProgStmt_seq_returned _ _ _ _ _ _ _ _ _ _ _ hifT]
      simp [hsum]
    · have hne : (a == b) = false := by
        simp [heq]
      have hcondF : memEvalExpr (.ueq (.var "a") (.var "b"))
          (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1))
          emptyMem [] = .ok (.b false) := by
        simp [memEvalExpr, envExtend, envLookup, hne2, hne3, hne4, hne5, hne]
      have hstepSkip : memEvalProgStmt earlyProg F .skip
          (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1))
          emptyMem [] =
          .ok (((envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)), emptyMem, []),
            .fellThrough) := by
        cases F <;> simp [memEvalProgStmt, memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith]
      have hifF : memEvalProgStmt earlyProg F
          (.if_ (.ueq (.var "a") (.var "b"))
            (.seq (.callRet "r1" "_ZNK3Acc3getEv" ["s1"])
              (.return_ (.var "r1")))
            .skip)
          (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1))
          emptyMem [] =
          .ok (((envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)), emptyMem, []),
            .fellThrough) :=
        Eq.trans (memEvalProgStmt_if_false _ _ _ _ _ _ _ _ hcondF) hstepSkip
      have hargs2 : lookupArgs
          (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1))
          ["s1", "b"] = some [.i32 s1, .i32 b] := by
        simp [lookupArgs, envExtend, envLookup,
          show ("b" : String) ≠ "s1" by decide,
          show ("b" : String) ≠ "s0" by decide,
          show ("b" : String) ≠ "a" by decide]
      have hadd2 := memEvalFuncFuel_accAdd F s1 b
      cases h2 : checkedAddI32 s1 b with
      | error e =>
        have hcall2 : memEvalFuncFuel F accAddFunc [.i32 s1, .i32 b] =
            .error e := by
          rw [hadd2]
          exact accAddFwd_err s1 b e h2
        have hstep2 := memEvalProgStmt_callRet_err earlyProg F "s2"
          "_ZN3Acc3addEi" ["s1", "b"]
          (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1))
          emptyMem []
          [.i32 s1, .i32 b] accAddFunc e hargs2 ha1find hcall2
        have hsum : scopeEarlyFwd a b = .error e := by
          simp only [scopeEarlyFwd_is_scopeEarly,
            scopeEarly_err_b a b s1 e h1 hne h2, i32_map_error]
        simp only [memEvalProgFunc, hbind, hbody, memEvalProgStmt_cleanup]
        rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep0,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep1,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hifF,
          memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstep2]
        simp [hsum]
      | ok s2 =>
        have hcall2 : memEvalFuncFuel F accAddFunc [.i32 s1, .i32 b] =
            .ok (.i32 s2) := by
          rw [hadd2]
          exact accAddFwd_ok s1 b s2 h2
        have hstep2 := memEvalProgStmt_callRet_ok earlyProg F "s2"
          "_ZN3Acc3addEi" ["s1", "b"]
          (envExtend (envExtend ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1))
          emptyMem []
          [.i32 s1, .i32 b] accAddFunc (.i32 s2) hargs2 ha1find hcall2
        have hargsG : lookupArgs
            (envExtend (envExtend (envExtend
              ([("a", .i32 a), ("b", .i32 b)] : Env)
              "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
            ["s2"] = some [.i32 s2] := by
          simp [lookupArgs, envExtend, envLookup]
        have hcallG := memEvalFuncFuel_accGet F s2
        have hstepG := memEvalProgStmt_callRet_ok earlyProg F "r"
          "_ZNK3Acc3getEv" ["s2"]
          (envExtend (envExtend (envExtend
            ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
          emptyMem []
          [.i32 s2] accGetFunc (.i32 s2) hargsG hgfind hcallG
        have hargsD : lookupArgs
            (envExtend (envExtend (envExtend (envExtend
              ([("a", .i32 a), ("b", .i32 b)] : Env)
              "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
              "r" (.i32 s2))
            ["r"] = some [.i32 s2] := by
          simp [lookupArgs, envExtend, envLookup]
        have hcallD := memEvalFuncFuel_accDtor F s2
        have hstepD := memEvalProgStmt_callRet_ok earlyProg F "u"
          "_ZN3AccD2Ev" ["r"]
          (envExtend (envExtend (envExtend (envExtend
            ([("a", .i32 a), ("b", .i32 b)] : Env)
            "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
            "r" (.i32 s2))
          emptyMem []
          [.i32 s2] accDtorFunc (.i32 s2) hargsD hdfind hcallD
        have hexprR : memEvalExpr (.var "r")
            (envExtend (envExtend (envExtend (envExtend (envExtend
              ([("a", .i32 a), ("b", .i32 b)] : Env)
              "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
              "r" (.i32 s2)) "u" (.i32 s2))
            emptyMem [] =
            .ok (.i32 s2) := by
          simp [memEvalExpr, envExtend, envLookup]
        have hstepR : memEvalProgStmt earlyProg F (.return_ (.var "r"))
            (envExtend (envExtend (envExtend (envExtend (envExtend
              ([("a", .i32 a), ("b", .i32 b)] : Env)
              "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
              "r" (.i32 s2)) "u" (.i32 s2))
            emptyMem [] =
            .ok ((envExtend (envExtend (envExtend (envExtend (envExtend
              ([("a", .i32 a), ("b", .i32 b)] : Env)
              "s0" (.i32 0)) "s1" (.i32 s1)) "s2" (.i32 s2))
              "r" (.i32 s2)) "u" (.i32 s2),
              emptyMem, []), .returned (.i32 s2)) :=
          memEvalProgStmt_return earlyProg F (.var "r") _ _ _ _ hexprR
        simp only [memEvalProgFunc, hbind, hbody, memEvalProgStmt_cleanup]
        rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep0,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep1,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hifF,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep2,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepG,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepD,
          hstepR]
        have hok : scopeEarlyFwd a b = .ok (.i32 s2) := by
          simp only [scopeEarlyFwd_is_scopeEarly,
            scopeEarly_ok_ne a b s1 s2 h1 hne h2, i32_map_ok]
        simp [hok]

/-- Transfer for `scope_early` (program level): both sides equal
    `scopeEarlyFwd`. -/
theorem memTransferProg_scopeEarly (F : Nat) (a b : BitVec 32)
    (_h : oracleNoalias scopeEarlyFunc [.i32 a, .i32 b]) :
    memEvalProgFunc earlyProg F scopeEarlyFunc [.i32 a, .i32 b] =
      evalProgFunc earlyProg F scopeEarlyFunc [.i32 a, .i32 b] := by
  rw [memEvalProgFunc_scopeEarly, evalProgFunc_scopeEarly]

/-! ## M3d C++ transfers: `box_through` (N1b) -/

/-- `memEval` for `box_through` (mirrors `evalFuncFuel_boxThrough`):
    `new` pins a fresh single-word block, the read cross-checks memory
    against the box value, `delete` consumes both tokens. -/
theorem memEvalFuncFuel_boxThrough (F : Nat) (x : BitVec 32) :
    memEvalFuncFuel F boxThroughFunc [.i32 x] = boxThroughFwd x := by
  have hbind : bindMemArgs boxThroughFunc.args [.i32 x] emptyMem =
      some ([("x", .i32 x)], emptyMem, []) := rfl
  have hbody : boxThroughFunc.body =
      .seq (.let_ "p" (.struct "Box" [.i 32]) (.boxNew (.var "x")))
      (.seq (.let_ "r" (.i 32) (.boxGet "p"))
      (.seq (.boxFree "p")
            (.return_ (.var "r")))) := rfl
  have hstep0 : memEvalStmtFuel F
      (.let_ "p" (.struct "Box" [.i 32]) (.boxNew (.var "x")))
      ([("x", .i32 x)] : Env) emptyMem [] =
      .ok (((("p", .boxVal (⟨x, false⟩ : Box32)) :: [("x", .i32 x)],
        (⟨1, [(0, ⟨0, true, [x]⟩)], []⟩ : Mem), [("p", 0, 0)])),
        .fellThrough) := by
    have h0 := memEvalStmtFuel_let_boxNew F "p" (.struct "Box" [.i 32])
      (.var "x") ([("x", .i32 x)] : Env) emptyMem [] x
      (⟨x, false⟩ : Box32) rfl rfl (boxNew_ok x)
    simpa [memAllocData, emptyMem] using h0
  have hlayV : layoutLookup ([("p", 0, 0)] : Layout) "p" = some (0, 0) :=
    layoutLookup_hit "p" 0 0 []
  have harr : envLookup
      ((("p", .boxVal (⟨x, false⟩ : Box32)) :: [("x", .i32 x)]) : Env)
      "p" = some (.boxVal (⟨x, false⟩ : Box32)) := rfl
  have hfindV : memFind (⟨1, [(0, ⟨0, true, [x]⟩)], []⟩ : Mem) 0 =
      some ⟨0, true, [x]⟩ := by
    simp [memFind]
  have hmem : memLoad (⟨1, [(0, ⟨0, true, [x]⟩)], []⟩ : Mem) 0 0 0 =
      .ok x :=
    memLoad_box_hit _ _ x hfindV
  have hval : boxGet (⟨x, false⟩ : Box32) = .ok x :=
    boxGet_ok _ rfl
  have hagree : memEvalExpr (.boxGet "p")
      ((("p", .boxVal (⟨x, false⟩ : Box32)) :: [("x", .i32 x)]) : Env)
      (⟨1, [(0, ⟨0, true, [x]⟩)], []⟩ : Mem) [("p", 0, 0)] =
      evalExpr (.boxGet "p")
        ((("p", .boxVal (⟨x, false⟩ : Box32)) :: [("x", .i32 x)]) : Env) :=
    memEvalExpr_boxGet_hit "p" _ _ _ _ x 0 0 hlayV harr hmem hval
  have hgetEval : evalExpr (.boxGet "p")
      ((("p", .boxVal (⟨x, false⟩ : Box32)) :: [("x", .i32 x)]) : Env) =
      .ok (.i32 x) :=
    evalExpr_boxGet_hit "p" _ _ x harr hval
  have hget : memEvalExpr (.boxGet "p")
      ((("p", .boxVal (⟨x, false⟩ : Box32)) :: [("x", .i32 x)]) : Env)
      (⟨1, [(0, ⟨0, true, [x]⟩)], []⟩ : Mem) [("p", 0, 0)] =
      .ok (.i32 x) := by
    rw [hagree]
    exact hgetEval
  have hstep1 : memEvalStmtFuel F (.let_ "r" (.i 32) (.boxGet "p"))
      ((("p", .boxVal (⟨x, false⟩ : Box32)) :: [("x", .i32 x)]) : Env)
      (⟨1, [(0, ⟨0, true, [x]⟩)], []⟩ : Mem) [("p", 0, 0)] =
      .ok (((("r", .i32 x) ::
        (("p", .boxVal (⟨x, false⟩ : Box32)) :: [("x", .i32 x)]),
        (⟨1, [(0, ⟨0, true, [x]⟩)], []⟩ : Mem), [("p", 0, 0)])),
        .fellThrough) :=
    memEvalStmtFuel_let_pure F "r" _ _ _ _ _ _
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) hagree hgetEval
  have hfree0 : boxFree (⟨x, false⟩ : Box32) = .ok ⟨x, true⟩ :=
    boxFree_ok _ rfl
  obtain ⟨mFree, hmfree, _hfindFree⟩ := vboxFree_lockstep
    (⟨1, [(0, ⟨0, true, [x]⟩)], []⟩ : Mem) 0 0
    (⟨x, false⟩ : Box32) ⟨0, true, [x]⟩ (⟨x, true⟩ : Box32)
    hfindV rfl rfl rfl rfl hfree0
  have hfreeArr : envLookup
      ((("r", .i32 x) ::
        (("p", .boxVal (⟨x, false⟩ : Box32)) :: [("x", .i32 x)])) : Env)
      "p" = some (.boxVal (⟨x, false⟩ : Box32)) := by
    simp [envLookup, show ("p" : String) ≠ "r" by decide]
  have hfreeLay : layoutLookup ([("p", 0, 0)] : Layout) "p" = some (0, 0) :=
    layoutLookup_hit "p" 0 0 []
  have hfreeUp : envUpdate
      ((("r", .i32 x) ::
        (("p", .boxVal (⟨x, false⟩ : Box32)) :: [("x", .i32 x)])) : Env)
      "p" (.boxVal (⟨x, true⟩ : Box32)) =
      some ((("r", .i32 x) ::
        (("p", .boxVal (⟨x, true⟩ : Box32)) :: [("x", .i32 x)])) : Env) := rfl
  have hstep2 : memEvalStmtFuel F (.boxFree "p")
      ((("r", .i32 x) ::
        (("p", .boxVal (⟨x, false⟩ : Box32)) :: [("x", .i32 x)])) : Env)
      (⟨1, [(0, ⟨0, true, [x]⟩)], []⟩ : Mem) [("p", 0, 0)] =
      .ok (((("r", .i32 x) ::
        (("p", .boxVal (⟨x, true⟩ : Box32)) :: [("x", .i32 x)]),
        mFree, [("p", 0, 0)])), .fellThrough) :=
    memEvalStmtFuel_boxFree F "p" _ _ _ 0 0 _ _ _ mFree
      hfreeArr hfreeLay hfree0 hmfree hfreeUp
  have hret : memEvalStmtFuel F (.return_ (.var "r"))
      ((("r", .i32 x) ::
        (("p", .boxVal (⟨x, true⟩ : Box32)) :: [("x", .i32 x)])) : Env)
      mFree [("p", 0, 0)] =
      .ok (((("r", .i32 x) ::
        (("p", .boxVal (⟨x, true⟩ : Box32)) :: [("x", .i32 x)]),
        mFree, [("p", 0, 0)])), .returned (.i32 x)) := by
    have hv : evalExpr (.var "r")
        ((("r", .i32 x) ::
          (("p", .boxVal (⟨x, true⟩ : Box32)) ::
            [("x", .i32 x)])) : Env) = .ok (.i32 x) := rfl
    exact memEvalStmtFuel_return F _ _ _ _ _ rfl hv
  have hrest : memEvalStmtFuel F
      (.seq (.let_ "r" (.i 32) (.boxGet "p"))
      (.seq (.boxFree "p")
            (.return_ (.var "r"))))
      ((("p", .boxVal (⟨x, false⟩ : Box32)) :: [("x", .i32 x)]) : Env)
      (⟨1, [(0, ⟨0, true, [x]⟩)], []⟩ : Mem) [("p", 0, 0)] =
      .ok (((("r", .i32 x) ::
        (("p", .boxVal (⟨x, true⟩ : Box32)) :: [("x", .i32 x)]),
        mFree, [("p", 0, 0)])), .returned (.i32 x)) :=
    memEvalStmtFuel_seq F _ _ _ _ _ _ _ _ _ _ _ _ hstep1
      (memEvalStmtFuel_seq F _ _ _ _ _ _ _ _ _ _ _ _ hstep2 hret)
  have hfull : memEvalStmtFuel F
      (.seq (.let_ "p" (.struct "Box" [.i 32]) (.boxNew (.var "x")))
      (.seq (.let_ "r" (.i 32) (.boxGet "p"))
      (.seq (.boxFree "p")
            (.return_ (.var "r")))))
      ([("x", .i32 x)] : Env) emptyMem [] =
      .ok (((("r", .i32 x) ::
        (("p", .boxVal (⟨x, true⟩ : Box32)) :: [("x", .i32 x)]),
        mFree, [("p", 0, 0)])), .returned (.i32 x)) :=
    memEvalStmtFuel_seq F _ _ _ _ _ _ _ _ _ _ _ _ hstep0 hrest
  simp only [memEvalFuncFuel, hbind, hbody, hfull]
  have hok : boxThroughFwd x = .ok (.i32 x) := by
    simp only [boxThroughFwd_is_boxThrough, boxThrough_ok, i32_map_ok]
  simp [hok]

/-- Transfer for `box_through`: both sides equal `boxThroughFwd`. -/
theorem memTransfer_boxThrough (F : Nat) (x : BitVec 32)
    (_h : oracleNoalias boxThroughFunc [.i32 x]) :
    memEvalFuncFuel F boxThroughFunc [.i32 x] =
      evalFuncFuel F boxThroughFunc [.i32 x] := by
  rw [memEvalFuncFuel_boxThrough F x, evalFuncFuel_boxThrough F x]

