/-
Circe.Transfer.Flow — M3c loop-free/flow/caller transfers plus N4a/N4c program transfers.
Over `Circe.Transfer.VecHeap`.
-/
import Circe.Transfer.VecHeap

/-! ## M3c loop-free transfers: `choose`, 64-bit widths, `cls`, `translate` -/

/-- Transfer for `choose` (any fuel): the body is a pure `if` over
    functionalized borrows, so memory is untouched and both sides
    select identically. -/
theorem memTransfer_choose (F : Nat) (b : Bool) (x y : BitVec 32)
    (_h : oracleNoalias chooseFunc [.b b, .i32 x, .i32 y]) :
    memEvalFuncFuel F chooseFunc [.b b, .i32 x, .i32 y] =
      evalFuncFuel F chooseFunc [.b b, .i32 x, .i32 y] := by
  have hbf : chooseFunc.args =
      [{ name := "b", ty := .bool, role := .owned },
       { name := "x", ty := .i 32, role := .mutBorrow 0 },
       { name := "y", ty := .i 32, role := .mutBorrow 0 }] := rfl
  have hbody : chooseFunc.body =
      .if_ (.var "b") (.return_ (.var "x")) (.return_ (.var "y")) := rfl
  have hb : bindMemArgs
      [{ name := "b", ty := .bool, role := .owned },
       { name := "x", ty := .i 32, role := .mutBorrow 0 },
       { name := "y", ty := .i 32, role := .mutBorrow 0 }]
      [.b b, .i32 x, .i32 y] emptyMem =
      some ([("b", .b b), ("x", .i32 x), ("y", .i32 y)], emptyMem, []) := rfl
  have hbb : envLookup [("b", .b b), ("x", .i32 x), ("y", .i32 y)] "b" =
      some (.b b) := by simp [envLookup]
  have hx : envLookup [("b", .b b), ("x", .i32 x), ("y", .i32 y)] "x" =
      some (.i32 x) := by
    simp [envLookup, show ("x" : String) ≠ "b" by decide]
  have hy : envLookup [("b", .b b), ("x", .i32 x), ("y", .i32 y)] "y" =
      some (.i32 y) := by
    simp [envLookup, show ("y" : String) ≠ "b" by decide,
      show ("y" : String) ≠ "x" by decide]
  cases b <;> cases F <;>
    simp [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hbody, hb,
      memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      evalStmtFuel, evalStmtZero, evalStmtWith,
      memEvalExpr, evalExpr, hbb, hx, hy]

/-- Transfer for `add64` (any fuel): same pure shape as `add`, at width
    64 through `checkedAddI64`. -/
theorem memTransfer_add64 (F : Nat) (a b : BitVec 64)
    (_h : oracleNoalias add64Func [.i64 a, .i64 b]) :
    memEvalFuncFuel F add64Func [.i64 a, .i64 b] =
      evalFuncFuel F add64Func [.i64 a, .i64 b] := by
  have hbf : add64Func.args =
      [{ name := "a", ty := .i 64, role := .owned },
       { name := "b", ty := .i 64, role := .owned }] := rfl
  have hbody : add64Func.body =
      .return_ (.add (.var "a") (.var "b")) := rfl
  have hb : bindMemArgs
      [{ name := "a", ty := .i 64, role := .owned },
       { name := "b", ty := .i 64, role := .owned }]
      [.i64 a, .i64 b] emptyMem =
      some ([("a", .i64 a), ("b", .i64 b)], emptyMem, []) := rfl
  have ha : envLookup [("a", .i64 a), ("b", .i64 b)] "a" =
      some (.i64 a) := by simp [envLookup]
  have hbb : envLookup [("a", .i64 a), ("b", .i64 b)] "b" =
      some (.i64 b) := by
    simp [envLookup, show ("b" : String) ≠ "a" by decide]
  simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hbody, hb]
  cases F <;>
    simp only [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      evalStmtFuel, evalStmtZero, evalStmtWith, memEvalExpr, evalExpr,
      ha, hbb] <;>
    (cases h : checkedAddI64 a b <;> rfl)

/-- Transfer for `addu64` (any fuel): wrapping unsigned addition never
    fails, so both sides compute the sum directly. -/
theorem memTransfer_addu64 (F : Nat) (a b : BitVec 64)
    (_h : oracleNoalias addu64Func [.u64 a, .u64 b]) :
    memEvalFuncFuel F addu64Func [.u64 a, .u64 b] =
      evalFuncFuel F addu64Func [.u64 a, .u64 b] := by
  have hbf : addu64Func.args =
      [{ name := "a", ty := .u 64, role := .owned },
       { name := "b", ty := .u 64, role := .owned }] := rfl
  have hbody : addu64Func.body =
      .return_ (.uadd (.var "a") (.var "b")) := rfl
  have hb : bindMemArgs
      [{ name := "a", ty := .u 64, role := .owned },
       { name := "b", ty := .u 64, role := .owned }]
      [.u64 a, .u64 b] emptyMem =
      some ([("a", .u64 a), ("b", .u64 b)], emptyMem, []) := rfl
  have ha : envLookup [("a", .u64 a), ("b", .u64 b)] "a" =
      some (.u64 a) := by simp [envLookup]
  have hbb : envLookup [("a", .u64 a), ("b", .u64 b)] "b" =
      some (.u64 b) := by
    simp [envLookup, show ("b" : String) ≠ "a" by decide]
  simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hbody, hb]
  cases F <;>
    simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      evalStmtFuel, evalStmtZero, evalStmtWith,
      memEvalExpr, evalExpr, ha, hbb]

/-! ## N6a transfers: `neg`, `sdiv` -/

/-- Transfer for `neg` (any fuel): same pure shape as `add`, through
    `checkedNegI32`. -/
theorem memTransfer_neg (F : Nat) (x : BitVec 32)
    (_h : oracleNoalias negFunc [.i32 x]) :
    memEvalFuncFuel F negFunc [.i32 x] =
      evalFuncFuel F negFunc [.i32 x] := by
  have hbf : negFunc.args =
      [{ name := "x", ty := .i 32, role := .owned }] := rfl
  have hbody : negFunc.body =
      .return_ (.neg (.var "x")) := rfl
  have hb : bindMemArgs
      [{ name := "x", ty := .i 32, role := .owned }]
      [.i32 x] emptyMem =
      some ([("x", .i32 x)], emptyMem, []) := rfl
  have hx : envLookup [("x", .i32 x)] "x" =
      some (.i32 x) := by simp [envLookup]
  simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hbody, hb]
  cases F <;>
    simp only [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      evalStmtFuel, evalStmtZero, evalStmtWith, memEvalExpr, evalExpr,
      hx] <;>
    (cases h : checkedNegI32 x <;> rfl)

/-- Transfer for `sdiv` (any fuel): same pure shape as `add`, through
    `checkedDivI32` (zero divisor and `INT_MIN / -1` stay loud on both
    sides). -/
theorem memTransfer_sdiv (F : Nat) (a b : BitVec 32)
    (_h : oracleNoalias sdivFunc [.i32 a, .i32 b]) :
    memEvalFuncFuel F sdivFunc [.i32 a, .i32 b] =
      evalFuncFuel F sdivFunc [.i32 a, .i32 b] := by
  have hbf : sdivFunc.args =
      [{ name := "a", ty := .i 32, role := .owned },
       { name := "b", ty := .i 32, role := .owned }] := rfl
  have hbody : sdivFunc.body =
      .return_ (.sdiv (.var "a") (.var "b")) := rfl
  have hb : bindMemArgs
      [{ name := "a", ty := .i 32, role := .owned },
       { name := "b", ty := .i 32, role := .owned }]
      [.i32 a, .i32 b] emptyMem =
      some ([("a", .i32 a), ("b", .i32 b)], emptyMem, []) := rfl
  have ha : envLookup [("a", .i32 a), ("b", .i32 b)] "a" =
      some (.i32 a) := by simp [envLookup]
  have hbb : envLookup [("a", .i32 a), ("b", .i32 b)] "b" =
      some (.i32 b) := by
    simp [envLookup, show ("b" : String) ≠ "a" by decide]
  simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hbody, hb]
  cases F <;>
    simp only [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      evalStmtFuel, evalStmtZero, evalStmtWith, memEvalExpr, evalExpr,
      ha, hbb] <;>
    (cases h : checkedDivI32 a b <;> rfl)

/-- Transfer for `cls` (any fuel): the switch-as-if-chain is pure, so
    memory is untouched and both sides classify identically. -/
theorem memTransfer_cls (F : Nat) (x : BitVec 32)
    (_h : oracleNoalias clsFunc [.u32 x]) :
    memEvalFuncFuel F clsFunc [.u32 x] =
      evalFuncFuel F clsFunc [.u32 x] := by
  have hbf : clsFunc.args =
      [{ name := "x", ty := .u 32, role := .owned }] := rfl
  have hbody : clsFunc.body =
      .if_ (.ueq (.var "x") (.lit (.u32 0)))
        (.return_ (.lit (.u32 10)))
        (.if_ (.ueq (.var "x") (.lit (.u32 1)))
          (.return_ (.lit (.u32 20)))
          (.return_ (.lit (.u32 30)))) := rfl
  have hb : bindMemArgs
      [{ name := "x", ty := .u 32, role := .owned }]
      [.u32 x] emptyMem =
      some ([("x", .u32 x)], emptyMem, []) := rfl
  have hx : envLookup [("x", .u32 x)] "x" = some (.u32 x) := by
    simp [envLookup]
  by_cases h0 : x = 0
  · subst h0
    simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hbody, hb]
    cases F <;>
      simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
        evalStmtFuel, evalStmtZero, evalStmtWith,
        memEvalExpr, evalExpr, litVal, envLookup]
  · have h0' : x ≠ 0#32 := h0
    by_cases h1 : x = 1
    · subst h1
      simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hbody, hb]
      cases F <;>
        simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
          evalStmtFuel, evalStmtZero, evalStmtWith,
          memEvalExpr, evalExpr, litVal, envLookup]
    · have h1' : x ≠ 1#32 := h1
      have e0 : (x == 0#32) = false := by simp [h0']
      have e1 : (x == 1#32) = false := by simp [h1']
      simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hbody, hb]
      cases F <;>
        simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
          evalStmtFuel, evalStmtZero, evalStmtWith,
          memEvalExpr, evalExpr, litVal, envLookup, e0, e1]

/-- Transfer for `cls_fall` (any fuel): the switch-as-if-chain is pure,
    so memory is untouched and both sides classify identically. -/
theorem memTransfer_clsFall (F : Nat) (x : BitVec 32)
    (_h : oracleNoalias clsFallFunc [.u32 x]) :
    memEvalFuncFuel F clsFallFunc [.u32 x] =
      evalFuncFuel F clsFallFunc [.u32 x] := by
  have hbf : clsFallFunc.args =
      [{ name := "x", ty := .u 32, role := .owned }] := rfl
  have hbody : clsFallFunc.body =
      .if_ (.ueq (.var "x") (.lit (.u32 0)))
        (.return_ (.lit (.u32 10)))
        (.if_ (.ueq (.var "x") (.lit (.u32 1)))
          (.return_ (.lit (.u32 10)))
          (.return_ (.lit (.u32 30)))) := rfl
  have hb : bindMemArgs
      [{ name := "x", ty := .u 32, role := .owned }]
      [.u32 x] emptyMem =
      some ([("x", .u32 x)], emptyMem, []) := rfl
  have hx : envLookup [("x", .u32 x)] "x" = some (.u32 x) := by
    simp [envLookup]
  by_cases h0 : x = 0
  · subst h0
    simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hbody, hb]
    cases F <;>
      simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
        evalStmtFuel, evalStmtZero, evalStmtWith,
        memEvalExpr, evalExpr, litVal, envLookup]
  · have h0' : x ≠ 0#32 := h0
    by_cases h1 : x = 1
    · subst h1
      simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hbody, hb]
      cases F <;>
        simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
          evalStmtFuel, evalStmtZero, evalStmtWith,
          memEvalExpr, evalExpr, litVal, envLookup]
    · have h1' : x ≠ 1#32 := h1
      have e0 : (x == 0#32) = false := by simp [h0']
      have e1 : (x == 1#32) = false := by simp [h1']
      simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hbody, hb]
      cases F <;>
        simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
          evalStmtFuel, evalStmtZero, evalStmtWith,
          memEvalExpr, evalExpr, litVal, envLookup, e0, e1]

/-- Transfer for `cls_dense` (any fuel): the 8-deep if-chain is pure,
    so memory is untouched and both sides classify identically. -/
theorem memTransfer_clsDense (F : Nat) (x : BitVec 32)
    (_h : oracleNoalias clsDenseFunc [.u32 x]) :
    memEvalFuncFuel F clsDenseFunc [.u32 x] =
      evalFuncFuel F clsDenseFunc [.u32 x] := by
  have hbf : clsDenseFunc.args =
      [{ name := "x", ty := .u 32, role := .owned }] := rfl
  have hb : bindMemArgs
      [{ name := "x", ty := .u 32, role := .owned }]
      [.u32 x] emptyMem =
      some ([("x", .u32 x)], emptyMem, []) := rfl
  have hx : envLookup [("x", .u32 x)] "x" = some (.u32 x) := by
    simp [envLookup]
  have U : ∀ (F : Nat),
      memEvalFuncFuel F clsDenseFunc [.u32 x] =
        evalFuncFuel F clsDenseFunc [.u32 x] := by
    intro F
    by_cases h0 : x = 0
    · subst h0
      simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hb,
        clsDenseFunc]
      cases F <;>
        simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
          evalStmtFuel, evalStmtZero, evalStmtWith,
          memEvalExpr, evalExpr, litVal, envLookup]
    · have h0' : x ≠ 0#32 := h0
      have e0 : (x == 0#32) = false := by simp [h0']
      by_cases h1 : x = 1
      · subst h1
        simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hb,
          clsDenseFunc]
        cases F <;>
          simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
            evalStmtFuel, evalStmtZero, evalStmtWith,
            memEvalExpr, evalExpr, litVal, envLookup, e0]
      · have h1' : x ≠ 1#32 := h1
        have e1 : (x == 1#32) = false := by simp [h1']
        by_cases h2 : x = 2
        · subst h2
          simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hb,
            clsDenseFunc]
          cases F <;>
            simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
              evalStmtFuel, evalStmtZero, evalStmtWith,
              memEvalExpr, evalExpr, litVal, envLookup, e0, e1]
        · have h2' : x ≠ 2#32 := h2
          have e2 : (x == 2#32) = false := by simp [h2']
          by_cases h3 : x = 3
          · subst h3
            simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hb,
              clsDenseFunc]
            cases F <;>
              simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
                evalStmtFuel, evalStmtZero, evalStmtWith,
                memEvalExpr, evalExpr, litVal, envLookup, e0, e1, e2]
          · have h3' : x ≠ 3#32 := h3
            have e3 : (x == 3#32) = false := by simp [h3']
            by_cases h4 : x = 4
            · subst h4
              simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hb,
                clsDenseFunc]
              cases F <;>
                simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
                  evalStmtFuel, evalStmtZero, evalStmtWith,
                  memEvalExpr, evalExpr, litVal, envLookup, e0, e1, e2, e3]
            · have h4' : x ≠ 4#32 := h4
              have e4 : (x == 4#32) = false := by simp [h4']
              by_cases h5 : x = 5
              · subst h5
                simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hb,
                  clsDenseFunc]
                cases F <;>
                  simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
                    evalStmtFuel, evalStmtZero, evalStmtWith,
                    memEvalExpr, evalExpr, litVal, envLookup,
                    e0, e1, e2, e3, e4]
              · have h5' : x ≠ 5#32 := h5
                have e5 : (x == 5#32) = false := by simp [h5']
                by_cases h6 : x = 6
                · subst h6
                  simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hb,
                    clsDenseFunc]
                  cases F <;>
                    simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
                      evalStmtFuel, evalStmtZero, evalStmtWith,
                      memEvalExpr, evalExpr, litVal, envLookup,
                      e0, e1, e2, e3, e4, e5]
                · have h6' : x ≠ 6#32 := h6
                  have e6 : (x == 6#32) = false := by simp [h6']
                  by_cases h7 : x = 7
                  · subst h7
                    simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hb,
                      clsDenseFunc]
                    cases F <;>
                      simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
                        evalStmtFuel, evalStmtZero, evalStmtWith,
                        memEvalExpr, evalExpr, litVal, envLookup,
                        e0, e1, e2, e3, e4, e5, e6]
                  · have h7' : x ≠ 7#32 := h7
                    have e7 : (x == 7#32) = false := by simp [h7']
                    simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hb,
                      clsDenseFunc]
                    cases F <;>
                      simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
                        evalStmtFuel, evalStmtZero, evalStmtWith,
                        memEvalExpr, evalExpr, litVal, envLookup,
                        e0, e1, e2, e3, e4, e5, e6, e7]
  exact U F

/-- Transfer for `cls_break` (any fuel): guarded assigns over a local
    are pure, so memory is untouched and both sides classify
    identically. -/
theorem memTransfer_clsBreak (F : Nat) (x : BitVec 32)
    (_h : oracleNoalias clsBreakFunc [.u32 x]) :
    memEvalFuncFuel F clsBreakFunc [.u32 x] =
      evalFuncFuel F clsBreakFunc [.u32 x] := by
  have hbf : clsBreakFunc.args =
      [{ name := "x", ty := .u 32, role := .owned }] := rfl
  have hbody : clsBreakFunc.body =
      .seq (.let_ "r" (.u 32) (.lit (.u32 99)))
      (.seq (.if_ (.ueq (.var "x") (.lit (.u32 0)))
               (.assign "r" (.lit (.u32 10)))
               .skip)
      (.seq (.if_ (.ueq (.var "x") (.lit (.u32 1)))
               (.assign "r" (.lit (.u32 20)))
               .skip)
            (.return_ (.var "r")))) := rfl
  have hb : bindMemArgs
      [{ name := "x", ty := .u 32, role := .owned }]
      [.u32 x] emptyMem =
      some ([("x", .u32 x)], emptyMem, []) := rfl
  have hx : envLookup [("x", .u32 x)] "x" = some (.u32 x) := by
    simp [envLookup]
  have hxr : ("x" : String) ≠ "r" := by decide
  by_cases h0 : x = 0
  · subst h0
    have hupd : envUpdate [("r", .u32 99#32), ("x", .u32 0#32)]
        "r" (.u32 10#32) =
        some [(("r", .u32 10#32)), ("x", .u32 0#32)] :=
      envUpdate_hit _ _ _ _
    have hlk : envLookup [(("r", .u32 10#32)), ("x", .u32 0#32)] "x" =
        some (.u32 0#32) := by simp [envLookup, hxr]
    have g01 : (0#32 == 1#32) = false := by decide
    simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hbody, hb]
    cases F <;>
      simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
        evalStmtFuel, evalStmtZero, evalStmtWith,
        memEvalExpr, evalExpr, litVal, envLookup, envExtend,
        hupd, hlk, g01]
  · have h0' : x ≠ 0#32 := h0
    have e0 : (x == 0#32) = false := by simp [h0']
    by_cases h1 : x = 1
    · subst h1
      have hupd : envUpdate [("r", .u32 99#32), ("x", .u32 1#32)]
          "r" (.u32 20#32) =
          some [(("r", .u32 20#32)), ("x", .u32 1#32)] :=
        envUpdate_hit _ _ _ _
      have hlk : envLookup [(("r", .u32 20#32)), ("x", .u32 1#32)] "x" =
          some (.u32 1#32) := by simp [envLookup, hxr]
      simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hbody, hb]
      cases F <;>
        simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
          evalStmtFuel, evalStmtZero, evalStmtWith,
          memEvalExpr, evalExpr, litVal, envLookup, envExtend, e0,
          hupd, hlk]
    · have h1' : x ≠ 1#32 := h1
      have e1 : (x == 1#32) = false := by simp [h1']
      have hlk : envLookup [(("r", .u32 99#32)), ("x", .u32 x)] "x" =
          some (.u32 x) := by simp [envLookup, hxr]
      simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hbody, hb]
      cases F <;>
        simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
          evalStmtFuel, evalStmtZero, evalStmtWith,
          memEvalExpr, evalExpr, litVal, envLookup, envExtend, e0, e1,
          hlk]

/-- Transfer for `cls_add` (any fuel): the `uadd` if-chain is pure,
    so memory is untouched and both sides classify identically. -/
theorem memTransfer_clsAdd (F : Nat) (x y : BitVec 32)
    (_h : oracleNoalias clsAddFunc [.u32 x, .u32 y]) :
    memEvalFuncFuel F clsAddFunc [.u32 x, .u32 y] =
      evalFuncFuel F clsAddFunc [.u32 x, .u32 y] := by
  have hbf : clsAddFunc.args =
      [{ name := "x", ty := .u 32, role := .owned },
       { name := "y", ty := .u 32, role := .owned }] := rfl
  have hbody : clsAddFunc.body =
      .if_ (.ueq (.var "x") (.lit (.u32 0)))
        (.return_ (.uadd (.var "y") (.lit (.u32 1))))
        (.if_ (.ueq (.var "x") (.lit (.u32 1)))
          (.return_ (.uadd (.var "y") (.lit (.u32 2))))
          (.return_ (.var "y"))) := rfl
  have hb : bindMemArgs
      [{ name := "x", ty := .u 32, role := .owned },
       { name := "y", ty := .u 32, role := .owned }]
      [.u32 x, .u32 y] emptyMem =
      some ([("x", .u32 x), ("y", .u32 y)], emptyMem, []) := rfl
  have hx : envLookup [("x", .u32 x), ("y", .u32 y)] "x" =
      some (.u32 x) := envExtend_hit _ _ _
  have hyx : ("y" : String) ≠ "x" := by decide
  have hy : envLookup [("x", .u32 x), ("y", .u32 y)] "y" =
      some (.u32 y) := by simp [envLookup, hyx]
  by_cases h0 : x = 0
  · subst h0
    simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hbody, hb]
    cases F <;>
      simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
        evalStmtFuel, evalStmtZero, evalStmtWith,
        memEvalExpr, evalExpr, litVal, envLookup, hy]
  · have h0' : x ≠ 0#32 := h0
    have e0 : (x == 0#32) = false := by simp [h0']
    by_cases h1 : x = 1
    · subst h1
      simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hbody, hb]
      cases F <;>
        simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
          evalStmtFuel, evalStmtZero, evalStmtWith,
          memEvalExpr, evalExpr, litVal, envLookup, hy, e0]
    · have h1' : x ≠ 1#32 := h1
      have e1 : (x == 1#32) = false := by simp [h1']
      simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hbf, hbody, hb]
      cases F <;>
        simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
          evalStmtFuel, evalStmtZero, evalStmtWith,
          memEvalExpr, evalExpr, litVal, envLookup, hy, e0, e1]

/-- Transfer for `translate` (any fuel): field projection + checked
    adds + struct construction are all pure (the struct crosses by
    value), so memory rides alongside untouched. The `Eval` side reuses
    `evalFuncFuel_translate` + the `translateFwd` bridges; the memory
    side computes directly. -/
theorem memTransfer_translate (F : Nat) (px py dx dy : BitVec 32)
    (_h : oracleNoalias translateFunc
      [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy]) :
    memEvalFuncFuel F translateFunc
      [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy] =
      evalFuncFuel F translateFunc
        [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy] := by
  have hbf : translateFunc.args =
      [{ name := "p", ty := .struct "Point" [.i 32, .i 32], role := .owned },
       { name := "dx", ty := .i 32, role := .owned },
       { name := "dy", ty := .i 32, role := .owned }] := rfl
  have hb : bindMemArgs
      [{ name := "p", ty := .struct "Point" [.i 32, .i 32], role := .owned },
       { name := "dx", ty := .i 32, role := .owned },
       { name := "dy", ty := .i 32, role := .owned }]
      [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy]
      emptyMem =
      some ([("p", .structVal "Point" [("x", px), ("y", py)]),
        ("dx", .i32 dx), ("dy", .i32 dy)], emptyMem, []) := rfl
  have hbody : translateFunc.body =
      .seq (.let_ "qx" (.i 32) (.add (.fget "p" "x") (.var "dx")))
      (.seq (.let_ "qy" (.i 32) (.add (.fget "p" "y") (.var "dy")))
            (.return_ (.pmk (.var "qx") (.var "qy")))) := rfl
  have hp : envLookup [("p", .structVal "Point" [("x", px), ("y", py)]),
      ("dx", .i32 dx), ("dy", .i32 dy)] "p" =
      some (.structVal "Point" [("x", px), ("y", py)]) := by
    simp [envLookup]
  have hdx : envLookup [("p", .structVal "Point" [("x", px), ("y", py)]),
      ("dx", .i32 dx), ("dy", .i32 dy)] "dx" = some (.i32 dx) := by
    simp [envLookup, show ("dx" : String) ≠ "p" by decide]
  have hdy : envLookup [("p", .structVal "Point" [("x", px), ("y", py)]),
      ("dx", .i32 dx), ("dy", .i32 dy)] "dy" = some (.i32 dy) := by
    simp [envLookup, show ("dy" : String) ≠ "p" by decide,
      show ("dy" : String) ≠ "dx" by decide]
  have hfx : fieldLookup [("x", px), ("y", py)] "x" = some px :=
    fieldLookup_translate_x px py
  have hfy : fieldLookup [("x", px), ("y", py)] "y" = some py :=
    fieldLookup_translate_y px py
  have haddx : memEvalExpr (.add (.fget "p" "x") (.var "dx"))
      [("p", .structVal "Point" [("x", px), ("y", py)]),
        ("dx", .i32 dx), ("dy", .i32 dy)] emptyMem [] =
      (checkedAddI32 px dx).map .i32 :=
    memEvalExpr_add_fget_var _ _ _ _ _ _ _ _ _ _ hp hfx hdx
  cases hx : checkedAddI32 px dx with
  | error e =>
    have haddx' : memEvalExpr (.add (.fget "p" "x") (.var "dx"))
        [("p", .structVal "Point" [("x", px), ("y", py)]),
          ("dx", .i32 dx), ("dy", .i32 dy)] emptyMem [] = .error e := by
      rw [haddx, hx]
      exact i32_map_error e
    have hmem : memEvalFuncFuel F translateFunc
        [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy] =
        .error e := by
      simp only [memEvalFuncFuel, hbf, hbody, hb]
      cases F <;>
        simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, haddx']
    have heval : evalFuncFuel F translateFunc
        [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy] =
        .error e := by
      rw [evalFuncFuel_translate]
      exact translateFwd_err_x _ _ _ _ _ hx
    rw [hmem, heval]
  | ok x' =>
    have haddx' : memEvalExpr (.add (.fget "p" "x") (.var "dx"))
        [("p", .structVal "Point" [("x", px), ("y", py)]),
          ("dx", .i32 dx), ("dy", .i32 dy)] emptyMem [] =
        .ok (.i32 x') := by
      rw [haddx, hx]
      exact i32_map_ok x'
    have hobj2 : envLookup (("qx", .i32 x') ::
        [("p", .structVal "Point" [("x", px), ("y", py)]),
          ("dx", .i32 dx), ("dy", .i32 dy)]) "p" =
        some (.structVal "Point" [("x", px), ("y", py)]) := by
      simp [envLookup, show ("p" : String) ≠ "qx" by decide]
    have hvar2 : envLookup (("qx", .i32 x') ::
        [("p", .structVal "Point" [("x", px), ("y", py)]),
          ("dx", .i32 dx), ("dy", .i32 dy)]) "dy" = some (.i32 dy) := by
      simp [envLookup, show ("dy" : String) ≠ "qx" by decide]
    have haddy : memEvalExpr (.add (.fget "p" "y") (.var "dy"))
        (("qx", .i32 x') ::
        [("p", .structVal "Point" [("x", px), ("y", py)]),
          ("dx", .i32 dx), ("dy", .i32 dy)]) emptyMem [] =
        (checkedAddI32 py dy).map .i32 :=
      memEvalExpr_add_fget_var _ _ _ _ _ _ _ _ _ _ hobj2 hfy hvar2
    cases hy : checkedAddI32 py dy with
    | error e =>
      have haddy' : memEvalExpr (.add (.fget "p" "y") (.var "dy"))
          (("qx", .i32 x') ::
          [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)]) emptyMem [] =
          .error e := by
        rw [haddy, hy]
        exact i32_map_error e
      have hmem : memEvalFuncFuel F translateFunc
          [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy] =
          .error e := by
        simp only [memEvalFuncFuel, hbf, hbody, hb]
        cases F <;>
          simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
            haddx', haddy']
      have heval : evalFuncFuel F translateFunc
          [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy] =
          .error e := by
        rw [evalFuncFuel_translate]
        exact translateFwd_err_y _ _ _ _ _ _ hx hy
      rw [hmem, heval]
    | ok y' =>
      have haddy' : memEvalExpr (.add (.fget "p" "y") (.var "dy"))
          (("qx", .i32 x') ::
          [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)]) emptyMem [] =
          .ok (.i32 y') := by
        rw [haddy, hy]
        exact i32_map_ok y'
      have hqx : evalExpr (.var "qx")
          (("qy", .i32 y') :: ("qx", .i32 x') ::
          [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)]) = .ok (.i32 x') := by
        simp [evalExpr, envLookup, show ("qx" : String) ≠ "qy" by decide]
      have hqy : evalExpr (.var "qy")
          (("qy", .i32 y') :: ("qx", .i32 x') ::
          [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)]) = .ok (.i32 y') := by
        simp [evalExpr, envLookup]
      have hpmk : memEvalExpr (.pmk (.var "qx") (.var "qy"))
          (("qy", .i32 y') :: ("qx", .i32 x') ::
          [("p", .structVal "Point" [("x", px), ("y", py)]),
            ("dx", .i32 dx), ("dy", .i32 dy)]) emptyMem [] =
          .ok (.structVal "Point" [("x", x'), ("y", y')]) := by
        have e1 : envLookup
            (("qy", .i32 y') :: ("qx", .i32 x') ::
            [("p", .structVal "Point" [("x", px), ("y", py)]),
              ("dx", .i32 dx), ("dy", .i32 dy)]) "qx" =
            some (.i32 x') := by
          simp [envLookup, show ("qx" : String) ≠ "qy" by decide]
        have e2 : envLookup
            (("qy", .i32 y') :: ("qx", .i32 x') ::
            [("p", .structVal "Point" [("x", px), ("y", py)]),
              ("dx", .i32 dx), ("dy", .i32 dy)]) "qy" =
            some (.i32 y') := by
          simp [envLookup]
        simp [memEvalExpr, e1, e2]
      have hmem : memEvalFuncFuel F translateFunc
          [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy] =
          .ok (.structVal "Point" [("x", x'), ("y", y')]) := by
        simp only [memEvalFuncFuel, hbf, hbody, hb]
        cases F <;>
          simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
            haddx', haddy', hpmk]
      have heval : evalFuncFuel F translateFunc
          [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy] =
          .ok (.structVal "Point" [("x", x'), ("y", y')]) := by
        rw [evalFuncFuel_translate]
        exact translateFwd_ok_bridge _ _ _ _ _ _ hx hy
      rw [hmem, heval]

/-! ## M3c flow transfers: `nested_sum`, `skip_sum` (scalar loops) -/

/-- Inner condition on memory reads `j` against `m` (pure, memory
    untouched — mirrors `nestedCondInner_eval`). -/
theorem memNestedCondInner_eval (nv mv : BitVec 32) (k t : Nat)
    (acc : BitVec 32) (m : Mem) (π : Layout) (h : t < 2 ^ 32) :
    memEvalExpr (.ult (.var "j") (.var "m")) (mkNestedEnv nv mv k acc t)
      m π =
      .ok (.b (decide (t < mv.toNat))) := by
  have hj := mkNestedEnv_j nv mv k acc t
  have hm := mkNestedEnv_m nv mv k acc t
  simp only [memEvalExpr, hj, hm, ofNat32_ult t mv h]

/-- Outer condition on memory reads `i` against `n` (pure — mirrors
    `nestedCondOuter_eval`). -/
theorem memNestedCondOuter_eval (nv mv : BitVec 32) (k t : Nat)
    (acc : BitVec 32) (m : Mem) (π : Layout) (h : k < 2 ^ 32) :
    memEvalExpr (.ult (.var "i") (.var "n")) (mkNestedEnv nv mv k acc t)
      m π =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkNestedEnv_i nv mv k acc t
  have hn := mkNestedEnv_n nv mv k acc t
  simp only [memEvalExpr, hi, hn, ofNat32_ult k nv h]

/-- One memory inner step advances `j` and accumulates `ofNat (k*t)`
    (any fuel: loop-free), with `Mem`/`Layout` untouched — mirrors
    `nestedBodyInner_eval`. -/
theorem memNestedBodyInner_eval (F : Nat) (nv mv : BitVec 32)
    (k t : Nat) (acc : BitVec 32) (m : Mem) (π : Layout) :
    memEvalStmtFuel F nestedBodyInner (mkNestedEnv nv mv k acc t) m π =
      .ok ((mkNestedEnv nv mv k
        (acc + BitVec.ofNat 32 (k * t)) (t + 1), m, π), .fellThrough) := by
  have hs : memEvalExpr (.uadd (.var "s") (.umul (.var "i") (.var "j")))
        (mkNestedEnv nv mv k acc t) m π =
        .ok (.u32 (acc + BitVec.ofNat 32 (k * t))) := by
    have h1 := mkNestedEnv_s nv mv k acc t
    have hii := mkNestedEnv_i nv mv k acc t
    have hj := mkNestedEnv_j nv mv k acc t
    simp only [memEvalExpr, h1, hii, hj, ofNat32_mul]
  have hj2 : memEvalExpr (.uadd (.var "j") (.lit (.u32 (BitVec.ofNat 32 1))))
        (mkNestedEnv nv mv k (acc + BitVec.ofNat 32 (k * t)) t) m π =
        .ok (.u32 (BitVec.ofNat 32 (t + 1))) := by
    have hj := mkNestedEnv_j nv mv k (acc + BitVec.ofNat 32 (k * t)) t
    simp only [memEvalExpr, litVal, hj, ofNat32_add_one]
  have up1 := nestedEnv_update_s nv mv k t acc
    (acc + BitVec.ofNat 32 (k * t))
  have up2 := nestedEnv_update_j nv mv k t (t + 1)
    (acc + BitVec.ofNat 32 (k * t))
  cases F <;>
    simp only [nestedBodyInner, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtWith, hs, hj2, up1, up2]

/-- Memory inner loop correctness: folds the row suffix, leaving
    `Mem`/`Layout` untouched — mirrors `nestedInner_correct`. -/
theorem memNestedInner_correct (nv mv : BitVec 32)
    (F k t : Nat) (acc : BitVec 32) (m : Mem) (π : Layout)
    (ht32 : t ≤ mv.toNat) (ht2 : t < 2 ^ 32) (hm : mv.toNat < 2 ^ 32)
    (hF : mv.toNat - t ≤ F) :
    memEvalStmtFuel F nestedInner (mkNestedEnv nv mv k acc t) m π =
      .ok (((mkNestedEnv nv mv k
        (acc + rowSuffixU32 k t mv.toNat) mv.toNat, m, π)),
        .fellThrough) := by
  induction F generalizing t acc with
  | zero =>
    have htt : t = mv.toNat := by omega
    subst htt
    have hcond : memEvalExpr (.ult (.var "j") (.var "m"))
          (mkNestedEnv nv mv k acc mv.toNat) m π = .ok (.b false) := by
      simpa using
        (memNestedCondInner_eval nv mv k mv.toNat acc m π
          (by omega : mv.toNat < 2 ^ 32))
    have hnil := rowSuffix_nil k mv.toNat
    simp [nestedInner, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtZeroHandler, memEvalStmtWith, hcond, hnil,
      BitVec.add_zero]
  | succ F ih =>
    by_cases hlt : t < mv.toNat
    · have hcond : memEvalExpr (.ult (.var "j") (.var "m"))
          (mkNestedEnv nv mv k acc t) m π = .ok (.b true) := by
        simpa [hlt] using (memNestedCondInner_eval nv mv k t acc m π ht2)
      have hbody := memNestedBodyInner_eval F nv mv k t acc m π
      have hstep : memEvalStmtFuel (F + 1) nestedInner
            (mkNestedEnv nv mv k acc t) m π
          = memEvalStmtFuel F nestedInner
            (mkNestedEnv nv mv k (acc + BitVec.ofNat 32 (k * t)) (t + 1))
            m π := by
        simp [nestedInner, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond, hbody]
      rw [hstep]
      have hrec := ih (t + 1) (acc + BitVec.ofNat 32 (k * t))
        (by omega) (by omega) (by omega)
      rw [hrec]
      have hrow := rowSuffix_step k t mv.toNat hlt
      have hacc : (acc + BitVec.ofNat 32 (k * t)) +
            rowSuffixU32 k (t + 1) mv.toNat
          = acc + rowSuffixU32 k t mv.toNat := by
        rw [hrow]; exact BitVec.add_assoc _ _ _
      rw [hacc]
    · have htt : t = mv.toNat := by omega
      subst htt
      have hcond : memEvalExpr (.ult (.var "j") (.var "m"))
            (mkNestedEnv nv mv k acc mv.toNat) m π = .ok (.b false) := by
        simpa using
          (memNestedCondInner_eval nv mv k mv.toNat acc m π
            (by omega : mv.toNat < 2 ^ 32))
      have hnil := rowSuffix_nil k mv.toNat
      simp [nestedInner, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith, hcond, hnil, BitVec.add_zero]

/-- Memory outer body: run the inner loop, step `i`, reset `j` —
    mirrors `nestedBodyOuter_eval` (one inner fact covers all fuels). -/
theorem memNestedBodyOuter_eval (F : Nat) (nv mv : BitVec 32)
    (k : Nat) (acc : BitVec 32) (m : Mem) (π : Layout)
    (hmF : mv.toNat ≤ F)
    (hm32 : mv.toNat < 2 ^ 32) :
    memEvalStmtFuel F nestedBodyOuter (mkNestedEnv nv mv k acc 0) m π =
      .ok (((mkNestedEnv nv mv (k + 1) (acc + rowU32 k mv.toNat) 0,
        m, π)), .fellThrough) := by
  have hinner : memEvalStmtFuel F nestedInner (mkNestedEnv nv mv k acc 0)
        m π =
        .ok (((mkNestedEnv nv mv k (acc + rowU32 k mv.toNat) mv.toNat,
          m, π)), .fellThrough) := by
    have h := memNestedInner_correct nv mv F k 0 acc m π
      (Nat.zero_le _) (by omega) hm32 (by omega)
    rwa [rowSuffix_full] at h
  have hincr : memEvalExpr (.uadd (.var "i") (.lit (.u32 (BitVec.ofNat 32 1))))
        (mkNestedEnv nv mv k (acc + rowU32 k mv.toNat) mv.toNat) m π =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have hii := mkNestedEnv_i nv mv k (acc + rowU32 k mv.toNat) mv.toNat
    simp only [memEvalExpr, litVal, hii, ofNat32_add_one]
  have up1 := nestedEnv_update_i nv mv k (k + 1) mv.toNat
    (acc + rowU32 k mv.toNat)
  have hreset : memEvalExpr (.lit (.u32 (BitVec.ofNat 32 0)))
        (mkNestedEnv nv mv (k + 1) (acc + rowU32 k mv.toNat) mv.toNat)
        m π =
        .ok (.u32 (BitVec.ofNat 32 0)) := rfl
  have up0 := nestedEnv_update_j nv mv (k + 1) mv.toNat 0
    (acc + rowU32 k mv.toNat)
  cases F with
  | zero =>
    have hinner0 : memEvalStmtWith memEvalStmtZeroHandler
          nestedInner (mkNestedEnv nv mv k acc 0) m π =
          .ok (((mkNestedEnv nv mv k (acc + rowU32 k mv.toNat) mv.toNat,
            m, π)), .fellThrough) := hinner
    simp [nestedBodyOuter, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtWith, hinner0, hincr, up1, hreset, up0]
  | succ F =>
    have hinnerS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          nestedInner (mkNestedEnv nv mv k acc 0) m π =
          .ok (((mkNestedEnv nv mv k (acc + rowU32 k mv.toNat) mv.toNat,
            m, π)), .fellThrough) := hinner
    simp [nestedBodyOuter, memEvalStmtFuel, memEvalStmtWith,
      hinnerS, hincr, up1, hreset, up0]

/-- Memory outer loop correctness: folds the nest suffix — mirrors
    `nestedOuter_correct` (one outer iteration costs `m+1` fuel). -/
theorem memNestedOuter_correct (nv mv : BitVec 32)
    (F k : Nat) (acc : BitVec 32) (m : Mem) (π : Layout)
    (hk : k ≤ nv.toNat) (hn : nv.toNat < 2 ^ 32) (hm : mv.toNat < 2 ^ 32)
    (hF : (nv.toNat - k) * (mv.toNat + 1) ≤ F) :
    memEvalStmtFuel F nestedOuter (mkNestedEnv nv mv k acc 0) m π =
      .ok (((mkNestedEnv nv mv nv.toNat
        (acc + nestSuffixU32 k nv.toNat mv.toNat) 0, m, π)),
        .fellThrough) := by
  induction F generalizing k acc with
  | zero =>
    have hkk : k = nv.toNat := by
      have hpos : 0 < nv.toNat - k ∨ k = nv.toNat := by omega
      rcases hpos with hpos | hkk
      · have hge := Nat.le_mul_of_pos_left (mv.toNat + 1) hpos
        omega
      · exact hkk
    subst hkk
    have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
          (mkNestedEnv nv mv nv.toNat acc 0) m π = .ok (.b false) := by
      simpa using (memNestedCondOuter_eval nv mv nv.toNat 0 acc m π hn)
    have hnil := nestSuffix_nil nv.toNat nv.toNat mv.toNat (Nat.le_refl _)
    simp [nestedOuter, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtZeroHandler, memEvalStmtWith, hcond, hnil,
      BitVec.add_zero]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
            (mkNestedEnv nv mv k acc 0) m π = .ok (.b true) := by
        simpa [hlt] using (memNestedCondOuter_eval nv mv k 0 acc m π hk32)
      have hbody := memNestedBodyOuter_eval F nv mv k acc m π
        (by have hge := Nat.le_mul_of_pos_left (mv.toNat + 1)
              (show 0 < nv.toNat - k by omega)
            omega)
        hm
      have hstep : memEvalStmtFuel (F + 1) nestedOuter
            (mkNestedEnv nv mv k acc 0) m π
          = memEvalStmtFuel F nestedOuter
            (mkNestedEnv nv mv (k + 1) (acc + rowU32 k mv.toNat) 0) m π := by
        simp [nestedOuter, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond, hbody]
      rw [hstep]
      have hsplit : (nv.toNat - k) * (mv.toNat + 1)
          = (nv.toNat - (k + 1)) * (mv.toNat + 1) + (mv.toNat + 1) := by
        have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
        rw [hkk1, Nat.add_mul, Nat.one_mul]
      have hrec := ih (k + 1) (acc + rowU32 k mv.toNat)
        (by omega)
        (show (nv.toNat - (k + 1)) * (mv.toNat + 1) ≤ F by omega)
      rw [hrec]
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      have hnest := nestSuffix_step k nv.toNat mv.toNat hlt
      have hacc : (acc + rowU32 k mv.toNat) +
            nestSuffixU32 (k + 1) nv.toNat mv.toNat
          = acc + nestSuffixU32 k nv.toNat mv.toNat := by
        rw [hnest]; exact BitVec.add_assoc _ _ _
      rw [hacc]
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
            (mkNestedEnv nv mv nv.toNat acc 0) m π = .ok (.b false) := by
        simpa using (memNestedCondOuter_eval nv mv nv.toNat 0 acc m π hn)
      have hnil := nestSuffix_nil nv.toNat nv.toNat mv.toNat (Nat.le_refl _)
      simp [nestedOuter, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith, hcond, hnil, BitVec.add_zero]

/-- `memEval` for `nested_sum`, fuel-generalized — mirrors
    `evalFuncFuel_nested` (memory rides alongside, untouched). -/
theorem memEvalFuncFuel_nested (F : Nat) (nv mv : BitVec 32)
    (hn : nv.toNat < 2 ^ 32) (hm : mv.toNat < 2 ^ 32)
    (hF : nv.toNat * (mv.toNat + 1) ≤ F) :
    memEvalFuncFuel F nestedFunc [.u32 nv, .u32 mv] = nestedFwd nv mv := by
  have hbf : nestedFunc.args =
      [{ name := "n", ty := .u 32, role := .owned },
       { name := "m", ty := .u 32, role := .owned }] := rfl
  have hbody : nestedFunc.body =
      .seq (.let_ "s" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
      (.seq (.let_ "i" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
      (.seq (.let_ "j" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
      (.seq nestedOuter
            (.return_ (.var "s"))))) := rfl
  have hb : bindMemArgs
      [{ name := "n", ty := .u 32, role := .owned },
       { name := "m", ty := .u 32, role := .owned }]
      [.u32 nv, .u32 mv] emptyMem =
      some ([("n", .u32 nv), ("m", .u32 mv)], emptyMem, []) := rfl
  have henv : [("j", .u32 (BitVec.ofNat 32 0)),
        ("i", .u32 (BitVec.ofNat 32 0)),
        ("s", .u32 (BitVec.ofNat 32 0)),
        ("n", .u32 nv), ("m", .u32 mv)]
      = mkNestedEnv nv mv 0 (BitVec.ofNat 32 0) 0 := rfl
  have hfull := nestSuffix_full nv.toNat mv.toNat
  have hsret : envLookup
        (mkNestedEnv nv mv nv.toNat (nestedSumU32 nv.toNat mv.toNat) 0)
        "s" = some (.u32 (nestedSumU32 nv.toNat mv.toNat)) :=
    mkNestedEnv_s nv mv nv.toNat (nestedSumU32 nv.toNat mv.toNat) 0
  have hret : memEvalExpr (.var "s")
      (mkNestedEnv nv mv nv.toNat (nestedSumU32 nv.toNat mv.toNat) 0)
      emptyMem [] = .ok (.u32 (nestedSumU32 nv.toNat mv.toNat)) := by
    simp [memEvalExpr, hsret]
  cases F with
  | zero =>
    have hloopH0 : memEvalStmtWith memEvalStmtZeroHandler
          nestedOuter (mkNestedEnv nv mv 0 (BitVec.ofNat 32 0) 0)
          emptyMem [] =
        .ok (((mkNestedEnv nv mv nv.toNat
            (BitVec.ofNat 32 0 + nestSuffixU32 0 nv.toNat mv.toNat) 0,
            emptyMem, [])), .fellThrough) :=
      memNestedOuter_correct nv mv 0 0 (BitVec.ofNat 32 0) emptyMem []
        (Nat.zero_le _) hn hm (by omega)
    simp only [memEvalFuncFuel, hbf, hbody, hb]
    simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, memEvalExpr,
      litVal, nestedFwd, henv, hloopH0, hsret, hfull, BitVec.zero_add]
  | succ F =>
    have hloopS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          nestedOuter (mkNestedEnv nv mv 0 (BitVec.ofNat 32 0) 0)
          emptyMem [] =
        .ok (((mkNestedEnv nv mv nv.toNat
            (BitVec.ofNat 32 0 + nestSuffixU32 0 nv.toNat mv.toNat) 0,
            emptyMem, [])), .fellThrough) :=
      memNestedOuter_correct nv mv (F + 1) 0 (BitVec.ofNat 32 0) emptyMem []
        (Nat.zero_le _) hn hm (by omega)
    simp only [memEvalFuncFuel, hbf, hbody, hb]
    simp [memEvalStmtFuel, memEvalStmtWith, memEvalExpr, litVal, nestedFwd,
      henv, hloopS, hsret, hfull, BitVec.zero_add]

/-- Transfer for `nested_sum`: both sides equal `nestedFwd`. -/
theorem memTransfer_nested (F : Nat) (nv mv : BitVec 32)
    (hn : nv.toNat < 2 ^ 32) (hm : mv.toNat < 2 ^ 32)
    (hF : nv.toNat * (mv.toNat + 1) ≤ F)
    (_h : oracleNoalias nestedFunc [.u32 nv, .u32 mv]) :
    memEvalFuncFuel F nestedFunc [.u32 nv, .u32 mv] =
      evalFuncFuel F nestedFunc [.u32 nv, .u32 mv] := by
  rw [memEvalFuncFuel_nested F nv mv hn hm hF,
    evalFuncFuel_nested F nv mv hn hm hF]

/-- Memory loop condition reads the index against the bound — mirrors
    `skipCond_eval` (pure). -/
theorem memSkipCond_eval (nv : BitVec 32) (k : Nat) (acc : BitVec 32)
    (m : Mem) (π : Layout) (h : k < 2 ^ 32) :
    memEvalExpr (.ult (.var "i") (.var "n")) (mkSkipEnv nv k acc) m π =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkSkipEnv_i nv k acc
  have hn := mkSkipEnv_n nv k acc
  simp only [memEvalExpr, hi, hn, ofNat32_ult k nv h]

/-- Memory `ueq` against a const decides `Nat` equality — mirrors
    `skipCond_eq` (pure). -/
theorem memSkipCond_eq (nv : BitVec 32) (k c : Nat) (acc : BitVec 32)
    (m : Mem) (π : Layout) (hk : k < 2 ^ 32) (hc : c < 2 ^ 32) :
    memEvalExpr (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 c))))
      (mkSkipEnv nv k acc) m π = .ok (.b (decide (k = c))) := by
  have hi := mkSkipEnv_i nv k acc
  simp only [memEvalExpr, hi, litVal, ofNat32_beq k c hk hc]

/-- Memory body at `k = 2`: increment, signal `continued` (any fuel) —
    mirrors `skipBody_continue`. -/
theorem memSkipBody_continue (F : Nat) (nv : BitVec 32) (acc : BitVec 32)
    (m : Mem) (π : Layout) :
    memEvalStmtFuel F skipBody (mkSkipEnv nv 2 acc) m π =
      .ok (((mkSkipEnv nv 3 acc, m, π)), .continued) := by
  have hcond1 : memEvalExpr
        (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 2))))
        (mkSkipEnv nv 2 acc) m π = .ok (.b true) := by
    simpa using (memSkipCond_eq nv 2 2 acc m π (by decide) (by decide))
  have hincr : memEvalExpr (.uadd (.var "i") (.lit (.u32 (BitVec.ofNat 32 1))))
        (mkSkipEnv nv 2 acc) m π = .ok (.u32 (BitVec.ofNat 32 3)) := by
    have hi := mkSkipEnv_i nv 2 acc
    have h3 : BitVec.ofNat 32 2 + BitVec.ofNat 32 1
        = BitVec.ofNat 32 3 :=
      ofNat32_add_one 2
    simp only [memEvalExpr, litVal, hi, h3]
  have upi := skipEnv_update_i nv 2 3 acc
  cases F <;>
    simp [skipBody, skipContBranch, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtWith, hcond1, hincr, upi]

/-- Memory body at `k = 8`: signal `broke`, env untouched (any fuel) —
    mirrors `skipBody_break`. -/
theorem memSkipBody_break (F : Nat) (nv : BitVec 32) (acc : BitVec 32)
    (m : Mem) (π : Layout) :
    memEvalStmtFuel F skipBody (mkSkipEnv nv 8 acc) m π =
      .ok (((mkSkipEnv nv 8 acc, m, π)), .broke) := by
  have hcond1 : memEvalExpr
        (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 2))))
        (mkSkipEnv nv 8 acc) m π = .ok (.b false) := by
    have h := memSkipCond_eq nv 8 2 acc m π (by decide) (by decide)
    simpa using h
  have hcond2 : memEvalExpr
        (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 8))))
        (mkSkipEnv nv 8 acc) m π = .ok (.b true) := by
    simpa using (memSkipCond_eq nv 8 8 acc m π (by decide) (by decide))
  cases F <;>
    simp [skipBody, memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      hcond1, hcond2]

/-- Memory body elsewhere: accumulate and step (any fuel) — mirrors
    `skipBody_step`. -/
theorem memSkipBody_step (F : Nat) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) (m : Mem) (π : Layout)
    (hne2 : k ≠ 2) (hne8 : k ≠ 8) (hk32 : k < 2 ^ 32) :
    memEvalStmtFuel F skipBody (mkSkipEnv nv k acc) m π =
      .ok (((mkSkipEnv nv (k + 1) (acc + BitVec.ofNat 32 k), m, π)),
        .fellThrough) := by
  have hcond1 : memEvalExpr
        (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 2))))
        (mkSkipEnv nv k acc) m π = .ok (.b false) := by
    have h := memSkipCond_eq nv k 2 acc m π hk32 (by decide)
    simpa [hne2] using h
  have hcond2 : memEvalExpr
        (.ueq (.var "i") (.lit (.u32 (BitVec.ofNat 32 8))))
        (mkSkipEnv nv k acc) m π = .ok (.b false) := by
    have h := memSkipCond_eq nv k 8 acc m π hk32 (by decide)
    simpa [hne8] using h
  have hs : memEvalExpr (.uadd (.var "s") (.var "i"))
        (mkSkipEnv nv k acc) m π = .ok (.u32 (acc + BitVec.ofNat 32 k)) := by
    have h1 := mkSkipEnv_s nv k acc
    have hii := mkSkipEnv_i nv k acc
    simp only [memEvalExpr, h1, hii]
  have hi2 : memEvalExpr (.uadd (.var "i") (.lit (.u32 (BitVec.ofNat 32 1))))
        (mkSkipEnv nv k (acc + BitVec.ofNat 32 k)) m π =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkSkipEnv_i nv k (acc + BitVec.ofNat 32 k)
    simp only [memEvalExpr, litVal, h1, ofNat32_add_one]
  have up1 := skipEnv_update_s nv k acc (acc + BitVec.ofNat 32 k)
  have up2 := skipEnv_update_i nv k (k + 1) (acc + BitVec.ofNat 32 k)
  cases F <;>
    simp [skipBody, skipTail, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtWith, hcond1, hcond2, hs, hi2, up1, up2]

/-- Memory loop correctness: folds the skip suffix, exits with
    `i = min n 8` — mirrors `skipWhile_correct`. -/
theorem memSkipWhile_correct (nv : BitVec 32)
    (F k : Nat) (acc : BitVec 32) (m : Mem) (π : Layout)
    (hk : k ≤ min nv.toNat 8)
    (hF : min nv.toNat 8 - k + 1 ≤ F) :
    memEvalStmtFuel F skipWhile (mkSkipEnv nv k acc) m π =
      .ok (((mkSkipEnv nv (min nv.toNat 8)
        (acc + skipSuffixU32 k (min nv.toNat 8)), m, π)),
        .fellThrough) := by
  induction F generalizing k acc with
  | zero => omega
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · by_cases h2 : k = 2
      · subst h2
        have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
              (mkSkipEnv nv 2 acc) m π = .ok (.b true) := by
          have hk32 : (2 : Nat) < 2 ^ 32 := by decide
          simpa [hlt] using (memSkipCond_eval nv 2 acc m π hk32)
        have hbody := memSkipBody_continue F nv acc m π
        have hstep : memEvalStmtFuel (F + 1) skipWhile (mkSkipEnv nv 2 acc)
              m π
            = memEvalStmtFuel F skipWhile (mkSkipEnv nv 3 acc) m π := by
          simp [skipWhile, memEvalStmtFuel, memEvalSuccHandler,
            memEvalStmtWith, hcond, hbody]
        rw [hstep]
        have hrec := ih 3 acc (by omega) (by omega)
        rw [hrec]
        have hskip := skipSuffix_skip2 (min nv.toNat 8) (by omega)
        have hacc : acc + skipSuffixU32 3 (min nv.toNat 8)
            = acc + skipSuffixU32 2 (min nv.toNat 8) := by
          rw [hskip]
        rw [hacc]
      · by_cases h8 : k = 8
        · subst h8
          have he : min nv.toNat 8 = 8 := by omega
          have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
                (mkSkipEnv nv 8 acc) m π = .ok (.b true) := by
            have hk32 : (8 : Nat) < 2 ^ 32 := by decide
            simpa [hlt] using (memSkipCond_eval nv 8 acc m π hk32)
          have hbody := memSkipBody_break F nv acc m π
          have hnil8 := skipSuffix_nil 8 8 (Nat.le_refl 8)
          simp [skipWhile, memEvalStmtFuel, memEvalSuccHandler,
            memEvalStmtWith, hcond, hbody, he, hnil8, BitVec.add_zero]
        · have hk32 : k < 2 ^ 32 := by omega
          have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
                (mkSkipEnv nv k acc) m π = .ok (.b true) := by
            simpa [hlt] using (memSkipCond_eval nv k acc m π hk32)
          have hbody := memSkipBody_step F nv k acc m π h2 h8 hk32
          have hstep : memEvalStmtFuel (F + 1) skipWhile (mkSkipEnv nv k acc)
                m π
              = memEvalStmtFuel F skipWhile
                (mkSkipEnv nv (k + 1) (acc + BitVec.ofNat 32 k)) m π := by
            simp [skipWhile, memEvalStmtFuel, memEvalSuccHandler,
              memEvalStmtWith, hcond, hbody]
          rw [hstep]
          have hrec := ih (k + 1) (acc + BitVec.ofNat 32 k)
            (by omega) (by omega)
          rw [hrec]
          have hlt' : k < min nv.toNat 8 := by omega
          have hstep' := skipSuffix_step k (min nv.toNat 8) hlt' h2
          have hacc : (acc + BitVec.ofNat 32 k) +
                skipSuffixU32 (k + 1) (min nv.toNat 8)
              = acc + skipSuffixU32 k (min nv.toNat 8) := by
            rw [hstep']; exact BitVec.add_assoc _ _ _
          rw [hacc]
    · have hkk : k = min nv.toNat 8 := by omega
      subst hkk
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
            (mkSkipEnv nv (min nv.toNat 8) acc) m π = .ok (.b false) := by
        have hfalse : (decide (min nv.toNat 8 < nv.toNat)) = false := by
          have : ¬ min nv.toNat 8 < nv.toNat := by omega
          simp [this]
        have hk32 : min nv.toNat 8 < 2 ^ 32 := by omega
        have h := memSkipCond_eval nv (min nv.toNat 8) acc m π hk32
        rwa [hfalse] at h
      have hnil := skipSuffix_nil (min nv.toNat 8) (min nv.toNat 8)
        (Nat.le_refl _)
      simp [skipWhile, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith, hcond, hnil, BitVec.add_zero]

/-- `memEval` for `skip_sum`, fuel-generalized — mirrors
    `evalFuncFuel_skip`. -/
theorem memEvalFuncFuel_skip (F : Nat) (nv : BitVec 32)
    (hF : min nv.toNat 8 + 1 ≤ F) :
    memEvalFuncFuel F skipFunc [.u32 nv] = skipFwd nv := by
  have hbf : skipFunc.args =
      [{ name := "n", ty := .u 32, role := .owned }] := rfl
  have hbody : skipFunc.body =
      .seq (.let_ "s" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
      (.seq (.let_ "i" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
      (.seq skipWhile
            (.return_ (.var "s")))) := rfl
  have hb : bindMemArgs
      [{ name := "n", ty := .u 32, role := .owned }]
      [.u32 nv] emptyMem =
      some ([("n", .u32 nv)], emptyMem, []) := rfl
  have henv : [("i", .u32 (BitVec.ofNat 32 0)),
        ("s", .u32 (BitVec.ofNat 32 0)),
        ("n", .u32 nv)]
      = mkSkipEnv nv 0 (BitVec.ofNat 32 0) := rfl
  have hfull := skipSuffix_full nv.toNat
  have hsret : envLookup
        (mkSkipEnv nv (min nv.toNat 8) (skipSumU32 nv.toNat)) "s" =
        some (.u32 (skipSumU32 nv.toNat)) :=
    mkSkipEnv_s nv (min nv.toNat 8) (skipSumU32 nv.toNat)
  cases F with
  | zero =>
    have hloopH0 : memEvalStmtWith memEvalStmtZeroHandler
          skipWhile (mkSkipEnv nv 0 (BitVec.ofNat 32 0))
          emptyMem [] =
        .ok (((mkSkipEnv nv (min nv.toNat 8)
            (BitVec.ofNat 32 0 + skipSuffixU32 0 (min nv.toNat 8)),
            emptyMem, [])), .fellThrough) :=
      memSkipWhile_correct nv 0 0 (BitVec.ofNat 32 0) emptyMem []
        (Nat.zero_le _) (by omega)
    simp only [memEvalFuncFuel, hbf, hbody, hb]
    simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, memEvalExpr,
      litVal, skipFwd, henv, hloopH0, hsret, hfull, BitVec.zero_add]
  | succ F =>
    have hloopS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
          skipWhile (mkSkipEnv nv 0 (BitVec.ofNat 32 0))
          emptyMem [] =
        .ok (((mkSkipEnv nv (min nv.toNat 8)
            (BitVec.ofNat 32 0 + skipSuffixU32 0 (min nv.toNat 8)),
            emptyMem, [])), .fellThrough) :=
      memSkipWhile_correct nv (F + 1) 0 (BitVec.ofNat 32 0) emptyMem []
        (Nat.zero_le _) (by omega)
    simp only [memEvalFuncFuel, hbf, hbody, hb]
    simp [memEvalStmtFuel, memEvalStmtWith, memEvalExpr,
      litVal, skipFwd, henv, hloopS, hsret, hfull, BitVec.zero_add]

/-- Transfer for `skip_sum`: both sides equal `skipFwd`. -/
theorem memTransfer_skip (F : Nat) (nv : BitVec 32)
    (hF : min nv.toNat 8 + 1 ≤ F)
    (_h : oracleNoalias skipFunc [.u32 nv]) :
    memEvalFuncFuel F skipFunc [.u32 nv] =
      evalFuncFuel F skipFunc [.u32 nv] := by
  rw [memEvalFuncFuel_skip F nv hF, evalFuncFuel_skip F nv hF]

/-! ## M3c flow transfer: `find_eq` (single-block stride search) -/

/-- Memory loop condition reads the index against the bound (pure —
    mirrors `findCond_eval`). -/
theorem memFindCond_eval (l : List (BitVec 32)) (nv kv : BitVec 32)
    (t : Nat) (m : Mem) (π : Layout) (h : t < 2 ^ 32) :
    memEvalExpr (.ult (.var "i") (.var "n")) (mkFindEnv l nv kv t) m π =
      .ok (.b (decide (t < nv.toNat))) := by
  have hi := mkFindEnv_i l nv kv t
  have hn := mkFindEnv_n l nv kv t
  simp only [memEvalExpr, hi, hn, ofNat32_ult t nv h]

/-- Memory body on match: return the index (any fuel) — mirrors
    `findBody_hit` (the `idx` read cross-checks memory against the
    value list, as in `memSumBody_eval`). -/
theorem memFindBody_hit (F : Nat) (l : List (BitVec 32)) (nv kv : BitVec 32)
    (t : Nat) (x : BitVec 32) (m : Mem) (π : Layout)
    (hget : l[t]? = some x) (heq : x = kv) (ht32 : t < 2 ^ 32)
    (hlay : layoutLookup π "a" = some (0, 0))
    (hmem : memFind m 0 = some ⟨0, true, l⟩) :
    memEvalStmtFuel F findBody (mkFindEnv l nv kv t) m π =
      .ok (((mkFindEnv l nv kv t, m, π)),
        .returned (.u32 (BitVec.ofNat 32 t))) := by
  have hkk : (BitVec.ofNat 32 t).toNat = t := ofNat32_toNat t ht32
  have ha := mkFindEnv_a l nv kv t
  have hii := mkFindEnv_i l nv kv t
  have hload : memLoad m 0 0 (BitVec.ofNat 32 t).toNat = .ok x := by
    rw [hkk]
    exact memLoad_hit m 0 0 t ⟨0, true, l⟩ x hmem rfl rfl hget
  have hget' : l[(BitVec.ofNat 32 t).toNat]? = some x := by
    rw [hkk]; exact hget
  have hidx : memEvalExpr (.idx "a" (.var "i")) (mkFindEnv l nv kv t) m π =
        .ok (.u32 x) := by
    simp only [memEvalExpr, hlay, ha, hii, hload, hget',
      beq_self_eq_true, ↓reduceIte]
  have hk := mkFindEnv_k l nv kv t
  have hcond : memEvalExpr (.ueq (.idx "a" (.var "i")) (.var "k"))
        (mkFindEnv l nv kv t) m π = .ok (.b true) := by
    simp only [memEvalExpr, hlay, ha, hii, hload, hget', hk, heq,
      beq_self_eq_true, ↓reduceIte]
  have hret : memEvalExpr (.var "i") (mkFindEnv l nv kv t) m π =
        .ok (.u32 (BitVec.ofNat 32 t)) := by
    simp [memEvalExpr, hii]
  cases F <;>
    simp [findBody, memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      hcond, hret]

/-- Memory body on miss: step the index (any fuel) — mirrors
    `findBody_miss`. -/
theorem memFindBody_miss (F : Nat) (l : List (BitVec 32)) (nv kv : BitVec 32)
    (t : Nat) (m : Mem) (π : Layout)
    (hmiss : ∀ x, l[t]? = some x → x ≠ kv)
    (htlen : t < l.length) (ht32 : t < 2 ^ 32)
    (hlay : layoutLookup π "a" = some (0, 0))
    (hmem : memFind m 0 = some ⟨0, true, l⟩) :
    memEvalStmtFuel F findBody (mkFindEnv l nv kv t) m π =
      .ok (((mkFindEnv l nv kv (t + 1), m, π)), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 t).toNat = t := ofNat32_toNat t ht32
  have hget : l[t]? = some l[t] := List.getElem?_eq_getElem htlen
  have hne : l[t] ≠ kv := hmiss _ hget
  have ha := mkFindEnv_a l nv kv t
  have hii := mkFindEnv_i l nv kv t
  have hload : memLoad m 0 0 (BitVec.ofNat 32 t).toNat = .ok l[t] := by
    rw [hkk]
    exact memLoad_hit m 0 0 t ⟨0, true, l⟩ l[t] hmem rfl rfl hget
  have hget' : l[(BitVec.ofNat 32 t).toNat]? = some l[t] := by
    rw [hkk]; exact hget
  have hidx : memEvalExpr (.idx "a" (.var "i")) (mkFindEnv l nv kv t) m π =
        .ok (.u32 l[t]) := by
    simp only [memEvalExpr, hlay, ha, hii, hload, hget',
      beq_self_eq_true, ↓reduceIte]
  have hk := mkFindEnv_k l nv kv t
  have hcond : memEvalExpr (.ueq (.idx "a" (.var "i")) (.var "k"))
        (mkFindEnv l nv kv t) m π = .ok (.b false) := by
    simp only [memEvalExpr, hlay, ha, hii, hload, hget', hk,
      beq_self_eq_true, ↓reduceIte]
    simp [hne]
  have hi2 : memEvalExpr (.uadd (.var "i") (.lit (.u32 (BitVec.ofNat 32 1))))
        (mkFindEnv l nv kv t) m π =
        .ok (.u32 (BitVec.ofNat 32 (t + 1))) := by
    simp only [memEvalExpr, litVal, hii, ofNat32_add_one]
  have up := findEnv_update_i l nv kv t (t + 1)
  cases F <;>
    simp [findBody, memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      hcond, hi2, up]

/-- Memory body past the end: the index read fails `OOB` (any fuel) —
    mirrors `findBody_oob` (memory bounds fail in lockstep: block data
    = value words). -/
theorem memFindBody_oob (F : Nat) (l : List (BitVec 32)) (nv kv : BitVec 32)
    (m : Mem) (π : Layout)
    (hlen32 : l.length < 2 ^ 32)
    (hlay : layoutLookup π "a" = some (0, 0))
    (hmem : memFind m 0 = some ⟨0, true, l⟩) :
    memEvalStmtFuel F findBody (mkFindEnv l nv kv l.length) m π =
      .error .OOB := by
  have hkk : (BitVec.ofNat 32 l.length).toNat = l.length :=
    ofNat32_toNat _ hlen32
  have hget : l[l.length]? = none :=
    List.getElem?_eq_none (Nat.le_refl _)
  have ha := mkFindEnv_a l nv kv l.length
  have hii := mkFindEnv_i l nv kv l.length
  have hload : memLoad m 0 0 (BitVec.ofNat 32 l.length).toNat =
      .error .OOB := by
    rw [hkk]
    simp [memLoad, hmem]
  have herr : memEvalExpr (.ueq (.idx "a" (.var "i")) (.var "k"))
        (mkFindEnv l nv kv l.length) m π = .error .OOB := by
    have hget' : l[(BitVec.ofNat 32 l.length).toNat]? = none := by
      rw [hkk]; exact hget
    simp only [memEvalExpr, hlay, ha, hii, hload, hget']
  cases F <;>
    simp [findBody, memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, herr]

/-- Memory loop correctness, hit — mirrors `findWhile_some`. -/
theorem memFindWhile_some (l : List (BitVec 32)) (nv kv : BitVec 32)
    (F t j : Nat) (m : Mem) (π : Layout)
    (htm : t ≤ min nv.toNat l.length)
    (h32n : nv.toNat < 2 ^ 32)
    (hF : min nv.toNat l.length - t + 1 ≤ F)
    (hlay : layoutLookup π "a" = some (0, 0))
    (hmem : memFind m 0 = some ⟨0, true, l⟩)
    (hfind : findSuffixU32 l t (min nv.toNat l.length) kv = some j) :
    memEvalStmtFuel F findWhile (mkFindEnv l nv kv t) m π =
      .ok (((mkFindEnv l nv kv j, m, π)),
        .returned (.u32 (BitVec.ofNat 32 j))) := by
  induction F generalizing t j with
  | zero => omega
  | succ F ih =>
    by_cases hlt : t < min nv.toNat l.length
    · have htn : t < nv.toNat := by omega
      have htl : t < l.length := by omega
      have ht32 : t < 2 ^ 32 := by omega
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
            (mkFindEnv l nv kv t) m π = .ok (.b true) := by
        simpa [htn] using (memFindCond_eval l nv kv t m π ht32)
      match hget : l[t]? with
      | some x =>
        by_cases heq : x = kv
        · have hbody := memFindBody_hit F l nv kv t x m π hget heq ht32
            hlay hmem
          have hfound := findSuffix_hit l t (min nv.toNat l.length) kv x
            hget heq hlt
          have hjt : t = j := by
            rw [hfound] at hfind
            exact Option.some_inj.mp hfind
          have hstep : memEvalStmtFuel (F + 1) findWhile
                (mkFindEnv l nv kv t) m π
              = .ok (((mkFindEnv l nv kv t, m, π)),
                .returned (.u32 (BitVec.ofNat 32 t))) := by
            simp [findWhile, memEvalStmtFuel, memEvalSuccHandler,
              memEvalStmtWith, hcond, hbody]
          rw [← hjt]
          exact hstep
        · have hmiss : ∀ y, l[t]? = some y → y ≠ kv := by
            intro y hy
            rw [hget] at hy
            cases hy
            exact heq
          have hbody := memFindBody_miss F l nv kv t m π hmiss htl ht32
            hlay hmem
          have htail := findSuffix_miss l t (min nv.toNat l.length) kv
            hmiss hlt
          have hstep : memEvalStmtFuel (F + 1) findWhile
                (mkFindEnv l nv kv t) m π
              = memEvalStmtFuel F findWhile (mkFindEnv l nv kv (t + 1))
                m π := by
            simp [findWhile, memEvalStmtFuel, memEvalSuccHandler,
              memEvalStmtWith, hcond, hbody]
          rw [hstep]
          rw [htail] at hfind
          exact ih (t + 1) j (by omega) (by omega) hfind
      | none =>
        have hsome : l[t]? = some l[t] := List.getElem?_eq_getElem htl
        rw [hsome] at hget
        simp at hget
    · have htt : t = min nv.toNat l.length := by omega
      subst htt
      have hnil := findSuffix_nil l (min nv.toNat l.length) kv
      rw [hnil] at hfind
      simp at hfind

/-- Memory loop correctness, miss — mirrors `findWhile_none`. -/
theorem memFindWhile_none (l : List (BitVec 32)) (nv kv : BitVec 32)
    (F t : Nat) (m : Mem) (π : Layout)
    (htm : t ≤ min nv.toNat l.length)
    (h32n : nv.toNat < 2 ^ 32) (h32l : l.length < 2 ^ 32)
    (hF : min nv.toNat l.length - t + 1 ≤ F)
    (hlay : layoutLookup π "a" = some (0, 0))
    (hmem : memFind m 0 = some ⟨0, true, l⟩)
    (hfind : findSuffixU32 l t (min nv.toNat l.length) kv = none) :
    memEvalStmtFuel F findWhile (mkFindEnv l nv kv t) m π =
      if decide (nv.toNat ≤ l.length) then
        .ok (((mkFindEnv l nv kv nv.toNat, m, π)), .fellThrough)
      else .error .OOB := by
  induction F generalizing t with
  | zero => omega
  | succ F ih =>
    by_cases hlt : t < min nv.toNat l.length
    · have htn : t < nv.toNat := by omega
      have htl : t < l.length := by omega
      have ht32 : t < 2 ^ 32 := by omega
      have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
            (mkFindEnv l nv kv t) m π = .ok (.b true) := by
        simpa [htn] using (memFindCond_eval l nv kv t m π ht32)
      have hget : l[t]? = some l[t] := List.getElem?_eq_getElem htl
      by_cases heq : l[t] = kv
      · exfalso
        have hfound := findSuffix_hit l t (min nv.toNat l.length) kv l[t]
          hget heq hlt
        rw [hfound] at hfind
        simp at hfind
      · have hmiss : ∀ y, l[t]? = some y → y ≠ kv := by
          intro y hy
          rw [hget] at hy
          cases hy
          exact heq
        have hbody := memFindBody_miss F l nv kv t m π hmiss htl ht32
          hlay hmem
        have htail := findSuffix_miss l t (min nv.toNat l.length) kv
          hmiss hlt
        have hstep : memEvalStmtFuel (F + 1) findWhile
              (mkFindEnv l nv kv t) m π
            = memEvalStmtFuel F findWhile (mkFindEnv l nv kv (t + 1))
              m π := by
          simp [findWhile, memEvalStmtFuel, memEvalSuccHandler,
            memEvalStmtWith, hcond, hbody]
        rw [hstep]
        rw [htail] at hfind
        exact ih (t + 1) (by omega) (by omega) hfind
    · have htt : t = min nv.toNat l.length := by omega
      by_cases hnlen : nv.toNat ≤ l.length
      · have htn : t = nv.toNat := by omega
        subst htn
        have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
              (mkFindEnv l nv kv nv.toNat) m π = .ok (.b false) := by
          simpa using (memFindCond_eval l nv kv nv.toNat m π h32n)
        have htrue : (decide (nv.toNat ≤ l.length)) = true := by
          simp [hnlen]
        simp [findWhile, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond, htrue]
      · have htl2 : t = l.length := by omega
        subst htl2
        have hlt' : l.length < nv.toNat := by omega
        have hcond : memEvalExpr (.ult (.var "i") (.var "n"))
              (mkFindEnv l nv kv l.length) m π = .ok (.b true) := by
          simpa [hlt'] using (memFindCond_eval l nv kv l.length m π h32l)
        have hbody := memFindBody_oob F l nv kv m π h32l hlay hmem
        have hfalse : (decide (nv.toNat ≤ l.length)) = false := by
          simp [hnlen]
        simp [findWhile, memEvalStmtFuel, memEvalSuccHandler,
          memEvalStmtWith, hcond, hbody, hfalse]

/-- `memEval` for `find_eq`, fuel-generalized — mirrors
    `evalFuncFuel_find` (memory rides alongside the singleton block). -/
theorem memEvalFuncFuel_findEq (F : Nat) (l : List (BitVec 32))
    (nv kv : BitVec 32)
    (h32n : nv.toNat < 2 ^ 32) (h32l : l.length < 2 ^ 32)
    (hF : min nv.toNat l.length + 1 ≤ F) :
    memEvalFuncFuel F findEqFunc [.arr32 l, .u32 nv, .u32 kv] =
      findEqFwd l nv kv := by
  have hbf : findEqFunc.args =
      [{ name := "a", ty := .array (.u 32) 4096, role := .sharedBorrow },
       { name := "n", ty := .u 32, role := .owned },
       { name := "k", ty := .u 32, role := .owned }] := rfl
  have hbody : findEqFunc.body =
      .seq (.let_ "i" (.u 32) (.lit (.u32 (BitVec.ofNat 32 0))))
      (.seq findWhile
            (.return_ (.var "n"))) := rfl
  have hb := bindMemArgs_findEq l nv kv
  have hlay : layoutLookup [("a", 0, 0)] "a" = some (0, 0) := by
    simp [layoutLookup]
  have hmem : memFind ⟨1, [(0, ⟨0, true, l⟩)], []⟩ 0 =
      some ⟨0, true, l⟩ := by
    simp [memFind]
  have henv : [("i", .u32 (BitVec.ofNat 32 0)), ("a", .arr32 l),
        ("n", .u32 nv), ("k", .u32 kv)]
      = mkFindEnv l nv kv 0 := rfl
  have hbridge := findSuffix_zero_idx l nv.toNat kv
  match hfi : findIdxU32 l nv.toNat kv with
  | some j =>
    have hloop : ∀ (G : Nat),
        min nv.toNat l.length + 1 ≤ G →
        memEvalStmtFuel G findWhile (mkFindEnv l nv kv 0)
          ⟨1, [(0, ⟨0, true, l⟩)], []⟩ [("a", 0, 0)] =
          .ok (((mkFindEnv l nv kv j, ⟨1, [(0, ⟨0, true, l⟩)], []⟩,
            [("a", 0, 0)])), .returned (.u32 (BitVec.ofNat 32 j))) := by
      intro G hG
      exact memFindWhile_some l nv kv G 0 j _ _
        (Nat.zero_le _) h32n (by omega) hlay hmem
        (by rw [hbridge, hfi])
    cases F with
    | zero =>
      have hloopH0 : memEvalStmtWith memEvalStmtZeroHandler
            findWhile (mkFindEnv l nv kv 0)
            ⟨1, [(0, ⟨0, true, l⟩)], []⟩ [("a", 0, 0)] =
          .ok (((mkFindEnv l nv kv j, ⟨1, [(0, ⟨0, true, l⟩)], []⟩,
            [("a", 0, 0)])), .returned (.u32 (BitVec.ofNat 32 j))) :=
        hloop 0 (by omega)
      simp only [memEvalFuncFuel, hbf, hbody, hb]
      simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, memEvalExpr,
        litVal, findEqFwd, findEqOut, henv, hloopH0, hfi]
    | succ F =>
      have hloopS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
            findWhile (mkFindEnv l nv kv 0)
            ⟨1, [(0, ⟨0, true, l⟩)], []⟩ [("a", 0, 0)] =
          .ok (((mkFindEnv l nv kv j, ⟨1, [(0, ⟨0, true, l⟩)], []⟩,
            [("a", 0, 0)])), .returned (.u32 (BitVec.ofNat 32 j))) :=
        hloop (F + 1) (by omega)
      simp only [memEvalFuncFuel, hbf, hbody, hb]
      simp [memEvalStmtFuel, memEvalStmtWith, memEvalExpr,
        litVal, findEqFwd, findEqOut, henv, hloopS, hfi]
  | none =>
    have hloop : ∀ (G : Nat),
        min nv.toNat l.length + 1 ≤ G →
        memEvalStmtFuel G findWhile (mkFindEnv l nv kv 0)
          ⟨1, [(0, ⟨0, true, l⟩)], []⟩ [("a", 0, 0)] =
          if decide (nv.toNat ≤ l.length) then
            .ok (((mkFindEnv l nv kv nv.toNat, ⟨1, [(0, ⟨0, true, l⟩)], []⟩,
              [("a", 0, 0)])), .fellThrough)
          else .error .OOB := by
      intro G hG
      exact memFindWhile_none l nv kv G 0 _ _
        (Nat.zero_le _) h32n h32l (by omega) hlay hmem
        (by rw [hbridge, hfi])
    by_cases hle : nv.toNat ≤ l.length
    · have htrue : (decide (nv.toNat ≤ l.length)) = true := by simp [hle]
      have hsnret : envLookup (mkFindEnv l nv kv nv.toNat) "n" =
            some (.u32 nv) :=
        mkFindEnv_n l nv kv nv.toNat
      have hinv : BitVec.ofNat 32 nv.toNat = nv := ofNat32_toNat_inv nv
      cases F with
      | zero =>
        have hloopH0 : memEvalStmtWith memEvalStmtZeroHandler
              findWhile (mkFindEnv l nv kv 0)
              ⟨1, [(0, ⟨0, true, l⟩)], []⟩ [("a", 0, 0)] =
            .ok (((mkFindEnv l nv kv nv.toNat, ⟨1, [(0, ⟨0, true, l⟩)], []⟩,
              [("a", 0, 0)])), .fellThrough) := by
          have h := hloop 0 (by omega)
          rwa [htrue] at h
        simp only [memEvalFuncFuel, hbf, hbody, hb]
        simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, memEvalExpr,
          litVal, findEqFwd, findEqOut, henv, hloopH0, hsnret, hfi, htrue,
          hinv]
      | succ F =>
        have hloopS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
              findWhile (mkFindEnv l nv kv 0)
              ⟨1, [(0, ⟨0, true, l⟩)], []⟩ [("a", 0, 0)] =
            .ok (((mkFindEnv l nv kv nv.toNat, ⟨1, [(0, ⟨0, true, l⟩)], []⟩,
              [("a", 0, 0)])), .fellThrough) := by
          have h := hloop (F + 1) (by omega)
          rwa [htrue] at h
        simp only [memEvalFuncFuel, hbf, hbody, hb]
        simp [memEvalStmtFuel, memEvalStmtWith, memEvalExpr,
          litVal, findEqFwd, findEqOut, henv, hloopS, hsnret, hfi, htrue,
          hinv]
    · have hfalse : (decide (nv.toNat ≤ l.length)) = false := by
        simp [hle]
      cases F with
      | zero =>
        have hloopH0 : memEvalStmtWith memEvalStmtZeroHandler
              findWhile (mkFindEnv l nv kv 0)
              ⟨1, [(0, ⟨0, true, l⟩)], []⟩ [("a", 0, 0)] = .error .OOB := by
          have h := hloop 0 (by omega)
          rwa [hfalse] at h
        simp only [memEvalFuncFuel, hbf, hbody, hb]
        simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, memEvalExpr,
          litVal, findEqFwd, findEqOut, henv, hloopH0, hfi, hfalse]
      | succ F =>
        have hloopS : memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
              findWhile (mkFindEnv l nv kv 0)
              ⟨1, [(0, ⟨0, true, l⟩)], []⟩ [("a", 0, 0)] = .error .OOB := by
          have h := hloop (F + 1) (by omega)
          rwa [hfalse] at h
        simp only [memEvalFuncFuel, hbf, hbody, hb]
        simp [memEvalStmtFuel, memEvalStmtWith, memEvalExpr,
          litVal, findEqFwd, findEqOut, henv, hloopS, hfi, hfalse]

/-- Transfer for `find_eq`: both sides equal `findEqFwd`. -/
theorem memTransfer_findEq (F : Nat) (l : List (BitVec 32))
    (nv kv : BitVec 32)
    (h32n : nv.toNat < 2 ^ 32) (h32l : l.length < 2 ^ 32)
    (hF : min nv.toNat l.length + 1 ≤ F)
    (_h : oracleNoalias findEqFunc [.arr32 l, .u32 nv, .u32 kv]) :
    memEvalFuncFuel F findEqFunc [.arr32 l, .u32 nv, .u32 kv] =
      evalFuncFuel F findEqFunc [.arr32 l, .u32 nv, .u32 kv] := by
  rw [memEvalFuncFuel_findEq F l nv kv h32n h32l hF,
    evalFuncFuel_find F l nv kv h32n h32l hF]

/-! ## M3c caller transfers: `add_caller`, `sum_caller` (program layer) -/

/-- `memEval` for the `add` leaf, stated about `addFunc` (the callee
    fact the caller proofs need; cf. `evalFuncFuel_add`). -/
theorem memEvalFuncFuel_add (F : Nat) (a b : BitVec 32) :
    memEvalFuncFuel F addFunc [.i32 a, .i32 b] = addFwd a b := by
  have hbf : addFunc.args =
      [{ name := "a", ty := .i 32, role := .owned },
       { name := "b", ty := .i 32, role := .owned }] := rfl
  have hbody : addFunc.body =
      .return_ (.add (.var "a") (.var "b")) := rfl
  have hb : bindMemArgs
      [{ name := "a", ty := .i 32, role := .owned },
       { name := "b", ty := .i 32, role := .owned }]
      [.i32 a, .i32 b] emptyMem =
      some ([("a", .i32 a), ("b", .i32 b)], emptyMem, []) :=
    bindMemArgs_add a b
  have ha := envLookup_add_a a b
  have hbb := envLookup_add_b a b
  simp only [memEvalFuncFuel, hbf, hbody, hb]
  cases F <;>
    simp only [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      memEvalExpr, addFwd, ha, hbb] <;>
    (cases checkedAddI32 a b <;> rfl)

/-- `memEval` for `add` under a renamed leaf (mirrors
    `evalFuncFuel_addAt` on the memory side; the name never matters). -/
theorem memEvalFuncFuel_addAt (F : Nat) (nm : String) (a b : BitVec 32) :
    memEvalFuncFuel F { addFunc with name := nm } [.i32 a, .i32 b] =
      addFwd a b := by
  have hbf : addFunc.args =
      [{ name := "a", ty := .i 32, role := .owned },
       { name := "b", ty := .i 32, role := .owned }] := rfl
  have hbody : addFunc.body =
      .return_ (.add (.var "a") (.var "b")) := rfl
  have hb : bindMemArgs
      [{ name := "a", ty := .i 32, role := .owned },
       { name := "b", ty := .i 32, role := .owned }]
      [.i32 a, .i32 b] emptyMem =
      some ([("a", .i32 a), ("b", .i32 b)], emptyMem, []) :=
    bindMemArgs_add a b
  have ha := envLookup_add_a a b
  have hbb := envLookup_add_b a b
  simp only [memEvalFuncFuel, hbf, hbody, hb]
  cases F <;>
    simp only [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      memEvalExpr, addFwd, ha, hbb] <;>
    (cases checkedAddI32 a b <;> rfl)

/-- `memEval` for `add3` (mirrors `evalFuncFuel_add3` on the memory
    side: the `let_` makes both adds single steps; int-only, so
    `Mem`/`Layout` stay `emptyMem`/`[]`). -/
theorem memEvalFuncFuel_add3 (F : Nat) (x y z : BitVec 32) :
    memEvalFuncFuel F add3Func [.i32 x, .i32 y, .i32 z] = add3Fwd x y z := by
  have hbind : bindMemArgs add3Func.args [.i32 x, .i32 y, .i32 z] emptyMem =
      some ([("a", .i32 x), ("b", .i32 y), ("c", .i32 z)], emptyMem, []) :=
    bindMemArgs_add3 x y z
  have hbody : add3Func.body =
      .seq (.let_ "t" (.i 32) (.add (.var "a") (.var "b")))
           (.return_ (.add (.var "t") (.var "c"))) := rfl
  have ha := envLookup_add3_a x y z
  have hb := envLookup_add3_b x y z
  have hc := envLookup_add3_c x y z
  have hmem1 : memEvalExpr (.add (.var "a") (.var "b"))
      ([("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] : Env) emptyMem [] =
      evalExpr (.add (.var "a") (.var "b"))
        [("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] := by
    simp only [memEvalExpr, evalExpr, ha, hb]
  simp only [memEvalFuncFuel, hbind, hbody]
  cases h1 : checkedAddI32 x y with
  | error e =>
    have hv1 : evalExpr (.add (.var "a") (.var "b"))
        ([("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] : Env) = .error e := by
      simp [evalExpr, ha, hb, h1, Except.map]
    have hmemv1 : memEvalExpr (.add (.var "a") (.var "b"))
        ([("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] : Env) emptyMem [] =
        .error e := by
      rw [hmem1]; exact hv1
    have hlet := memEvalStmtFuel_let_err F "t" (.i 32)
      (.add (.var "a") (.var "b"))
      [("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] emptyMem [] e
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) hmemv1
    have hseq := memEvalStmtFuel_seq_err F
      (.let_ "t" (.i 32) (.add (.var "a") (.var "b")))
      (.return_ (.add (.var "t") (.var "c")))
      [("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] emptyMem [] _ hlet
    rw [hseq]
    simp [add3Fwd, h1]
  | ok t =>
    have hv1 : evalExpr (.add (.var "a") (.var "b"))
        ([("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] : Env) =
        .ok (.i32 t) := by
      simp [evalExpr, ha, hb, h1, Except.map]
    have hlet := memEvalStmtFuel_let_pure F "t" (.i 32)
      (.add (.var "a") (.var "b"))
      [("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] emptyMem [] (.i32 t)
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h) hmem1 hv1
    have ht : envLookup (envExtend [("a", .i32 x), ("b", .i32 y),
        ("c", .i32 z)] "t" (.i32 t)) "t" = some (.i32 t) :=
      envExtend_hit _ _ _
    have hc2 : envLookup (envExtend [("a", .i32 x), ("b", .i32 y),
        ("c", .i32 z)] "t" (.i32 t)) "c" = some (.i32 z) := by
      simp [envExtend, envLookup, show ("c" : String) ≠ "t" by decide]
    have hmem2 : memEvalExpr (.add (.var "t") (.var "c"))
        (envExtend [("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] "t" (.i32 t))
        emptyMem [] =
        evalExpr (.add (.var "t") (.var "c"))
          (envExtend [("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] "t"
            (.i32 t)) := by
      simp only [memEvalExpr, evalExpr, ht, hc2]
    cases h2 : checkedAddI32 t z with
    | error e =>
      have hv2 : evalExpr (.add (.var "t") (.var "c"))
          (envExtend [("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] "t"
            (.i32 t)) = .error e := by
        simp [evalExpr, ht, hc2, h2, Except.map]
      have hmemv2 : memEvalExpr (.add (.var "t") (.var "c"))
          (envExtend [("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] "t"
            (.i32 t)) emptyMem [] = .error e := by
        rw [hmem2]; exact hv2
      have hret := memEvalStmtFuel_return_err F (.add (.var "t") (.var "c"))
        (envExtend [("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] "t" (.i32 t))
        emptyMem [] e hmemv2
      rw [memEvalStmtFuel_seq_fallthrough F
        (.let_ "t" (.i 32) (.add (.var "a") (.var "b")))
        (.return_ (.add (.var "t") (.var "c")))
        ([("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] : Env)
        emptyMem []
        (envExtend [("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] "t" (.i32 t))
        emptyMem [] hlet, hret]
      simp [add3Fwd, h1, h2, i32_map_error]
    | ok r =>
      have hv2 : evalExpr (.add (.var "t") (.var "c"))
          (envExtend [("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] "t"
            (.i32 t)) = .ok (.i32 r) := by
        simp [evalExpr, ht, hc2, h2, Except.map]
      have hret := memEvalStmtFuel_return F (.add (.var "t") (.var "c"))
        (envExtend [("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] "t" (.i32 t))
        emptyMem [] (.i32 r) hmem2 hv2
      have hseq := memEvalStmtFuel_seq_fallthrough F
        (.let_ "t" (.i 32) (.add (.var "a") (.var "b")))
        (.return_ (.add (.var "t") (.var "c")))
        ([("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] : Env)
        emptyMem []
        (envExtend [("a", .i32 x), ("b", .i32 y), ("c", .i32 z)] "t" (.i32 t))
        emptyMem [] hlet
      rw [hseq, hret]
      simp [add3Fwd, h1, h2, i32_map_ok]

/-- Transfer for `add3`: both sides equal `add3Fwd`. -/
theorem memTransfer_add3 (F : Nat) (x y z : BitVec 32)
    (_h : oracleNoalias add3Func [.i32 x, .i32 y, .i32 z]) :
    memEvalFuncFuel F add3Func [.i32 x, .i32 y, .i32 z] =
      evalFuncFuel F add3Func [.i32 x, .i32 y, .i32 z] := by
  rw [memEvalFuncFuel_add3, evalFuncFuel_add3]

/-- `memEval` for `add_caller`: program evaluation over `[addFunc]`
    agrees with the forward (mirrors `evalProgFunc_addCaller`; caller
    `Mem`/`Layout` stay `emptyMem`/`[]` — each callee runs on its own
    fresh entry blocks). -/
theorem memEvalProgFunc_addCaller (F : Nat) (x y z : BitVec 32) :
    memEvalProgFunc [addFunc] F addCallerFunc [.i32 x, .i32 y, .i32 z] =
      addCallerFwd x y z := by
  have hbind : bindMemArgs addCallerFunc.args [.i32 x, .i32 y, .i32 z]
      emptyMem =
      some ([("x", .i32 x), ("y", .i32 y), ("z", .i32 z)], emptyMem, []) :=
    bindMemArgs_addCaller x y z
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
    have hc1 : memEvalFuncFuel F addFunc [.i32 x, .i32 y] = .error e := by
      rw [memEvalFuncFuel_add]
      unfold addFwd
      rw [h1]
      exact i32_map_error e
    have hargs1 : lookupArgs [("x", .i32 x), ("y", .i32 y), ("z", .i32 z)]
        ["x", "y"] = some [.i32 x, .i32 y] := by
      simp [lookupArgs, hx, hy]
    have hstep1 := memEvalProgStmt_callRet_err [addFunc] F "t" "add" ["x", "y"]
      [("x", .i32 x), ("y", .i32 y), ("z", .i32 z)] emptyMem []
      [.i32 x, .i32 y] addFunc e hargs1 hfind hc1
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstep1]
    simp [addCallerFwd, h1]
  | ok t =>
    have hc1 : memEvalFuncFuel F addFunc [.i32 x, .i32 y] =
        .ok (.i32 t) := by
      rw [memEvalFuncFuel_add]
      unfold addFwd
      rw [h1]
      exact i32_map_ok t
    have hargs1 : lookupArgs [("x", .i32 x), ("y", .i32 y), ("z", .i32 z)]
        ["x", "y"] = some [.i32 x, .i32 y] := by
      simp [lookupArgs, hx, hy]
    have hstep1 := memEvalProgStmt_callRet_ok [addFunc] F "t" "add" ["x", "y"]
      [("x", .i32 x), ("y", .i32 y), ("z", .i32 z)] emptyMem []
      [.i32 x, .i32 y] addFunc (.i32 t) hargs1 hfind hc1
    have htz : envLookup (envExtend [("x", .i32 x), ("y", .i32 y),
        ("z", .i32 z)] "t" (.i32 t)) "t" = some (.i32 t) :=
      envExtend_hit _ _ _
    have htz2 : envLookup (envExtend [("x", .i32 x), ("y", .i32 y),
        ("z", .i32 z)] "t" (.i32 t)) "z" = some (.i32 z) := by
      simp [envExtend, envLookup, show ("z" : String) ≠ "t" by decide]
    cases h2 : checkedAddI32 t z with
    | error e =>
      have hc2 : memEvalFuncFuel F addFunc [.i32 t, .i32 z] = .error e := by
        rw [memEvalFuncFuel_add]
        unfold addFwd
        rw [h2]
        exact i32_map_error e
      have hargs2 : lookupArgs (envExtend [("x", .i32 x), ("y", .i32 y),
          ("z", .i32 z)] "t" (.i32 t)) ["t", "z"] =
          some [.i32 t, .i32 z] := by
        simp [lookupArgs, htz, htz2]
      have hstep2 := memEvalProgStmt_callRet_err [addFunc] F "r" "add"
        ["t", "z"] (envExtend [("x", .i32 x), ("y", .i32 y),
          ("z", .i32 z)] "t" (.i32 t)) emptyMem []
        [.i32 t, .i32 z] addFunc e hargs2 hfind hc2
      simp only [memEvalProgFunc, hbind, hbody]
      rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep1,
        memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstep2]
      simp [addCallerFwd, h1, h2, i32_map_error]
    | ok r =>
      have hc2 : memEvalFuncFuel F addFunc [.i32 t, .i32 z] =
          .ok (.i32 r) := by
        rw [memEvalFuncFuel_add]
        unfold addFwd
        rw [h2]
        exact i32_map_ok r
      have hargs2 : lookupArgs (envExtend [("x", .i32 x), ("y", .i32 y),
          ("z", .i32 z)] "t" (.i32 t)) ["t", "z"] =
          some [.i32 t, .i32 z] := by
        simp [lookupArgs, htz, htz2]
      have hstep2 := memEvalProgStmt_callRet_ok [addFunc] F "r" "add"
        ["t", "z"] (envExtend [("x", .i32 x), ("y", .i32 y),
          ("z", .i32 z)] "t" (.i32 t)) emptyMem []
        [.i32 t, .i32 z] addFunc (.i32 r) hargs2 hfind hc2
      have hret : memEvalProgStmt [addFunc] F (.return_ (.var "r"))
          (envExtend (envExtend [("x", .i32 x), ("y", .i32 y),
            ("z", .i32 z)] "t" (.i32 t)) "r" (.i32 r)) emptyMem [] =
          .ok (((envExtend (envExtend [("x", .i32 x), ("y", .i32 y),
            ("z", .i32 z)] "t" (.i32 t)) "r" (.i32 r),
            emptyMem, []), .returned (.i32 r))) :=
        memEvalProgStmt_return [addFunc] F (.var "r") _
          _ _ (.i32 r) (by simp [memEvalExpr, envExtend_hit])
      simp only [memEvalProgFunc, hbind, hbody]
      rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep1,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep2, hret]
      simp [addCallerFwd, h1, h2, i32_map_ok]

/-- Transfer for `add_caller` (program level): both sides equal
    `addCallerFwd`. -/
theorem memTransferProg_addCaller (F : Nat) (x y z : BitVec 32)
    (_h : oracleNoalias addCallerFunc [.i32 x, .i32 y, .i32 z]) :
    memEvalProgFunc [addFunc] F addCallerFunc [.i32 x, .i32 y, .i32 z] =
      evalProgFunc [addFunc] F addCallerFunc [.i32 x, .i32 y, .i32 z] := by
  rw [memEvalProgFunc_addCaller, evalProgFunc_addCaller]

/-- `memEval` for `sum_caller`: program evaluation over `[sumFunc]`
    agrees with the delegating forward (mirrors `evalProgFunc_sumCaller`;
    the caller block rides alongside while the callee runs on its own
    fresh entry block). -/
theorem memEvalProgFunc_sumCaller (F : Nat) (l : List (BitVec 32))
    (nv : BitVec 32)
    (hle : nv.toNat ≤ l.length) (h32 : nv.toNat < 2 ^ 32)
    (hF : nv.toNat ≤ F) :
    memEvalProgFunc [sumFunc] F sumCallerFunc [.arr32 l, .u32 nv] =
      sumCallerFwd l nv := by
  have hbind : bindMemArgs sumCallerFunc.args [.arr32 l, .u32 nv] emptyMem =
      some ([("a", .arr32 l), ("n", .u32 nv)],
        ⟨1, [(0, ⟨0, true, l⟩)], []⟩, [("a", 0, 0)]) :=
    bindMemArgs_sumCaller l nv
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
  have hcall := memEvalFuncFuel_sum F l nv hle h32 hF
  cases hsum : sumFwd l nv with
  | error e =>
    have hcall' : memEvalFuncFuel F sumFunc [.arr32 l, .u32 nv] =
        .error e := by
      rw [hcall, hsum]
    have hstep := memEvalProgStmt_callRet_err [sumFunc] F "s" "sum_array"
      ["a", "n"] [("a", .arr32 l), ("n", .u32 nv)]
      ⟨1, [(0, ⟨0, true, l⟩)], []⟩ [("a", 0, 0)]
      [.arr32 l, .u32 nv] sumFunc e hargs hfind hcall'
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstep]
    simp [sumCallerFwd, hsum]
  | ok v =>
    have hcall' : memEvalFuncFuel F sumFunc [.arr32 l, .u32 nv] = .ok v := by
      rw [hcall, hsum]
    have hstep := memEvalProgStmt_callRet_ok [sumFunc] F "s" "sum_array"
      ["a", "n"] [("a", .arr32 l), ("n", .u32 nv)]
      ⟨1, [(0, ⟨0, true, l⟩)], []⟩ [("a", 0, 0)]
      [.arr32 l, .u32 nv] sumFunc v hargs hfind hcall'
    have hret : memEvalProgStmt [sumFunc] F (.return_ (.var "s"))
        (envExtend [("a", .arr32 l), ("n", .u32 nv)] "s" v)
        ⟨1, [(0, ⟨0, true, l⟩)], []⟩ [("a", 0, 0)] =
        .ok (((envExtend [("a", .arr32 l), ("n", .u32 nv)] "s" v,
          ⟨1, [(0, ⟨0, true, l⟩)], []⟩, [("a", 0, 0)]), .returned v)) :=
      memEvalProgStmt_return [sumFunc] F (.var "s") _
        _ _ v (by simp [memEvalExpr, envExtend_hit])
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep, hret]
    simp [sumCallerFwd, hsum]

/-- Transfer for `sum_caller` (program level): both sides equal
    `sumCallerFwd`. -/
theorem memTransferProg_sumCaller (F : Nat) (l : List (BitVec 32))
    (nv : BitVec 32)
    (hle : nv.toNat ≤ l.length) (h32 : nv.toNat < 2 ^ 32)
    (hF : nv.toNat ≤ F)
    (_h : oracleNoalias sumCallerFunc [.arr32 l, .u32 nv]) :
    memEvalProgFunc [sumFunc] F sumCallerFunc [.arr32 l, .u32 nv] =
      evalProgFunc [sumFunc] F sumCallerFunc [.arr32 l, .u32 nv] := by
  rw [memEvalProgFunc_sumCaller F l nv hle h32 hF,
    evalProgFunc_sumCaller F l nv hle h32 hF]

/-! ## N4a program transfers: `use_add`, `use_ns_add` -/

/-- `memEval` for `use_add`: program evaluation over the renamed `add`
    leaf agrees with the delegating forward (mirrors
    `evalProgFunc_useAdd`; int-only, so `Mem`/`Layout` stay
    `emptyMem`/`[]`). -/
theorem memEvalProgFunc_useAdd (F : Nat) (x y : BitVec 32) :
    memEvalProgFunc [{ addFunc with name := "_Z3addii" }] F useAddFunc
      [.i32 x, .i32 y] = useAddFwd x y := by
  have hbind : bindMemArgs useAddFunc.args [.i32 x, .i32 y] emptyMem =
      some ([("x", .i32 x), ("y", .i32 y)], emptyMem, []) :=
    bindMemArgs_useAdd x y
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
  have hcall := memEvalFuncFuel_addAt F "_Z3addii" x y
  cases hadd : addFwd x y with
  | error e =>
    have hcall' : memEvalFuncFuel F { addFunc with name := "_Z3addii" }
        [.i32 x, .i32 y] = .error e := by
      rw [hcall, hadd]
    have hstep := memEvalProgStmt_callRet_err
      [{ addFunc with name := "_Z3addii" }]
      F "s" "_Z3addii" ["x", "y"] [("x", .i32 x), ("y", .i32 y)]
      emptyMem []
      [.i32 x, .i32 y] { addFunc with name := "_Z3addii" } e hargs hfind hcall'
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstep]
    simp [useAddFwd, hadd]
  | ok v =>
    have hcall' : memEvalFuncFuel F { addFunc with name := "_Z3addii" }
        [.i32 x, .i32 y] = .ok v := by
      rw [hcall, hadd]
    have hstep := memEvalProgStmt_callRet_ok
      [{ addFunc with name := "_Z3addii" }]
      F "s" "_Z3addii" ["x", "y"] [("x", .i32 x), ("y", .i32 y)]
      emptyMem []
      [.i32 x, .i32 y] { addFunc with name := "_Z3addii" } v hargs hfind hcall'
    have hret : memEvalProgStmt [{ addFunc with name := "_Z3addii" }] F
        (.return_ (.var "s")) (envExtend [("x", .i32 x), ("y", .i32 y)] "s" v)
        emptyMem [] =
        .ok (((envExtend [("x", .i32 x), ("y", .i32 y)] "s" v,
          emptyMem, []), .returned v)) :=
      memEvalProgStmt_return [{ addFunc with name := "_Z3addii" }] F (.var "s") _
        _ _ v (by simp [memEvalExpr, envExtend_hit])
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep, hret]
    simp [useAddFwd, hadd]

/-- Transfer for `use_add` (program level): both sides equal
    `useAddFwd`. -/
theorem memTransferProg_useAdd (F : Nat) (x y : BitVec 32)
    (_h : oracleNoalias useAddFunc [.i32 x, .i32 y]) :
    memEvalProgFunc [{ addFunc with name := "_Z3addii" }] F useAddFunc
      [.i32 x, .i32 y] =
      evalProgFunc [{ addFunc with name := "_Z3addii" }] F useAddFunc
        [.i32 x, .i32 y] := by
  rw [memEvalProgFunc_useAdd, evalProgFunc_useAdd]

/-- `memEval` for `use_ns_add`: same proof at the namespaced leaf. -/
theorem memEvalProgFunc_useNsAdd (F : Nat) (x y : BitVec 32) :
    memEvalProgFunc [{ addFunc with name := "_ZN2ns3addEii" }] F useNsAddFunc
      [.i32 x, .i32 y] = useNsAddFwd x y := by
  have hbind : bindMemArgs useNsAddFunc.args [.i32 x, .i32 y] emptyMem =
      some ([("x", .i32 x), ("y", .i32 y)], emptyMem, []) :=
    bindMemArgs_useAdd x y
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
  have hcall := memEvalFuncFuel_addAt F "_ZN2ns3addEii" x y
  cases hadd : addFwd x y with
  | error e =>
    have hcall' : memEvalFuncFuel F { addFunc with name := "_ZN2ns3addEii" }
        [.i32 x, .i32 y] = .error e := by
      rw [hcall, hadd]
    have hstep := memEvalProgStmt_callRet_err
      [{ addFunc with name := "_ZN2ns3addEii" }]
      F "s" "_ZN2ns3addEii" ["x", "y"] [("x", .i32 x), ("y", .i32 y)]
      emptyMem []
      [.i32 x, .i32 y] { addFunc with name := "_ZN2ns3addEii" } e hargs hfind hcall'
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstep]
    simp [useNsAddFwd, hadd]
  | ok v =>
    have hcall' : memEvalFuncFuel F { addFunc with name := "_ZN2ns3addEii" }
        [.i32 x, .i32 y] = .ok v := by
      rw [hcall, hadd]
    have hstep := memEvalProgStmt_callRet_ok
      [{ addFunc with name := "_ZN2ns3addEii" }]
      F "s" "_ZN2ns3addEii" ["x", "y"] [("x", .i32 x), ("y", .i32 y)]
      emptyMem []
      [.i32 x, .i32 y] { addFunc with name := "_ZN2ns3addEii" } v hargs hfind hcall'
    have hret : memEvalProgStmt [{ addFunc with name := "_ZN2ns3addEii" }] F
        (.return_ (.var "s")) (envExtend [("x", .i32 x), ("y", .i32 y)] "s" v)
        emptyMem [] =
        .ok (((envExtend [("x", .i32 x), ("y", .i32 y)] "s" v,
          emptyMem, []), .returned v)) :=
      memEvalProgStmt_return [{ addFunc with name := "_ZN2ns3addEii" }] F (.var "s") _
        _ _ v (by simp [memEvalExpr, envExtend_hit])
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep, hret]
    simp [useNsAddFwd, hadd]

/-- Transfer for `use_ns_add` (program level): both sides equal
    `useNsAddFwd`. -/
theorem memTransferProg_useNsAdd (F : Nat) (x y : BitVec 32)
    (_h : oracleNoalias useNsAddFunc [.i32 x, .i32 y]) :
    memEvalProgFunc [{ addFunc with name := "_ZN2ns3addEii" }] F useNsAddFunc
      [.i32 x, .i32 y] =
      evalProgFunc [{ addFunc with name := "_ZN2ns3addEii" }] F useNsAddFunc
        [.i32 x, .i32 y] := by
  rw [memEvalProgFunc_useNsAdd, evalProgFunc_useNsAdd]

/-! ## N4c program transfers: `use_tadd32`, `use_tadd64` -/

/-- `memEval` for `add64` under a renamed leaf (mirrors
    `evalFuncFuel_add64At` on the memory side; the name never
    matters). -/
theorem memEvalFuncFuel_add64At (F : Nat) (nm : String) (a b : BitVec 64) :
    memEvalFuncFuel F { add64Func with name := nm } [.i64 a, .i64 b] =
      add64Fwd a b := by
  have hbf : add64Func.args =
      [{ name := "a", ty := .i 64, role := .owned },
       { name := "b", ty := .i 64, role := .owned }] := rfl
  have hbody : add64Func.body =
      .return_ (.add (.var "a") (.var "b")) := rfl
  have hb : bindMemArgs
      [{ name := "a", ty := .i 64, role := .owned },
       { name := "b", ty := .i 64, role := .owned }]
      [.i64 a, .i64 b] emptyMem =
      some ([("a", .i64 a), ("b", .i64 b)], emptyMem, []) :=
    bindMemArgs_add64 a b
  have ha := envLookup_add64_a a b
  have hbb := envLookup_add64_b a b
  simp only [memEvalFuncFuel, hbf, hbody, hb]
  cases F <;>
    simp only [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      memEvalExpr, add64Fwd, ha, hbb] <;>
    (cases checkedAddI64 a b <;> rfl)

/-- `memEval` for `use_tadd32`: program evaluation over the renamed
    `add` leaf agrees with the delegating forward (mirrors
    `evalProgFunc_useTadd32`; int-only, so `Mem`/`Layout` stay
    `emptyMem`/`[]`). -/
theorem memEvalProgFunc_useTadd32 (F : Nat) (x y : BitVec 32) :
    memEvalProgFunc [{ addFunc with name := "_Z4taddIiET_S0_S0_" }] F
      useTadd32Func [.i32 x, .i32 y] = useTadd32Fwd x y := by
  have hbind : bindMemArgs useTadd32Func.args [.i32 x, .i32 y] emptyMem =
      some ([("x", .i32 x), ("y", .i32 y)], emptyMem, []) :=
    bindMemArgs_useAdd x y
  have hbody : useTadd32Func.body =
      .seq (.callRet "s" "_Z4taddIiET_S0_S0_" ["x", "y"])
           (.return_ (.var "s")) := rfl
  have hx := envLookup_useAddCaller_x x y
  have hy := envLookup_useAddCaller_y x y
  have hfind : findFunc [{ addFunc with name := "_Z4taddIiET_S0_S0_" }]
      "_Z4taddIiET_S0_S0_" =
      some { addFunc with name := "_Z4taddIiET_S0_S0_" } :=
    findFunc_hit { addFunc with name := "_Z4taddIiET_S0_S0_" } []
  have hargs : lookupArgs [("x", .i32 x), ("y", .i32 y)] ["x", "y"] =
      some [.i32 x, .i32 y] := by
    simp [lookupArgs, hx, hy]
  have hcall := memEvalFuncFuel_addAt F "_Z4taddIiET_S0_S0_" x y
  cases hadd : addFwd x y with
  | error e =>
    have hcall' : memEvalFuncFuel F
        { addFunc with name := "_Z4taddIiET_S0_S0_" }
        [.i32 x, .i32 y] = .error e := by
      rw [hcall, hadd]
    have hstep := memEvalProgStmt_callRet_err
      [{ addFunc with name := "_Z4taddIiET_S0_S0_" }]
      F "s" "_Z4taddIiET_S0_S0_" ["x", "y"] [("x", .i32 x), ("y", .i32 y)]
      emptyMem []
      [.i32 x, .i32 y] { addFunc with name := "_Z4taddIiET_S0_S0_" } e
      hargs hfind hcall'
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstep]
    simp [useTadd32Fwd, hadd]
  | ok v =>
    have hcall' : memEvalFuncFuel F
        { addFunc with name := "_Z4taddIiET_S0_S0_" }
        [.i32 x, .i32 y] = .ok v := by
      rw [hcall, hadd]
    have hstep := memEvalProgStmt_callRet_ok
      [{ addFunc with name := "_Z4taddIiET_S0_S0_" }]
      F "s" "_Z4taddIiET_S0_S0_" ["x", "y"] [("x", .i32 x), ("y", .i32 y)]
      emptyMem []
      [.i32 x, .i32 y] { addFunc with name := "_Z4taddIiET_S0_S0_" } v
      hargs hfind hcall'
    have hret : memEvalProgStmt
        [{ addFunc with name := "_Z4taddIiET_S0_S0_" }] F
        (.return_ (.var "s")) (envExtend [("x", .i32 x), ("y", .i32 y)] "s" v)
        emptyMem [] =
        .ok (((envExtend [("x", .i32 x), ("y", .i32 y)] "s" v,
          emptyMem, []), .returned v)) :=
      memEvalProgStmt_return
        [{ addFunc with name := "_Z4taddIiET_S0_S0_" }] F (.var "s") _
        _ _ v (by simp [memEvalExpr, envExtend_hit])
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep, hret]
    simp [useTadd32Fwd, hadd]

/-- Transfer for `use_tadd32` (program level): both sides equal
    `useTadd32Fwd`. -/
theorem memTransferProg_useTadd32 (F : Nat) (x y : BitVec 32)
    (_h : oracleNoalias useTadd32Func [.i32 x, .i32 y]) :
    memEvalProgFunc [{ addFunc with name := "_Z4taddIiET_S0_S0_" }] F
      useTadd32Func [.i32 x, .i32 y] =
      evalProgFunc [{ addFunc with name := "_Z4taddIiET_S0_S0_" }] F
        useTadd32Func [.i32 x, .i32 y] := by
  rw [memEvalProgFunc_useTadd32, evalProgFunc_useTadd32]

/-- `memEval` for `use_tadd64`: same proof at width 64 over the
    renamed `add64` leaf. -/
theorem memEvalProgFunc_useTadd64 (F : Nat) (x y : BitVec 64) :
    memEvalProgFunc [{ add64Func with name := "_Z4taddIlET_S0_S0_" }] F
      useTadd64Func [.i64 x, .i64 y] = useTadd64Fwd x y := by
  have hbind : bindMemArgs useTadd64Func.args [.i64 x, .i64 y] emptyMem =
      some ([("x", .i64 x), ("y", .i64 y)], emptyMem, []) :=
    bindMemArgs_useTadd64 x y
  have hbody : useTadd64Func.body =
      .seq (.callRet "s" "_Z4taddIlET_S0_S0_" ["x", "y"])
           (.return_ (.var "s")) := rfl
  have hx := envLookup_useTadd64Caller_x x y
  have hy := envLookup_useTadd64Caller_y x y
  have hfind : findFunc [{ add64Func with name := "_Z4taddIlET_S0_S0_" }]
      "_Z4taddIlET_S0_S0_" =
      some { add64Func with name := "_Z4taddIlET_S0_S0_" } :=
    findFunc_hit { add64Func with name := "_Z4taddIlET_S0_S0_" } []
  have hargs : lookupArgs [("x", .i64 x), ("y", .i64 y)] ["x", "y"] =
      some [.i64 x, .i64 y] := by
    simp [lookupArgs, hx, hy]
  have hcall := memEvalFuncFuel_add64At F "_Z4taddIlET_S0_S0_" x y
  cases hadd : add64Fwd x y with
  | error e =>
    have hcall' : memEvalFuncFuel F
        { add64Func with name := "_Z4taddIlET_S0_S0_" }
        [.i64 x, .i64 y] = .error e := by
      rw [hcall, hadd]
    have hstep := memEvalProgStmt_callRet_err
      [{ add64Func with name := "_Z4taddIlET_S0_S0_" }]
      F "s" "_Z4taddIlET_S0_S0_" ["x", "y"] [("x", .i64 x), ("y", .i64 y)]
      emptyMem []
      [.i64 x, .i64 y] { add64Func with name := "_Z4taddIlET_S0_S0_" } e
      hargs hfind hcall'
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstep]
    simp [useTadd64Fwd, hadd]
  | ok v =>
    have hcall' : memEvalFuncFuel F
        { add64Func with name := "_Z4taddIlET_S0_S0_" }
        [.i64 x, .i64 y] = .ok v := by
      rw [hcall, hadd]
    have hstep := memEvalProgStmt_callRet_ok
      [{ add64Func with name := "_Z4taddIlET_S0_S0_" }]
      F "s" "_Z4taddIlET_S0_S0_" ["x", "y"] [("x", .i64 x), ("y", .i64 y)]
      emptyMem []
      [.i64 x, .i64 y] { add64Func with name := "_Z4taddIlET_S0_S0_" } v
      hargs hfind hcall'
    have hret : memEvalProgStmt
        [{ add64Func with name := "_Z4taddIlET_S0_S0_" }] F
        (.return_ (.var "s")) (envExtend [("x", .i64 x), ("y", .i64 y)] "s" v)
        emptyMem [] =
        .ok (((envExtend [("x", .i64 x), ("y", .i64 y)] "s" v,
          emptyMem, []), .returned v)) :=
      memEvalProgStmt_return
        [{ add64Func with name := "_Z4taddIlET_S0_S0_" }] F (.var "s") _
        _ _ v (by simp [memEvalExpr, envExtend_hit])
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep, hret]
    simp [useTadd64Fwd, hadd]

/-- Transfer for `use_tadd64` (program level): both sides equal
    `useTadd64Fwd`. -/
theorem memTransferProg_useTadd64 (F : Nat) (x y : BitVec 64)
    (_h : oracleNoalias useTadd64Func [.i64 x, .i64 y]) :
    memEvalProgFunc [{ add64Func with name := "_Z4taddIlET_S0_S0_" }] F
      useTadd64Func [.i64 x, .i64 y] =
      evalProgFunc [{ add64Func with name := "_Z4taddIlET_S0_S0_" }] F
        useTadd64Func [.i64 x, .i64 y] := by
  rw [memEvalProgFunc_useTadd64, evalProgFunc_useTadd64]

