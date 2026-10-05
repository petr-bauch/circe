/-
Circe.Transfer.GrowEntry — N4d-iv-b2 `vec_push_sum` entry transfer.
Over `Circe.Transfer.GrowEmplace`.
-/
import Circe.Transfer.GrowEmplace

/-! ## N4d-iv-b2 `vec_push_sum` entry: memory agreement -/

/-- `memEval` for the closed entry: sixteen steps over `emptyMem`/`[]`
    (no caller footprint; every callee runs on its own binding) agree
    with `vecPushSumEntryFwd`. Mirrors `evalProgFunc_vecPushSumEntry`
    step for step. -/
theorem memEvalProgFunc_vecPushSumEntry (F : Nat) (hF : 6 ≤ F) :
    memEvalProgFunc vecGrowProg F vecPushSumEntryFunc [] =
      vecPushSumEntryFwd := by
  obtain ⟨F', rfl, hF'⟩ := fuel_step_down 5 hF
  have hbind : bindMemArgs vecPushSumEntryFunc.args [] emptyMem =
      some ([], emptyMem, []) := rfl
  have hbody : vecPushSumEntryFunc.body =
      .seq (.callRet "v0" stdVecCtorName [])
      (.seq (.let_ "c0" (.i 32) (.lit (.i32 (BitVec.ofNat 32 1))))
      (.seq (.callProg "v1" stdVecPushBackName ["v0", "c0"])
      (.seq (.let_ "c1" (.i 32) (.lit (.i32 (BitVec.ofNat 32 2))))
      (.seq (.callProg "v2" stdVecPushBackName ["v1", "c1"])
      (.seq (.let_ "c2" (.i 32) (.lit (.i32 (BitVec.ofNat 32 3))))
      (.seq (.callProg "v3" stdVecPushBackName ["v2", "c2"])
      (.seq (.let_ "n0" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.seq (.callRet "e0" stdVecGrowIndexName ["v3", "n0"])
      (.seq (.let_ "n1" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      (.seq (.callRet "e1" stdVecGrowIndexName ["v3", "n1"])
      (.seq (.let_ "n2" (.u 64) (.lit (.u64 (BitVec.ofNat 64 2))))
      (.seq (.callRet "e2" stdVecGrowIndexName ["v3", "n2"])
      (.seq (.let_ "s1" (.i 32) (.add (.var "e0") (.var "e1")))
      (.seq (.let_ "s2" (.i 32) (.add (.var "s1") (.var "e2")))
      (.seq (.callRet "v4" stdVecDtorName ["v3"])
        (.return_ (.var "s2"))))))))))))))))) := rfl
  -- Concrete triples threaded through the entry.
  have hP1 : stdVecPushBackFwd ⟨[], false⟩ 0 0 (BitVec.ofNat 32 1) =
      .ok (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1) := rfl
  have hP2 : stdVecPushBackFwd ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1
      (BitVec.ofNat 32 2) =
      .ok (.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2) := rfl
  -- The third push leaves the spare capacity word zeroed.
  have hP3 : stdVecPushBackFwd
      ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2
      (BitVec.ofNat 32 3) =
      .ok (.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4) := rfl
  have hE0 : stdVecGrowIndexFwd
      ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
        (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3
      (BitVec.ofNat 64 0) =
      .ok (.i32 (BitVec.ofNat 32 1)) := rfl
  have hE1 : stdVecGrowIndexFwd
      ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
        (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3
      (BitVec.ofNat 64 1) =
      .ok (.i32 (BitVec.ofNat 32 2)) := rfl
  have hE2 : stdVecGrowIndexFwd
      ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
        (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3
      (BitVec.ofNat 64 2) =
      .ok (.i32 (BitVec.ofNat 32 3)) := rfl
  have hA1 : checkedAddI32 (BitVec.ofNat 32 1) (BitVec.ofNat 32 2) =
      .ok (BitVec.ofNat 32 3) := rfl
  have hA2 : checkedAddI32 (BitVec.ofNat 32 3) (BitVec.ofNat 32 3) =
      .ok (BitVec.ofNat 32 6) := rfl
  have hD : stdVecDtorFwd
      ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
        (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4 =
      .ok (.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], true⟩ 3 4) := rfl
  -- Step 1: the default ctor.
  have hargs0 : lookupArgs ([] : Env) [] = some [] := rfl
  have hFwd0 : stdVecEmptyCtorFwd =
      .ok (.stdVecOwned ⟨[], false⟩ 0 0) := rfl
  have hmcall0 : memEvalFuncFuel (F' + 1) stdVecEmptyCtorFunc [] =
      .ok (.stdVecOwned ⟨[], false⟩ 0 0) := by
    rw [memEvalFuncFuel_stdVecEmptyCtor, hFwd0]
  have hmstepV0 : memEvalProgStmt vecGrowProg (F' + 1)
      (.callRet "v0" stdVecCtorName [])
      ([] : Env) emptyMem [] =
      .ok ((envExtend ([] : Env) "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0), emptyMem, []),
        .fellThrough) :=
    memEvalProgStmt_callRet_ok vecGrowProg (F' + 1) "v0"
      stdVecCtorName [] _ emptyMem [] _ stdVecEmptyCtorFunc
      (.stdVecOwned ⟨[], false⟩ 0 0)
      hargs0 findFunc_stdVecEmptyCtor hmcall0
  -- Step 2: `c0 = 1`.
  have hlitC0 : evalExpr (.lit (.i32 (BitVec.ofNat 32 1)))
      (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0)) =
      .ok (.i32 (BitVec.ofNat 32 1)) := by
    simp [evalExpr, litVal]
  have hmstepC0 : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "c0" (.i 32) (.lit (.i32 (BitVec.ofNat 32 1))))
      (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0)) emptyMem [] =
      .ok ((envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)), emptyMem, []),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h)
      (memEvalExpr_lit _ _ _ _) hlitC0
  -- Step 3: first push.
  have hv0 : envLookup
      (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1))) "v0" =
      some (.stdVecOwned ⟨[], false⟩ 0 0) := by
    simp [envLookup, envExtend,
      show ("v0" : String) ≠ "c0" by decide]
  have hc0 : envLookup
      (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1))) "c0" =
      some (.i32 (BitVec.ofNat 32 1)) := by
    simp [envLookup, envExtend]
  have hargs1 : lookupArgs
      (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1))) ["v0", "c0"] =
      some [.stdVecOwned ⟨[], false⟩ 0 0,
        .i32 (BitVec.ofNat 32 1)] := by
    simp only [lookupArgs, hv0, hc0]
  have hmcall1 : memEvalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned ⟨[], false⟩ 0 0, .i32 (BitVec.ofNat 32 1)] =
      stdVecPushBackFwd ⟨[], false⟩ 0 0 (BitVec.ofNat 32 1) :=
    memEvalProgFunc_stdVecPushBack F' _ 0 0 _ rfl (by decide)
      (Nat.zero_le _) (by decide) (by decide) (by omega)
  have hmcall1' : memEvalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned ⟨[], false⟩ 0 0, .i32 (BitVec.ofNat 32 1)] =
      .ok (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1) := by
    rw [hmcall1, hP1]
  have hmstepV1 : memEvalProgStmt vecGrowProg (F' + 1)
      (.callProg "v1" stdVecPushBackName ["v0", "c0"])
      (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1))) emptyMem [] =
      .ok ((envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1),
        emptyMem, []), .fellThrough) :=
    memEvalProgStmt_callProg_ok vecGrowProg F' "v1"
      stdVecPushBackName ["v0", "c0"] _ emptyMem [] _ stdVecPushBackFunc
      (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1)
      hargs1 findFunc_stdVecPushBack hmcall1'
  -- Step 4: `c1 = 2`.
  have hlitC1 : evalExpr (.lit (.i32 (BitVec.ofNat 32 2)))
      (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1)) =
      .ok (.i32 (BitVec.ofNat 32 2)) := by
    simp [evalExpr, litVal]
  have hmstepC1 : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "c1" (.i 32) (.lit (.i32 (BitVec.ofNat 32 2))))
      (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
      emptyMem [] =
      .ok ((envExtend (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)), emptyMem, []),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h)
      (memEvalExpr_lit _ _ _ _) hlitC1
  -- Step 5: second push.
  have hv1 : envLookup
      (envExtend (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2))) "v1" =
      some (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1) := by
    simp [envLookup, envExtend,
      show ("v1" : String) ≠ "c1" by decide]
  have hc1 : envLookup
      (envExtend (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2))) "c1" =
      some (.i32 (BitVec.ofNat 32 2)) := by
    simp [envLookup, envExtend]
  have hargs2 : lookupArgs
      (envExtend (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2))) ["v1", "c1"] =
      some [.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1,
        .i32 (BitVec.ofNat 32 2)] := by
    simp only [lookupArgs, hv1, hc1]
  have hmcall2 : memEvalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1,
        .i32 (BitVec.ofNat 32 2)] =
      stdVecPushBackFwd ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1
        (BitVec.ofNat 32 2) :=
    memEvalProgFunc_stdVecPushBack F' _ 1 1 _ rfl (by decide)
      (by decide) (by decide) (by decide) (by omega)
  have hmcall2' : memEvalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1,
        .i32 (BitVec.ofNat 32 2)] =
      .ok (.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2) := by
    rw [hmcall2, hP2]
  have hmstepV2 : memEvalProgStmt vecGrowProg (F' + 1)
      (.callProg "v2" stdVecPushBackName ["v1", "c1"])
      (envExtend (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2))) emptyMem [] =
      .ok ((envExtend (envExtend (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2),
        emptyMem, []), .fellThrough) :=
    memEvalProgStmt_callProg_ok vecGrowProg F' "v2"
      stdVecPushBackName ["v1", "c1"] _ emptyMem [] _ stdVecPushBackFunc
      (.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2)
      hargs2 findFunc_stdVecPushBack hmcall2'
  -- Step 6: `c2 = 3`.
  have hlitC2 : evalExpr (.lit (.i32 (BitVec.ofNat 32 3)))
      (envExtend (envExtend (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2)) =
      .ok (.i32 (BitVec.ofNat 32 3)) := by
    simp [evalExpr, litVal]
  have hmstepC2 : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "c2" (.i 32) (.lit (.i32 (BitVec.ofNat 32 3))))
      (envExtend (envExtend (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
      emptyMem [] =
      .ok ((envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)), emptyMem, []),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h)
      (memEvalExpr_lit _ _ _ _) hlitC2
  -- Step 7: third push.
  have hv2 : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3))) "v2" =
      some (.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2) := by
    simp [envLookup, envExtend,
      show ("v2" : String) ≠ "c2" by decide]
  have hc2 : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3))) "c2" =
      some (.i32 (BitVec.ofNat 32 3)) := by
    simp [envLookup, envExtend]
  have hargs3 : lookupArgs
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3))) ["v2", "c2"] =
      some [.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2,
        .i32 (BitVec.ofNat 32 3)] := by
    simp only [lookupArgs, hv2, hc2]
  have hmcall3 : memEvalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2,
        .i32 (BitVec.ofNat 32 3)] =
      stdVecPushBackFwd
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2
        (BitVec.ofNat 32 3) :=
    memEvalProgFunc_stdVecPushBack F' _ 2 2 _ rfl (by decide)
      (by decide) (by decide) (by decide) (by omega)
  have hmcall3' : memEvalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2,
        .i32 (BitVec.ofNat 32 3)] =
      .ok (.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4) := by
    rw [hmcall3, hP3]
  have hmstepV3 : memEvalProgStmt vecGrowProg (F' + 1)
      (.callProg "v3" stdVecPushBackName ["v2", "c2"])
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3))) emptyMem [] =
      .ok ((envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)))
        "v3" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4),
        emptyMem, []), .fellThrough) :=
    memEvalProgStmt_callProg_ok vecGrowProg F' "v3"
      stdVecPushBackName ["v2", "c2"] _ emptyMem [] _ stdVecPushBackFunc
      (.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4)
      hargs3 findFunc_stdVecPushBack hmcall3'
  -- Step 8: `n0 = 0`.
  have hlitN0 : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)))
        "v3" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4)) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  have hmstepN0 : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "n0" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)))
        "v3" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
      emptyMem [] =
      .ok ((envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)))
        "v3" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
        "n0" (.u64 (BitVec.ofNat 64 0)), emptyMem, []),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h)
      (memEvalExpr_lit _ _ _ _) hlitN0
  -- Step 9: first read.
  have hv3n : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)))
        "v3" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
        "n0" (.u64 (BitVec.ofNat 64 0))) "v3" =
      some (.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4) := by
    simp [envLookup, envExtend,
      show ("v3" : String) ≠ "n0" by decide]
  have hn0 : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)))
        "v3" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
        "n0" (.u64 (BitVec.ofNat 64 0))) "n0" =
      some (.u64 (BitVec.ofNat 64 0)) := by
    simp [envLookup, envExtend]
  have hargsE0 : lookupArgs
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)))
        "v3" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
        "n0" (.u64 (BitVec.ofNat 64 0))) ["v3", "n0"] =
      some [.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4,
        .u64 (BitVec.ofNat 64 0)] := by
    simp only [lookupArgs, hv3n, hn0]
  have hget0 : ([(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
      (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)][
      (BitVec.ofNat 64 0).toNat]? =
      some (BitVec.ofNat 32 1)) := by decide
  have hlt0 : (BitVec.ofNat 64 0).toNat < 3 := by decide
  have hmcallE0 : memEvalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4,
        .u64 (BitVec.ofNat 64 0)] =
      stdVecGrowIndexFwd
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3
        (BitVec.ofNat 64 0) :=
    memEvalFuncFuel_stdVecGrowIndex _ _ 3 4 _ rfl _ hget0 hlt0
  have hmcallE0' : memEvalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4,
        .u64 (BitVec.ofNat 64 0)] =
      .ok (.i32 (BitVec.ofNat 32 1)) := by
    rw [hmcallE0, hE0]
  have hmstepE0 : memEvalProgStmt vecGrowProg (F' + 1)
      (.callRet "e0" stdVecGrowIndexName ["v3", "n0"])
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)))
        "v3" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
        "n0" (.u64 (BitVec.ofNat 64 0))) emptyMem [] =
      .ok ((envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)))
        "v3" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)), emptyMem, []),
        .fellThrough) :=
    memEvalProgStmt_callRet_ok vecGrowProg (F' + 1) "e0"
      stdVecGrowIndexName ["v3", "n0"] _ emptyMem [] _
      stdVecGrowIndexFunc (.i32 (BitVec.ofNat 32 1))
      hargsE0 findFunc_stdVecGrowIndex hmcallE0'
  -- Step 10: `n1 = 1`.
  have hlitN1 : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)))
        "v3" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1))) =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have hmstepN1 : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "n1" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)))
        "v3" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
      emptyMem [] =
      .ok ((envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)))
        "v3" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1)), emptyMem, []),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h)
      (memEvalExpr_lit _ _ _ _) hlitN1
  -- Step 11: second read.
  have hv3n1 : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)))
        "v3" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1))) "v3" =
      some (.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4) := by
    simp [envLookup, envExtend,
      show ("v3" : String) ≠ "n1" by decide,
      show ("v3" : String) ≠ "e0" by decide,
      show ("v3" : String) ≠ "n0" by decide]
  have hn1 : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)))
        "v3" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1))) "n1" =
      some (.u64 (BitVec.ofNat 64 1)) := by
    simp [envLookup, envExtend]
  have hargsE1 : lookupArgs
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)))
        "v3" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1))) ["v3", "n1"] =
      some [.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4,
        .u64 (BitVec.ofNat 64 1)] := by
    simp only [lookupArgs, hv3n1, hn1]
  have hget1 : ([(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
      (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)][
      (BitVec.ofNat 64 1).toNat]? =
      some (BitVec.ofNat 32 2)) := by decide
  have hlt1 : (BitVec.ofNat 64 1).toNat < 3 := by decide
  have hmcallE1 : memEvalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4,
        .u64 (BitVec.ofNat 64 1)] =
      stdVecGrowIndexFwd
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3
        (BitVec.ofNat 64 1) :=
    memEvalFuncFuel_stdVecGrowIndex _ _ 3 4 _ rfl _ hget1 hlt1
  have hmcallE1' : memEvalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4,
        .u64 (BitVec.ofNat 64 1)] =
      .ok (.i32 (BitVec.ofNat 32 2)) := by
    rw [hmcallE1, hE1]
  have hmstepE1 : memEvalProgStmt vecGrowProg (F' + 1)
      (.callRet "e1" stdVecGrowIndexName ["v3", "n1"])
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)))
        "v3" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1))) emptyMem [] =
      .ok ((envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)))
        "v3" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1)))
        "e1" (.i32 (BitVec.ofNat 32 2)), emptyMem, []),
        .fellThrough) :=
    memEvalProgStmt_callRet_ok vecGrowProg (F' + 1) "e1"
      stdVecGrowIndexName ["v3", "n1"] _ emptyMem [] _
      stdVecGrowIndexFunc (.i32 (BitVec.ofNat 32 2))
      hargsE1 findFunc_stdVecGrowIndex hmcallE1'
  -- Step 12: `n2 = 2`.
  have hlitN2 : evalExpr (.lit (.u64 (BitVec.ofNat 64 2)))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)))
        "v3" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1)))
        "e1" (.i32 (BitVec.ofNat 32 2))) =
      .ok (.u64 (BitVec.ofNat 64 2)) := by
    simp [evalExpr, litVal]
  have hmstepN2 : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "n2" (.u 64) (.lit (.u64 (BitVec.ofNat 64 2))))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)))
        "v3" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1)))
        "e1" (.i32 (BitVec.ofNat 32 2)))
      emptyMem [] =
      .ok ((envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)))
        "v3" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1)))
        "e1" (.i32 (BitVec.ofNat 32 2)))
        "n2" (.u64 (BitVec.ofNat 64 2)), emptyMem, []),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h)
      (memEvalExpr_lit _ _ _ _) hlitN2
  -- Step 13: third read.
  have hv3n2 : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)))
        "v3" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1)))
        "e1" (.i32 (BitVec.ofNat 32 2)))
        "n2" (.u64 (BitVec.ofNat 64 2))) "v3" =
      some (.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4) := by
    simp [envLookup, envExtend,
      show ("v3" : String) ≠ "n2" by decide,
      show ("v3" : String) ≠ "e1" by decide,
      show ("v3" : String) ≠ "n1" by decide,
      show ("v3" : String) ≠ "e0" by decide,
      show ("v3" : String) ≠ "n0" by decide]
  have hn2 : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)))
        "v3" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1)))
        "e1" (.i32 (BitVec.ofNat 32 2)))
        "n2" (.u64 (BitVec.ofNat 64 2))) "n2" =
      some (.u64 (BitVec.ofNat 64 2)) := by
    simp [envLookup, envExtend]
  have hargsE2 : lookupArgs
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)))
        "v3" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1)))
        "e1" (.i32 (BitVec.ofNat 32 2)))
        "n2" (.u64 (BitVec.ofNat 64 2))) ["v3", "n2"] =
      some [.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4,
        .u64 (BitVec.ofNat 64 2)] := by
    simp only [lookupArgs, hv3n2, hn2]
  have hget2 : ([(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
      (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)][
      (BitVec.ofNat 64 2).toNat]? =
      some (BitVec.ofNat 32 3)) := by decide
  have hlt2 : (BitVec.ofNat 64 2).toNat < 3 := by decide
  have hmcallE2 : memEvalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4,
        .u64 (BitVec.ofNat 64 2)] =
      stdVecGrowIndexFwd
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3
        (BitVec.ofNat 64 2) :=
    memEvalFuncFuel_stdVecGrowIndex _ _ 3 4 _ rfl _ hget2 hlt2
  have hmcallE2' : memEvalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4,
        .u64 (BitVec.ofNat 64 2)] =
      .ok (.i32 (BitVec.ofNat 32 3)) := by
    rw [hmcallE2, hE2]
  have hmstepE2 : memEvalProgStmt vecGrowProg (F' + 1)
      (.callRet "e2" stdVecGrowIndexName ["v3", "n2"])
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)))
        "v3" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1)))
        "e1" (.i32 (BitVec.ofNat 32 2)))
        "n2" (.u64 (BitVec.ofNat 64 2))) emptyMem [] =
      .ok ((envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend [] "v0"
            (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)))
        "v3" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1)))
        "e1" (.i32 (BitVec.ofNat 32 2)))
        "n2" (.u64 (BitVec.ofNat 64 2)))
        "e2" (.i32 (BitVec.ofNat 32 3)), emptyMem, []),
        .fellThrough) :=
    memEvalProgStmt_callRet_ok vecGrowProg (F' + 1) "e2"
      stdVecGrowIndexName ["v3", "n2"] _ emptyMem [] _
      stdVecGrowIndexFunc (.i32 (BitVec.ofNat 32 3))
      hargsE2 findFunc_stdVecGrowIndex hmcallE2'
  -- Step 14: `s1 = e0 + e1`.
  have he0 : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend [] "v0"
            (.stdVecOwned ⟨[], false⟩ 0 0))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v2" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
          "c2" (.i32 (BitVec.ofNat 32 3)))
          "v3" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "n2" (.u64 (BitVec.ofNat 64 2)))
          "e2" (.i32 (BitVec.ofNat 32 3))) "e0" =
      some (.i32 (BitVec.ofNat 32 1)) := by
    simp [envLookup, envExtend,
      show ("e0" : String) ≠ "e2" by decide,
      show ("e0" : String) ≠ "n2" by decide,
      show ("e0" : String) ≠ "e1" by decide,
      show ("e0" : String) ≠ "n1" by decide]
  have he1 : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend [] "v0"
            (.stdVecOwned ⟨[], false⟩ 0 0))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v2" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
          "c2" (.i32 (BitVec.ofNat 32 3)))
          "v3" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "n2" (.u64 (BitVec.ofNat 64 2)))
          "e2" (.i32 (BitVec.ofNat 32 3))) "e1" =
      some (.i32 (BitVec.ofNat 32 2)) := by
    simp [envLookup, envExtend,
      show ("e1" : String) ≠ "e2" by decide,
      show ("e1" : String) ≠ "n2" by decide]
  have hs1E : evalExpr (.add (.var "e0") (.var "e1"))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend [] "v0"
            (.stdVecOwned ⟨[], false⟩ 0 0))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v2" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
          "c2" (.i32 (BitVec.ofNat 32 3)))
          "v3" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "n2" (.u64 (BitVec.ofNat 64 2)))
          "e2" (.i32 (BitVec.ofNat 32 3))) =
      .ok (.i32 (BitVec.ofNat 32 3)) := by
    cir_step evalExpr [he0, he1, hA1]
  have hmagreeS1 : memEvalExpr (.add (.var "e0") (.var "e1"))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend [] "v0"
            (.stdVecOwned ⟨[], false⟩ 0 0))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v2" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
          "c2" (.i32 (BitVec.ofNat 32 3)))
          "v3" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "n2" (.u64 (BitVec.ofNat 64 2)))
          "e2" (.i32 (BitVec.ofNat 32 3))) emptyMem [] =
      evalExpr (.add (.var "e0") (.var "e1"))
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend (envExtend
            (envExtend (envExtend (envExtend [] "v0"
              (.stdVecOwned ⟨[], false⟩ 0 0))
            "c0" (.i32 (BitVec.ofNat 32 1)))
            "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
            "c1" (.i32 (BitVec.ofNat 32 2)))
            "v2" (.stdVecOwned
              ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
            "c2" (.i32 (BitVec.ofNat 32 3)))
            "v3" (.stdVecOwned
              ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
                (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
            "n0" (.u64 (BitVec.ofNat 64 0)))
            "e0" (.i32 (BitVec.ofNat 32 1)))
            "n1" (.u64 (BitVec.ofNat 64 1)))
            "e1" (.i32 (BitVec.ofNat 32 2)))
            "n2" (.u64 (BitVec.ofNat 64 2)))
            "e2" (.i32 (BitVec.ofNat 32 3))) := by
    simp only [memEvalExpr, evalExpr, he0, he1]
  have hmstepS1 : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "s1" (.i 32) (.add (.var "e0") (.var "e1")))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend [] "v0"
            (.stdVecOwned ⟨[], false⟩ 0 0))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v2" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
          "c2" (.i32 (BitVec.ofNat 32 3)))
          "v3" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "n2" (.u64 (BitVec.ofNat 64 2)))
          "e2" (.i32 (BitVec.ofNat 32 3))) emptyMem [] =
      .ok ((envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend [] "v0"
            (.stdVecOwned ⟨[], false⟩ 0 0))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v2" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
          "c2" (.i32 (BitVec.ofNat 32 3)))
          "v3" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "n2" (.u64 (BitVec.ofNat 64 2)))
          "e2" (.i32 (BitVec.ofNat 32 3)))
          "s1" (.i32 (BitVec.ofNat 32 3)), emptyMem, []),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h)
      hmagreeS1 hs1E
  -- Step 15: `s2 = s1 + e2`.
  have hs1 : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend [] "v0"
            (.stdVecOwned ⟨[], false⟩ 0 0))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v2" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
          "c2" (.i32 (BitVec.ofNat 32 3)))
          "v3" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "n2" (.u64 (BitVec.ofNat 64 2)))
          "e2" (.i32 (BitVec.ofNat 32 3)))
          "s1" (.i32 (BitVec.ofNat 32 3))) "s1" =
      some (.i32 (BitVec.ofNat 32 3)) := by
    simp [envLookup, envExtend]
  have he2s : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend [] "v0"
            (.stdVecOwned ⟨[], false⟩ 0 0))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v2" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
          "c2" (.i32 (BitVec.ofNat 32 3)))
          "v3" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "n2" (.u64 (BitVec.ofNat 64 2)))
          "e2" (.i32 (BitVec.ofNat 32 3)))
          "s1" (.i32 (BitVec.ofNat 32 3))) "e2" =
      some (.i32 (BitVec.ofNat 32 3)) := by
    simp [envLookup, envExtend,
      show ("e2" : String) ≠ "s1" by decide]
  have hs2E : evalExpr (.add (.var "s1") (.var "e2"))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend [] "v0"
            (.stdVecOwned ⟨[], false⟩ 0 0))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v2" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
          "c2" (.i32 (BitVec.ofNat 32 3)))
          "v3" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "n2" (.u64 (BitVec.ofNat 64 2)))
          "e2" (.i32 (BitVec.ofNat 32 3)))
          "s1" (.i32 (BitVec.ofNat 32 3))) =
      .ok (.i32 (BitVec.ofNat 32 6)) := by
    cir_step evalExpr [hs1, he2s, hA2]
  have hmagreeS2 : memEvalExpr (.add (.var "s1") (.var "e2"))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend [] "v0"
            (.stdVecOwned ⟨[], false⟩ 0 0))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v2" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
          "c2" (.i32 (BitVec.ofNat 32 3)))
          "v3" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "n2" (.u64 (BitVec.ofNat 64 2)))
          "e2" (.i32 (BitVec.ofNat 32 3)))
          "s1" (.i32 (BitVec.ofNat 32 3))) emptyMem [] =
      evalExpr (.add (.var "s1") (.var "e2"))
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend (envExtend
            (envExtend (envExtend (envExtend (envExtend [] "v0"
              (.stdVecOwned ⟨[], false⟩ 0 0))
            "c0" (.i32 (BitVec.ofNat 32 1)))
            "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
            "c1" (.i32 (BitVec.ofNat 32 2)))
            "v2" (.stdVecOwned
              ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
            "c2" (.i32 (BitVec.ofNat 32 3)))
            "v3" (.stdVecOwned
              ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
                (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
            "n0" (.u64 (BitVec.ofNat 64 0)))
            "e0" (.i32 (BitVec.ofNat 32 1)))
            "n1" (.u64 (BitVec.ofNat 64 1)))
            "e1" (.i32 (BitVec.ofNat 32 2)))
            "n2" (.u64 (BitVec.ofNat 64 2)))
            "e2" (.i32 (BitVec.ofNat 32 3)))
            "s1" (.i32 (BitVec.ofNat 32 3))) := by
    simp only [memEvalExpr, evalExpr, hs1, he2s]
  have hmstepS2 : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "s2" (.i 32) (.add (.var "s1") (.var "e2")))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend [] "v0"
            (.stdVecOwned ⟨[], false⟩ 0 0))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v2" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
          "c2" (.i32 (BitVec.ofNat 32 3)))
          "v3" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "n2" (.u64 (BitVec.ofNat 64 2)))
          "e2" (.i32 (BitVec.ofNat 32 3)))
          "s1" (.i32 (BitVec.ofNat 32 3))) emptyMem [] =
      .ok ((envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend (envExtend [] "v0"
            (.stdVecOwned ⟨[], false⟩ 0 0))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v2" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
          "c2" (.i32 (BitVec.ofNat 32 3)))
          "v3" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "n2" (.u64 (BitVec.ofNat 64 2)))
          "e2" (.i32 (BitVec.ofNat 32 3)))
          "s1" (.i32 (BitVec.ofNat 32 3)))
          "s2" (.i32 (BitVec.ofNat 32 6)), emptyMem, []),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h)
      hmagreeS2 hs2E
  -- Step 16: the `cleanup`-normal destructor.
  have hv3d : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend (envExtend [] "v0"
            (.stdVecOwned ⟨[], false⟩ 0 0))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v2" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
          "c2" (.i32 (BitVec.ofNat 32 3)))
          "v3" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "n2" (.u64 (BitVec.ofNat 64 2)))
          "e2" (.i32 (BitVec.ofNat 32 3)))
          "s1" (.i32 (BitVec.ofNat 32 3)))
          "s2" (.i32 (BitVec.ofNat 32 6))) "v3" =
      some (.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4) := by
    simp [envLookup, envExtend,
      show ("v3" : String) ≠ "s2" by decide,
      show ("v3" : String) ≠ "s1" by decide,
      show ("v3" : String) ≠ "e2" by decide,
      show ("v3" : String) ≠ "n2" by decide,
      show ("v3" : String) ≠ "e1" by decide,
      show ("v3" : String) ≠ "n1" by decide,
      show ("v3" : String) ≠ "e0" by decide,
      show ("v3" : String) ≠ "n0" by decide]
  have hargsD : lookupArgs
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend (envExtend [] "v0"
            (.stdVecOwned ⟨[], false⟩ 0 0))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v2" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
          "c2" (.i32 (BitVec.ofNat 32 3)))
          "v3" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "n2" (.u64 (BitVec.ofNat 64 2)))
          "e2" (.i32 (BitVec.ofNat 32 3)))
          "s1" (.i32 (BitVec.ofNat 32 3)))
          "s2" (.i32 (BitVec.ofNat 32 6))) ["v3"] =
      some [.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4] := by
    simp only [lookupArgs, hv3d]
  have hmcallD : memEvalFuncFuel (F' + 1) stdVecDtorFunc
      [.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4] =
      stdVecDtorFwd
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4 :=
    memEvalFuncFuel_stdVecDtor _ _ 3 4 (by decide) rfl
  have hmcallD' : memEvalFuncFuel (F' + 1) stdVecDtorFunc
      [.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4] =
      .ok (.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], true⟩ 3 4) := by
    rw [hmcallD, hD]
  have hmstepV4 : memEvalProgStmt vecGrowProg (F' + 1)
      (.callRet "v4" stdVecDtorName ["v3"])
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend (envExtend [] "v0"
            (.stdVecOwned ⟨[], false⟩ 0 0))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v2" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
          "c2" (.i32 (BitVec.ofNat 32 3)))
          "v3" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "n2" (.u64 (BitVec.ofNat 64 2)))
          "e2" (.i32 (BitVec.ofNat 32 3)))
          "s1" (.i32 (BitVec.ofNat 32 3)))
          "s2" (.i32 (BitVec.ofNat 32 6))) emptyMem [] =
      .ok ((envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend (envExtend
            (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v2" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
          "c2" (.i32 (BitVec.ofNat 32 3)))
          "v3" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "n2" (.u64 (BitVec.ofNat 64 2)))
          "e2" (.i32 (BitVec.ofNat 32 3)))
          "s1" (.i32 (BitVec.ofNat 32 3)))
          "s2" (.i32 (BitVec.ofNat 32 6)))
          "v4" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], true⟩ 3 4),
        emptyMem, []), .fellThrough) :=
    memEvalProgStmt_callRet_ok vecGrowProg (F' + 1) "v4"
      stdVecDtorName ["v3"] _ emptyMem [] _ stdVecDtorFunc
      (.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], true⟩ 3 4)
      hargsD findFunc_stdVecDtor hmcallD'
  -- Step 17: return the sum.
  have hs2r : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend (envExtend
            (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v2" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
          "c2" (.i32 (BitVec.ofNat 32 3)))
          "v3" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "n2" (.u64 (BitVec.ofNat 64 2)))
          "e2" (.i32 (BitVec.ofNat 32 3)))
          "s1" (.i32 (BitVec.ofNat 32 3)))
          "s2" (.i32 (BitVec.ofNat 32 6)))
          "v4" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], true⟩ 3 4)) "s2" =
      some (.i32 (BitVec.ofNat 32 6)) := by
    simp [envLookup, envExtend,
      show ("s2" : String) ≠ "v4" by decide]
  have hrE : evalExpr (.var "s2")
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend (envExtend
            (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v2" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
          "c2" (.i32 (BitVec.ofNat 32 3)))
          "v3" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "n2" (.u64 (BitVec.ofNat 64 2)))
          "e2" (.i32 (BitVec.ofNat 32 3)))
          "s1" (.i32 (BitVec.ofNat 32 3)))
          "s2" (.i32 (BitVec.ofNat 32 6)))
          "v4" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], true⟩ 3 4)) =
      .ok (.i32 (BitVec.ofNat 32 6)) := by
    simp [evalExpr, envLookup, envExtend]
  have hrmem : memEvalExpr (.var "s2")
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend (envExtend
            (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v2" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
          "c2" (.i32 (BitVec.ofNat 32 3)))
          "v3" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "n2" (.u64 (BitVec.ofNat 64 2)))
          "e2" (.i32 (BitVec.ofNat 32 3)))
          "s1" (.i32 (BitVec.ofNat 32 3)))
          "s2" (.i32 (BitVec.ofNat 32 6)))
          "v4" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], true⟩ 3 4))
      emptyMem [] =
      .ok (.i32 (BitVec.ofNat 32 6)) := by
    rw [memEvalExpr_var]; exact hrE
  have hmret : memEvalProgStmt vecGrowProg (F' + 1)
      (.return_ (.var "s2"))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend (envExtend
            (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v2" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
          "c2" (.i32 (BitVec.ofNat 32 3)))
          "v3" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "n2" (.u64 (BitVec.ofNat 64 2)))
          "e2" (.i32 (BitVec.ofNat 32 3)))
          "s1" (.i32 (BitVec.ofNat 32 3)))
          "s2" (.i32 (BitVec.ofNat 32 6)))
          "v4" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], true⟩ 3 4))
      emptyMem [] =
      .ok (((envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend (envExtend
            (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v2" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
          "c2" (.i32 (BitVec.ofNat 32 3)))
          "v3" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "n2" (.u64 (BitVec.ofNat 64 2)))
          "e2" (.i32 (BitVec.ofNat 32 3)))
          "s1" (.i32 (BitVec.ofNat 32 3)))
          "s2" (.i32 (BitVec.ofNat 32 6)))
          "v4" (.stdVecOwned
            ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], true⟩ 3 4)),
        emptyMem, []),
        .returned (.i32 (BitVec.ofNat 32 6))) :=
    memEvalProgStmt_return vecGrowProg (F' + 1) _ _ _ _ _ hrmem
  simp only [memEvalProgFunc, hbind, hbody]
  rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepV0,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepC0,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepV1,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepC1,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepV2,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepC2,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepV3,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepN0,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepE0,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepN1,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepE1,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepN2,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepE2,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepS1,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepS2,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepV4, hmret]
  simp only [vecPushSumEntryFwd, hP1, hP2, hP3, hE0, hE1, hE2, hA1, hA2, hD,
    vecGrow_bind_ok, vecGrowOwned, vecGrowI32]

/-- Transfer for the closed entry: program evaluation over the proved
    composer agrees on both sides (no caller footprint; the empty
    layout from `oracleNoalias_vecPushSumEntry` suffices). -/
theorem memTransfer_vecPushSumEntry (F : Nat) (hF : 6 ≤ F)
    (_h : oracleNoalias vecPushSumEntryFunc []) :
    memEvalProgFunc vecGrowProg F vecPushSumEntryFunc [] =
      evalProgFunc vecGrowProg F vecPushSumEntryFunc [] := by
  rw [memEvalProgFunc_vecPushSumEntry F hF, evalProgFunc_vecPushSumEntry F hF]



