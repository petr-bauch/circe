/-
Circe.Emit.VecCompose.Entry — the closed `vec_push_sum` entry over the
proved composers, over `Circe.Emit.VecCompose.Emplace`.
-/
import Circe.Emit.Fragment
import Circe.Emit.VecGrow
import Circe.Emit.VecCompose.Emplace

/-! ## N4d-iv-b2: the `vec_push_sum` entry -/

/-- Mangled name of the `vec_push_sum` entry. -/
def vecPushSumEntryName : String :=
  "_Z12vec_push_sumv"

/-- Canonical CoreIR for `vec_push_sum`: the default ctor is a
    `callRet` into the frozen empty-triple leaf; the three
    `ref.tmp` const/store allocas fuse to direct `i32` lets feeding
    three `callProg`s into the proved `push_back` forwarder; the
    three `operator[]` calls are `callRet`s into the entry-scoped
    index leaf (caller-side loads fused); the two `nsw` adds are
    plain lets; the `cleanup`-normal destructor is an explicit
    `callRet` into the frozen dtor leaf (the `cleanup` wrapper fuses
    away, the `box_through` precedent) and the trailing `cir.trap`
    has no model (unreachable after the join). Returns the final
    sum directly. -/
def vecPushSumEntryFunc : Func :=
  ⟨vecPushSumEntryName, [], .i 32,
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
     (.return_ (.var "s2")))))))))))))))))⟩

/-- Value-level forward for `vec_push_sum`: build `[1, 2, 3]` through
    the proved forwarder, read back all three words, add them with
    `checkedAddI32`, run the destructor, return the sum. -/
def vecPushSumEntryFwd : Result Value :=
  (stdVecPushBackFwd ⟨[], false⟩ 0 0 (BitVec.ofNat 32 1)).bind fun v1 =>
  (vecGrowOwned v1).bind fun (b1, l1, c1) =>
  (stdVecPushBackFwd b1 l1 c1 (BitVec.ofNat 32 2)).bind fun v2 =>
  (vecGrowOwned v2).bind fun (b2, l2, c2) =>
  (stdVecPushBackFwd b2 l2 c2 (BitVec.ofNat 32 3)).bind fun v3 =>
  (vecGrowOwned v3).bind fun (b3, l3, c3) =>
  (stdVecGrowIndexFwd b3 l3 (BitVec.ofNat 64 0)).bind fun e0v =>
  (vecGrowI32 e0v).bind fun e0 =>
  (stdVecGrowIndexFwd b3 l3 (BitVec.ofNat 64 1)).bind fun e1v =>
  (vecGrowI32 e1v).bind fun e1 =>
  (stdVecGrowIndexFwd b3 l3 (BitVec.ofNat 64 2)).bind fun e2v =>
  (vecGrowI32 e2v).bind fun e2 =>
  ((checkedAddI32 e0 e1).bind fun s1 =>
   (checkedAddI32 s1 e2)).bind fun s2 =>
  (stdVecDtorFwd b3 l3 c3).bind fun _ =>
  .ok (.i32 s2)

/-- `findFunc` resolves the entry callees in the grown program
    (standalone, reused by both the value and memory entry proofs). -/
theorem findFunc_stdVecPushBack :
    findFunc vecGrowProg stdVecPushBackName =
      some stdVecPushBackFunc := by
  unfold vecGrowProg
  rw [findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide)]
  exact findFunc_hit _ _

/-- `findFunc` resolves the entry-scoped index leaf. -/
theorem findFunc_stdVecGrowIndex :
    findFunc vecGrowProg stdVecGrowIndexName =
      some stdVecGrowIndexFunc := by
  unfold vecGrowProg
  rw [findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide)]
  exact findFunc_hit _ _

/-- `findFunc` resolves the default ctor leaf. -/
theorem findFunc_stdVecEmptyCtor :
    findFunc vecGrowProg stdVecCtorName =
      some stdVecEmptyCtorFunc := by
  unfold vecGrowProg
  rw [findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide)]
  exact findFunc_hit _ _

/-- `findFunc` resolves the destructor leaf. -/
theorem findFunc_stdVecDtor :
    findFunc vecGrowProg stdVecDtorName =
      some stdVecDtorFunc := by
  unfold vecGrowProg
  rw [findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide)]
  exact findFunc_hit _ _

set_option maxRecDepth 8192 in
/-- `emit_correct` for `vec_push_sum`: the closed entry over the
    frozen leaves plus the proved composers agrees with the
    compute-to-`6` forward. Fuel covers the three sequential
    `callProg` depths (`6 ≤ F`: the third push needs `2 + 3 ≤ F'`). -/
theorem evalProgFunc_vecPushSumEntry (F : Nat) (hF : 6 ≤ F) :
    evalProgFunc vecGrowProg F vecPushSumEntryFunc [] =
      vecPushSumEntryFwd := by
  obtain ⟨F', rfl, hF'⟩ := fuel_step_down 5 hF
  have hbind : bindArgs vecPushSumEntryFunc.args [] = some [] := rfl
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
  have hT0 : (.stdVecOwned ⟨[], false⟩ 0 0 : Value) =
      .stdVecOwned ⟨[], false⟩ 0 0 := rfl
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
  have hcall0 : evalFuncFuel (F' + 1) stdVecEmptyCtorFunc [] =
      .ok (.stdVecOwned ⟨[], false⟩ 0 0) :=
    evalFuncFuel_stdVecEmptyCtor _
  have hstepV0 := evalProgStmt_callRet_ok vecGrowProg (F' + 1) "v0"
    stdVecCtorName [] ([] : Env) _ stdVecEmptyCtorFunc
    (.stdVecOwned ⟨[], false⟩ 0 0)
    hargs0 findFunc_stdVecEmptyCtor hcall0
  -- Step 2: `c0 = 1`.
  have hlitC0 : evalExpr (.lit (.i32 (BitVec.ofNat 32 1)))
      (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0)) =
      .ok (.i32 (BitVec.ofNat 32 1)) := by
    simp [evalExpr, litVal]
  have hstepC0 : evalProgStmt vecGrowProg (F' + 1)
      (.let_ "c0" (.i 32) (.lit (.i32 (BitVec.ofNat 32 1))))
      (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0)) =
      .ok (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)), .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hlitC0
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
  have hcall1 : evalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned ⟨[], false⟩ 0 0, .i32 (BitVec.ofNat 32 1)] =
      stdVecPushBackFwd ⟨[], false⟩ 0 0 (BitVec.ofNat 32 1) :=
    evalProgFunc_stdVecPushBack F' _ 0 0 _ rfl (by decide)
      (Nat.zero_le _) (by decide) (by decide) (by omega)
  have hcall1' : evalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned ⟨[], false⟩ 0 0, .i32 (BitVec.ofNat 32 1)] =
      .ok (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1) := by
    rw [hcall1, hP1]
  have hstepV1 := evalProgStmt_callProg_ok vecGrowProg F' "v1"
    stdVecPushBackName ["v0", "c0"] _ _ stdVecPushBackFunc
    (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1)
    hargs1 findFunc_stdVecPushBack hcall1'
  -- Step 4: `c1 = 2`.
  have hlitC1 : evalExpr (.lit (.i32 (BitVec.ofNat 32 2)))
      (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1)) =
      .ok (.i32 (BitVec.ofNat 32 2)) := by
    simp [evalExpr, litVal]
  have hstepC1 : evalProgStmt vecGrowProg (F' + 1)
      (.let_ "c1" (.i 32) (.lit (.i32 (BitVec.ofNat 32 2))))
      (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1)) =
      .ok (envExtend (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)), .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hlitC1
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
  have hcall2 : evalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1,
        .i32 (BitVec.ofNat 32 2)] =
      stdVecPushBackFwd ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1
        (BitVec.ofNat 32 2) :=
    evalProgFunc_stdVecPushBack F' _ 1 1 _ rfl (by decide)
      (by decide) (by decide) (by decide) (by omega)
  have hcall2' : evalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1,
        .i32 (BitVec.ofNat 32 2)] =
      .ok (.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2) := by
    rw [hcall2, hP2]
  have hstepV2 := evalProgStmt_callProg_ok vecGrowProg F' "v2"
    stdVecPushBackName ["v1", "c1"] _ _ stdVecPushBackFunc
    (.stdVecOwned
      ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2)
    hargs2 findFunc_stdVecPushBack hcall2'
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
  have hstepC2 : evalProgStmt vecGrowProg (F' + 1)
      (.let_ "c2" (.i 32) (.lit (.i32 (BitVec.ofNat 32 3))))
      (envExtend (envExtend (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2)) =
      .ok (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v1" (.stdVecOwned ⟨[(BitVec.ofNat 32 1)], false⟩ 1 1))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v2" (.stdVecOwned
          ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2))
        "c2" (.i32 (BitVec.ofNat 32 3)), .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hlitC2
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
  have hcall3 : evalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2,
        .i32 (BitVec.ofNat 32 3)] =
      stdVecPushBackFwd
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2
        (BitVec.ofNat 32 3) :=
    evalProgFunc_stdVecPushBack F' _ 2 2 _ rfl (by decide)
      (by decide) (by decide) (by decide) (by omega)
  have hcall3' : evalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2)], false⟩ 2 2,
        .i32 (BitVec.ofNat 32 3)] =
      .ok (.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4) := by
    rw [hcall3, hP3]
  have hstepV3 := evalProgStmt_callProg_ok vecGrowProg F' "v3"
    stdVecPushBackName ["v2", "c2"] _ _ stdVecPushBackFunc
    (.stdVecOwned
      ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
        (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4)
    hargs3 findFunc_stdVecPushBack hcall3'
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
  have hstepN0 : evalProgStmt vecGrowProg (F' + 1)
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
            (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4)) =
      .ok (envExtend (envExtend (envExtend (envExtend (envExtend
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
        "n0" (.u64 (BitVec.ofNat 64 0)), .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hlitN0
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
  have hcallE0 : evalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4,
        .u64 (BitVec.ofNat 64 0)] =
      stdVecGrowIndexFwd
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3
        (BitVec.ofNat 64 0) :=
    evalFuncFuel_stdVecGrowIndex _ _ 3 4 _ rfl _ hget0 hlt0
  have hcallE0' : evalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4,
        .u64 (BitVec.ofNat 64 0)] =
      .ok (.i32 (BitVec.ofNat 32 1)) := by
    rw [hcallE0, hE0]
  have hstepE0 := evalProgStmt_callRet_ok vecGrowProg (F' + 1) "e0"
    stdVecGrowIndexName ["v3", "n0"] _ _ stdVecGrowIndexFunc
    (.i32 (BitVec.ofNat 32 1))
    hargsE0 findFunc_stdVecGrowIndex hcallE0'
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
  have hstepN1 : evalProgStmt vecGrowProg (F' + 1)
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
        "e0" (.i32 (BitVec.ofNat 32 1))) =
      .ok (envExtend (envExtend (envExtend (envExtend (envExtend
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
        "n1" (.u64 (BitVec.ofNat 64 1)), .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hlitN1
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
  have hcallE1 : evalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4,
        .u64 (BitVec.ofNat 64 1)] =
      stdVecGrowIndexFwd
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3
        (BitVec.ofNat 64 1) :=
    evalFuncFuel_stdVecGrowIndex _ _ 3 4 _ rfl _ hget1 hlt1
  have hcallE1' : evalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4,
        .u64 (BitVec.ofNat 64 1)] =
      .ok (.i32 (BitVec.ofNat 32 2)) := by
    rw [hcallE1, hE1]
  have hstepE1 := evalProgStmt_callRet_ok vecGrowProg (F' + 1) "e1"
    stdVecGrowIndexName ["v3", "n1"] _ _ stdVecGrowIndexFunc
    (.i32 (BitVec.ofNat 32 2))
    hargsE1 findFunc_stdVecGrowIndex hcallE1'
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
  have hstepN2 : evalProgStmt vecGrowProg (F' + 1)
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
        "e1" (.i32 (BitVec.ofNat 32 2))) =
      .ok (envExtend (envExtend (envExtend (envExtend (envExtend
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
        "n2" (.u64 (BitVec.ofNat 64 2)), .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hlitN2
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
  have hcallE2 : evalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4,
        .u64 (BitVec.ofNat 64 2)] =
      stdVecGrowIndexFwd
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3
        (BitVec.ofNat 64 2) :=
    evalFuncFuel_stdVecGrowIndex _ _ 3 4 _ rfl _ hget2 hlt2
  have hcallE2' : evalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4,
        .u64 (BitVec.ofNat 64 2)] =
      .ok (.i32 (BitVec.ofNat 32 3)) := by
    rw [hcallE2, hE2]
  have hstepE2 := evalProgStmt_callRet_ok vecGrowProg (F' + 1) "e2"
    stdVecGrowIndexName ["v3", "n2"] _ _ stdVecGrowIndexFunc
    (.i32 (BitVec.ofNat 32 3))
    hargsE2 findFunc_stdVecGrowIndex hcallE2'
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
  have hstepS1 : evalProgStmt vecGrowProg (F' + 1)
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
          "e2" (.i32 (BitVec.ofNat 32 3))) =
      .ok (envExtend (envExtend (envExtend (envExtend (envExtend
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
          "s1" (.i32 (BitVec.ofNat 32 3)), .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hs1E
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
  have hstepS2 : evalProgStmt vecGrowProg (F' + 1)
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
          "s1" (.i32 (BitVec.ofNat 32 3))) =
      .ok (envExtend (envExtend (envExtend (envExtend (envExtend
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
          "s2" (.i32 (BitVec.ofNat 32 6)), .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hs2E
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
  have hcallD : evalFuncFuel (F' + 1) stdVecDtorFunc
      [.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4] =
      stdVecDtorFwd
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4 :=
    evalFuncFuel_stdVecDtor _ _ 3 4 (by decide)
  have hcallD' : evalFuncFuel (F' + 1) stdVecDtorFunc
      [.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], false⟩ 3 4] =
      .ok (.stdVecOwned
        ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
          (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], true⟩ 3 4) := by
    rw [hcallD, hD]
  have hstepV4 := evalProgStmt_callRet_ok vecGrowProg (F' + 1) "v4"
    stdVecDtorName ["v3"] _ _ stdVecDtorFunc
    (.stdVecOwned
      ⟨[(BitVec.ofNat 32 1), (BitVec.ofNat 32 2),
        (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], true⟩ 3 4)
    hargsD findFunc_stdVecDtor hcallD'
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
  have hret : evalProgStmt vecGrowProg (F' + 1)
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
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], true⟩ 3 4)) =
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
              (BitVec.ofNat 32 3), (BitVec.ofNat 32 0)], true⟩ 3 4)),
        .returned (.i32 (BitVec.ofNat 32 6))) :=
    evalProgStmt_return vecGrowProg (F' + 1) _ _ _ hrE
  simp only [evalProgFunc, hbind, hbody]
  rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepV0,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepC0,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepV1,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepC1,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepV2,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepC2,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepV3,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepN0,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepE0,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepN1,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepE1,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepN2,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepE2,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepS1,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepS2,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepV4, hret]
  simp only [vecPushSumEntryFwd, hP1, hP2, hP3, hE0, hE1, hE2, hA1, hA2, hD,
    vecGrow_bind_ok, vecGrowOwned, vecGrowI32]
