/-
Circe.Transfer.GrowRealloc — N4d-iv-b2 `_M_realloc_insert` composer transfer.
Over `Circe.Transfer.GrowReloc`.
-/
import Circe.Transfer.GrowReloc

/-! ## N4d-iv-b2 `_M_realloc_insert` composer: memory agreement -/

/-- `memEval` for `_M_realloc_insert`: program evaluation over the
    frozen b1 leaves agrees with the composer forward (mirrors
    `evalProgFunc_stdVecGrowRealloc`; memory and layout thread through
    unchanged — every call runs on its own entry block — so the only
    memory obligations are the two header loads for `lenOld` /
    `capOld`). -/
theorem memEvalProgFunc_stdVecGrowRealloc (F : Nat) (b : Vec32)
    (len cap : Nat) (pos : BitVec 64) (x : BitVec 32)
    (hlive : b.freed = false)
    (hmax : len ≤ stdVecMaxDiffBV.toNat)
    (hSlen : pos.toNat ≤ len)
    (hlenB : len ≤ b.val.length)
    (h64 : b.val.length < 2 ^ 64)
    (hfuel1 : pos.toNat + 1 ≤ F)
    (hfuel2 : len - pos.toNat + 1 ≤ F) :
    memEvalProgFunc vecGrowProg F stdVecGrowReallocFunc
      [.stdVecOwned b len cap, .u64 pos, .i32 x] =
      stdVecGrowReallocFwd b len cap pos x := by
  have hbind : bindMemArgs stdVecGrowReallocFunc.args
      [.stdVecOwned b len cap, .u64 pos, .i32 x] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)],
        tripleMem b len cap, [("t", 0, 0)]) := rfl
  have hbody : stdVecGrowReallocFunc.body =
      (.seq (.let_ "one" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      (.seq (.let_ "zero" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.seq (.callRet "newlen" stdVecCheckLenName ["t", "one"])
      (.seq (.callRet "bpos" stdVecBeginName ["t"])
      (.seq (.callRet "kd" stdVecMinusName ["pos", "bpos"])
      (.seq (.let_ "k" (.u 64) (.u64ofI64 (.var "kd")))
      (.seq (.let_ "lenOld" (.u 64) (.vgrowLen "t"))
      (.seq (.let_ "capOld" (.u 64) (.vgrowCap "t"))
      (.seq (.callRet "tNew0" stdVecAllocateName ["newlen"])
      (.seq (.callRet "tNew1" stdVecTraitsConstructName
               ["tNew0", "k", "x"])
      (.seq (.callRet "tC1" stdVecRelocName
               ["t", "tNew1", "zero", "k", "zero"])
      (.seq (.let_ "kp1" (.u 64)
               (.uadd (.var "k") (.var "one")))
      (.seq (.callRet "tC2" stdVecRelocName
               ["t", "tC1", "k", "lenOld", "kp1"])
      (.seq (.let_ "lenNew" (.u 64)
               (.uadd (.var "lenOld") (.var "one")))
      (.seq (.callRet "tDead" stdVecDeallocName ["t", "capOld"])
            (.return_ (.vgrowSetLen "tC2" (.var "lenNew")))))))))))))))))) := rfl
  have hM64 : stdVecMaxDiffBV.toNat < 2 ^ 64 := BitVec.isLt _
  have hlen64 : len < 2 ^ 64 := by omega
  have hrt : (BitVec.ofNat 64 len).toNat = len := ofNat64_toNat _ hlen64
  have h1w : (BitVec.ofNat 64 1).toNat = 1 := ofNat64_toNat 1 (by decide)
  have hz : (BitVec.ofNat 64 0).toNat = 0 := ofNat64_toNat 0 (by decide)
  have hkd : pos - BitVec.ofNat 64 0 = pos := BitVec.sub_zero pos
  have hpos64 : pos.toNat < 2 ^ 64 := BitVec.isLt _
  have hlay : layoutLookup [("t", 0, 0)] "t" = some (0, 0) := by
    simp [layoutLookup]
  have hmemLen : memLoad (tripleMem b len cap) 0 0 0 =
      .ok (BitVec.ofNat 32 len) := by
    simp [tripleMem, memLoad, memFind, hlive]
  have hmemCap : memLoad (tripleMem b len cap) 0 0 1 =
      .ok (BitVec.ofNat 32 cap) := by
    simp [tripleMem, memLoad, memFind, hlive]
  have hfindCk : findFunc vecGrowProg stdVecCheckLenName =
      some stdVecCheckLenFunc := findFunc_hit _ _
  have hfindBg : findFunc vecGrowProg stdVecBeginName =
      some stdVecBeginFunc := by
    unfold vecGrowProg
    rw [findFunc_miss _ _ _ (by decide)]
    exact findFunc_hit _ _
  have hfindMi : findFunc vecGrowProg stdVecMinusName =
      some stdVecMinusFunc := by
    unfold vecGrowProg
    rw [findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide)]
    exact findFunc_hit _ _
  have hfindAl : findFunc vecGrowProg stdVecAllocateName =
      some stdVecAllocFunc := by
    unfold vecGrowProg
    rw [findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide)]
    exact findFunc_hit _ _
  have hfindCon : findFunc vecGrowProg stdVecTraitsConstructName =
      some stdVecConstructFunc := by
    unfold vecGrowProg
    rw [findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide)]
    exact findFunc_hit _ _
  have hfindRe : findFunc vecGrowProg stdVecRelocName =
      some stdVecRelocFunc := by
    unfold vecGrowProg
    rw [findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide)]
    exact findFunc_hit _ _
  have hfindGd : findFunc vecGrowProg stdVecDeallocName =
      some stdVecDeallocGuardFunc := by
    unfold vecGrowProg
    rw [findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide)]
    exact findFunc_hit _ _
  have hone : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)] = .ok (.u64 (BitVec.ofNat 64 1)) := rfl
  have hmemOne : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)] (tripleMem b len cap) [("t", 0, 0)] =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    rw [memEvalExpr_lit]
    exact hone
  have hstepOne : memEvalProgStmt vecGrowProg F
      (.let_ "one" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)] (tripleMem b len cap) [("t", 0, 0)] =
      .ok (((envExtend [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)] "one" (.u64 (BitVec.ofNat 64 1)),
        tripleMem b len cap, [("t", 0, 0)]), .fellThrough)) :=
    by simp only [memEvalProgStmt]; exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _ (fun _ => by simp) (fun _ => by simp) (fun _ => by simp) hmemOne hone
  have hzero : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)] "one" (.u64 (BitVec.ofNat 64 1))) =
      .ok (.u64 (BitVec.ofNat 64 0)) := rfl
  have hmemZero : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)] "one" (.u64 (BitVec.ofNat 64 1)))
      (tripleMem b len cap) [("t", 0, 0)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    rw [memEvalExpr_lit]
    exact hzero
  have hstepZero : memEvalProgStmt vecGrowProg F
      (.let_ "zero" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (envExtend [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)] "one" (.u64 (BitVec.ofNat 64 1)))
      (tripleMem b len cap) [("t", 0, 0)] =
      .ok (((envExtend (envExtend [("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] "one"
        (.u64 (BitVec.ofNat 64 1))) "zero" (.u64 (BitVec.ofNat 64 0)),
        tripleMem b len cap, [("t", 0, 0)]), .fellThrough)) :=
    by simp only [memEvalProgStmt]; exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _ (fun _ => by simp) (fun _ => by simp) (fun _ => by simp) hmemZero hzero
  have htCk : envLookup (envExtend (envExtend
      [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
      "one" (.u64 (BitVec.ofNat 64 1))) "zero"
      (.u64 (BitVec.ofNat 64 0))) "t" =
      some (.stdVecOwned b len cap) := by
    simp [envLookup, envExtend,
      show ("t" : String) ≠ "zero" by decide,
      show ("t" : String) ≠ "one" by decide]
  have honeCk : envLookup (envExtend (envExtend
      [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
      "one" (.u64 (BitVec.ofNat 64 1))) "zero"
      (.u64 (BitVec.ofNat 64 0))) "one" =
      some (.u64 (BitVec.ofNat 64 1)) := by
    simp [envLookup, envExtend,
      show ("one" : String) ≠ "zero" by decide]
  have hargsCk : lookupArgs (envExtend (envExtend
      [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
      "one" (.u64 (BitVec.ofNat 64 1))) "zero"
      (.u64 (BitVec.ofNat 64 0))) ["t", "one"] =
      some [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 1)] := by
    simp only [lookupArgs, htCk, honeCk]
  have hcallCk : memEvalFuncFuel F stdVecCheckLenFunc
      [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 1)] =
      stdVecCheckLenFwd len (BitVec.ofNat 64 1) :=
    memEvalFuncFuel_stdVecCheckLen F b len cap (BitVec.ofNat 64 1) hlive
  cases hck : stdVecCheckLenFwd len (BitVec.ofNat 64 1) with
  | error e =>
    have hcallCk' : memEvalFuncFuel F stdVecCheckLenFunc
        [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 1)] =
        .error e := by rw [hcallCk, hck]
    have hstepCk := memEvalProgStmt_callRet_err vecGrowProg F "newlen"
      stdVecCheckLenName ["t", "one"] _ (tripleMem b len cap) [("t", 0, 0)] _ stdVecCheckLenFunc e
      hargsCk hfindCk hcallCk'
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepOne,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepZero,
      memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstepCk]
    simp only [stdVecGrowReallocFwd, hck, vecGrow_bind_err]
  | ok v =>
    obtain ⟨newlen, rfl, hle1⟩ := stdVecCheckLenFwd_ok1 _ _ hmax hck
    have hcallCk' : memEvalFuncFuel F stdVecCheckLenFunc
        [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 1)] =
        .ok (.u64 newlen) := by rw [hcallCk, hck]
    have hstepCk := memEvalProgStmt_callRet_ok vecGrowProg F "newlen"
      stdVecCheckLenName ["t", "one"] _ (tripleMem b len cap) [("t", 0, 0)] _ stdVecCheckLenFunc
      (.u64 newlen) hargsCk hfindCk hcallCk'
    have htBg : envLookup (envExtend (envExtend (envExtend
      [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
      "one" (.u64 (BitVec.ofNat 64 1))) "zero"
      (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "t" =
      some (.stdVecOwned b len cap) := by
      simp [envLookup, envExtend,
        show ("t" : String) ≠ "newlen" by decide,
        show ("t" : String) ≠ "zero" by decide,
        show ("t" : String) ≠ "one" by decide]
    have hargsBg : lookupArgs (envExtend (envExtend (envExtend
      [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
      "one" (.u64 (BitVec.ofNat 64 1))) "zero"
      (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) ["t"] =
      some [.stdVecOwned b len cap] := by
      simp only [lookupArgs, htBg]
    have hcallBg : memEvalFuncFuel F stdVecBeginFunc
        [.stdVecOwned b len cap] = stdVecBeginFwd :=
      memEvalFuncFuel_stdVecBegin F b len cap
    have hbgU : stdVecBeginFwd = .ok (.u64 (BitVec.ofNat 64 0)) := rfl
    cases hbg : stdVecBeginFwd with
    | error e =>
      have hcallBg' : memEvalFuncFuel F stdVecBeginFunc
          [.stdVecOwned b len cap] = .error e := by
        rw [hcallBg, hbg]
      have hstepBg := memEvalProgStmt_callRet_err vecGrowProg F "bpos"
        stdVecBeginName ["t"] _ (tripleMem b len cap) [("t", 0, 0)] _
        stdVecBeginFunc e hargsBg hfindBg hcallBg'
      simp only [memEvalProgFunc, hbind, hbody]
      rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepOne,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepZero,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepCk,
        memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstepBg]
      simp only [stdVecGrowReallocFwd, hck, hbg, vecGrow_bind_ok,
        vecGrow_bind_err, vecGrowU64]
    | ok v =>
      rw [hbgU] at hbg
      cases hbg
      have hcallBg' : memEvalFuncFuel F stdVecBeginFunc
          [.stdVecOwned b len cap] = .ok (.u64 (BitVec.ofNat 64 0)) := by
        rw [hcallBg, hbgU]
      have hstepBg := memEvalProgStmt_callRet_ok vecGrowProg F "bpos"
        stdVecBeginName ["t"] _ (tripleMem b len cap) [("t", 0, 0)] _
        stdVecBeginFunc (.u64 (BitVec.ofNat 64 0)) hargsBg hfindBg hcallBg'
      have hposMi : envLookup (envExtend (envExtend (envExtend (envExtend
        [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
        "one" (.u64 (BitVec.ofNat 64 1))) "zero"
        (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
        (.u64 (BitVec.ofNat 64 0))) "pos" = some (.u64 pos) := by
        simp [envLookup, envExtend,
          show ("pos" : String) ≠ "bpos" by decide,
          show ("pos" : String) ≠ "newlen" by decide,
          show ("pos" : String) ≠ "zero" by decide,
          show ("pos" : String) ≠ "one" by decide]
      have hbposMi : envLookup (envExtend (envExtend (envExtend (envExtend
        [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
        "one" (.u64 (BitVec.ofNat 64 1))) "zero"
        (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
        (.u64 (BitVec.ofNat 64 0))) "bpos" =
        some (.u64 (BitVec.ofNat 64 0)) :=
        envExtend_hit _ _ _
      have hargsMi : lookupArgs (envExtend (envExtend (envExtend (envExtend
        [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
        "one" (.u64 (BitVec.ofNat 64 1))) "zero"
        (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
        (.u64 (BitVec.ofNat 64 0))) ["pos", "bpos"] =
        some [.u64 pos, .u64 (BitVec.ofNat 64 0)] := by
        simp only [lookupArgs, hposMi, hbposMi]
      have hcallMi : memEvalFuncFuel F stdVecMinusFunc
          [.u64 pos, .u64 (BitVec.ofNat 64 0)] =
          stdVecMinusFwd pos (BitVec.ofNat 64 0) :=
        memEvalFuncFuel_stdVecMinus F pos (BitVec.ofNat 64 0)
      have hmiU : stdVecMinusFwd pos (BitVec.ofNat 64 0) =
          .ok (.i64 (pos - BitVec.ofNat 64 0)) := rfl
      cases hmi : stdVecMinusFwd pos (BitVec.ofNat 64 0) with
      | error e =>
        have hcallMi' : memEvalFuncFuel F stdVecMinusFunc
            [.u64 pos, .u64 (BitVec.ofNat 64 0)] = .error e := by
          rw [hcallMi, hmi]
        have hstepMi := memEvalProgStmt_callRet_err vecGrowProg F "kd"
          stdVecMinusName ["pos", "bpos"] _ (tripleMem b len cap)
          [("t", 0, 0)] _ stdVecMinusFunc e hargsMi hfindMi hcallMi'
        simp only [memEvalProgFunc, hbind, hbody]
        rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepOne,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepZero,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepCk,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepBg,
          memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstepMi]
        simp only [stdVecGrowReallocFwd, hck, hbgU, hmi, vecGrow_bind_ok,
          vecGrow_bind_err, vecGrowU64]
      | ok v =>
        rw [hmiU] at hmi
        cases hmi
        have hcallMi' : memEvalFuncFuel F stdVecMinusFunc
            [.u64 pos, .u64 (BitVec.ofNat 64 0)] =
            .ok (.i64 (pos - BitVec.ofNat 64 0)) := by
          rw [hcallMi, hmiU]
        have hstepMi := memEvalProgStmt_callRet_ok vecGrowProg F "kd"
          stdVecMinusName ["pos", "bpos"] _ (tripleMem b len cap)
          [("t", 0, 0)] _ stdVecMinusFunc
          (.i64 (pos - BitVec.ofNat 64 0)) hargsMi hfindMi hcallMi'
        have hkdHit : evalExpr (.var "kd") (envExtend (envExtend (envExtend
          (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
          "one" (.u64 (BitVec.ofNat 64 1))) "zero"
          (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
          (.u64 (BitVec.ofNat 64 0))) "kd"
          (.i64 (pos - BitVec.ofNat 64 0))) =
          .ok (.i64 (pos - BitVec.ofNat 64 0)) :=
          evalExpr_var_hit _ _ _ (envExtend_hit _ _ _)
        have hkEvalBase : evalExpr (.u64ofI64 (.var "kd")) (envExtend
          (envExtend (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
          "one" (.u64 (BitVec.ofNat 64 1))) "zero"
          (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
          (.u64 (BitVec.ofNat 64 0))) "kd"
          (.i64 (pos - BitVec.ofNat 64 0))) =
          .ok (.u64 (pos - BitVec.ofNat 64 0)) :=
          evalExpr_u64ofI64_hit _ _ _ hkdHit
        have hkmem : memEvalExpr (.u64ofI64 (.var "kd")) (envExtend
          (envExtend (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
          "one" (.u64 (BitVec.ofNat 64 1))) "zero"
          (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
          (.u64 (BitVec.ofNat 64 0))) "kd"
          (.i64 (pos - BitVec.ofNat 64 0)))
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok (.u64 (pos - BitVec.ofNat 64 0)) := by
          rw [memEvalExpr_u64ofI64_agree _ _ _ _ (memEvalExpr_var _ _ _ _)]
          exact hkEvalBase
        have hstepK : memEvalProgStmt vecGrowProg F
            (.let_ "k" (.u 64) (.u64ofI64 (.var "kd"))) (envExtend
            (envExtend (envExtend (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
            "one" (.u64 (BitVec.ofNat 64 1))) "zero"
            (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
            (.u64 (BitVec.ofNat 64 0))) "kd"
            (.i64 (pos - BitVec.ofNat 64 0)))
            (tripleMem b len cap) [("t", 0, 0)] =
            .ok (((envExtend (envExtend (envExtend (envExtend (envExtend
            (envExtend
            [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
            "one" (.u64 (BitVec.ofNat 64 1))) "zero"
            (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
            (.u64 (BitVec.ofNat 64 0))) "kd"
            (.i64 (pos - BitVec.ofNat 64 0))) "k"
            (.u64 (pos - BitVec.ofNat 64 0)),
            tripleMem b len cap, [("t", 0, 0)]), .fellThrough)) :=
          by simp only [memEvalProgStmt]; exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _ (fun _ => by simp) (fun _ => by simp) (fun _ => by simp) hkmem hkEvalBase
        have htLen : envLookup (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
          "one" (.u64 (BitVec.ofNat 64 1))) "zero"
          (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
          (.u64 (BitVec.ofNat 64 0))) "kd"
          (.i64 (pos - BitVec.ofNat 64 0))) "k"
          (.u64 (pos - BitVec.ofNat 64 0))) "t" =
          some (.stdVecOwned b len cap) := by
          simp [envLookup, envExtend,
            show ("t" : String) ≠ "k" by decide,
            show ("t" : String) ≠ "kd" by decide,
            show ("t" : String) ≠ "bpos" by decide,
            show ("t" : String) ≠ "newlen" by decide,
            show ("t" : String) ≠ "zero" by decide,
            show ("t" : String) ≠ "one" by decide]
        have hlenOldEval : evalExpr (.vgrowLen "t") (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
          "one" (.u64 (BitVec.ofNat 64 1))) "zero"
          (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
          (.u64 (BitVec.ofNat 64 0))) "kd"
          (.i64 (pos - BitVec.ofNat 64 0))) "k"
          (.u64 (pos - BitVec.ofNat 64 0))) =
          .ok (.u64 (BitVec.ofNat 64 len)) :=
          evalExpr_vgrowLen_some _ _ _ _ _ htLen
        have hlenOldmem : memEvalExpr (.vgrowLen "t") (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
          "one" (.u64 (BitVec.ofNat 64 1))) "zero"
          (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
          (.u64 (BitVec.ofNat 64 0))) "kd"
          (.i64 (pos - BitVec.ofNat 64 0))) "k"
          (.u64 (pos - BitVec.ofNat 64 0)))
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok (.u64 (BitVec.ofNat 64 len)) := by
          rw [memEvalExpr_vgrowLen_hit "t" _ _ _ _ _ _ _ _ hlay htLen hmemLen]
          exact hlenOldEval
        have hstepLenOld : memEvalProgStmt vecGrowProg F
            (.let_ "lenOld" (.u 64) (.vgrowLen "t")) (envExtend (envExtend
            (envExtend (envExtend (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
            "one" (.u64 (BitVec.ofNat 64 1))) "zero"
            (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
            (.u64 (BitVec.ofNat 64 0))) "kd"
            (.i64 (pos - BitVec.ofNat 64 0))) "k"
            (.u64 (pos - BitVec.ofNat 64 0)))
            (tripleMem b len cap) [("t", 0, 0)] =
            .ok (((envExtend (envExtend (envExtend (envExtend (envExtend
            (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
            "one" (.u64 (BitVec.ofNat 64 1))) "zero"
            (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
            (.u64 (BitVec.ofNat 64 0))) "kd"
            (.i64 (pos - BitVec.ofNat 64 0))) "k"
            (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
            (.u64 (BitVec.ofNat 64 len)),
            tripleMem b len cap, [("t", 0, 0)]), .fellThrough)) :=
          by simp only [memEvalProgStmt]; exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _ (fun _ => by simp) (fun _ => by simp) (fun _ => by simp) hlenOldmem hlenOldEval
        have htCap : envLookup (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
          "one" (.u64 (BitVec.ofNat 64 1))) "zero"
          (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
          (.u64 (BitVec.ofNat 64 0))) "kd"
          (.i64 (pos - BitVec.ofNat 64 0))) "k"
          (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
          (.u64 (BitVec.ofNat 64 len))) "t" =
          some (.stdVecOwned b len cap) := by
          simp [envLookup, envExtend,
            show ("t" : String) ≠ "lenOld" by decide,
            show ("t" : String) ≠ "k" by decide,
            show ("t" : String) ≠ "kd" by decide,
            show ("t" : String) ≠ "bpos" by decide,
            show ("t" : String) ≠ "newlen" by decide,
            show ("t" : String) ≠ "zero" by decide,
            show ("t" : String) ≠ "one" by decide]
        have hcapOldEval : evalExpr (.vgrowCap "t") (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
          "one" (.u64 (BitVec.ofNat 64 1))) "zero"
          (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
          (.u64 (BitVec.ofNat 64 0))) "kd"
          (.i64 (pos - BitVec.ofNat 64 0))) "k"
          (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
          (.u64 (BitVec.ofNat 64 len))) =
          .ok (.u64 (BitVec.ofNat 64 cap)) :=
          evalExpr_vgrowCap_some _ _ _ _ _ htCap
        have hcapOldmem : memEvalExpr (.vgrowCap "t") (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
          "one" (.u64 (BitVec.ofNat 64 1))) "zero"
          (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
          (.u64 (BitVec.ofNat 64 0))) "kd"
          (.i64 (pos - BitVec.ofNat 64 0))) "k"
          (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
          (.u64 (BitVec.ofNat 64 len)))
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok (.u64 (BitVec.ofNat 64 cap)) := by
          rw [memEvalExpr_vgrowCap_hit "t" _ _ _ _ _ _ _ _ hlay htCap hmemCap]
          exact hcapOldEval
        have hstepCapOld : memEvalProgStmt vecGrowProg F
            (.let_ "capOld" (.u 64) (.vgrowCap "t")) (envExtend (envExtend
            (envExtend (envExtend (envExtend (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
            "one" (.u64 (BitVec.ofNat 64 1))) "zero"
            (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
            (.u64 (BitVec.ofNat 64 0))) "kd"
            (.i64 (pos - BitVec.ofNat 64 0))) "k"
            (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
            (.u64 (BitVec.ofNat 64 len)))
            (tripleMem b len cap) [("t", 0, 0)] =
            .ok (((envExtend (envExtend (envExtend (envExtend (envExtend
            (envExtend (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
            "one" (.u64 (BitVec.ofNat 64 1))) "zero"
            (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
            (.u64 (BitVec.ofNat 64 0))) "kd"
            (.i64 (pos - BitVec.ofNat 64 0))) "k"
            (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
            (.u64 (BitVec.ofNat 64 len))) "capOld"
            (.u64 (BitVec.ofNat 64 cap)),
            tripleMem b len cap, [("t", 0, 0)]), .fellThrough)) :=
          by simp only [memEvalProgStmt]; exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _ (fun _ => by simp) (fun _ => by simp) (fun _ => by simp) hcapOldmem hcapOldEval
        have hnewlenAl : envLookup (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
          "one" (.u64 (BitVec.ofNat 64 1))) "zero"
          (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
          (.u64 (BitVec.ofNat 64 0))) "kd"
          (.i64 (pos - BitVec.ofNat 64 0))) "k"
          (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
          (.u64 (BitVec.ofNat 64 len))) "capOld"
          (.u64 (BitVec.ofNat 64 cap))) "newlen" =
          some (.u64 newlen) := by
          simp [envLookup, envExtend,
            show ("newlen" : String) ≠ "capOld" by decide,
            show ("newlen" : String) ≠ "lenOld" by decide,
            show ("newlen" : String) ≠ "k" by decide,
            show ("newlen" : String) ≠ "kd" by decide,
            show ("newlen" : String) ≠ "bpos" by decide]
        have hargsAl : lookupArgs (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
          "one" (.u64 (BitVec.ofNat 64 1))) "zero"
          (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
          (.u64 (BitVec.ofNat 64 0))) "kd"
          (.i64 (pos - BitVec.ofNat 64 0))) "k"
          (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
          (.u64 (BitVec.ofNat 64 len))) "capOld"
          (.u64 (BitVec.ofNat 64 cap))) ["newlen"] =
          some [.u64 newlen] := by
          simp only [lookupArgs, hnewlenAl]
        have hcallAl : memEvalFuncFuel F stdVecAllocFunc [.u64 newlen] =
            stdVecAllocFwd newlen :=
          memEvalFuncFuel_stdVecAlloc F newlen
        have hnpos : 0 < newlen.toNat := by omega
        have hnewpos : (BitVec.ofNat 64 0).ult newlen = true := by
          simp only [BitVec.ult_eq_decide, hz, hnpos]
          rfl
        cases hal : stdVecAllocFwd newlen with
        | error e =>
          have hcallAl' : memEvalFuncFuel F stdVecAllocFunc [.u64 newlen] =
              .error e := by rw [hcallAl, hal]
          have hstepAl := memEvalProgStmt_callRet_err vecGrowProg F "tNew0"
            stdVecAllocateName ["newlen"] _ (tripleMem b len cap)
            [("t", 0, 0)] _ stdVecAllocFunc e hargsAl hfindAl hcallAl'
          simp only [memEvalProgFunc, hbind, hbody]
          rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepOne,
            memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepZero,
            memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepCk,
            memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepBg,
            memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepMi,
            memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepK,
            memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepLenOld,
            memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepCapOld,
            memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstepAl]
          simp only [stdVecGrowReallocFwd, hck, hbgU, hmiU, hal,
            vecGrow_bind_ok, vecGrow_bind_err, vecGrowU64, vecGrowI64]
        | ok v =>
          obtain ⟨bNew, rfl, hNlive, hNlen⟩ :=
            stdVecAllocFwd_ok _ _ hnewpos hal
          have hcallAl' : memEvalFuncFuel F stdVecAllocFunc [.u64 newlen] =
              .ok (.stdVecOwned bNew 0 newlen.toNat) := by
            rw [hcallAl, hal]
          have hstepAl := memEvalProgStmt_callRet_ok vecGrowProg F "tNew0"
            stdVecAllocateName ["newlen"] _ (tripleMem b len cap)
            [("t", 0, 0)] _ stdVecAllocFunc
            (.stdVecOwned bNew 0 newlen.toNat) hargsAl hfindAl hcallAl'
          have htNew0Con : envLookup (envExtend (envExtend (envExtend
            (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
            "one" (.u64 (BitVec.ofNat 64 1))) "zero"
            (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
            (.u64 (BitVec.ofNat 64 0))) "kd"
            (.i64 (pos - BitVec.ofNat 64 0))) "k"
            (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
            (.u64 (BitVec.ofNat 64 len))) "capOld"
            (.u64 (BitVec.ofNat 64 cap))) "tNew0"
            (.stdVecOwned bNew 0 newlen.toNat)) "tNew0" =
            some (.stdVecOwned bNew 0 newlen.toNat) :=
            envExtend_hit _ _ _
          have hkCon : envLookup (envExtend (envExtend (envExtend
            (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
            "one" (.u64 (BitVec.ofNat 64 1))) "zero"
            (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
            (.u64 (BitVec.ofNat 64 0))) "kd"
            (.i64 (pos - BitVec.ofNat 64 0))) "k"
            (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
            (.u64 (BitVec.ofNat 64 len))) "capOld"
            (.u64 (BitVec.ofNat 64 cap))) "tNew0"
            (.stdVecOwned bNew 0 newlen.toNat)) "k" =
            some (.u64 (pos - BitVec.ofNat 64 0)) := by
            simp [envLookup, envExtend,
              show ("k" : String) ≠ "tNew0" by decide,
              show ("k" : String) ≠ "capOld" by decide,
              show ("k" : String) ≠ "lenOld" by decide]
          have hxCon : envLookup (envExtend (envExtend (envExtend
            (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
            "one" (.u64 (BitVec.ofNat 64 1))) "zero"
            (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
            (.u64 (BitVec.ofNat 64 0))) "kd"
            (.i64 (pos - BitVec.ofNat 64 0))) "k"
            (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
            (.u64 (BitVec.ofNat 64 len))) "capOld"
            (.u64 (BitVec.ofNat 64 cap))) "tNew0"
            (.stdVecOwned bNew 0 newlen.toNat)) "x" =
            some (.i32 x) := by
            simp [envLookup, envExtend,
              show ("x" : String) ≠ "tNew0" by decide,
              show ("x" : String) ≠ "capOld" by decide,
              show ("x" : String) ≠ "lenOld" by decide,
              show ("x" : String) ≠ "k" by decide,
              show ("x" : String) ≠ "kd" by decide,
              show ("x" : String) ≠ "bpos" by decide,
              show ("x" : String) ≠ "newlen" by decide,
              show ("x" : String) ≠ "zero" by decide,
              show ("x" : String) ≠ "one" by decide,
              show ("x" : String) ≠ "t" by decide,
              show ("x" : String) ≠ "pos" by decide]
          have hargsCon : lookupArgs (envExtend (envExtend (envExtend
            (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
            "one" (.u64 (BitVec.ofNat 64 1))) "zero"
            (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
            (.u64 (BitVec.ofNat 64 0))) "kd"
            (.i64 (pos - BitVec.ofNat 64 0))) "k"
            (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
            (.u64 (BitVec.ofNat 64 len))) "capOld"
            (.u64 (BitVec.ofNat 64 cap))) "tNew0"
            (.stdVecOwned bNew 0 newlen.toNat))
            ["tNew0", "k", "x"] =
            some [.stdVecOwned bNew 0 newlen.toNat,
              .u64 (pos - BitVec.ofNat 64 0), .i32 x] := by
            simp only [lookupArgs, htNew0Con, hkCon, hxCon]
          have hcallCon : memEvalFuncFuel F stdVecConstructFunc
              [.stdVecOwned bNew 0 newlen.toNat,
                .u64 (pos - BitVec.ofNat 64 0), .i32 x] =
              stdVecConstructFwd bNew 0 newlen.toNat
                (pos - BitVec.ofNat 64 0) x :=
            memEvalFuncFuel_stdVecConstruct F bNew 0 newlen.toNat
              (pos - BitVec.ofNat 64 0) x
          cases hcon : stdVecConstructFwd bNew 0 newlen.toNat
              (pos - BitVec.ofNat 64 0) x with
          | error e =>
            have hcallCon' : memEvalFuncFuel F stdVecConstructFunc
                [.stdVecOwned bNew 0 newlen.toNat,
                  .u64 (pos - BitVec.ofNat 64 0), .i32 x] =
                .error e := by rw [hcallCon, hcon]
            have hstepCon := memEvalProgStmt_callRet_err vecGrowProg F "tNew1"
              stdVecTraitsConstructName ["tNew0", "k", "x"] _
              (tripleMem b len cap) [("t", 0, 0)] _ stdVecConstructFunc e
              hargsCon hfindCon hcallCon'
            simp only [memEvalProgFunc, hbind, hbody]
            rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepOne,
              memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepZero,
              memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepCk,
              memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepBg,
              memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepMi,
              memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepK,
              memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepLenOld,
              memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepCapOld,
              memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepAl,
              memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstepCon]
            simp only [stdVecGrowReallocFwd, hck, hbgU, hmiU, hal, hcon,
              vecGrow_bind_ok, vecGrow_bind_err, vecGrowU64, vecGrowI64,
              vecGrowOwned]
          | ok v =>
            obtain ⟨bC, rfl, hClive, hClen⟩ :=
              stdVecConstructFwd_ok _ _ _ _ _ _ hcon
            have hcallCon' : memEvalFuncFuel F stdVecConstructFunc
                [.stdVecOwned bNew 0 newlen.toNat,
                  .u64 (pos - BitVec.ofNat 64 0), .i32 x] =
                .ok (.stdVecOwned bC 0 newlen.toNat) := by
              rw [hcallCon, hcon]
            have hstepCon := memEvalProgStmt_callRet_ok vecGrowProg F "tNew1"
              stdVecTraitsConstructName ["tNew0", "k", "x"] _
              (tripleMem b len cap) [("t", 0, 0)] _ stdVecConstructFunc
              (.stdVecOwned bC 0 newlen.toNat) hargsCon hfindCon hcallCon'
            have hkdT : (pos - BitVec.ofNat 64 0).toNat = pos.toNat := by
              rw [hkd]
            have htR1 : envLookup (envExtend (envExtend (envExtend
              (envExtend (envExtend (envExtend (envExtend (envExtend
              (envExtend (envExtend
              [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
              "one" (.u64 (BitVec.ofNat 64 1))) "zero"
              (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
              (.u64 (BitVec.ofNat 64 0))) "kd"
              (.i64 (pos - BitVec.ofNat 64 0))) "k"
              (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
              (.u64 (BitVec.ofNat 64 len))) "capOld"
              (.u64 (BitVec.ofNat 64 cap))) "tNew0"
              (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
              (.stdVecOwned bC 0 newlen.toNat)) "t" =
              some (.stdVecOwned b len cap) := by
              simp [envLookup, envExtend,
                show ("t" : String) ≠ "tNew1" by decide,
                show ("t" : String) ≠ "tNew0" by decide,
                show ("t" : String) ≠ "capOld" by decide,
                show ("t" : String) ≠ "lenOld" by decide,
                show ("t" : String) ≠ "k" by decide,
                show ("t" : String) ≠ "kd" by decide,
                show ("t" : String) ≠ "bpos" by decide,
                show ("t" : String) ≠ "newlen" by decide,
                show ("t" : String) ≠ "zero" by decide,
                show ("t" : String) ≠ "one" by decide]
            have htNew1R1 : envLookup (envExtend (envExtend (envExtend
              (envExtend (envExtend (envExtend (envExtend (envExtend
              (envExtend (envExtend
              [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
              "one" (.u64 (BitVec.ofNat 64 1))) "zero"
              (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
              (.u64 (BitVec.ofNat 64 0))) "kd"
              (.i64 (pos - BitVec.ofNat 64 0))) "k"
              (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
              (.u64 (BitVec.ofNat 64 len))) "capOld"
              (.u64 (BitVec.ofNat 64 cap))) "tNew0"
              (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
              (.stdVecOwned bC 0 newlen.toNat)) "tNew1" =
              some (.stdVecOwned bC 0 newlen.toNat) :=
              envExtend_hit _ _ _
            have hzeroR1 : envLookup (envExtend (envExtend (envExtend
              (envExtend (envExtend (envExtend (envExtend (envExtend
              (envExtend (envExtend
              [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
              "one" (.u64 (BitVec.ofNat 64 1))) "zero"
              (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
              (.u64 (BitVec.ofNat 64 0))) "kd"
              (.i64 (pos - BitVec.ofNat 64 0))) "k"
              (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
              (.u64 (BitVec.ofNat 64 len))) "capOld"
              (.u64 (BitVec.ofNat 64 cap))) "tNew0"
              (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
              (.stdVecOwned bC 0 newlen.toNat)) "zero" =
              some (.u64 (BitVec.ofNat 64 0)) := by
              simp [envLookup, envExtend,
                show ("zero" : String) ≠ "tNew1" by decide,
                show ("zero" : String) ≠ "tNew0" by decide,
                show ("zero" : String) ≠ "capOld" by decide,
                show ("zero" : String) ≠ "lenOld" by decide,
                show ("zero" : String) ≠ "k" by decide,
                show ("zero" : String) ≠ "kd" by decide,
                show ("zero" : String) ≠ "bpos" by decide,
                show ("zero" : String) ≠ "newlen" by decide]
            have hkR1 : envLookup (envExtend (envExtend (envExtend
              (envExtend (envExtend (envExtend (envExtend (envExtend
              (envExtend (envExtend
              [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
              "one" (.u64 (BitVec.ofNat 64 1))) "zero"
              (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
              (.u64 (BitVec.ofNat 64 0))) "kd"
              (.i64 (pos - BitVec.ofNat 64 0))) "k"
              (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
              (.u64 (BitVec.ofNat 64 len))) "capOld"
              (.u64 (BitVec.ofNat 64 cap))) "tNew0"
              (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
              (.stdVecOwned bC 0 newlen.toNat)) "k" =
              some (.u64 (pos - BitVec.ofNat 64 0)) := by
              simp [envLookup, envExtend,
                show ("k" : String) ≠ "tNew1" by decide,
                show ("k" : String) ≠ "tNew0" by decide,
                show ("k" : String) ≠ "capOld" by decide,
                show ("k" : String) ≠ "lenOld" by decide]
            have hargsR1 : lookupArgs (envExtend (envExtend (envExtend
              (envExtend (envExtend (envExtend (envExtend (envExtend
              (envExtend (envExtend
              [("t", .stdVecOwned b len cap), ("pos", .u64 pos), ("x", .i32 x)]
              "one" (.u64 (BitVec.ofNat 64 1))) "zero"
              (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
              (.u64 (BitVec.ofNat 64 0))) "kd"
              (.i64 (pos - BitVec.ofNat 64 0))) "k"
              (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
              (.u64 (BitVec.ofNat 64 len))) "capOld"
              (.u64 (BitVec.ofNat 64 cap))) "tNew0"
              (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
              (.stdVecOwned bC 0 newlen.toNat))
              ["t", "tNew1", "zero", "k", "zero"] =
              some [.stdVecOwned b len cap,
                .stdVecOwned bC 0 newlen.toNat,
                .u64 (BitVec.ofNat 64 0),
                .u64 (pos - BitVec.ofNat 64 0),
                .u64 (BitVec.ofNat 64 0)] := by
              simp only [lookupArgs, htR1, htNew1R1, hzeroR1, hkR1]
            have hcallR1 : memEvalFuncFuel F stdVecRelocFunc
                [.stdVecOwned b len cap,
                  .stdVecOwned bC 0 newlen.toNat,
                  .u64 (BitVec.ofNat 64 0),
                  .u64 (pos - BitVec.ofNat 64 0),
                  .u64 (BitVec.ofNat 64 0)] =
                stdVecRelocFwd b len cap bC 0 newlen.toNat
                  (BitVec.ofNat 64 0) (pos - BitVec.ofNat 64 0)
                  (BitVec.ofNat 64 0) :=
              memEvalFuncFuel_stdVecReloc F b len cap bC 0 newlen.toNat
                (BitVec.ofNat 64 0) (pos - BitVec.ofNat 64 0)
                (BitVec.ofNat 64 0) (by rw [hz, hkdT]; omega) hlive hClive
                (by rw [hkdT]; omega) (by rw [hz, hkdT, hClen, hNlen]; omega)
                (by rw [hkdT]; exact hSlen) h64
                (by rw [hClen, hNlen]; exact BitVec.isLt _)
                (by rw [hz, hkdT]; omega)
            cases hr1 : stdVecRelocFwd b len cap bC 0 newlen.toNat
                (BitVec.ofNat 64 0) (pos - BitVec.ofNat 64 0)
                (BitVec.ofNat 64 0) with
            | error e =>
              have hcallR1' : memEvalFuncFuel F stdVecRelocFunc
                  [.stdVecOwned b len cap,
                    .stdVecOwned bC 0 newlen.toNat,
                    .u64 (BitVec.ofNat 64 0),
                    .u64 (pos - BitVec.ofNat 64 0),
                    .u64 (BitVec.ofNat 64 0)] = .error e := by
                rw [hcallR1, hr1]
              have hstepR1 := memEvalProgStmt_callRet_err vecGrowProg F "tC1"
                stdVecRelocName ["t", "tNew1", "zero", "k", "zero"] _
                (tripleMem b len cap) [("t", 0, 0)] _ stdVecRelocFunc e
                hargsR1 hfindRe hcallR1'
              simp only [memEvalProgFunc, hbind, hbody]
              rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepOne,
                memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepZero,
                memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepCk,
                memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepBg,
                memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepMi,
                memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepK,
                memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepLenOld,
                memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepCapOld,
                memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepAl,
                memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepCon,
                memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstepR1]
              simp only [stdVecGrowReallocFwd, hck, hbgU, hmiU, hal,
                hcon, hr1, vecGrow_bind_ok, vecGrow_bind_err, vecGrowU64,
                vecGrowI64, vecGrowOwned]
            | ok v =>
              obtain ⟨bR1, rfl, hR1live, hR1len⟩ :=
                stdVecRelocFwd_ok _ _ _ _ _ _ _ _ _ _ hClive hr1
              have hcallR1' : memEvalFuncFuel F stdVecRelocFunc
                  [.stdVecOwned b len cap,
                    .stdVecOwned bC 0 newlen.toNat,
                    .u64 (BitVec.ofNat 64 0),
                    .u64 (pos - BitVec.ofNat 64 0),
                    .u64 (BitVec.ofNat 64 0)] =
                  .ok (.stdVecOwned bR1 0 newlen.toNat) := by
                rw [hcallR1, hr1]
              have hstepR1 := memEvalProgStmt_callRet_ok vecGrowProg F "tC1"
                stdVecRelocName ["t", "tNew1", "zero", "k", "zero"] _
                (tripleMem b len cap) [("t", 0, 0)] _ stdVecRelocFunc
                (.stdVecOwned bR1 0 newlen.toNat)
                hargsR1 hfindRe hcallR1'
              have hkKp1 : envLookup (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend
                [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                  ("x", .i32 x)]
                "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
                (.u64 (BitVec.ofNat 64 0))) "kd"
                (.i64 (pos - BitVec.ofNat 64 0))) "k"
                (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                (.u64 (BitVec.ofNat 64 len))) "capOld"
                (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                (.stdVecOwned bR1 0 newlen.toNat)) "k" =
                some (.u64 (pos - BitVec.ofNat 64 0)) := by
                simp [envLookup, envExtend,
                  show ("k" : String) ≠ "tC1" by decide,
                  show ("k" : String) ≠ "tNew1" by decide,
                  show ("k" : String) ≠ "tNew0" by decide,
                  show ("k" : String) ≠ "capOld" by decide,
                  show ("k" : String) ≠ "lenOld" by decide]
              have honeKp1 : envLookup (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend
                [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                  ("x", .i32 x)]
                "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
                (.u64 (BitVec.ofNat 64 0))) "kd"
                (.i64 (pos - BitVec.ofNat 64 0))) "k"
                (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                (.u64 (BitVec.ofNat 64 len))) "capOld"
                (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                (.stdVecOwned bR1 0 newlen.toNat)) "one" =
                some (.u64 (BitVec.ofNat 64 1)) := by
                simp [envLookup, envExtend,
                  show ("one" : String) ≠ "tC1" by decide,
                  show ("one" : String) ≠ "tNew1" by decide,
                  show ("one" : String) ≠ "tNew0" by decide,
                  show ("one" : String) ≠ "capOld" by decide,
                  show ("one" : String) ≠ "lenOld" by decide,
                  show ("one" : String) ≠ "k" by decide,
                  show ("one" : String) ≠ "kd" by decide,
                  show ("one" : String) ≠ "bpos" by decide,
                  show ("one" : String) ≠ "newlen" by decide,
                  show ("one" : String) ≠ "zero" by decide]
              have hkp1Eval : evalExpr (.uadd (.var "k") (.var "one"))
                (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend
                [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                  ("x", .i32 x)]
                "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
                (.u64 (BitVec.ofNat 64 0))) "kd"
                (.i64 (pos - BitVec.ofNat 64 0))) "k"
                (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                (.u64 (BitVec.ofNat 64 len))) "capOld"
                (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                (.stdVecOwned bR1 0 newlen.toNat)) =
                .ok (.u64 ((pos - BitVec.ofNat 64 0) +
                  BitVec.ofNat 64 1)) :=
                evalExpr_uadd_u64 _ _ _ _ _
                  (evalExpr_var_hit _ _ _ hkKp1)
                  (evalExpr_var_hit _ _ _ honeKp1)
              have hkp1mem : memEvalExpr (.uadd (.var "k") (.var "one"))
                (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend
                [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                  ("x", .i32 x)]
                "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
                (.u64 (BitVec.ofNat 64 0))) "kd"
                (.i64 (pos - BitVec.ofNat 64 0))) "k"
                (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                (.u64 (BitVec.ofNat 64 len))) "capOld"
                (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                (.stdVecOwned bR1 0 newlen.toNat))
                (tripleMem b len cap) [("t", 0, 0)] =
                .ok (.u64 ((pos - BitVec.ofNat 64 0) +
                  BitVec.ofNat 64 1)) := by
                rw [memEvalExpr_uadd_agree _ _ _ _ _
                  (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _)]
                exact hkp1Eval
              have hstepKp1 : memEvalProgStmt vecGrowProg F
                  (.let_ "kp1" (.u 64)
                    (.uadd (.var "k") (.var "one"))) (envExtend (envExtend
                  (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend
                  [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                    ("x", .i32 x)]
                  "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                  (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
                  (.u64 (BitVec.ofNat 64 0))) "kd"
                  (.i64 (pos - BitVec.ofNat 64 0))) "k"
                  (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                  (.u64 (BitVec.ofNat 64 len))) "capOld"
                  (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                  (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                  (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                  (.stdVecOwned bR1 0 newlen.toNat))
                  (tripleMem b len cap) [("t", 0, 0)] =
                  .ok (((envExtend (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend
                  [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                    ("x", .i32 x)]
                  "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                  (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
                  (.u64 (BitVec.ofNat 64 0))) "kd"
                  (.i64 (pos - BitVec.ofNat 64 0))) "k"
                  (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                  (.u64 (BitVec.ofNat 64 len))) "capOld"
                  (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                  (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                  (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                  (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                  (.u64 ((pos - BitVec.ofNat 64 0) +
                    BitVec.ofNat 64 1)),
                  tripleMem b len cap, [("t", 0, 0)]), .fellThrough)) :=
                by simp only [memEvalProgStmt]; exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _ (fun _ => by simp) (fun _ => by simp) (fun _ => by simp) hkp1mem hkp1Eval
              have hpos1lt : pos.toNat + 1 < 2 ^ 64 := by omega
              have hkp1rt : (pos - BitVec.ofNat 64 0 +
                  BitVec.ofNat 64 1).toNat = pos.toNat + 1 := by
                rw [BitVec.toNat_add_of_lt (by rw [hkdT, h1w]; omega),
                  hkdT, h1w]
              have htR2 : envLookup (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend
                [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                  ("x", .i32 x)]
                "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
                (.u64 (BitVec.ofNat 64 0))) "kd"
                (.i64 (pos - BitVec.ofNat 64 0))) "k"
                (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                (.u64 (BitVec.ofNat 64 len))) "capOld"
                (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                (.u64 ((pos - BitVec.ofNat 64 0) +
                  BitVec.ofNat 64 1))) "t" =
                some (.stdVecOwned b len cap) := by
                simp [envLookup, envExtend,
                  show ("t" : String) ≠ "kp1" by decide,
                  show ("t" : String) ≠ "tC1" by decide,
                  show ("t" : String) ≠ "tNew1" by decide,
                  show ("t" : String) ≠ "tNew0" by decide,
                  show ("t" : String) ≠ "capOld" by decide,
                  show ("t" : String) ≠ "lenOld" by decide,
                  show ("t" : String) ≠ "k" by decide,
                  show ("t" : String) ≠ "kd" by decide,
                  show ("t" : String) ≠ "bpos" by decide,
                  show ("t" : String) ≠ "newlen" by decide,
                  show ("t" : String) ≠ "zero" by decide,
                  show ("t" : String) ≠ "one" by decide]
              have htC1R2 : envLookup (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend
                [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                  ("x", .i32 x)]
                "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
                (.u64 (BitVec.ofNat 64 0))) "kd"
                (.i64 (pos - BitVec.ofNat 64 0))) "k"
                (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                (.u64 (BitVec.ofNat 64 len))) "capOld"
                (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                (.u64 ((pos - BitVec.ofNat 64 0) +
                  BitVec.ofNat 64 1))) "tC1" =
                some (.stdVecOwned bR1 0 newlen.toNat) := by
                simp [envLookup, envExtend,
                  show ("tC1" : String) ≠ "kp1" by decide]
              have hkR2 : envLookup (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend
                [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                  ("x", .i32 x)]
                "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
                (.u64 (BitVec.ofNat 64 0))) "kd"
                (.i64 (pos - BitVec.ofNat 64 0))) "k"
                (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                (.u64 (BitVec.ofNat 64 len))) "capOld"
                (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                (.u64 ((pos - BitVec.ofNat 64 0) +
                  BitVec.ofNat 64 1))) "k" =
                some (.u64 (pos - BitVec.ofNat 64 0)) := by
                simp [envLookup, envExtend,
                  show ("k" : String) ≠ "kp1" by decide,
                  show ("k" : String) ≠ "tC1" by decide,
                  show ("k" : String) ≠ "tNew1" by decide,
                  show ("k" : String) ≠ "tNew0" by decide,
                  show ("k" : String) ≠ "capOld" by decide,
                  show ("k" : String) ≠ "lenOld" by decide]
              have hlenOldR2 : envLookup (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend
                [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                  ("x", .i32 x)]
                "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
                (.u64 (BitVec.ofNat 64 0))) "kd"
                (.i64 (pos - BitVec.ofNat 64 0))) "k"
                (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                (.u64 (BitVec.ofNat 64 len))) "capOld"
                (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                (.u64 ((pos - BitVec.ofNat 64 0) +
                  BitVec.ofNat 64 1))) "lenOld" =
                some (.u64 (BitVec.ofNat 64 len)) := by
                simp [envLookup, envExtend,
                  show ("lenOld" : String) ≠ "kp1" by decide,
                  show ("lenOld" : String) ≠ "tC1" by decide,
                  show ("lenOld" : String) ≠ "tNew1" by decide,
                  show ("lenOld" : String) ≠ "tNew0" by decide,
                  show ("lenOld" : String) ≠ "capOld" by decide]
              have hkp1R2 : envLookup (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend
                [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                  ("x", .i32 x)]
                "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
                (.u64 (BitVec.ofNat 64 0))) "kd"
                (.i64 (pos - BitVec.ofNat 64 0))) "k"
                (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                (.u64 (BitVec.ofNat 64 len))) "capOld"
                (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                (.u64 ((pos - BitVec.ofNat 64 0) +
                  BitVec.ofNat 64 1))) "kp1" =
                some (.u64 ((pos - BitVec.ofNat 64 0) +
                  BitVec.ofNat 64 1)) :=
                envExtend_hit _ _ _
              have hargsR2 : lookupArgs (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend (envExtend
                (envExtend (envExtend (envExtend (envExtend
                [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                  ("x", .i32 x)]
                "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen)) "bpos"
                (.u64 (BitVec.ofNat 64 0))) "kd"
                (.i64 (pos - BitVec.ofNat 64 0))) "k"
                (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                (.u64 (BitVec.ofNat 64 len))) "capOld"
                (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                (.u64 ((pos - BitVec.ofNat 64 0) +
                  BitVec.ofNat 64 1)))
                ["t", "tC1", "k", "lenOld", "kp1"] =
                some [.stdVecOwned b len cap,
                  .stdVecOwned bR1 0 newlen.toNat,
                  .u64 (pos - BitVec.ofNat 64 0),
                  .u64 (BitVec.ofNat 64 len),
                  .u64 ((pos - BitVec.ofNat 64 0) +
                    BitVec.ofNat 64 1)] := by
                simp only [lookupArgs, htR2, htC1R2, hkR2, hlenOldR2,
                  hkp1R2]
              have hcallR2 : memEvalFuncFuel F stdVecRelocFunc
                  [.stdVecOwned b len cap,
                    .stdVecOwned bR1 0 newlen.toNat,
                    .u64 (pos - BitVec.ofNat 64 0),
                    .u64 (BitVec.ofNat 64 len),
                    .u64 ((pos - BitVec.ofNat 64 0) +
                      BitVec.ofNat 64 1)] =
                  stdVecRelocFwd b len cap bR1 0 newlen.toNat
                    (pos - BitVec.ofNat 64 0) (BitVec.ofNat 64 len)
                    ((pos - BitVec.ofNat 64 0) +
                      BitVec.ofNat 64 1) :=
                memEvalFuncFuel_stdVecReloc F b len cap bR1 0 newlen.toNat
                  (pos - BitVec.ofNat 64 0) (BitVec.ofNat 64 len)
                  ((pos - BitVec.ofNat 64 0) + BitVec.ofNat 64 1)
                  (by rw [hkdT, hrt]; exact hSlen) hlive hR1live
                  (by rw [hrt]; exact hlenB)
                  (by rw [hkp1rt, hrt, hkdT, hR1len, hClen, hNlen]; omega)
                  (by simp [hrt]) h64
                  (by rw [hR1len, hClen, hNlen]; exact BitVec.isLt _)
                  (by rw [hrt, hkdT]; exact hfuel2)
              cases hr2 : stdVecRelocFwd b len cap bR1 0 newlen.toNat
                  (pos - BitVec.ofNat 64 0) (BitVec.ofNat 64 len)
                  ((pos - BitVec.ofNat 64 0) + BitVec.ofNat 64 1) with
              | error e =>
                have hcallR2' : memEvalFuncFuel F stdVecRelocFunc
                    [.stdVecOwned b len cap,
                      .stdVecOwned bR1 0 newlen.toNat,
                      .u64 (pos - BitVec.ofNat 64 0),
                      .u64 (BitVec.ofNat 64 len),
                      .u64 ((pos - BitVec.ofNat 64 0) +
                        BitVec.ofNat 64 1)] = .error e := by
                  rw [hcallR2, hr2]
                have hstepR2 := memEvalProgStmt_callRet_err vecGrowProg F "tC2"
                  stdVecRelocName ["t", "tC1", "k", "lenOld", "kp1"] _
                  (tripleMem b len cap) [("t", 0, 0)] _ stdVecRelocFunc e
                  hargsR2 hfindRe hcallR2'
                simp only [memEvalProgFunc, hbind, hbody]
                rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepOne,
                  memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepZero,
                  memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepCk,
                  memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepBg,
                  memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepMi,
                  memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepK,
                  memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepLenOld,
                  memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepCapOld,
                  memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepAl,
                  memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepCon,
                  memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepR1,
                  memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepKp1,
                  memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstepR2]
                simp only [stdVecGrowReallocFwd, hck, hbgU, hmiU, hal,
                  hcon, hr1, hr2, vecGrow_bind_ok, vecGrow_bind_err,
                  vecGrowU64, vecGrowI64, vecGrowOwned]
              | ok v =>
                obtain ⟨bR2, rfl, hR2live, hR2len⟩ :=
                  stdVecRelocFwd_ok _ _ _ _ _ _ _ _ _ _ hR1live hr2
                have hcallR2' : memEvalFuncFuel F stdVecRelocFunc
                    [.stdVecOwned b len cap,
                      .stdVecOwned bR1 0 newlen.toNat,
                      .u64 (pos - BitVec.ofNat 64 0),
                      .u64 (BitVec.ofNat 64 len),
                      .u64 ((pos - BitVec.ofNat 64 0) +
                        BitVec.ofNat 64 1)] =
                    .ok (.stdVecOwned bR2 0 newlen.toNat) := by
                  rw [hcallR2, hr2]
                have hstepR2 := memEvalProgStmt_callRet_ok vecGrowProg F "tC2"
                  stdVecRelocName ["t", "tC1", "k", "lenOld", "kp1"] _
                  (tripleMem b len cap) [("t", 0, 0)] _ stdVecRelocFunc
                  (.stdVecOwned bR2 0 newlen.toNat)
                  hargsR2 hfindRe hcallR2'
                have hlenOldLN : envLookup (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                    ("x", .i32 x)]
                  "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                  (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                  "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                  (.i64 (pos - BitVec.ofNat 64 0))) "k"
                  (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                  (.u64 (BitVec.ofNat 64 len))) "capOld"
                  (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                  (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                  (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                  (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                  (.u64 ((pos - BitVec.ofNat 64 0) +
                    BitVec.ofNat 64 1))) "tC2"
                  (.stdVecOwned bR2 0 newlen.toNat)) "lenOld" =
                  some (.u64 (BitVec.ofNat 64 len)) := by
                  simp [envLookup, envExtend,
                    show ("lenOld" : String) ≠ "tC2" by decide,
                    show ("lenOld" : String) ≠ "kp1" by decide,
                    show ("lenOld" : String) ≠ "tC1" by decide,
                    show ("lenOld" : String) ≠ "tNew1" by decide,
                    show ("lenOld" : String) ≠ "tNew0" by decide,
                    show ("lenOld" : String) ≠ "capOld" by decide]
                have honeLN : envLookup (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                    ("x", .i32 x)]
                  "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                  (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                  "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                  (.i64 (pos - BitVec.ofNat 64 0))) "k"
                  (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                  (.u64 (BitVec.ofNat 64 len))) "capOld"
                  (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                  (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                  (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                  (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                  (.u64 ((pos - BitVec.ofNat 64 0) +
                    BitVec.ofNat 64 1))) "tC2"
                  (.stdVecOwned bR2 0 newlen.toNat)) "one" =
                  some (.u64 (BitVec.ofNat 64 1)) := by
                  simp [envLookup, envExtend,
                    show ("one" : String) ≠ "tC2" by decide,
                    show ("one" : String) ≠ "kp1" by decide,
                    show ("one" : String) ≠ "tC1" by decide,
                    show ("one" : String) ≠ "tNew1" by decide,
                    show ("one" : String) ≠ "tNew0" by decide,
                    show ("one" : String) ≠ "capOld" by decide,
                    show ("one" : String) ≠ "lenOld" by decide,
                    show ("one" : String) ≠ "k" by decide,
                    show ("one" : String) ≠ "kd" by decide,
                    show ("one" : String) ≠ "bpos" by decide,
                    show ("one" : String) ≠ "newlen" by decide,
                    show ("one" : String) ≠ "zero" by decide]
                have hlenNewEval : evalExpr
                    (.uadd (.var "lenOld") (.var "one")) (envExtend
                    (envExtend (envExtend
                    (envExtend (envExtend (envExtend (envExtend (envExtend
                    (envExtend (envExtend (envExtend (envExtend (envExtend
                    [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                      ("x", .i32 x)]
                    "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                    (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                    "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                    (.i64 (pos - BitVec.ofNat 64 0))) "k"
                    (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                    (.u64 (BitVec.ofNat 64 len))) "capOld"
                    (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                    (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                    (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                    (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                    (.u64 ((pos - BitVec.ofNat 64 0) +
                      BitVec.ofNat 64 1))) "tC2"
                    (.stdVecOwned bR2 0 newlen.toNat)) =
                    .ok (.u64 ((BitVec.ofNat 64 len) +
                      BitVec.ofNat 64 1)) :=
                  evalExpr_uadd_u64 _ _ _ _ _
                    (evalExpr_var_hit _ _ _ hlenOldLN)
                    (evalExpr_var_hit _ _ _ honeLN)
                have hlenNewmem : memEvalExpr
                    (.uadd (.var "lenOld") (.var "one")) (envExtend
                    (envExtend (envExtend
                    (envExtend (envExtend (envExtend (envExtend (envExtend
                    (envExtend (envExtend (envExtend (envExtend (envExtend
                    [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                      ("x", .i32 x)]
                    "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                    (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                    "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                    (.i64 (pos - BitVec.ofNat 64 0))) "k"
                    (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                    (.u64 (BitVec.ofNat 64 len))) "capOld"
                    (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                    (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                    (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                    (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                    (.u64 ((pos - BitVec.ofNat 64 0) +
                      BitVec.ofNat 64 1))) "tC2"
                    (.stdVecOwned bR2 0 newlen.toNat))
                    (tripleMem b len cap) [("t", 0, 0)] =
                    .ok (.u64 ((BitVec.ofNat 64 len) +
                      BitVec.ofNat 64 1)) := by
                  rw [memEvalExpr_uadd_agree _ _ _ _ _
                    (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _)]
                  exact hlenNewEval
                have hstepLenNew : memEvalProgStmt vecGrowProg F
                    (.let_ "lenNew" (.u 64)
                      (.uadd (.var "lenOld") (.var "one"))) (envExtend
                    (envExtend (envExtend
                    (envExtend (envExtend (envExtend (envExtend (envExtend
                    (envExtend (envExtend (envExtend (envExtend (envExtend
                    [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                      ("x", .i32 x)]
                    "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                    (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                    "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                    (.i64 (pos - BitVec.ofNat 64 0))) "k"
                    (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                    (.u64 (BitVec.ofNat 64 len))) "capOld"
                    (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                    (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                    (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                    (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                    (.u64 ((pos - BitVec.ofNat 64 0) +
                      BitVec.ofNat 64 1))) "tC2"
                    (.stdVecOwned bR2 0 newlen.toNat))
                    (tripleMem b len cap) [("t", 0, 0)] =
                    .ok (((envExtend (envExtend (envExtend (envExtend
                    (envExtend (envExtend (envExtend (envExtend (envExtend
                    (envExtend (envExtend (envExtend (envExtend (envExtend
                    [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                      ("x", .i32 x)]
                    "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                    (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                    "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                    (.i64 (pos - BitVec.ofNat 64 0))) "k"
                    (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                    (.u64 (BitVec.ofNat 64 len))) "capOld"
                    (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                    (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                    (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                    (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                    (.u64 ((pos - BitVec.ofNat 64 0) +
                      BitVec.ofNat 64 1))) "tC2"
                    (.stdVecOwned bR2 0 newlen.toNat)) "lenNew"
                    (.u64 ((BitVec.ofNat 64 len) +
                      BitVec.ofNat 64 1)),
                    tripleMem b len cap, [("t", 0, 0)]), .fellThrough)) :=
                  by simp only [memEvalProgStmt]; exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _ (fun _ => by simp) (fun _ => by simp) (fun _ => by simp) hlenNewmem hlenNewEval
                have htGd : envLookup (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  (envExtend
                  [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                    ("x", .i32 x)]
                  "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                  (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                  "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                  (.i64 (pos - BitVec.ofNat 64 0))) "k"
                  (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                  (.u64 (BitVec.ofNat 64 len))) "capOld"
                  (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                  (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                  (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                  (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                  (.u64 ((pos - BitVec.ofNat 64 0) +
                    BitVec.ofNat 64 1))) "tC2"
                  (.stdVecOwned bR2 0 newlen.toNat)) "lenNew"
                  (.u64 ((BitVec.ofNat 64 len) +
                    BitVec.ofNat 64 1))) "t" =
                  some (.stdVecOwned b len cap) := by
                  simp [envLookup, envExtend,
                    show ("t" : String) ≠ "lenNew" by decide,
                    show ("t" : String) ≠ "tC2" by decide,
                    show ("t" : String) ≠ "kp1" by decide,
                    show ("t" : String) ≠ "tC1" by decide,
                    show ("t" : String) ≠ "tNew1" by decide,
                    show ("t" : String) ≠ "tNew0" by decide,
                    show ("t" : String) ≠ "capOld" by decide,
                    show ("t" : String) ≠ "lenOld" by decide,
                    show ("t" : String) ≠ "k" by decide,
                    show ("t" : String) ≠ "kd" by decide,
                    show ("t" : String) ≠ "bpos" by decide,
                    show ("t" : String) ≠ "newlen" by decide,
                    show ("t" : String) ≠ "zero" by decide,
                    show ("t" : String) ≠ "one" by decide]
                have hcapOldGd : envLookup (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  (envExtend
                  [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                    ("x", .i32 x)]
                  "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                  (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                  "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                  (.i64 (pos - BitVec.ofNat 64 0))) "k"
                  (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                  (.u64 (BitVec.ofNat 64 len))) "capOld"
                  (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                  (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                  (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                  (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                  (.u64 ((pos - BitVec.ofNat 64 0) +
                    BitVec.ofNat 64 1))) "tC2"
                  (.stdVecOwned bR2 0 newlen.toNat)) "lenNew"
                  (.u64 ((BitVec.ofNat 64 len) +
                    BitVec.ofNat 64 1))) "capOld" =
                  some (.u64 (BitVec.ofNat 64 cap)) := by
                  simp [envLookup, envExtend,
                    show ("capOld" : String) ≠ "lenNew" by decide,
                    show ("capOld" : String) ≠ "tC2" by decide,
                    show ("capOld" : String) ≠ "kp1" by decide,
                    show ("capOld" : String) ≠ "tC1" by decide,
                    show ("capOld" : String) ≠ "tNew1" by decide,
                    show ("capOld" : String) ≠ "tNew0" by decide]
                have hargsGd : lookupArgs (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  (envExtend
                  [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                    ("x", .i32 x)]
                  "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                  (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                  "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                  (.i64 (pos - BitVec.ofNat 64 0))) "k"
                  (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                  (.u64 (BitVec.ofNat 64 len))) "capOld"
                  (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                  (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                  (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                  (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                  (.u64 ((pos - BitVec.ofNat 64 0) +
                    BitVec.ofNat 64 1))) "tC2"
                  (.stdVecOwned bR2 0 newlen.toNat)) "lenNew"
                  (.u64 ((BitVec.ofNat 64 len) +
                    BitVec.ofNat 64 1))) ["t", "capOld"] =
                  some [.stdVecOwned b len cap,
                    .u64 (BitVec.ofNat 64 cap)] := by
                  simp only [lookupArgs, htGd, hcapOldGd]
                have hcallGd : memEvalFuncFuel F stdVecDeallocGuardFunc
                    [.stdVecOwned b len cap,
                      .u64 (BitVec.ofNat 64 cap)] =
                    stdVecDeallocGuardFwd b len cap
                      (BitVec.ofNat 64 cap) :=
                  memEvalFuncFuel_stdVecDeallocGuard F b len cap
                    (BitVec.ofNat 64 cap) hlive
                cases hgd : stdVecDeallocGuardFwd b len cap
                    (BitVec.ofNat 64 cap) with
                | error e =>
                  have hcallGd' : memEvalFuncFuel F stdVecDeallocGuardFunc
                      [.stdVecOwned b len cap,
                        .u64 (BitVec.ofNat 64 cap)] = .error e := by
                    rw [hcallGd, hgd]
                  have hstepGd := memEvalProgStmt_callRet_err vecGrowProg F
                    "tDead" stdVecDeallocName ["t", "capOld"] _
                    (tripleMem b len cap) [("t", 0, 0)] _
                    stdVecDeallocGuardFunc e hargsGd hfindGd hcallGd'
                  simp only [memEvalProgFunc, hbind, hbody]
                  rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepOne,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepZero,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepCk,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepBg,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepMi,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepK,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepLenOld,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepCapOld,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepAl,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepCon,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepR1,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepKp1,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepR2,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepLenNew,
                    memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstepGd]
                  simp only [stdVecGrowReallocFwd, hck, hbgU, hmiU, hal,
                    hcon, hr1, hr2, hgd, vecGrow_bind_ok, vecGrow_bind_err,
                    vecGrowU64, vecGrowI64, vecGrowOwned]
                | ok v =>
                  have hcallGd' : memEvalFuncFuel F stdVecDeallocGuardFunc
                      [.stdVecOwned b len cap,
                        .u64 (BitVec.ofNat 64 cap)] = .ok v := by
                    rw [hcallGd, hgd]
                  have hstepGd := memEvalProgStmt_callRet_ok vecGrowProg F
                    "tDead" stdVecDeallocName ["t", "capOld"] _
                    (tripleMem b len cap) [("t", 0, 0)] _
                    stdVecDeallocGuardFunc v hargsGd hfindGd hcallGd'
                  have htC2 : envLookup (envExtend (envExtend (envExtend
                    (envExtend (envExtend (envExtend (envExtend (envExtend
                    (envExtend (envExtend (envExtend (envExtend (envExtend
                    (envExtend (envExtend
                    [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                      ("x", .i32 x)]
                    "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                    (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                    "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                    (.i64 (pos - BitVec.ofNat 64 0))) "k"
                    (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                    (.u64 (BitVec.ofNat 64 len))) "capOld"
                    (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                    (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                    (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                    (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                    (.u64 ((pos - BitVec.ofNat 64 0) +
                      BitVec.ofNat 64 1))) "tC2"
                    (.stdVecOwned bR2 0 newlen.toNat)) "lenNew"
                    (.u64 ((BitVec.ofNat 64 len) +
                      BitVec.ofNat 64 1))) "tDead" v) "tC2" =
                    some (.stdVecOwned bR2 0 newlen.toNat) := by
                    simp [envLookup, envExtend,
                      show ("tC2" : String) ≠ "tDead" by decide]
                  have hlenNewHit : evalExpr (.var "lenNew") (envExtend
                    (envExtend (envExtend
                    (envExtend (envExtend (envExtend (envExtend (envExtend
                    (envExtend (envExtend (envExtend (envExtend (envExtend
                    (envExtend (envExtend
                    [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                      ("x", .i32 x)]
                    "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                    (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                    "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                    (.i64 (pos - BitVec.ofNat 64 0))) "k"
                    (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                    (.u64 (BitVec.ofNat 64 len))) "capOld"
                    (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                    (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                    (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                    (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                    (.u64 ((pos - BitVec.ofNat 64 0) +
                      BitVec.ofNat 64 1))) "tC2"
                    (.stdVecOwned bR2 0 newlen.toNat)) "lenNew"
                    (.u64 ((BitVec.ofNat 64 len) +
                      BitVec.ofNat 64 1))) "tDead" v) =
                    .ok (.u64 ((BitVec.ofNat 64 len) +
                      BitVec.ofNat 64 1)) := by
                    simp [evalExpr, envLookup, envExtend,
                      show ("lenNew" : String) ≠ "tDead" by decide]
                  have hretEval : evalExpr
                      (.vgrowSetLen "tC2" (.var "lenNew")) (envExtend
                      (envExtend (envExtend
                      (envExtend (envExtend (envExtend (envExtend (envExtend
                      (envExtend (envExtend (envExtend (envExtend (envExtend
                      (envExtend (envExtend
                      [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                        ("x", .i32 x)]
                      "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                      (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                      "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                      (.i64 (pos - BitVec.ofNat 64 0))) "k"
                      (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                      (.u64 (BitVec.ofNat 64 len))) "capOld"
                      (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                      (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                      (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                      (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                      (.u64 ((pos - BitVec.ofNat 64 0) +
                        BitVec.ofNat 64 1))) "tC2"
                      (.stdVecOwned bR2 0 newlen.toNat)) "lenNew"
                      (.u64 ((BitVec.ofNat 64 len) +
                        BitVec.ofNat 64 1))) "tDead" v) =
                      .ok (.stdVecOwned bR2
                        (((BitVec.ofNat 64 len) +
                          BitVec.ofNat 64 1).toNat) newlen.toNat) :=
                    evalExpr_vgrowSetLen_hit _ _ _ _ _ _ _ htC2 hlenNewHit
                  have hretmemEval : memEvalExpr
                      (.vgrowSetLen "tC2" (.var "lenNew")) (envExtend
                      (envExtend (envExtend
                      (envExtend (envExtend (envExtend (envExtend (envExtend
                      (envExtend (envExtend (envExtend (envExtend (envExtend
                      (envExtend (envExtend
                      [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                        ("x", .i32 x)]
                      "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                      (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                      "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                      (.i64 (pos - BitVec.ofNat 64 0))) "k"
                      (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                      (.u64 (BitVec.ofNat 64 len))) "capOld"
                      (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                      (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                      (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                      (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                      (.u64 ((pos - BitVec.ofNat 64 0) +
                        BitVec.ofNat 64 1))) "tC2"
                      (.stdVecOwned bR2 0 newlen.toNat)) "lenNew"
                      (.u64 ((BitVec.ofNat 64 len) +
                        BitVec.ofNat 64 1))) "tDead" v)
                      (tripleMem b len cap) [("t", 0, 0)] =
                      .ok (.stdVecOwned bR2
                        (((BitVec.ofNat 64 len) +
                          BitVec.ofNat 64 1).toNat) newlen.toNat) := by
                    rw [memEvalExpr_vgrowSetLen_agree _ _ _ _ _
                      (memEvalExpr_var _ _ _ _)]
                    exact hretEval
                  have hret : memEvalProgStmt vecGrowProg F
                      (.return_ (.vgrowSetLen "tC2" (.var "lenNew")))
                      (envExtend (envExtend (envExtend
                      (envExtend (envExtend (envExtend (envExtend (envExtend
                      (envExtend (envExtend (envExtend (envExtend (envExtend
                      (envExtend (envExtend
                      [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                        ("x", .i32 x)]
                      "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                      (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                      "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                      (.i64 (pos - BitVec.ofNat 64 0))) "k"
                      (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                      (.u64 (BitVec.ofNat 64 len))) "capOld"
                      (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                      (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                      (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                      (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                      (.u64 ((pos - BitVec.ofNat 64 0) +
                        BitVec.ofNat 64 1))) "tC2"
                      (.stdVecOwned bR2 0 newlen.toNat)) "lenNew"
                      (.u64 ((BitVec.ofNat 64 len) +
                        BitVec.ofNat 64 1))) "tDead" v)
                      (tripleMem b len cap) [("t", 0, 0)] =
                      .ok (((envExtend (envExtend (envExtend
                      (envExtend (envExtend (envExtend (envExtend (envExtend
                      (envExtend (envExtend (envExtend (envExtend (envExtend
                      (envExtend (envExtend
                      [("t", .stdVecOwned b len cap), ("pos", .u64 pos),
                        ("x", .i32 x)]
                      "one" (.u64 (BitVec.ofNat 64 1))) "zero"
                      (.u64 (BitVec.ofNat 64 0))) "newlen" (.u64 newlen))
                      "bpos" (.u64 (BitVec.ofNat 64 0))) "kd"
                      (.i64 (pos - BitVec.ofNat 64 0))) "k"
                      (.u64 (pos - BitVec.ofNat 64 0))) "lenOld"
                      (.u64 (BitVec.ofNat 64 len))) "capOld"
                      (.u64 (BitVec.ofNat 64 cap))) "tNew0"
                      (.stdVecOwned bNew 0 newlen.toNat)) "tNew1"
                      (.stdVecOwned bC 0 newlen.toNat)) "tC1"
                      (.stdVecOwned bR1 0 newlen.toNat)) "kp1"
                      (.u64 ((pos - BitVec.ofNat 64 0) +
                        BitVec.ofNat 64 1))) "tC2"
                      (.stdVecOwned bR2 0 newlen.toNat)) "lenNew"
                      (.u64 ((BitVec.ofNat 64 len) +
                        BitVec.ofNat 64 1))) "tDead" v,
                      tripleMem b len cap, [("t", 0, 0)]),
                      .returned (.stdVecOwned bR2
                        (((BitVec.ofNat 64 len) +
                          BitVec.ofNat 64 1).toNat) newlen.toNat))) :=
                    memEvalProgStmt_return vecGrowProg F _ _ _ _ _
                      hretmemEval
                  simp only [memEvalProgFunc, hbind, hbody]
                  rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepOne,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepZero,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepCk,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepBg,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepMi,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepK,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepLenOld,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepCapOld,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepAl,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepCon,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepR1,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepKp1,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepR2,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepLenNew,
                    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepGd,
                    hret]
                  simp only [stdVecGrowReallocFwd, hck, hbgU, hmiU, hal,
                    hcon, hr1, hr2, hgd, vecGrow_bind_ok, vecGrowU64,
                    vecGrowI64, vecGrowOwned]

/-- Transfer for `_M_realloc_insert`: program evaluation over the
    frozen b1 leaves agrees on both sides (the composer takes the old
    triple by value, so the footprint singleton from
    `oracleNoalias_stdVecGrowRealloc` suffices). -/
theorem memTransfer_stdVecGrowRealloc (F : Nat) (b : Vec32)
    (len cap : Nat) (pos : BitVec 64) (x : BitVec 32)
    (hlive : b.freed = false)
    (hmax : len ≤ stdVecMaxDiffBV.toNat)
    (hSlen : pos.toNat ≤ len)
    (hlenB : len ≤ b.val.length)
    (h64 : b.val.length < 2 ^ 64)
    (hfuel1 : pos.toNat + 1 ≤ F)
    (hfuel2 : len - pos.toNat + 1 ≤ F)
    (_h : oracleNoalias stdVecGrowReallocFunc
      [.stdVecOwned b len cap, .u64 pos, .i32 x]) :
    memEvalProgFunc vecGrowProg F stdVecGrowReallocFunc
      [.stdVecOwned b len cap, .u64 pos, .i32 x] =
      evalProgFunc vecGrowProg F stdVecGrowReallocFunc
        [.stdVecOwned b len cap, .u64 pos, .i32 x] := by
  rw [memEvalProgFunc_stdVecGrowRealloc F b len cap pos x hlive hmax
    hSlen hlenB h64 hfuel1 hfuel2,
    evalProgFunc_stdVecGrowRealloc F b len cap pos x hlive hmax hSlen
      hlenB h64 hfuel1 hfuel2]

