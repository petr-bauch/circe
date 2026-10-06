/-
Circe.Transfer.GrowReserve — N7b `reserve` composer + `vec_reserve_sum`
entry: memory/program agreement.

The composer proof mirrors `evalProgFunc_stdVecReserve` step for step
at memory level (the `max_size` throw arm, the allocate → relocate →
deallocate chain over the frozen b1 leaf forwards, the passthrough
arm); the entry mirrors `evalProgFunc_vecReserveSumEntry` like
`memEvalProgFunc_vecPushSumEntry` mirrors its value side.
-/
import Circe.Transfer.GrowEntry

/-! ## N7b `reserve` composer: memory agreement -/

/-- `memEval` for `reserve`: the guarded program over the frozen b1
    leaves agrees with the composer forward (mirrors
    `evalProgFunc_stdVecReserve`; memory and layout thread through
    unchanged — the composer binds only words — so each `callRet`
    discharges through its leaf `memEvalFuncFuel`). -/
theorem memEvalProgFunc_stdVecReserve (F : Nat) (b : Vec32) (len cap : Nat)
    (n : BitVec 64)
    (hlive : b.freed = false)
    (hlenB : len ≤ b.val.length)
    (hlenC : len ≤ cap)
    (hcap64 : cap < 2 ^ 64)
    (h64 : b.val.length < 2 ^ 64)
    (hfuel : len + 1 ≤ F) :
    memEvalProgFunc vecGrowProg F stdVecReserveFunc
      [.stdVecOwned b len cap, .u64 n] =
      stdVecReserveFwd b len cap n := by
  have hbind : bindMemArgs stdVecReserveFunc.args
      [.stdVecOwned b len cap, .u64 n] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("n", .u64 n)],
        tripleMem b len cap, [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "n", ty := .u 64, role := .owned }]
      [.stdVecOwned b len cap, .u64 n] emptyMem = _
    exact bindMemArgs_stdVecReserve b len cap n
  have hbody : stdVecReserveFunc.body =
      (.if_ (.ult (.lit (.u64 stdVecMaxDiffBV)) (.var "n"))
      .fail
      (.if_ (.ult (.vgrowCap "t") (.var "n"))
        (.seq (.let_ "zero" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
          (.seq (.let_ "lenOld" (.u 64) (.vgrowLen "t"))
          (.seq (.let_ "capOld" (.u 64) (.vgrowCap "t"))
          (.seq (.callRet "tA" stdVecAllocateName ["n"])
          (.seq (.callRet "tR" stdVecRelocName
                   ["t", "tA", "zero", "lenOld", "zero"])
          (.seq (.callRet "tDead" stdVecDeallocName ["t", "capOld"])
            (.return_ (.vgrowSetLen "tR" (.var "lenOld")))))))))
        (.return_ (.var "t")))) := rfl
  have hM64 : stdVecMaxDiffBV.toNat < 2 ^ 64 := BitVec.isLt _
  have hlen64 : len < 2 ^ 64 := by omega
  have hrt : (BitVec.ofNat 64 len).toNat = len := ofNat64_toNat _ hlen64
  have hcapT : (BitVec.ofNat 64 cap).toNat = cap :=
    ofNat64_toNat _ hcap64
  have hz : (BitVec.ofNat 64 0).toNat = 0 := ofNat64_toNat 0 (by decide)
  have hfindAl : findFunc vecGrowProg stdVecAllocateName =
      some stdVecAllocFunc := by
    unfold vecGrowProg
    rw [findFunc_miss _ _ _ (by decide),
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
  have hmaxEval : evalExpr
      (.ult (.lit (.u64 stdVecMaxDiffBV)) (.var "n"))
      [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
      .ok (.b (stdVecMaxDiffBV.ult n)) := by
    simp [evalExpr, litVal, envLookup,
      show ("n" : String) ≠ "t" by decide]
  have hmaxMem : memEvalExpr
      (.ult (.lit (.u64 stdVecMaxDiffBV)) (.var "n"))
      [("t", .stdVecOwned b len cap), ("n", .u64 n)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr
        (.ult (.lit (.u64 stdVecMaxDiffBV)) (.var "n"))
        [("t", .stdVecOwned b len cap), ("n", .u64 n)] :=
    memEvalExpr_ult_agree _ _ _ _ _
      (memEvalExpr_lit _ _ _ _) (memEvalExpr_var _ _ _ _)
  by_cases hmax : stdVecMaxDiffBV.ult n = true
  · -- Over `max_size`: the throw arm fails loudly.
    have hcond : evalExpr
          (.ult (.lit (.u64 stdVecMaxDiffBV)) (.var "n"))
          [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
          .ok (.b true) := by
      simp [hmaxEval, hmax]
    have hcondMem : memEvalExpr
          (.ult (.lit (.u64 stdVecMaxDiffBV)) (.var "n"))
          [("t", .stdVecOwned b len cap), ("n", .u64 n)]
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok (.b true) := by
      rw [hmaxMem]; exact hcond
    have hfailMem : memEvalProgStmt vecGrowProg F .fail
          [("t", .stdVecOwned b len cap), ("n", .u64 n)]
          (tripleMem b len cap) [("t", 0, 0)] =
          .error .AssertFail := by
      simp only [memEvalProgStmt]
      exact memEvalStmtFuel_fail _ _ _ _
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_if_true vecGrowProg F _ _ _ _ _ _ hcondMem,
      hfailMem]
    simp [stdVecReserveFwd, hmax]
  · -- Under `max_size`: the capacity guard dispatches.
    have hmaxF : stdVecMaxDiffBV.ult n = false := by
      cases hc : stdVecMaxDiffBV.ult n with
      | true => simp [hc] at hmax
      | false => rfl
    have hcond : evalExpr
          (.ult (.lit (.u64 stdVecMaxDiffBV)) (.var "n"))
          [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
          .ok (.b false) := by
      simp [hmaxEval, hmaxF]
    have hcondMem : memEvalExpr
          (.ult (.lit (.u64 stdVecMaxDiffBV)) (.var "n"))
          [("t", .stdVecOwned b len cap), ("n", .u64 n)]
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok (.b false) := by
      rw [hmaxMem]; exact hcond
    have htCap : envLookup [("t", .stdVecOwned b len cap),
          ("n", .u64 n)] "t" =
        some (.stdVecOwned b len cap) := by
      simp [envLookup]
    have hcapEval : evalExpr (.ult (.vgrowCap "t") (.var "n"))
          [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
          .ok (.b ((BitVec.ofNat 64 cap).ult n)) := by
      have hcap := evalExpr_vgrowCap_some "t"
        [("t", .stdVecOwned b len cap), ("n", .u64 n)] b len cap htCap
      simp [evalExpr, envLookup,
        show ("n" : String) ≠ "t" by decide]
    have hlay : layoutLookup [("t", 0, 0)] "t" = some (0, 0) := by
      simp [layoutLookup]
    have hmemCap : memLoad (tripleMem b len cap) 0 0 1 =
        .ok (BitVec.ofNat 32 cap) := by
      simp [tripleMem, memLoad, memFind, hlive]
    have hcapAgree : memEvalExpr (.vgrowCap "t")
          [("t", .stdVecOwned b len cap), ("n", .u64 n)]
          (tripleMem b len cap) [("t", 0, 0)] =
          evalExpr (.vgrowCap "t")
            [("t", .stdVecOwned b len cap), ("n", .u64 n)] :=
      memEvalExpr_vgrowCap_hit "t" _ _ _ b len cap 0 0 hlay htCap hmemCap
    have hcapMem : memEvalExpr (.ult (.vgrowCap "t") (.var "n"))
          [("t", .stdVecOwned b len cap), ("n", .u64 n)]
          (tripleMem b len cap) [("t", 0, 0)] =
          evalExpr (.ult (.vgrowCap "t") (.var "n"))
            [("t", .stdVecOwned b len cap), ("n", .u64 n)] :=
      memEvalExpr_ult_agree _ _ _ _ _ hcapAgree
        (memEvalExpr_var _ _ _ _)
    by_cases hcap : (BitVec.ofNat 64 cap).ult n = true
    · -- Reallocation arm: allocate → relocate → deallocate.
      have hcond2 : evalExpr (.ult (.vgrowCap "t") (.var "n"))
            [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
            .ok (.b true) := by
        simp [hcapEval, hcap]
      have hcondMem2 : memEvalExpr (.ult (.vgrowCap "t") (.var "n"))
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            (tripleMem b len cap) [("t", 0, 0)] =
            .ok (.b true) := by
        rw [hcapMem]; exact hcond2
      have hcapLt : (BitVec.ofNat 64 cap).toNat < n.toNat := by
        have h := hcap
        rw [BitVec.ult_eq_decide] at h
        simpa using h
      have hnPos : (BitVec.ofNat 64 0).ult n = true := by
        have h0 : (BitVec.ofNat 64 0).toNat < n.toNat := by
          rw [hz]
          omega
        rw [BitVec.ult_eq_decide]
        simpa using h0
      have hzero : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
            [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
            .ok (.u64 (BitVec.ofNat 64 0)) := rfl
      have hmemZero : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            (tripleMem b len cap) [("t", 0, 0)] =
            .ok (.u64 (BitVec.ofNat 64 0)) := by
        rw [memEvalExpr_lit]
        exact hzero
      have hstepZero : memEvalProgStmt vecGrowProg F
            (.let_ "zero" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            (tripleMem b len cap) [("t", 0, 0)] =
            .ok (((envExtend [("t", .stdVecOwned b len cap),
              ("n", .u64 n)] "zero" (.u64 (BitVec.ofNat 64 0)),
              tripleMem b len cap, [("t", 0, 0)]), .fellThrough)) := by
        rw [memEvalProgStmt_let_fb]
        exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
          (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
          hmemZero hzero
      have htLen : envLookup (envExtend
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            "zero" (.u64 (BitVec.ofNat 64 0))) "t" =
            some (.stdVecOwned b len cap) := by
        simp [envLookup, envExtend,
          show ("t" : String) ≠ "zero" by decide]
      have hlenOldEval : evalExpr (.vgrowLen "t") (envExtend
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            "zero" (.u64 (BitVec.ofNat 64 0))) =
            .ok (.u64 (BitVec.ofNat 64 len)) :=
        evalExpr_vgrowLen_some _ _ _ _ _ htLen
      have hmemLen : memLoad (tripleMem b len cap) 0 0 0 =
          .ok (BitVec.ofNat 32 len) := by
        simp [tripleMem, memLoad, memFind, hlive]
      have hlenOldMem : memEvalExpr (.vgrowLen "t") (envExtend
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            "zero" (.u64 (BitVec.ofNat 64 0)))
            (tripleMem b len cap) [("t", 0, 0)] =
            .ok (.u64 (BitVec.ofNat 64 len)) := by
        rw [memEvalExpr_vgrowLen_hit "t" _ _ _ _ _ _ _ _ hlay htLen
          hmemLen]
        exact hlenOldEval
      have hstepLenOld : memEvalProgStmt vecGrowProg F
            (.let_ "lenOld" (.u 64) (.vgrowLen "t")) (envExtend
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            "zero" (.u64 (BitVec.ofNat 64 0)))
            (tripleMem b len cap) [("t", 0, 0)] =
            .ok (((envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            "zero" (.u64 (BitVec.ofNat 64 0))) "lenOld"
            (.u64 (BitVec.ofNat 64 len)),
            tripleMem b len cap, [("t", 0, 0)]), .fellThrough)) := by
        rw [memEvalProgStmt_let_fb]
        exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
          (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
          hlenOldMem hlenOldEval
      have htCap2 : envLookup (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            "zero" (.u64 (BitVec.ofNat 64 0))) "lenOld"
            (.u64 (BitVec.ofNat 64 len))) "t" =
            some (.stdVecOwned b len cap) := by
        simp [envLookup, envExtend,
          show ("t" : String) ≠ "lenOld" by decide,
          show ("t" : String) ≠ "zero" by decide]
      have hcapOldEval : evalExpr (.vgrowCap "t") (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            "zero" (.u64 (BitVec.ofNat 64 0))) "lenOld"
            (.u64 (BitVec.ofNat 64 len))) =
            .ok (.u64 (BitVec.ofNat 64 cap)) :=
        evalExpr_vgrowCap_some _ _ _ _ _ htCap2
      have hcapOldMem : memEvalExpr (.vgrowCap "t") (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            "zero" (.u64 (BitVec.ofNat 64 0))) "lenOld"
            (.u64 (BitVec.ofNat 64 len)))
            (tripleMem b len cap) [("t", 0, 0)] =
            .ok (.u64 (BitVec.ofNat 64 cap)) := by
        rw [memEvalExpr_vgrowCap_hit "t" _ _ _ _ _ _ _ _ hlay htCap2
          hmemCap]
        exact hcapOldEval
      have hstepCapOld : memEvalProgStmt vecGrowProg F
            (.let_ "capOld" (.u 64) (.vgrowCap "t")) (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            "zero" (.u64 (BitVec.ofNat 64 0))) "lenOld"
            (.u64 (BitVec.ofNat 64 len)))
            (tripleMem b len cap) [("t", 0, 0)] =
            .ok (((envExtend (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            "zero" (.u64 (BitVec.ofNat 64 0))) "lenOld"
            (.u64 (BitVec.ofNat 64 len))) "capOld"
            (.u64 (BitVec.ofNat 64 cap)),
            tripleMem b len cap, [("t", 0, 0)]), .fellThrough)) := by
        rw [memEvalProgStmt_let_fb]
        exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
          (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
          hcapOldMem hcapOldEval
      have hcallAl : memEvalFuncFuel F stdVecAllocFunc [.u64 n] =
          stdVecAllocFwd n :=
        memEvalFuncFuel_stdVecAlloc F n
      cases halR : stdVecAllocFwd n with
      | error e =>
        have hcallAl' : memEvalFuncFuel F stdVecAllocFunc [.u64 n] =
            .error e := by
          rw [hcallAl, halR]
        have hargsAl : lookupArgs (envExtend (envExtend (envExtend
              [("t", .stdVecOwned b len cap), ("n", .u64 n)]
              "zero" (.u64 (BitVec.ofNat 64 0))) "lenOld"
              (.u64 (BitVec.ofNat 64 len))) "capOld"
              (.u64 (BitVec.ofNat 64 cap))) ["n"] =
            some [.u64 n] := by
          simp [lookupArgs, envLookup, envExtend]
        have hstepAl := memEvalProgStmt_callRet_err vecGrowProg F "tA"
          stdVecAllocateName ["n"] _ (tripleMem b len cap)
          [("t", 0, 0)] _ stdVecAllocFunc e hargsAl hfindAl hcallAl'
        simp only [memEvalProgFunc, hbind, hbody]
        rw [memEvalProgStmt_if_false vecGrowProg F _ _ _ _ _ _ hcondMem,
          memEvalProgStmt_if_true vecGrowProg F _ _ _ _ _ _ hcondMem2,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
            hstepZero,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
            hstepLenOld,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
            hstepCapOld,
          memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstepAl]
        simp only [stdVecReserveFwd, ite_true, ite_false, reduceCtorEq, hmaxF, hcap, halR,
          vecGrow_bind_err, vecGrowOwned]
      | ok v =>
        obtain ⟨bNew, rfl, hNewLive, hNewLen⟩ :=
          stdVecAllocFwd_ok n v hnPos halR
        have hcallAl' : memEvalFuncFuel F stdVecAllocFunc [.u64 n] =
            .ok (.stdVecOwned bNew 0 n.toNat) := by
          rw [hcallAl, halR]
        have hargsAl : lookupArgs (envExtend (envExtend (envExtend
              [("t", .stdVecOwned b len cap), ("n", .u64 n)]
              "zero" (.u64 (BitVec.ofNat 64 0))) "lenOld"
              (.u64 (BitVec.ofNat 64 len))) "capOld"
              (.u64 (BitVec.ofNat 64 cap))) ["n"] =
            some [.u64 n] := by
          simp [lookupArgs, envLookup, envExtend]
        have hstepAl := memEvalProgStmt_callRet_ok vecGrowProg F "tA"
          stdVecAllocateName ["n"] _ (tripleMem b len cap)
          [("t", 0, 0)] _ stdVecAllocFunc
          (.stdVecOwned bNew 0 n.toNat) hargsAl hfindAl hcallAl'
        have hargsRe : lookupArgs (envExtend (envExtend (envExtend
              (envExtend
              [("t", .stdVecOwned b len cap), ("n", .u64 n)]
              "zero" (.u64 (BitVec.ofNat 64 0))) "lenOld"
              (.u64 (BitVec.ofNat 64 len))) "capOld"
              (.u64 (BitVec.ofNat 64 cap))) "tA"
              (.stdVecOwned bNew 0 n.toNat))
              ["t", "tA", "zero", "lenOld", "zero"] =
            some [.stdVecOwned b len cap,
              .stdVecOwned bNew 0 n.toNat,
              .u64 (BitVec.ofNat 64 0),
              .u64 (BitVec.ofNat 64 len),
              .u64 (BitVec.ofNat 64 0)] := by
          simp [lookupArgs, envLookup, envExtend,
            show ("t" : String) ≠ "tA" by decide,
            show ("t" : String) ≠ "capOld" by decide,
            show ("t" : String) ≠ "lenOld" by decide,
            show ("t" : String) ≠ "zero" by decide,
            show ("zero" : String) ≠ "tA" by decide,
            show ("zero" : String) ≠ "capOld" by decide,
            show ("zero" : String) ≠ "lenOld" by decide,
            show ("lenOld" : String) ≠ "tA" by decide,
            show ("lenOld" : String) ≠ "capOld" by decide]
        have hcallRe : memEvalFuncFuel F stdVecRelocFunc
              [.stdVecOwned b len cap,
                .stdVecOwned bNew 0 n.toNat,
                .u64 (BitVec.ofNat 64 0),
                .u64 (BitVec.ofNat 64 len),
                .u64 (BitVec.ofNat 64 0)] =
              stdVecRelocFwd b len cap bNew 0 n.toNat
                (BitVec.ofNat 64 0) (BitVec.ofNat 64 len)
                (BitVec.ofNat 64 0) :=
          memEvalFuncFuel_stdVecReloc F b len cap bNew 0 n.toNat
            (BitVec.ofNat 64 0) (BitVec.ofNat 64 len)
            (BitVec.ofNat 64 0) (by rw [hz, hrt]; omega) hlive hNewLive
            (by rw [hrt]; exact hlenB)
            (by rw [hz, hrt, hNewLen]; omega)
            (by simp [hrt]) h64
            (by rw [hNewLen]; exact BitVec.isLt _)
            (by rw [hrt, hz]; omega)
        cases hr1 : stdVecRelocFwd b len cap bNew 0 n.toNat
            (BitVec.ofNat 64 0) (BitVec.ofNat 64 len)
            (BitVec.ofNat 64 0) with
        | error e =>
          have hcallRe' : memEvalFuncFuel F stdVecRelocFunc
                [.stdVecOwned b len cap,
                  .stdVecOwned bNew 0 n.toNat,
                  .u64 (BitVec.ofNat 64 0),
                  .u64 (BitVec.ofNat 64 len),
                  .u64 (BitVec.ofNat 64 0)] = .error e := by
            rw [hcallRe, hr1]
          have hstepRe := memEvalProgStmt_callRet_err vecGrowProg F "tR"
            stdVecRelocName ["t", "tA", "zero", "lenOld", "zero"] _
            (tripleMem b len cap) [("t", 0, 0)] _
            stdVecRelocFunc e hargsRe hfindRe hcallRe'
          simp only [memEvalProgFunc, hbind, hbody]
          rw [memEvalProgStmt_if_false vecGrowProg F _ _ _ _ _ _ hcondMem,
            memEvalProgStmt_if_true vecGrowProg F _ _ _ _ _ _ hcondMem2,
            memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
              hstepZero,
            memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
              hstepLenOld,
            memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
              hstepCapOld,
            memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
              hstepAl,
            memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstepRe]
          simp only [stdVecReserveFwd, ite_true, ite_false, reduceCtorEq, hmaxF, hcap, halR, hr1,
            vecGrow_bind_ok, vecGrow_bind_err, vecGrowOwned]
        | ok v =>
          obtain ⟨bR, rfl, hRlive, hRlen⟩ :=
            stdVecRelocFwd_ok _ _ _ _ _ _ _ _ _ _ hNewLive hr1
          have hcallRe' : memEvalFuncFuel F stdVecRelocFunc
                [.stdVecOwned b len cap,
                  .stdVecOwned bNew 0 n.toNat,
                  .u64 (BitVec.ofNat 64 0),
                  .u64 (BitVec.ofNat 64 len),
                  .u64 (BitVec.ofNat 64 0)] =
                .ok (.stdVecOwned bR 0 n.toNat) := by
            rw [hcallRe, hr1]
          have hstepRe := memEvalProgStmt_callRet_ok vecGrowProg F "tR"
            stdVecRelocName ["t", "tA", "zero", "lenOld", "zero"] _
            (tripleMem b len cap) [("t", 0, 0)] _
            stdVecRelocFunc (.stdVecOwned bR 0 n.toNat)
            hargsRe hfindRe hcallRe'
          have hargsGd : lookupArgs (envExtend (envExtend (envExtend
                (envExtend (envExtend
                [("t", .stdVecOwned b len cap), ("n", .u64 n)]
                "zero" (.u64 (BitVec.ofNat 64 0))) "lenOld"
                (.u64 (BitVec.ofNat 64 len))) "capOld"
                (.u64 (BitVec.ofNat 64 cap))) "tA"
                (.stdVecOwned bNew 0 n.toNat)) "tR"
                (.stdVecOwned bR 0 n.toNat)) ["t", "capOld"] =
              some [.stdVecOwned b len cap,
                .u64 (BitVec.ofNat 64 cap)] := by
            simp [lookupArgs, envLookup, envExtend,
              show ("t" : String) ≠ "tR" by decide,
              show ("t" : String) ≠ "tA" by decide,
              show ("t" : String) ≠ "capOld" by decide,
              show ("t" : String) ≠ "lenOld" by decide,
              show ("t" : String) ≠ "zero" by decide,
              show ("capOld" : String) ≠ "tR" by decide,
              show ("capOld" : String) ≠ "tA" by decide]
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
            rw [memEvalProgStmt_if_false vecGrowProg F _ _ _ _ _ _
                hcondMem,
              memEvalProgStmt_if_true vecGrowProg F _ _ _ _ _ _
                hcondMem2,
              memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                hstepZero,
              memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                hstepLenOld,
              memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                hstepCapOld,
              memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                hstepAl,
              memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                hstepRe,
              memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstepGd]
            simp only [stdVecReserveFwd, ite_true, ite_false, reduceCtorEq, hmaxF, hcap, halR, hr1, hgd,
              vecGrow_bind_ok, vecGrow_bind_err, vecGrowOwned]
          | ok v =>
            have hcallGd' : memEvalFuncFuel F stdVecDeallocGuardFunc
                  [.stdVecOwned b len cap,
                    .u64 (BitVec.ofNat 64 cap)] = .ok v := by
              rw [hcallGd, hgd]
            have hstepGd := memEvalProgStmt_callRet_ok vecGrowProg F
              "tDead" stdVecDeallocName ["t", "capOld"] _
              (tripleMem b len cap) [("t", 0, 0)] _
              stdVecDeallocGuardFunc v hargsGd hfindGd hcallGd'
            have htR : envLookup (envExtend (envExtend (envExtend
                  (envExtend (envExtend (envExtend
                  [("t", .stdVecOwned b len cap), ("n", .u64 n)]
                  "zero" (.u64 (BitVec.ofNat 64 0))) "lenOld"
                  (.u64 (BitVec.ofNat 64 len))) "capOld"
                  (.u64 (BitVec.ofNat 64 cap))) "tA"
                  (.stdVecOwned bNew 0 n.toNat)) "tR"
                  (.stdVecOwned bR 0 n.toNat)) "tDead" v) "tR" =
                  some (.stdVecOwned bR 0 n.toNat) := by
              simp [envLookup, envExtend,
                show ("tR" : String) ≠ "tDead" by decide]
            have hlenOldHit : evalExpr (.var "lenOld") (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  [("t", .stdVecOwned b len cap), ("n", .u64 n)]
                  "zero" (.u64 (BitVec.ofNat 64 0))) "lenOld"
                  (.u64 (BitVec.ofNat 64 len))) "capOld"
                  (.u64 (BitVec.ofNat 64 cap))) "tA"
                  (.stdVecOwned bNew 0 n.toNat)) "tR"
                  (.stdVecOwned bR 0 n.toNat)) "tDead" v) =
                  .ok (.u64 (BitVec.ofNat 64 len)) := by
              simp [evalExpr, envLookup, envExtend,
                show ("lenOld" : String) ≠ "tDead" by decide,
                show ("lenOld" : String) ≠ "tR" by decide,
                show ("lenOld" : String) ≠ "tA" by decide,
                show ("lenOld" : String) ≠ "capOld" by decide]
            have hretEval : evalExpr
                  (.vgrowSetLen "tR" (.var "lenOld")) (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  [("t", .stdVecOwned b len cap), ("n", .u64 n)]
                  "zero" (.u64 (BitVec.ofNat 64 0))) "lenOld"
                  (.u64 (BitVec.ofNat 64 len))) "capOld"
                  (.u64 (BitVec.ofNat 64 cap))) "tA"
                  (.stdVecOwned bNew 0 n.toNat)) "tR"
                  (.stdVecOwned bR 0 n.toNat)) "tDead" v) =
                  .ok (.stdVecOwned bR ((BitVec.ofNat 64 len).toNat)
                    n.toNat) :=
              evalExpr_vgrowSetLen_hit _ _ _ _ _ _ _ htR hlenOldHit
            have hretMemEval : memEvalExpr
                  (.vgrowSetLen "tR" (.var "lenOld")) (envExtend
                  (envExtend (envExtend (envExtend (envExtend (envExtend
                  [("t", .stdVecOwned b len cap), ("n", .u64 n)]
                  "zero" (.u64 (BitVec.ofNat 64 0))) "lenOld"
                  (.u64 (BitVec.ofNat 64 len))) "capOld"
                  (.u64 (BitVec.ofNat 64 cap))) "tA"
                  (.stdVecOwned bNew 0 n.toNat)) "tR"
                  (.stdVecOwned bR 0 n.toNat)) "tDead" v)
                  (tripleMem b len cap) [("t", 0, 0)] =
                  .ok (.stdVecOwned bR ((BitVec.ofNat 64 len).toNat)
                    n.toNat) := by
              rw [memEvalExpr_vgrowSetLen_agree _ _ _ _ _
                (memEvalExpr_var _ _ _ _)]
              exact hretEval
            have hret : memEvalProgStmt vecGrowProg F
                  (.return_ (.vgrowSetLen "tR" (.var "lenOld")))
                  (envExtend (envExtend (envExtend (envExtend
                  (envExtend (envExtend
                  [("t", .stdVecOwned b len cap), ("n", .u64 n)]
                  "zero" (.u64 (BitVec.ofNat 64 0))) "lenOld"
                  (.u64 (BitVec.ofNat 64 len))) "capOld"
                  (.u64 (BitVec.ofNat 64 cap))) "tA"
                  (.stdVecOwned bNew 0 n.toNat)) "tR"
                  (.stdVecOwned bR 0 n.toNat)) "tDead" v)
                  (tripleMem b len cap) [("t", 0, 0)] =
                  .ok ((envExtend (envExtend (envExtend (envExtend
                  (envExtend (envExtend
                  [("t", .stdVecOwned b len cap), ("n", .u64 n)]
                  "zero" (.u64 (BitVec.ofNat 64 0))) "lenOld"
                  (.u64 (BitVec.ofNat 64 len))) "capOld"
                  (.u64 (BitVec.ofNat 64 cap))) "tA"
                  (.stdVecOwned bNew 0 n.toNat)) "tR"
                  (.stdVecOwned bR 0 n.toNat)) "tDead" v,
                  tripleMem b len cap, [("t", 0, 0)]),
                  .returned (.stdVecOwned bR
                    ((BitVec.ofNat 64 len).toNat) n.toNat)) :=
              memEvalProgStmt_return vecGrowProg F _ _ _ _ _
                hretMemEval
            simp only [memEvalProgFunc, hbind, hbody]
            rw [memEvalProgStmt_if_false vecGrowProg F _ _ _ _ _ _
                hcondMem,
              memEvalProgStmt_if_true vecGrowProg F _ _ _ _ _ _
                hcondMem2,
              memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                hstepZero,
              memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                hstepLenOld,
              memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                hstepCapOld,
              memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                hstepAl,
              memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                hstepRe,
              memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                hstepGd,
              hret]
            simp only [stdVecReserveFwd, ite_true, ite_false, reduceCtorEq, hmaxF, hcap, halR, hr1, hgd,
              vecGrow_bind_ok, vecGrowOwned]
    · -- Capacity suffices: the triple passes through.
      have hcapF : (BitVec.ofNat 64 cap).ult n = false := by
        cases hc : (BitVec.ofNat 64 cap).ult n with
        | true => simp [hc] at hcap
        | false => rfl
      have hcond2 : evalExpr (.ult (.vgrowCap "t") (.var "n"))
            [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
            .ok (.b false) := by
        simp [hcapEval, hcapF]
      have hcondMem2 : memEvalExpr (.ult (.vgrowCap "t") (.var "n"))
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            (tripleMem b len cap) [("t", 0, 0)] =
            .ok (.b false) := by
        rw [hcapMem]; exact hcond2
      have htRet : envLookup [("t", .stdVecOwned b len cap),
            ("n", .u64 n)] "t" =
          some (.stdVecOwned b len cap) := by
        simp [envLookup]
      have hretEval : evalExpr (.var "t")
            [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
            .ok (.stdVecOwned b len cap) := by
        simp [evalExpr, htRet]
      have hretMemEval : memEvalExpr (.var "t")
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            (tripleMem b len cap) [("t", 0, 0)] =
            .ok (.stdVecOwned b len cap) := by
        rw [memEvalExpr_var]
        exact hretEval
      have hret : memEvalProgStmt vecGrowProg F
            (.return_ (.var "t"))
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            (tripleMem b len cap) [("t", 0, 0)] =
            .ok (([("t", .stdVecOwned b len cap), ("n", .u64 n)],
              tripleMem b len cap, [("t", 0, 0)]),
              .returned (.stdVecOwned b len cap)) :=
        memEvalProgStmt_return vecGrowProg F _ _ _ _ _
          hretMemEval
      simp only [memEvalProgFunc, hbind, hbody]
      rw [memEvalProgStmt_if_false vecGrowProg F _ _ _ _ _ _ hcondMem,
        memEvalProgStmt_if_false vecGrowProg F _ _ _ _ _ _ hcondMem2,
        hret]
      simp [stdVecReserveFwd, hmaxF, hcapF]

/-- Transfer for `reserve`: program evaluation over the frozen leaves
    plus the proved composer agrees on both sides (the composer takes
    the old triple by value, so the footprint singleton from
    `oracleNoalias_stdVecReserve` suffices). -/
theorem memTransfer_stdVecReserve (F : Nat) (b : Vec32)
    (len cap : Nat) (n : BitVec 64)
    (hlive : b.freed = false)
    (hlenB : len ≤ b.val.length)
    (hlenC : len ≤ cap)
    (hcap64 : cap < 2 ^ 64)
    (h64 : b.val.length < 2 ^ 64)
    (hfuel : len + 1 ≤ F)
    (_h : oracleNoalias stdVecReserveFunc
      [.stdVecOwned b len cap, .u64 n]) :
    memEvalProgFunc vecGrowProg F stdVecReserveFunc
      [.stdVecOwned b len cap, .u64 n] =
      evalProgFunc vecGrowProg F stdVecReserveFunc
        [.stdVecOwned b len cap, .u64 n] := by
  rw [memEvalProgFunc_stdVecReserve F b len cap n hlive hlenB hlenC
    hcap64 h64 hfuel,
    evalProgFunc_stdVecReserve F b len cap n hlive hlenB hlenC
      hcap64 h64 hfuel]

/-! ## N7b `vec_reserve_sum` entry: memory agreement -/

/-- `memEval` for the closed entry: thirteen steps over `emptyMem`/`[]`
    (no caller footprint; every callee runs on its own binding) agree
    with `vecReserveSumEntryFwd`. Mirrors
    `evalProgFunc_vecReserveSumEntry` step for step (like
    `memEvalProgFunc_vecPushSumEntry` mirrors its value side). -/
theorem memEvalProgFunc_vecReserveSumEntry (F : Nat) (hF : 6 ≤ F) :
    memEvalProgFunc vecGrowProg F vecReserveSumEntryFunc [] =
      vecReserveSumEntryFwd := by
  obtain ⟨F', rfl, hF'⟩ := fuel_step_down 5 hF
  have hbind : bindMemArgs vecReserveSumEntryFunc.args [] emptyMem =
      some ([], emptyMem, []) := rfl
  have hbody : vecReserveSumEntryFunc.body =
      .seq (.callRet "v0" stdVecCtorName [])
      (.seq (.let_ "n" (.u 64) (.lit (.u64 (BitVec.ofNat 64 10))))
      (.seq (.callProg "v1" stdVecReserveName ["v0", "n"])
      (.seq (.let_ "c0" (.i 32) (.lit (.i32 (BitVec.ofNat 32 1))))
      (.seq (.callProg "v2" stdVecPushBackName ["v1", "c0"])
      (.seq (.let_ "c1" (.i 32) (.lit (.i32 (BitVec.ofNat 32 2))))
      (.seq (.callProg "v3" stdVecPushBackName ["v2", "c1"])
      (.seq (.let_ "n0" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.seq (.callRet "e0" stdVecGrowIndexName ["v3", "n0"])
      (.seq (.let_ "n1" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      (.seq (.callRet "e1" stdVecGrowIndexName ["v3", "n1"])
      (.seq (.let_ "s" (.i 32) (.add (.var "e0") (.var "e1")))
      (.seq (.callRet "v4" stdVecDtorName ["v3"])
        (.return_ (.var "s")))))))))))))) := rfl
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
  -- Step 2: `n = 10`.
  have hlitN : evalExpr (.lit (.u64 (BitVec.ofNat 64 10)))
      (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0)) =
      .ok (.u64 (BitVec.ofNat 64 10)) := by
    simp [evalExpr, litVal]
  have hmstepN : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "n" (.u 64) (.lit (.u64 (BitVec.ofNat 64 10))))
      (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0)) emptyMem [] =
      .ok ((envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)), emptyMem, []),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h)
      (memEvalExpr_lit _ _ _ _) hlitN
  -- Step 3: `reserve(10)`.
  have hv0n : envLookup
      (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10))) "v0" =
      some (.stdVecOwned ⟨[], false⟩ 0 0) := by
    simp [envLookup, envExtend,
      show ("v0" : String) ≠ "n" by decide]
  have hnn : envLookup
      (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10))) "n" =
      some (.u64 (BitVec.ofNat 64 10)) := by
    simp [envLookup, envExtend]
  have hargsR : lookupArgs
      (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10))) ["v0", "n"] =
      some [.stdVecOwned ⟨[], false⟩ 0 0,
        .u64 (BitVec.ofNat 64 10)] := by
    simp only [lookupArgs, hv0n, hnn]
  have hmcallR : memEvalProgFunc vecGrowProg F' stdVecReserveFunc
      [.stdVecOwned ⟨[], false⟩ 0 0, .u64 (BitVec.ofNat 64 10)] =
      stdVecReserveFwd ⟨[], false⟩ 0 0 (BitVec.ofNat 64 10) :=
    memEvalProgFunc_stdVecReserve F' _ 0 0 _ rfl (by decide)
      (Nat.zero_le _) (by decide) (by decide) (by omega)
  have hmcallR' : memEvalProgFunc vecGrowProg F' stdVecReserveFunc
      [.stdVecOwned ⟨[], false⟩ 0 0, .u64 (BitVec.ofNat 64 10)] =
      .ok (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10) := by
    rw [hmcallR, vecReserveStep_eq]
  have hmstepV1 : memEvalProgStmt vecGrowProg (F' + 1)
      (.callProg "v1" stdVecReserveName ["v0", "n"])
      (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10))) emptyMem [] =
      .ok ((envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10),
        emptyMem, []), .fellThrough) :=
    memEvalProgStmt_callProg_ok vecGrowProg F' "v1"
      stdVecReserveName ["v0", "n"] _ emptyMem [] _ stdVecReserveFunc
      (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)
      hargsR findFunc_stdVecReserve hmcallR'
  -- Step 4: `c0 = 1`.
  have hlitC0 : evalExpr (.lit (.i32 (BitVec.ofNat 32 1)))
      (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)) =
      .ok (.i32 (BitVec.ofNat 32 1)) := by
    simp [evalExpr, litVal]
  have hmstepC0 : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "c0" (.i 32) (.lit (.i32 (BitVec.ofNat 32 1))))
      (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
      emptyMem [] =
      .ok ((envExtend (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)), emptyMem, []),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h)
      (memEvalExpr_lit _ _ _ _) hlitC0
  -- Step 5: first push.
  have hv1 : envLookup
      (envExtend (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1))) "v1" =
      some (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10) := by
    simp [envLookup, envExtend,
      show ("v1" : String) ≠ "c0" by decide]
  have hc0 : envLookup
      (envExtend (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1))) "c0" =
      some (.i32 (BitVec.ofNat 32 1)) := by
    simp [envLookup, envExtend]
  have hargsP1 : lookupArgs
      (envExtend (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1))) ["v1", "c0"] =
      some [.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10,
        .i32 (BitVec.ofNat 32 1)] := by
    simp only [lookupArgs, hv1, hc0]
  have hmcallP1 : memEvalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10,
        .i32 (BitVec.ofNat 32 1)] =
      stdVecPushBackFwd ⟨List.replicate 10 0, false⟩ 0 10
        (BitVec.ofNat 32 1) :=
    memEvalProgFunc_stdVecPushBack F' _ 0 10 _ rfl (by decide)
      (Nat.zero_le _) (by decide) (by decide) (by omega)
  have hmcallP1' : memEvalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10,
        .i32 (BitVec.ofNat 32 1)] =
      .ok (.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10) := by
    rw [hmcallP1, vecReservePush1_eq]
  have hmstepV2 : memEvalProgStmt vecGrowProg (F' + 1)
      (.callProg "v2" stdVecPushBackName ["v1", "c0"])
      (envExtend (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1))) emptyMem [] =
      .ok ((envExtend (envExtend (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10),
        emptyMem, []), .fellThrough) :=
    memEvalProgStmt_callProg_ok vecGrowProg F' "v2"
      stdVecPushBackName ["v1", "c0"] _ emptyMem [] _ stdVecPushBackFunc
      (.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10)
      hargsP1 findFunc_stdVecPushBack hmcallP1'
  -- Step 6: `c1 = 2`.
  have hlitC1 : evalExpr (.lit (.i32 (BitVec.ofNat 32 2)))
      (envExtend (envExtend (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10)) =
      .ok (.i32 (BitVec.ofNat 32 2)) := by
    simp [evalExpr, litVal]
  have hmstepC1 : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "c1" (.i 32) (.lit (.i32 (BitVec.ofNat 32 2))))
      (envExtend (envExtend (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
      emptyMem [] =
      .ok ((envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)), emptyMem, []),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h)
      (memEvalExpr_lit _ _ _ _) hlitC1
  -- Step 7: second push.
  have hv2 : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2))) "v2" =
      some (.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10) := by
    simp [envLookup, envExtend,
      show ("v2" : String) ≠ "c1" by decide]
  have hc1 : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2))) "c1" =
      some (.i32 (BitVec.ofNat 32 2)) := by
    simp [envLookup, envExtend]
  have hargsP2 : lookupArgs
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2))) ["v2", "c1"] =
      some [.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10,
        .i32 (BitVec.ofNat 32 2)] := by
    simp only [lookupArgs, hv2, hc1]
  have hmcallP2 : memEvalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10,
        .i32 (BitVec.ofNat 32 2)] =
      stdVecPushBackFwd
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10
        (BitVec.ofNat 32 2) :=
    memEvalProgFunc_stdVecPushBack F' _ 1 10 _ rfl (by decide)
      (by decide) (by decide) (by decide) (by omega)
  have hmcallP2' : memEvalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10,
        .i32 (BitVec.ofNat 32 2)] =
      .ok (.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10) := by
    rw [hmcallP2, vecReservePush2_eq]
  have hmstepV3 : memEvalProgStmt vecGrowProg (F' + 1)
      (.callProg "v3" stdVecPushBackName ["v2", "c1"])
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2))) emptyMem [] =
      .ok ((envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10),
        emptyMem, []), .fellThrough) :=
    memEvalProgStmt_callProg_ok vecGrowProg F' "v3"
      stdVecPushBackName ["v2", "c1"] _ emptyMem [] _ stdVecPushBackFunc
      (.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10)
      hargsP2 findFunc_stdVecPushBack hmcallP2'
  -- Step 8: `n0 = 0`.
  have hlitN0 : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10)) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  have hmstepN0 : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "n0" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
      emptyMem [] =
      .ok ((envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
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
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0))) "v3" =
      some (.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10) := by
    simp [envLookup, envExtend,
      show ("v3" : String) ≠ "n0" by decide]
  have hn0 : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0))) "n0" =
      some (.u64 (BitVec.ofNat 64 0)) := by
    simp [envLookup, envExtend]
  have hargsE0 : lookupArgs
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0))) ["v3", "n0"] =
      some [.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10,
        .u64 (BitVec.ofNat 64 0)] := by
    simp only [lookupArgs, hv3n, hn0]
  have hget0 : (((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
      (BitVec.ofNat 32 2))[(BitVec.ofNat 64 0).toNat]? =
      some (BitVec.ofNat 32 1) := by decide
  have hlt0 : (BitVec.ofNat 64 0).toNat < 2 := by decide
  have hmcallE0 : memEvalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10,
        .u64 (BitVec.ofNat 64 0)] =
      stdVecGrowIndexFwd
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2
        (BitVec.ofNat 64 0) :=
    memEvalFuncFuel_stdVecGrowIndex _ _ 2 10 _ rfl _ hget0 hlt0
  have hmcallE0' : memEvalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10,
        .u64 (BitVec.ofNat 64 0)] =
      .ok (.i32 (BitVec.ofNat 32 1)) := by
    rw [hmcallE0, vecReserveRead0_eq]
  have hmstepE0 : memEvalProgStmt vecGrowProg (F' + 1)
      (.callRet "e0" stdVecGrowIndexName ["v3", "n0"])
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0))) emptyMem [] =
      .ok ((envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
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
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1))) =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have hmstepN1 : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "n1" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
      emptyMem [] =
      .ok ((envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
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
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1))) "v3" =
      some (.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10) := by
    simp [envLookup, envExtend,
      show ("v3" : String) ≠ "n1" by decide,
      show ("v3" : String) ≠ "e0" by decide,
      show ("v3" : String) ≠ "n0" by decide]
  have hn1 : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1))) "n1" =
      some (.u64 (BitVec.ofNat 64 1)) := by
    simp [envLookup, envExtend]
  have hargsE1 : lookupArgs
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1))) ["v3", "n1"] =
      some [.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10,
        .u64 (BitVec.ofNat 64 1)] := by
    simp only [lookupArgs, hv3n1, hn1]
  have hget1 : (((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
      (BitVec.ofNat 32 2))[(BitVec.ofNat 64 1).toNat]? =
      some (BitVec.ofNat 32 2) := by decide
  have hlt1 : (BitVec.ofNat 64 1).toNat < 2 := by decide
  have hmcallE1 : memEvalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10,
        .u64 (BitVec.ofNat 64 1)] =
      stdVecGrowIndexFwd
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2
        (BitVec.ofNat 64 1) :=
    memEvalFuncFuel_stdVecGrowIndex _ _ 2 10 _ rfl _ hget1 hlt1
  have hmcallE1' : memEvalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10,
        .u64 (BitVec.ofNat 64 1)] =
      .ok (.i32 (BitVec.ofNat 32 2)) := by
    rw [hmcallE1, vecReserveRead1_eq]
  have hmstepE1 : memEvalProgStmt vecGrowProg (F' + 1)
      (.callRet "e1" stdVecGrowIndexName ["v3", "n1"])
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1))) emptyMem [] =
      .ok ((envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1)))
        "e1" (.i32 (BitVec.ofNat 32 2)), emptyMem, []),
        .fellThrough) :=
    memEvalProgStmt_callRet_ok vecGrowProg (F' + 1) "e1"
      stdVecGrowIndexName ["v3", "n1"] _ emptyMem [] _
      stdVecGrowIndexFunc (.i32 (BitVec.ofNat 32 2))
      hargsE1 findFunc_stdVecGrowIndex hmcallE1'
  -- Step 12: `s = e0 + e1`.
  have he0 : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1)))
        "e1" (.i32 (BitVec.ofNat 32 2))) "e0" =
      some (.i32 (BitVec.ofNat 32 1)) := by
    simp [envLookup, envExtend,
      show ("e0" : String) ≠ "e1" by decide,
      show ("e0" : String) ≠ "n1" by decide]
  have he1 : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1)))
        "e1" (.i32 (BitVec.ofNat 32 2))) "e1" =
      some (.i32 (BitVec.ofNat 32 2)) := by
    simp [envLookup, envExtend]
  have hsE : evalExpr (.add (.var "e0") (.var "e1"))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1)))
        "e1" (.i32 (BitVec.ofNat 32 2))) =
      .ok (.i32 (BitVec.ofNat 32 3)) := by
    cir_step evalExpr [he0, he1, vecReserveAdd_eq]
  have hmagreeS : memEvalExpr (.add (.var "e0") (.var "e1"))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1)))
        "e1" (.i32 (BitVec.ofNat 32 2))) emptyMem [] =
      evalExpr (.add (.var "e0") (.var "e1"))
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend (envExtend (envExtend
            (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
          "n" (.u64 (BitVec.ofNat 64 10)))
          "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v2" (.stdVecOwned
            ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v3" (.stdVecOwned
            ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 2), false⟩ 2 10))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2))) := by
    simp only [memEvalExpr, evalExpr, he0, he1]
  have hmstepS : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "s" (.i 32) (.add (.var "e0") (.var "e1")))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1)))
        "e1" (.i32 (BitVec.ofNat 32 2)))
      emptyMem [] =
      .ok ((envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1)))
        "e1" (.i32 (BitVec.ofNat 32 2)))
        "s" (.i32 (BitVec.ofNat 32 3)), emptyMem, []),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (by intro se h; cases h) (by intro se h; cases h)
      (by intro ce h; cases h)
      hmagreeS hsE
  -- Step 13: the destructor.
  have hv3d : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1)))
        "e1" (.i32 (BitVec.ofNat 32 2)))
        "s" (.i32 (BitVec.ofNat 32 3))) "v3" =
      some (.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10) := by
    simp [envLookup, envExtend,
      show ("v3" : String) ≠ "s" by decide,
      show ("v3" : String) ≠ "e1" by decide,
      show ("v3" : String) ≠ "n1" by decide,
      show ("v3" : String) ≠ "e0" by decide,
      show ("v3" : String) ≠ "n0" by decide]
  have hargsD : lookupArgs
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1)))
        "e1" (.i32 (BitVec.ofNat 32 2)))
        "s" (.i32 (BitVec.ofNat 32 3))) ["v3"] =
      some [.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10] := by
    simp only [lookupArgs, hv3d]
  have hmcallD : memEvalFuncFuel (F' + 1) stdVecDtorFunc
      [.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10] =
      stdVecDtorFwd
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10 :=
    memEvalFuncFuel_stdVecDtor _ _ 2 10 (by decide) rfl
  have hmcallD' : memEvalFuncFuel (F' + 1) stdVecDtorFunc
      [.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10] =
      .ok (.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), true⟩ 2 10) := by
    rw [hmcallD, vecReserveDtor_eq]
  have hmstepV4 : memEvalProgStmt vecGrowProg (F' + 1)
      (.callRet "v4" stdVecDtorName ["v3"])
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1)))
        "e1" (.i32 (BitVec.ofNat 32 2)))
        "s" (.i32 (BitVec.ofNat 32 3)))
      emptyMem [] =
      .ok ((envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend [] "v0"
            (.stdVecOwned ⟨[], false⟩ 0 0))
          "n" (.u64 (BitVec.ofNat 64 10)))
          "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v2" (.stdVecOwned
            ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v3" (.stdVecOwned
            ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 2), false⟩ 2 10))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "s" (.i32 (BitVec.ofNat 32 3)))
          "v4" (.stdVecOwned
            ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 2), true⟩ 2 10), emptyMem, []),
        .fellThrough) :=
    memEvalProgStmt_callRet_ok vecGrowProg (F' + 1) "v4"
      stdVecDtorName ["v3"] _ emptyMem [] _
      stdVecDtorFunc (.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), true⟩ 2 10)
      hargsD findFunc_stdVecDtor hmcallD'
  -- Return `s = 3`.
  have hrE : evalExpr (.var "s")
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend [] "v0"
            (.stdVecOwned ⟨[], false⟩ 0 0))
          "n" (.u64 (BitVec.ofNat 64 10)))
          "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v2" (.stdVecOwned
            ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v3" (.stdVecOwned
            ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 2), false⟩ 2 10))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "s" (.i32 (BitVec.ofNat 32 3)))
          "v4" (.stdVecOwned
            ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 2), true⟩ 2 10)) =
      .ok (.i32 (BitVec.ofNat 32 3)) := by
    simp [evalExpr, envLookup, envExtend]
  have hrmem : memEvalExpr (.var "s")
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend [] "v0"
            (.stdVecOwned ⟨[], false⟩ 0 0))
          "n" (.u64 (BitVec.ofNat 64 10)))
          "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v2" (.stdVecOwned
            ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v3" (.stdVecOwned
            ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 2), false⟩ 2 10))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "s" (.i32 (BitVec.ofNat 32 3)))
          "v4" (.stdVecOwned
            ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 2), true⟩ 2 10))
      emptyMem [] =
      .ok (.i32 (BitVec.ofNat 32 3)) := by
    rw [memEvalExpr_var]; exact hrE
  have hmret : memEvalProgStmt vecGrowProg (F' + 1)
      (.return_ (.var "s"))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend [] "v0"
            (.stdVecOwned ⟨[], false⟩ 0 0))
          "n" (.u64 (BitVec.ofNat 64 10)))
          "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v2" (.stdVecOwned
            ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v3" (.stdVecOwned
            ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 2), false⟩ 2 10))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "s" (.i32 (BitVec.ofNat 32 3)))
          "v4" (.stdVecOwned
            ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 2), true⟩ 2 10))
      emptyMem [] =
      .ok (((envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend [] "v0"
            (.stdVecOwned ⟨[], false⟩ 0 0))
          "n" (.u64 (BitVec.ofNat 64 10)))
          "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
          "c0" (.i32 (BitVec.ofNat 32 1)))
          "v2" (.stdVecOwned
            ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10))
          "c1" (.i32 (BitVec.ofNat 32 2)))
          "v3" (.stdVecOwned
            ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 2), false⟩ 2 10))
          "n0" (.u64 (BitVec.ofNat 64 0)))
          "e0" (.i32 (BitVec.ofNat 32 1)))
          "n1" (.u64 (BitVec.ofNat 64 1)))
          "e1" (.i32 (BitVec.ofNat 32 2)))
          "s" (.i32 (BitVec.ofNat 32 3)))
          "v4" (.stdVecOwned
            ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 2), true⟩ 2 10)),
        emptyMem, []),
        .returned (.i32 (BitVec.ofNat 32 3))) :=
    memEvalProgStmt_return vecGrowProg (F' + 1) _ _ _ _ _ hrmem
  simp only [memEvalProgFunc, hbind, hbody]
  rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepV0,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepN,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepV1,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepC0,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepV2,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepC1,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepV3,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepN0,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepE0,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepN1,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepE1,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepS,
    memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hmstepV4,
    hmret]
  simp only [vecReserveSumEntryFwd, vecReserveStep_eq, vecReservePush1_eq,
    vecReservePush2_eq, vecReserveRead0_eq, vecReserveRead1_eq,
    vecReserveAdd_eq, vecReserveDtor_eq, vecGrow_bind_ok, vecGrowOwned,
    vecGrowI32]

/-- Transfer for the closed entry: program evaluation over the proved
    composer agrees on both sides (no caller footprint; the empty
    layout from `oracleNoalias_vecReserveSumEntry` suffices). -/
theorem memTransfer_vecReserveSumEntry (F : Nat) (hF : 6 ≤ F)
    (_h : oracleNoalias vecReserveSumEntryFunc []) :
    memEvalProgFunc vecGrowProg F vecReserveSumEntryFunc [] =
      evalProgFunc vecGrowProg F vecReserveSumEntryFunc [] := by
  rw [memEvalProgFunc_vecReserveSumEntry F hF,
    evalProgFunc_vecReserveSumEntry F hF]
