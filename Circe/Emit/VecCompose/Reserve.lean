/-
Circe.Emit.VecCompose.Reserve — N7b `reserve` + `capacity` over the
frozen N4d leaves, plus the closed `vec_reserve_sum` entry.

`capacity` is the `size` twin (`_M_end_of_storage` − `_M_start`
via `ptr_diff` + `s64 → u64` cast, fused into the `vgrowCap`
read).

`reserve(n)` is a guarded composer: the `max_size` throw arm fuses
to `fail` (the `_M_check_len` precedent — the `get_global` +
`array_to_ptrdecay` + `throw_length_error` sites pin the arm
textually); the `capacity < n` arm allocates `n`, relocates the
`len` live words, deallocates the old buffer, and re-pins the
header (`_M_start = tmp`, `_M_finish = tmp + len`,
`_M_end_of_storage = tmp + n`) — a `vgrowSetLen` over the
relocated triple. The pure-read calls (`max_size`, `capacity`,
`size`) inline (`max_size` to the `stdVecMaxDiffBV` const, like
`_M_check_len` inlines its reads); only heap-effect leaves are
`callRet`s (`allocate`, `relocate`, `deallocate`); the
`_M_get_Tp_allocator` call drops (stateless, like `_M_realloc_insert`
drops it). `len` never changes — only the capacity grows.

The `vec_reserve_sum` entry is the closed script: default ctor,
`reserve(10)` via `callProg`, two `push_back`s, two indexed reads,
one `nsw` add, dtor, `trap`-less return of `3`.
-/
import Circe.Emit.Fragment
import Circe.Emit.VecGrow
import Circe.Emit.VecCompose.Base
import Circe.Emit.VecCompose.Realloc
import Circe.Emit.VecCompose.Entry

/-! ## N7b: `capacity` leaf -/

/-- Mangled name of the `capacity` member. -/
def stdVecCapacityName : String :=
  "_ZNKSt6vectorIiSaIiEE8capacityEv"

/-- Canonical CoreIR for `capacity`: the double `_M_impl`
    projection pair (`_M_end_of_storage` + `_M_start` loads) +
    `ptr_diff` + `cast` fused into the `vgrowCap` read (the
    `stdVecSizeFunc` twin). -/
def stdVecGrowCapacityFunc : Func :=
  ⟨stdVecCapacityName,
   [{ name := "t", ty := .vecBlock, role := .owned }],
   .u 64,
   .return_ (.vgrowCap "t")⟩

/-- Value-level forward for `capacity`. -/
def stdVecGrowCapacityFwd (cap : Nat) : Result Value :=
  .ok (.u64 (BitVec.ofNat 64 cap))

/-- Env fact for the `capacity` shape. -/
theorem envLookup_stdVecGrowCapacity_t (b : Vec32) (len cap : Nat) :
    envLookup [("t", .stdVecOwned b len cap)] "t" =
      some (.stdVecOwned b len cap) := by
  simp [envLookup]

/-- `emit_correct` for `capacity` (any fuel). -/
theorem evalFuncFuel_stdVecGrowCapacity (F : Nat) (b : Vec32)
    (len cap : Nat) :
    evalFuncFuel F stdVecGrowCapacityFunc [.stdVecOwned b len cap] =
      stdVecGrowCapacityFwd cap := by
  have hbind : bindArgs stdVecGrowCapacityFunc.args
      [.stdVecOwned b len cap] =
      some [("t", .stdVecOwned b len cap)] := rfl
  have hbody : stdVecGrowCapacityFunc.body =
      .return_ (.vgrowCap "t") := rfl
  have ht := envLookup_stdVecGrowCapacity_t b len cap
  have hcap : evalExpr (.vgrowCap "t") [("t", .stdVecOwned b len cap)] =
      .ok (.u64 (BitVec.ofNat 64 cap)) :=
    evalExpr_vgrowCap_some "t" _ b len cap ht
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, hcap, stdVecGrowCapacityFwd]

/-! ## N7b: `reserve` composer -/

/-- Value-level forward for `reserve`: sequential `Result` binds
    over the frozen leaf forwards (the `stdVecGrowReallocFwd`
    shape — each bind is one composer `callRet`). -/
def stdVecReserveFwd (b : Vec32) (len cap : Nat) (n : BitVec 64) :
    Result Value :=
  if stdVecMaxDiffBV.ult n then .error .AssertFail
  else if (BitVec.ofNat 64 cap).ult n then
    (stdVecAllocFwd n).bind fun alv =>
    (vecGrowOwned alv).bind fun (bNew, lenA, capA) =>
    (stdVecRelocFwd b len cap bNew lenA capA
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 len)
      (BitVec.ofNat 64 0)).bind fun rlv =>
    (vecGrowOwned rlv).bind fun (bR, _lenR, capR) =>
    (stdVecDeallocGuardFwd b len cap
      (BitVec.ofNat 64 cap)).bind fun _ =>
    .ok (.stdVecOwned bR ((BitVec.ofNat 64 len).toNat) capR)
  else .ok (.stdVecOwned b len cap)

/-- `emit_correct` for `reserve`: the program over the frozen b1
    leaves agrees with the composer forward. Caller-side
    preconditions: the old triple is live, the length fits the
    buffer and the capacity (`len ≤ cap`, the vector invariant),
    the capacity is address-bounded, and fuel covers the relocate
    (`len + 1 ≤ F`). -/
theorem evalProgFunc_stdVecReserve (F : Nat) (b : Vec32) (len cap : Nat)
    (n : BitVec 64)
    (hlive : b.freed = false)
    (hlenB : len ≤ b.val.length)
    (hlenC : len ≤ cap)
    (hcap64 : cap < 2 ^ 64)
    (h64 : b.val.length < 2 ^ 64)
    (hfuel : len + 1 ≤ F) :
    evalProgFunc vecGrowProg F stdVecReserveFunc
      [.stdVecOwned b len cap, .u64 n] =
      stdVecReserveFwd b len cap n := by
  have hbind : bindArgs stdVecReserveFunc.args
      [.stdVecOwned b len cap, .u64 n] =
      some [("t", .stdVecOwned b len cap), ("n", .u64 n)] := rfl
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
  by_cases hmax : stdVecMaxDiffBV.ult n = true
  · -- Over `max_size`: the throw arm fails loudly.
    have hcond : evalExpr
          (.ult (.lit (.u64 stdVecMaxDiffBV)) (.var "n"))
          [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
          .ok (.b true) := by
      simp [hmaxEval, hmax]
    have hfail : evalProgStmt vecGrowProg F .fail
          [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
          .error .AssertFail := by
      simp [evalProgStmt, evalStmtFuel_fail]
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_if_true vecGrowProg F _ _ _ _ hcond, hfail]
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
    by_cases hcap : (BitVec.ofNat 64 cap).ult n = true
    · -- Reallocation arm: allocate → relocate → deallocate.
      have hcond2 : evalExpr (.ult (.vgrowCap "t") (.var "n"))
            [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
            .ok (.b true) := by
        simp [hcapEval, hcap]
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
      have hstepZero : evalProgStmt vecGrowProg F
            (.let_ "zero" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
            [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
            .ok (envExtend [("t", .stdVecOwned b len cap),
              ("n", .u64 n)] "zero" (.u64 (BitVec.ofNat 64 0)),
              .fellThrough) := by
        rw [evalProgStmt_let_fb]
        exact evalStmtFuel_let_ _ _ _ _ _ _ hzero
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
      have hstepLenOld : evalProgStmt vecGrowProg F
            (.let_ "lenOld" (.u 64) (.vgrowLen "t")) (envExtend
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            "zero" (.u64 (BitVec.ofNat 64 0))) =
            .ok (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            "zero" (.u64 (BitVec.ofNat 64 0))) "lenOld"
            (.u64 (BitVec.ofNat 64 len)), .fellThrough) := by
        rw [evalProgStmt_let_fb]
        exact evalStmtFuel_let_ _ _ _ _ _ _ hlenOldEval
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
      have hstepCapOld : evalProgStmt vecGrowProg F
            (.let_ "capOld" (.u 64) (.vgrowCap "t")) (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            "zero" (.u64 (BitVec.ofNat 64 0))) "lenOld"
            (.u64 (BitVec.ofNat 64 len))) =
            .ok (envExtend (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            "zero" (.u64 (BitVec.ofNat 64 0))) "lenOld"
            (.u64 (BitVec.ofNat 64 len))) "capOld"
            (.u64 (BitVec.ofNat 64 cap)), .fellThrough) := by
        rw [evalProgStmt_let_fb]
        exact evalStmtFuel_let_ _ _ _ _ _ _ hcapOldEval
      have hal : evalFuncFuel F stdVecAllocFunc [.u64 n] =
          stdVecAllocFwd n :=
        evalFuncFuel_stdVecAlloc F n
      cases halR : stdVecAllocFwd n with
      | error e =>
        have hcallAl' : evalFuncFuel F stdVecAllocFunc [.u64 n] =
            .error e := by
          rw [hal, halR]
        have hargsAl : lookupArgs (envExtend (envExtend (envExtend
              [("t", .stdVecOwned b len cap), ("n", .u64 n)]
              "zero" (.u64 (BitVec.ofNat 64 0))) "lenOld"
              (.u64 (BitVec.ofNat 64 len))) "capOld"
              (.u64 (BitVec.ofNat 64 cap))) ["n"] =
            some [.u64 n] := by
          simp [lookupArgs, envLookup, envExtend]
        have hstepAl := evalProgStmt_callRet_err vecGrowProg F "tA"
          stdVecAllocateName ["n"] _ _ stdVecAllocFunc e
          hargsAl hfindAl hcallAl'
        simp only [evalProgFunc, hbind, hbody]
        rw [evalProgStmt_if_false vecGrowProg F _ _ _ _ hcond, evalProgStmt_if_true vecGrowProg F _ _ _ _ hcond2,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepZero,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepLenOld,
          evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCapOld,
          evalProgStmt_seq_err _ _ _ _ _ _ hstepAl]
        simp only [stdVecReserveFwd, ite_true, ite_false, reduceCtorEq, hmaxF, hcap, halR,
          vecGrow_bind_err, vecGrowOwned]
      | ok v =>
        obtain ⟨bNew, rfl, hNewLive, hNewLen⟩ :=
          stdVecAllocFwd_ok n v hnPos halR
        have hcallAl' : evalFuncFuel F stdVecAllocFunc [.u64 n] =
            .ok (.stdVecOwned bNew 0 n.toNat) := by
          rw [hal, halR]
        have hargsAl : lookupArgs (envExtend (envExtend (envExtend
              [("t", .stdVecOwned b len cap), ("n", .u64 n)]
              "zero" (.u64 (BitVec.ofNat 64 0))) "lenOld"
              (.u64 (BitVec.ofNat 64 len))) "capOld"
              (.u64 (BitVec.ofNat 64 cap))) ["n"] =
            some [.u64 n] := by
          simp [lookupArgs, envLookup, envExtend]
        have hstepAl := evalProgStmt_callRet_ok vecGrowProg F "tA"
          stdVecAllocateName ["n"] _ _ stdVecAllocFunc
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
        have hcallRe : evalFuncFuel F stdVecRelocFunc
              [.stdVecOwned b len cap,
                .stdVecOwned bNew 0 n.toNat,
                .u64 (BitVec.ofNat 64 0),
                .u64 (BitVec.ofNat 64 len),
                .u64 (BitVec.ofNat 64 0)] =
              stdVecRelocFwd b len cap bNew 0 n.toNat
                (BitVec.ofNat 64 0) (BitVec.ofNat 64 len)
                (BitVec.ofNat 64 0) :=
          evalFuncFuel_stdVecReloc F b len cap bNew 0 n.toNat
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
          have hcallRe' : evalFuncFuel F stdVecRelocFunc
                [.stdVecOwned b len cap,
                  .stdVecOwned bNew 0 n.toNat,
                  .u64 (BitVec.ofNat 64 0),
                  .u64 (BitVec.ofNat 64 len),
                  .u64 (BitVec.ofNat 64 0)] = .error e := by
            rw [hcallRe, hr1]
          have hstepRe := evalProgStmt_callRet_err vecGrowProg F "tR"
            stdVecRelocName ["t", "tA", "zero", "lenOld", "zero"] _ _
            stdVecRelocFunc e hargsRe hfindRe hcallRe'
          simp only [evalProgFunc, hbind, hbody]
          rw [evalProgStmt_if_false vecGrowProg F _ _ _ _ hcond, evalProgStmt_if_true vecGrowProg F _ _ _ _ hcond2,
            evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepZero,
            evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepLenOld,
            evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCapOld,
            evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepAl,
            evalProgStmt_seq_err _ _ _ _ _ _ hstepRe]
          simp only [stdVecReserveFwd, ite_true, ite_false, reduceCtorEq, hmaxF, hcap, halR, hr1,
            vecGrow_bind_ok, vecGrow_bind_err, vecGrowOwned]
        | ok v =>
          obtain ⟨bR, rfl, hRlive, hRlen⟩ :=
            stdVecRelocFwd_ok _ _ _ _ _ _ _ _ _ _ hNewLive hr1
          have hcallRe' : evalFuncFuel F stdVecRelocFunc
                [.stdVecOwned b len cap,
                  .stdVecOwned bNew 0 n.toNat,
                  .u64 (BitVec.ofNat 64 0),
                  .u64 (BitVec.ofNat 64 len),
                  .u64 (BitVec.ofNat 64 0)] =
                .ok (.stdVecOwned bR 0 n.toNat) := by
            rw [hcallRe, hr1]
          have hstepRe := evalProgStmt_callRet_ok vecGrowProg F "tR"
            stdVecRelocName ["t", "tA", "zero", "lenOld", "zero"] _ _
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
          have hcallGd : evalFuncFuel F stdVecDeallocGuardFunc
                [.stdVecOwned b len cap,
                  .u64 (BitVec.ofNat 64 cap)] =
                stdVecDeallocGuardFwd b len cap
                  (BitVec.ofNat 64 cap) :=
            evalFuncFuel_stdVecDeallocGuard F b len cap
              (BitVec.ofNat 64 cap)
          cases hgd : stdVecDeallocGuardFwd b len cap
              (BitVec.ofNat 64 cap) with
          | error e =>
            have hcallGd' : evalFuncFuel F stdVecDeallocGuardFunc
                  [.stdVecOwned b len cap,
                    .u64 (BitVec.ofNat 64 cap)] = .error e := by
              rw [hcallGd, hgd]
            have hstepGd := evalProgStmt_callRet_err vecGrowProg F
              "tDead" stdVecDeallocName ["t", "capOld"] _ _
              stdVecDeallocGuardFunc e hargsGd hfindGd hcallGd'
            simp only [evalProgFunc, hbind, hbody]
            rw [evalProgStmt_if_false vecGrowProg F _ _ _ _ hcond, evalProgStmt_if_true vecGrowProg F _ _ _ _ hcond2,
              evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepZero,
              evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepLenOld,
              evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCapOld,
              evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepAl,
              evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepRe,
              evalProgStmt_seq_err _ _ _ _ _ _ hstepGd]
            simp only [stdVecReserveFwd, ite_true, ite_false, reduceCtorEq, hmaxF, hcap, halR, hr1, hgd,
              vecGrow_bind_ok, vecGrow_bind_err, vecGrowOwned]
          | ok v =>
            have hcallGd' : evalFuncFuel F stdVecDeallocGuardFunc
                  [.stdVecOwned b len cap,
                    .u64 (BitVec.ofNat 64 cap)] = .ok v := by
              rw [hcallGd, hgd]
            have hstepGd := evalProgStmt_callRet_ok vecGrowProg F
              "tDead" stdVecDeallocName ["t", "capOld"] _ _
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
            have hret : evalProgStmt vecGrowProg F
                  (.return_ (.vgrowSetLen "tR" (.var "lenOld")))
                  (envExtend (envExtend (envExtend (envExtend
                  (envExtend (envExtend
                  [("t", .stdVecOwned b len cap), ("n", .u64 n)]
                  "zero" (.u64 (BitVec.ofNat 64 0))) "lenOld"
                  (.u64 (BitVec.ofNat 64 len))) "capOld"
                  (.u64 (BitVec.ofNat 64 cap))) "tA"
                  (.stdVecOwned bNew 0 n.toNat)) "tR"
                  (.stdVecOwned bR 0 n.toNat)) "tDead" v) =
                  .ok (envExtend (envExtend (envExtend (envExtend
                  (envExtend (envExtend
                  [("t", .stdVecOwned b len cap), ("n", .u64 n)]
                  "zero" (.u64 (BitVec.ofNat 64 0))) "lenOld"
                  (.u64 (BitVec.ofNat 64 len))) "capOld"
                  (.u64 (BitVec.ofNat 64 cap))) "tA"
                  (.stdVecOwned bNew 0 n.toNat)) "tR"
                  (.stdVecOwned bR 0 n.toNat)) "tDead" v,
                  .returned (.stdVecOwned bR
                    ((BitVec.ofNat 64 len).toNat) n.toNat)) :=
              evalProgStmt_return vecGrowProg F _ _ _ hretEval
            simp only [evalProgFunc, hbind, hbody]
            rw [evalProgStmt_if_false vecGrowProg F _ _ _ _ hcond, evalProgStmt_if_true vecGrowProg F _ _ _ _ hcond2,
              evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepZero,
              evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepLenOld,
              evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCapOld,
              evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepAl,
              evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepRe,
              evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepGd,
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
      have htRet : envLookup [("t", .stdVecOwned b len cap),
            ("n", .u64 n)] "t" =
          some (.stdVecOwned b len cap) := by
        simp [envLookup]
      have hretEval : evalExpr (.var "t")
            [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
            .ok (.stdVecOwned b len cap) := by
        simp [evalExpr, htRet]
      have hret : evalProgStmt vecGrowProg F
            (.return_ (.var "t"))
            [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
            .ok ([("t", .stdVecOwned b len cap), ("n", .u64 n)],
              .returned (.stdVecOwned b len cap)) :=
        evalProgStmt_return vecGrowProg F _ _ _ hretEval
      simp only [evalProgFunc, hbind, hbody]
      rw [evalProgStmt_if_false vecGrowProg F _ _ _ _ hcond,
        evalProgStmt_if_false vecGrowProg F _ _ _ _ hcond2, hret]
      simp [stdVecReserveFwd, hmaxF, hcapF]

/-! ## N7b: `vec_reserve_sum` entry -/

/-- Mangled name of the `vec_reserve_sum` entry. -/
def vecReserveSumEntryName : String := "_Z15vec_reserve_sumv"

/-- Canonical CoreIR for `tests/cpp/vec_reserve_sum.cpp`: default ctor,
    `reserve(10)` via `callProg`, two fast-path `push_back`s, two indexed
    reads, one `nsw` add, dtor, `trap`-less return of `3`. -/
def vecReserveSumEntryFunc : Func :=
  ⟨vecReserveSumEntryName, [], .i 32,
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
     (.return_ (.var "s"))))))))))))))⟩

/-- Value-level forward for `vec_reserve_sum`: `reserve(10)` over the
    empty triple (reallocation arm, zero words relocated), two fast-path
    pushes, two indexed reads, `checkedAddI32`, destructor, return `3`. -/
def vecReserveSumEntryFwd : Result Value :=
  (stdVecReserveFwd ⟨[], false⟩ 0 0 (BitVec.ofNat 64 10)).bind fun v1 =>
  (vecGrowOwned v1).bind fun (b1, l1, c1) =>
  (stdVecPushBackFwd b1 l1 c1 (BitVec.ofNat 32 1)).bind fun v2 =>
  (vecGrowOwned v2).bind fun (b2, l2, c2) =>
  (stdVecPushBackFwd b2 l2 c2 (BitVec.ofNat 32 2)).bind fun v3 =>
  (vecGrowOwned v3).bind fun (b3, l3, c3) =>
  (stdVecGrowIndexFwd b3 l3 (BitVec.ofNat 64 0)).bind fun e0v =>
  (vecGrowI32 e0v).bind fun e0 =>
  (stdVecGrowIndexFwd b3 l3 (BitVec.ofNat 64 1)).bind fun e1v =>
  (vecGrowI32 e1v).bind fun e1 =>
  (checkedAddI32 e0 e1).bind fun s =>
  (stdVecDtorFwd b3 l3 c3).bind fun _ =>
  .ok (.i32 s)

/-- `findFunc` resolves the `reserve` callee in the grown program
    (now trailing the list, after the destructor). -/
theorem findFunc_stdVecReserve :
    findFunc vecGrowProg stdVecReserveName =
      some stdVecReserveFunc := by
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
    findFunc_miss _ _ _ (by decide),
    findFunc_miss _ _ _ (by decide)]
  exact findFunc_hit _ _

/-- The `reserve(10)` step computes the ten-word spare triple
    (reallocation arm over the empty buffer, nothing relocated). -/
theorem vecReserveStep_eq :
    stdVecReserveFwd ⟨[], false⟩ 0 0 (BitVec.ofNat 64 10) =
      .ok (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10) := rfl

/-- First fast-path push writes index `0` of the spare triple. -/
theorem vecReservePush1_eq :
    stdVecPushBackFwd ⟨List.replicate 10 0, false⟩ 0 10
      (BitVec.ofNat 32 1) =
      .ok (.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10) :=
  rfl

/-- Second fast-path push writes index `1`. -/
theorem vecReservePush2_eq :
    stdVecPushBackFwd
      ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10
      (BitVec.ofNat 32 2) =
      .ok (.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10) := rfl

/-- Indexed reads pin the two pushed words. -/
theorem vecReserveRead0_eq :
    stdVecGrowIndexFwd
      ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
        (BitVec.ofNat 32 2), false⟩ 2 (BitVec.ofNat 64 0) =
      .ok (.i32 (BitVec.ofNat 32 1)) := rfl

/-- Indexed reads pin the two pushed words. -/
theorem vecReserveRead1_eq :
    stdVecGrowIndexFwd
      ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
        (BitVec.ofNat 32 2), false⟩ 2 (BitVec.ofNat 64 1) =
      .ok (.i32 (BitVec.ofNat 32 2)) := rfl

/-- The `nsw` add computes `3`. -/
theorem vecReserveAdd_eq :
    checkedAddI32 (BitVec.ofNat 32 1) (BitVec.ofNat 32 2) =
      .ok (BitVec.ofNat 32 3) := rfl

/-- The destructor frees the ten-word triple. -/
theorem vecReserveDtor_eq :
    stdVecDtorFwd
      ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
        (BitVec.ofNat 32 2), false⟩ 2 10 =
      .ok (.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), true⟩ 2 10) := rfl

set_option maxRecDepth 8192 in
/-- `emit_correct` for `vec_reserve_sum`: the closed entry over the
    grown program agrees with the compute-to-`3` forward. Fuel covers
    the three sequential `callProg` depths (`6 ≤ F`). -/
theorem evalProgFunc_vecReserveSumEntry (F : Nat) (hF : 6 ≤ F) :
    evalProgFunc vecGrowProg F vecReserveSumEntryFunc [] =
      vecReserveSumEntryFwd := by
  obtain ⟨F', rfl, hF'⟩ := fuel_step_down 5 hF
  have hbind : bindArgs vecReserveSumEntryFunc.args [] = some [] := rfl
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
  have hcall0 : evalFuncFuel (F' + 1) stdVecEmptyCtorFunc [] =
      .ok (.stdVecOwned ⟨[], false⟩ 0 0) :=
    evalFuncFuel_stdVecEmptyCtor _
  have hstepV0 := evalProgStmt_callRet_ok vecGrowProg (F' + 1) "v0"
    stdVecCtorName [] ([] : Env) _ stdVecEmptyCtorFunc
    (.stdVecOwned ⟨[], false⟩ 0 0)
    hargs0 findFunc_stdVecEmptyCtor hcall0
  -- Step 2: `n = 10`.
  have hlitN : evalExpr (.lit (.u64 (BitVec.ofNat 64 10)))
      (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0)) =
      .ok (.u64 (BitVec.ofNat 64 10)) := by
    simp [evalExpr, litVal]
  have hstepN : evalProgStmt vecGrowProg (F' + 1)
      (.let_ "n" (.u 64) (.lit (.u64 (BitVec.ofNat 64 10))))
      (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0)) =
      .ok (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)), .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hlitN
  -- Step 3: `reserve(10)` takes the reallocation arm over the empty
  -- triple (zero words relocated, ten-word spare buffer).
  have hv0 : envLookup
      (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10))) "v0" =
      some (.stdVecOwned ⟨[], false⟩ 0 0) := by
    simp [envLookup, envExtend,
      show ("v0" : String) ≠ "n" by decide]
  have hn : envLookup
      (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10))) "n" =
      some (.u64 (BitVec.ofNat 64 10)) := by
    simp [envLookup, envExtend]
  have hargsR : lookupArgs
      (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10))) ["v0", "n"] =
      some [.stdVecOwned ⟨[], false⟩ 0 0,
        .u64 (BitVec.ofNat 64 10)] := by
    simp only [lookupArgs, hv0, hn]
  have hcallR : evalProgFunc vecGrowProg F' stdVecReserveFunc
      [.stdVecOwned ⟨[], false⟩ 0 0, .u64 (BitVec.ofNat 64 10)] =
      stdVecReserveFwd ⟨[], false⟩ 0 0 (BitVec.ofNat 64 10) :=
    evalProgFunc_stdVecReserve F' _ 0 0 _ rfl (by decide)
      (Nat.zero_le _) (by decide) (by decide) (by omega)
  have hcallR' : evalProgFunc vecGrowProg F' stdVecReserveFunc
      [.stdVecOwned ⟨[], false⟩ 0 0, .u64 (BitVec.ofNat 64 10)] =
      .ok (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10) := by
    rw [hcallR, vecReserveStep_eq]
  have hstepV1 := evalProgStmt_callProg_ok vecGrowProg F' "v1"
    stdVecReserveName ["v0", "n"] _ _ stdVecReserveFunc
    (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)
    hargsR findFunc_stdVecReserve hcallR'
  -- Step 4: `c0 = 1`.
  have hlitC0 : evalExpr (.lit (.i32 (BitVec.ofNat 32 1)))
      (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)) =
      .ok (.i32 (BitVec.ofNat 32 1)) := by
    simp [evalExpr, litVal]
  have hstepC0 : evalProgStmt vecGrowProg (F' + 1)
      (.let_ "c0" (.i 32) (.lit (.i32 (BitVec.ofNat 32 1))))
      (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)) =
      .ok (envExtend (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)), .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hlitC0
  -- Step 5: first push (fast path into the spare triple).
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
  have hargs1 : lookupArgs
      (envExtend (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1))) ["v1", "c0"] =
      some [.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10,
        .i32 (BitVec.ofNat 32 1)] := by
    simp only [lookupArgs, hv1, hc0]
  have hcallP1 : evalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10,
        .i32 (BitVec.ofNat 32 1)] =
      stdVecPushBackFwd ⟨List.replicate 10 0, false⟩ 0 10
        (BitVec.ofNat 32 1) :=
    evalProgFunc_stdVecPushBack F' _ 0 10 _ rfl (by decide)
      (by decide) (by decide) (by decide) (by omega)
  have hcallP1' : evalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10,
        .i32 (BitVec.ofNat 32 1)] =
      .ok (.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10) := by
    rw [hcallP1, vecReservePush1_eq]
  have hstepV2 := evalProgStmt_callProg_ok vecGrowProg F' "v2"
    stdVecPushBackName ["v1", "c0"] _ _ stdVecPushBackFunc
    (.stdVecOwned
      ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10)
    hargs1 findFunc_stdVecPushBack hcallP1'
  -- Step 6: `c1 = 2`.
  have hlitC1 : evalExpr (.lit (.i32 (BitVec.ofNat 32 2)))
      (envExtend (envExtend (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)) =
      .ok (.i32 (BitVec.ofNat 32 2)) := by
    simp [evalExpr, litVal]
  have hstepC1 : evalProgStmt vecGrowProg (F' + 1)
      (.let_ "c1" (.i 32) (.lit (.i32 (BitVec.ofNat 32 2))))
      (envExtend (envExtend (envExtend (envExtend (envExtend [] "v0"
        (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)) =
      .ok (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)), .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hlitC1
  -- Step 7: second push.
  have hv2 : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))
        "c1" (.i32 (BitVec.ofNat 32 2))) "v2" =
      some (.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
        1 10) := by
    simp [envLookup, envExtend,
      show ("v2" : String) ≠ "c1" by decide]
  have hc1 : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))
        "c1" (.i32 (BitVec.ofNat 32 2))) "c1" =
      some (.i32 (BitVec.ofNat 32 2)) := by
    simp [envLookup, envExtend]
  have hargs2 : lookupArgs
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))
        "c1" (.i32 (BitVec.ofNat 32 2))) ["v2", "c1"] =
      some [.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
        1 10,
        .i32 (BitVec.ofNat 32 2)] := by
    simp only [lookupArgs, hv2, hc1]
  have hcallP2 : evalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
        1 10,
        .i32 (BitVec.ofNat 32 2)] =
      stdVecPushBackFwd
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
        1 10 (BitVec.ofNat 32 2) :=
    evalProgFunc_stdVecPushBack F' _ 1 10 _ rfl (by decide)
      (by decide) (by decide) (by decide) (by omega)
  have hcallP2' : evalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
        1 10,
        .i32 (BitVec.ofNat 32 2)] =
      .ok (.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10) := by
    rw [hcallP2, vecReservePush2_eq]
  have hstepV3 := evalProgStmt_callProg_ok vecGrowProg F' "v3"
    stdVecPushBackName ["v2", "c1"] _ _ stdVecPushBackFunc
    (.stdVecOwned
      ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
        (BitVec.ofNat 32 2), false⟩ 2 10)
    hargs2 findFunc_stdVecPushBack hcallP2'
  -- Step 8: `n0 = 0`.
  have hlitN0 : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10)) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  have hstepN0 : evalProgStmt vecGrowProg (F' + 1)
      (.let_ "n0" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10)) =
      .ok (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0)), .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hlitN0
  -- Step 9: first read pins `1`.
  have hv3n : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))
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
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))
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
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))
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
  have hget0 : ((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
      (BitVec.ofNat 32 2))[(BitVec.ofNat 64 0).toNat]? =
      some (BitVec.ofNat 32 1)) := by decide
  have hlt0 : (BitVec.ofNat 64 0).toNat < 2 := by decide
  have hcallE0 : evalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10,
        .u64 (BitVec.ofNat 64 0)] =
      stdVecGrowIndexFwd
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2
        (BitVec.ofNat 64 0) :=
    evalFuncFuel_stdVecGrowIndex _ _ 2 10 _ rfl _ hget0 hlt0
  have hcallE0' : evalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10,
        .u64 (BitVec.ofNat 64 0)] =
      .ok (.i32 (BitVec.ofNat 32 1)) := by
    rw [hcallE0, vecReserveRead0_eq]
  have hstepE0 := evalProgStmt_callRet_ok vecGrowProg (F' + 1) "e0"
    stdVecGrowIndexName ["v3", "n0"] _ _ stdVecGrowIndexFunc
    (.i32 (BitVec.ofNat 32 1))
    hargsE0 findFunc_stdVecGrowIndex hcallE0'
  -- Step 10: `n1 = 1`.
  have hlitN1 : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1))) =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have hstepN1 : evalProgStmt vecGrowProg (F' + 1)
      (.let_ "n1" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1))) =
      .ok (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1)), .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hlitN1
  -- Step 11: second read pins `2`.
  have hv3n1 : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend [] "v0"
          (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))
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
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))
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
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))
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
  have hget1 : ((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
      (BitVec.ofNat 32 2))[(BitVec.ofNat 64 1).toNat]? =
      some (BitVec.ofNat 32 2)) := by decide
  have hlt1 : (BitVec.ofNat 64 1).toNat < 2 := by decide
  have hcallE1 : evalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10,
        .u64 (BitVec.ofNat 64 1)] =
      stdVecGrowIndexFwd
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2
        (BitVec.ofNat 64 1) :=
    evalFuncFuel_stdVecGrowIndex _ _ 2 10 _ rfl _ hget1 hlt1
  have hcallE1' : evalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10,
        .u64 (BitVec.ofNat 64 1)] =
      .ok (.i32 (BitVec.ofNat 32 2)) := by
    rw [hcallE1, vecReserveRead1_eq]
  have hstepE1 := evalProgStmt_callRet_ok vecGrowProg (F' + 1) "e1"
    stdVecGrowIndexName ["v3", "n1"] _ _ stdVecGrowIndexFunc
    (.i32 (BitVec.ofNat 32 2))
    hargsE1 findFunc_stdVecGrowIndex hcallE1'
  -- Step 12: `s = e0 + e1 = 3`.
  have he0 : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))
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
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))
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
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))
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
  have hstepS : evalProgStmt vecGrowProg (F' + 1)
      (.let_ "s" (.i 32) (.add (.var "e0") (.var "e1")))
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend [] "v0" (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1)))
        "e1" (.i32 (BitVec.ofNat 32 2))) =
      .ok (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend [] "v0"
            (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))
        "c1" (.i32 (BitVec.ofNat 32 2)))
        "v3" (.stdVecOwned
          ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 2), false⟩ 2 10))
        "n0" (.u64 (BitVec.ofNat 64 0)))
        "e0" (.i32 (BitVec.ofNat 32 1)))
        "n1" (.u64 (BitVec.ofNat 64 1)))
        "e1" (.i32 (BitVec.ofNat 32 2)))
        "s" (.i32 (BitVec.ofNat 32 3)), .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hsE
  -- Step 13: destructor frees the triple.
  have hv3d : envLookup
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend [] "v0"
            (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))
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
          (envExtend (envExtend [] "v0"
            (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))
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
  have hcallD : evalFuncFuel (F' + 1) stdVecDtorFunc
      [.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10] =
      stdVecDtorFwd
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10 :=
    evalFuncFuel_stdVecDtor _ _ _ _ (by decide)
  have hcallD' : evalFuncFuel (F' + 1) stdVecDtorFunc
      [.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), false⟩ 2 10] =
      .ok (.stdVecOwned
        ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 2), true⟩ 2 10) := by
    rw [hcallD, vecReserveDtor_eq]
  have hstepV4 := evalProgStmt_callRet_ok vecGrowProg (F' + 1) "v4"
    stdVecDtorName ["v3"] _ _ stdVecDtorFunc
    (.stdVecOwned
      ⟨((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
        (BitVec.ofNat 32 2), true⟩ 2 10)
    hargsD findFunc_stdVecDtor hcallD'
  -- Step 14: return `3`.
  have hrE : evalExpr (.var "s")
      (envExtend (envExtend (envExtend (envExtend (envExtend
        (envExtend (envExtend (envExtend (envExtend (envExtend
          (envExtend (envExtend (envExtend [] "v0"
            (.stdVecOwned ⟨[], false⟩ 0 0))
        "n" (.u64 (BitVec.ofNat 64 10)))
        "v1" (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10))
        "c0" (.i32 (BitVec.ofNat 32 1)))
        "v2" (.stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10))
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
  have hret : evalProgStmt vecGrowProg (F' + 1)
      (.return_ (.var "s")) _ = _ :=
    evalProgStmt_return vecGrowProg (F' + 1) _ _ _ hrE
  simp only [evalProgFunc, hbind, hbody]
  rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepV0,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepN,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepV1,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepC0,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepV2,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepC1,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepV3,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepN0,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepE0,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepN1,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepE1,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepS,
    evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepV4, hret]
  simp only [vecReserveSumEntryFwd, vecReserveStep_eq, vecReservePush1_eq,
    vecReservePush2_eq, vecReserveRead0_eq, vecReserveRead1_eq,
    vecReserveAdd_eq, vecReserveDtor_eq, vecGrow_bind_ok, vecGrowOwned,
    vecGrowI32]
