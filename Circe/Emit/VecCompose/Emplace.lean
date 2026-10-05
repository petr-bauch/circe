/-
Circe.Emit.VecCompose.Emplace — the `emplace_back` composer, the
`push_back` forwarder, and the entry-scoped non-const `operator[]`
leaf, over `Circe.Emit.VecCompose.Realloc`.
-/
import Circe.Emit.Fragment
import Circe.Emit.VecGrow
import Circe.Emit.VecCompose.Realloc

/-! ## N4d-iv-b2: `emplace_back` (fast/slow growth composer) -/

/-- Value-level forward for `emplace_back`: capacity decides. Fast
    (`len ≠ cap`): the frozen construct forward at `len`, length
    `len + 1` (one equation per composer `callRet`, mirroring how
    `stdVecGrowReallocFwd` threads the leaf forwards). Slow
    (`len = cap`): the realloc forward at `pos = len` (the fused
    `end()` value). -/
def stdVecEmplaceBackFwd (b : Vec32) (len cap : Nat) (x : BitVec 32) :
    Result Value :=
  if len == cap then
    stdVecGrowReallocFwd b len cap (BitVec.ofNat 64 len) x
  else
    (stdVecConstructFwd b len cap (BitVec.ofNat 64 len) x).bind fun conv =>
    (vecGrowOwned conv).bind fun (b', _, _) =>
    .ok (.stdVecOwned b' (len + 1) cap)

set_option maxRecDepth 8192 in
/-- `emit_correct` for `emplace_back`: the program over the frozen
    leaves plus the proved realloc composer agrees with the capacity
    dispatch forward. Caller-side preconditions: the old triple is
    live, `len` is below the `length_error` boundary, the element
    lands in the buffer, words fit, and fuel covers the slow path
    (one `callProg` depth plus the realloc relocates). -/
theorem evalProgFunc_stdVecEmplaceBack (F : Nat) (b : Vec32) (len cap : Nat)
    (x : BitVec 32)
    (hlive : b.freed = false)
    (hmax : len ≤ stdVecMaxDiffBV.toNat)
    (hlen : len ≤ b.val.length)
    (h64 : b.val.length < 2 ^ 64)
    (hcap64 : cap < 2 ^ 64)
    (hF : len + 2 ≤ F) :
    evalProgFunc vecGrowProg F stdVecEmplaceBackFunc
      [.stdVecOwned b len cap, .i32 x] =
      stdVecEmplaceBackFwd b len cap x := by
  obtain ⟨F', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : F ≠ 0)
  have hbind : bindArgs stdVecEmplaceBackFunc.args
      [.stdVecOwned b len cap, .i32 x] =
      some [("t", .stdVecOwned b len cap), ("x", .i32 x)] := rfl
  have hbody : stdVecEmplaceBackFunc.body =
      (.seq (.let_ "len" (.u 64) (.vgrowLen "t"))
      (.seq (.let_ "cap" (.u 64) (.vgrowCap "t"))
      (.if_ (.une (.var "len") (.var "cap"))
        (.seq (.callRet "tF" stdVecTraitsConstructName ["t", "len", "x"])
        (.seq (.let_ "len1" (.u 64)
                 (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
              (.return_ (.vgrowSetLen "tF" (.var "len1")))))
        (.seq (.callRet "pos" stdVecEndName ["t"])
        (.seq (.callProg "r" stdVecGrowReallocName ["t", "pos", "x"])
              (.return_ (.var "r"))))))) := rfl
  have hMlt : stdVecMaxDiff < 2 ^ 64 := by decide
  have hMrt : stdVecMaxDiffBV.toNat = stdVecMaxDiff :=
    ofNat64_toNat _ hMlt
  have hM64 : stdVecMaxDiffBV.toNat < 2 ^ 64 := by omega
  have hlen64 : len < 2 ^ 64 := by omega
  have hrt : (BitVec.ofNat 64 len).toNat = len := ofNat64_toNat _ hlen64
  have h1w : (BitVec.ofNat 64 1).toNat = 1 := ofNat64_toNat 1 (by decide)
  have hMv : stdVecMaxDiff = 2305843009213693951 := rfl
  have hlen1lt : len + 1 < 2 ^ 64 := by omega
  have hlen1 : ((BitVec.ofNat 64 len) + (BitVec.ofNat 64 1)).toNat =
      len + 1 := by
    rw [BitVec.toNat_add_of_lt (by rw [hrt, h1w]; exact hlen1lt), hrt, h1w]
  have ht0 : envLookup [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      "t" = some (.stdVecOwned b len cap) := by simp [envLookup]
  have hlenV : evalExpr (.vgrowLen "t")
      [("t", .stdVecOwned b len cap), ("x", .i32 x)] =
      .ok (.u64 (BitVec.ofNat 64 len)) :=
    evalExpr_vgrowLen_some "t" _ b len cap ht0
  have hstepLen : evalProgStmt vecGrowProg (F' + 1)
      (.let_ "len" (.u 64) (.vgrowLen "t"))
      [("t", .stdVecOwned b len cap), ("x", .i32 x)] =
      .ok (envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)]
        "len" (.u64 (BitVec.ofNat 64 len)), .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hlenV
  have ht1 : envLookup (envExtend
      [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      "len" (.u64 (BitVec.ofNat 64 len))) "t" =
      some (.stdVecOwned b len cap) := by
    simp [envLookup, envExtend, show ("t" : String) ≠ "len" by decide]
  have hcapV : evalExpr (.vgrowCap "t") (envExtend
      [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      "len" (.u64 (BitVec.ofNat 64 len))) =
      .ok (.u64 (BitVec.ofNat 64 cap)) :=
    evalExpr_vgrowCap_some "t" _ b len cap ht1
  have hstepCap : evalProgStmt vecGrowProg (F' + 1)
      (.let_ "cap" (.u 64) (.vgrowCap "t"))
      (envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)]
        "len" (.u64 (BitVec.ofNat 64 len))) =
      .ok (envExtend (envExtend
        [("t", .stdVecOwned b len cap), ("x", .i32 x)]
        "len" (.u64 (BitVec.ofNat 64 len)))
        "cap" (.u64 (BitVec.ofNat 64 cap)), .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact evalStmtFuel_let_ _ _ _ _ _ _ hcapV
  have hlen2 : envLookup (envExtend (envExtend
      [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      "len" (.u64 (BitVec.ofNat 64 len)))
      "cap" (.u64 (BitVec.ofNat 64 cap))) "len" =
      some (.u64 (BitVec.ofNat 64 len)) := by
    simp [envLookup, envExtend, show ("len" : String) ≠ "cap" by decide]
  have hcap2 : envLookup (envExtend (envExtend
      [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      "len" (.u64 (BitVec.ofNat 64 len)))
      "cap" (.u64 (BitVec.ofNat 64 cap))) "cap" =
      some (.u64 (BitVec.ofNat 64 cap)) := by
    simp [envLookup, envExtend]
  have ht2 : envLookup (envExtend (envExtend
      [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      "len" (.u64 (BitVec.ofNat 64 len)))
      "cap" (.u64 (BitVec.ofNat 64 cap))) "t" =
      some (.stdVecOwned b len cap) := by
    simp [envLookup, envExtend,
      show ("t" : String) ≠ "cap" by decide,
      show ("t" : String) ≠ "len" by decide]
  have hx2 : envLookup (envExtend (envExtend
      [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      "len" (.u64 (BitVec.ofNat 64 len)))
      "cap" (.u64 (BitVec.ofNat 64 cap))) "x" =
      some (.i32 x) := by
    simp [envLookup, envExtend,
      show ("x" : String) ≠ "cap" by decide,
      show ("x" : String) ≠ "len" by decide]
  have hfindCon : findFunc vecGrowProg stdVecTraitsConstructName =
      some stdVecConstructFunc := by
    unfold vecGrowProg
    rw [findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide)]
    exact findFunc_hit _ _
  have hfindEnd : findFunc vecGrowProg stdVecEndName =
      some stdVecEndFunc := by
    unfold vecGrowProg
    rw [findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide)]
    exact findFunc_hit _ _
  have hfindR : findFunc vecGrowProg stdVecGrowReallocName =
      some stdVecGrowReallocFunc := by
    unfold vecGrowProg
    rw [findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide)]
    exact findFunc_hit _ _
  by_cases hlc : len = cap
  · -- Slow path: `len = cap`, the `end()` position feeds the
    -- realloc composer via `callProg` at depth `F'`.
    have hcond : evalExpr (.une (.var "len") (.var "cap"))
        (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap))) =
        .ok (.b false) := by
      simp [evalExpr, envLookup, envExtend,
        show ("len" : String) ≠ "cap" by decide, hlc]
    have hif : evalProgStmt vecGrowProg (F' + 1)
        (.if_ (.une (.var "len") (.var "cap"))
          (.seq (.callRet "tF" stdVecTraitsConstructName ["t", "len", "x"])
          (.seq (.let_ "len1" (.u 64)
                   (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
                (.return_ (.vgrowSetLen "tF" (.var "len1")))))
          (.seq (.callRet "pos" stdVecEndName ["t"])
          (.seq (.callProg "r" stdVecGrowReallocName ["t", "pos", "x"])
                (.return_ (.var "r")))))
        (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap))) =
        evalProgStmt vecGrowProg (F' + 1)
        (.seq (.callRet "pos" stdVecEndName ["t"])
        (.seq (.callProg "r" stdVecGrowReallocName ["t", "pos", "x"])
              (.return_ (.var "r"))))
        (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap))) :=
      evalProgStmt_if_false vecGrowProg (F' + 1) _ _ _ _ hcond
    have hargsPos : lookupArgs (envExtend (envExtend
        [("t", .stdVecOwned b len cap), ("x", .i32 x)]
        "len" (.u64 (BitVec.ofNat 64 len)))
        "cap" (.u64 (BitVec.ofNat 64 cap))) ["t"] =
        some [.stdVecOwned b len cap] := by
      simp only [lookupArgs, ht2]
    have hcallEnd : evalFuncFuel (F' + 1) stdVecEndFunc
        [.stdVecOwned b len cap] = stdVecEndFwd len :=
      evalFuncFuel_stdVecEnd _ b len cap
    have hcallEnd' : evalFuncFuel (F' + 1) stdVecEndFunc
        [.stdVecOwned b len cap] = .ok (.u64 (BitVec.ofNat 64 len)) := by
      rw [hcallEnd]; rfl
    have hstepPos := evalProgStmt_callRet_ok vecGrowProg (F' + 1) "pos"
      stdVecEndName ["t"] _ _ stdVecEndFunc (.u64 (BitVec.ofNat 64 len))
      hargsPos hfindEnd hcallEnd'
    have ht3 : envLookup (envExtend (envExtend (envExtend
        [("t", .stdVecOwned b len cap), ("x", .i32 x)]
        "len" (.u64 (BitVec.ofNat 64 len)))
        "cap" (.u64 (BitVec.ofNat 64 cap)))
        "pos" (.u64 (BitVec.ofNat 64 len))) "t" =
        some (.stdVecOwned b len cap) := by
      simp [envLookup, envExtend,
        show ("t" : String) ≠ "pos" by decide,
        show ("t" : String) ≠ "cap" by decide,
        show ("t" : String) ≠ "len" by decide]
    have hpos3 : envLookup (envExtend (envExtend (envExtend
        [("t", .stdVecOwned b len cap), ("x", .i32 x)]
        "len" (.u64 (BitVec.ofNat 64 len)))
        "cap" (.u64 (BitVec.ofNat 64 cap)))
        "pos" (.u64 (BitVec.ofNat 64 len))) "pos" =
        some (.u64 (BitVec.ofNat 64 len)) := by
      simp [envLookup, envExtend]
    have hx3 : envLookup (envExtend (envExtend (envExtend
        [("t", .stdVecOwned b len cap), ("x", .i32 x)]
        "len" (.u64 (BitVec.ofNat 64 len)))
        "cap" (.u64 (BitVec.ofNat 64 cap)))
        "pos" (.u64 (BitVec.ofNat 64 len))) "x" =
        some (.i32 x) := by
      simp [envLookup, envExtend,
        show ("x" : String) ≠ "pos" by decide,
        show ("x" : String) ≠ "cap" by decide,
        show ("x" : String) ≠ "len" by decide]
    have hargsR : lookupArgs (envExtend (envExtend (envExtend
        [("t", .stdVecOwned b len cap), ("x", .i32 x)]
        "len" (.u64 (BitVec.ofNat 64 len)))
        "cap" (.u64 (BitVec.ofNat 64 cap)))
        "pos" (.u64 (BitVec.ofNat 64 len))) ["t", "pos", "x"] =
        some [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len),
          .i32 x] := by
      simp only [lookupArgs, ht3, hpos3, hx3]
    have hSlen : (BitVec.ofNat 64 len).toNat ≤ len := Nat.le_of_eq hrt
    have hcallR : evalProgFunc vecGrowProg F' stdVecGrowReallocFunc
        [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len), .i32 x] =
        stdVecGrowReallocFwd b len cap (BitVec.ofNat 64 len) x :=
      evalProgFunc_stdVecGrowRealloc F' b len cap (BitVec.ofNat 64 len) x
        hlive hmax hSlen hlen h64
        (by rw [hrt]; omega) (by rw [hrt]; omega)
    have hFwdSlow : stdVecEmplaceBackFwd b len cap x =
        stdVecGrowReallocFwd b len cap (BitVec.ofNat 64 len) x := by
      unfold stdVecEmplaceBackFwd; simp [hlc]
    cases hR : stdVecGrowReallocFwd b len cap (BitVec.ofNat 64 len) x with
    | error e =>
      have hcallR' : evalProgFunc vecGrowProg F' stdVecGrowReallocFunc
          [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len), .i32 x] =
          .error e := by rw [hcallR, hR]
      have hstepR := evalProgStmt_callProg_err vecGrowProg F' "r"
        stdVecGrowReallocName ["t", "pos", "x"] _ _ stdVecGrowReallocFunc e
        hargsR hfindR hcallR'
      simp only [evalProgFunc, hbind, hbody]
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepLen,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCap,
        hif, evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepPos,
        evalProgStmt_seq_err _ _ _ _ _ _ hstepR]
      simp only [hFwdSlow, hR]
    | ok v =>
      have hcallR' : evalProgFunc vecGrowProg F' stdVecGrowReallocFunc
          [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len), .i32 x] =
          .ok v := by rw [hcallR, hR]
      have hstepR := evalProgStmt_callProg_ok vecGrowProg F' "r"
        stdVecGrowReallocName ["t", "pos", "x"] _ _ stdVecGrowReallocFunc v
        hargsR hfindR hcallR'
      have hrE : evalExpr (.var "r") (envExtend (envExtend (envExtend
          (envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "pos" (.u64 (BitVec.ofNat 64 len))) "r" v) =
          .ok v := by
        simp [evalExpr, envLookup, envExtend]
      have hret : evalProgStmt vecGrowProg (F' + 1)
          (.return_ (.var "r")) (envExtend (envExtend (envExtend
          (envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "pos" (.u64 (BitVec.ofNat 64 len))) "r" v) =
          .ok ((envExtend (envExtend (envExtend
          (envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "pos" (.u64 (BitVec.ofNat 64 len))) "r" v), .returned v) :=
        evalProgStmt_return vecGrowProg (F' + 1) _ _ _ hrE
      simp only [evalProgFunc, hbind, hbody]
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepLen,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCap,
        hif, evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepPos,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepR, hret]
      simp only [hFwdSlow, hR]
  · -- Fast path: `len ≠ cap`, construct at `len`, bump to `len + 1`.
    have hne64 : BitVec.ofNat 64 len ≠ BitVec.ofNat 64 cap := by
      intro hcon
      apply hlc
      have h1 := congrArg BitVec.toNat hcon
      rw [hrt, ofNat64_toNat _ hcap64] at h1
      exact h1
    have hcond : evalExpr (.une (.var "len") (.var "cap"))
        (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap))) =
        .ok (.b true) := by
      simp [evalExpr, envLookup, envExtend,
        show ("len" : String) ≠ "cap" by decide, hne64]
    have hif : evalProgStmt vecGrowProg (F' + 1)
        (.if_ (.une (.var "len") (.var "cap"))
          (.seq (.callRet "tF" stdVecTraitsConstructName ["t", "len", "x"])
          (.seq (.let_ "len1" (.u 64)
                   (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
                (.return_ (.vgrowSetLen "tF" (.var "len1")))))
          (.seq (.callRet "pos" stdVecEndName ["t"])
          (.seq (.callProg "r" stdVecGrowReallocName ["t", "pos", "x"])
                (.return_ (.var "r")))))
        (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap))) =
        evalProgStmt vecGrowProg (F' + 1)
        (.seq (.callRet "tF" stdVecTraitsConstructName ["t", "len", "x"])
        (.seq (.let_ "len1" (.u 64)
                 (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
              (.return_ (.vgrowSetLen "tF" (.var "len1")))))
        (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap))) :=
      evalProgStmt_if_true vecGrowProg (F' + 1) _ _ _ _ hcond
    have hargsCon : lookupArgs (envExtend (envExtend
        [("t", .stdVecOwned b len cap), ("x", .i32 x)]
        "len" (.u64 (BitVec.ofNat 64 len)))
        "cap" (.u64 (BitVec.ofNat 64 cap))) ["t", "len", "x"] =
        some [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len),
          .i32 x] := by
      simp only [lookupArgs, ht2, hlen2, hx2]
    have hcallCon : evalFuncFuel (F' + 1) stdVecConstructFunc
        [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len), .i32 x] =
        stdVecConstructFwd b len cap (BitVec.ofNat 64 len) x :=
      evalFuncFuel_stdVecConstruct (F' + 1) b len cap
        (BitVec.ofNat 64 len) x
    have hFwdFast : stdVecEmplaceBackFwd b len cap x =
        ((stdVecConstructFwd b len cap (BitVec.ofNat 64 len) x).bind
          fun conv =>
        (vecGrowOwned conv).bind fun (b', _, _) =>
        .ok (.stdVecOwned b' (len + 1) cap)) := by
      unfold stdVecEmplaceBackFwd; simp [hlc]
    cases hcon : stdVecConstructFwd b len cap (BitVec.ofNat 64 len) x with
    | error e =>
      have hcallCon' : evalFuncFuel (F' + 1) stdVecConstructFunc
          [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len), .i32 x] =
          .error e := by rw [hcallCon, hcon]
      have hstepCon := evalProgStmt_callRet_err vecGrowProg (F' + 1) "tF"
        stdVecTraitsConstructName ["t", "len", "x"] _ _
        stdVecConstructFunc e hargsCon hfindCon hcallCon'
      simp only [evalProgFunc, hbind, hbody]
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepLen,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCap,
        hif, evalProgStmt_seq_err _ _ _ _ _ _ hstepCon]
      simp only [hFwdFast, hcon, vecGrow_bind_err]
    | ok v =>
      obtain ⟨bC, rfl, hClive, hClen⟩ :=
        stdVecConstructFwd_ok _ _ _ _ _ _ hcon
      have hcallCon' : evalFuncFuel (F' + 1) stdVecConstructFunc
          [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len), .i32 x] =
          .ok (.stdVecOwned bC len cap) := by rw [hcallCon, hcon]
      have hstepCon := evalProgStmt_callRet_ok vecGrowProg (F' + 1) "tF"
        stdVecTraitsConstructName ["t", "len", "x"] _ _
        stdVecConstructFunc (.stdVecOwned bC len cap)
        hargsCon hfindCon hcallCon'
      have hlenF : envLookup (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "tF" (.stdVecOwned bC len cap)) "len" =
          some (.u64 (BitVec.ofNat 64 len)) := by
        simp [envLookup, envExtend,
          show ("len" : String) ≠ "tF" by decide,
          show ("len" : String) ≠ "cap" by decide]
      have hlen1Eval : evalExpr
          (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1))))
          (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "tF" (.stdVecOwned bC len cap)) =
          .ok (.u64 ((BitVec.ofNat 64 len) + (BitVec.ofNat 64 1))) :=
        evalExpr_uadd_u64 _ _ _ _ _
          (evalExpr_var_hit _ _ _ hlenF) rfl
      have hstepLen1 : evalProgStmt vecGrowProg (F' + 1)
          (.let_ "len1" (.u 64)
            (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
          (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "tF" (.stdVecOwned bC len cap)) =
          .ok (envExtend (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "tF" (.stdVecOwned bC len cap))
          "len1" (.u64 ((BitVec.ofNat 64 len) + (BitVec.ofNat 64 1))),
          .fellThrough) := by
        rw [evalProgStmt_let_fb]
        exact evalStmtFuel_let_ _ _ _ _ _ _ hlen1Eval
      have htFret : envLookup (envExtend (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "tF" (.stdVecOwned bC len cap))
          "len1" (.u64 ((BitVec.ofNat 64 len) +
            (BitVec.ofNat 64 1)))) "tF" =
          some (.stdVecOwned bC len cap) := by
        simp [envLookup, envExtend,
          show ("tF" : String) ≠ "len1" by decide]
      have hlen1E : evalExpr (.var "len1") (envExtend (envExtend
          (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "tF" (.stdVecOwned bC len cap))
          "len1" (.u64 ((BitVec.ofNat 64 len) +
            (BitVec.ofNat 64 1)))) =
          .ok (.u64 ((BitVec.ofNat 64 len) + (BitVec.ofNat 64 1))) := by
        simp [evalExpr, envLookup, envExtend]
      have hretEval : evalExpr
          (.vgrowSetLen "tF" (.var "len1")) (envExtend (envExtend
          (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "tF" (.stdVecOwned bC len cap))
          "len1" (.u64 ((BitVec.ofNat 64 len) +
            (BitVec.ofNat 64 1)))) =
          .ok (.stdVecOwned bC (len + 1) cap) := by
        have h0 : evalExpr
            (.vgrowSetLen "tF" (.var "len1")) (envExtend (envExtend
            (envExtend (envExtend
            [("t", .stdVecOwned b len cap), ("x", .i32 x)]
            "len" (.u64 (BitVec.ofNat 64 len)))
            "cap" (.u64 (BitVec.ofNat 64 cap)))
            "tF" (.stdVecOwned bC len cap))
            "len1" (.u64 ((BitVec.ofNat 64 len) +
              (BitVec.ofNat 64 1)))) =
            .ok (.stdVecOwned bC
              (((BitVec.ofNat 64 len) + (BitVec.ofNat 64 1)).toNat) cap) :=
          evalExpr_vgrowSetLen_hit _ _ _ _ _ _ _ htFret hlen1E
        rw [hlen1] at h0; exact h0
      have hret : evalProgStmt vecGrowProg (F' + 1)
          (.return_ (.vgrowSetLen "tF" (.var "len1"))) (envExtend
          (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "tF" (.stdVecOwned bC len cap))
          "len1" (.u64 ((BitVec.ofNat 64 len) +
            (BitVec.ofNat 64 1)))) =
          .ok ((envExtend (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "tF" (.stdVecOwned bC len cap))
          "len1" (.u64 ((BitVec.ofNat 64 len) +
            (BitVec.ofNat 64 1)))),
            .returned (.stdVecOwned bC (len + 1) cap)) :=
        evalProgStmt_return vecGrowProg (F' + 1) _ _ _ hretEval
      simp only [evalProgFunc, hbind, hbody]
      rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepLen,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCap,
        hif, evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCon,
        evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepLen1, hret]
      simp only [hFwdFast, hcon, vecGrow_bind_ok, vecGrowOwned]

/-! ## N4d-iv-b2: `push_back` (forwarder into `emplace_back`) -/

/-- Value-level forward for `push_back`: the `emplace_back` dispatch
    forward (the discarded reference never affects the triple). -/
def stdVecPushBackFwd (b : Vec32) (len cap : Nat) (x : BitVec 32) :
    Result Value :=
  stdVecEmplaceBackFwd b len cap x

/-- `findFunc` resolves the `emplace_back` callee in the grown
    program (standalone, reused by both the value and memory
    forwarder proofs). -/
theorem findFunc_stdVecEmplaceBack :
    findFunc vecGrowProg stdVecEmplaceBackName =
      some stdVecEmplaceBackFunc := by
  unfold vecGrowProg
  rw [findFunc_miss _ _ _ (by decide),
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
/-- `emit_correct` for `push_back`: the single-`callProg` forwarder
    agrees with the `emplace_back` dispatch forward. Caller-side
    preconditions mirror `emplace_back`'s; fuel covers one more
    `callProg` depth (`len + 3 ≤ F`). -/
theorem evalProgFunc_stdVecPushBack (F : Nat) (b : Vec32) (len cap : Nat)
    (x : BitVec 32)
    (hlive : b.freed = false)
    (hmax : len ≤ stdVecMaxDiffBV.toNat)
    (hlen : len ≤ b.val.length)
    (h64 : b.val.length < 2 ^ 64)
    (hcap64 : cap < 2 ^ 64)
    (hF : len + 3 ≤ F) :
    evalProgFunc vecGrowProg F stdVecPushBackFunc
      [.stdVecOwned b len cap, .i32 x] =
      stdVecPushBackFwd b len cap x := by
  obtain ⟨F', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : F ≠ 0)
  have hF' : len + 2 ≤ F' := by omega
  have hbind : bindArgs stdVecPushBackFunc.args
      [.stdVecOwned b len cap, .i32 x] =
      some [("t", .stdVecOwned b len cap), ("x", .i32 x)] := rfl
  have hbody : stdVecPushBackFunc.body =
      (.seq (.callProg "r" stdVecEmplaceBackName ["t", "x"])
        (.return_ (.var "r"))) := rfl
  have hFwd : stdVecPushBackFwd b len cap x =
      stdVecEmplaceBackFwd b len cap x := rfl
  have ht : envLookup [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      "t" = some (.stdVecOwned b len cap) := by simp [envLookup]
  have hx : envLookup [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      "x" = some (.i32 x) := by
    simp [envLookup]
  have hargs : lookupArgs [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      ["t", "x"] = some [.stdVecOwned b len cap, .i32 x] := by
    simp only [lookupArgs, ht, hx]
  have hcall : evalProgFunc vecGrowProg F' stdVecEmplaceBackFunc
      [.stdVecOwned b len cap, .i32 x] =
      stdVecEmplaceBackFwd b len cap x :=
    evalProgFunc_stdVecEmplaceBack F' b len cap x hlive hmax
      hlen h64 hcap64 hF'
  cases hR : stdVecEmplaceBackFwd b len cap x with
  | error e =>
    have hcall' : evalProgFunc vecGrowProg F' stdVecEmplaceBackFunc
        [.stdVecOwned b len cap, .i32 x] = .error e := by rw [hcall, hR]
    have hstepCall := evalProgStmt_callProg_err vecGrowProg F' "r"
      stdVecEmplaceBackName ["t", "x"] _ _ stdVecEmplaceBackFunc e
      hargs findFunc_stdVecEmplaceBack hcall'
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_err _ _ _ _ _ _ hstepCall]
    simp only [hFwd, hR]
  | ok v =>
    have hcall' : evalProgFunc vecGrowProg F' stdVecEmplaceBackFunc
        [.stdVecOwned b len cap, .i32 x] = .ok v := by rw [hcall, hR]
    have hstepCall := evalProgStmt_callProg_ok vecGrowProg F' "r"
      stdVecEmplaceBackName ["t", "x"] _ _ stdVecEmplaceBackFunc v
      hargs findFunc_stdVecEmplaceBack hcall'
    have hrE : evalExpr (.var "r")
        (envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)] "r" v) =
        .ok v := by
      simp [evalExpr, envLookup, envExtend]
    have hret : evalProgStmt vecGrowProg (F' + 1)
        (.return_ (.var "r"))
        (envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)] "r" v) =
        .ok ((envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "r" v), .returned v) :=
      evalProgStmt_return vecGrowProg (F' + 1) _ _ _ hrE
    simp only [evalProgFunc, hbind, hbody]
    rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hstepCall, hret]
    simp only [hFwd, hR]

/-! ## N4d-iv-b2: entry-scoped non-const `operator[]` leaf -/

/-- Value-level forward for the non-const `operator[]`: the word at
    `u64` index `n`, `OOB` at or past the length (mirrors the
    `vgrowAt` evaluator exactly, cf. `stdVecIndexFwd`). -/
def stdVecGrowIndexFwd (b : Vec32) (len : Nat) (n : BitVec 64) :
    Result Value :=
  if b.freed then .error .AssertFail
  else match b.val[n.toNat]? with
  | some x => if n.toNat < len then .ok (.i32 x) else .error .OOB
  | none => .error .OOB

/-- `emit_correct` for the non-const `operator[]` (any fuel; the
    index is in bounds). -/
theorem evalFuncFuel_stdVecGrowIndex (F : Nat) (b : Vec32) (len cap : Nat)
    (n : BitVec 64)
    (hlive : b.freed = false)
    (x : BitVec 32)
    (hget : b.val[n.toNat]? = some x)
    (hlt : n.toNat < len) :
    evalFuncFuel F stdVecGrowIndexFunc [.stdVecOwned b len cap, .u64 n] =
      stdVecGrowIndexFwd b len n := by
  have hbind : bindArgs stdVecGrowIndexFunc.args
      [.stdVecOwned b len cap, .u64 n] =
      some [("t", .stdVecOwned b len cap), ("n", .u64 n)] := rfl
  have hbody : stdVecGrowIndexFunc.body =
      .return_ (.vgrowAt "t" (.var "n")) := rfl
  have ht : envLookup [("t", .stdVecOwned b len cap), ("n", .u64 n)]
      "t" = some (.stdVecOwned b len cap) := by simp [envLookup]
  have hn : envLookup [("t", .stdVecOwned b len cap), ("n", .u64 n)]
      "n" = some (.u64 n) := by
    simp [envLookup]
  have hnV : evalExpr (.var "n")
      [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  have hat : evalExpr (.vgrowAt "t" (.var "n"))
      [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
      .ok (.i32 x) :=
    evalExpr_vgrowAt_some "t" (.var "n") _ b len cap n x ht hnV
      hlive hget hlt
  have hFwd : stdVecGrowIndexFwd b len n = .ok (.i32 x) := by
    simp [stdVecGrowIndexFwd, hlive, hget, hlt]
  cases F <;>
    simp only [evalFuncFuel, hbind, hbody, evalStmtFuel, evalStmtZero,
      evalStmtWith, hat, hFwd]

