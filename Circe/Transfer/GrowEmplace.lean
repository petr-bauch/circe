/-
Circe.Transfer.GrowEmplace — N4d-iv-b2 `emplace_back` / `push_back` transfers, the ix leaf,
and the `let_` memory bridge.
Over `Circe.Transfer.GrowRealloc`.
-/
import Circe.Transfer.GrowRealloc

/-! ## N4d-iv-b2 `emplace_back` composer: memory agreement -/

/-- `memEval` for `emplace_back`: program evaluation over the frozen
    leaves plus the proved realloc composer agrees with the capacity
    dispatch forward (mirrors `evalProgFunc_stdVecEmplaceBack`;
    memory and layout thread through unchanged — the guard lets,
    the `end` position call, and both arms' value steps are pure —
    so the only memory obligations are the two header loads for
    `len` / `cap`). -/
theorem memEvalProgFunc_stdVecEmplaceBack (F : Nat) (b : Vec32)
    (len cap : Nat) (x : BitVec 32)
    (hlive : b.freed = false)
    (hmax : len ≤ stdVecMaxDiffBV.toNat)
    (hlen : len ≤ b.val.length)
    (h64 : b.val.length < 2 ^ 64)
    (hcap64 : cap < 2 ^ 64)
    (hF : len + 2 ≤ F) :
    memEvalProgFunc vecGrowProg F stdVecEmplaceBackFunc
      [.stdVecOwned b len cap, .i32 x] =
      stdVecEmplaceBackFwd b len cap x := by
  obtain ⟨F', rfl, _⟩ := fuel_step_down (len + 1) hF
  have hbind : bindMemArgs stdVecEmplaceBackFunc.args
      [.stdVecOwned b len cap, .i32 x] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("x", .i32 x)],
        tripleMem b len cap, [("t", 0, 0)]) := rfl
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
  have hMv : stdVecMaxDiff = 2305843009213693951 := rfl
  have hrt : (BitVec.ofNat 64 len).toNat = len := ofNat64_toNat _ hlen64
  have h1w : (BitVec.ofNat 64 1).toNat = 1 := ofNat64_toNat 1 (by decide)
  have hlen1lt : len + 1 < 2 ^ 64 := by omega
  have hlen1 : ((BitVec.ofNat 64 len) + (BitVec.ofNat 64 1)).toNat =
      len + 1 := by
    rw [BitVec.toNat_add_of_lt (by rw [hrt, h1w]; exact hlen1lt), hrt, h1w]
  have hlay : layoutLookup [("t", 0, 0)] "t" = some (0, 0) := by
    simp [layoutLookup]
  have hmemLen : memLoad (tripleMem b len cap) 0 0 0 =
      .ok (BitVec.ofNat 32 len) := by
    simp [tripleMem, memLoad, memFind, hlive]
  have hmemCap : memLoad (tripleMem b len cap) 0 0 1 =
      .ok (BitVec.ofNat 32 cap) := by
    simp [tripleMem, memLoad, memFind, hlive]
  have ht0 : envLookup [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      "t" = some (.stdVecOwned b len cap) := by simp [envLookup]
  have hlenEval : evalExpr (.vgrowLen "t")
      [("t", .stdVecOwned b len cap), ("x", .i32 x)] =
      .ok (.u64 (BitVec.ofNat 64 len)) :=
    evalExpr_vgrowLen_some "t" _ b len cap ht0
  have hlenMem : memEvalExpr (.vgrowLen "t")
      [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      (tripleMem b len cap) [("t", 0, 0)] =
      .ok (.u64 (BitVec.ofNat 64 len)) := by
    rw [memEvalExpr_vgrowLen_hit "t" _ _ _ _ _ _ _ _ hlay ht0 hmemLen]
    exact hlenEval
  have hstepLen : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "len" (.u 64) (.vgrowLen "t"))
      [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      (tripleMem b len cap) [("t", 0, 0)] =
      .ok (((envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)]
        "len" (.u64 (BitVec.ofNat 64 len)),
        tripleMem b len cap, [("t", 0, 0)]), .fellThrough)) :=
    by simp only [memEvalProgStmt]; exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _ (fun _ => by simp) (fun _ => by simp) (fun _ => by simp) hlenMem hlenEval
  have ht1 : envLookup (envExtend
      [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      "len" (.u64 (BitVec.ofNat 64 len))) "t" =
      some (.stdVecOwned b len cap) := by
    simp [envLookup, envExtend, show ("t" : String) ≠ "len" by decide]
  have hcapEval : evalExpr (.vgrowCap "t") (envExtend
      [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      "len" (.u64 (BitVec.ofNat 64 len))) =
      .ok (.u64 (BitVec.ofNat 64 cap)) :=
    evalExpr_vgrowCap_some "t" _ b len cap ht1
  have hcapMem : memEvalExpr (.vgrowCap "t") (envExtend
      [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      "len" (.u64 (BitVec.ofNat 64 len)))
      (tripleMem b len cap) [("t", 0, 0)] =
      .ok (.u64 (BitVec.ofNat 64 cap)) := by
    rw [memEvalExpr_vgrowCap_hit "t" _ _ _ _ _ _ _ _ hlay ht1 hmemCap]
    exact hcapEval
  have hstepCap : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "cap" (.u 64) (.vgrowCap "t"))
      (envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)]
        "len" (.u64 (BitVec.ofNat 64 len)))
      (tripleMem b len cap) [("t", 0, 0)] =
      .ok (((envExtend (envExtend
        [("t", .stdVecOwned b len cap), ("x", .i32 x)]
        "len" (.u64 (BitVec.ofNat 64 len)))
        "cap" (.u64 (BitVec.ofNat 64 cap)),
        tripleMem b len cap, [("t", 0, 0)]), .fellThrough)) :=
    by simp only [memEvalProgStmt]; exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _ (fun _ => by simp) (fun _ => by simp) (fun _ => by simp) hcapMem hcapEval
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
  · -- Slow path (memory side): `end()` is pure, the realloc
    -- composer runs under the memory program evaluator at `F'`.
    have hcondEval : evalExpr (.une (.var "len") (.var "cap"))
        (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap))) =
        .ok (.b false) := by
      simp [evalExpr, envLookup, envExtend,
        show ("len" : String) ≠ "cap" by decide, hlc]
    have hcondMem : memEvalExpr (.une (.var "len") (.var "cap"))
        (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
        (tripleMem b len cap) [("t", 0, 0)] =
        .ok (.b false) := by
      rw [memEvalExpr_une_agree _ _ _ _ _
        (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _)]
      exact hcondEval
    have hif : memEvalProgStmt vecGrowProg (F' + 1)
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
          "cap" (.u64 (BitVec.ofNat 64 cap)))
        (tripleMem b len cap) [("t", 0, 0)] =
        memEvalProgStmt vecGrowProg (F' + 1)
        (.seq (.callRet "pos" stdVecEndName ["t"])
        (.seq (.callProg "r" stdVecGrowReallocName ["t", "pos", "x"])
              (.return_ (.var "r"))))
        (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
        (tripleMem b len cap) [("t", 0, 0)] :=
      memEvalProgStmt_if_false vecGrowProg (F' + 1) _ _ _ _ _ _ hcondMem
    have hargsPos : lookupArgs (envExtend (envExtend
        [("t", .stdVecOwned b len cap), ("x", .i32 x)]
        "len" (.u64 (BitVec.ofNat 64 len)))
        "cap" (.u64 (BitVec.ofNat 64 cap))) ["t"] =
        some [.stdVecOwned b len cap] := by
      simp only [lookupArgs, ht2]
    have hcallEnd : memEvalFuncFuel (F' + 1) stdVecEndFunc
        [.stdVecOwned b len cap] = stdVecEndFwd len :=
      memEvalFuncFuel_stdVecEnd _ b len cap hlive
    have hcallEnd' : memEvalFuncFuel (F' + 1) stdVecEndFunc
        [.stdVecOwned b len cap] = .ok (.u64 (BitVec.ofNat 64 len)) := by
      rw [hcallEnd]; rfl
    have hstepPos := memEvalProgStmt_callRet_ok vecGrowProg (F' + 1) "pos"
      stdVecEndName ["t"] _ (tripleMem b len cap) [("t", 0, 0)] _
      stdVecEndFunc (.u64 (BitVec.ofNat 64 len)) hargsPos hfindEnd hcallEnd'
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
    have hcallR : memEvalProgFunc vecGrowProg F' stdVecGrowReallocFunc
        [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len), .i32 x] =
        stdVecGrowReallocFwd b len cap (BitVec.ofNat 64 len) x :=
      memEvalProgFunc_stdVecGrowRealloc F' b len cap
        (BitVec.ofNat 64 len) x hlive hmax hSlen hlen h64
        (by rw [hrt]; omega) (by rw [hrt]; omega)
    have hFwdSlow : stdVecEmplaceBackFwd b len cap x =
        stdVecGrowReallocFwd b len cap (BitVec.ofNat 64 len) x := by
      unfold stdVecEmplaceBackFwd; simp [hlc]
    cases hR : stdVecGrowReallocFwd b len cap (BitVec.ofNat 64 len) x with
    | error e =>
      have hcallR' : memEvalProgFunc vecGrowProg F' stdVecGrowReallocFunc
          [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len), .i32 x] =
          .error e := by rw [hcallR, hR]
      have hstepR := memEvalProgStmt_callProg_err vecGrowProg F' "r"
        stdVecGrowReallocName ["t", "pos", "x"] _
        (tripleMem b len cap) [("t", 0, 0)] _
        stdVecGrowReallocFunc e hargsR hfindR hcallR'
      simp only [memEvalProgFunc, hbind, hbody]
      rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepLen,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepCap,
        hif,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepPos,
        memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstepR]
      simp only [hFwdSlow, hR]
    | ok v =>
      have hcallR' : memEvalProgFunc vecGrowProg F' stdVecGrowReallocFunc
          [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len), .i32 x] =
          .ok v := by rw [hcallR, hR]
      have hstepR := memEvalProgStmt_callProg_ok vecGrowProg F' "r"
        stdVecGrowReallocName ["t", "pos", "x"] _
        (tripleMem b len cap) [("t", 0, 0)] _
        stdVecGrowReallocFunc v hargsR hfindR hcallR'
      have hrEeval : evalExpr (.var "r") (envExtend (envExtend (envExtend
          (envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "pos" (.u64 (BitVec.ofNat 64 len))) "r" v) =
          .ok v := by
        simp [evalExpr, envLookup, envExtend]
      have hrE : memEvalExpr (.var "r") (envExtend (envExtend (envExtend
          (envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "pos" (.u64 (BitVec.ofNat 64 len))) "r" v)
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok v := by
        rw [memEvalExpr_var]; exact hrEeval
      have hret : memEvalProgStmt vecGrowProg (F' + 1)
          (.return_ (.var "r")) (envExtend (envExtend (envExtend
          (envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "pos" (.u64 (BitVec.ofNat 64 len))) "r" v)
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok (((envExtend (envExtend (envExtend
          (envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "pos" (.u64 (BitVec.ofNat 64 len))) "r" v),
          tripleMem b len cap, [("t", 0, 0)]), .returned v) :=
        memEvalProgStmt_return vecGrowProg (F' + 1) _ _ _ _ _ hrE
      simp only [memEvalProgFunc, hbind, hbody]
      rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepLen,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepCap,
        hif,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepPos,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepR, hret]
      simp only [hFwdSlow, hR]
  · -- Fast path (memory side): construct writes the buffer word in
    -- place; memory is otherwise unchanged.
    have hne64 : BitVec.ofNat 64 len ≠ BitVec.ofNat 64 cap := by
      intro hcon
      apply hlc
      have h1 := congrArg BitVec.toNat hcon
      rw [hrt, ofNat64_toNat _ hcap64] at h1
      exact h1
    have hcondEval : evalExpr (.une (.var "len") (.var "cap"))
        (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap))) =
        .ok (.b true) := by
      simp [evalExpr, envLookup, envExtend,
        show ("len" : String) ≠ "cap" by decide, hne64]
    have hcondMem : memEvalExpr (.une (.var "len") (.var "cap"))
        (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
        (tripleMem b len cap) [("t", 0, 0)] =
        .ok (.b true) := by
      rw [memEvalExpr_une_agree _ _ _ _ _
        (memEvalExpr_var _ _ _ _) (memEvalExpr_var _ _ _ _)]
      exact hcondEval
    have hif : memEvalProgStmt vecGrowProg (F' + 1)
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
          "cap" (.u64 (BitVec.ofNat 64 cap)))
        (tripleMem b len cap) [("t", 0, 0)] =
        memEvalProgStmt vecGrowProg (F' + 1)
        (.seq (.callRet "tF" stdVecTraitsConstructName ["t", "len", "x"])
        (.seq (.let_ "len1" (.u 64)
                 (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
              (.return_ (.vgrowSetLen "tF" (.var "len1")))))
        (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
        (tripleMem b len cap) [("t", 0, 0)] :=
      memEvalProgStmt_if_true vecGrowProg (F' + 1) _ _ _ _ _ _ hcondMem
    have hargsCon : lookupArgs (envExtend (envExtend
        [("t", .stdVecOwned b len cap), ("x", .i32 x)]
        "len" (.u64 (BitVec.ofNat 64 len)))
        "cap" (.u64 (BitVec.ofNat 64 cap))) ["t", "len", "x"] =
        some [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len),
          .i32 x] := by
      simp only [lookupArgs, ht2, hlen2, hx2]
    have hcallCon : memEvalFuncFuel (F' + 1) stdVecConstructFunc
        [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len), .i32 x] =
        stdVecConstructFwd b len cap (BitVec.ofNat 64 len) x :=
      memEvalFuncFuel_stdVecConstruct (F' + 1) b len cap
        (BitVec.ofNat 64 len) x
    have hFwdFast : stdVecEmplaceBackFwd b len cap x =
        ((stdVecConstructFwd b len cap (BitVec.ofNat 64 len) x).bind
          fun conv =>
        (vecGrowOwned conv).bind fun (b', _, _) =>
        .ok (.stdVecOwned b' (len + 1) cap)) := by
      unfold stdVecEmplaceBackFwd; simp [hlc]
    cases hcon : stdVecConstructFwd b len cap (BitVec.ofNat 64 len) x with
    | error e =>
      have hcallCon' : memEvalFuncFuel (F' + 1) stdVecConstructFunc
          [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len), .i32 x] =
          .error e := by rw [hcallCon, hcon]
      have hstepCon := memEvalProgStmt_callRet_err vecGrowProg (F' + 1)
        "tF" stdVecTraitsConstructName ["t", "len", "x"] _
        (tripleMem b len cap) [("t", 0, 0)] _
        stdVecConstructFunc e hargsCon hfindCon hcallCon'
      simp only [memEvalProgFunc, hbind, hbody]
      rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepLen,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepCap,
        hif, memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstepCon]
      simp only [hFwdFast, hcon, vecGrow_bind_err]
    | ok v =>
      obtain ⟨bC, rfl, hClive, hClen⟩ :=
        stdVecConstructFwd_ok _ _ _ _ _ _ hcon
      have hcallCon' : memEvalFuncFuel (F' + 1) stdVecConstructFunc
          [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len), .i32 x] =
          .ok (.stdVecOwned bC len cap) := by rw [hcallCon, hcon]
      have hstepCon := memEvalProgStmt_callRet_ok vecGrowProg (F' + 1)
        "tF" stdVecTraitsConstructName ["t", "len", "x"] _
        (tripleMem b len cap) [("t", 0, 0)] _
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
      have hlen1Mem : memEvalExpr
          (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1))))
          (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "tF" (.stdVecOwned bC len cap))
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok (.u64 ((BitVec.ofNat 64 len) + (BitVec.ofNat 64 1))) := by
        rw [memEvalExpr_uadd_agree _ _ _ _ _
          (memEvalExpr_var _ _ _ _) (memEvalExpr_lit _ _ _ _)]
        exact hlen1Eval
      have hstepLen1 : memEvalProgStmt vecGrowProg (F' + 1)
          (.let_ "len1" (.u 64)
            (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
          (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "tF" (.stdVecOwned bC len cap))
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok (((envExtend (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "tF" (.stdVecOwned bC len cap))
          "len1" (.u64 ((BitVec.ofNat 64 len) + (BitVec.ofNat 64 1))),
          tripleMem b len cap, [("t", 0, 0)]), .fellThrough)) :=
        by simp only [memEvalProgStmt]; exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _ (fun _ => by simp) (fun _ => by simp) (fun _ => by simp) hlen1Mem hlen1Eval
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
      have hretMem : memEvalExpr
          (.vgrowSetLen "tF" (.var "len1")) (envExtend (envExtend
          (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "tF" (.stdVecOwned bC len cap))
          "len1" (.u64 ((BitVec.ofNat 64 len) +
            (BitVec.ofNat 64 1))))
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok (.stdVecOwned bC (len + 1) cap) := by
        rw [memEvalExpr_vgrowSetLen_agree _ _ _ _ _
          (memEvalExpr_var _ _ _ _)]
        exact hretEval
      have hret : memEvalProgStmt vecGrowProg (F' + 1)
          (.return_ (.vgrowSetLen "tF" (.var "len1"))) (envExtend
          (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "tF" (.stdVecOwned bC len cap))
          "len1" (.u64 ((BitVec.ofNat 64 len) +
            (BitVec.ofNat 64 1))))
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok (((envExtend (envExtend (envExtend (envExtend
          [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "len" (.u64 (BitVec.ofNat 64 len)))
          "cap" (.u64 (BitVec.ofNat 64 cap)))
          "tF" (.stdVecOwned bC len cap))
          "len1" (.u64 ((BitVec.ofNat 64 len) +
            (BitVec.ofNat 64 1)))),
          tripleMem b len cap, [("t", 0, 0)]),
          .returned (.stdVecOwned bC (len + 1) cap)) :=
        memEvalProgStmt_return vecGrowProg (F' + 1) _ _ _ _ _ hretMem
      simp only [memEvalProgFunc, hbind, hbody]
      rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepLen,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepCap,
        hif,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepCon,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepLen1,
        hret]
      simp only [hFwdFast, hcon, vecGrow_bind_ok, vecGrowOwned]

/-- Transfer for `emplace_back`: program evaluation over the frozen
    leaves plus the proved realloc composer agrees on both sides (the
    composer takes the old triple by value, so the footprint
    singleton from `oracleNoalias_stdVecEmplaceBack` suffices). -/
theorem memTransfer_stdVecEmplaceBack (F : Nat) (b : Vec32)
    (len cap : Nat) (x : BitVec 32)
    (hlive : b.freed = false)
    (hmax : len ≤ stdVecMaxDiffBV.toNat)
    (hlen : len ≤ b.val.length)
    (h64 : b.val.length < 2 ^ 64)
    (hcap64 : cap < 2 ^ 64)
    (hF : len + 2 ≤ F)
    (_h : oracleNoalias stdVecEmplaceBackFunc
      [.stdVecOwned b len cap, .i32 x]) :
    memEvalProgFunc vecGrowProg F stdVecEmplaceBackFunc
      [.stdVecOwned b len cap, .i32 x] =
      evalProgFunc vecGrowProg F stdVecEmplaceBackFunc
        [.stdVecOwned b len cap, .i32 x] := by
  rw [memEvalProgFunc_stdVecEmplaceBack F b len cap x hlive hmax
    hlen h64 hcap64 hF,
    evalProgFunc_stdVecEmplaceBack F b len cap x hlive hmax
      hlen h64 hcap64 hF]

/-! ## N4d-iv-b2 `push_back` forwarder: memory agreement -/

/-- `memEval` for `push_back`: the single-`callProg` forwarder agrees
    with the `emplace_back` dispatch forward (mirrors
    `evalProgFunc_stdVecPushBack`; memory and layout thread through
    unchanged — the forwarder binds no locals — so there are no
    memory obligations beyond the callee's). -/
theorem memEvalProgFunc_stdVecPushBack (F : Nat) (b : Vec32)
    (len cap : Nat) (x : BitVec 32)
    (hlive : b.freed = false)
    (hmax : len ≤ stdVecMaxDiffBV.toNat)
    (hlen : len ≤ b.val.length)
    (h64 : b.val.length < 2 ^ 64)
    (hcap64 : cap < 2 ^ 64)
    (hF : len + 3 ≤ F) :
    memEvalProgFunc vecGrowProg F stdVecPushBackFunc
      [.stdVecOwned b len cap, .i32 x] =
      stdVecPushBackFwd b len cap x := by
  obtain ⟨F', rfl, hF'⟩ := fuel_step_down (len + 2) hF
  have hbind : bindMemArgs stdVecPushBackFunc.args
      [.stdVecOwned b len cap, .i32 x] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("x", .i32 x)],
        tripleMem b len cap, [("t", 0, 0)]) := rfl
  have hbody : stdVecPushBackFunc.body =
      (.seq (.callProg "r" stdVecEmplaceBackName ["t", "x"])
        (.return_ (.var "r"))) := rfl
  have hFwd : stdVecPushBackFwd b len cap x =
      stdVecEmplaceBackFwd b len cap x := rfl
  have ht : envLookup [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      "t" = some (.stdVecOwned b len cap) := by simp [envLookup]
  have hx : envLookup [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      "x" = some (.i32 x) := by
    simp [envLookup, show ("t" : String) ≠ "x" by decide]
  have hargs : lookupArgs [("t", .stdVecOwned b len cap), ("x", .i32 x)]
      ["t", "x"] = some [.stdVecOwned b len cap, .i32 x] := by
    simp only [lookupArgs, ht, hx]
  have hcall : memEvalProgFunc vecGrowProg F' stdVecEmplaceBackFunc
      [.stdVecOwned b len cap, .i32 x] =
      stdVecEmplaceBackFwd b len cap x :=
    memEvalProgFunc_stdVecEmplaceBack F' b len cap x hlive hmax
      hlen h64 hcap64 hF'
  cases hR : stdVecEmplaceBackFwd b len cap x with
  | error e =>
    have hcall' : memEvalProgFunc vecGrowProg F' stdVecEmplaceBackFunc
        [.stdVecOwned b len cap, .i32 x] = .error e := by rw [hcall, hR]
    have hstepCall := memEvalProgStmt_callProg_err vecGrowProg F' "r"
      stdVecEmplaceBackName ["t", "x"] _
      (tripleMem b len cap) [("t", 0, 0)] _
      stdVecEmplaceBackFunc e
      hargs findFunc_stdVecEmplaceBack hcall'
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstepCall]
    simp only [hFwd, hR]
  | ok v =>
    have hcall' : memEvalProgFunc vecGrowProg F' stdVecEmplaceBackFunc
        [.stdVecOwned b len cap, .i32 x] = .ok v := by rw [hcall, hR]
    have hstepCall := memEvalProgStmt_callProg_ok vecGrowProg F' "r"
      stdVecEmplaceBackName ["t", "x"] _
      (tripleMem b len cap) [("t", 0, 0)] _
      stdVecEmplaceBackFunc v
      hargs findFunc_stdVecEmplaceBack hcall'
    have hrEeval : evalExpr (.var "r")
        (envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)] "r" v) =
        .ok v := by
      simp [evalExpr, envLookup, envExtend]
    have hrE : memEvalExpr (.var "r")
        (envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)] "r" v)
        (tripleMem b len cap) [("t", 0, 0)] =
        .ok v := by
      rw [memEvalExpr_var]; exact hrEeval
    have hret : memEvalProgStmt vecGrowProg (F' + 1)
        (.return_ (.var "r"))
        (envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)] "r" v)
        (tripleMem b len cap) [("t", 0, 0)] =
        .ok (((envExtend [("t", .stdVecOwned b len cap), ("x", .i32 x)]
          "r" v),
          tripleMem b len cap, [("t", 0, 0)]), .returned v) :=
      memEvalProgStmt_return vecGrowProg (F' + 1) _ _ _ _ _ hrE
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepCall,
      hret]
    simp only [hFwd, hR]

/-- Transfer for `push_back`: program evaluation over the proved
    `emplace_back` composer agrees on both sides (the forwarder takes
    the old triple by value, so the footprint singleton from
    `oracleNoalias_stdVecPushBack` suffices). -/
theorem memTransfer_stdVecPushBack (F : Nat) (b : Vec32)
    (len cap : Nat) (x : BitVec 32)
    (hlive : b.freed = false)
    (hmax : len ≤ stdVecMaxDiffBV.toNat)
    (hlen : len ≤ b.val.length)
    (h64 : b.val.length < 2 ^ 64)
    (hcap64 : cap < 2 ^ 64)
    (hF : len + 3 ≤ F)
    (_h : oracleNoalias stdVecPushBackFunc
      [.stdVecOwned b len cap, .i32 x]) :
    memEvalProgFunc vecGrowProg F stdVecPushBackFunc
      [.stdVecOwned b len cap, .i32 x] =
      evalProgFunc vecGrowProg F stdVecPushBackFunc
        [.stdVecOwned b len cap, .i32 x] := by
  rw [memEvalProgFunc_stdVecPushBack F b len cap x hlive hmax
    hlen h64 hcap64 hF,
    evalProgFunc_stdVecPushBack F b len cap x hlive hmax
      hlen h64 hcap64 hF]

/-! ## N4d-iv-b2 entry-scoped `operator[]` leaf: memory agreement -/

/-- `memEval` for the non-const `operator[]` (the element word agrees
    in memory; the triple must be live and the index in bounds). -/
theorem memEvalFuncFuel_stdVecGrowIndex (F : Nat) (b : Vec32)
    (len cap : Nat) (n : BitVec 64)
    (hlive : b.freed = false)
    (x : BitVec 32)
    (hget : b.val[n.toNat]? = some x)
    (hlt : n.toNat < len) :
    memEvalFuncFuel F stdVecGrowIndexFunc
      [.stdVecOwned b len cap, .u64 n] =
      stdVecGrowIndexFwd b len n := by
  have hb : bindMemArgs stdVecGrowIndexFunc.args
      [.stdVecOwned b len cap, .u64 n] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("n", .u64 n)],
        (tripleMem b len cap),
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "n", ty := .u 64, role := .owned }]
      [.stdVecOwned b len cap, .u64 n] emptyMem = _
    exact bindMemArgs_stdVecGrowIndex b len cap n
  have hbody : stdVecGrowIndexFunc.body =
      .return_ (.vgrowAt "t" (.var "n")) := rfl
  have ht : envLookup [("t", .stdVecOwned b len cap), ("n", .u64 n)]
      "t" = some (.stdVecOwned b len cap) := by simp [envLookup]
  have hn : envLookup [("t", .stdVecOwned b len cap), ("n", .u64 n)]
      "n" = some (.u64 n) := by
    simp [envLookup]
  have hieval : evalExpr (.var "n")
      [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  have hat : evalExpr (.vgrowAt "t" (.var "n"))
      [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
      .ok (.i32 x) :=
    evalExpr_vgrowAt_some "t" (.var "n") _ b len cap n x ht hieval
      hlive hget hlt
  have hlay : layoutLookup [("t", 0, 0)] "t" = some (0, 0) := by
    simp [layoutLookup]
  have hmem : memLoad (tripleMem b len cap) 0 0 (n.toNat + 2) =
      .ok x := by
    simp [tripleMem, memLoad, memFind, hlive, hget]
  have hie : memEvalExpr (.var "n")
      [("t", .stdVecOwned b len cap), ("n", .u64 n)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.var "n") [("t", .stdVecOwned b len cap), ("n", .u64 n)] :=
    memEvalExpr_var _ _ _ _
  have hagree := memEvalExpr_vgrowAt_hit "t" (.var "n") _ _ _
    b len cap n x 0 0 hlay ht hie hieval hlive hmem hget hlt
  have hFwd : stdVecGrowIndexFwd b len n = .ok (.i32 x) := by
    simp [stdVecGrowIndexFwd, hlive, hget, hlt]
  have hret := memEvalStmtFuel_return F (.vgrowAt "t" (.var "n")) _ _ _ _
    hagree hat
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret, hFwd]

/-- Transfer for the non-const `operator[]`. -/
theorem memTransfer_stdVecGrowIndex (F : Nat) (b : Vec32)
    (len cap : Nat) (n : BitVec 64)
    (hlive : b.freed = false)
    (x : BitVec 32)
    (hget : b.val[n.toNat]? = some x)
    (hlt : n.toNat < len)
    (_h : oracleNoalias stdVecGrowIndexFunc
      [.stdVecOwned b len cap, .u64 n]) :
    memEvalFuncFuel F stdVecGrowIndexFunc
      [.stdVecOwned b len cap, .u64 n] =
      evalFuncFuel F stdVecGrowIndexFunc
        [.stdVecOwned b len cap, .u64 n] := by
  rw [memEvalFuncFuel_stdVecGrowIndex F b len cap n hlive x hget hlt,
    evalFuncFuel_stdVecGrowIndex F b len cap n hlive x hget hlt]

