/-
Circe.Transfer.GrowInsert — N7c insert composers transfer.
Over `Circe.Transfer.GrowShift`.
-/
import Circe.Transfer.GrowShift
import Circe.Transfer.GrowRealloc
import Circe.Transfer.GrowReserve

/-! ## N7c `_M_insert_aux`: composer transfer -/

/-- `memEval` for `_M_insert_aux`: the program over the frozen leaves
    agrees with the composer forward (mirrors
    `evalProgFunc_stdVecInsertAux`; caller memory threads through
    unchanged — callees communicate by value — so every step runs
    against the entry triple). -/
theorem memEvalProgFunc_stdVecInsertAux (F : Nat) (b : Vec32)
    (len cap : Nat) (pos : BitVec 64) (x : BitVec 32)
    (hlive : b.freed = false)
    (hbuf : len + 1 ≤ b.val.length)
    (hpos : pos.toNat ≤ len)
    (hlen1 : 1 ≤ len)
    (hS64 : b.val.length < 2 ^ 64)
    (hF : len + 1 ≤ F) :
    memEvalProgFunc vecGrowProg F stdVecInsertAuxFunc
      [.stdVecOwned b len cap, .u64 pos, .i32 x] =
      stdVecInsertAuxFwd b len cap pos x := by
  have hlen64 : len < 2 ^ 64 := by omega
  have hlen1p64 : len + 1 < 2 ^ 64 := by omega
  have hlenT : (BitVec.ofNat 64 len).toNat = len :=
    ofNat64_toNat _ hlen64
  have hlenp1T : (BitVec.ofNat 64 (len + 1)).toNat = len + 1 :=
    ofNat64_toNat _ hlen1p64
  have hb : bindMemArgs stdVecInsertAuxFunc.args
      [.stdVecOwned b len cap, .u64 pos, .i32 x] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)],
        tripleMem b len cap, [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "pos", ty := .u 64, role := .owned },
       { name := "x", ty := .i 32, role := .owned }]
      [.stdVecOwned b len cap, .u64 pos, .i32 x] emptyMem = _
    exact bindMemArgs_stdVecInsertAux b len cap pos x
  have hbody : stdVecInsertAuxFunc.body =
      (.seq (.let_ "len" (.u 64) (.vgrowLen "t"))
      (.seq (.let_ "last" (.u 64)
              (.usub (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
      (.seq (.let_ "lw" (.i 32) (.vgrowAt "t" (.var "last")))
      (.seq (.callRet "t1" stdVecTraitsConstructName ["t", "len", "lw"])
      (.seq (.let_ "lenp1" (.u 64)
              (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
      (.seq (.let_ "t2" (.vecBlock)
              (.vgrowSetLen "t1" (.var "lenp1")))
      (.seq (.callRet "t3" stdVecShiftBackName
              ["t2", "pos", "len", "lenp1"])
      (.seq (.callRet "t4" stdVecTraitsConstructName ["t3", "pos", "x"])
        (.return_ (.var "t4")))))))))) := rfl
  have hfindC : findFunc vecGrowProg stdVecTraitsConstructName =
      some stdVecConstructFunc := by
    unfold vecGrowProg
    rw [findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide)]
    exact findFunc_hit _ _
  have hfindS : findFunc vecGrowProg stdVecShiftBackName =
      some stdVecShiftBackFunc := by
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
      findFunc_miss _ _ _ (by decide),
      findFunc_miss _ _ _ (by decide)]
    exact findFunc_hit _ _
  have hlay : layoutLookup [("t", 0, 0)] "t" = some (0, 0) := by
    simp [layoutLookup]
  have ht0 : envLookup [("t", .stdVecOwned b len cap),
      ("pos", .u64 pos), ("x", .i32 x)] "t" =
      some (.stdVecOwned b len cap) := by simp [envLookup]
  have hlenE : evalExpr (.vgrowLen "t")
      [("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] =
      .ok (.u64 (BitVec.ofNat 64 len)) :=
    evalExpr_vgrowLen_some "t" _ b len cap ht0
  have hmemLen : memLoad (tripleMem b len cap) 0 0 0 =
      .ok (BitVec.ofNat 32 len) := by
    simp [tripleMem, memLoad, memFind, hlive]
  have mhlenE : memEvalExpr (.vgrowLen "t")
      [("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.vgrowLen "t")
        [("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] :=
    memEvalExpr_vgrowLen_hit "t" _ _ _ _ _ _ _ _ hlay ht0 hmemLen
  have mhlenE_ok : memEvalExpr (.vgrowLen "t")
      [("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)]
      (tripleMem b len cap) [("t", 0, 0)] =
      .ok (.u64 (BitVec.ofNat 64 len)) := by
    rw [mhlenE]; exact hlenE
  have elen : memEvalProgStmt vecGrowProg F
      (.let_ "len" (.u 64) (.vgrowLen "t"))
      [("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)]
      (tripleMem b len cap) [("t", 0, 0)] =
      .ok ((([("len", .u64 (BitVec.ofNat 64 len)),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)],
        tripleMem b len cap, [("t", 0, 0)])), .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
      mhlenE hlenE
  have hlenV : evalExpr (.var "len")
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] =
      .ok (.u64 (BitVec.ofNat 64 len)) := by
    simp [evalExpr, envLookup]
  have mhlenV : memEvalExpr (.var "len")
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.var "len")
        [(("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] :=
    memEvalExpr_var _ _ _ _
  have hlit1 : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have mhlit1 : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        [(("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] :=
    memEvalExpr_lit _ _ _ _
  have mhlastE := memEvalExpr_usub_agree (.var "len")
    (.lit (.u64 (BitVec.ofNat 64 1))) _ _ _ mhlenV mhlit1
  have hlastE : evalExpr
      (.usub (.var "len") (.lit (.u64 (BitVec.ofNat 64 1))))
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] =
      .ok (.u64 (BitVec.ofNat 64 len - BitVec.ofNat 64 1)) :=
    evalExpr_usub_u64u64 _ _ _ _ _ hlenV hlit1
  have hlastB : BitVec.ofNat 64 len - BitVec.ofNat 64 1 =
      BitVec.ofNat 64 (len - 1) :=
    ofNat_sub_one len hlen64 hlen1
  have hlastT : (BitVec.ofNat 64 (len - 1)).toNat = len - 1 :=
    ofNat64_toNat _ (by omega)
  have elast : memEvalProgStmt vecGrowProg F
      (.let_ "last" (.u 64)
        (.usub (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)]
      (tripleMem b len cap) [("t", 0, 0)] =
      .ok ((([(("last", .u64 (BitVec.ofNat 64 (len - 1)))),
        (("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)],
        tripleMem b len cap, [("t", 0, 0)])), .fellThrough) := by
    rw [memEvalProgStmt_let_fb, ← hlastB]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
      mhlastE hlastE
  cases hget0 : b.val[len - 1]? with
  | none =>
    have hget' : b.val[(BitVec.ofNat 64 (len - 1)).toNat]? = none := by
      rw [hlastT]; exact hget0
    have htL : envLookup
        [(("last", .u64 (BitVec.ofNat 64 (len - 1)))),
          (("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] "t" =
        some (.stdVecOwned b len cap) := by
      simp [envLookup,
        show ("t" : String) ≠ "last" by decide,
        show ("t" : String) ≠ "len" by decide]
    have hlastV : evalExpr (.var "last")
        [(("last", .u64 (BitVec.ofNat 64 (len - 1)))),
          (("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] =
        .ok (.u64 (BitVec.ofNat 64 (len - 1))) := by
      simp [evalExpr, envLookup]
    have mhlastV : memEvalExpr (.var "last")
        [(("last", .u64 (BitVec.ofNat 64 (len - 1)))),
          (("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)]
        (tripleMem b len cap) [("t", 0, 0)] =
        evalExpr (.var "last")
          [(("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)] :=
      memEvalExpr_var _ _ _ _
    have hlwE : evalExpr (.vgrowAt "t" (.var "last"))
        [(("last", .u64 (BitVec.ofNat 64 (len - 1)))),
          (("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] = .error .OOB :=
      evalExpr_vgrowAt_oob_miss "t" _ _ b len cap _ htL hlastV
        hlive hget'
    have hmemLoadE : memLoad (tripleMem b len cap) 0 0
        ((BitVec.ofNat 64 (len - 1)).toNat + 2) = .error .OOB := by
      rw [hlastT]
      simp [memLoad, tripleMem, memFind, hlive, hget0]
    have mhlwE := memEvalExpr_vgrowAt_oob_miss "t" (.var "last")
      _ _ _ b len cap (BitVec.ofNat 64 (len - 1)) 0 0 hlay htL
      mhlastV hlastV hlive hmemLoadE hget'
    have mlwE_ok : memEvalExpr (.vgrowAt "t" (.var "last"))
        [(("last", .u64 (BitVec.ofNat 64 (len - 1)))),
          (("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)]
        (tripleMem b len cap) [("t", 0, 0)] = .error .OOB := by
      rw [mhlwE]; exact hlwE
    have elw : memEvalProgStmt vecGrowProg F
        (.let_ "lw" (.i 32) (.vgrowAt "t" (.var "last")))
        [(("last", .u64 (BitVec.ofNat 64 (len - 1)))),
          (("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)]
        (tripleMem b len cap) [("t", 0, 0)] = .error .OOB := by
      rw [memEvalProgStmt_let_fb]
      exact memEvalStmtFuel_let_err _ _ _ _ _ _ _ _
        (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
        mlwE_ok
    have hidxE : stdVecGrowIndexFwd b len
        (BitVec.ofNat 64 (len - 1)) = .error .OOB := by
      have hnt : (BitVec.ofNat 64 (len - 1)).toNat = len - 1 :=
        hlastT
      simp [stdVecGrowIndexFwd, hlive, hnt, hget0]
    have hfwd : stdVecInsertAuxFwd b len cap pos x = .error .OOB := by
      simp only [stdVecInsertAuxFwd, hidxE, vecGrow_bind_err]
    have hstmt : memEvalProgStmt vecGrowProg F
        stdVecInsertAuxFunc.body
        [("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)]
        (tripleMem b len cap) [("t", 0, 0)] = .error .OOB := by
      rw [hbody]
      exact (memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
        elen).trans
        ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
          elast).trans
          (memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ elw))
    simp only [memEvalProgFunc, hb, hstmt, hfwd]
  | some w =>
    have hget' : b.val[(BitVec.ofNat 64 (len - 1)).toNat]? = some w := by
      rw [hlastT]; exact hget0
    have hlt : (BitVec.ofNat 64 (len - 1)).toNat < len := by
      rw [hlastT]; omega
    have htL : envLookup
        [(("last", .u64 (BitVec.ofNat 64 (len - 1)))),
          (("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] "t" =
        some (.stdVecOwned b len cap) := by
      simp [envLookup,
        show ("t" : String) ≠ "last" by decide,
        show ("t" : String) ≠ "len" by decide]
    have hlastV : evalExpr (.var "last")
        [(("last", .u64 (BitVec.ofNat 64 (len - 1)))),
          (("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] =
        .ok (.u64 (BitVec.ofNat 64 (len - 1))) := by
      simp [evalExpr, envLookup]
    have mhlastV : memEvalExpr (.var "last")
        [(("last", .u64 (BitVec.ofNat 64 (len - 1)))),
          (("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)]
        (tripleMem b len cap) [("t", 0, 0)] =
        evalExpr (.var "last")
          [(("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)] :=
      memEvalExpr_var _ _ _ _
    have hlw : evalExpr (.vgrowAt "t" (.var "last"))
        [(("last", .u64 (BitVec.ofNat 64 (len - 1)))),
          (("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] = .ok (.i32 w) :=
      evalExpr_vgrowAt_some "t" _ _ b len cap _ _ htL hlastV hlive
        hget' hlt
    have hmemLoad : memLoad (tripleMem b len cap) 0 0
        ((BitVec.ofNat 64 (len - 1)).toNat + 2) = .ok w := by
      rw [hlastT]
      simp [memLoad, tripleMem, memFind, hlive, hget0]
    have mhlw := memEvalExpr_vgrowAt_hit "t" (.var "last")
      _ _ _ b len cap (BitVec.ofNat 64 (len - 1)) w 0 0 hlay htL
      mhlastV hlastV hlive hmemLoad hget' hlt
    have mhlw_ok : memEvalExpr (.vgrowAt "t" (.var "last"))
        [(("last", .u64 (BitVec.ofNat 64 (len - 1)))),
          (("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)]
        (tripleMem b len cap) [("t", 0, 0)] = .ok (.i32 w) := by
      rw [mhlw]; exact hlw
    have elw : memEvalProgStmt vecGrowProg F
        (.let_ "lw" (.i 32) (.vgrowAt "t" (.var "last")))
        [(("last", .u64 (BitVec.ofNat 64 (len - 1)))),
          (("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)]
        (tripleMem b len cap) [("t", 0, 0)] =
        .ok ((([(("lw", .i32 w)),
          (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
          (("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)],
          tripleMem b len cap, [("t", 0, 0)])), .fellThrough) := by
      rw [memEvalProgStmt_let_fb]
      exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
        (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
        mhlw hlw
    have hlt' : len - 1 < len := by omega
    have hidx : stdVecGrowIndexFwd b len
        (BitVec.ofNat 64 (len - 1)) = .ok (.i32 w) := by
      simp [stdVecGrowIndexFwd, hlive, hlastT, hget0, hlt']
    have hargsT1 : lookupArgs
        [(("lw", .i32 w)),
          (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
          (("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)]
        ["t", "len", "lw"] =
        some [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len),
          .i32 w] := by
      simp [lookupArgs, envLookup,
        show ("t" : String) ≠ "lw" by decide,
        show ("t" : String) ≠ "last" by decide,
        show ("t" : String) ≠ "len" by decide,
        show ("len" : String) ≠ "lw" by decide,
        show ("len" : String) ≠ "last" by decide]
    have hcallC1 : memEvalFuncFuel F stdVecConstructFunc
        [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len), .i32 w] =
        stdVecConstructFwd b len cap (BitVec.ofNat 64 len) w :=
      memEvalFuncFuel_stdVecConstruct F b len cap
        (BitVec.ofNat 64 len) w
    cases hc1 : stdVecConstructFwd b len cap
        (BitVec.ofNat 64 len) w with
    | error e =>
      have hcallC1' : memEvalFuncFuel F stdVecConstructFunc
          [.stdVecOwned b len cap, .u64 (BitVec.ofNat 64 len),
            .i32 w] = .error e := by
        rw [hcallC1, hc1]
      have hstepT1 := memEvalProgStmt_callRet_err vecGrowProg F "t1"
        stdVecTraitsConstructName ["t", "len", "lw"] _
        (tripleMem b len cap) [("t", 0, 0)] _
        stdVecConstructFunc e hargsT1 hfindC hcallC1'
      have hfwd : stdVecInsertAuxFwd b len cap pos x = .error e := by
        simp only [stdVecInsertAuxFwd, hidx, vecGrow_bind_ok,
          vecGrowI32, hc1, vecGrow_bind_err]
      have hstmt : memEvalProgStmt vecGrowProg F
          stdVecInsertAuxFunc.body
          [("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)]
          (tripleMem b len cap) [("t", 0, 0)] = .error e := by
        rw [hbody]
        exact (memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
          elen).trans
          ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
            elast).trans
            ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
              elw).trans
              (memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstepT1)))
      simp only [memEvalProgFunc, hb, hstmt, hfwd]
    | ok c1v =>
      obtain ⟨b1, hbc1, hlive1, hlenB1⟩ :=
        stdVecConstructFwd_ok b len cap (BitVec.ofNat 64 len) w
          c1v hc1
      have hstepT1 := memEvalProgStmt_callRet_ok vecGrowProg F "t1"
        stdVecTraitsConstructName ["t", "len", "lw"] _
        (tripleMem b len cap) [("t", 0, 0)] _
        stdVecConstructFunc c1v hargsT1 hfindC
        (by rw [hcallC1, hc1])
      have hlenV1 : evalExpr (.var "len")
          [(("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)] =
          .ok (.u64 (BitVec.ofNat 64 len)) := by
        simp [evalExpr, envLookup,
          show ("len" : String) ≠ "t1" by decide,
          show ("len" : String) ≠ "lw" by decide,
          show ("len" : String) ≠ "last" by decide]
      have mhlenV1 : memEvalExpr (.var "len")
          [(("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)]
          (tripleMem b len cap) [("t", 0, 0)] =
          evalExpr (.var "len")
            [(("t1", c1v)),
              (("lw", .i32 w)),
              (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] :=
        memEvalExpr_var _ _ _ _
      have hlit1' : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
          [(("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)] =
          .ok (.u64 (BitVec.ofNat 64 1)) := by
        simp [evalExpr, litVal]
      have mhlit1' : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
          [(("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)]
          (tripleMem b len cap) [("t", 0, 0)] =
          evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
            [(("t1", c1v)),
              (("lw", .i32 w)),
              (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] :=
        memEvalExpr_lit _ _ _ _
      have mhlenp1E := memEvalExpr_uadd_agree (.var "len")
        (.lit (.u64 (BitVec.ofNat 64 1))) _ _ _ mhlenV1 mhlit1'
      have hlenp1E : evalExpr
          (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1))))
          [(("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)] =
          .ok (.u64 (BitVec.ofNat 64 (len + 1))) := by
        have h := evalExpr_uadd_u64 _ _ _ _ _ hlenV1 hlit1'
        rwa [ofNat64_add_one len] at h
      have mhlenp1E_ok : memEvalExpr
          (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1))))
          [(("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)]
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok (.u64 (BitVec.ofNat 64 (len + 1))) := by
        rw [mhlenp1E]; exact hlenp1E
      have elenp1 : memEvalProgStmt vecGrowProg F
          (.let_ "lenp1" (.u 64)
            (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
          [(("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)]
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok ((([(("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
            (("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)],
            tripleMem b len cap, [("t", 0, 0)])), .fellThrough) := by
        rw [memEvalProgStmt_let_fb]
        exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
          (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
          mhlenp1E hlenp1E
      have ht1V : evalExpr (.var "t1")
          [(("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
            (("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)] = .ok c1v := by
        simp [evalExpr, envLookup,
          show ("t1" : String) ≠ "lenp1" by decide]
      have hlenp1V : evalExpr (.var "lenp1")
          [(("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
            (("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)] =
          .ok (.u64 (BitVec.ofNat 64 (len + 1))) := by
        simp [evalExpr, envLookup]
      have mhlenp1V : memEvalExpr (.var "lenp1")
          [(("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
            (("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)]
          (tripleMem b len cap) [("t", 0, 0)] =
          evalExpr (.var "lenp1")
            [(("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
              (("t1", c1v)),
              (("lw", .i32 w)),
              (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] :=
        memEvalExpr_var _ _ _ _
      have mhlenp1V_ok : memEvalExpr (.var "lenp1")
          [(("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
            (("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)]
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok (.u64 (BitVec.ofNat 64 (len + 1))) := by
        rw [mhlenp1V]; exact hlenp1V
      have mht2agree := memEvalExpr_vgrowSetLen_agree "t1"
        (.var "lenp1") _ _ _ mhlenp1V
      have ht2E : evalExpr (.vgrowSetLen "t1" (.var "lenp1"))
          [(("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
            (("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)] =
          .ok (.stdVecOwned b1 (len + 1) cap) := by
        have ht1L : envLookup
            [(("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
              (("t1", c1v)),
              (("lw", .i32 w)),
              (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] "t1" = some c1v := by
          simp [envLookup,
            show ("t1" : String) ≠ "lenp1" by decide]
        have ht1L' : envLookup
            [(("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
              (("t1", c1v)),
              (("lw", .i32 w)),
              (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] "t1" =
            some (.stdVecOwned b1 len cap) := by
          rw [← hbc1]; exact ht1L
        have h := evalExpr_vgrowSetLen_hit "t1" _ _ b1 len cap
          (BitVec.ofNat 64 (len + 1)) ht1L' hlenp1V
        rwa [hlenp1T] at h
      have mht2E_ok : memEvalExpr (.vgrowSetLen "t1" (.var "lenp1"))
          [(("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
            (("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)]
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok (.stdVecOwned b1 (len + 1) cap) := by
        rw [mht2agree]; exact ht2E
      have et2 : memEvalProgStmt vecGrowProg F
          (.let_ "t2" (.vecBlock)
            (.vgrowSetLen "t1" (.var "lenp1")))
          [(("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
            (("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)]
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok ((([(("t2", .stdVecOwned b1 (len + 1) cap)),
            (("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
            (("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)],
            tripleMem b len cap, [("t", 0, 0)])), .fellThrough) := by
        rw [memEvalProgStmt_let_fb]
        exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
          (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
          mht2agree ht2E
      have hargsT3 : lookupArgs
          [(("t2", .stdVecOwned b1 (len + 1) cap)),
            (("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
            (("t1", c1v)),
            (("lw", .i32 w)),
            (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)]
          ["t2", "pos", "len", "lenp1"] =
          some [.stdVecOwned b1 (len + 1) cap, .u64 pos,
            .u64 (BitVec.ofNat 64 len),
            .u64 (BitVec.ofNat 64 (len + 1))] := by
        simp [lookupArgs, envLookup,
          show ("pos" : String) ≠ "t2" by decide,
          show ("pos" : String) ≠ "lenp1" by decide,
          show ("pos" : String) ≠ "t1" by decide,
          show ("pos" : String) ≠ "lw" by decide,
          show ("pos" : String) ≠ "last" by decide,
          show ("pos" : String) ≠ "len" by decide,
          show ("pos" : String) ≠ "t" by decide,
          show ("len" : String) ≠ "t2" by decide,
          show ("len" : String) ≠ "lenp1" by decide,
          show ("len" : String) ≠ "t1" by decide,
          show ("len" : String) ≠ "lw" by decide,
          show ("len" : String) ≠ "last" by decide,
          show ("lenp1" : String) ≠ "t2" by decide]
      have hcallS : memEvalFuncFuel F stdVecShiftBackFunc
          [.stdVecOwned b1 (len + 1) cap, .u64 pos,
            .u64 (BitVec.ofNat 64 len),
            .u64 (BitVec.ofNat 64 (len + 1))] =
          stdVecShiftBackFwd b1 (len + 1) cap pos
            (BitVec.ofNat 64 len) (BitVec.ofNat 64 (len + 1)) :=
        memEvalFuncFuel_stdVecShiftBack F b1 (len + 1) cap pos
          (BitVec.ofNat 64 len) (BitVec.ofNat 64 (len + 1))
          (by rw [hlenT]; exact hpos)
          (by rw [hlenT, hlenp1T]; omega)
          hlive1
          (by rw [hlenT]; omega)
          (by rw [hlenp1T]; omega)
          (by rw [hlenT]; omega)
          (by rw [hlenB1]; exact hS64)
          (by rw [hlenT]; omega)
      cases hs3 : stdVecShiftBackFwd b1 (len + 1) cap pos
          (BitVec.ofNat 64 len) (BitVec.ofNat 64 (len + 1)) with
      | error e =>
        have hcallS' : memEvalFuncFuel F stdVecShiftBackFunc
            [.stdVecOwned b1 (len + 1) cap, .u64 pos,
              .u64 (BitVec.ofNat 64 len),
              .u64 (BitVec.ofNat 64 (len + 1))] = .error e := by
          rw [hcallS, hs3]
        have hstepT3 := memEvalProgStmt_callRet_err vecGrowProg F "t3"
          stdVecShiftBackName ["t2", "pos", "len", "lenp1"] _
          (tripleMem b len cap) [("t", 0, 0)] _
          stdVecShiftBackFunc e hargsT3 hfindS hcallS'
        have hfwd : stdVecInsertAuxFwd b len cap pos x = .error e := by
          simp only [stdVecInsertAuxFwd, hidx, vecGrow_bind_ok,
            vecGrowI32, hc1, vecGrowOwned, hbc1, hs3,
            vecGrow_bind_err]
        have hstmt : memEvalProgStmt vecGrowProg F
            stdVecInsertAuxFunc.body
            [("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)]
            (tripleMem b len cap) [("t", 0, 0)] = .error e := by
          rw [hbody]
          exact (memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
            elen).trans
            ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
              elast).trans
              ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                elw).trans
                ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                  hstepT1).trans
                  ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                    elenp1).trans
                    ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                      et2).trans
                      (memEvalProgStmt_seq_err _ _ _ _ _ _ _ _
                        hstepT3))))))
        simp only [memEvalProgFunc, hb, hstmt, hfwd]
      | ok s3v =>
        obtain ⟨b3, hbc3, hlive3, hlenB3⟩ :=
          stdVecShiftBackFwd_ok b1 (len + 1) cap pos
            (BitVec.ofNat 64 len) (BitVec.ofNat 64 (len + 1)) s3v
            hlive1 hs3
        have hstepT3 := memEvalProgStmt_callRet_ok vecGrowProg F "t3"
          stdVecShiftBackName ["t2", "pos", "len", "lenp1"] _
          (tripleMem b len cap) [("t", 0, 0)] _
          stdVecShiftBackFunc s3v hargsT3 hfindS
          (by rw [hcallS, hs3])
        have hargsT4 : lookupArgs
            [(("t3", s3v)),
              (("t2", .stdVecOwned b1 (len + 1) cap)),
              (("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
              (("t1", c1v)),
              (("lw", .i32 w)),
              (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)]
            ["t3", "pos", "x"] =
            some [s3v, .u64 pos, .i32 x] := by
          simp [lookupArgs, envLookup,
            show ("pos" : String) ≠ "t3" by decide,
            show ("pos" : String) ≠ "t2" by decide,
            show ("pos" : String) ≠ "lenp1" by decide,
            show ("pos" : String) ≠ "t1" by decide,
            show ("pos" : String) ≠ "lw" by decide,
            show ("pos" : String) ≠ "last" by decide,
            show ("pos" : String) ≠ "len" by decide,
            show ("pos" : String) ≠ "t" by decide]
        have hcallC2 : memEvalFuncFuel F stdVecConstructFunc
            [s3v, .u64 pos, .i32 x] =
            stdVecConstructFwd b3 (len + 1) cap pos x := by
          rw [hbc3]
          exact memEvalFuncFuel_stdVecConstruct F b3 (len + 1) cap
            pos x
        cases hc4 : stdVecConstructFwd b3 (len + 1) cap pos x with
        | error e =>
          have hcallC2' : memEvalFuncFuel F stdVecConstructFunc
              [s3v, .u64 pos, .i32 x] = .error e := by
            rw [hcallC2, hc4]
          have hstepT4 := memEvalProgStmt_callRet_err vecGrowProg F
            "t4" stdVecTraitsConstructName ["t3", "pos", "x"] _
            (tripleMem b len cap) [("t", 0, 0)] _
            stdVecConstructFunc e hargsT4 hfindC hcallC2'
          have hfwd : stdVecInsertAuxFwd b len cap pos x = .error e := by
            simp only [stdVecInsertAuxFwd, hidx, vecGrow_bind_ok,
              vecGrowI32, hc1, vecGrowOwned, hbc1, hs3, hbc3, hc4]
          have hstmt : memEvalProgStmt vecGrowProg F
              stdVecInsertAuxFunc.body
              [("t", .stdVecOwned b len cap),
                ("pos", .u64 pos), ("x", .i32 x)]
              (tripleMem b len cap) [("t", 0, 0)] = .error e := by
            rw [hbody]
            exact (memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
              elen).trans
              ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                elast).trans
                ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                  elw).trans
                  ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                    hstepT1).trans
                    ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                      elenp1).trans
                      ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                        et2).trans
                        ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                          hstepT3).trans
                          (memEvalProgStmt_seq_err _ _ _ _ _ _ _ _
                            hstepT4)))))))
          simp only [memEvalProgFunc, hb, hstmt, hfwd]
        | ok c4v =>
          obtain ⟨b4, hbc4, _, _⟩ :=
            stdVecConstructFwd_ok b3 (len + 1) cap pos x c4v hc4
          have hstepT4 := memEvalProgStmt_callRet_ok vecGrowProg F
            "t4" stdVecTraitsConstructName ["t3", "pos", "x"] _
            (tripleMem b len cap) [("t", 0, 0)] _
            stdVecConstructFunc c4v hargsT4 hfindC
            (by rw [hcallC2, hc4])
          have hvar : evalExpr (.var "t4")
              [(("t4", c4v)),
                (("t3", s3v)),
                (("t2", .stdVecOwned b1 (len + 1) cap)),
                (("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
                (("t1", c1v)),
                (("lw", .i32 w)),
                (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
                (("len", .u64 (BitVec.ofNat 64 len))),
                ("t", .stdVecOwned b len cap),
                ("pos", .u64 pos), ("x", .i32 x)] = .ok c4v := by
            simp [evalExpr, envLookup]
          have mhvar : memEvalExpr (.var "t4")
              [(("t4", c4v)),
                (("t3", s3v)),
                (("t2", .stdVecOwned b1 (len + 1) cap)),
                (("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
                (("t1", c1v)),
                (("lw", .i32 w)),
                (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
                (("len", .u64 (BitVec.ofNat 64 len))),
                ("t", .stdVecOwned b len cap),
                ("pos", .u64 pos), ("x", .i32 x)]
              (tripleMem b len cap) [("t", 0, 0)] = .ok c4v := by
            rw [memEvalExpr_var _ _ _ _]; exact hvar
          have hret : memEvalProgStmt vecGrowProg F
              (.return_ (.var "t4"))
              [(("t4", c4v)),
                (("t3", s3v)),
                (("t2", .stdVecOwned b1 (len + 1) cap)),
                (("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
                (("t1", c1v)),
                (("lw", .i32 w)),
                (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
                (("len", .u64 (BitVec.ofNat 64 len))),
                ("t", .stdVecOwned b len cap),
                ("pos", .u64 pos), ("x", .i32 x)]
              (tripleMem b len cap) [("t", 0, 0)] =
              .ok ((([(("t4", c4v)),
                (("t3", s3v)),
                (("t2", .stdVecOwned b1 (len + 1) cap)),
                (("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
                (("t1", c1v)),
                (("lw", .i32 w)),
                (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
                (("len", .u64 (BitVec.ofNat 64 len))),
                ("t", .stdVecOwned b len cap),
                ("pos", .u64 pos), ("x", .i32 x)],
                tripleMem b len cap, [("t", 0, 0)])),
                .returned c4v) :=
            memEvalProgStmt_return vecGrowProg F _ _ _ _ _ mhvar
          have hfwd : stdVecInsertAuxFwd b len cap pos x = .ok c4v := by
            simp only [stdVecInsertAuxFwd, hidx, vecGrow_bind_ok,
              vecGrowI32, hc1, vecGrowOwned, hbc1, hs3, hbc3, hc4]
          have hstmt : memEvalProgStmt vecGrowProg F
              stdVecInsertAuxFunc.body
              [("t", .stdVecOwned b len cap),
                ("pos", .u64 pos), ("x", .i32 x)]
              (tripleMem b len cap) [("t", 0, 0)] =
              .ok ((([(("t4", c4v)),
                (("t3", s3v)),
                (("t2", .stdVecOwned b1 (len + 1) cap)),
                (("lenp1", .u64 (BitVec.ofNat 64 (len + 1)))),
                (("t1", c1v)),
                (("lw", .i32 w)),
                (("last", .u64 (BitVec.ofNat 64 (len - 1)))),
                (("len", .u64 (BitVec.ofNat 64 len))),
                ("t", .stdVecOwned b len cap),
                ("pos", .u64 pos), ("x", .i32 x)],
                tripleMem b len cap, [("t", 0, 0)])),
                .returned c4v) := by
            rw [hbody]
            exact (memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
              elen).trans
              ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                elast).trans
                ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                  elw).trans
                  ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                    hstepT1).trans
                    ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                      elenp1).trans
                      ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                        et2).trans
                        ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                          hstepT3).trans
                          ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                            hstepT4).trans
                            hret)))))))
          simp only [memEvalProgFunc, hb, hstmt, hfwd, hbc4]

/-- Transfer for `_M_insert_aux`: memory execution agrees with value
    execution (both sides reduce to the composer forward). -/
theorem memTransfer_stdVecInsertAux (F : Nat) (b : Vec32)
    (len cap : Nat) (pos : BitVec 64) (x : BitVec 32)
    (hlive : b.freed = false)
    (hbuf : len + 1 ≤ b.val.length)
    (hpos : pos.toNat ≤ len)
    (hlen1 : 1 ≤ len)
    (hS64 : b.val.length < 2 ^ 64)
    (hF : len + 1 ≤ F)
    (_h : oracleNoalias stdVecInsertAuxFunc
      [.stdVecOwned b len cap, .u64 pos, .i32 x]) :
    memEvalProgFunc vecGrowProg F stdVecInsertAuxFunc
      [.stdVecOwned b len cap, .u64 pos, .i32 x] =
      evalProgFunc vecGrowProg F stdVecInsertAuxFunc
        [.stdVecOwned b len cap, .u64 pos, .i32 x] := by
  rw [memEvalProgFunc_stdVecInsertAux F b len cap pos x hlive hbuf
    hpos hlen1 hS64 hF,
    evalProgFunc_stdVecInsertAux F b len cap pos x hlive hbuf hpos
      hlen1 hS64 hF]

/-! ## N7c `_M_insert_rval`: router transfer -/

/-- `memEval` for `_M_insert_rval`: the program over the frozen leaves
    plus the proved aux / realloc composers agrees with the router
    forward (mirrors `evalProgFunc_stdVecInsertRval`). -/
theorem memEvalProgFunc_stdVecInsertRval (F : Nat) (b : Vec32)
    (len cap : Nat) (pos : BitVec 64) (x : BitVec 32)
    (hlive : b.freed = false)
    (hbuf : len + 1 ≤ b.val.length)
    (hpos : pos.toNat ≤ len)
    (hlen1 : 1 ≤ len)
    (hmax : len ≤ stdVecMaxDiffBV.toNat)
    (hS64 : b.val.length < 2 ^ 64)
    (hcap64 : cap < 2 ^ 64)
    (hF : len + 2 ≤ F) :
    memEvalProgFunc vecGrowProg F stdVecInsertRvalFunc
      [.stdVecOwned b len cap, .u64 pos, .i32 x] =
      stdVecInsertRvalFwd b len cap pos x := by
  obtain ⟨F', rfl, hF'⟩ := fuel_step_down (len + 1) hF
  have hlen64 : len < 2 ^ 64 := by omega
  have hlenT : (BitVec.ofNat 64 len).toNat = len :=
    ofNat64_toNat _ hlen64
  have hcapT : (BitVec.ofNat 64 cap).toNat = cap :=
    ofNat64_toNat _ hcap64
  have hlenp1T : (BitVec.ofNat 64 (len + 1)).toNat = len + 1 :=
    ofNat64_toNat _ (by omega)
  have hb : bindMemArgs stdVecInsertRvalFunc.args
      [.stdVecOwned b len cap, .u64 pos, .i32 x] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)],
        tripleMem b len cap, [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "pos", ty := .u 64, role := .owned },
       { name := "x", ty := .i 32, role := .owned }]
      [.stdVecOwned b len cap, .u64 pos, .i32 x] emptyMem = _
    exact bindMemArgs_stdVecInsertRval b len cap pos x
  have hbody : stdVecInsertRvalFunc.body =
      (.seq (.let_ "len" (.u 64) (.vgrowLen "t"))
      (.if_ (.ult (.var "len") (.vgrowCap "t"))
        (.if_ (.ueq (.var "pos") (.var "len"))
          (.seq (.callRet "t1" stdVecTraitsConstructName ["t", "pos", "x"])
            (.return_ (.vgrowSetLen "t1"
              (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))))
          (.seq (.callProg "t2" stdVecInsertAuxName ["t", "pos", "x"])
            (.return_ (.var "t2"))))
        (.seq (.callProg "t3" stdVecGrowReallocName ["t", "pos", "x"])
          (.return_ (.var "t3"))))) := rfl
  have hlay : layoutLookup [("t", 0, 0)] "t" = some (0, 0) := by
    simp [layoutLookup]
  have ht0 : envLookup [("t", .stdVecOwned b len cap),
      ("pos", .u64 pos), ("x", .i32 x)] "t" =
      some (.stdVecOwned b len cap) := by simp [envLookup]
  have hlenE : evalExpr (.vgrowLen "t")
      [("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] =
      .ok (.u64 (BitVec.ofNat 64 len)) :=
    evalExpr_vgrowLen_some "t" _ b len cap ht0
  have hmemLen : memLoad (tripleMem b len cap) 0 0 0 =
      .ok (BitVec.ofNat 32 len) := by
    simp [tripleMem, memLoad, memFind, hlive]
  have mhlenE : memEvalExpr (.vgrowLen "t")
      [("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.vgrowLen "t")
        [("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] :=
    memEvalExpr_vgrowLen_hit "t" _ _ _ _ _ _ _ _ hlay ht0 hmemLen
  have mhlenE_ok : memEvalExpr (.vgrowLen "t")
      [("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)]
      (tripleMem b len cap) [("t", 0, 0)] =
      .ok (.u64 (BitVec.ofNat 64 len)) := by
    rw [mhlenE]; exact hlenE
  have elen : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "len" (.u 64) (.vgrowLen "t"))
      [("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)]
      (tripleMem b len cap) [("t", 0, 0)] =
      .ok ((([(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)],
        tripleMem b len cap, [("t", 0, 0)])), .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
      mhlenE hlenE
  have htL : envLookup
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] "t" =
      some (.stdVecOwned b len cap) := by
    simp [envLookup,
      show ("t" : String) ≠ "len" by decide]
  have hposV : evalExpr (.var "pos")
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] = .ok (.u64 pos) := by
    simp [evalExpr, envLookup,
      show ("pos" : String) ≠ "len" by decide,
      show ("pos" : String) ≠ "t" by decide]
  have hlenV : evalExpr (.var "len")
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] =
      .ok (.u64 (BitVec.ofNat 64 len)) := by
    simp [evalExpr, envLookup]
  have mhposV : memEvalExpr (.var "pos")
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.var "pos")
        [(("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] :=
    memEvalExpr_var _ _ _ _
  have mhlenV : memEvalExpr (.var "len")
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.var "len")
        [(("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] :=
    memEvalExpr_var _ _ _ _
  have hcapE : evalExpr (.vgrowCap "t")
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] =
      .ok (.u64 (BitVec.ofNat 64 cap)) :=
    evalExpr_vgrowCap_some "t" _ b len cap htL
  have hmemCap : memLoad (tripleMem b len cap) 0 0 1 =
      .ok (BitVec.ofNat 32 cap) := by
    simp [tripleMem, memLoad, memFind, hlive]
  have mhcapE : memEvalExpr (.vgrowCap "t")
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.vgrowCap "t")
        [(("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] :=
    memEvalExpr_vgrowCap_hit "t" _ _ _ _ _ _ _ _ hlay htL hmemCap
  have mhcapE_ok : memEvalExpr (.vgrowCap "t")
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)]
      (tripleMem b len cap) [("t", 0, 0)] =
      .ok (.u64 (BitVec.ofNat 64 cap)) := by
    rw [mhcapE]; exact hcapE
  have hultE : evalExpr (.ult (.var "len") (.vgrowCap "t"))
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] =
      .ok (.b ((BitVec.ofNat 64 len).ult (BitVec.ofNat 64 cap))) :=
    evalExpr_ult_u64 _ _ _ _ _ hlenV hcapE
  have mhultE := memEvalExpr_ult_agree (.var "len") (.vgrowCap "t")
    _ _ _ mhlenV mhcapE
  have mhultE_ok : memEvalExpr (.ult (.var "len") (.vgrowCap "t"))
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)]
      (tripleMem b len cap) [("t", 0, 0)] =
      .ok (.b ((BitVec.ofNat 64 len).ult (BitVec.ofNat 64 cap))) := by
    rw [mhultE]; exact hultE
  have hueqE : evalExpr (.ueq (.var "pos") (.var "len"))
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)] =
      .ok (.b (pos == BitVec.ofNat 64 len)) :=
    evalExpr_ueq_u64_vars _ _ _ _ _ hposV hlenV
  have mhueqE := memEvalExpr_ueq_agree (.var "pos") (.var "len")
    _ _ _ mhposV mhlenV
  have mhueqE_ok : memEvalExpr (.ueq (.var "pos") (.var "len"))
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)]
      (tripleMem b len cap) [("t", 0, 0)] =
      .ok (.b (pos == BitVec.ofNat 64 len)) := by
    rw [mhueqE]; exact hueqE
  have hargsT1 : lookupArgs
      [(("len", .u64 (BitVec.ofNat 64 len))),
        ("t", .stdVecOwned b len cap),
        ("pos", .u64 pos), ("x", .i32 x)]
      ["t", "pos", "x"] =
      some [.stdVecOwned b len cap, .u64 pos, .i32 x] := by
    simp [lookupArgs, envLookup,
      show ("t" : String) ≠ "len" by decide,
      show ("pos" : String) ≠ "len" by decide,
      show ("pos" : String) ≠ "t" by decide,
      show ("x" : String) ≠ "len" by decide,
      show ("x" : String) ≠ "t" by decide,
      show ("x" : String) ≠ "pos" by decide]
  cases hroomB : (BitVec.ofNat 64 len).ult (BitVec.ofNat 64 cap) with
  | true =>
    have hroom : len < cap := by
      have h := hroomB
      rw [BitVec.ult_eq_decide, hlenT, hcapT] at h
      exact of_decide_eq_true h
    have hcond : memEvalExpr (.ult (.var "len") (.vgrowCap "t"))
        [(("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)]
        (tripleMem b len cap) [("t", 0, 0)] =
        .ok (.b true) := by simp [mhultE_ok, hroomB]
    cases heqB : (pos == BitVec.ofNat 64 len) with
    | true =>
      have hcond2 : memEvalExpr (.ueq (.var "pos") (.var "len"))
          [(("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)]
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok (.b true) := by simp [mhueqE_ok, heqB]
      have hcallC1 : memEvalFuncFuel (F' + 1) stdVecConstructFunc
          [.stdVecOwned b len cap, .u64 pos, .i32 x] =
          stdVecConstructFwd b len cap pos x :=
        memEvalFuncFuel_stdVecConstruct _ b len cap pos x
      cases hcE : stdVecConstructFwd b len cap pos x with
      | error e =>
        have hcallC1' : memEvalFuncFuel (F' + 1) stdVecConstructFunc
            [.stdVecOwned b len cap, .u64 pos, .i32 x] = .error e := by
          rw [hcallC1, hcE]
        have hstepT1 := memEvalProgStmt_callRet_err vecGrowProg (F' + 1)
            "t1" stdVecTraitsConstructName ["t", "pos", "x"] _
            (tripleMem b len cap) [("t", 0, 0)] _
            stdVecConstructFunc e hargsT1
            findFunc_stdVecConstruct hcallC1'
        have hfwd : stdVecInsertRvalFwd b len cap pos x = .error e := by
          simp only [stdVecInsertRvalFwd, ite_eq_left hroom, ite_eq_left heqB,
            hcE, vecGrow_bind_err]
        have hstmt : memEvalProgStmt vecGrowProg (F' + 1)
            stdVecInsertRvalFunc.body
            [("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)]
            (tripleMem b len cap) [("t", 0, 0)] = .error e := by
          rw [hbody]
          exact (memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
            elen).trans
            ((memEvalProgStmt_if_true _ _ _ _ _ _ _ _ hcond).trans
              ((memEvalProgStmt_if_true _ _ _ _ _ _ _ _ hcond2).trans
                (memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstepT1)))
        simp only [memEvalProgFunc, hb, hstmt, hfwd]
      | ok c1v =>
        obtain ⟨bC, hbc, _, _⟩ :=
          stdVecConstructFwd_ok b len cap pos x c1v hcE
        have hstepT1 := memEvalProgStmt_callRet_ok vecGrowProg (F' + 1)
            "t1" stdVecTraitsConstructName ["t", "pos", "x"] _
            (tripleMem b len cap) [("t", 0, 0)] _
            stdVecConstructFunc c1v hargsT1
            findFunc_stdVecConstruct
            (by rw [hcallC1, hcE])
        have ht1L : envLookup
            [(("t1", c1v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] "t1" = some c1v := by
          simp [envLookup]
        have ht1L' : envLookup
            [(("t1", c1v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] "t1" =
            some (.stdVecOwned bC len cap) := by
          rw [← hbc]; exact ht1L
        have hlenV1 : evalExpr (.var "len")
            [(("t1", c1v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] =
            .ok (.u64 (BitVec.ofNat 64 len)) := by
          simp [evalExpr, envLookup,
            show ("len" : String) ≠ "t1" by decide]
        have mhlenV1 : memEvalExpr (.var "len")
            [(("t1", c1v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)]
            (tripleMem b len cap) [("t", 0, 0)] =
            evalExpr (.var "len")
              [(("t1", c1v)),
                (("len", .u64 (BitVec.ofNat 64 len))),
                ("t", .stdVecOwned b len cap),
                ("pos", .u64 pos), ("x", .i32 x)] :=
          memEvalExpr_var _ _ _ _
        have hlit1' : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
            [(("t1", c1v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] =
            .ok (.u64 (BitVec.ofNat 64 1)) := by
          simp [evalExpr, litVal]
        have mhlit1' : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
            [(("t1", c1v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)]
            (tripleMem b len cap) [("t", 0, 0)] =
            evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
              [(("t1", c1v)),
                (("len", .u64 (BitVec.ofNat 64 len))),
                ("t", .stdVecOwned b len cap),
                ("pos", .u64 pos), ("x", .i32 x)] :=
          memEvalExpr_lit _ _ _ _
        have mhlenp1E := memEvalExpr_uadd_agree (.var "len")
          (.lit (.u64 (BitVec.ofNat 64 1))) _ _ _ mhlenV1 mhlit1'
        have hlenp1E : evalExpr
            (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1))))
            [(("t1", c1v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] =
            .ok (.u64 (BitVec.ofNat 64 (len + 1))) := by
          have h := evalExpr_uadd_u64 _ _ _ _ _ hlenV1 hlit1'
          rwa [ofNat64_add_one len] at h
        have mhlenp1E_ok : memEvalExpr
            (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1))))
            [(("t1", c1v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)]
            (tripleMem b len cap) [("t", 0, 0)] =
            .ok (.u64 (BitVec.ofNat 64 (len + 1))) := by
          rw [mhlenp1E]; exact hlenp1E
        have mht1agree := memEvalExpr_vgrowSetLen_agree "t1"
          (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1))))
          _ _ _ mhlenp1E
        have hsetE : evalExpr
            (.vgrowSetLen "t1"
              (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
            [(("t1", c1v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] =
            .ok (.stdVecOwned bC (len + 1) cap) := by
          have h := evalExpr_vgrowSetLen_hit "t1" _ _
            bC len cap (BitVec.ofNat 64 (len + 1)) ht1L' hlenp1E
          rwa [hlenp1T] at h
        have mht1E_ok : memEvalExpr
            (.vgrowSetLen "t1"
              (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1)))))
            [(("t1", c1v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)]
            (tripleMem b len cap) [("t", 0, 0)] =
            .ok (.stdVecOwned bC (len + 1) cap) := by
          rw [mht1agree]; exact hsetE
        have hret : memEvalProgStmt vecGrowProg (F' + 1)
            (.return_ (.vgrowSetLen "t1"
              (.uadd (.var "len") (.lit (.u64 (BitVec.ofNat 64 1))))))
            [(("t1", c1v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)]
            (tripleMem b len cap) [("t", 0, 0)] =
            .ok ((([(("t1", c1v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)],
              tripleMem b len cap, [("t", 0, 0)])),
              .returned (.stdVecOwned bC (len + 1) cap)) :=
          memEvalProgStmt_return vecGrowProg (F' + 1) _ _ _ _ _
            mht1E_ok
        have hfwd : stdVecInsertRvalFwd b len cap pos x =
            .ok (.stdVecOwned bC (len + 1) cap) := by
          simp only [stdVecInsertRvalFwd, ite_eq_left hroom, ite_eq_left heqB,
            hcE, vecGrow_bind_ok, vecGrowOwned, hbc]
        have hstmt : memEvalProgStmt vecGrowProg (F' + 1)
            stdVecInsertRvalFunc.body
            [("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)]
            (tripleMem b len cap) [("t", 0, 0)] =
            .ok ((([(("t1", c1v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)],
              tripleMem b len cap, [("t", 0, 0)])),
              .returned (.stdVecOwned bC (len + 1) cap)) := by
          rw [hbody]
          exact (memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
            elen).trans
            ((memEvalProgStmt_if_true _ _ _ _ _ _ _ _ hcond).trans
              ((memEvalProgStmt_if_true _ _ _ _ _ _ _ _ hcond2).trans
                ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                  hstepT1).trans
                  hret)))
        simp only [memEvalProgFunc, hb, hstmt, hfwd]
    | false =>
      have hcond2 : memEvalExpr (.ueq (.var "pos") (.var "len"))
          [(("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)]
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok (.b false) := by simp [mhueqE_ok, heqB]
      have hneB : ¬ ((pos == BitVec.ofNat 64 len) = true) := by
        simp [heqB]
      have hcallA : memEvalProgFunc vecGrowProg F' stdVecInsertAuxFunc
          [.stdVecOwned b len cap, .u64 pos, .i32 x] =
          stdVecInsertAuxFwd b len cap pos x :=
        memEvalProgFunc_stdVecInsertAux F' b len cap pos x hlive
          hbuf hpos hlen1 hS64 hF'
      cases hA : stdVecInsertAuxFwd b len cap pos x with
      | error e =>
        have hcallA' : memEvalProgFunc vecGrowProg F'
            stdVecInsertAuxFunc
            [.stdVecOwned b len cap, .u64 pos, .i32 x] = .error e := by
          rw [hcallA, hA]
        have hstepT2 := memEvalProgStmt_callProg_err vecGrowProg F'
            "t2" stdVecInsertAuxName ["t", "pos", "x"] _
            (tripleMem b len cap) [("t", 0, 0)] _
            stdVecInsertAuxFunc e hargsT1 findFunc_stdVecInsertAux
            hcallA'
        have hfwd : stdVecInsertRvalFwd b len cap pos x = .error e := by
          simp only [stdVecInsertRvalFwd, ite_eq_left hroom, ite_eq_right hneB, hA]
        have hstmt : memEvalProgStmt vecGrowProg (F' + 1)
            stdVecInsertRvalFunc.body
            [("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)]
            (tripleMem b len cap) [("t", 0, 0)] = .error e := by
          rw [hbody]
          exact (memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
            elen).trans
            ((memEvalProgStmt_if_true _ _ _ _ _ _ _ _ hcond).trans
              ((memEvalProgStmt_if_false _ _ _ _ _ _ _ _ hcond2).trans
                (memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstepT2)))
        simp only [memEvalProgFunc, hb, hstmt, hfwd]
      | ok v =>
        have hcallA' : memEvalProgFunc vecGrowProg F'
            stdVecInsertAuxFunc
            [.stdVecOwned b len cap, .u64 pos, .i32 x] = .ok v := by
          rw [hcallA, hA]
        have hstepT2 := memEvalProgStmt_callProg_ok vecGrowProg F'
            "t2" stdVecInsertAuxName ["t", "pos", "x"] _
            (tripleMem b len cap) [("t", 0, 0)] _
            stdVecInsertAuxFunc v hargsT1 findFunc_stdVecInsertAux
            hcallA'
        have hvarT2 : evalExpr (.var "t2")
            [(("t2", v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)] = .ok v := by
          simp [evalExpr, envLookup]
        have mhvarT2 : memEvalExpr (.var "t2")
            [(("t2", v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)]
            (tripleMem b len cap) [("t", 0, 0)] = .ok v := by
          rw [memEvalExpr_var _ _ _ _]; exact hvarT2
        have hret : memEvalProgStmt vecGrowProg (F' + 1)
            (.return_ (.var "t2"))
            [(("t2", v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)]
            (tripleMem b len cap) [("t", 0, 0)] =
            .ok ((([(("t2", v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)],
              tripleMem b len cap, [("t", 0, 0)])),
              .returned v) :=
          memEvalProgStmt_return vecGrowProg (F' + 1) _ _ _ _ _
            mhvarT2
        have hfwd : stdVecInsertRvalFwd b len cap pos x = .ok v := by
          simp only [stdVecInsertRvalFwd, ite_eq_left hroom, ite_eq_right hneB, hA]
        have hstmt : memEvalProgStmt vecGrowProg (F' + 1)
            stdVecInsertRvalFunc.body
            [("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)]
            (tripleMem b len cap) [("t", 0, 0)] =
            .ok ((([(("t2", v)),
              (("len", .u64 (BitVec.ofNat 64 len))),
              ("t", .stdVecOwned b len cap),
              ("pos", .u64 pos), ("x", .i32 x)],
              tripleMem b len cap, [("t", 0, 0)])),
              .returned v) := by
          rw [hbody]
          exact (memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
            elen).trans
            ((memEvalProgStmt_if_true _ _ _ _ _ _ _ _ hcond).trans
              ((memEvalProgStmt_if_false _ _ _ _ _ _ _ _ hcond2).trans
                ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                  hstepT2).trans
                  hret)))
        simp only [memEvalProgFunc, hb, hstmt, hfwd]
  | false =>
    have hroom : ¬ len < cap := by
      intro hlt
      have h := hroomB
      rw [BitVec.ult_eq_decide, hlenT, hcapT] at h
      simp [hlt] at h
    have hcond : memEvalExpr (.ult (.var "len") (.vgrowCap "t"))
        [(("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)]
        (tripleMem b len cap) [("t", 0, 0)] =
        .ok (.b false) := by simp [mhultE_ok, hroomB]
    have hargsT3 : lookupArgs
        [(("len", .u64 (BitVec.ofNat 64 len))),
          ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)]
        ["t", "pos", "x"] =
        some [.stdVecOwned b len cap, .u64 pos, .i32 x] := by
      simp [lookupArgs, envLookup,
        show ("t" : String) ≠ "len" by decide,
        show ("pos" : String) ≠ "len" by decide,
        show ("pos" : String) ≠ "t" by decide,
        show ("x" : String) ≠ "len" by decide,
        show ("x" : String) ≠ "t" by decide,
        show ("x" : String) ≠ "pos" by decide]
    have hcallR : memEvalProgFunc vecGrowProg F'
        stdVecGrowReallocFunc
        [.stdVecOwned b len cap, .u64 pos, .i32 x] =
        stdVecGrowReallocFwd b len cap pos x :=
      memEvalProgFunc_stdVecGrowRealloc F' b len cap pos x hlive
        hmax hpos (by omega) hS64 (by omega) (by omega)
    cases hR : stdVecGrowReallocFwd b len cap pos x with
    | error e =>
      have hcallR' : memEvalProgFunc vecGrowProg F'
          stdVecGrowReallocFunc
          [.stdVecOwned b len cap, .u64 pos, .i32 x] = .error e := by
        rw [hcallR, hR]
      have hstepT3 := memEvalProgStmt_callProg_err vecGrowProg F'
          "t3" stdVecGrowReallocName ["t", "pos", "x"] _
          (tripleMem b len cap) [("t", 0, 0)] _
          stdVecGrowReallocFunc e hargsT3
          findFunc_stdVecGrowRealloc hcallR'
      have hfwd : stdVecInsertRvalFwd b len cap pos x = .error e := by
        simp only [stdVecInsertRvalFwd, ite_eq_right hroom, hR]
      have hstmt : memEvalProgStmt vecGrowProg (F' + 1)
          stdVecInsertRvalFunc.body
          [("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)]
          (tripleMem b len cap) [("t", 0, 0)] = .error e := by
        rw [hbody]
        exact (memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
          elen).trans
          ((memEvalProgStmt_if_false _ _ _ _ _ _ _ _ hcond).trans
            (memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstepT3))
      simp only [memEvalProgFunc, hb, hstmt, hfwd]
    | ok v =>
      have hcallR' : memEvalProgFunc vecGrowProg F'
          stdVecGrowReallocFunc
          [.stdVecOwned b len cap, .u64 pos, .i32 x] = .ok v := by
        rw [hcallR, hR]
      have hstepT3 := memEvalProgStmt_callProg_ok vecGrowProg F'
          "t3" stdVecGrowReallocName ["t", "pos", "x"] _
          (tripleMem b len cap) [("t", 0, 0)] _
          stdVecGrowReallocFunc v hargsT3
          findFunc_stdVecGrowRealloc hcallR'
      have hvarT3 : evalExpr (.var "t3")
          [(("t3", v)),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)] = .ok v := by
        simp [evalExpr, envLookup]
      have mhvarT3 : memEvalExpr (.var "t3")
          [(("t3", v)),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)]
          (tripleMem b len cap) [("t", 0, 0)] = .ok v := by
        rw [memEvalExpr_var _ _ _ _]; exact hvarT3
      have hret : memEvalProgStmt vecGrowProg (F' + 1)
          (.return_ (.var "t3"))
          [(("t3", v)),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)]
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok ((([(("t3", v)),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)],
            tripleMem b len cap, [("t", 0, 0)])),
            .returned v) :=
        memEvalProgStmt_return vecGrowProg (F' + 1) _ _ _ _ _
          mhvarT3
      have hfwd : stdVecInsertRvalFwd b len cap pos x = .ok v := by
        simp only [stdVecInsertRvalFwd, ite_eq_right hroom, hR]
      have hstmt : memEvalProgStmt vecGrowProg (F' + 1)
          stdVecInsertRvalFunc.body
          [("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)]
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok ((([(("t3", v)),
            (("len", .u64 (BitVec.ofNat 64 len))),
            ("t", .stdVecOwned b len cap),
            ("pos", .u64 pos), ("x", .i32 x)],
            tripleMem b len cap, [("t", 0, 0)])),
            .returned v) := by
        rw [hbody]
        exact (memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
          elen).trans
          ((memEvalProgStmt_if_false _ _ _ _ _ _ _ _ hcond).trans
            ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
              hstepT3).trans
              hret))
      simp only [memEvalProgFunc, hb, hstmt, hfwd]

/-- Transfer for `_M_insert_rval`: memory execution agrees with value
    execution (both sides reduce to the router forward). -/
theorem memTransfer_stdVecInsertRval (F : Nat) (b : Vec32)
    (len cap : Nat) (pos : BitVec 64) (x : BitVec 32)
    (hlive : b.freed = false)
    (hbuf : len + 1 ≤ b.val.length)
    (hpos : pos.toNat ≤ len)
    (hlen1 : 1 ≤ len)
    (hmax : len ≤ stdVecMaxDiffBV.toNat)
    (hS64 : b.val.length < 2 ^ 64)
    (hcap64 : cap < 2 ^ 64)
    (hF : len + 2 ≤ F)
    (_h : oracleNoalias stdVecInsertRvalFunc
      [.stdVecOwned b len cap, .u64 pos, .i32 x]) :
    memEvalProgFunc vecGrowProg F stdVecInsertRvalFunc
      [.stdVecOwned b len cap, .u64 pos, .i32 x] =
      evalProgFunc vecGrowProg F stdVecInsertRvalFunc
        [.stdVecOwned b len cap, .u64 pos, .i32 x] := by
  rw [memEvalProgFunc_stdVecInsertRval F b len cap pos x hlive hbuf
    hpos hlen1 hmax hS64 hcap64 hF,
    evalProgFunc_stdVecInsertRval F b len cap pos x hlive hbuf hpos
      hlen1 hmax hS64 hcap64 hF]

/-! ## N7c `insert` forwarder: transfer -/

/-- `memEval` for the `insert` forwarder: delegate to `_M_insert_rval`
    (mirrors `evalProgFunc_stdVecInsert`). -/
theorem memEvalProgFunc_stdVecInsert (F : Nat) (b : Vec32)
    (len cap : Nat) (pos : BitVec 64) (x : BitVec 32)
    (hlive : b.freed = false)
    (hbuf : len + 1 ≤ b.val.length)
    (hpos : pos.toNat ≤ len)
    (hlen1 : 1 ≤ len)
    (hmax : len ≤ stdVecMaxDiffBV.toNat)
    (hS64 : b.val.length < 2 ^ 64)
    (hcap64 : cap < 2 ^ 64)
    (hF : len + 3 ≤ F) :
    memEvalProgFunc vecGrowProg F stdVecInsertFunc
      [.stdVecOwned b len cap, .u64 pos, .i32 x] =
      stdVecInsertFwd b len cap pos x := by
  obtain ⟨F', rfl, hF'⟩ := fuel_step_down (len + 2) hF
  have hFwd : stdVecInsertFwd b len cap pos x =
      stdVecInsertRvalFwd b len cap pos x := rfl
  have hb : bindMemArgs stdVecInsertFunc.args
      [.stdVecOwned b len cap, .u64 pos, .i32 x] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("pos", .u64 pos),
        ("x", .i32 x)],
        tripleMem b len cap, [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "pos", ty := .u 64, role := .owned },
       { name := "x", ty := .i 32, role := .owned }]
      [.stdVecOwned b len cap, .u64 pos, .i32 x] emptyMem = _
    exact bindMemArgs_stdVecInsert b len cap pos x
  have hbody : stdVecInsertFunc.body =
      (.seq (.callProg "t1" stdVecInsertRvalName ["t", "pos", "x"])
        (.return_ (.var "t1"))) := rfl
  have hargs : lookupArgs [("t", .stdVecOwned b len cap),
      ("pos", .u64 pos), ("x", .i32 x)]
      ["t", "pos", "x"] = some [.stdVecOwned b len cap, .u64 pos,
        .i32 x] := by
    simp [lookupArgs, envLookup,
      show ("pos" : String) ≠ "t" by decide,
      show ("x" : String) ≠ "t" by decide,
      show ("x" : String) ≠ "pos" by decide]
  have hcall : memEvalProgFunc vecGrowProg F' stdVecInsertRvalFunc
      [.stdVecOwned b len cap, .u64 pos, .i32 x] =
      stdVecInsertRvalFwd b len cap pos x :=
    memEvalProgFunc_stdVecInsertRval F' b len cap pos x hlive hbuf
      hpos hlen1 hmax hS64 hcap64 hF'
  cases hR : stdVecInsertRvalFwd b len cap pos x with
  | error e =>
    have hcall' : memEvalProgFunc vecGrowProg F'
        stdVecInsertRvalFunc
        [.stdVecOwned b len cap, .u64 pos, .i32 x] = .error e := by
      rw [hcall, hR]
    have hstepCall := memEvalProgStmt_callProg_err vecGrowProg F'
        "t1" stdVecInsertRvalName ["t", "pos", "x"] _
        (tripleMem b len cap) [("t", 0, 0)] _
        stdVecInsertRvalFunc e hargs findFunc_stdVecInsertRval
        hcall'
    have hstmt : memEvalProgStmt vecGrowProg (F' + 1)
        stdVecInsertFunc.body
        [("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)]
        (tripleMem b len cap) [("t", 0, 0)] = .error e := by
      simp only [memEvalProgFunc, hb, hbody]
      rw [memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstepCall]
    simp only [memEvalProgFunc, hb, hstmt, hFwd, hR]
  | ok v =>
    have hcall' : memEvalProgFunc vecGrowProg F'
        stdVecInsertRvalFunc
        [.stdVecOwned b len cap, .u64 pos, .i32 x] = .ok v := by
      rw [hcall, hR]
    have hstepCall := memEvalProgStmt_callProg_ok vecGrowProg F'
        "t1" stdVecInsertRvalName ["t", "pos", "x"] _
        (tripleMem b len cap) [("t", 0, 0)] _
        stdVecInsertRvalFunc v hargs findFunc_stdVecInsertRval
        hcall'
    have hvar : evalExpr (.var "t1")
        [(("t1", v)), ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)] = .ok v := by
      simp [evalExpr, envLookup]
    have mhvar : memEvalExpr (.var "t1")
        [(("t1", v)), ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)]
        (tripleMem b len cap) [("t", 0, 0)] = .ok v := by
      rw [memEvalExpr_var _ _ _ _]; exact hvar
    have hret : memEvalProgStmt vecGrowProg (F' + 1)
        (.return_ (.var "t1"))
        [(("t1", v)), ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)]
        (tripleMem b len cap) [("t", 0, 0)] =
        .ok ((([(("t1", v)), ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)],
          tripleMem b len cap, [("t", 0, 0)]),
          .returned v)) :=
      memEvalProgStmt_return vecGrowProg (F' + 1) _ _ _ _ _ mhvar
    have hfwd : stdVecInsertFwd b len cap pos x = .ok v := by
      simp only [stdVecInsertFwd, hR]
    have hstmt : memEvalProgStmt vecGrowProg (F' + 1)
        stdVecInsertFunc.body
        [("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)]
        (tripleMem b len cap) [("t", 0, 0)] =
        .ok ((([(("t1", v)), ("t", .stdVecOwned b len cap),
          ("pos", .u64 pos), ("x", .i32 x)],
          tripleMem b len cap, [("t", 0, 0)]),
          .returned v)) := by
      rw [hbody]
      exact (memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
        hstepCall).trans hret
    simp only [memEvalProgFunc, hb, hstmt, hfwd]

/-- Transfer for the `insert` forwarder: memory execution agrees with
    value execution (both sides reduce to the rval forward). -/
theorem memTransfer_stdVecInsert (F : Nat) (b : Vec32)
    (len cap : Nat) (pos : BitVec 64) (x : BitVec 32)
    (hlive : b.freed = false)
    (hbuf : len + 1 ≤ b.val.length)
    (hpos : pos.toNat ≤ len)
    (hlen1 : 1 ≤ len)
    (hmax : len ≤ stdVecMaxDiffBV.toNat)
    (hS64 : b.val.length < 2 ^ 64)
    (hcap64 : cap < 2 ^ 64)
    (hF : len + 3 ≤ F)
    (_h : oracleNoalias stdVecInsertFunc
      [.stdVecOwned b len cap, .u64 pos, .i32 x]) :
    memEvalProgFunc vecGrowProg F stdVecInsertFunc
      [.stdVecOwned b len cap, .u64 pos, .i32 x] =
      evalProgFunc vecGrowProg F stdVecInsertFunc
        [.stdVecOwned b len cap, .u64 pos, .i32 x] := by
  rw [memEvalProgFunc_stdVecInsert F b len cap pos x hlive hbuf hpos
    hlen1 hmax hS64 hcap64 hF,
    evalProgFunc_stdVecInsert F b len cap pos x hlive hbuf hpos
      hlen1 hmax hS64 hcap64 hF]

/-! ## N7c-ii-b `vec_insert_sum` entry: transfer -/

set_option maxRecDepth 8192 in
/-- `memEval` for `vec_insert_sum`: the closed entry over the grown
    program agrees with the compute-to-`6` forward (mirrors
    `evalProgFunc_vecInsertSumEntry`; the entry threads `emptyMem`
    — every callee re-binds from its value arguments). -/
theorem memEvalProgFunc_vecInsertSumEntry (F : Nat) (hF : 6 ≤ F) :
    memEvalProgFunc vecGrowProg F vecInsertSumEntryFunc [] =
      vecInsertSumEntryFwd := by
  obtain ⟨F', rfl, hF'⟩ := fuel_step_down 5 hF
  have hbind : bindMemArgs vecInsertSumEntryFunc.args [] emptyMem =
      some ([], emptyMem, []) :=
    bindMemArgs_vecInsertSumEntry
  have hbody : vecInsertSumEntryFunc.body =
      .seq (.callRet "v0" stdVecCtorName [])
      (.seq (.let_ "n" (.u 64) (.lit (.u64 (BitVec.ofNat 64 10))))
      (.seq (.callProg "v1" stdVecReserveName ["v0", "n"])
      (.seq (.let_ "c0" (.i 32) (.lit (.i32 (BitVec.ofNat 32 1))))
      (.seq (.callProg "v2" stdVecPushBackName ["v1", "c0"])
      (.seq (.let_ "c1" (.i 32) (.lit (.i32 (BitVec.ofNat 32 3))))
      (.seq (.callProg "v3" stdVecPushBackName ["v2", "c1"])
      (.seq (.callRet "bpos" stdVecBeginName ["v3"])
      (.seq (.let_ "one" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      (.seq (.callRet "p1" stdVecPlusElName ["bpos", "one"])
      (.seq (.let_ "c2" (.i 32) (.lit (.i32 (BitVec.ofNat 32 2))))
      (.seq (.callProg "v4" stdVecInsertName ["v3", "p1", "c2"])
      (.seq (.let_ "n0" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.seq (.callRet "e0" stdVecGrowIndexName ["v4", "n0"])
      (.seq (.let_ "n1" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      (.seq (.callRet "e1" stdVecGrowIndexName ["v4", "n1"])
      (.seq (.let_ "s01" (.i 32) (.add (.var "e0") (.var "e1")))
      (.seq (.let_ "n2" (.u 64) (.lit (.u64 (BitVec.ofNat 64 2))))
      (.seq (.callRet "e2" stdVecGrowIndexName ["v4", "n2"])
      (.seq (.let_ "s" (.i 32) (.add (.var "s01") (.var "e2")))
      (.seq (.callRet "v5" stdVecDtorName ["v4"])
        (.return_ (.var "s")))))))))))))))))))))) := rfl
  -- Step 1: the default ctor.
  have hargs0 : lookupArgs ([] : Env) [] = some [] := rfl
  have hcall0 : memEvalFuncFuel (F' + 1) stdVecEmptyCtorFunc [] =
      .ok (.stdVecOwned ⟨[], false⟩ 0 0) :=
    memEvalFuncFuel_stdVecEmptyCtor _
  have hstepV0 := memEvalProgStmt_callRet_ok vecGrowProg (F' + 1)
      "v0" stdVecCtorName [] ([] : Env) emptyMem [] _
      stdVecEmptyCtorFunc
      (.stdVecOwned ⟨[], false⟩ 0 0)
      hargs0 findFunc_stdVecEmptyCtor hcall0
  -- Step 2: `n = 10`.
  have hlitN : evalExpr (.lit (.u64 (BitVec.ofNat 64 10)))
      [("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.u64 (BitVec.ofNat 64 10)) := by
    simp [evalExpr, litVal]
  have mhlitN : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 10)))
      [("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 10)))
        [("v0", .stdVecOwned ⟨[], false⟩ 0 0)] :=
    memEvalExpr_lit _ _ _ _
  have mhlitN_ok : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 10)))
      [("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      .ok (.u64 (BitVec.ofNat 64 10)) := by
    rw [mhlitN]; exact hlitN
  have hstepN : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "n" (.u 64) (.lit (.u64 (BitVec.ofNat 64 10))))
      [("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      .ok ((([("n", .u64 (BitVec.ofNat 64 10)),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], emptyMem, [])),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
      mhlitN hlitN
  -- Step 3: `reserve(10)` takes the reallocation arm over the empty
  -- triple (zero words relocated, ten-word spare buffer).
  have hargsR : lookupArgs
      [(("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v0", "n"] =
      some [.stdVecOwned ⟨[], false⟩ 0 0,
        .u64 (BitVec.ofNat 64 10)] := by
    simp [lookupArgs, envLookup,
      show ("v0" : String) ≠ "n" by decide]
  have hcallR : memEvalProgFunc vecGrowProg F' stdVecReserveFunc
      [.stdVecOwned ⟨[], false⟩ 0 0, .u64 (BitVec.ofNat 64 10)] =
      stdVecReserveFwd ⟨[], false⟩ 0 0 (BitVec.ofNat 64 10) :=
    memEvalProgFunc_stdVecReserve F' _ 0 0 _ rfl (by decide)
      (Nat.zero_le _) (by decide) (by decide) (by omega)
  have hcallR' : memEvalProgFunc vecGrowProg F' stdVecReserveFunc
      [.stdVecOwned ⟨[], false⟩ 0 0, .u64 (BitVec.ofNat 64 10)] =
      .ok (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10) := by
    rw [hcallR, vecReserveStep_eq]
  have hstepV1 := memEvalProgStmt_callProg_ok vecGrowProg F' "v1"
      stdVecReserveName ["v0", "n"] _ emptyMem [] _
      stdVecReserveFunc
      (.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)
      hargsR findFunc_stdVecReserve hcallR'
  -- Step 4: `c0 = 1`.
  have hlitC0 : evalExpr (.lit (.i32 (BitVec.ofNat 32 1)))
      [(("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.i32 (BitVec.ofNat 32 1)) := by
    simp [evalExpr, litVal]
  have mhlitC0 : memEvalExpr (.lit (.i32 (BitVec.ofNat 32 1)))
      [(("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      evalExpr (.lit (.i32 (BitVec.ofNat 32 1)))
        [(("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
          (("n", .u64 (BitVec.ofNat 64 10))),
          ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] :=
    memEvalExpr_lit _ _ _ _
  have hstepC0 : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "c0" (.i 32) (.lit (.i32 (BitVec.ofNat 32 1))))
      [(("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      .ok ((([(("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], emptyMem, [])),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
      mhlitC0 hlitC0
  -- Step 5: first push (fast path into the spare triple).
  have hargs1 : lookupArgs
      [(("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v1", "c0"] =
      some [.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10,
        .i32 (BitVec.ofNat 32 1)] := by
    simp [lookupArgs, envLookup,
      show ("v1" : String) ≠ "c0" by decide]
  have hcallP1 : memEvalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10,
        .i32 (BitVec.ofNat 32 1)] =
      stdVecPushBackFwd ⟨List.replicate 10 0, false⟩ 0 10
        (BitVec.ofNat 32 1) :=
    memEvalProgFunc_stdVecPushBack F' _ 0 10 _ rfl (by decide)
      (by decide) (by decide) (by decide) (by omega)
  have hcallP1' : memEvalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10,
        .i32 (BitVec.ofNat 32 1)] =
      .ok (.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10) := by
    rw [hcallP1, vecReservePush1_eq]
  have hstepV2 := memEvalProgStmt_callProg_ok vecGrowProg F' "v2"
      stdVecPushBackName ["v1", "c0"] _ emptyMem [] _
      stdVecPushBackFunc
      (.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩ 1 10)
      hargs1 findFunc_stdVecPushBack hcallP1'
  -- Step 6: `c1 = 3`.
  have hlitC1 : evalExpr (.lit (.i32 (BitVec.ofNat 32 3)))
      [(("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.i32 (BitVec.ofNat 32 3)) := by
    simp [evalExpr, litVal]
  have mhlitC1 : memEvalExpr (.lit (.i32 (BitVec.ofNat 32 3)))
      [(("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      evalExpr (.lit (.i32 (BitVec.ofNat 32 3)))
        [(("v2", .stdVecOwned
            ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
            1 10)),
          (("c0", .i32 (BitVec.ofNat 32 1))),
          (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
          (("n", .u64 (BitVec.ofNat 64 10))),
          ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] :=
    memEvalExpr_lit _ _ _ _
  have hstepC1 : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "c1" (.i 32) (.lit (.i32 (BitVec.ofNat 32 3))))
      [(("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      .ok ((([(("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], emptyMem, [])),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
      mhlitC1 hlitC1
  -- Step 7: second push (`3` at index `1`).
  have hargs2 : lookupArgs
      [(("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v2", "c1"] =
      some [.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
        1 10,
        .i32 (BitVec.ofNat 32 3)] := by
    simp [lookupArgs, envLookup,
      show ("v2" : String) ≠ "c1" by decide]
  have hcallP2 : memEvalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
        1 10,
        .i32 (BitVec.ofNat 32 3)] =
      stdVecPushBackFwd
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
        1 10 (BitVec.ofNat 32 3) :=
    memEvalProgFunc_stdVecPushBack F' _ 1 10 _ rfl (by decide)
      (by decide) (by decide) (by decide) (by omega)
  have hcallP2' : memEvalProgFunc vecGrowProg F' stdVecPushBackFunc
      [.stdVecOwned
        ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
        1 10,
        .i32 (BitVec.ofNat 32 3)] =
      .ok (.stdVecOwned
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 3)), false⟩ 2 10) := by
    rw [hcallP2, vecInsertPush2_eq]
  have hstepV3 := memEvalProgStmt_callProg_ok vecGrowProg F' "v3"
      stdVecPushBackName ["v2", "c1"] _ emptyMem [] _
      stdVecPushBackFunc
      (.stdVecOwned
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 3)), false⟩ 2 10)
      hargs2 findFunc_stdVecPushBack hcallP2'
  -- Step 8: `begin` reads the base offset (`0`).
  have hargsB : lookupArgs
      [(("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v3"] =
      some [.stdVecOwned
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 3)), false⟩ 2 10] := by
    simp [lookupArgs, envLookup]
  have hcallB : memEvalFuncFuel (F' + 1) stdVecBeginFunc
      [.stdVecOwned
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 3)), false⟩ 2 10] =
      stdVecBeginFwd :=
    memEvalFuncFuel_stdVecBegin _ _ _ _
  have hcallB' : memEvalFuncFuel (F' + 1) stdVecBeginFunc
      [.stdVecOwned
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 3)), false⟩ 2 10] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    rw [hcallB]; rfl
  have hstepBpos := memEvalProgStmt_callRet_ok vecGrowProg (F' + 1)
      "bpos" stdVecBeginName ["v3"] _ emptyMem [] _
      stdVecBeginFunc
      (.u64 (BitVec.ofNat 64 0))
      hargsB findFunc_stdVecBegin hcallB'
  -- Step 9: `one = 1` (the `s64` step as `u64` bits).
  have hlitOne : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      [(("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have mhlitOne : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      [(("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        [(("bpos", .u64 (BitVec.ofNat 64 0))),
          (("v3", .stdVecOwned
            ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 3)), false⟩ 2 10)),
          (("c1", .i32 (BitVec.ofNat 32 3))),
          (("v2", .stdVecOwned
            ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
            1 10)),
          (("c0", .i32 (BitVec.ofNat 32 1))),
          (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
          (("n", .u64 (BitVec.ofNat 64 10))),
          ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] :=
    memEvalExpr_lit _ _ _ _
  have hstepOne : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "one" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      [(("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      .ok ((([(("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], emptyMem, [])),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
      mhlitOne hlitOne
  -- Step 10: `begin() + 1` advances to position `1`.
  have hargsP1 : lookupArgs
      [(("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["bpos", "one"] =
      some [.u64 (BitVec.ofNat 64 0), .u64 (BitVec.ofNat 64 1)] := by
    simp [lookupArgs, envLookup,
      show ("bpos" : String) ≠ "one" by decide]
  have hcallP1x : memEvalFuncFuel (F' + 1) stdVecPlusElFunc
      [.u64 (BitVec.ofNat 64 0), .u64 (BitVec.ofNat 64 1)] =
      stdVecPlusElFwd (BitVec.ofNat 64 0) (BitVec.ofNat 64 1) :=
    memEvalFuncFuel_stdVecPlusEl _ _ _
  have hcallP1x' : memEvalFuncFuel (F' + 1) stdVecPlusElFunc
      [.u64 (BitVec.ofNat 64 0), .u64 (BitVec.ofNat 64 1)] =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    rw [hcallP1x, vecInsertPlusEl_eq]
  have hstepP1 := memEvalProgStmt_callRet_ok vecGrowProg (F' + 1)
      "p1" stdVecPlusElName ["bpos", "one"] _ emptyMem [] _
      stdVecPlusElFunc
      (.u64 (BitVec.ofNat 64 1))
      hargsP1 findFunc_stdVecPlusEl hcallP1x'
  -- Step 11: `c2 = 2`.
  have hlitC2 : evalExpr (.lit (.i32 (BitVec.ofNat 32 2)))
      [(("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.i32 (BitVec.ofNat 32 2)) := by
    simp [evalExpr, litVal]
  have mhlitC2 : memEvalExpr (.lit (.i32 (BitVec.ofNat 32 2)))
      [(("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      evalExpr (.lit (.i32 (BitVec.ofNat 32 2)))
        [(("p1", .u64 (BitVec.ofNat 64 1))),
          (("one", .u64 (BitVec.ofNat 64 1))),
          (("bpos", .u64 (BitVec.ofNat 64 0))),
          (("v3", .stdVecOwned
            ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 3)), false⟩ 2 10)),
          (("c1", .i32 (BitVec.ofNat 32 3))),
          (("v2", .stdVecOwned
            ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
            1 10)),
          (("c0", .i32 (BitVec.ofNat 32 1))),
          (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
          (("n", .u64 (BitVec.ofNat 64 10))),
          ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] :=
    memEvalExpr_lit _ _ _ _
  have hstepC2 : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "c2" (.i 32) (.lit (.i32 (BitVec.ofNat 32 2))))
      [(("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      .ok ((([(("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], emptyMem, [])),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
      mhlitC2 hlitC2
  -- Step 12: the `insert` at position `1` (aux arm: room, `pos ≠ len`).
  have hargsV4 : lookupArgs
      [(("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v3", "p1", "c2"] =
      some [.stdVecOwned
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 3)), false⟩ 2 10,
        .u64 (BitVec.ofNat 64 1), .i32 (BitVec.ofNat 32 2)] := by
    simp [lookupArgs, envLookup,
      show ("v3" : String) ≠ "c2" by decide,
      show ("v3" : String) ≠ "p1" by decide,
      show ("v3" : String) ≠ "one" by decide,
      show ("v3" : String) ≠ "bpos" by decide,
      show ("p1" : String) ≠ "c2" by decide]
  have hcallV4 : memEvalProgFunc vecGrowProg F' stdVecInsertFunc
      [.stdVecOwned
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 3)), false⟩ 2 10,
        .u64 (BitVec.ofNat 64 1), .i32 (BitVec.ofNat 32 2)] =
      stdVecInsertFwd
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 3)), false⟩ 2 10
        (BitVec.ofNat 64 1) (BitVec.ofNat 32 2) :=
    memEvalProgFunc_stdVecInsert F' _ 2 10 _ _ rfl (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by omega)
  have hcallV4' : memEvalProgFunc vecGrowProg F' stdVecInsertFunc
      [.stdVecOwned
        ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 3)), false⟩ 2 10,
        .u64 (BitVec.ofNat 64 1), .i32 (BitVec.ofNat 32 2)] =
      .ok (.stdVecOwned ⟨((((((List.replicate 10 0).set 0
        (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
        (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
        (BitVec.ofNat 32 2)), false⟩ 3 10) := by
    rw [hcallV4, vecInsertStep_eq]
  have hstepV4 := memEvalProgStmt_callProg_ok vecGrowProg F' "v4"
      stdVecInsertName ["v3", "p1", "c2"] _ emptyMem [] _
      stdVecInsertFunc
      (.stdVecOwned ⟨((((((List.replicate 10 0).set 0
        (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
        (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
        (BitVec.ofNat 32 2)), false⟩ 3 10)
      hargsV4 findFunc_stdVecInsert hcallV4'
  -- Step 13: `n0 = 0`.
  have hlitN0 : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [(("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
        (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
        (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
        (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  have mhlitN0 : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [(("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
        (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
        (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
        (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [(("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
          (("c2", .i32 (BitVec.ofNat 32 2))),
          (("p1", .u64 (BitVec.ofNat 64 1))),
          (("one", .u64 (BitVec.ofNat 64 1))),
          (("bpos", .u64 (BitVec.ofNat 64 0))),
          (("v3", .stdVecOwned
            ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 3)), false⟩ 2 10)),
          (("c1", .i32 (BitVec.ofNat 32 3))),
          (("v2", .stdVecOwned
            ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
            1 10)),
          (("c0", .i32 (BitVec.ofNat 32 1))),
          (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
          (("n", .u64 (BitVec.ofNat 64 10))),
          ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] :=
    memEvalExpr_lit _ _ _ _
  have hstepN0 : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "n0" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      [(("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
        (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
        (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
        (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      .ok ((([(("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], emptyMem, [])),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
      mhlitN0 hlitN0
  -- Step 14: first read pins `1`.
  have hargsE0 : lookupArgs
      [(("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v4", "n0"] =
      some [.stdVecOwned ⟨((((((List.replicate 10 0).set 0
        (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
        (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
        (BitVec.ofNat 32 2)), false⟩ 3 10,
        .u64 (BitVec.ofNat 64 0)] := by
    simp [lookupArgs, envLookup,
      show ("v4" : String) ≠ "n0" by decide]
  have hget0 : ((((((List.replicate 10 0).set 0
      (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
      (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
      (BitVec.ofNat 32 2))[(BitVec.ofNat 64 0).toNat]? =
      some (BitVec.ofNat 32 1) := by decide
  have hlt0 : (BitVec.ofNat 64 0).toNat < 3 := by decide
  have hcallE0 : memEvalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned ⟨((((((List.replicate 10 0).set 0
        (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
        (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
        (BitVec.ofNat 32 2)), false⟩ 3 10,
        .u64 (BitVec.ofNat 64 0)] =
      stdVecGrowIndexFwd
        ⟨((((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 1 (BitVec.ofNat 32 2)), false⟩ 3
        (BitVec.ofNat 64 0) :=
    memEvalFuncFuel_stdVecGrowIndex _ _ 3 10 _ rfl _ hget0 hlt0
  have hcallE0' : memEvalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned ⟨((((((List.replicate 10 0).set 0
        (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
        (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
        (BitVec.ofNat 32 2)), false⟩ 3 10,
        .u64 (BitVec.ofNat 64 0)] =
      .ok (.i32 (BitVec.ofNat 32 1)) := by
    rw [hcallE0, vecInsertRead0_eq]
  have hstepE0 := memEvalProgStmt_callRet_ok vecGrowProg (F' + 1)
      "e0" stdVecGrowIndexName ["v4", "n0"] _ emptyMem [] _
      stdVecGrowIndexFunc
      (.i32 (BitVec.ofNat 32 1))
      hargsE0 findFunc_stdVecGrowIndex hcallE0'
  -- Step 15: `n1 = 1`.
  have hlitN1 : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      [(("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have mhlitN1 : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      [(("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        [(("e0", .i32 (BitVec.ofNat 32 1))),
          (("n0", .u64 (BitVec.ofNat 64 0))),
          (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
            (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
            (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 2)), false⟩ 3 10)),
          (("c2", .i32 (BitVec.ofNat 32 2))),
          (("p1", .u64 (BitVec.ofNat 64 1))),
          (("one", .u64 (BitVec.ofNat 64 1))),
          (("bpos", .u64 (BitVec.ofNat 64 0))),
          (("v3", .stdVecOwned
            ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 3)), false⟩ 2 10)),
          (("c1", .i32 (BitVec.ofNat 32 3))),
          (("v2", .stdVecOwned
            ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
            1 10)),
          (("c0", .i32 (BitVec.ofNat 32 1))),
          (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
          (("n", .u64 (BitVec.ofNat 64 10))),
          ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] :=
    memEvalExpr_lit _ _ _ _
  have hstepN1 : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "n1" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      [(("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      .ok ((([(("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], emptyMem, [])),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
      mhlitN1 hlitN1
  -- Step 16: second read pins `2`.
  have hargsE1 : lookupArgs
      [(("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v4", "n1"] =
      some [.stdVecOwned ⟨((((((List.replicate 10 0).set 0
        (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
        (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
        (BitVec.ofNat 32 2)), false⟩ 3 10,
        .u64 (BitVec.ofNat 64 1)] := by
    simp [lookupArgs, envLookup,
      show ("v4" : String) ≠ "n1" by decide,
      show ("v4" : String) ≠ "e0" by decide,
      show ("v4" : String) ≠ "n0" by decide]
  have hget1 : ((((((List.replicate 10 0).set 0
      (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
      (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
      (BitVec.ofNat 32 2))[(BitVec.ofNat 64 1).toNat]? =
      some (BitVec.ofNat 32 2) := by decide
  have hlt1 : (BitVec.ofNat 64 1).toNat < 3 := by decide
  have hcallE1 : memEvalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned ⟨((((((List.replicate 10 0).set 0
        (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
        (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
        (BitVec.ofNat 32 2)), false⟩ 3 10,
        .u64 (BitVec.ofNat 64 1)] =
      stdVecGrowIndexFwd
        ⟨((((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 1 (BitVec.ofNat 32 2)), false⟩ 3
        (BitVec.ofNat 64 1) :=
    memEvalFuncFuel_stdVecGrowIndex _ _ 3 10 _ rfl _ hget1 hlt1
  have hcallE1' : memEvalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned ⟨((((((List.replicate 10 0).set 0
        (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
        (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
        (BitVec.ofNat 32 2)), false⟩ 3 10,
        .u64 (BitVec.ofNat 64 1)] =
      .ok (.i32 (BitVec.ofNat 32 2)) := by
    rw [hcallE1, vecInsertRead1_eq]
  have hstepE1 := memEvalProgStmt_callRet_ok vecGrowProg (F' + 1)
      "e1" stdVecGrowIndexName ["v4", "n1"] _ emptyMem [] _
      stdVecGrowIndexFunc
      (.i32 (BitVec.ofNat 32 2))
      hargsE1 findFunc_stdVecGrowIndex hcallE1'
  -- Step 17: `s01 = e0 + e1 = 3`.
  have he0 : envLookup
      [(("e1", .i32 (BitVec.ofNat 32 2))),
        (("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] "e0" =
      some (.i32 (BitVec.ofNat 32 1)) := by
    simp [envLookup,
      show ("e0" : String) ≠ "e1" by decide,
      show ("e0" : String) ≠ "n1" by decide]
  have he1 : envLookup
      [(("e1", .i32 (BitVec.ofNat 32 2))),
        (("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] "e1" =
      some (.i32 (BitVec.ofNat 32 2)) := by
    simp [envLookup]
  have hs01E : evalExpr (.add (.var "e0") (.var "e1"))
      [(("e1", .i32 (BitVec.ofNat 32 2))),
        (("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.i32 (BitVec.ofNat 32 3)) := by
    cir_step evalExpr [he0, he1, vecReserveAdd_eq]
  have mhs01agree : memEvalExpr (.add (.var "e0") (.var "e1"))
      [(("e1", .i32 (BitVec.ofNat 32 2))),
        (("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      evalExpr (.add (.var "e0") (.var "e1"))
        [(("e1", .i32 (BitVec.ofNat 32 2))),
          (("n1", .u64 (BitVec.ofNat 64 1))),
          (("e0", .i32 (BitVec.ofNat 32 1))),
          (("n0", .u64 (BitVec.ofNat 64 0))),
          (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
            (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
            (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 2)), false⟩ 3 10)),
          (("c2", .i32 (BitVec.ofNat 32 2))),
          (("p1", .u64 (BitVec.ofNat 64 1))),
          (("one", .u64 (BitVec.ofNat 64 1))),
          (("bpos", .u64 (BitVec.ofNat 64 0))),
          (("v3", .stdVecOwned
            ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 3)), false⟩ 2 10)),
          (("c1", .i32 (BitVec.ofNat 32 3))),
          (("v2", .stdVecOwned
            ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
            1 10)),
          (("c0", .i32 (BitVec.ofNat 32 1))),
          (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
          (("n", .u64 (BitVec.ofNat 64 10))),
          ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] := by
    simp only [memEvalExpr, evalExpr, he0, he1]
  have mhs01E_ok : memEvalExpr (.add (.var "e0") (.var "e1"))
      [(("e1", .i32 (BitVec.ofNat 32 2))),
        (("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      .ok (.i32 (BitVec.ofNat 32 3)) := by
    rw [mhs01agree]; exact hs01E
  have hstepS01 : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "s01" (.i 32) (.add (.var "e0") (.var "e1")))
      [(("e1", .i32 (BitVec.ofNat 32 2))),
        (("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      .ok ((([(("s01", .i32 (BitVec.ofNat 32 3))),
        (("e1", .i32 (BitVec.ofNat 32 2))),
        (("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], emptyMem, [])),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
      mhs01agree hs01E
  -- Step 18: `n2 = 2`.
  have hlitN2 : evalExpr (.lit (.u64 (BitVec.ofNat 64 2)))
      [(("s01", .i32 (BitVec.ofNat 32 3))),
        (("e1", .i32 (BitVec.ofNat 32 2))),
        (("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.u64 (BitVec.ofNat 64 2)) := by
    simp [evalExpr, litVal]
  have mhlitN2 : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 2)))
      [(("s01", .i32 (BitVec.ofNat 32 3))),
        (("e1", .i32 (BitVec.ofNat 32 2))),
        (("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 2)))
        [(("s01", .i32 (BitVec.ofNat 32 3))),
          (("e1", .i32 (BitVec.ofNat 32 2))),
          (("n1", .u64 (BitVec.ofNat 64 1))),
          (("e0", .i32 (BitVec.ofNat 32 1))),
          (("n0", .u64 (BitVec.ofNat 64 0))),
          (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
            (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
            (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 2)), false⟩ 3 10)),
          (("c2", .i32 (BitVec.ofNat 32 2))),
          (("p1", .u64 (BitVec.ofNat 64 1))),
          (("one", .u64 (BitVec.ofNat 64 1))),
          (("bpos", .u64 (BitVec.ofNat 64 0))),
          (("v3", .stdVecOwned
            ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 3)), false⟩ 2 10)),
          (("c1", .i32 (BitVec.ofNat 32 3))),
          (("v2", .stdVecOwned
            ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
            1 10)),
          (("c0", .i32 (BitVec.ofNat 32 1))),
          (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
          (("n", .u64 (BitVec.ofNat 64 10))),
          ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] :=
    memEvalExpr_lit _ _ _ _
  have hstepN2 : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "n2" (.u 64) (.lit (.u64 (BitVec.ofNat 64 2))))
      [(("s01", .i32 (BitVec.ofNat 32 3))),
        (("e1", .i32 (BitVec.ofNat 32 2))),
        (("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      .ok ((([(("n2", .u64 (BitVec.ofNat 64 2))),
        (("s01", .i32 (BitVec.ofNat 32 3))),
        (("e1", .i32 (BitVec.ofNat 32 2))),
        (("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], emptyMem, [])),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
      mhlitN2 hlitN2
  -- Step 19: third read pins `3`.
  have hargsE2 : lookupArgs
      [(("n2", .u64 (BitVec.ofNat 64 2))),
        (("s01", .i32 (BitVec.ofNat 32 3))),
        (("e1", .i32 (BitVec.ofNat 32 2))),
        (("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v4", "n2"] =
      some [.stdVecOwned ⟨((((((List.replicate 10 0).set 0
        (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
        (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
        (BitVec.ofNat 32 2)), false⟩ 3 10,
        .u64 (BitVec.ofNat 64 2)] := by
    simp [lookupArgs, envLookup,
      show ("v4" : String) ≠ "n2" by decide,
      show ("v4" : String) ≠ "s01" by decide,
      show ("v4" : String) ≠ "e1" by decide,
      show ("v4" : String) ≠ "n1" by decide,
      show ("v4" : String) ≠ "e0" by decide,
      show ("v4" : String) ≠ "n0" by decide]
  have hget2 : ((((((List.replicate 10 0).set 0
      (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
      (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
      (BitVec.ofNat 32 2))[(BitVec.ofNat 64 2).toNat]? =
      some (BitVec.ofNat 32 3) := by decide
  have hlt2 : (BitVec.ofNat 64 2).toNat < 3 := by decide
  have hcallE2 : memEvalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned ⟨((((((List.replicate 10 0).set 0
        (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
        (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
        (BitVec.ofNat 32 2)), false⟩ 3 10,
        .u64 (BitVec.ofNat 64 2)] =
      stdVecGrowIndexFwd
        ⟨((((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 1 (BitVec.ofNat 32 2)), false⟩ 3
        (BitVec.ofNat 64 2) :=
    memEvalFuncFuel_stdVecGrowIndex _ _ 3 10 _ rfl _ hget2 hlt2
  have hcallE2' : memEvalFuncFuel (F' + 1) stdVecGrowIndexFunc
      [.stdVecOwned ⟨((((((List.replicate 10 0).set 0
        (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
        (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
        (BitVec.ofNat 32 2)), false⟩ 3 10,
        .u64 (BitVec.ofNat 64 2)] =
      .ok (.i32 (BitVec.ofNat 32 3)) := by
    rw [hcallE2, vecInsertRead2_eq]
  have hstepE2 := memEvalProgStmt_callRet_ok vecGrowProg (F' + 1)
      "e2" stdVecGrowIndexName ["v4", "n2"] _ emptyMem [] _
      stdVecGrowIndexFunc
      (.i32 (BitVec.ofNat 32 3))
      hargsE2 findFunc_stdVecGrowIndex hcallE2'
  -- Step 20: `s = s01 + e2 = 6`.
  have hs01 : envLookup
      [(("e2", .i32 (BitVec.ofNat 32 3))),
        (("n2", .u64 (BitVec.ofNat 64 2))),
        (("s01", .i32 (BitVec.ofNat 32 3))),
        (("e1", .i32 (BitVec.ofNat 32 2))),
        (("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] "s01" =
      some (.i32 (BitVec.ofNat 32 3)) := by
    simp [envLookup,
      show ("s01" : String) ≠ "e2" by decide,
      show ("s01" : String) ≠ "n2" by decide]
  have he2 : envLookup
      [(("e2", .i32 (BitVec.ofNat 32 3))),
        (("n2", .u64 (BitVec.ofNat 64 2))),
        (("s01", .i32 (BitVec.ofNat 32 3))),
        (("e1", .i32 (BitVec.ofNat 32 2))),
        (("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] "e2" =
      some (.i32 (BitVec.ofNat 32 3)) := by
    simp [envLookup]
  have hsE : evalExpr (.add (.var "s01") (.var "e2"))
      [(("e2", .i32 (BitVec.ofNat 32 3))),
        (("n2", .u64 (BitVec.ofNat 64 2))),
        (("s01", .i32 (BitVec.ofNat 32 3))),
        (("e1", .i32 (BitVec.ofNat 32 2))),
        (("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.i32 (BitVec.ofNat 32 6)) := by
    cir_step evalExpr [hs01, he2, vecInsertAdd2_eq]
  have mhsagree : memEvalExpr (.add (.var "s01") (.var "e2"))
      [(("e2", .i32 (BitVec.ofNat 32 3))),
        (("n2", .u64 (BitVec.ofNat 64 2))),
        (("s01", .i32 (BitVec.ofNat 32 3))),
        (("e1", .i32 (BitVec.ofNat 32 2))),
        (("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      evalExpr (.add (.var "s01") (.var "e2"))
        [(("e2", .i32 (BitVec.ofNat 32 3))),
          (("n2", .u64 (BitVec.ofNat 64 2))),
          (("s01", .i32 (BitVec.ofNat 32 3))),
          (("e1", .i32 (BitVec.ofNat 32 2))),
          (("n1", .u64 (BitVec.ofNat 64 1))),
          (("e0", .i32 (BitVec.ofNat 32 1))),
          (("n0", .u64 (BitVec.ofNat 64 0))),
          (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
            (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
            (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
            (BitVec.ofNat 32 2)), false⟩ 3 10)),
          (("c2", .i32 (BitVec.ofNat 32 2))),
          (("p1", .u64 (BitVec.ofNat 64 1))),
          (("one", .u64 (BitVec.ofNat 64 1))),
          (("bpos", .u64 (BitVec.ofNat 64 0))),
          (("v3", .stdVecOwned
            ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
              (BitVec.ofNat 32 3)), false⟩ 2 10)),
          (("c1", .i32 (BitVec.ofNat 32 3))),
          (("v2", .stdVecOwned
            ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
            1 10)),
          (("c0", .i32 (BitVec.ofNat 32 1))),
          (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
          (("n", .u64 (BitVec.ofNat 64 10))),
          ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] := by
    simp only [memEvalExpr, evalExpr, hs01, he2]
  have mhsE_ok : memEvalExpr (.add (.var "s01") (.var "e2"))
      [(("e2", .i32 (BitVec.ofNat 32 3))),
        (("n2", .u64 (BitVec.ofNat 64 2))),
        (("s01", .i32 (BitVec.ofNat 32 3))),
        (("e1", .i32 (BitVec.ofNat 32 2))),
        (("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      .ok (.i32 (BitVec.ofNat 32 6)) := by
    rw [mhsagree]; exact hsE
  have hstepS : memEvalProgStmt vecGrowProg (F' + 1)
      (.let_ "s" (.i 32) (.add (.var "s01") (.var "e2")))
      [(("e2", .i32 (BitVec.ofNat 32 3))),
        (("n2", .u64 (BitVec.ofNat 64 2))),
        (("s01", .i32 (BitVec.ofNat 32 3))),
        (("e1", .i32 (BitVec.ofNat 32 2))),
        (("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      .ok ((([(("s", .i32 (BitVec.ofNat 32 6))),
        (("e2", .i32 (BitVec.ofNat 32 3))),
        (("n2", .u64 (BitVec.ofNat 64 2))),
        (("s01", .i32 (BitVec.ofNat 32 3))),
        (("e1", .i32 (BitVec.ofNat 32 2))),
        (("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], emptyMem, [])),
        .fellThrough) := by
    rw [memEvalProgStmt_let_fb]
    exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
      (fun _ => by simp) (fun _ => by simp) (fun _ => by simp)
      mhsagree hsE
  -- Step 21: destructor frees the triple.
  have hargsD : lookupArgs
      [(("s", .i32 (BitVec.ofNat 32 6))),
        (("e2", .i32 (BitVec.ofNat 32 3))),
        (("n2", .u64 (BitVec.ofNat 64 2))),
        (("s01", .i32 (BitVec.ofNat 32 3))),
        (("e1", .i32 (BitVec.ofNat 32 2))),
        (("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] ["v4"] =
      some [.stdVecOwned ⟨((((((List.replicate 10 0).set 0
        (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
        (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
        (BitVec.ofNat 32 2)), false⟩ 3 10] := by
    simp [lookupArgs, envLookup,
      show ("v4" : String) ≠ "s" by decide,
      show ("v4" : String) ≠ "e2" by decide,
      show ("v4" : String) ≠ "n2" by decide,
      show ("v4" : String) ≠ "s01" by decide,
      show ("v4" : String) ≠ "e1" by decide,
      show ("v4" : String) ≠ "n1" by decide,
      show ("v4" : String) ≠ "e0" by decide,
      show ("v4" : String) ≠ "n0" by decide]
  have hcallD : memEvalFuncFuel (F' + 1) stdVecDtorFunc
      [.stdVecOwned ⟨((((((List.replicate 10 0).set 0
        (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
        (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
        (BitVec.ofNat 32 2)), false⟩ 3 10] =
      stdVecDtorFwd
        ⟨((((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 1 (BitVec.ofNat 32 2)), false⟩ 3
        10 :=
    memEvalFuncFuel_stdVecDtor _ _ _ _ (by decide) rfl
  have hcallD' : memEvalFuncFuel (F' + 1) stdVecDtorFunc
      [.stdVecOwned ⟨((((((List.replicate 10 0).set 0
        (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
        (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
        (BitVec.ofNat 32 2)), false⟩ 3 10] =
      .ok (.stdVecOwned
        ⟨((((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 1 (BitVec.ofNat 32 2)), true⟩
        3 10) := by
    rw [hcallD, vecInsertDtor_eq]
  have hstepV5 := memEvalProgStmt_callRet_ok vecGrowProg (F' + 1)
      "v5" stdVecDtorName ["v4"] _ emptyMem [] _
      stdVecDtorFunc
      (.stdVecOwned
        ⟨((((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 1 (BitVec.ofNat 32 2)), true⟩
        3 10)
      hargsD findFunc_stdVecDtor hcallD'
  -- Step 22: return `6`.
  have hrE : evalExpr (.var "s")
      [(("v5", .stdVecOwned
        ⟨((((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 1 (BitVec.ofNat 32 2)), true⟩
        3 10)),
        (("s", .i32 (BitVec.ofNat 32 6))),
        (("e2", .i32 (BitVec.ofNat 32 3))),
        (("n2", .u64 (BitVec.ofNat 64 2))),
        (("s01", .i32 (BitVec.ofNat 32 3))),
        (("e1", .i32 (BitVec.ofNat 32 2))),
        (("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] =
      .ok (.i32 (BitVec.ofNat 32 6)) := by
    simp [evalExpr, envLookup]
  have mhrE : memEvalExpr (.var "s")
      [(("v5", .stdVecOwned
        ⟨((((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 1 (BitVec.ofNat 32 2)), true⟩
        3 10)),
        (("s", .i32 (BitVec.ofNat 32 6))),
        (("e2", .i32 (BitVec.ofNat 32 3))),
        (("n2", .u64 (BitVec.ofNat 64 2))),
        (("s01", .i32 (BitVec.ofNat 32 3))),
        (("e1", .i32 (BitVec.ofNat 32 2))),
        (("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      .ok (.i32 (BitVec.ofNat 32 6)) := by
    rw [memEvalExpr_var _ _ _ _]; exact hrE
  have hret : memEvalProgStmt vecGrowProg (F' + 1)
      (.return_ (.var "s"))
      [(("v5", .stdVecOwned
        ⟨((((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 1 (BitVec.ofNat 32 2)), true⟩
        3 10)),
        (("s", .i32 (BitVec.ofNat 32 6))),
        (("e2", .i32 (BitVec.ofNat 32 3))),
        (("n2", .u64 (BitVec.ofNat 64 2))),
        (("s01", .i32 (BitVec.ofNat 32 3))),
        (("e1", .i32 (BitVec.ofNat 32 2))),
        (("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)] emptyMem [] =
      .ok ((([(("v5", .stdVecOwned
        ⟨((((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 1 (BitVec.ofNat 32 2)), true⟩
        3 10)),
        (("s", .i32 (BitVec.ofNat 32 6))),
        (("e2", .i32 (BitVec.ofNat 32 3))),
        (("n2", .u64 (BitVec.ofNat 64 2))),
        (("s01", .i32 (BitVec.ofNat 32 3))),
        (("e1", .i32 (BitVec.ofNat 32 2))),
        (("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], emptyMem, []),
        .returned (.i32 (BitVec.ofNat 32 6)))) :=
    memEvalProgStmt_return vecGrowProg (F' + 1) _ _ _ _ _ mhrE
  have hstmt : memEvalProgStmt vecGrowProg (F' + 1)
      vecInsertSumEntryFunc.body [] emptyMem [] =
      .ok ((([(("v5", .stdVecOwned
        ⟨((((((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 1 (BitVec.ofNat 32 2)), true⟩
        3 10)),
        (("s", .i32 (BitVec.ofNat 32 6))),
        (("e2", .i32 (BitVec.ofNat 32 3))),
        (("n2", .u64 (BitVec.ofNat 64 2))),
        (("s01", .i32 (BitVec.ofNat 32 3))),
        (("e1", .i32 (BitVec.ofNat 32 2))),
        (("n1", .u64 (BitVec.ofNat 64 1))),
        (("e0", .i32 (BitVec.ofNat 32 1))),
        (("n0", .u64 (BitVec.ofNat 64 0))),
        (("v4", .stdVecOwned ⟨((((((List.replicate 10 0).set 0
          (BitVec.ofNat 32 1)).set 1 (BitVec.ofNat 32 3)).set 2
          (BitVec.ofNat 32 3)).set 2 (BitVec.ofNat 32 3)).set 1
          (BitVec.ofNat 32 2)), false⟩ 3 10)),
        (("c2", .i32 (BitVec.ofNat 32 2))),
        (("p1", .u64 (BitVec.ofNat 64 1))),
        (("one", .u64 (BitVec.ofNat 64 1))),
        (("bpos", .u64 (BitVec.ofNat 64 0))),
        (("v3", .stdVecOwned
          ⟨(((List.replicate 10 0).set 0 (BitVec.ofNat 32 1)).set 1
            (BitVec.ofNat 32 3)), false⟩ 2 10)),
        (("c1", .i32 (BitVec.ofNat 32 3))),
        (("v2", .stdVecOwned
          ⟨(List.replicate 10 0).set 0 (BitVec.ofNat 32 1), false⟩
          1 10)),
        (("c0", .i32 (BitVec.ofNat 32 1))),
        (("v1", .stdVecOwned ⟨List.replicate 10 0, false⟩ 0 10)),
        (("n", .u64 (BitVec.ofNat 64 10))),
        ("v0", .stdVecOwned ⟨[], false⟩ 0 0)], emptyMem, []),
        .returned (.i32 (BitVec.ofNat 32 6)))) := by
    rw [hbody]
    exact (memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
      hstepV0).trans
      ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
        hstepN).trans
        ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
          hstepV1).trans
          ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
            hstepC0).trans
            ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
              hstepV2).trans
              ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                hstepC1).trans
                ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                  hstepV3).trans
                  ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                    hstepBpos).trans
                    ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                      hstepOne).trans
                      ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                        hstepP1).trans
                        ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                          hstepC2).trans
                          ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                            hstepV4).trans
                            ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                              hstepN0).trans
                              ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                                hstepE0).trans
                                ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                                  hstepN1).trans
                                  ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                                    hstepE1).trans
                                    ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                                      hstepS01).trans
                                      ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                                        hstepN2).trans
                                        ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                                          hstepE2).trans
                                          ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                                            hstepS).trans
                                            ((memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _
                                              hstepV5).trans
                                              hret))))))))))))))))))))
  have hfwd : vecInsertSumEntryFwd = .ok (.i32 (BitVec.ofNat 32 6)) := by
    simp only [vecInsertSumEntryFwd, vecReserveStep_eq,
      vecReservePush1_eq, vecInsertPush2_eq, vecInsertPlusEl_eq,
      vecInsertStep_eq, vecInsertRead0_eq, vecInsertRead1_eq,
      vecInsertRead2_eq, vecReserveAdd_eq, vecInsertAdd2_eq,
      vecInsertDtor_eq, vecGrow_bind_ok, vecGrowOwned, vecGrowU64,
      vecGrowI32, stdVecBeginFwd]
  simp only [memEvalProgFunc, hbind, hstmt, hfwd]

/-- Transfer for `vec_insert_sum`: memory execution agrees with value
    execution (both sides compute `6`; precedes
    `memTransfer_vecPushSumEntry`). -/
theorem memTransfer_vecInsertSumEntry (F : Nat) (hF : 6 ≤ F)
    (_h : oracleNoalias vecInsertSumEntryFunc []) :
    memEvalProgFunc vecGrowProg F vecInsertSumEntryFunc [] =
      evalProgFunc vecGrowProg F vecInsertSumEntryFunc [] := by
  rw [memEvalProgFunc_vecInsertSumEntry F hF,
    evalProgFunc_vecInsertSumEntry F hF]
