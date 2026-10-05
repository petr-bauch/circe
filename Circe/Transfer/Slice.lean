/-
Circe.Transfer.Slice — N4d-i/ii/iii/iv-a slice transfers plus the M3d `methodSum` leaf.
Over `Circe.Transfer.Flow`.
-/
import Circe.Transfer.Flow

/-! ## N4d-i `std::array` transfers: reads agree, hit and `OOB` -/

/-- `memEval` for `_S_ref` (hit): the memory load agrees with the
    value read (mirrors `evalFuncFuel_arrayRef`). -/
theorem memEvalFuncFuel_arrayRef (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64) (x : BitVec 32)
    (hidx : l[n.toNat]? = some x) :
    memEvalFuncFuel F arrayRefFunc [.arr32 l, .u64 n] =
      arrayRefFwd l n := by
  have hb : bindMemArgs arrayRefFunc.args [.arr32 l, .u64 n] emptyMem =
      some ([("t", .arr32 l), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, true, l⟩)], []⟩, [("t", 0, 0)]) :=
    bindMemArgs_arrayRef l n
  have hbody : arrayRefFunc.body =
      .return_ (.idxi "t" (.var "n")) := rfl
  have harr : envLookup [("t", .arr32 l), ("n", .u64 n)] "t" =
      some (.arr32 l) := by
    simp [envLookup]
  have hn : envLookup [("t", .arr32 l), ("n", .u64 n)] "n" =
      some (.u64 n) := by
    simp [envLookup, show ("n" : String) ≠ "t" by decide]
  have hlay : layoutLookup [("t", 0, 0)] "t" = some (0, 0) := by
    simp [layoutLookup]
  have hmem : memLoad ⟨1, [(0, ⟨0, true, l⟩)], []⟩ 0 0 n.toNat =
      .ok x := by
    simp [memLoad, memFind, hidx]
  have hie : memEvalExpr (.var "n") [("t", .arr32 l), ("n", .u64 n)]
      ⟨1, [(0, ⟨0, true, l⟩)], []⟩ [("t", 0, 0)] =
      evalExpr (.var "n") [("t", .arr32 l), ("n", .u64 n)] := rfl
  have hieval : evalExpr (.var "n") [("t", .arr32 l), ("n", .u64 n)] =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  have hagree := memEvalExpr_idxi_hit "t" (.var "n") _ _ _ l n x 0 0
    hlay harr hie hieval hmem hidx
  have heval : evalExpr (.idxi "t" (.var "n"))
      [("t", .arr32 l), ("n", .u64 n)] = .ok (.i32 x) := by
    simp [evalExpr, harr, hn, hidx]
  have hret := memEvalStmtFuel_return F (.idxi "t" (.var "n")) _ _ _
    (.i32 x) hagree heval
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  simp [arrayRefFwd, hidx]

/-- `memEval` for `_S_ref` (`OOB`): both sides fail loudly together
    (mirrors `evalFuncFuel_arrayRef` on the miss path). -/
theorem memEvalFuncFuel_arrayRef_oob (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64)
    (hidx : l[n.toNat]? = none) :
    memEvalFuncFuel F arrayRefFunc [.arr32 l, .u64 n] =
      .error .OOB := by
  have hb : bindMemArgs arrayRefFunc.args [.arr32 l, .u64 n] emptyMem =
      some ([("t", .arr32 l), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, true, l⟩)], []⟩, [("t", 0, 0)]) :=
    bindMemArgs_arrayRef l n
  have hbody : arrayRefFunc.body =
      .return_ (.idxi "t" (.var "n")) := rfl
  have harr : envLookup [("t", .arr32 l), ("n", .u64 n)] "t" =
      some (.arr32 l) := by
    simp [envLookup]
  have hn : envLookup [("t", .arr32 l), ("n", .u64 n)] "n" =
      some (.u64 n) := by
    simp [envLookup, show ("n" : String) ≠ "t" by decide]
  have hlay : layoutLookup [("t", 0, 0)] "t" = some (0, 0) := by
    simp [layoutLookup]
  have hmem : memLoad ⟨1, [(0, ⟨0, true, l⟩)], []⟩ 0 0 n.toNat =
      .error .OOB := by
    simp [memLoad, memFind, hidx]
  have hie : memEvalExpr (.var "n") [("t", .arr32 l), ("n", .u64 n)]
      ⟨1, [(0, ⟨0, true, l⟩)], []⟩ [("t", 0, 0)] =
      evalExpr (.var "n") [("t", .arr32 l), ("n", .u64 n)] := rfl
  have hieval : evalExpr (.var "n") [("t", .arr32 l), ("n", .u64 n)] =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  have hagree := memEvalExpr_idxi_oob "t" (.var "n") _ _ _ l n 0 0
    hlay harr hie hieval hmem hidx
  have heval : evalExpr (.idxi "t" (.var "n"))
      [("t", .arr32 l), ("n", .u64 n)] = .error .OOB := by
    simp [evalExpr, harr, hn, hidx]
  have herr : memEvalExpr (.idxi "t" (.var "n"))
      [("t", .arr32 l), ("n", .u64 n)]
      ⟨1, [(0, ⟨0, true, l⟩)], []⟩ [("t", 0, 0)] = .error .OOB :=
    hagree.trans heval
  have hret := memEvalStmtFuel_return_err F (.idxi "t" (.var "n")) _ _ _
    .OOB herr
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]

/-- Transfer for `_S_ref` (hit): both sides equal `arrayRefFwd`. -/
theorem memTransfer_arrayRef (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64) (x : BitVec 32)
    (hidx : l[n.toNat]? = some x)
    (_h : oracleNoalias arrayRefFunc [.arr32 l, .u64 n]) :
    memEvalFuncFuel F arrayRefFunc [.arr32 l, .u64 n] =
      evalFuncFuel F arrayRefFunc [.arr32 l, .u64 n] := by
  rw [memEvalFuncFuel_arrayRef F l n x hidx, evalFuncFuel_arrayRef]

/-- Transfer for `_S_ref` (`OOB`): both sides fail loudly. -/
theorem memTransfer_arrayRef_oob (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64)
    (hidx : l[n.toNat]? = none)
    (_h : oracleNoalias arrayRefFunc [.arr32 l, .u64 n]) :
    memEvalFuncFuel F arrayRefFunc [.arr32 l, .u64 n] =
      evalFuncFuel F arrayRefFunc [.arr32 l, .u64 n] := by
  rw [memEvalFuncFuel_arrayRef_oob F l n hidx, evalFuncFuel_arrayRef,
    arrayRefFwd, hidx]

/-- `memEval` for `operator[]` (hit): same read through the fused
    edge (mirrors `evalFuncFuel_arrayAt`). -/
theorem memEvalFuncFuel_arrayAt (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64) (x : BitVec 32)
    (hidx : l[n.toNat]? = some x) :
    memEvalFuncFuel F arrayAtFunc [.arr32 l, .u64 n] =
      arrayAtFwd l n := by
  have hb : bindMemArgs arrayAtFunc.args [.arr32 l, .u64 n] emptyMem =
      some ([("a", .arr32 l), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, true, l⟩)], []⟩, [("a", 0, 0)]) :=
    bindMemArgs_arrayAt l n
  have hbody : arrayAtFunc.body =
      .return_ (.idxi "a" (.var "n")) := rfl
  have harr : envLookup [("a", .arr32 l), ("n", .u64 n)] "a" =
      some (.arr32 l) := by
    simp [envLookup]
  have hn : envLookup [("a", .arr32 l), ("n", .u64 n)] "n" =
      some (.u64 n) := by
    simp [envLookup, show ("n" : String) ≠ "a" by decide]
  have hlay : layoutLookup [("a", 0, 0)] "a" = some (0, 0) := by
    simp [layoutLookup]
  have hmem : memLoad ⟨1, [(0, ⟨0, true, l⟩)], []⟩ 0 0 n.toNat =
      .ok x := by
    simp [memLoad, memFind, hidx]
  have hie : memEvalExpr (.var "n") [("a", .arr32 l), ("n", .u64 n)]
      ⟨1, [(0, ⟨0, true, l⟩)], []⟩ [("a", 0, 0)] =
      evalExpr (.var "n") [("a", .arr32 l), ("n", .u64 n)] := rfl
  have hieval : evalExpr (.var "n") [("a", .arr32 l), ("n", .u64 n)] =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  have hagree := memEvalExpr_idxi_hit "a" (.var "n") _ _ _ l n x 0 0
    hlay harr hie hieval hmem hidx
  have heval : evalExpr (.idxi "a" (.var "n"))
      [("a", .arr32 l), ("n", .u64 n)] = .ok (.i32 x) := by
    simp [evalExpr, harr, hn, hidx]
  have hret := memEvalStmtFuel_return F (.idxi "a" (.var "n")) _ _ _
    (.i32 x) hagree heval
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  simp [arrayAtFwd, arrayRefFwd, hidx]

/-- `memEval` for `operator[]` (`OOB`): both sides fail loudly. -/
theorem memEvalFuncFuel_arrayAt_oob (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64)
    (hidx : l[n.toNat]? = none) :
    memEvalFuncFuel F arrayAtFunc [.arr32 l, .u64 n] =
      .error .OOB := by
  have hb : bindMemArgs arrayAtFunc.args [.arr32 l, .u64 n] emptyMem =
      some ([("a", .arr32 l), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, true, l⟩)], []⟩, [("a", 0, 0)]) :=
    bindMemArgs_arrayAt l n
  have hbody : arrayAtFunc.body =
      .return_ (.idxi "a" (.var "n")) := rfl
  have harr : envLookup [("a", .arr32 l), ("n", .u64 n)] "a" =
      some (.arr32 l) := by
    simp [envLookup]
  have hn : envLookup [("a", .arr32 l), ("n", .u64 n)] "n" =
      some (.u64 n) := by
    simp [envLookup, show ("n" : String) ≠ "a" by decide]
  have hlay : layoutLookup [("a", 0, 0)] "a" = some (0, 0) := by
    simp [layoutLookup]
  have hmem : memLoad ⟨1, [(0, ⟨0, true, l⟩)], []⟩ 0 0 n.toNat =
      .error .OOB := by
    simp [memLoad, memFind, hidx]
  have hie : memEvalExpr (.var "n") [("a", .arr32 l), ("n", .u64 n)]
      ⟨1, [(0, ⟨0, true, l⟩)], []⟩ [("a", 0, 0)] =
      evalExpr (.var "n") [("a", .arr32 l), ("n", .u64 n)] := rfl
  have hieval : evalExpr (.var "n") [("a", .arr32 l), ("n", .u64 n)] =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  have hagree := memEvalExpr_idxi_oob "a" (.var "n") _ _ _ l n 0 0
    hlay harr hie hieval hmem hidx
  have heval : evalExpr (.idxi "a" (.var "n"))
      [("a", .arr32 l), ("n", .u64 n)] = .error .OOB := by
    simp [evalExpr, harr, hn, hidx]
  have herr : memEvalExpr (.idxi "a" (.var "n"))
      [("a", .arr32 l), ("n", .u64 n)]
      ⟨1, [(0, ⟨0, true, l⟩)], []⟩ [("a", 0, 0)] = .error .OOB :=
    hagree.trans heval
  have hret := memEvalStmtFuel_return_err F (.idxi "a" (.var "n")) _ _ _
    .OOB herr
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]

/-- Transfer for `operator[]` (hit): both sides equal `arrayAtFwd`. -/
theorem memTransfer_arrayAt (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64) (x : BitVec 32)
    (hidx : l[n.toNat]? = some x)
    (_h : oracleNoalias arrayAtFunc [.arr32 l, .u64 n]) :
    memEvalFuncFuel F arrayAtFunc [.arr32 l, .u64 n] =
      evalFuncFuel F arrayAtFunc [.arr32 l, .u64 n] := by
  rw [memEvalFuncFuel_arrayAt F l n x hidx, evalFuncFuel_arrayAt]

/-- Transfer for `operator[]` (`OOB`): both sides fail loudly. -/
theorem memTransfer_arrayAt_oob (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64)
    (hidx : l[n.toNat]? = none)
    (_h : oracleNoalias arrayAtFunc [.arr32 l, .u64 n]) :
    memEvalFuncFuel F arrayAtFunc [.arr32 l, .u64 n] =
      evalFuncFuel F arrayAtFunc [.arr32 l, .u64 n] := by
  rw [memEvalFuncFuel_arrayAt_oob F l n hidx, evalFuncFuel_arrayAt,
    arrayAtFwd, arrayRefFwd, hidx]

/-- `memEval` for `array_sum`: program evaluation over
    `[arrayAtFunc]` agrees with the threaded-add forward (mirrors
    `evalProgFunc_arraySum`; memory rides alongside, untouched). -/
theorem memEvalProgFunc_arraySum (F : Nat) (a b c d : BitVec 32) :
    memEvalProgFunc [arrayAtFunc] F arraySumFunc [.arr32 [a, b, c, d]] =
      arraySumFwd a b c d := by
  have hbind : bindMemArgs arraySumFunc.args [.arr32 [a, b, c, d]] emptyMem =
      some ([("a", .arr32 [a, b, c, d])], ⟨1, [(0, ⟨0, true, [a, b, c, d]⟩)], []⟩, [("a", 0, 0)]) :=
    bindMemArgs_arraySum a b c d
  have hbody : arraySumFunc.body =
      .seq (.let_ "i0" (.u 64) (.lit (.u64 0)))
      (.seq (.callRet "e0" arrayAtName ["a", "i0"])
      (.seq (.let_ "i1" (.u 64) (.lit (.u64 1)))
      (.seq (.callRet "e1" arrayAtName ["a", "i1"])
      (.seq (.let_ "i2" (.u 64) (.lit (.u64 2)))
      (.seq (.callRet "e2" arrayAtName ["a", "i2"])
      (.seq (.let_ "i3" (.u 64) (.lit (.u64 3)))
      (.seq (.callRet "e3" arrayAtName ["a", "i3"])
             (.return_ (.add (.add (.add (.var "e0") (.var "e1"))
               (.var "e2")) (.var "e3")))))))))) := rfl
  have hfind : findFunc [arrayAtFunc] arrayAtName = some arrayAtFunc :=
    findFunc_hit arrayAtFunc []
  have hlet0 : memEvalProgStmt [arrayAtFunc] F
      (.let_ "i0" (.u 64) (.lit (.u64 0)))
      [("a", .arr32 [a, b, c, d])] ⟨1, [(0, ⟨0, true, [a, b, c, d]⟩)], []⟩ [("a", 0, 0)] =
      .ok (((envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)), ⟨1, [(0, ⟨0, true, [a, b, c, d]⟩)], []⟩, [("a", 0, 0)]), .fellThrough) := by
    simp only [memEvalProgStmt]
    exact memEvalStmtFuel_let_pure F "i0" (.u 64) _ _ _ _
      (.u64 (0 : BitVec 64)) (by simp) (by simp) (by simp) rfl
      (by simp [evalExpr, litVal])
  have hargs0 : lookupArgs (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0))
      ["a", "i0"] = some [.arr32 [a, b, c, d], .u64 0] := by
    simp [lookupArgs, envExtend, envLookup]
  have hcall0 : memEvalFuncFuel F arrayAtFunc
      [.arr32 [a, b, c, d], .u64 0] = .ok (.i32 a) := by
    have hidx0 : [a, b, c, d][(0 : BitVec 64).toNat]? =
        some (a : BitVec 32) := by
      rfl
    rw [memEvalFuncFuel_arrayAt F [a, b, c, d] 0 a hidx0]
    rfl
  have hstep0 := memEvalProgStmt_callRet_ok [arrayAtFunc]
    F "e0" arrayAtName ["a", "i0"]
    (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) ⟨1, [(0, ⟨0, true, [a, b, c, d]⟩)], []⟩ [("a", 0, 0)]
    [.arr32 [a, b, c, d], .u64 0] arrayAtFunc (.i32 a)
    hargs0 hfind hcall0
  have hlet1 : memEvalProgStmt [arrayAtFunc] F
      (.let_ "i1" (.u 64) (.lit (.u64 1)))
      (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) ⟨1, [(0, ⟨0, true, [a, b, c, d]⟩)], []⟩ [("a", 0, 0)] =
      .ok (((envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)), ⟨1, [(0, ⟨0, true, [a, b, c, d]⟩)], []⟩, [("a", 0, 0)]), .fellThrough) := by
    simp only [memEvalProgStmt]
    exact memEvalStmtFuel_let_pure F "i1" (.u 64) _ _ _ _
      (.u64 (1 : BitVec 64)) (by simp) (by simp) (by simp) rfl
      (by simp [evalExpr, litVal])
  have hargs1 : lookupArgs (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1))
      ["a", "i1"] = some [.arr32 [a, b, c, d], .u64 1] := by
    simp [lookupArgs, envExtend, envLookup]
  have hcall1 : memEvalFuncFuel F arrayAtFunc
      [.arr32 [a, b, c, d], .u64 1] = .ok (.i32 b) := by
    have hidx1 : [a, b, c, d][(1 : BitVec 64).toNat]? =
        some (b : BitVec 32) := by
      rfl
    rw [memEvalFuncFuel_arrayAt F [a, b, c, d] 1 b hidx1]
    rfl
  have hstep1 := memEvalProgStmt_callRet_ok [arrayAtFunc]
    F "e1" arrayAtName ["a", "i1"]
    (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) ⟨1, [(0, ⟨0, true, [a, b, c, d]⟩)], []⟩ [("a", 0, 0)]
    [.arr32 [a, b, c, d], .u64 1] arrayAtFunc (.i32 b)
    hargs1 hfind hcall1
  have hlet2 : memEvalProgStmt [arrayAtFunc] F
      (.let_ "i2" (.u 64) (.lit (.u64 2)))
      (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) ⟨1, [(0, ⟨0, true, [a, b, c, d]⟩)], []⟩ [("a", 0, 0)] =
      .ok (((envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)), ⟨1, [(0, ⟨0, true, [a, b, c, d]⟩)], []⟩, [("a", 0, 0)]), .fellThrough) := by
    simp only [memEvalProgStmt]
    exact memEvalStmtFuel_let_pure F "i2" (.u 64) _ _ _ _
      (.u64 (2 : BitVec 64)) (by simp) (by simp) (by simp) rfl
      (by simp [evalExpr, litVal])
  have hargs2 : lookupArgs (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2))
      ["a", "i2"] = some [.arr32 [a, b, c, d], .u64 2] := by
    simp [lookupArgs, envExtend, envLookup]
  have hcall2 : memEvalFuncFuel F arrayAtFunc
      [.arr32 [a, b, c, d], .u64 2] = .ok (.i32 c) := by
    have hidx2 : [a, b, c, d][(2 : BitVec 64).toNat]? =
        some (c : BitVec 32) := by
      rfl
    rw [memEvalFuncFuel_arrayAt F [a, b, c, d] 2 c hidx2]
    rfl
  have hstep2 := memEvalProgStmt_callRet_ok [arrayAtFunc]
    F "e2" arrayAtName ["a", "i2"]
    (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) ⟨1, [(0, ⟨0, true, [a, b, c, d]⟩)], []⟩ [("a", 0, 0)]
    [.arr32 [a, b, c, d], .u64 2] arrayAtFunc (.i32 c)
    hargs2 hfind hcall2
  have hlet3 : memEvalProgStmt [arrayAtFunc] F
      (.let_ "i3" (.u 64) (.lit (.u64 3)))
      (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) ⟨1, [(0, ⟨0, true, [a, b, c, d]⟩)], []⟩ [("a", 0, 0)] =
      .ok (((envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) "i3" (.u64 3)), ⟨1, [(0, ⟨0, true, [a, b, c, d]⟩)], []⟩, [("a", 0, 0)]), .fellThrough) := by
    simp only [memEvalProgStmt]
    exact memEvalStmtFuel_let_pure F "i3" (.u 64) _ _ _ _
      (.u64 (3 : BitVec 64)) (by simp) (by simp) (by simp) rfl
      (by simp [evalExpr, litVal])
  have hargs3 : lookupArgs (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) "i3" (.u64 3))
      ["a", "i3"] = some [.arr32 [a, b, c, d], .u64 3] := by
    simp [lookupArgs, envExtend, envLookup]
  have hcall3 : memEvalFuncFuel F arrayAtFunc
      [.arr32 [a, b, c, d], .u64 3] = .ok (.i32 d) := by
    have hidx3 : [a, b, c, d][(3 : BitVec 64).toNat]? =
        some (d : BitVec 32) := by
      rfl
    rw [memEvalFuncFuel_arrayAt F [a, b, c, d] 3 d hidx3]
    rfl
  have hstep3 := memEvalProgStmt_callRet_ok [arrayAtFunc]
    F "e3" arrayAtName ["a", "i3"]
    (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) "i3" (.u64 3)) ⟨1, [(0, ⟨0, true, [a, b, c, d]⟩)], []⟩ [("a", 0, 0)]
    [.arr32 [a, b, c, d], .u64 3] arrayAtFunc (.i32 d)
    hargs3 hfind hcall3
  cases h1 : checkedAddI32 a b with
  | error e =>
    have hexpr : memEvalExpr
        (.add (.add (.add (.var "e0") (.var "e1")) (.var "e2"))
          (.var "e3"))
        (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) "i3" (.u64 3)) "e3" (.i32 d)) ⟨1, [(0, ⟨0, true, [a, b, c, d]⟩)], []⟩ [("a", 0, 0)] = .error e := by
      simp [memEvalExpr, envExtend, envLookup, h1, Except.map]
    have hret : memEvalProgStmt [arrayAtFunc] F
        (.return_ (.add (.add (.add (.var "e0") (.var "e1"))
          (.var "e2")) (.var "e3")))
        (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) "i3" (.u64 3)) "e3" (.i32 d)) ⟨1, [(0, ⟨0, true, [a, b, c, d]⟩)], []⟩ [("a", 0, 0)] = .error e := by
      simp only [memEvalProgStmt]; exact memEvalStmtFuel_return_err F _ _ _ _ e hexpr
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hlet0,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep0,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hlet1,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep1,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hlet2,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep2,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hlet3,
      memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep3, hret]
    simp [arraySumFwd, h1]
  | ok t =>
    cases h2 : checkedAddI32 t c with
    | error e =>
      have hexpr : memEvalExpr
          (.add (.add (.add (.var "e0") (.var "e1")) (.var "e2"))
          (.var "e3"))
          (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) "i3" (.u64 3)) "e3" (.i32 d)) ⟨1, [(0, ⟨0, true, [a, b, c, d]⟩)], []⟩ [("a", 0, 0)] = .error e := by
        simp [memEvalExpr, envExtend, envLookup, h1, h2, Except.map]
      have hret : memEvalProgStmt [arrayAtFunc] F
          (.return_ (.add (.add (.add (.var "e0") (.var "e1"))
          (.var "e2")) (.var "e3")))
          (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) "i3" (.u64 3)) "e3" (.i32 d)) ⟨1, [(0, ⟨0, true, [a, b, c, d]⟩)], []⟩ [("a", 0, 0)] = .error e := by
        simp only [memEvalProgStmt]; exact memEvalStmtFuel_return_err F _ _ _ _ e hexpr
      simp only [memEvalProgFunc, hbind, hbody]
      rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hlet0,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep0,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hlet1,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep1,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hlet2,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep2,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hlet3,
        memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep3, hret]
      simp [arraySumFwd, h1, h2]
    | ok u =>
      cases h3 : checkedAddI32 u d with
      | error e =>
        have hexpr : memEvalExpr
            (.add (.add (.add (.var "e0") (.var "e1")) (.var "e2"))
          (.var "e3"))
            (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) "i3" (.u64 3)) "e3" (.i32 d)) ⟨1, [(0, ⟨0, true, [a, b, c, d]⟩)], []⟩ [("a", 0, 0)] = .error e := by
          simp [memEvalExpr, envExtend, envLookup, h1, h2, h3, Except.map]
        have hret : memEvalProgStmt [arrayAtFunc] F
            (.return_ (.add (.add (.add (.var "e0") (.var "e1"))
          (.var "e2")) (.var "e3")))
            (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) "i3" (.u64 3)) "e3" (.i32 d)) ⟨1, [(0, ⟨0, true, [a, b, c, d]⟩)], []⟩ [("a", 0, 0)] = .error e := by
          simp only [memEvalProgStmt]; exact memEvalStmtFuel_return_err F _ _ _ _ e hexpr
        simp only [memEvalProgFunc, hbind, hbody]
        rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hlet0,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep0,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hlet1,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep1,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hlet2,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep2,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hlet3,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep3, hret]
        simp [arraySumFwd, h1, h2, h3, i32_map_error]
      | ok r =>
        have hexpr : memEvalExpr
            (.add (.add (.add (.var "e0") (.var "e1")) (.var "e2"))
          (.var "e3"))
            (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) "i3" (.u64 3)) "e3" (.i32 d)) ⟨1, [(0, ⟨0, true, [a, b, c, d]⟩)], []⟩ [("a", 0, 0)] = .ok (.i32 r) := by
          simp [memEvalExpr, envExtend, envLookup, h1, h2, h3, Except.map]
        have hret : memEvalProgStmt [arrayAtFunc] F
            (.return_ (.add (.add (.add (.var "e0") (.var "e1"))
          (.var "e2")) (.var "e3")))
            (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) "i3" (.u64 3)) "e3" (.i32 d)) ⟨1, [(0, ⟨0, true, [a, b, c, d]⟩)], []⟩ [("a", 0, 0)] =
            .ok ((((envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend (envExtend [("a", .arr32 [a, b, c, d])] "i0" (.u64 0)) "e0" (.i32 a)) "i1" (.u64 1)) "e1" (.i32 b)) "i2" (.u64 2)) "e2" (.i32 c)) "i3" (.u64 3)) "e3" (.i32 d)), ⟨1, [(0, ⟨0, true, [a, b, c, d]⟩)], []⟩, [("a", 0, 0)])), .returned (.i32 r)) :=
          memEvalProgStmt_return [arrayAtFunc] F _ _ _ _
            (.i32 r) hexpr
        simp only [memEvalProgFunc, hbind, hbody]
        rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hlet0,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep0,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hlet1,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep1,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hlet2,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep2,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hlet3,
          memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep3, hret]
        simp [arraySumFwd, h1, h2, h3, i32_map_ok]

/-- Transfer for `array_sum` (program level): both sides equal
    `arraySumFwd`. -/
theorem memTransferProg_arraySum (F : Nat) (a b c d : BitVec 32)
    (_h : oracleNoalias arraySumFunc [.arr32 [a, b, c, d]]) :
    memEvalProgFunc [arrayAtFunc] F arraySumFunc [.arr32 [a, b, c, d]] =
      evalProgFunc [arrayAtFunc] F arraySumFunc [.arr32 [a, b, c, d]] := by
  rw [memEvalProgFunc_arraySum, evalProgFunc_arraySum]

/-! ## N4d-ii `std::optional` transfers: engaged bit and payload agree -/

/-- `memEval` for `_M_is_engaged` (engaged): the engaged-bit word in
    memory agrees with the `optVal` flag (mirrors
    `evalFuncFuel_optHas`). -/
theorem memEvalFuncFuel_optHas_some (F : Nat) (x : BitVec 32) :
    memEvalFuncFuel F optHasFunc [.optVal (some x)] =
      optHasFwd (some x) := by
  have hb : bindMemArgs optHasFunc.args [.optVal (some x)] emptyMem =
      some ([("b", .optVal (some x))],
        ⟨1, [(0, ⟨0, true, [x, 1]⟩)], []⟩, [("b", 0, 0)]) :=
    bindMemArgs_optVal "b" (some x)
  have hbody : optHasFunc.body = .return_ (.optHas "b") := rfl
  have ho : envLookup [("b", .optVal (some x))] "b" =
      some (.optVal (some x)) := by
    simp [envLookup]
  have hlay : layoutLookup [("b", 0, 0)] "b" = some (0, 0) := by
    simp [layoutLookup]
  have hmem : memLoad ⟨1, [(0, ⟨0, true, [x, 1]⟩)], []⟩ 0 0 1 =
      .ok 1 := by
    simp [memLoad, memFind]
  have hval : (1 : BitVec 32) =
      (if (some x).isSome then 1 else 0 : BitVec 32) := rfl
  have hagree := memEvalExpr_optHas_hit "b" _ _ _ (some x) 0 0 1
    hlay ho hmem hval
  have heval : evalExpr (.optHas "b") [("b", .optVal (some x))] =
      .ok (.b true) :=
    evalExpr_optHas_some "b" _ x ho
  have hret := memEvalStmtFuel_return F (.optHas "b") _ _ _ (.b true)
    hagree heval
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  simp [optHasFwd]

/-- `memEval` for `_M_is_engaged` (disengaged): both sides report
    `false`. -/
theorem memEvalFuncFuel_optHas_none (F : Nat) :
    memEvalFuncFuel F optHasFunc [.optVal none] = optHasFwd none := by
  have hb : bindMemArgs optHasFunc.args [.optVal none] emptyMem =
      some ([("b", .optVal none)],
        ⟨1, [(0, ⟨0, true, [0, 0]⟩)], []⟩, [("b", 0, 0)]) :=
    bindMemArgs_optVal "b" none
  have hbody : optHasFunc.body = .return_ (.optHas "b") := rfl
  have ho : envLookup [("b", .optVal none)] "b" =
      some (.optVal none) := by
    simp [envLookup]
  have hlay : layoutLookup [("b", 0, 0)] "b" = some (0, 0) := by
    simp [layoutLookup]
  have hmem : memLoad ⟨1, [(0, ⟨0, true, [0, 0]⟩)], []⟩ 0 0 1 =
      .ok 0 := by
    simp [memLoad, memFind]
  have hval : (0 : BitVec 32) =
      (if (none : Option (BitVec 32)).isSome then 1 else 0 : BitVec 32) :=
    rfl
  have hagree := memEvalExpr_optHas_hit "b" _ _ _ none 0 0 0
    hlay ho hmem hval
  have heval : evalExpr (.optHas "b") [("b", .optVal none)] =
      .ok (.b false) :=
    evalExpr_optHas_none "b" _ ho
  have hret := memEvalStmtFuel_return F (.optHas "b") _ _ _ (.b false)
    hagree heval
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  simp [optHasFwd]

/-- Transfer for `_M_is_engaged` (engaged). -/
theorem memTransfer_optHas_some (F : Nat) (x : BitVec 32)
    (_h : oracleNoalias optHasFunc [.optVal (some x)]) :
    memEvalFuncFuel F optHasFunc [.optVal (some x)] =
      evalFuncFuel F optHasFunc [.optVal (some x)] := by
  rw [memEvalFuncFuel_optHas_some F x, evalFuncFuel_optHas]

/-- Transfer for `_M_is_engaged` (disengaged). -/
theorem memTransfer_optHas_none (F : Nat)
    (_h : oracleNoalias optHasFunc [.optVal none]) :
    memEvalFuncFuel F optHasFunc [.optVal none] =
      evalFuncFuel F optHasFunc [.optVal none] := by
  rw [memEvalFuncFuel_optHas_none F, evalFuncFuel_optHas]

/-- `memEval` for `has_value` (engaged; fused call edge). -/
theorem memEvalFuncFuel_optHasValue_some (F : Nat) (x : BitVec 32) :
    memEvalFuncFuel F optHasValueFunc [.optVal (some x)] =
      optHasValueFwd (some x) := by
  have hb : bindMemArgs optHasValueFunc.args [.optVal (some x)] emptyMem =
      some ([("o", .optVal (some x))],
        ⟨1, [(0, ⟨0, true, [x, 1]⟩)], []⟩, [("o", 0, 0)]) :=
    bindMemArgs_optVal "o" (some x)
  have hbody : optHasValueFunc.body = .return_ (.optHas "o") := rfl
  have ho : envLookup [("o", .optVal (some x))] "o" =
      some (.optVal (some x)) := by
    simp [envLookup]
  have hlay : layoutLookup [("o", 0, 0)] "o" = some (0, 0) := by
    simp [layoutLookup]
  have hmem : memLoad ⟨1, [(0, ⟨0, true, [x, 1]⟩)], []⟩ 0 0 1 =
      .ok 1 := by
    simp [memLoad, memFind]
  have hval : (1 : BitVec 32) =
      (if (some x).isSome then 1 else 0 : BitVec 32) := rfl
  have hagree := memEvalExpr_optHas_hit "o" _ _ _ (some x) 0 0 1
    hlay ho hmem hval
  have heval : evalExpr (.optHas "o") [("o", .optVal (some x))] =
      .ok (.b true) :=
    evalExpr_optHas_some "o" _ x ho
  have hret := memEvalStmtFuel_return F (.optHas "o") _ _ _ (.b true)
    hagree heval
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  simp [optHasValueFwd, optHasFwd]

/-- `memEval` for `has_value` (disengaged; fused call edge). -/
theorem memEvalFuncFuel_optHasValue_none (F : Nat) :
    memEvalFuncFuel F optHasValueFunc [.optVal none] =
      optHasValueFwd none := by
  have hb : bindMemArgs optHasValueFunc.args [.optVal none] emptyMem =
      some ([("o", .optVal none)],
        ⟨1, [(0, ⟨0, true, [0, 0]⟩)], []⟩, [("o", 0, 0)]) :=
    bindMemArgs_optVal "o" none
  have hbody : optHasValueFunc.body = .return_ (.optHas "o") := rfl
  have ho : envLookup [("o", .optVal none)] "o" =
      some (.optVal none) := by
    simp [envLookup]
  have hlay : layoutLookup [("o", 0, 0)] "o" = some (0, 0) := by
    simp [layoutLookup]
  have hmem : memLoad ⟨1, [(0, ⟨0, true, [0, 0]⟩)], []⟩ 0 0 1 =
      .ok 0 := by
    simp [memLoad, memFind]
  have hval : (0 : BitVec 32) =
      (if (none : Option (BitVec 32)).isSome then 1 else 0 : BitVec 32) :=
    rfl
  have hagree := memEvalExpr_optHas_hit "o" _ _ _ none 0 0 0
    hlay ho hmem hval
  have heval : evalExpr (.optHas "o") [("o", .optVal none)] =
      .ok (.b false) :=
    evalExpr_optHas_none "o" _ ho
  have hret := memEvalStmtFuel_return F (.optHas "o") _ _ _ (.b false)
    hagree heval
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  simp [optHasValueFwd, optHasFwd]

/-- Transfer for `has_value` (engaged). -/
theorem memTransfer_optHasValue_some (F : Nat) (x : BitVec 32)
    (_h : oracleNoalias optHasValueFunc [.optVal (some x)]) :
    memEvalFuncFuel F optHasValueFunc [.optVal (some x)] =
      evalFuncFuel F optHasValueFunc [.optVal (some x)] := by
  rw [memEvalFuncFuel_optHasValue_some F x, evalFuncFuel_optHasValue]

/-- Transfer for `has_value` (disengaged). -/
theorem memTransfer_optHasValue_none (F : Nat)
    (_h : oracleNoalias optHasValueFunc [.optVal none]) :
    memEvalFuncFuel F optHasValueFunc [.optVal none] =
      evalFuncFuel F optHasValueFunc [.optVal none] := by
  rw [memEvalFuncFuel_optHasValue_none F, evalFuncFuel_optHasValue]

/-- `memEval` for payload `_M_get` (engaged): both memory words
    agree with the payload (mirrors `evalFuncFuel_optGet`). -/
theorem memEvalFuncFuel_optGet_some (F : Nat) (x : BitVec 32) :
    memEvalFuncFuel F optGetFunc [.optVal (some x)] =
      optGetFwd (some x) := by
  have hb : bindMemArgs optGetFunc.args [.optVal (some x)] emptyMem =
      some ([("p", .optVal (some x))],
        ⟨1, [(0, ⟨0, true, [x, 1]⟩)], []⟩, [("p", 0, 0)]) :=
    bindMemArgs_optVal "p" (some x)
  have hbody : optGetFunc.body = .return_ (.optGet "p") := rfl
  have ho : envLookup [("p", .optVal (some x))] "p" =
      some (.optVal (some x)) := by
    simp [envLookup]
  have hlay : layoutLookup [("p", 0, 0)] "p" = some (0, 0) := by
    simp [layoutLookup]
  have hmem0 : memLoad ⟨1, [(0, ⟨0, true, [x, 1]⟩)], []⟩ 0 0 0 =
      .ok x := by
    simp [memLoad, memFind]
  have hmem1 : memLoad ⟨1, [(0, ⟨0, true, [x, 1]⟩)], []⟩ 0 0 1 =
      .ok 1 := by
    simp [memLoad, memFind]
  have hagree := memEvalExpr_optGet_hit "p" _ _ _ x 0 0
    hlay ho hmem0 hmem1
  have heval : evalExpr (.optGet "p") [("p", .optVal (some x))] =
      .ok (.i32 x) :=
    evalExpr_optGet_some "p" _ x ho
  have hret := memEvalStmtFuel_return F (.optGet "p") _ _ _ (.i32 x)
    hagree heval
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  simp [optGetFwd]

/-- `memEval` for payload `_M_get` (disengaged): both sides fail
    `AssertFail` loudly. -/
theorem memEvalFuncFuel_optGet_none (F : Nat) :
    memEvalFuncFuel F optGetFunc [.optVal none] = .error .AssertFail := by
  have hb : bindMemArgs optGetFunc.args [.optVal none] emptyMem =
      some ([("p", .optVal none)],
        ⟨1, [(0, ⟨0, true, [0, 0]⟩)], []⟩, [("p", 0, 0)]) :=
    bindMemArgs_optVal "p" none
  have hbody : optGetFunc.body = .return_ (.optGet "p") := rfl
  have ho : envLookup [("p", .optVal none)] "p" =
      some (.optVal none) := by
    simp [envLookup]
  have hlay : layoutLookup [("p", 0, 0)] "p" = some (0, 0) := by
    simp [layoutLookup]
  have hmem0 : memLoad ⟨1, [(0, ⟨0, true, [0, 0]⟩)], []⟩ 0 0 0 =
      .ok 0 := by
    simp [memLoad, memFind]
  have hmem1 : memLoad ⟨1, [(0, ⟨0, true, [0, 0]⟩)], []⟩ 0 0 1 =
      .ok 0 := by
    simp [memLoad, memFind]
  have hagree := memEvalExpr_optGet_oob "p" _ _ _ 0 0 0 0
    hlay ho hmem0 hmem1
  have heval : evalExpr (.optGet "p") [("p", .optVal none)] =
      .error .AssertFail :=
    evalExpr_optGet_none "p" _ ho
  have herr : memEvalExpr (.optGet "p") [("p", .optVal none)]
      ⟨1, [(0, ⟨0, true, [0, 0]⟩)], []⟩ [("p", 0, 0)] =
      .error .AssertFail :=
    hagree.trans heval
  have hret := memEvalStmtFuel_return_err F (.optGet "p") _ _ _
    .AssertFail herr
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]

/-- Transfer for payload `_M_get` (engaged). -/
theorem memTransfer_optGet_some (F : Nat) (x : BitVec 32)
    (_h : oracleNoalias optGetFunc [.optVal (some x)]) :
    memEvalFuncFuel F optGetFunc [.optVal (some x)] =
      evalFuncFuel F optGetFunc [.optVal (some x)] := by
  rw [memEvalFuncFuel_optGet_some F x, evalFuncFuel_optGet]

/-- Transfer for payload `_M_get` (disengaged): both sides fail loudly. -/
theorem memTransfer_optGet_none (F : Nat)
    (_h : oracleNoalias optGetFunc [.optVal none]) :
    memEvalFuncFuel F optGetFunc [.optVal none] =
      evalFuncFuel F optGetFunc [.optVal none] := by
  rw [memEvalFuncFuel_optGet_none F, evalFuncFuel_optGet, optGetFwd]

/-- `memEval` for `operator*` (engaged; fused call edges). -/
theorem memEvalFuncFuel_optDerefOp_some (F : Nat) (x : BitVec 32) :
    memEvalFuncFuel F optDerefOpFunc [.optVal (some x)] =
      optDerefOpFwd (some x) := by
  have hb : bindMemArgs optDerefOpFunc.args [.optVal (some x)] emptyMem =
      some ([("o", .optVal (some x))],
        ⟨1, [(0, ⟨0, true, [x, 1]⟩)], []⟩, [("o", 0, 0)]) :=
    bindMemArgs_optVal "o" (some x)
  have hbody : optDerefOpFunc.body = .return_ (.optGet "o") := rfl
  have ho : envLookup [("o", .optVal (some x))] "o" =
      some (.optVal (some x)) := by
    simp [envLookup]
  have hlay : layoutLookup [("o", 0, 0)] "o" = some (0, 0) := by
    simp [layoutLookup]
  have hmem0 : memLoad ⟨1, [(0, ⟨0, true, [x, 1]⟩)], []⟩ 0 0 0 =
      .ok x := by
    simp [memLoad, memFind]
  have hmem1 : memLoad ⟨1, [(0, ⟨0, true, [x, 1]⟩)], []⟩ 0 0 1 =
      .ok 1 := by
    simp [memLoad, memFind]
  have hagree := memEvalExpr_optGet_hit "o" _ _ _ x 0 0
    hlay ho hmem0 hmem1
  have heval : evalExpr (.optGet "o") [("o", .optVal (some x))] =
      .ok (.i32 x) :=
    evalExpr_optGet_some "o" _ x ho
  have hret := memEvalStmtFuel_return F (.optGet "o") _ _ _ (.i32 x)
    hagree heval
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  simp [optDerefOpFwd, optGetFwd]

/-- `memEval` for `operator*` (disengaged; fused call edges). -/
theorem memEvalFuncFuel_optDerefOp_none (F : Nat) :
    memEvalFuncFuel F optDerefOpFunc [.optVal none] =
      .error .AssertFail := by
  have hb : bindMemArgs optDerefOpFunc.args [.optVal none] emptyMem =
      some ([("o", .optVal none)],
        ⟨1, [(0, ⟨0, true, [0, 0]⟩)], []⟩, [("o", 0, 0)]) :=
    bindMemArgs_optVal "o" none
  have hbody : optDerefOpFunc.body = .return_ (.optGet "o") := rfl
  have ho : envLookup [("o", .optVal none)] "o" =
      some (.optVal none) := by
    simp [envLookup]
  have hlay : layoutLookup [("o", 0, 0)] "o" = some (0, 0) := by
    simp [layoutLookup]
  have hmem0 : memLoad ⟨1, [(0, ⟨0, true, [0, 0]⟩)], []⟩ 0 0 0 =
      .ok 0 := by
    simp [memLoad, memFind]
  have hmem1 : memLoad ⟨1, [(0, ⟨0, true, [0, 0]⟩)], []⟩ 0 0 1 =
      .ok 0 := by
    simp [memLoad, memFind]
  have hagree := memEvalExpr_optGet_oob "o" _ _ _ 0 0 0 0
    hlay ho hmem0 hmem1
  have heval : evalExpr (.optGet "o") [("o", .optVal none)] =
      .error .AssertFail :=
    evalExpr_optGet_none "o" _ ho
  have herr : memEvalExpr (.optGet "o") [("o", .optVal none)]
      ⟨1, [(0, ⟨0, true, [0, 0]⟩)], []⟩ [("o", 0, 0)] =
      .error .AssertFail :=
    hagree.trans heval
  have hret := memEvalStmtFuel_return_err F (.optGet "o") _ _ _
    .AssertFail herr
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]

/-- Transfer for `operator*` (engaged). -/
theorem memTransfer_optDerefOp_some (F : Nat) (x : BitVec 32)
    (_h : oracleNoalias optDerefOpFunc [.optVal (some x)]) :
    memEvalFuncFuel F optDerefOpFunc [.optVal (some x)] =
      evalFuncFuel F optDerefOpFunc [.optVal (some x)] := by
  rw [memEvalFuncFuel_optDerefOp_some F x, evalFuncFuel_optDerefOp]

/-- Transfer for `operator*` (disengaged): both sides fail loudly. -/
theorem memTransfer_optDerefOp_none (F : Nat)
    (_h : oracleNoalias optDerefOpFunc [.optVal none]) :
    memEvalFuncFuel F optDerefOpFunc [.optVal none] =
      evalFuncFuel F optDerefOpFunc [.optVal none] := by
  rw [memEvalFuncFuel_optDerefOp_none F, evalFuncFuel_optDerefOp,
    optDerefOpFwd, optGetFwd]

/-- `memEval` for impl `_M_get`: program evaluation over the payload
    leaf agrees with the delegating forward (memory rides alongside,
    untouched; mirrors `evalProgFunc_optImplGet`). -/
theorem memEvalProgFunc_optImplGet (F : Nat) (v : Option (BitVec 32)) :
    memEvalProgFunc [optGetFunc] F optImplGetFunc [.optVal v] =
      optGetFwd v := by
  have hbind : bindMemArgs optImplGetFunc.args [.optVal v] emptyMem =
      some ([("o", .optVal v)],
        ⟨1, [(0, ⟨0, true,
          match v with
          | some x => [x, 1]
          | none => [0, 0]⟩)], []⟩,
        [("o", 0, 0)]) :=
    bindMemArgs_optVal "o" v
  have hbody : optImplGetFunc.body =
      .seq (.callRet "r" optGetName ["o"])
           (.return_ (.var "r")) := rfl
  have hfind : findFunc [optGetFunc] optGetName = some optGetFunc := rfl
  have hargs : lookupArgs [("o", .optVal v)] ["o"] =
      some [.optVal v] := rfl
  cases v with
  | none =>
    have hcall : memEvalFuncFuel F optGetFunc [.optVal none] =
        .error .AssertFail :=
      memEvalFuncFuel_optGet_none F
    have hstep := memEvalProgStmt_callRet_err [optGetFunc] F "r"
      optGetName ["o"] [("o", .optVal none)]
      ⟨1, [(0, ⟨0, true, [0, 0]⟩)], []⟩ [("o", 0, 0)]
      [.optVal none] optGetFunc .AssertFail hargs hfind hcall
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstep]
    simp [optGetFwd]
  | some x =>
    have hcall : memEvalFuncFuel F optGetFunc [.optVal (some x)] =
        .ok (.i32 x) :=
      memEvalFuncFuel_optGet_some F x
    have hstep := memEvalProgStmt_callRet_ok [optGetFunc] F "r"
      optGetName ["o"] [("o", .optVal (some x))]
      ⟨1, [(0, ⟨0, true, [x, 1]⟩)], []⟩ [("o", 0, 0)]
      [.optVal (some x)] optGetFunc (.i32 x) hargs hfind hcall
    have hexpr : memEvalExpr (.var "r")
        (envExtend [("o", .optVal (some x))] "r" (.i32 x))
        ⟨1, [(0, ⟨0, true, [x, 1]⟩)], []⟩ [("o", 0, 0)] =
        .ok (.i32 x) := by
      simp [memEvalExpr, envExtend, envLookup]
    have hret := memEvalProgStmt_return [optGetFunc] F (.var "r")
      (envExtend [("o", .optVal (some x))] "r" (.i32 x))
      ⟨1, [(0, ⟨0, true, [x, 1]⟩)], []⟩ [("o", 0, 0)]
      (.i32 x) hexpr
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep, hret]
    simp [optGetFwd]

/-- Transfer for impl `_M_get` (program level). -/
theorem memTransferProg_optImplGet (F : Nat) (v : Option (BitVec 32))
    (_h : oracleNoalias optImplGetFunc [.optVal v]) :
    memEvalProgFunc [optGetFunc] F optImplGetFunc [.optVal v] =
      evalProgFunc [optGetFunc] F optImplGetFunc [.optVal v] := by
  rw [memEvalProgFunc_optImplGet, evalProgFunc_optImplGet]

/-- `memEval` for `opt_deref`: program evaluation over the two
    leaves agrees with the sentinel forward (mirrors
    `evalProgFunc_optDeref`; memory rides alongside, untouched). -/
theorem memEvalProgFunc_optDeref (F : Nat) (v : Option (BitVec 32)) :
    memEvalProgFunc optDerefProg F optDerefFunc [.optVal v] =
      optDerefFwd v := by
  have hbind : bindMemArgs optDerefFunc.args [.optVal v] emptyMem =
      some ([("o", .optVal v)],
        ⟨1, [(0, ⟨0, true,
          match v with
          | some x => [x, 1]
          | none => [0, 0]⟩)], []⟩,
        [("o", 0, 0)]) :=
    bindMemArgs_optVal "o" v
  have hbody : optDerefFunc.body =
      .seq (.callRet "h" optHasValueName ["o"])
      (.if_ (.var "h")
        (.seq (.callRet "v" optDerefOpName ["o"])
              (.return_ (.var "v")))
        (.return_ (.lit (.i32 (-1 : BitVec 32))))) := rfl
  have hfindH : findFunc optDerefProg optHasValueName =
      some optHasValueFunc := rfl
  have hfindD : findFunc optDerefProg optDerefOpName =
      some optDerefOpFunc := rfl
  have hargsH : lookupArgs [("o", .optVal v)] ["o"] =
      some [.optVal v] := rfl
  cases v with
  | none =>
    have hcallH : memEvalFuncFuel F optHasValueFunc [.optVal none] =
        .ok (.b false) :=
      memEvalFuncFuel_optHasValue_none F
    have hstepH := memEvalProgStmt_callRet_ok optDerefProg F "h"
      optHasValueName ["o"] [("o", .optVal none)]
      ⟨1, [(0, ⟨0, true, [0, 0]⟩)], []⟩ [("o", 0, 0)]
      [.optVal none] optHasValueFunc (.b false) hargsH hfindH hcallH
    have hcondF : memEvalExpr (.var "h")
        (envExtend [("o", .optVal none)] "h" (.b false))
        ⟨1, [(0, ⟨0, true, [0, 0]⟩)], []⟩ [("o", 0, 0)] =
        .ok (.b false) := by
      simp [memEvalExpr, envExtend, envLookup]
    have hifF : memEvalProgStmt optDerefProg F
        (.if_ (.var "h")
          (.seq (.callRet "v" optDerefOpName ["o"])
                (.return_ (.var "v")))
          (.return_ (.lit (.i32 (-1 : BitVec 32)))))
        (envExtend [("o", .optVal none)] "h" (.b false))
        ⟨1, [(0, ⟨0, true, [0, 0]⟩)], []⟩ [("o", 0, 0)] =
        memEvalProgStmt optDerefProg F
          (.return_ (.lit (.i32 (-1 : BitVec 32))))
          (envExtend [("o", .optVal none)] "h" (.b false))
          ⟨1, [(0, ⟨0, true, [0, 0]⟩)], []⟩ [("o", 0, 0)] :=
      memEvalProgStmt_if_false _ _ _ _ _ _ _ _ hcondF
    have hexprE : memEvalExpr (.lit (.i32 (-1 : BitVec 32)))
        (envExtend [("o", .optVal none)] "h" (.b false))
        ⟨1, [(0, ⟨0, true, [0, 0]⟩)], []⟩ [("o", 0, 0)] =
        .ok (.i32 (-1 : BitVec 32)) := by
      simp [memEvalExpr, litVal]
    have helse := memEvalProgStmt_return optDerefProg F
      (.lit (.i32 (-1 : BitVec 32)))
      (envExtend [("o", .optVal none)] "h" (.b false))
      ⟨1, [(0, ⟨0, true, [0, 0]⟩)], []⟩ [("o", 0, 0)]
      (.i32 (-1 : BitVec 32)) hexprE
    have hifF' : memEvalProgStmt optDerefProg F
        (.if_ (.var "h")
          (.seq (.callRet "v" optDerefOpName ["o"])
                (.return_ (.var "v")))
          (.return_ (.lit (.i32 (-1 : BitVec 32)))))
        (envExtend [("o", .optVal none)] "h" (.b false))
        ⟨1, [(0, ⟨0, true, [0, 0]⟩)], []⟩ [("o", 0, 0)] =
        .ok (((envExtend [("o", .optVal none)] "h" (.b false)),
          ⟨1, [(0, ⟨0, true, [0, 0]⟩)], []⟩, [("o", 0, 0)]),
          .returned (.i32 (-1 : BitVec 32))) :=
      Eq.trans hifF helse
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepH, hifF']
    simp [optDerefFwd]
  | some x =>
    have hcallH : memEvalFuncFuel F optHasValueFunc [.optVal (some x)] =
        .ok (.b true) :=
      memEvalFuncFuel_optHasValue_some F x
    have hstepH := memEvalProgStmt_callRet_ok optDerefProg F "h"
      optHasValueName ["o"] [("o", .optVal (some x))]
      ⟨1, [(0, ⟨0, true, [x, 1]⟩)], []⟩ [("o", 0, 0)]
      [.optVal (some x)] optHasValueFunc (.b true) hargsH hfindH hcallH
    have hcondT : memEvalExpr (.var "h")
        (envExtend [("o", .optVal (some x))] "h" (.b true))
        ⟨1, [(0, ⟨0, true, [x, 1]⟩)], []⟩ [("o", 0, 0)] =
        .ok (.b true) := by
      simp [memEvalExpr, envExtend, envLookup]
    have hargsV : lookupArgs
        (envExtend [("o", .optVal (some x))] "h" (.b true)) ["o"] =
        some [.optVal (some x)] := by
      simp [lookupArgs, envExtend, envLookup,
        show ("o" : String) ≠ "h" by decide]
    have hcallV : memEvalFuncFuel F optDerefOpFunc [.optVal (some x)] =
        .ok (.i32 x) :=
      memEvalFuncFuel_optDerefOp_some F x
    have hstepV := memEvalProgStmt_callRet_ok optDerefProg F "v"
      optDerefOpName ["o"]
      (envExtend [("o", .optVal (some x))] "h" (.b true))
      ⟨1, [(0, ⟨0, true, [x, 1]⟩)], []⟩ [("o", 0, 0)]
      [.optVal (some x)] optDerefOpFunc (.i32 x)
      hargsV hfindD hcallV
    have hexprV : memEvalExpr (.var "v")
        (envExtend (envExtend [("o", .optVal (some x))] "h" (.b true))
          "v" (.i32 x))
        ⟨1, [(0, ⟨0, true, [x, 1]⟩)], []⟩ [("o", 0, 0)] =
        .ok (.i32 x) := by
      simp [memEvalExpr, envExtend, envLookup]
    have hretV := memEvalProgStmt_return optDerefProg F (.var "v")
      (envExtend (envExtend [("o", .optVal (some x))] "h" (.b true))
        "v" (.i32 x))
      ⟨1, [(0, ⟨0, true, [x, 1]⟩)], []⟩ [("o", 0, 0)]
      (.i32 x) hexprV
    have hthen : memEvalProgStmt optDerefProg F
        (.seq (.callRet "v" optDerefOpName ["o"])
              (.return_ (.var "v")))
        (envExtend [("o", .optVal (some x))] "h" (.b true))
        ⟨1, [(0, ⟨0, true, [x, 1]⟩)], []⟩ [("o", 0, 0)] =
        .ok (((envExtend (envExtend [("o", .optVal (some x))] "h" (.b true))
          "v" (.i32 x)),
          ⟨1, [(0, ⟨0, true, [x, 1]⟩)], []⟩, [("o", 0, 0)]),
          .returned (.i32 x)) :=
      Eq.trans
        (memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepV) hretV
    have hifT : memEvalProgStmt optDerefProg F
        (.if_ (.var "h")
          (.seq (.callRet "v" optDerefOpName ["o"])
                (.return_ (.var "v")))
          (.return_ (.lit (.i32 (-1 : BitVec 32)))))
        (envExtend [("o", .optVal (some x))] "h" (.b true))
        ⟨1, [(0, ⟨0, true, [x, 1]⟩)], []⟩ [("o", 0, 0)] =
        .ok (((envExtend (envExtend [("o", .optVal (some x))] "h" (.b true))
          "v" (.i32 x)),
          ⟨1, [(0, ⟨0, true, [x, 1]⟩)], []⟩, [("o", 0, 0)]),
          .returned (.i32 x)) :=
      Eq.trans (memEvalProgStmt_if_true _ _ _ _ _ _ _ _ hcondT) hthen
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstepH, hifT]
    simp [optDerefFwd]

/-- Transfer for `opt_deref` (program level). -/
theorem memTransferProg_optDeref (F : Nat) (v : Option (BitVec 32))
    (_h : oracleNoalias optDerefFunc [.optVal v]) :
    memEvalProgFunc optDerefProg F optDerefFunc [.optVal v] =
      evalProgFunc optDerefProg F optDerefFunc [.optVal v] := by
  rw [memEvalProgFunc_optDeref, evalProgFunc_optDeref]

/-! ## N4d-iii `std::span` transfers: extent and words agree -/

/-- `memEval` for `_M_extent`: the extent word in memory matches the
    `spanVal` length (mirrors `evalFuncFuel_spanExtent`). -/
theorem memEvalFuncFuel_spanExtent (F : Nat) (l : List (BitVec 32)) :
    memEvalFuncFuel F spanExtentFunc [.spanVal l] = spanExtentFwd l := by
  have hb : bindMemArgs spanExtentFunc.args [.spanVal l] emptyMem =
      some ([("e", .spanVal l)],
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("e", 0, 0)]) :=
    bindMemArgs_spanVal "e" spanExtentObjTy l
  have hbody : spanExtentFunc.body = .return_ (.spanLen "e") := rfl
  have ho : envLookup [("e", .spanVal l)] "e" =
      some (.spanVal l) := by
    simp [envLookup]
  have hlay : layoutLookup [("e", 0, 0)] "e" = some (0, 0) := by
    simp [layoutLookup]
  have hmem : memLoad
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ 0 0 0 =
      .ok (BitVec.ofNat 32 l.length) := by
    simp [memLoad, memFind]
  have hagree := memEvalExpr_spanLen_hit "e" _ _ _ l 0 0 hlay ho hmem
  have heval : evalExpr (.spanLen "e") [("e", .spanVal l)] =
      .ok (.u64 (BitVec.ofNat 64 l.length)) :=
    evalExpr_spanLen_some "e" _ l ho
  have hret := memEvalStmtFuel_return F (.spanLen "e") _ _ _ _
    hagree heval
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  simp [spanExtentFwd]

/-- Transfer for `_M_extent`. -/
theorem memTransfer_spanExtent (F : Nat) (l : List (BitVec 32))
    (_h : oracleNoalias spanExtentFunc [.spanVal l]) :
    memEvalFuncFuel F spanExtentFunc [.spanVal l] =
      evalFuncFuel F spanExtentFunc [.spanVal l] := by
  rw [memEvalFuncFuel_spanExtent, evalFuncFuel_spanExtent]

/-- `memEval` for `size` (fused call edge). -/
theorem memEvalFuncFuel_spanSize (F : Nat) (l : List (BitVec 32)) :
    memEvalFuncFuel F spanSizeFunc [.spanVal l] = spanSizeFwd l := by
  have hb : bindMemArgs spanSizeFunc.args [.spanVal l] emptyMem =
      some ([("s", .spanVal l)],
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("s", 0, 0)]) :=
    bindMemArgs_spanVal "s" spanObjTy l
  have hbody : spanSizeFunc.body = .return_ (.spanLen "s") := rfl
  have ho : envLookup [("s", .spanVal l)] "s" =
      some (.spanVal l) := by
    simp [envLookup]
  have hlay : layoutLookup [("s", 0, 0)] "s" = some (0, 0) := by
    simp [layoutLookup]
  have hmem : memLoad
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ 0 0 0 =
      .ok (BitVec.ofNat 32 l.length) := by
    simp [memLoad, memFind]
  have hagree := memEvalExpr_spanLen_hit "s" _ _ _ l 0 0 hlay ho hmem
  have heval : evalExpr (.spanLen "s") [("s", .spanVal l)] =
      .ok (.u64 (BitVec.ofNat 64 l.length)) :=
    evalExpr_spanLen_some "s" _ l ho
  have hret := memEvalStmtFuel_return F (.spanLen "s") _ _ _ _
    hagree heval
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  simp [spanSizeFwd, spanExtentFwd]

/-- Transfer for `size`. -/
theorem memTransfer_spanSize (F : Nat) (l : List (BitVec 32))
    (_h : oracleNoalias spanSizeFunc [.spanVal l]) :
    memEvalFuncFuel F spanSizeFunc [.spanVal l] =
      evalFuncFuel F spanSizeFunc [.spanVal l] := by
  rw [memEvalFuncFuel_spanSize, evalFuncFuel_spanSize]

/-- `memEval` for `operator[]` (hit): the reified word in memory
    matches the `spanVal` word (mirrors `evalFuncFuel_spanIndex`,
    cf. `memEvalExpr_idxi_hit`). -/
theorem memEvalFuncFuel_spanIndex_hit (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64) (x : BitVec 32)
    (hget : l[n.toNat]? = some x) :
    memEvalFuncFuel F spanIndexFunc [.spanVal l, .u64 n] =
      spanIndexFwd l n := by
  have hb : bindMemArgs spanIndexFunc.args [.spanVal l, .u64 n] emptyMem =
      some ([("s", .spanVal l), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("s", 0, 0)]) :=
    bindMemArgs_spanIndex l n
  have hbody : spanIndexFunc.body =
      .return_ (.spanAt "s" (.var "n")) := rfl
  have hs : envLookup [("s", .spanVal l), ("n", .u64 n)] "s" =
      some (.spanVal l) := by
    simp [envLookup]
  have hn : envLookup [("s", .spanVal l), ("n", .u64 n)] "n" =
      some (.u64 n) := by
    simp [envLookup, show ("n" : String) ≠ "s" by decide]
  have hlay : layoutLookup [("s", 0, 0)] "s" = some (0, 0) := by
    simp [layoutLookup]
  have hie : memEvalExpr (.var "n") [("s", .spanVal l), ("n", .u64 n)]
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("s", 0, 0)] =
      evalExpr (.var "n") [("s", .spanVal l), ("n", .u64 n)] := by
    simp [memEvalExpr, evalExpr, hn]
  have hieval : evalExpr (.var "n") [("s", .spanVal l), ("n", .u64 n)] =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  have hmem : memLoad
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      0 0 (n.toNat + 1) = .ok x := by
    simp [memLoad, memFind, hget]
  have hagree := memEvalExpr_spanAt_hit "s" (.var "n") _ _ _
    l n x 0 0 hlay hs hie hieval hmem hget
  have heval : evalExpr (.spanAt "s" (.var "n"))
      [("s", .spanVal l), ("n", .u64 n)] = .ok (.i32 x) :=
    evalExpr_spanAt_some "s" _ _ _ _ _ hs hieval hget
  have hret := memEvalStmtFuel_return F (.spanAt "s" (.var "n")) _ _ _ _
    hagree heval
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  simp [spanIndexFwd, hget]

/-- `memEval` for `operator[]` (`OOB`): the memory load itself
    fails past the reified words. -/
theorem memEvalFuncFuel_spanIndex_oob (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64)
    (hget : l[n.toNat]? = none) :
    memEvalFuncFuel F spanIndexFunc [.spanVal l, .u64 n] =
      spanIndexFwd l n := by
  have hb : bindMemArgs spanIndexFunc.args [.spanVal l, .u64 n] emptyMem =
      some ([("s", .spanVal l), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("s", 0, 0)]) :=
    bindMemArgs_spanIndex l n
  have hbody : spanIndexFunc.body =
      .return_ (.spanAt "s" (.var "n")) := rfl
  have hs : envLookup [("s", .spanVal l), ("n", .u64 n)] "s" =
      some (.spanVal l) := by
    simp [envLookup]
  have hn : envLookup [("s", .spanVal l), ("n", .u64 n)] "n" =
      some (.u64 n) := by
    simp [envLookup, show ("n" : String) ≠ "s" by decide]
  have hlay : layoutLookup [("s", 0, 0)] "s" = some (0, 0) := by
    simp [layoutLookup]
  have hie : memEvalExpr (.var "n") [("s", .spanVal l), ("n", .u64 n)]
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("s", 0, 0)] =
      evalExpr (.var "n") [("s", .spanVal l), ("n", .u64 n)] := by
    simp [memEvalExpr, evalExpr, hn]
  have hieval : evalExpr (.var "n") [("s", .spanVal l), ("n", .u64 n)] =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  have hmem : memLoad
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      0 0 (n.toNat + 1) = .error .OOB := by
    simp [memLoad, memFind, hget]
  have hagree := memEvalExpr_spanAt_oob "s" (.var "n") _ _ _
    l n 0 0 hlay hs hie hieval hmem hget
  have heval : evalExpr (.spanAt "s" (.var "n"))
      [("s", .spanVal l), ("n", .u64 n)] = .error .OOB := by
    simp [evalExpr, hs, hn, hget]
  have hmemerr : memEvalExpr (.spanAt "s" (.var "n"))
      [("s", .spanVal l), ("n", .u64 n)]
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("s", 0, 0)] = .error .OOB := by
    rw [hagree, heval]
  have hret := memEvalStmtFuel_return_err F (.spanAt "s" (.var "n"))
    _ _ _ _ hmemerr
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  simp [spanIndexFwd, hget]

/-- Transfer for `operator[]` (both paths). -/
theorem memTransfer_spanIndex_hit (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64) (x : BitVec 32)
    (hget : l[n.toNat]? = some x)
    (_h : oracleNoalias spanIndexFunc [.spanVal l, .u64 n]) :
    memEvalFuncFuel F spanIndexFunc [.spanVal l, .u64 n] =
      evalFuncFuel F spanIndexFunc [.spanVal l, .u64 n] := by
  rw [memEvalFuncFuel_spanIndex_hit F l n x hget, evalFuncFuel_spanIndex]

/-- Transfer for `operator[]` (`OOB` path). -/
theorem memTransfer_spanIndex_oob (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64)
    (hget : l[n.toNat]? = none)
    (_h : oracleNoalias spanIndexFunc [.spanVal l, .u64 n]) :
    memEvalFuncFuel F spanIndexFunc [.spanVal l, .u64 n] =
      evalFuncFuel F spanIndexFunc [.spanVal l, .u64 n] := by
  rw [memEvalFuncFuel_spanIndex_oob F l n hget, evalFuncFuel_spanIndex]

/-- Memory loop condition reads the `u64` index against the reified
    extent (pure — mirrors `spanCond_eval`). -/
theorem memSpanCond_eval (l : List (BitVec 32)) (k : Nat)
    (acc : BitVec 32) (m : Mem) (π : Layout) (a : Addr) (t : Nat)
    (hk64 : k < 2 ^ 64) (hl64 : l.length < 2 ^ 64)
    (hlay : layoutLookup π "s" = some (a, t))
    (hmemlen : memLoad m a t 0 = .ok (BitVec.ofNat 32 l.length)) :
    memEvalExpr (.ult (.var "i") (.spanLen "s")) (mkSpanEnv l k acc)
      m π = .ok (.b (decide (k < l.length))) := by
  have hi := mkSpanEnv_i l k acc
  have hs := mkSpanEnv_s l k acc
  have hlen : (BitVec.ofNat 64 l.length).toNat = l.length :=
    ofNat64_toNat _ hl64
  simp only [memEvalExpr, hi, hs, hlay, hmemlen, hlen,
    ofNat64_ult k _ hk64, beq_self_eq_true, ↓reduceIte]

/-- Memory body with a successful add: accumulate and step, memory
    untouched (any fuel) — mirrors `spanBody_step_ok`. -/
theorem memSpanBody_step_ok (F : Nat) (l : List (BitVec 32)) (k : Nat)
    (acc x a : BitVec 32) (m : Mem) (π : Layout) (ad : Addr) (t : Nat)
    (_hk : k < l.length) (hk64 : k < 2 ^ 64) (_hl64 : l.length < 2 ^ 64)
    (hget : l[k]? = some x)
    (hc : checkedAddI32 acc x = .ok a)
    (hlay : layoutLookup π "s" = some (ad, t))
    (_hmemlen : memLoad m ad t 0 = .ok (BitVec.ofNat 32 l.length))
    (hmemall : ∀ (j : Nat) (y : BitVec 32),
      l[j]? = some y → memLoad m ad t (j + 1) = .ok y) :
    memEvalStmtFuel F spanBody (mkSpanEnv l k acc) m π =
      .ok (((mkSpanEnv l (k + 1) a, m, π)), .fellThrough) := by
  have hi := mkSpanEnv_i l k acc
  have ht := mkSpanEnv_t l k acc
  have hs := mkSpanEnv_s l k acc
  have htn : (BitVec.ofNat 64 k).toNat = k := ofNat64_toNat k hk64
  have hadd : memEvalExpr
      (.add (.var "t") (.spanAt "s" (.var "i")))
        (mkSpanEnv l k acc) m π = .ok (.i32 a) := by
    simp only [memEvalExpr, ht, hi, hs, hlay, htn, hget,
      hmemall k x hget, hc, Except.map, beq_self_eq_true, ↓reduceIte]
  have hincr : memEvalExpr
      (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1))))
        (mkSpanEnv l k a) m π =
        .ok (.u64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [memEvalExpr, litVal, mkSpanEnv_i l k a, ofNat64_add_one]
  have up1 := spanEnv_update_t l k acc a
  have up2 := spanEnv_update_i l k (k + 1) a
  cases F <;>
    simp [spanBody, memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      hadd, hincr, up1, up2]

/-- Memory body with an overflowing add: the `nsw` error is loud
    (any fuel) — mirrors `spanBody_step_err`. -/
theorem memSpanBody_step_err (F : Nat) (l : List (BitVec 32)) (k : Nat)
    (acc x : BitVec 32) (e : Panic) (m : Mem) (π : Layout)
    (ad : Addr) (t : Nat)
    (_hk : k < l.length) (hk64 : k < 2 ^ 64) (_hl64 : l.length < 2 ^ 64)
    (hget : l[k]? = some x)
    (hc : checkedAddI32 acc x = .error e)
    (hlay : layoutLookup π "s" = some (ad, t))
    (_hmemlen : memLoad m ad t 0 = .ok (BitVec.ofNat 32 l.length))
    (hmemall : ∀ (j : Nat) (y : BitVec 32),
      l[j]? = some y → memLoad m ad t (j + 1) = .ok y) :
    memEvalStmtFuel F spanBody (mkSpanEnv l k acc) m π = .error e := by
  have hi := mkSpanEnv_i l k acc
  have ht := mkSpanEnv_t l k acc
  have hs := mkSpanEnv_s l k acc
  have htn : (BitVec.ofNat 64 k).toNat = k := ofNat64_toNat k hk64
  have hadd : memEvalExpr
      (.add (.var "t") (.spanAt "s" (.var "i")))
        (mkSpanEnv l k acc) m π = .error e := by
    simp only [memEvalExpr, ht, hi, hs, hlay, htn, hget,
      hmemall k x hget, hc, Except.map, beq_self_eq_true, ↓reduceIte]
  cases F <;>
    simp [spanBody, memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      hadd]

/-- Memory loop correctness: folds the checked-add suffix with the
    memory cross-checked at every step, exits with `i = length`
    (fuel-generalized — the S3a `memSkipWhile_correct` shape). -/
theorem memSpanWhile_correct (l : List (BitVec 32))
    (F k : Nat) (acc : BitVec 32) (m : Mem) (π : Layout)
    (ad : Addr) (t : Nat)
    (hk : k ≤ l.length) (hl64 : l.length < 2 ^ 64)
    (hlay : layoutLookup π "s" = some (ad, t))
    (hmemlen : memLoad m ad t 0 = .ok (BitVec.ofNat 32 l.length))
    (hmemall : ∀ (j : Nat) (x : BitVec 32),
      l[j]? = some x → memLoad m ad t (j + 1) = .ok x)
    (hF : l.length - k + 1 ≤ F) :
    memEvalStmtFuel F spanWhile (mkSpanEnv l k acc) m π =
      match spanFold (l.drop k) acc with
      | .error e => .error e
      | .ok acc' => .ok (((mkSpanEnv l l.length acc', m, π)),
        .fellThrough) := by
  induction F generalizing k acc with
  | zero => omega
  | succ F ih =>
    by_cases hlt : k < l.length
    · have hk64 : k < 2 ^ 64 := by omega
      have hget : l[k]? = some l[k] := List.getElem?_eq_getElem hlt
      have hcond : memEvalExpr (.ult (.var "i") (.spanLen "s"))
            (mkSpanEnv l k acc) m π = .ok (.b true) := by
        simpa [hlt] using
          (memSpanCond_eval l k acc m π ad t hk64 hl64 hlay hmemlen)
      have hunfold := spanFold_step l k acc l[k] hget
      cases hc : checkedAddI32 acc l[k] with
      | error e =>
        have hbody := memSpanBody_step_err F l k acc l[k] e m π ad t
          hlt hk64 hl64 hget hc hlay hmemlen hmemall
        have hstep :
            memEvalStmtFuel (F + 1) spanWhile (mkSpanEnv l k acc) m π
            = .error e := by
          simp [spanWhile, memEvalStmtFuel, memEvalSuccHandler,
            memEvalStmtWith, hcond, hbody]
        rw [hstep, hunfold, hc]
      | ok a =>
        have hbody := memSpanBody_step_ok F l k acc l[k] a m π ad t
          hlt hk64 hl64 hget hc hlay hmemlen hmemall
        have hstep :
            memEvalStmtFuel (F + 1) spanWhile (mkSpanEnv l k acc) m π
            = memEvalStmtFuel F spanWhile (mkSpanEnv l (k + 1) a) m π := by
          simp [spanWhile, memEvalStmtFuel, memEvalSuccHandler,
            memEvalStmtWith, hcond, hbody]
        rw [hstep, hunfold, hc]
        exact ih (k + 1) a (by omega) (by omega)
    · have hkk : k = l.length := by omega
      subst hkk
      have hcond : memEvalExpr (.ult (.var "i") (.spanLen "s"))
            (mkSpanEnv l l.length acc) m π = .ok (.b false) := by
        have hfalse : (decide (l.length < l.length)) = false := by
          simp
        have hk64 : l.length < 2 ^ 64 := hl64
        have h := memSpanCond_eval l l.length acc m π ad t hk64 hl64
          hlay hmemlen
        rwa [hfalse] at h
      have hnil : spanFold [] acc = .ok acc := rfl
      simp [spanWhile, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith, hcond, hnil]

/-- `memEval` for `span_sum`, fuel-generalized — mirrors
    `evalFuncFuel_spanSum` (cf. `memEvalFuncFuel_skip`). -/
theorem memEvalFuncFuel_spanSum (F : Nat) (l : List (BitVec 32))
    (hl64 : l.length < 2 ^ 64) (hF : l.length + 1 ≤ F) :
    memEvalFuncFuel F spanSumFunc [.spanVal l] = spanSumFwd l := by
  have hbf : spanSumFunc.args =
      [{ name := "s", ty := spanObjTy, role := .sharedBorrow }] := rfl
  have hbody : spanSumFunc.body =
      .seq (.let_ "t" (.i 32) (.lit (.i32 (BitVec.ofNat 32 0))))
      (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.seq spanWhile
            (.return_ (.var "t")))) := rfl
  have hb : bindMemArgs
      [{ name := "s", ty := spanObjTy, role := .sharedBorrow }]
      [.spanVal l] emptyMem =
      some ([("s", .spanVal l)],
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("s", 0, 0)]) :=
    bindMemArgs_spanVal "s" spanObjTy l
  have henv : [("i", .u64 (BitVec.ofNat 64 0)),
        ("t", .i32 (BitVec.ofNat 32 0)),
        ("s", .spanVal l)]
      = mkSpanEnv l 0 (BitVec.ofNat 32 0) := rfl
  have hlay : layoutLookup [("s", 0, 0)] "s" = some (0, 0) := by
    simp [layoutLookup]
  have hmemlen : memLoad
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      0 0 0 = .ok (BitVec.ofNat 32 l.length) := by
    simp [memLoad, memFind]
  have hmemall : ∀ (j : Nat) (x : BitVec 32),
      l[j]? = some x →
      memLoad ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
        0 0 (j + 1) = .ok x := by
    intro j x hget
    simp [memLoad, memFind, hget]
  have hsret : ∀ acc' : BitVec 32,
      envLookup (mkSpanEnv l l.length acc') "t" = some (.i32 acc') :=
    fun acc' => mkSpanEnv_t l l.length acc'
  cases hfold : spanFold l (BitVec.ofNat 32 0) with
  | error e =>
    have hsum0 : spanSumFwd l = .error e := spanSumFwd_err l e hfold
    cases F with
    | zero =>
      have hloopH0 : memEvalStmtWith memEvalStmtZeroHandler
            spanWhile (mkSpanEnv l 0 (BitVec.ofNat 32 0))
            ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
            [("s", 0, 0)] = .error e := by
        have h := memSpanWhile_correct l 0 0 (BitVec.ofNat 32 0)
          ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
          [("s", 0, 0)] 0 0 (Nat.zero_le _) hl64 hlay hmemlen hmemall
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      simp only [memEvalFuncFuel, hbf, hbody, hb]
      simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
        memEvalExpr, litVal, henv, hloopH0, hsum0]
    | succ F =>
      have hloopS :
          memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
            spanWhile (mkSpanEnv l 0 (BitVec.ofNat 32 0))
            ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
            [("s", 0, 0)] = .error e := by
        have h := memSpanWhile_correct l (F + 1) 0 (BitVec.ofNat 32 0)
          ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
          [("s", 0, 0)] 0 0 (Nat.zero_le _) hl64 hlay hmemlen hmemall
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      simp only [memEvalFuncFuel, hbf, hbody, hb]
      simp [memEvalStmtFuel, memEvalStmtWith,
        memEvalExpr, litVal, henv, hloopS, hsum0]
  | ok acc' =>
    have hsum' : spanSumFwd l = .ok (.i32 acc') :=
      spanSumFwd_ok l acc' hfold
    cases F with
    | zero =>
      have hloopH0 : memEvalStmtWith memEvalStmtZeroHandler
            spanWhile (mkSpanEnv l 0 (BitVec.ofNat 32 0))
            ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
            [("s", 0, 0)] =
            .ok ((((mkSpanEnv l l.length acc',
              ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
              [("s", 0, 0)]))), .fellThrough) := by
        have h := memSpanWhile_correct l 0 0 (BitVec.ofNat 32 0)
          ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
          [("s", 0, 0)] 0 0 (Nat.zero_le _) hl64 hlay hmemlen hmemall
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      have hsret' := hsret acc'
      simp only [memEvalFuncFuel, hbf, hbody, hb]
      simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
        memEvalExpr, litVal, henv, hloopH0, hsret', hsum']
    | succ F =>
      have hloopS :
          memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
            spanWhile (mkSpanEnv l 0 (BitVec.ofNat 32 0))
            ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
            [("s", 0, 0)] =
            .ok ((((mkSpanEnv l l.length acc',
              ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
              [("s", 0, 0)]))), .fellThrough) := by
        have h := memSpanWhile_correct l (F + 1) 0 (BitVec.ofNat 32 0)
          ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
          [("s", 0, 0)] 0 0 (Nat.zero_le _) hl64 hlay hmemlen hmemall
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      have hsret' := hsret acc'
      simp only [memEvalFuncFuel, hbf, hbody, hb]
      simp [memEvalStmtFuel, memEvalStmtWith,
        memEvalExpr, litVal, henv, hloopS, hsret', hsum']

/-- Transfer for `span_sum`: both sides equal `spanSumFwd`. -/
theorem memTransfer_spanSum (F : Nat) (l : List (BitVec 32))
    (hl64 : l.length < 2 ^ 64) (hF : l.length + 1 ≤ F)
    (_h : oracleNoalias spanSumFunc [.spanVal l]) :
    memEvalFuncFuel F spanSumFunc [.spanVal l] =
      evalFuncFuel F spanSumFunc [.spanVal l] := by
  rw [memEvalFuncFuel_spanSum F l hl64 hF, evalFuncFuel_spanSum F l hl64 hF]


/-! ## N4d-iv-a `std::vector` transfers: length and words agree -/

/-- `memEval` for `size` (fused projection pair + `ptr_diff` + `cast`). -/
theorem memEvalFuncFuel_stdVecSize (F : Nat) (l : List (BitVec 32)) :
    memEvalFuncFuel F stdVecSizeFunc [.stdVecVal l] = stdVecSizeFwd l := by
  have hb : bindMemArgs stdVecSizeFunc.args [.stdVecVal l] emptyMem =
      some ([("s", .stdVecVal l)],
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("s", 0, 0)]) :=
    bindMemArgs_stdVecVal "s" stdVecObjTy l
  have hbody : stdVecSizeFunc.body = .return_ (.stdVecLen "s") := rfl
  have ho : envLookup [("s", .stdVecVal l)] "s" =
      some (.stdVecVal l) := by
    simp [envLookup]
  have hlay : layoutLookup [("s", 0, 0)] "s" = some (0, 0) := by
    simp [layoutLookup]
  have hmem : memLoad
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩ 0 0 0 =
      .ok (BitVec.ofNat 32 l.length) := by
    simp [memLoad, memFind]
  have hagree := memEvalExpr_stdVecLen_hit "s" _ _ _ l 0 0 hlay ho hmem
  have heval : evalExpr (.stdVecLen "s") [("s", .stdVecVal l)] =
      .ok (.u64 (BitVec.ofNat 64 l.length)) :=
    evalExpr_stdVecLen_some "s" _ l ho
  have hret := memEvalStmtFuel_return F (.stdVecLen "s") _ _ _ _
    hagree heval
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  simp [stdVecSizeFwd]

/-- Transfer for `size`. -/
theorem memTransfer_stdVecSize (F : Nat) (l : List (BitVec 32))
    (_h : oracleNoalias stdVecSizeFunc [.stdVecVal l]) :
    memEvalFuncFuel F stdVecSizeFunc [.stdVecVal l] =
      evalFuncFuel F stdVecSizeFunc [.stdVecVal l] := by
  rw [memEvalFuncFuel_stdVecSize, evalFuncFuel_stdVecSize]

/-- `memEval` for `operator[]` (hit): the reified word in memory
    matches the `stdVecVal` word (mirrors `evalFuncFuel_stdVecIndex`,
    cf. `memEvalExpr_idxi_hit`). -/
theorem memEvalFuncFuel_stdVecIndex_hit (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64) (x : BitVec 32)
    (hget : l[n.toNat]? = some x) :
    memEvalFuncFuel F stdVecIndexFunc [.stdVecVal l, .u64 n] =
      stdVecIndexFwd l n := by
  have hb : bindMemArgs stdVecIndexFunc.args [.stdVecVal l, .u64 n] emptyMem =
      some ([("s", .stdVecVal l), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("s", 0, 0)]) :=
    bindMemArgs_stdVecIndex l n
  have hbody : stdVecIndexFunc.body =
      .return_ (.stdVecAt "s" (.var "n")) := rfl
  have hs : envLookup [("s", .stdVecVal l), ("n", .u64 n)] "s" =
      some (.stdVecVal l) := by
    simp [envLookup]
  have hn : envLookup [("s", .stdVecVal l), ("n", .u64 n)] "n" =
      some (.u64 n) := by
    simp [envLookup, show ("n" : String) ≠ "s" by decide]
  have hlay : layoutLookup [("s", 0, 0)] "s" = some (0, 0) := by
    simp [layoutLookup]
  have hie : memEvalExpr (.var "n") [("s", .stdVecVal l), ("n", .u64 n)]
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("s", 0, 0)] =
      evalExpr (.var "n") [("s", .stdVecVal l), ("n", .u64 n)] := by
    simp [memEvalExpr, evalExpr, hn]
  have hieval : evalExpr (.var "n") [("s", .stdVecVal l), ("n", .u64 n)] =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  have hmem : memLoad
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      0 0 (n.toNat + 1) = .ok x := by
    simp [memLoad, memFind, hget]
  have hagree := memEvalExpr_stdVecAt_hit "s" (.var "n") _ _ _
    l n x 0 0 hlay hs hie hieval hmem hget
  have heval : evalExpr (.stdVecAt "s" (.var "n"))
      [("s", .stdVecVal l), ("n", .u64 n)] = .ok (.i32 x) :=
    evalExpr_stdVecAt_some "s" _ _ _ _ _ hs hieval hget
  have hret := memEvalStmtFuel_return F (.stdVecAt "s" (.var "n")) _ _ _ _
    hagree heval
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  simp [stdVecIndexFwd, hget]

/-- `memEval` for `operator[]` (`OOB`): the memory load itself
    fails past the reified words. -/
theorem memEvalFuncFuel_stdVecIndex_oob (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64)
    (hget : l[n.toNat]? = none) :
    memEvalFuncFuel F stdVecIndexFunc [.stdVecVal l, .u64 n] =
      stdVecIndexFwd l n := by
  have hb : bindMemArgs stdVecIndexFunc.args [.stdVecVal l, .u64 n] emptyMem =
      some ([("s", .stdVecVal l), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("s", 0, 0)]) :=
    bindMemArgs_stdVecIndex l n
  have hbody : stdVecIndexFunc.body =
      .return_ (.stdVecAt "s" (.var "n")) := rfl
  have hs : envLookup [("s", .stdVecVal l), ("n", .u64 n)] "s" =
      some (.stdVecVal l) := by
    simp [envLookup]
  have hn : envLookup [("s", .stdVecVal l), ("n", .u64 n)] "n" =
      some (.u64 n) := by
    simp [envLookup, show ("n" : String) ≠ "s" by decide]
  have hlay : layoutLookup [("s", 0, 0)] "s" = some (0, 0) := by
    simp [layoutLookup]
  have hie : memEvalExpr (.var "n") [("s", .stdVecVal l), ("n", .u64 n)]
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("s", 0, 0)] =
      evalExpr (.var "n") [("s", .stdVecVal l), ("n", .u64 n)] := by
    simp [memEvalExpr, evalExpr, hn]
  have hieval : evalExpr (.var "n") [("s", .stdVecVal l), ("n", .u64 n)] =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  have hmem : memLoad
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      0 0 (n.toNat + 1) = .error .OOB := by
    simp [memLoad, memFind, hget]
  have hagree := memEvalExpr_stdVecAt_oob "s" (.var "n") _ _ _
    l n 0 0 hlay hs hie hieval hmem hget
  have heval : evalExpr (.stdVecAt "s" (.var "n"))
      [("s", .stdVecVal l), ("n", .u64 n)] = .error .OOB := by
    simp [evalExpr, hs, hn, hget]
  have hmemerr : memEvalExpr (.stdVecAt "s" (.var "n"))
      [("s", .stdVecVal l), ("n", .u64 n)]
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("s", 0, 0)] = .error .OOB := by
    rw [hagree, heval]
  have hret := memEvalStmtFuel_return_err F (.stdVecAt "s" (.var "n"))
    _ _ _ _ hmemerr
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  simp [stdVecIndexFwd, hget]

/-- Transfer for `operator[]` (both paths). -/
theorem memTransfer_stdVecIndex_hit (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64) (x : BitVec 32)
    (hget : l[n.toNat]? = some x)
    (_h : oracleNoalias stdVecIndexFunc [.stdVecVal l, .u64 n]) :
    memEvalFuncFuel F stdVecIndexFunc [.stdVecVal l, .u64 n] =
      evalFuncFuel F stdVecIndexFunc [.stdVecVal l, .u64 n] := by
  rw [memEvalFuncFuel_stdVecIndex_hit F l n x hget, evalFuncFuel_stdVecIndex]

/-- Transfer for `operator[]` (`OOB` path). -/
theorem memTransfer_stdVecIndex_oob (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64)
    (hget : l[n.toNat]? = none)
    (_h : oracleNoalias stdVecIndexFunc [.stdVecVal l, .u64 n]) :
    memEvalFuncFuel F stdVecIndexFunc [.stdVecVal l, .u64 n] =
      evalFuncFuel F stdVecIndexFunc [.stdVecVal l, .u64 n] := by
  rw [memEvalFuncFuel_stdVecIndex_oob F l n hget, evalFuncFuel_stdVecIndex]

/-- Memory loop condition reads the `u64` index against the reified
    length (pure — mirrors `stdVecCond_eval`). -/
theorem memStdVecCond_eval (l : List (BitVec 32)) (k : Nat)
    (acc : BitVec 32) (m : Mem) (π : Layout) (a : Addr) (t : Nat)
    (hk64 : k < 2 ^ 64) (hl64 : l.length < 2 ^ 64)
    (hlay : layoutLookup π "s" = some (a, t))
    (hmemlen : memLoad m a t 0 = .ok (BitVec.ofNat 32 l.length)) :
    memEvalExpr (.ult (.var "i") (.stdVecLen "s")) (mkStdVecEnv l k acc)
      m π = .ok (.b (decide (k < l.length))) := by
  have hi := mkStdVecEnv_i l k acc
  have hs := mkStdVecEnv_s l k acc
  have hlen : (BitVec.ofNat 64 l.length).toNat = l.length :=
    ofNat64_toNat _ hl64
  simp only [memEvalExpr, hi, hs, hlay, hmemlen, hlen,
    ofNat64_ult k _ hk64, beq_self_eq_true, ↓reduceIte]

/-- Memory body with a successful add: accumulate and step, memory
    untouched (any fuel) — mirrors `stdVecBody_step_ok`. -/
theorem memStdVecBody_step_ok (F : Nat) (l : List (BitVec 32)) (k : Nat)
    (acc x a : BitVec 32) (m : Mem) (π : Layout) (ad : Addr) (t : Nat)
    (_hk : k < l.length) (hk64 : k < 2 ^ 64) (_hl64 : l.length < 2 ^ 64)
    (hget : l[k]? = some x)
    (hc : checkedAddI32 acc x = .ok a)
    (hlay : layoutLookup π "s" = some (ad, t))
    (_hmemlen : memLoad m ad t 0 = .ok (BitVec.ofNat 32 l.length))
    (hmemall : ∀ (j : Nat) (y : BitVec 32),
      l[j]? = some y → memLoad m ad t (j + 1) = .ok y) :
    memEvalStmtFuel F stdVecBody (mkStdVecEnv l k acc) m π =
      .ok (((mkStdVecEnv l (k + 1) a, m, π)), .fellThrough) := by
  have hi := mkStdVecEnv_i l k acc
  have ht := mkStdVecEnv_t l k acc
  have hs := mkStdVecEnv_s l k acc
  have htn : (BitVec.ofNat 64 k).toNat = k := ofNat64_toNat k hk64
  have hadd : memEvalExpr
      (.add (.var "t") (.stdVecAt "s" (.var "i")))
        (mkStdVecEnv l k acc) m π = .ok (.i32 a) := by
    simp only [memEvalExpr, ht, hi, hs, hlay, htn, hget,
      hmemall k x hget, hc, Except.map, beq_self_eq_true, ↓reduceIte]
  have hincr : memEvalExpr
      (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1))))
        (mkStdVecEnv l k a) m π =
        .ok (.u64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [memEvalExpr, litVal, mkStdVecEnv_i l k a, ofNat64_add_one]
  have up1 := stdVecEnv_update_t l k acc a
  have up2 := stdVecEnv_update_i l k (k + 1) a
  cases F <;>
    simp [stdVecBody, memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      hadd, hincr, up1, up2]

/-- Memory body with an overflowing add: the `nsw` error is loud
    (any fuel) — mirrors `stdVecBody_step_err`. -/
theorem memStdVecBody_step_err (F : Nat) (l : List (BitVec 32)) (k : Nat)
    (acc x : BitVec 32) (e : Panic) (m : Mem) (π : Layout)
    (ad : Addr) (t : Nat)
    (_hk : k < l.length) (hk64 : k < 2 ^ 64) (_hl64 : l.length < 2 ^ 64)
    (hget : l[k]? = some x)
    (hc : checkedAddI32 acc x = .error e)
    (hlay : layoutLookup π "s" = some (ad, t))
    (_hmemlen : memLoad m ad t 0 = .ok (BitVec.ofNat 32 l.length))
    (hmemall : ∀ (j : Nat) (y : BitVec 32),
      l[j]? = some y → memLoad m ad t (j + 1) = .ok y) :
    memEvalStmtFuel F stdVecBody (mkStdVecEnv l k acc) m π = .error e := by
  have hi := mkStdVecEnv_i l k acc
  have ht := mkStdVecEnv_t l k acc
  have hs := mkStdVecEnv_s l k acc
  have htn : (BitVec.ofNat 64 k).toNat = k := ofNat64_toNat k hk64
  have hadd : memEvalExpr
      (.add (.var "t") (.stdVecAt "s" (.var "i")))
        (mkStdVecEnv l k acc) m π = .error e := by
    simp only [memEvalExpr, ht, hi, hs, hlay, htn, hget,
      hmemall k x hget, hc, Except.map, beq_self_eq_true, ↓reduceIte]
  cases F <;>
    simp [stdVecBody, memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      hadd]

/-- Memory loop correctness: folds the checked-add suffix with the
    memory cross-checked at every step, exits with `i = length`
    (fuel-generalized — the S3a `memSkipWhile_correct` shape). -/
theorem memStdVecWhile_correct (l : List (BitVec 32))
    (F k : Nat) (acc : BitVec 32) (m : Mem) (π : Layout)
    (ad : Addr) (t : Nat)
    (hk : k ≤ l.length) (hl64 : l.length < 2 ^ 64)
    (hlay : layoutLookup π "s" = some (ad, t))
    (hmemlen : memLoad m ad t 0 = .ok (BitVec.ofNat 32 l.length))
    (hmemall : ∀ (j : Nat) (x : BitVec 32),
      l[j]? = some x → memLoad m ad t (j + 1) = .ok x)
    (hF : l.length - k + 1 ≤ F) :
    memEvalStmtFuel F stdVecWhile (mkStdVecEnv l k acc) m π =
      match stdVecFold (l.drop k) acc with
      | .error e => .error e
      | .ok acc' => .ok (((mkStdVecEnv l l.length acc', m, π)),
        .fellThrough) := by
  induction F generalizing k acc with
  | zero => omega
  | succ F ih =>
    by_cases hlt : k < l.length
    · have hk64 : k < 2 ^ 64 := by omega
      have hget : l[k]? = some l[k] := List.getElem?_eq_getElem hlt
      have hcond : memEvalExpr (.ult (.var "i") (.stdVecLen "s"))
            (mkStdVecEnv l k acc) m π = .ok (.b true) := by
        simpa [hlt] using
          (memStdVecCond_eval l k acc m π ad t hk64 hl64 hlay hmemlen)
      have hunfold := stdVecFold_step l k acc l[k] hget
      cases hc : checkedAddI32 acc l[k] with
      | error e =>
        have hbody := memStdVecBody_step_err F l k acc l[k] e m π ad t
          hlt hk64 hl64 hget hc hlay hmemlen hmemall
        have hstep :
            memEvalStmtFuel (F + 1) stdVecWhile (mkStdVecEnv l k acc) m π
            = .error e := by
          simp [stdVecWhile, memEvalStmtFuel, memEvalSuccHandler,
            memEvalStmtWith, hcond, hbody]
        rw [hstep, hunfold, hc]
      | ok a =>
        have hbody := memStdVecBody_step_ok F l k acc l[k] a m π ad t
          hlt hk64 hl64 hget hc hlay hmemlen hmemall
        have hstep :
            memEvalStmtFuel (F + 1) stdVecWhile (mkStdVecEnv l k acc) m π
            = memEvalStmtFuel F stdVecWhile (mkStdVecEnv l (k + 1) a) m π := by
          simp [stdVecWhile, memEvalStmtFuel, memEvalSuccHandler,
            memEvalStmtWith, hcond, hbody]
        rw [hstep, hunfold, hc]
        exact ih (k + 1) a (by omega) (by omega)
    · have hkk : k = l.length := by omega
      subst hkk
      have hcond : memEvalExpr (.ult (.var "i") (.stdVecLen "s"))
            (mkStdVecEnv l l.length acc) m π = .ok (.b false) := by
        have hfalse : (decide (l.length < l.length)) = false := by
          simp
        have hk64 : l.length < 2 ^ 64 := hl64
        have h := memStdVecCond_eval l l.length acc m π ad t hk64 hl64
          hlay hmemlen
        rwa [hfalse] at h
      have hnil : stdVecFold [] acc = .ok acc := rfl
      simp [stdVecWhile, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith, hcond, hnil]

/-- `memEval` for `vec_read_sum`, fuel-generalized — mirrors
    `evalFuncFuel_stdVecReadSum` (cf. `memEvalFuncFuel_skip`). -/
theorem memEvalFuncFuel_stdVecReadSum (F : Nat) (l : List (BitVec 32))
    (hl64 : l.length < 2 ^ 64) (hF : l.length + 1 ≤ F) :
    memEvalFuncFuel F stdVecReadSumFunc [.stdVecVal l] = stdVecReadSumFwd l := by
  have hbf : stdVecReadSumFunc.args =
      [{ name := "s", ty := stdVecObjTy, role := .sharedBorrow }] := rfl
  have hbody : stdVecReadSumFunc.body =
      .seq (.let_ "t" (.i 32) (.lit (.i32 (BitVec.ofNat 32 0))))
      (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.seq stdVecWhile
            (.return_ (.var "t")))) := rfl
  have hb : bindMemArgs
      [{ name := "s", ty := stdVecObjTy, role := .sharedBorrow }]
      [.stdVecVal l] emptyMem =
      some ([("s", .stdVecVal l)],
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("s", 0, 0)]) :=
    bindMemArgs_stdVecVal "s" stdVecObjTy l
  have henv : [("i", .u64 (BitVec.ofNat 64 0)),
        ("t", .i32 (BitVec.ofNat 32 0)),
        ("s", .stdVecVal l)]
      = mkStdVecEnv l 0 (BitVec.ofNat 32 0) := rfl
  have hlay : layoutLookup [("s", 0, 0)] "s" = some (0, 0) := by
    simp [layoutLookup]
  have hmemlen : memLoad
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      0 0 0 = .ok (BitVec.ofNat 32 l.length) := by
    simp [memLoad, memFind]
  have hmemall : ∀ (j : Nat) (x : BitVec 32),
      l[j]? = some x →
      memLoad ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
        0 0 (j + 1) = .ok x := by
    intro j x hget
    simp [memLoad, memFind, hget]
  have hsret : ∀ acc' : BitVec 32,
      envLookup (mkStdVecEnv l l.length acc') "t" = some (.i32 acc') :=
    fun acc' => mkStdVecEnv_t l l.length acc'
  cases hfold : stdVecFold l (BitVec.ofNat 32 0) with
  | error e =>
    have hsum0 : stdVecReadSumFwd l = .error e := stdVecReadSumFwd_err l e hfold
    cases F with
    | zero =>
      have hloopH0 : memEvalStmtWith memEvalStmtZeroHandler
            stdVecWhile (mkStdVecEnv l 0 (BitVec.ofNat 32 0))
            ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
            [("s", 0, 0)] = .error e := by
        have h := memStdVecWhile_correct l 0 0 (BitVec.ofNat 32 0)
          ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
          [("s", 0, 0)] 0 0 (Nat.zero_le _) hl64 hlay hmemlen hmemall
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      simp only [memEvalFuncFuel, hbf, hbody, hb]
      simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
        memEvalExpr, litVal, henv, hloopH0, hsum0]
    | succ F =>
      have hloopS :
          memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
            stdVecWhile (mkStdVecEnv l 0 (BitVec.ofNat 32 0))
            ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
            [("s", 0, 0)] = .error e := by
        have h := memStdVecWhile_correct l (F + 1) 0 (BitVec.ofNat 32 0)
          ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
          [("s", 0, 0)] 0 0 (Nat.zero_le _) hl64 hlay hmemlen hmemall
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      simp only [memEvalFuncFuel, hbf, hbody, hb]
      simp [memEvalStmtFuel, memEvalStmtWith,
        memEvalExpr, litVal, henv, hloopS, hsum0]
  | ok acc' =>
    have hsum' : stdVecReadSumFwd l = .ok (.i32 acc') :=
      stdVecReadSumFwd_ok l acc' hfold
    cases F with
    | zero =>
      have hloopH0 : memEvalStmtWith memEvalStmtZeroHandler
            stdVecWhile (mkStdVecEnv l 0 (BitVec.ofNat 32 0))
            ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
            [("s", 0, 0)] =
            .ok ((((mkStdVecEnv l l.length acc',
              ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
              [("s", 0, 0)]))), .fellThrough) := by
        have h := memStdVecWhile_correct l 0 0 (BitVec.ofNat 32 0)
          ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
          [("s", 0, 0)] 0 0 (Nat.zero_le _) hl64 hlay hmemlen hmemall
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      have hsret' := hsret acc'
      simp only [memEvalFuncFuel, hbf, hbody, hb]
      simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
        memEvalExpr, litVal, henv, hloopH0, hsret', hsum']
    | succ F =>
      have hloopS :
          memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
            stdVecWhile (mkStdVecEnv l 0 (BitVec.ofNat 32 0))
            ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
            [("s", 0, 0)] =
            .ok ((((mkStdVecEnv l l.length acc',
              ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
              [("s", 0, 0)]))), .fellThrough) := by
        have h := memStdVecWhile_correct l (F + 1) 0 (BitVec.ofNat 32 0)
          ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
          [("s", 0, 0)] 0 0 (Nat.zero_le _) hl64 hlay hmemlen hmemall
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      have hsret' := hsret acc'
      simp only [memEvalFuncFuel, hbf, hbody, hb]
      simp [memEvalStmtFuel, memEvalStmtWith,
        memEvalExpr, litVal, henv, hloopS, hsret', hsum']

/-- Transfer for `vec_read_sum`: both sides equal `stdVecReadSumFwd`. -/
theorem memTransfer_stdVecReadSum (F : Nat) (l : List (BitVec 32))
    (hl64 : l.length < 2 ^ 64) (hF : l.length + 1 ≤ F)
    (_h : oracleNoalias stdVecReadSumFunc [.stdVecVal l]) :
    memEvalFuncFuel F stdVecReadSumFunc [.stdVecVal l] =
      evalFuncFuel F stdVecReadSumFunc [.stdVecVal l] := by
  rw [memEvalFuncFuel_stdVecReadSum F l hl64 hF, evalFuncFuel_stdVecReadSum F l hl64 hF]



/-! ## M3d C++ transfers: `methodSum` leaf + `pointSumRef` entry (N1a) -/

/-- `add` of two projected fields agrees on the memory side (the
    method-leaf shape; cf. `evalExpr_add_fget_fget` on the value side
    and `memEvalExpr_add_fget_var` for the `translate` shape). -/
theorem memEvalExpr_add_fget_fget (ρ : Env) (m : Mem) (π : Layout)
    (obj : String) (tag : String) (fields : List (String × BitVec 32))
    (px py : BitVec 32)
    (hobj : envLookup ρ obj = some (.structVal tag fields))
    (hfx : fieldLookup fields "x" = some px)
    (hfy : fieldLookup fields "y" = some py) :
    memEvalExpr (.add (.fget obj "x") (.fget obj "y")) ρ m π =
      (checkedAddI32 px py).map .i32 := by
  simp [memEvalExpr, hobj, hfx, hfy]

/-- `memEval` for the method leaf: evaluation agrees with the forward
    on all inputs (mirrors `evalFuncFuel_methodSum`; `this` binds a
    `Point` value, so no layout pin is consulted and memory is
    untouched). -/
theorem memEvalFuncFuel_methodSum (F : Nat) (px py : BitVec 32) :
    memEvalFuncFuel F methodSumFunc
      [.structVal "Point" [("x", px), ("y", py)]] =
      methodSumFwd px py := by
  have hbind : bindMemArgs methodSumFunc.args
      [.structVal "Point" [("x", px), ("y", py)]] emptyMem =
      some ([("this", .structVal "Point" [("x", px), ("y", py)])],
        emptyMem, []) := by
    show bindMemArgs
      [{ name := "this", ty := .struct "Point" [.i 32, .i 32],
         role := .owned }]
      [.structVal "Point" [("x", px), ("y", py)]] emptyMem = _
    exact bindMemArgs_methodSum px py
  have hbody : methodSumFunc.body =
      .return_ (.add (.fget "this" "x") (.fget "this" "y")) := rfl
  have hthis := envLookup_methodSum_this px py
  have hfx := fieldLookup_methodSum_x px py
  have hfy := fieldLookup_methodSum_y px py
  have hadd : memEvalExpr (.add (.fget "this" "x") (.fget "this" "y"))
      [("this", .structVal "Point" [("x", px), ("y", py)])] emptyMem [] =
      (checkedAddI32 px py).map .i32 :=
    memEvalExpr_add_fget_fget _ _ _ _ _ _ _ _ hthis hfx hfy
  have heval : evalExpr (.add (.fget "this" "x") (.fget "this" "y"))
      [("this", .structVal "Point" [("x", px), ("y", py)])] =
      (checkedAddI32 px py).map .i32 :=
    evalExpr_add_fget_fget _ _ _ _ _ _ hthis hfx hfy
  have hagree : memEvalExpr (.add (.fget "this" "x") (.fget "this" "y"))
      [("this", .structVal "Point" [("x", px), ("y", py)])] emptyMem [] =
      evalExpr (.add (.fget "this" "x") (.fget "this" "y"))
        [("this", .structVal "Point" [("x", px), ("y", py)])] := by
    rw [hadd, heval]
  cases h : checkedAddI32 px py with
  | error e =>
    have hadd' : memEvalExpr (.add (.fget "this" "x") (.fget "this" "y"))
        [("this", .structVal "Point" [("x", px), ("y", py)])] emptyMem [] =
        .error e := by
      rw [hadd, h]
      exact i32_map_error e
    have hret : memEvalStmtFuel F
        (.return_ (.add (.fget "this" "x") (.fget "this" "y")))
        [("this", .structVal "Point" [("x", px), ("y", py)])] emptyMem [] =
        .error e := by
      cases F <;>
        simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, hadd']
    simp only [memEvalFuncFuel, hbind, hbody, hret, methodSumFwd, h,
      i32_map_error]
  | ok s =>
    have hv : evalExpr (.add (.fget "this" "x") (.fget "this" "y"))
        [("this", .structVal "Point" [("x", px), ("y", py)])] =
        .ok (.i32 s) := by
      rw [heval, h]
      exact i32_map_ok s
    have hret : memEvalStmtFuel F
        (.return_ (.add (.fget "this" "x") (.fget "this" "y")))
        [("this", .structVal "Point" [("x", px), ("y", py)])] emptyMem [] =
        .ok (([("this", .structVal "Point" [("x", px), ("y", py)])],
          emptyMem, []), .returned (.i32 s)) :=
      memEvalStmtFuel_return _ _ _ _ _ (.i32 s) hagree hv
    simp only [memEvalFuncFuel, hbind, hbody, hret, methodSumFwd, h,
      i32_map_ok]

/-- Transfer for the method leaf: both sides equal `methodSumFwd`. -/
theorem memTransfer_methodSum (F : Nat) (px py : BitVec 32)
    (_h : oracleNoalias methodSumFunc
      [.structVal "Point" [("x", px), ("y", py)]]) :
    memEvalFuncFuel F methodSumFunc
      [.structVal "Point" [("x", px), ("y", py)]] =
      evalFuncFuel F methodSumFunc
        [.structVal "Point" [("x", px), ("y", py)]] := by
  rw [memEvalFuncFuel_methodSum, evalFuncFuel_methodSum]

/-- `memEval` for the `point_sum_ref` entry: program evaluation over
    `[methodSumFunc]` agrees with the delegating forward (mirrors
    `evalProgFunc_pointSumRef`; caller `Mem`/`Layout` stay
    `emptyMem`/`[]` — the callee runs on its own fresh entry blocks). -/
theorem memEvalProgFunc_pointSumRef (F : Nat) (px py : BitVec 32) :
    memEvalProgFunc [methodSumFunc] F pointSumRefFunc
      [.structVal "Point" [("x", px), ("y", py)]] =
      pointSumRefFwd px py := by
  have hbind : bindMemArgs pointSumRefFunc.args
      [.structVal "Point" [("x", px), ("y", py)]] emptyMem =
      some ([("p", .structVal "Point" [("x", px), ("y", py)])],
        emptyMem, []) :=
    bindMemArgs_pointSumRef px py
  have hbody : pointSumRefFunc.body =
      .seq (.callRet "s" "_ZNK5Point3sumEv" ["p"])
           (.return_ (.var "s")) := rfl
  have hp := envLookup_pointSumRef_p px py
  have hfind : findFunc [methodSumFunc] "_ZNK5Point3sumEv" =
      some methodSumFunc :=
    findFunc_hit methodSumFunc []
  have hargs : lookupArgs [("p", .structVal "Point" [("x", px), ("y", py)])]
      ["p"] = some [.structVal "Point" [("x", px), ("y", py)]] := by
    simp [lookupArgs, hp]
  have hcall := memEvalFuncFuel_methodSum F px py
  cases hsum : methodSumFwd px py with
  | error e =>
    have hcall' : memEvalFuncFuel F methodSumFunc
        [.structVal "Point" [("x", px), ("y", py)]] = .error e := by
      rw [hcall, hsum]
    have hstep := memEvalProgStmt_callRet_err [methodSumFunc] F "s"
      "_ZNK5Point3sumEv" ["p"]
      [("p", .structVal "Point" [("x", px), ("y", py)])]
      emptyMem []
      [.structVal "Point" [("x", px), ("y", py)]] methodSumFunc e hargs
      hfind hcall'
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_err _ _ _ _ _ _ _ _ hstep]
    simp [pointSumRefFwd, hsum]
  | ok v =>
    have hcall' : memEvalFuncFuel F methodSumFunc
        [.structVal "Point" [("x", px), ("y", py)]] = .ok v := by
      rw [hcall, hsum]
    have hstep := memEvalProgStmt_callRet_ok [methodSumFunc] F "s"
      "_ZNK5Point3sumEv" ["p"]
      [("p", .structVal "Point" [("x", px), ("y", py)])]
      emptyMem []
      [.structVal "Point" [("x", px), ("y", py)]] methodSumFunc v hargs
      hfind hcall'
    have hret : memEvalProgStmt [methodSumFunc] F (.return_ (.var "s"))
        (envExtend [("p", .structVal "Point" [("x", px), ("y", py)])]
          "s" v) emptyMem [] =
        .ok ((envExtend [("p", .structVal "Point" [("x", px), ("y", py)])]
          "s" v, emptyMem, []), .returned v) :=
      memEvalProgStmt_return [methodSumFunc] F (.var "s") _
        _ _ v (by simp [memEvalExpr, envExtend_hit])
    simp only [memEvalProgFunc, hbind, hbody]
    rw [memEvalProgStmt_seq_fallthrough _ _ _ _ _ _ _ _ _ _ hstep, hret]
    simp [pointSumRefFwd, hsum]

/-- Transfer for `point_sum_ref` (program level): both sides equal
    `pointSumRefFwd`. -/
theorem memTransferProg_pointSumRef (F : Nat) (px py : BitVec 32)
    (_h : oracleNoalias pointSumRefFunc
      [.structVal "Point" [("x", px), ("y", py)]]) :
    memEvalProgFunc [methodSumFunc] F pointSumRefFunc
      [.structVal "Point" [("x", px), ("y", py)]] =
      evalProgFunc [methodSumFunc] F pointSumRefFunc
        [.structVal "Point" [("x", px), ("y", py)]] := by
  rw [memEvalProgFunc_pointSumRef, evalProgFunc_pointSumRef]

