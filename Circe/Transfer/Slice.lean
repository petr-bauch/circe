/-
Circe.Transfer.Slice — N4d-i/ii/iii/iv-a slice transfers plus the M3d `methodSum` leaf.
Over `Circe.Transfer.Flow`.
-/
import Circe.Transfer.Flow
import Circe.Emit.VecAt
import Circe.Emit.VecAtSum
import Circe.Emit.Reborrow
import Circe.Emit.WrPair
import Circe.Emit.CondPair
import Circe.Emit.AliasCond
import Circe.CondFrame

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
      (.u64 0) (by simp) (by simp) (by simp) rfl
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


/-! ## N7a `std::string_view` transfers: length and bytes agree -/

/-- Memory condition for the view loop: the `u64` index against
    the reified length (mirrors `memSpanCond_eval`). -/
theorem memViewCond_eval (l : List (BitVec 8)) (k : Nat)
    (acc : BitVec 32) (m : Mem) (π : Layout) (a : Addr) (t : Nat)
    (hk64 : k < 2 ^ 64) (hl64 : l.length < 2 ^ 64)
    (hlay : layoutLookup π "s" = some (a, t))
    (hmemlen : memLoad m a t 0 = .ok (BitVec.ofNat 32 l.length)) :
    memEvalExpr (.ult (.var "i") (.viewLen "s")) (mkViewEnv l k acc)
      m π = .ok (.b (decide (k < l.length))) := by
  have hi := mkViewEnv_i l k acc
  have hs := mkViewEnv_s l k acc
  have hlen : (BitVec.ofNat 64 l.length).toNat = l.length :=
    ofNat64_toNat _ hl64
  simp only [memEvalExpr, hi, hs, hlay, hmemlen, hlen,
    ofNat64_ult k _ hk64, beq_self_eq_true, ↓reduceIte]

/-- Memory body with a successful add: accumulate and step, memory
    untouched (any fuel) — mirrors `memSpanBody_step_ok`. -/
theorem memViewBody_step_ok (F : Nat) (l : List (BitVec 8)) (k : Nat)
    (acc : BitVec 32) (b : BitVec 8) (a : BitVec 32)
    (m : Mem) (π : Layout) (ad : Addr) (t : Nat)
    (_hk : k < l.length) (hk64 : k < 2 ^ 64) (_hl64 : l.length < 2 ^ 64)
    (hget : l[k]? = some b)
    (hc : checkedAddI32 acc (b.signExtend 32) = .ok a)
    (hlay : layoutLookup π "s" = some (ad, t))
    (_hmemlen : memLoad m ad t 0 = .ok (BitVec.ofNat 32 l.length))
    (hmemall : ∀ (j : Nat) (y : BitVec 8),
      l[j]? = some y →
        memLoad m ad t (j + 1) = .ok (BitVec.ofNat 32 y.toNat)) :
    memEvalStmtFuel F viewBody (mkViewEnv l k acc) m π =
      .ok (((mkViewEnv l (k + 1) a, m, π)), .fellThrough) := by
  have hi := mkViewEnv_i l k acc
  have ht := mkViewEnv_t l k acc
  have hs := mkViewEnv_s l k acc
  have htn : (BitVec.ofNat 64 k).toNat = k := ofNat64_toNat k hk64
  have hadd : memEvalExpr
      (.add (.var "t") (.viewAt "s" (.var "i")))
        (mkViewEnv l k acc) m π = .ok (.i32 a) := by
    simp only [memEvalExpr, ht, hi, hs, hlay, htn, hget,
      hmemall k b hget, hc, Except.map, beq_self_eq_true, ↓reduceIte]
  have hincr : memEvalExpr
      (.uadd (.var "i") (.lit (.u64 (BitVec.ofNat 64 1))))
        (mkViewEnv l k a) m π =
        .ok (.u64 (BitVec.ofNat 64 (k + 1))) := by
    simp only [memEvalExpr, litVal, mkViewEnv_i l k a, ofNat64_add_one]
  have up1 := viewEnv_update_t l k acc a
  have up2 := viewEnv_update_i l k (k + 1) a
  cases F <;>
    simp [viewBody, memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      hadd, hincr, up1, up2]

/-- Memory body with an overflowing add: the `nsw` error is loud
    (any fuel) — mirrors `memSpanBody_step_err`. -/
theorem memViewBody_step_err (F : Nat) (l : List (BitVec 8)) (k : Nat)
    (acc : BitVec 32) (b : BitVec 8) (e : Panic)
    (m : Mem) (π : Layout) (ad : Addr) (t : Nat)
    (_hk : k < l.length) (hk64 : k < 2 ^ 64) (_hl64 : l.length < 2 ^ 64)
    (hget : l[k]? = some b)
    (hc : checkedAddI32 acc (b.signExtend 32) = .error e)
    (hlay : layoutLookup π "s" = some (ad, t))
    (_hmemlen : memLoad m ad t 0 = .ok (BitVec.ofNat 32 l.length))
    (hmemall : ∀ (j : Nat) (y : BitVec 8),
      l[j]? = some y →
        memLoad m ad t (j + 1) = .ok (BitVec.ofNat 32 y.toNat)) :
    memEvalStmtFuel F viewBody (mkViewEnv l k acc) m π = .error e := by
  have hi := mkViewEnv_i l k acc
  have ht := mkViewEnv_t l k acc
  have hs := mkViewEnv_s l k acc
  have htn : (BitVec.ofNat 64 k).toNat = k := ofNat64_toNat k hk64
  have hadd : memEvalExpr
      (.add (.var "t") (.viewAt "s" (.var "i")))
        (mkViewEnv l k acc) m π = .error e := by
    simp only [memEvalExpr, ht, hi, hs, hlay, htn, hget,
      hmemall k b hget, hc, Except.map, beq_self_eq_true, ↓reduceIte]
  cases F <;>
    simp [viewBody, memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      hadd]

/-- Memory loop correctness: folds the checked-add suffix with the
    memory cross-checked at every step, exits with `i = length`
    (fuel-generalized — the S3a `memSkipWhile_correct` shape). -/
theorem memViewWhile_correct (l : List (BitVec 8))
    (F k : Nat) (acc : BitVec 32) (m : Mem) (π : Layout)
    (ad : Addr) (t : Nat)
    (hk : k ≤ l.length) (hl64 : l.length < 2 ^ 64)
    (hlay : layoutLookup π "s" = some (ad, t))
    (hmemlen : memLoad m ad t 0 = .ok (BitVec.ofNat 32 l.length))
    (hmemall : ∀ (j : Nat) (y : BitVec 8),
      l[j]? = some y →
        memLoad m ad t (j + 1) = .ok (BitVec.ofNat 32 y.toNat))
    (hF : l.length - k + 1 ≤ F) :
    memEvalStmtFuel F viewWhile (mkViewEnv l k acc) m π =
      match viewFold (l.drop k) acc with
      | .error e => .error e
      | .ok acc' => .ok (((mkViewEnv l l.length acc', m, π)),
        .fellThrough) := by
  induction F generalizing k acc with
  | zero => omega
  | succ F ih =>
    by_cases hlt : k < l.length
    · have hk64 : k < 2 ^ 64 := by omega
      have hget : l[k]? = some l[k] := List.getElem?_eq_getElem hlt
      have hcond : memEvalExpr (.ult (.var "i") (.viewLen "s"))
            (mkViewEnv l k acc) m π = .ok (.b true) := by
        simpa [hlt] using
          (memViewCond_eval l k acc m π ad t hk64 hl64 hlay hmemlen)
      have hunfold := viewFold_step l k acc l[k] hget
      cases hc : checkedAddI32 acc ((l[k]).signExtend 32) with
      | error e =>
        have hbody := memViewBody_step_err F l k acc l[k] e m π ad t
          hlt hk64 hl64 hget hc hlay hmemlen hmemall
        have hstep :
            memEvalStmtFuel (F + 1) viewWhile (mkViewEnv l k acc) m π
            = .error e := by
          simp [viewWhile, memEvalStmtFuel, memEvalSuccHandler,
            memEvalStmtWith, hcond, hbody]
        rw [hstep, hunfold, hc]
      | ok a =>
        have hbody := memViewBody_step_ok F l k acc l[k] a m π ad t
          hlt hk64 hl64 hget hc hlay hmemlen hmemall
        have hstep :
            memEvalStmtFuel (F + 1) viewWhile (mkViewEnv l k acc) m π
            = memEvalStmtFuel F viewWhile (mkViewEnv l (k + 1) a) m π := by
          simp [viewWhile, memEvalStmtFuel, memEvalSuccHandler,
            memEvalStmtWith, hcond, hbody]
        rw [hstep, hunfold, hc]
        exact ih (k + 1) a (by omega) (by omega)
    · have hkk : k = l.length := by omega
      subst hkk
      have hcond : memEvalExpr (.ult (.var "i") (.viewLen "s"))
            (mkViewEnv l l.length acc) m π = .ok (.b false) := by
        have hfalse : (decide (l.length < l.length)) = false := by
          simp
        have hk64 : l.length < 2 ^ 64 := hl64
        have h := memViewCond_eval l l.length acc m π ad t hk64 hl64
          hlay hmemlen
        rwa [hfalse] at h
      have hnil : viewFold [] acc = .ok acc := rfl
      simp [viewWhile, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith, hcond, hnil]

/-- `memEval` for `view_sum`, fuel-generalized — mirrors
    `memEvalFuncFuel_spanSum`. -/
theorem memEvalFuncFuel_viewSum (F : Nat) (l : List (BitVec 8))
    (hl64 : l.length < 2 ^ 64) (hF : l.length + 1 ≤ F) :
    memEvalFuncFuel F viewSumFunc [.viewVal l] = viewSumFwd l := by
  have hbf : viewSumFunc.args =
      [{ name := "s", ty := viewObjTy, role := .sharedBorrow }] := rfl
  have hbody : viewSumFunc.body =
      .seq (.let_ "t" (.i 32) (.lit (.i32 (BitVec.ofNat 32 0))))
      (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.seq viewWhile
            (.return_ (.var "t")))) := rfl
  have hb : bindMemArgs
      [{ name := "s", ty := viewObjTy, role := .sharedBorrow }]
      [.viewVal l] emptyMem =
      some ([("s", .viewVal l)],
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) ::
          l.map (fun x => BitVec.ofNat 32 x.toNat)⟩)], []⟩,
        [("s", 0, 0)]) :=
    bindMemArgs_viewVal "s" viewObjTy l
  have henv : [("i", .u64 (BitVec.ofNat 64 0)),
        ("t", .i32 (BitVec.ofNat 32 0)),
        ("s", .viewVal l)]
      = mkViewEnv l 0 (BitVec.ofNat 32 0) := rfl
  have hlay : layoutLookup [("s", 0, 0)] "s" = some (0, 0) := by
    simp [layoutLookup]
  have hmemlen : memLoad
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) ::
        l.map (fun x => BitVec.ofNat 32 x.toNat)⟩)], []⟩
      0 0 0 = .ok (BitVec.ofNat 32 l.length) := by
    simp [memLoad, memFind]
  have hmemall : ∀ (j : Nat) (y : BitVec 8),
      l[j]? = some y →
      memLoad ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) ::
        l.map (fun x => BitVec.ofNat 32 x.toNat)⟩)], []⟩
        0 0 (j + 1) = .ok (BitVec.ofNat 32 y.toNat) := by
    intro j y hget
    simp [memLoad, memFind, hget]
  have hsret : ∀ acc' : BitVec 32,
      envLookup (mkViewEnv l l.length acc') "t" = some (.i32 acc') :=
    fun acc' => mkViewEnv_t l l.length acc'
  cases hfold : viewFold l (BitVec.ofNat 32 0) with
  | error e =>
    have hsum0 : viewSumFwd l = .error e := viewSumFwd_err l e hfold
    cases F with
    | zero =>
      have hloopH0 : memEvalStmtWith memEvalStmtZeroHandler
            viewWhile (mkViewEnv l 0 (BitVec.ofNat 32 0))
            ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) ::
              l.map (fun x => BitVec.ofNat 32 x.toNat)⟩)], []⟩
            [("s", 0, 0)] = .error e := by
        have h := memViewWhile_correct l 0 0 (BitVec.ofNat 32 0)
          ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) ::
            l.map (fun x => BitVec.ofNat 32 x.toNat)⟩)], []⟩
          [("s", 0, 0)] 0 0 (Nat.zero_le _) hl64 hlay hmemlen hmemall
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      simp only [memEvalFuncFuel, hbf, hbody, hb]
      simp only [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
        memEvalExpr, litVal, henv, hloopH0, hsum0]
    | succ F =>
      have hloopS :
          memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
            viewWhile (mkViewEnv l 0 (BitVec.ofNat 32 0))
            ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) ::
              l.map (fun x => BitVec.ofNat 32 x.toNat)⟩)], []⟩
            [("s", 0, 0)] = .error e := by
        have h := memViewWhile_correct l (F + 1) 0 (BitVec.ofNat 32 0)
          ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) ::
            l.map (fun x => BitVec.ofNat 32 x.toNat)⟩)], []⟩
          [("s", 0, 0)] 0 0 (Nat.zero_le _) hl64 hlay hmemlen hmemall
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      simp only [memEvalFuncFuel, hbf, hbody, hb]
      simp only [memEvalStmtFuel, memEvalStmtWith,
        memEvalExpr, litVal, henv, hloopS, hsum0]
  | ok acc' =>
    have hsum' : viewSumFwd l = .ok (.i32 acc') :=
      viewSumFwd_ok l acc' hfold
    cases F with
    | zero =>
      have hloopH0 : memEvalStmtWith memEvalStmtZeroHandler
            viewWhile (mkViewEnv l 0 (BitVec.ofNat 32 0))
            ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) ::
              l.map (fun x => BitVec.ofNat 32 x.toNat)⟩)], []⟩
            [("s", 0, 0)] =
            .ok ((((mkViewEnv l l.length acc',
              ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) ::
                l.map (fun x => BitVec.ofNat 32 x.toNat)⟩)], []⟩,
              [("s", 0, 0)]))), .fellThrough) := by
        have h := memViewWhile_correct l 0 0 (BitVec.ofNat 32 0)
          ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) ::
            l.map (fun x => BitVec.ofNat 32 x.toNat)⟩)], []⟩
          [("s", 0, 0)] 0 0 (Nat.zero_le _) hl64 hlay hmemlen hmemall
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      have hsret' := hsret acc'
      simp only [memEvalFuncFuel, hbf, hbody, hb]
      simp only [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
        memEvalExpr, litVal, henv, hloopH0, hsret', hsum']
    | succ F =>
      have hloopS :
          memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel F))
            viewWhile (mkViewEnv l 0 (BitVec.ofNat 32 0))
            ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) ::
              l.map (fun x => BitVec.ofNat 32 x.toNat)⟩)], []⟩
            [("s", 0, 0)] =
            .ok ((((mkViewEnv l l.length acc',
              ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) ::
                l.map (fun x => BitVec.ofNat 32 x.toNat)⟩)], []⟩,
              [("s", 0, 0)]))), .fellThrough) := by
        have h := memViewWhile_correct l (F + 1) 0 (BitVec.ofNat 32 0)
          ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) ::
            l.map (fun x => BitVec.ofNat 32 x.toNat)⟩)], []⟩
          [("s", 0, 0)] 0 0 (Nat.zero_le _) hl64 hlay hmemlen hmemall
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      have hsret' := hsret acc'
      simp only [memEvalFuncFuel, hbf, hbody, hb]
      simp only [memEvalStmtFuel, memEvalStmtWith,
        memEvalExpr, litVal, henv, hloopS, hsret', hsum']

/-- Transfer for `view_sum`: both sides equal `viewSumFwd`. -/
theorem memTransfer_viewSum (F : Nat) (l : List (BitVec 8))
    (hl64 : l.length < 2 ^ 64) (hF : l.length + 1 ≤ F)
    (_h : oracleNoalias viewSumFunc [.viewVal l]) :
    memEvalFuncFuel F viewSumFunc [.viewVal l] =
      evalFuncFuel F viewSumFunc [.viewVal l] := by
  rw [memEvalFuncFuel_viewSum F l hl64 hF, evalFuncFuel_viewSum F l hl64 hF]


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


/-! ## `at()` checked reads: guard agrees, reads agree, aborts agree -/

/-- Shared guard agreement: the `ult n size` condition evaluates
    identically on both sides (memory rides alongside, untouched). -/
theorem memStdVecGuard_agree (l : List (BitVec 32)) (n : BitVec 64)
    (ρ : Env) (m : Mem) (π : Layout)
    (hs : envLookup ρ "s" = some (.stdVecVal l))
    (_hn : envLookup ρ "n" = some (.u64 n))
    (hlay : layoutLookup π "s" = some (0, 0))
    (hmem : memLoad m 0 0 0 = .ok (BitVec.ofNat 32 l.length)) :
    memEvalExpr (.ult (.var "n") (.stdVecLen "s")) ρ m π =
      evalExpr (.ult (.var "n") (.stdVecLen "s")) ρ := by
  have hmlen : memEvalExpr (.stdVecLen "s") ρ m π =
      evalExpr (.stdVecLen "s") ρ :=
    memEvalExpr_stdVecLen_hit "s" _ _ _ l 0 0 hlay hs hmem
  have hmnv : memEvalExpr (.var "n") ρ m π =
      evalExpr (.var "n") ρ :=
    memEvalExpr_var _ _ _ _
  exact memEvalExpr_ult_agree (.var "n") (.stdVecLen "s") _ _ _ hmnv hmlen

/-- `memEval` for `_M_range_check` (hit): guard true, echo index. -/
theorem memEvalFuncFuel_stdVecRangeCheck_hit (F : Nat)
    (l : List (BitVec 32)) (n : BitVec 64)
    (hlen64 : l.length < 2 ^ 64) (hle : n.toNat < l.length) :
    memEvalFuncFuel F stdVecRangeCheckFunc [.stdVecVal l, .u64 n] =
      stdVecRangeCheckFwd l n := by
  have hb : bindMemArgs stdVecRangeCheckFunc.args [.stdVecVal l, .u64 n]
      emptyMem =
      some ([("s", .stdVecVal l), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("s", 0, 0)]) :=
    bindMemArgs_stdVecIndex l n
  have hbody : stdVecRangeCheckFunc.body =
      .if_ (.ult (.var "n") (.stdVecLen "s"))
        (.return_ (.var "n"))
        .fail := rfl
  have hs : envLookup [("s", .stdVecVal l), ("n", .u64 n)] "s" =
      some (.stdVecVal l) := by
    simp [envLookup]
  have hn : envLookup [("s", .stdVecVal l), ("n", .u64 n)] "n" =
      some (.u64 n) := by
    simp [envLookup, show ("n" : String) ≠ "s" by decide]
  have hlay : layoutLookup [("s", 0, 0)] "s" = some (0, 0) := by
    simp [layoutLookup]
  have hmem : memLoad
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      0 0 0 = .ok (BitVec.ofNat 32 l.length) := by
    simp [memLoad, memFind]
  have hmc := memStdVecGuard_agree l n _ _ _ hs hn hlay hmem
  have hc : memEvalExpr (.ult (.var "n") (.stdVecLen "s"))
      [("s", .stdVecVal l), ("n", .u64 n)]
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("s", 0, 0)] = .ok (.b true) := by
    rw [hmc]
    have hv := stdVecRangeCheckCond_eval l n hlen64
    simpa [hle] using hv
  have hfwd : stdVecRangeCheckFwd l n = .ok (.u64 n) :=
    stdVecRangeCheckFwd_ok l n hle
  have hnv : evalExpr (.var "n") [("s", .stdVecVal l), ("n", .u64 n)] =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  have hmnv : memEvalExpr (.var "n") [("s", .stdVecVal l), ("n", .u64 n)]
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("s", 0, 0)] =
      evalExpr (.var "n") [("s", .stdVecVal l), ("n", .u64 n)] :=
    memEvalExpr_var _ _ _ _
  have hret := memEvalStmtFuel_return F (.var "n") _ _ _ _ hmnv hnv
  have hstmt : memEvalStmtFuel F stdVecRangeCheckFunc.body
      [("s", .stdVecVal l), ("n", .u64 n)]
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("s", 0, 0)] =
      .ok ((([("s", .stdVecVal l), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("s", 0, 0)])),
        .returned (.u64 n)) := by
    rw [hbody]
    exact (memEvalStmtFuel_if_true F _ _ _ _ _ _ hc).trans hret
  simp only [memEvalFuncFuel, hb, hstmt, hfwd]

/-- `memEval` for `_M_range_check` (abort): guard false, loud abort
    on both sides (the throw never touches memory). -/
theorem memEvalFuncFuel_stdVecRangeCheck_fail (F : Nat)
    (l : List (BitVec 32)) (n : BitVec 64)
    (hlen64 : l.length < 2 ^ 64) (hlt : ¬ n.toNat < l.length) :
    memEvalFuncFuel F stdVecRangeCheckFunc [.stdVecVal l, .u64 n] =
      stdVecRangeCheckFwd l n := by
  have hb : bindMemArgs stdVecRangeCheckFunc.args [.stdVecVal l, .u64 n]
      emptyMem =
      some ([("s", .stdVecVal l), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("s", 0, 0)]) :=
    bindMemArgs_stdVecIndex l n
  have hbody : stdVecRangeCheckFunc.body =
      .if_ (.ult (.var "n") (.stdVecLen "s"))
        (.return_ (.var "n"))
        .fail := rfl
  have hs : envLookup [("s", .stdVecVal l), ("n", .u64 n)] "s" =
      some (.stdVecVal l) := by
    simp [envLookup]
  have hn : envLookup [("s", .stdVecVal l), ("n", .u64 n)] "n" =
      some (.u64 n) := by
    simp [envLookup, show ("n" : String) ≠ "s" by decide]
  have hlay : layoutLookup [("s", 0, 0)] "s" = some (0, 0) := by
    simp [layoutLookup]
  have hmem : memLoad
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      0 0 0 = .ok (BitVec.ofNat 32 l.length) := by
    simp [memLoad, memFind]
  have hmc := memStdVecGuard_agree l n _ _ _ hs hn hlay hmem
  have hc : memEvalExpr (.ult (.var "n") (.stdVecLen "s"))
      [("s", .stdVecVal l), ("n", .u64 n)]
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("s", 0, 0)] = .ok (.b false) := by
    rw [hmc]
    have hv := stdVecRangeCheckCond_eval l n hlen64
    simpa [hlt] using hv
  have hfwd : stdVecRangeCheckFwd l n = .error .AssertFail :=
    stdVecRangeCheckFwd_fail l n hlt
  have hmfail : memEvalStmtFuel F .fail
      [("s", .stdVecVal l), ("n", .u64 n)]
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("s", 0, 0)] = .error .AssertFail :=
    memEvalStmtFuel_fail F _ _ _
  have hstmt : memEvalStmtFuel F stdVecRangeCheckFunc.body
      [("s", .stdVecVal l), ("n", .u64 n)]
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("s", 0, 0)] = .error .AssertFail := by
    rw [hbody]
    exact (memEvalStmtFuel_if_false F _ _ _ _ _ _ hc).trans hmfail
  simp only [memEvalFuncFuel, hb, hstmt, hfwd]

/-- Transfer for `_M_range_check` (both paths). -/
theorem memTransfer_stdVecRangeCheck_hit (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64) (hlen64 : l.length < 2 ^ 64)
    (hle : n.toNat < l.length)
    (_h : oracleNoalias stdVecRangeCheckFunc [.stdVecVal l, .u64 n]) :
    memEvalFuncFuel F stdVecRangeCheckFunc [.stdVecVal l, .u64 n] =
      evalFuncFuel F stdVecRangeCheckFunc [.stdVecVal l, .u64 n] := by
  rw [memEvalFuncFuel_stdVecRangeCheck_hit F l n hlen64 hle,
    evalFuncFuel_stdVecRangeCheck F l n hlen64]

/-- Transfer for `_M_range_check` (abort path). -/
theorem memTransfer_stdVecRangeCheck_fail (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64) (hlen64 : l.length < 2 ^ 64)
    (hlt : ¬ n.toNat < l.length)
    (_h : oracleNoalias stdVecRangeCheckFunc [.stdVecVal l, .u64 n]) :
    memEvalFuncFuel F stdVecRangeCheckFunc [.stdVecVal l, .u64 n] =
      evalFuncFuel F stdVecRangeCheckFunc [.stdVecVal l, .u64 n] := by
  rw [memEvalFuncFuel_stdVecRangeCheck_fail F l n hlen64 hlt,
    evalFuncFuel_stdVecRangeCheck_fail F l n hlen64 hlt]
  exact stdVecRangeCheckFwd_fail l n hlt

/-- `memEval` for `at()` (all inputs; the guard splits internally,
    mirroring `evalFuncFuel_stdVecAt`). -/
theorem memEvalFuncFuel_stdVecAt (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64) (hlen64 : l.length < 2 ^ 64) :
    memEvalFuncFuel F stdVecAtFunc [.stdVecVal l, .u64 n] =
      stdVecAtFwd l n := by
  have hb : bindMemArgs stdVecAtFunc.args [.stdVecVal l, .u64 n] emptyMem =
      some ([("s", .stdVecVal l), ("n", .u64 n)],
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("s", 0, 0)]) :=
    bindMemArgs_stdVecIndex l n
  have hbody : stdVecAtFunc.body =
      .if_ (.ult (.var "n") (.stdVecLen "s"))
        (.return_ (.stdVecAt "s" (.var "n")))
        .fail := rfl
  have hs : envLookup [("s", .stdVecVal l), ("n", .u64 n)] "s" =
      some (.stdVecVal l) := by
    simp [envLookup]
  have hn : envLookup [("s", .stdVecVal l), ("n", .u64 n)] "n" =
      some (.u64 n) := by
    simp [envLookup, show ("n" : String) ≠ "s" by decide]
  have hlay : layoutLookup [("s", 0, 0)] "s" = some (0, 0) := by
    simp [layoutLookup]
  have hmem : memLoad
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      0 0 0 = .ok (BitVec.ofNat 32 l.length) := by
    simp [memLoad, memFind]
  have hmc := memStdVecGuard_agree l n _ _ _ hs hn hlay hmem
  have hnv : evalExpr (.var "n") [("s", .stdVecVal l), ("n", .u64 n)] =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  have hmnv : memEvalExpr (.var "n") [("s", .stdVecVal l), ("n", .u64 n)]
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("s", 0, 0)] =
      evalExpr (.var "n") [("s", .stdVecVal l), ("n", .u64 n)] :=
    memEvalExpr_var _ _ _ _
  by_cases h : n.toNat < l.length
  · have hne : l[n.toNat]? ≠ none := by
      rw [ne_eq, List.getElem?_eq_none_iff]
      omega
    obtain ⟨x, hget'⟩ := Option.ne_none_iff_exists.mp hne
    have hget : l[n.toNat]? = some x := by simpa using hget'.symm
    have hc : memEvalExpr (.ult (.var "n") (.stdVecLen "s"))
        [("s", .stdVecVal l), ("n", .u64 n)]
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
        [("s", 0, 0)] = .ok (.b true) := by
      rw [hmc]
      simpa [h] using stdVecRangeCheckCond_eval l n hlen64
    have hfwd : stdVecAtFwd l n = .ok (.i32 x) :=
      stdVecAtFwd_ok l n x h hget
    have hmemload : memLoad
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
        0 0 (n.toNat + 1) = .ok x := by
      simp [memLoad, memFind, hget]
    have hagree := memEvalExpr_stdVecAt_hit "s" (.var "n") _ _ _
      l n x 0 0 hlay hs hmnv hnv hmemload hget
    have heval : evalExpr (.stdVecAt "s" (.var "n"))
        [("s", .stdVecVal l), ("n", .u64 n)] = .ok (.i32 x) :=
      evalExpr_stdVecAt_some "s" _ _ _ _ _ hs hnv hget
    have hret := memEvalStmtFuel_return F (.stdVecAt "s" (.var "n"))
      _ _ _ _ hagree heval
    have hstmt : memEvalStmtFuel F stdVecAtFunc.body
        [("s", .stdVecVal l), ("n", .u64 n)]
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
        [("s", 0, 0)] =
        .ok ((([("s", .stdVecVal l), ("n", .u64 n)],
          ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
          [("s", 0, 0)])),
          .returned (.i32 x)) := by
      rw [hbody]
      exact (memEvalStmtFuel_if_true F _ _ _ _ _ _ hc).trans hret
    simp only [memEvalFuncFuel, hb, hstmt, hfwd]
  · have hc : memEvalExpr (.ult (.var "n") (.stdVecLen "s"))
        [("s", .stdVecVal l), ("n", .u64 n)]
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
        [("s", 0, 0)] = .ok (.b false) := by
      rw [hmc]
      simpa [h] using stdVecRangeCheckCond_eval l n hlen64
    have hfwd : stdVecAtFwd l n = .error .AssertFail :=
      stdVecAtFwd_fail l n h
    have hmfail : memEvalStmtFuel F .fail
        [("s", .stdVecVal l), ("n", .u64 n)]
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
        [("s", 0, 0)] = .error .AssertFail :=
      memEvalStmtFuel_fail F _ _ _
    have hstmt : memEvalStmtFuel F stdVecAtFunc.body
        [("s", .stdVecVal l), ("n", .u64 n)]
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
        [("s", 0, 0)] = .error .AssertFail := by
      rw [hbody]
      exact (memEvalStmtFuel_if_false F _ _ _ _ _ _ hc).trans hmfail
    simp only [memEvalFuncFuel, hb, hstmt, hfwd]

/-- Transfer for `at()` (both paths). -/
theorem memTransfer_stdVecAt (F : Nat) (l : List (BitVec 32))
    (n : BitVec 64) (hlen64 : l.length < 2 ^ 64)
    (_h : oracleNoalias stdVecAtFunc [.stdVecVal l, .u64 n]) :
    memEvalFuncFuel F stdVecAtFunc [.stdVecVal l, .u64 n] =
      evalFuncFuel F stdVecAtFunc [.stdVecVal l, .u64 n] := by
  rw [memEvalFuncFuel_stdVecAt F l n hlen64,
    evalFuncFuel_stdVecAt F l n hlen64]

/-- `memEval` for the entry (all inputs; the guard splits internally,
    mirroring `evalFuncFuel_vecAtOne`). -/
theorem memEvalFuncFuel_vecAtOne (F : Nat) (l : List (BitVec 32))
    (hlen64 : l.length < 2 ^ 64) :
    memEvalFuncFuel F vecAtOneFunc [.stdVecVal l] = vecAtOneFwd l := by
  have hb : bindMemArgs vecAtOneFunc.args [.stdVecVal l] emptyMem =
      some ([("v", .stdVecVal l)],
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
        [("v", 0, 0)]) :=
    bindMemArgs_stdVecVal "v" stdVecObjTy l
  have hbody : vecAtOneFunc.body =
      .if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "v"))
        (.return_ (.stdVecAt "v" (.lit (.u64 (BitVec.ofNat 64 0)))))
        .fail := rfl
  have hv : envLookup [("v", .stdVecVal l)] "v" =
      some (.stdVecVal l) := by
    simp [envLookup]
  have hlay : layoutLookup [("v", 0, 0)] "v" = some (0, 0) := by
    simp [layoutLookup]
  have hmem : memLoad
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      0 0 0 = .ok (BitVec.ofNat 32 l.length) := by
    simp [memLoad, memFind]
  have hmlen : memEvalExpr (.stdVecLen "v") [("v", .stdVecVal l)]
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("v", 0, 0)] =
      evalExpr (.stdVecLen "v") [("v", .stdVecVal l)] :=
    memEvalExpr_stdVecLen_hit "v" _ _ _ l 0 0 hlay hv hmem
  have hmlit : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("v", .stdVecVal l)]
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("v", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0))) [("v", .stdVecVal l)] :=
    memEvalExpr_lit _ _ _ _
  have hmc : memEvalExpr
      (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "v"))
      [("v", .stdVecVal l)]
      ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
      [("v", 0, 0)] =
      evalExpr
        (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "v"))
        [("v", .stdVecVal l)] :=
    memEvalExpr_ult_agree (.lit (.u64 (BitVec.ofNat 64 0)))
      (.stdVecLen "v") _ _ _ hmlit hmlen
  have hzero : (BitVec.ofNat 64 0).toNat = 0 := ofNat64_toNat 0 (by omega)
  have hlit : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("v", .stdVecVal l)] = .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  by_cases h : 0 < l.length
  · have hne : l[(0 : Nat)]? ≠ none := by
      rw [ne_eq, List.getElem?_eq_none_iff]
      omega
    obtain ⟨x, hget'⟩ := Option.ne_none_iff_exists.mp hne
    have hget : l[0]? = some x := by simpa using hget'.symm
    have hc : memEvalExpr
        (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "v"))
        [("v", .stdVecVal l)]
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
        [("v", 0, 0)] = .ok (.b true) := by
      rw [hmc]
      simpa [h] using vecAtOneCond_eval l hlen64
    have hfwd : vecAtOneFwd l = .ok (.i32 x) := by
      simp [vecAtOneFwd, hget]
    have hget0 : l[(BitVec.ofNat 64 0).toNat]? = some x := by
      rw [hzero]; exact hget
    have hmemload : memLoad
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
        0 0 ((BitVec.ofNat 64 0).toNat + 1) = .ok x := by
      rw [hzero]; simp [memLoad, memFind, hget]
    have hagree := memEvalExpr_stdVecAt_hit "v"
      (.lit (.u64 (BitVec.ofNat 64 0))) _ _ _
      l (BitVec.ofNat 64 0) x 0 0 hlay hv hmlit hlit hmemload hget0
    have heval : evalExpr
        (.stdVecAt "v" (.lit (.u64 (BitVec.ofNat 64 0))))
        [("v", .stdVecVal l)] = .ok (.i32 x) :=
      evalExpr_stdVecAt_some "v" _ _ _ _ _ hv hlit hget0
    have hret := memEvalStmtFuel_return F
      (.stdVecAt "v" (.lit (.u64 (BitVec.ofNat 64 0)))) _ _ _ _
      hagree heval
    have hstmt : memEvalStmtFuel F vecAtOneFunc.body
        [("v", .stdVecVal l)]
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
        [("v", 0, 0)] =
        .ok ((([("v", .stdVecVal l)],
          ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
          [("v", 0, 0)])),
          .returned (.i32 x)) := by
      rw [hbody]
      exact (memEvalStmtFuel_if_true F _ _ _ _ _ _ hc).trans hret
    simp only [memEvalFuncFuel, hb, hstmt, hfwd]
  · have hc : memEvalExpr
        (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "v"))
        [("v", .stdVecVal l)]
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
        [("v", 0, 0)] = .ok (.b false) := by
      rw [hmc]
      simpa [h] using vecAtOneCond_eval l hlen64
    have hempty : l[0]? = none := by
      rw [List.getElem?_eq_none]
      simpa using h
    have hfwd : vecAtOneFwd l = .error .AssertFail := by
      simp [vecAtOneFwd, hempty]
    have hmfail : memEvalStmtFuel F .fail
        [("v", .stdVecVal l)]
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
        [("v", 0, 0)] = .error .AssertFail :=
      memEvalStmtFuel_fail F _ _ _
    have hstmt : memEvalStmtFuel F vecAtOneFunc.body
        [("v", .stdVecVal l)]
        ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
        [("v", 0, 0)] = .error .AssertFail := by
      rw [hbody]
      exact (memEvalStmtFuel_if_false F _ _ _ _ _ _ hc).trans hmfail
    simp only [memEvalFuncFuel, hb, hstmt, hfwd]

/-- Transfer for the entry (both paths). -/
theorem memTransfer_vecAtOne (F : Nat) (l : List (BitVec 32))
    (hlen64 : l.length < 2 ^ 64)
    (_h : oracleNoalias vecAtOneFunc [.stdVecVal l]) :
    memEvalFuncFuel F vecAtOneFunc [.stdVecVal l] =
      evalFuncFuel F vecAtOneFunc [.stdVecVal l] := by
  rw [memEvalFuncFuel_vecAtOne F l hlen64, evalFuncFuel_vecAtOne F l hlen64]

/-- Guard evaluation on memory (mirrors `vecAtSumGuard_eval`). -/
theorem memVecAtSumGuard_eval (l : List (BitVec 32)) (k : Nat)
    (acc : BitVec 32) (m : Mem) (π : Layout) (ad : Addr) (t : Nat)
    (hk64 : k < 2 ^ 64) (hl64 : l.length < 2 ^ 64)
    (hlay : layoutLookup π "s" = some (ad, t))
    (hmemlen : memLoad m ad t 0 = .ok (BitVec.ofNat 32 l.length)) :
    memEvalExpr vecAtSumGuard (mkStdVecEnv l k acc) m π =
      .ok (.b (decide (k < l.length))) := by
  have h := memStdVecCond_eval l k acc m π ad t hk64 hl64 hlay hmemlen
  simpa [vecAtSumGuard] using h

/-- Body with a successful add on memory: guard holds in-loop, so
    the step is the inherited body step (any fuel). -/
theorem memVecAtSumBody_step_ok (F : Nat) (l : List (BitVec 32)) (k : Nat)
    (acc x a : BitVec 32) (m : Mem) (π : Layout) (ad : Addr) (t : Nat)
    (hlt : k < l.length) (hk64 : k < 2 ^ 64) (hl64 : l.length < 2 ^ 64)
    (hget : l[k]? = some x)
    (hc : checkedAddI32 acc x = .ok a)
    (hlay : layoutLookup π "s" = some (ad, t))
    (hmemlen : memLoad m ad t 0 = .ok (BitVec.ofNat 32 l.length))
    (hmemall : ∀ (j : Nat) (y : BitVec 32),
      l[j]? = some y → memLoad m ad t (j + 1) = .ok y) :
    memEvalStmtFuel F vecAtSumBody (mkStdVecEnv l k acc) m π =
      .ok (((mkStdVecEnv l (k + 1) a, m, π)), .fellThrough) := by
  have hg : memEvalExpr vecAtSumGuard (mkStdVecEnv l k acc) m π =
      .ok (.b true) := by
    have h := memVecAtSumGuard_eval l k acc m π ad t hk64 hl64 hlay hmemlen
    simpa [hlt] using h
  have hbody := memStdVecBody_step_ok F l k acc x a m π ad t hlt hk64 hl64
    hget hc hlay hmemlen hmemall
  simp only [vecAtSumBody]
  rw [memEvalStmtFuel_if_true _ _ _ _ _ _ _ hg]
  exact hbody

/-- Body with an overflowing add on memory: the `nsw` error is loud,
    the index never advances (any fuel). -/
theorem memVecAtSumBody_step_err (F : Nat) (l : List (BitVec 32)) (k : Nat)
    (acc x : BitVec 32) (e : Panic) (m : Mem) (π : Layout)
    (ad : Addr) (t : Nat)
    (hlt : k < l.length) (hk64 : k < 2 ^ 64) (hl64 : l.length < 2 ^ 64)
    (hget : l[k]? = some x)
    (hc : checkedAddI32 acc x = .error e)
    (hlay : layoutLookup π "s" = some (ad, t))
    (hmemlen : memLoad m ad t 0 = .ok (BitVec.ofNat 32 l.length))
    (hmemall : ∀ (j : Nat) (y : BitVec 32),
      l[j]? = some y → memLoad m ad t (j + 1) = .ok y) :
    memEvalStmtFuel F vecAtSumBody (mkStdVecEnv l k acc) m π = .error e := by
  have hg : memEvalExpr vecAtSumGuard (mkStdVecEnv l k acc) m π =
      .ok (.b true) := by
    have h := memVecAtSumGuard_eval l k acc m π ad t hk64 hl64 hlay hmemlen
    simpa [hlt] using h
  have hbody := memStdVecBody_step_err F l k acc x e m π ad t hlt hk64 hl64
    hget hc hlay hmemlen hmemall
  simp only [vecAtSumBody]
  rw [memEvalStmtFuel_if_true _ _ _ _ _ _ _ hg]
  exact hbody

/-- Loop correctness on memory: folds the checked-add suffix
    (mirrors `memStdVecWhile_correct` — the guard is subsumed, so
    the fold is the inherited one). -/
theorem memVecAtSumWhile_correct (l : List (BitVec 32))
    (F k : Nat) (acc : BitVec 32) (m : Mem) (π : Layout)
    (ad : Addr) (t : Nat)
    (hk : k ≤ l.length) (hl64 : l.length < 2 ^ 64)
    (hlay : layoutLookup π "s" = some (ad, t))
    (hmemlen : memLoad m ad t 0 = .ok (BitVec.ofNat 32 l.length))
    (hmemall : ∀ (j : Nat) (x : BitVec 32),
      l[j]? = some x → memLoad m ad t (j + 1) = .ok x)
    (hF : l.length - k + 1 ≤ F) :
    memEvalStmtFuel F vecAtSumWhile (mkStdVecEnv l k acc) m π =
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
        have hbody := memVecAtSumBody_step_err F l k acc l[k] e m π ad t
          hlt hk64 hl64 hget hc hlay hmemlen hmemall
        have hstep :
            memEvalStmtFuel (F + 1) vecAtSumWhile (mkStdVecEnv l k acc) m π
            = .error e := by
          simp [vecAtSumWhile, memEvalStmtFuel, memEvalSuccHandler,
            memEvalStmtWith, hcond, hbody]
        rw [hstep, hunfold, hc]
      | ok a =>
        have hbody := memVecAtSumBody_step_ok F l k acc l[k] a m π ad t
          hlt hk64 hl64 hget hc hlay hmemlen hmemall
        have hstep :
            memEvalStmtFuel (F + 1) vecAtSumWhile (mkStdVecEnv l k acc) m π
            = memEvalStmtFuel F vecAtSumWhile (mkStdVecEnv l (k + 1) a) m π := by
          simp [vecAtSumWhile, memEvalStmtFuel, memEvalSuccHandler,
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
      simp [vecAtSumWhile, memEvalStmtFuel, memEvalSuccHandler,
        memEvalStmtWith, hcond, hnil]

/-- `memEval` for `vec_at_sum`, fuel-generalized — mirrors
    `evalFuncFuel_vecAtSum`. -/
theorem memEvalFuncFuel_vecAtSum (F : Nat) (l : List (BitVec 32))
    (hl64 : l.length < 2 ^ 64) (hF : l.length + 1 ≤ F) :
    memEvalFuncFuel F vecAtSumFunc [.stdVecVal l] = vecAtSumFwd l := by
  have hbf : vecAtSumFunc.args =
      [{ name := "s", ty := stdVecObjTy, role := .sharedBorrow }] := rfl
  have hbody : vecAtSumFunc.body =
      .seq (.let_ "t" (.i 32) (.lit (.i32 (BitVec.ofNat 32 0))))
      (.seq (.let_ "i" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.seq vecAtSumWhile
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
    have hsum0 : vecAtSumFwd l = .error e := stdVecReadSumFwd_err l e hfold
    cases F with
    | zero =>
      have hloopH0 : memEvalStmtWith memEvalStmtZeroHandler
            vecAtSumWhile (mkStdVecEnv l 0 (BitVec.ofNat 32 0))
            ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
            [("s", 0, 0)] = .error e := by
        have h := memVecAtSumWhile_correct l 0 0 (BitVec.ofNat 32 0)
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
            vecAtSumWhile (mkStdVecEnv l 0 (BitVec.ofNat 32 0))
            ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
            [("s", 0, 0)] = .error e := by
        have h := memVecAtSumWhile_correct l (F + 1) 0 (BitVec.ofNat 32 0)
          ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
          [("s", 0, 0)] 0 0 (Nat.zero_le _) hl64 hlay hmemlen hmemall
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      simp only [memEvalFuncFuel, hbf, hbody, hb]
      simp [memEvalStmtFuel, memEvalStmtWith,
        memEvalExpr, litVal, henv, hloopS, hsum0]
  | ok acc' =>
    have hsum' : vecAtSumFwd l = .ok (.i32 acc') :=
      stdVecReadSumFwd_ok l acc' hfold
    cases F with
    | zero =>
      have hloopH0 : memEvalStmtWith memEvalStmtZeroHandler
            vecAtSumWhile (mkStdVecEnv l 0 (BitVec.ofNat 32 0))
            ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
            [("s", 0, 0)] =
            .ok ((((mkStdVecEnv l l.length acc',
              ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
              [("s", 0, 0)]))), .fellThrough) := by
        have h := memVecAtSumWhile_correct l 0 0 (BitVec.ofNat 32 0)
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
            vecAtSumWhile (mkStdVecEnv l 0 (BitVec.ofNat 32 0))
            ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
            [("s", 0, 0)] =
            .ok ((((mkStdVecEnv l l.length acc',
              ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩,
              [("s", 0, 0)]))), .fellThrough) := by
        have h := memVecAtSumWhile_correct l (F + 1) 0 (BitVec.ofNat 32 0)
          ⟨1, [(0, ⟨0, true, (BitVec.ofNat 32 l.length) :: l⟩)], []⟩
          [("s", 0, 0)] 0 0 (Nat.zero_le _) hl64 hlay hmemlen hmemall
          (by omega)
        rw [List.drop_zero] at h
        rwa [hfold] at h
      have hsret' := hsret acc'
      simp only [memEvalFuncFuel, hbf, hbody, hb]
      simp [memEvalStmtFuel, memEvalStmtWith,
        memEvalExpr, litVal, henv, hloopS, hsret', hsum']

/-- Transfer for `vec_at_sum`: both sides equal the inherited fold. -/
theorem memTransfer_vecAtSum (F : Nat) (l : List (BitVec 32))
    (hl64 : l.length < 2 ^ 64) (hF : l.length + 1 ≤ F)
    (_h : oracleNoalias vecAtSumFunc [.stdVecVal l]) :
    memEvalFuncFuel F vecAtSumFunc [.stdVecVal l] =
      evalFuncFuel F vecAtSumFunc [.stdVecVal l] := by
  rw [memEvalFuncFuel_vecAtSum F l hl64 hF, evalFuncFuel_vecAtSum F l hl64 hF]

/-! ## F1: sequential-writer transfer (memory threaded untouched) -/

/-- Memory evaluation of `reborrow`: the fused body has no `Mem` ops
    (the two writes are value-level; the single cell is addressed
    gate-side via L2 + F0), so `Mem` threads through both adds
    untouched and the result is the forward function. -/
theorem memEvalFuncFuel_reborrow (F : Nat) (x : BitVec 32) :
    memEvalFuncFuel F reborrowFunc [.i32 x] = reborrowFwd x := by
  have hbf : reborrowFunc.args =
      [{ name := "x", ty := .i 32, role := .mutBorrow 0 }] := rfl
  have hbody : reborrowFunc.body =
      .seq (.let_ "t" (.i 32) (.add (.var "x") (.lit (.i32 1))))
           (.return_ (.add (.var "t") (.lit (.i32 2)))) := rfl
  have hb := bindMemArgs_reborrow x
  have hx : envLookup [("x", .i32 x)] "x" = some (.i32 x) := by
    simp [envLookup]
  simp only [memEvalFuncFuel, bindArgs, hbf, hbody, hb]
  cases h1 : checkedAddI32 x 1 with
  | error e =>
    have hme : memEvalExpr (.add (.var "x") (.lit (.i32 1)))
        [("x", .i32 x)] emptyMem [] = .error e := by
      rw [memEvalExpr_add_var_lit _ _ _ _ _ _ hx, h1]
      exact i32_map_error e
    have hlet := memEvalStmtFuel_let_err F "t" (.i 32) _ _ _ _ e
      (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h) hme
    rw [memEvalStmtFuel_seq_err _ _ _ _ _ _ _ hlet]
    exact (reborrowFwd_err1 x e h1).symm
  | ok t =>
    have hagree : memEvalExpr (.add (.var "x") (.lit (.i32 1)))
        [("x", .i32 x)] emptyMem [] =
        evalExpr (.add (.var "x") (.lit (.i32 1))) [("x", .i32 x)] := by
      rw [memEvalExpr_add_var_lit _ _ _ _ _ _ hx,
        evalExpr_add_var_lit _ _ _ _ hx]
    have hv : evalExpr (.add (.var "x") (.lit (.i32 1)))
        [("x", .i32 x)] = .ok (.i32 t) := by
      rw [evalExpr_add_var_lit _ _ _ _ hx, h1]
      exact i32_map_ok t
    have hlet := memEvalStmtFuel_let_pure F "t" (.i 32) _ _ _ _
      (.i32 t) (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
      hagree hv
    have ht : envLookup [("t", .i32 t), ("x", .i32 x)] "t" =
        some (.i32 t) :=
      envExtend_hit _ _ _
    cases h2 : checkedAddI32 t 2#32 with
    | error e =>
      have hme2 : memEvalExpr (.add (.var "t") (.lit (.i32 2#32)))
          [("t", .i32 t), ("x", .i32 x)] emptyMem [] =
          .error e := by
        rw [memEvalExpr_add_var_lit _ _ _ _ _ _ ht, h2]
        exact i32_map_error e
      -- The `return_` evaluates the second add, which errors.
      have hret : memEvalStmtFuel F
          (.return_ (.add (.var "t") (.lit (.i32 2))))
          [("t", .i32 t), ("x", .i32 x)] emptyMem [] =
          .error e := by
        cases F with
        | zero =>
          simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, hme2]
        | succ n =>
          simp [memEvalStmtFuel, memEvalStmtWith, hme2]
      rw [memEvalStmtFuel_seq_fallthrough _ _ _ _ _ _ _ _ _ hlet, hret]
      exact (reborrowFwd_err2 x t e h1 h2).symm
    | ok r =>
      have hme2 : memEvalExpr (.add (.var "t") (.lit (.i32 2#32)))
          [("t", .i32 t), ("x", .i32 x)] emptyMem [] =
          .ok (.i32 r) := by
        rw [memEvalExpr_add_var_lit _ _ _ _ _ _ ht, h2]
        exact i32_map_ok r
      have hret : memEvalStmtFuel F
          (.return_ (.add (.var "t") (.lit (.i32 2))))
          [("t", .i32 t), ("x", .i32 x)] emptyMem [] =
          .ok (([("t", .i32 t), ("x", .i32 x)], emptyMem, []),
            .returned (.i32 r)) := by
        cases F with
        | zero =>
          simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, hme2]
        | succ n =>
          simp [memEvalStmtFuel, memEvalStmtWith, hme2]
      rw [memEvalStmtFuel_seq_fallthrough _ _ _ _ _ _ _ _ _ hlet, hret]
      exact (reborrowFwd_ok x t r h1 h2).symm

/-- Transfer for `reborrow`: both sides equal the forward function. -/
theorem memTransfer_reborrow (F : Nat) (x : BitVec 32)
    (_h : oracleNoalias reborrowFunc [.i32 x]) :
    memEvalFuncFuel F reborrowFunc [.i32 x] =
      evalFuncFuel F reborrowFunc [.i32 x] := by
  rw [memEvalFuncFuel_reborrow F x, evalFuncFuel_reborrow F x]

/-! ## L1b: second-writer transfer (memory threaded untouched) -/

/-- Memory evaluation of `reborrow34`: the fused body has no `Mem` ops
    (the two writes are value-level; the single cell is addressed
    gate-side via L2 + F0), so `Mem` threads through both adds
    untouched and the result is the forward function. -/
theorem memEvalFuncFuel_reborrow34 (F : Nat) (x : BitVec 32) :
    memEvalFuncFuel F reborrow34Func [.i32 x] = reborrow34Fwd x := by
  have hbf : reborrow34Func.args =
      [{ name := "x", ty := .i 32, role := .mutBorrow 0 }] := rfl
  have hbody : reborrow34Func.body =
      .seq (.let_ "t" (.i 32) (.add (.var "x") (.lit (.i32 3))))
           (.return_ (.add (.var "t") (.lit (.i32 4)))) := rfl
  have hb := bindMemArgs_reborrow34 x
  have hx : envLookup [("x", .i32 x)] "x" = some (.i32 x) := by
    simp [envLookup]
  simp only [memEvalFuncFuel, bindArgs, hbf, hbody, hb]
  cases h1 : checkedAddI32 x 3 with
  | error e =>
    have hme : memEvalExpr (.add (.var "x") (.lit (.i32 3)))
        [("x", .i32 x)] emptyMem [] = .error e := by
      rw [memEvalExpr_add_var_lit _ _ _ _ _ _ hx, h1]
      exact i32_map_error e
    have hlet := memEvalStmtFuel_let_err F "t" (.i 32) _ _ _ _ e
      (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h) hme
    rw [memEvalStmtFuel_seq_err _ _ _ _ _ _ _ hlet]
    exact (reborrow34Fwd_err1 x e h1).symm
  | ok t =>
    have hagree : memEvalExpr (.add (.var "x") (.lit (.i32 3)))
        [("x", .i32 x)] emptyMem [] =
        evalExpr (.add (.var "x") (.lit (.i32 3))) [("x", .i32 x)] := by
      rw [memEvalExpr_add_var_lit _ _ _ _ _ _ hx,
        evalExpr_add_var_lit _ _ _ _ hx]
    have hv : evalExpr (.add (.var "x") (.lit (.i32 3)))
        [("x", .i32 x)] = .ok (.i32 t) := by
      rw [evalExpr_add_var_lit _ _ _ _ hx, h1]
      exact i32_map_ok t
    have hlet := memEvalStmtFuel_let_pure F "t" (.i 32) _ _ _ _
      (.i32 t) (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h)
      hagree hv
    have ht : envLookup [("t", .i32 t), ("x", .i32 x)] "t" =
        some (.i32 t) :=
      envExtend_hit _ _ _
    cases h2 : checkedAddI32 t 4#32 with
    | error e =>
      have hme2 : memEvalExpr (.add (.var "t") (.lit (.i32 4#32)))
          [("t", .i32 t), ("x", .i32 x)] emptyMem [] =
          .error e := by
        rw [memEvalExpr_add_var_lit _ _ _ _ _ _ ht, h2]
        exact i32_map_error e
      -- The `return_` evaluates the second add, which errors.
      have hret : memEvalStmtFuel F
          (.return_ (.add (.var "t") (.lit (.i32 4))))
          [("t", .i32 t), ("x", .i32 x)] emptyMem [] =
          .error e := by
        cases F with
        | zero =>
          simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, hme2]
        | succ n =>
          simp [memEvalStmtFuel, memEvalStmtWith, hme2]
      rw [memEvalStmtFuel_seq_fallthrough _ _ _ _ _ _ _ _ _ hlet, hret]
      exact (reborrow34Fwd_err2 x t e h1 h2).symm
    | ok r =>
      have hme2 : memEvalExpr (.add (.var "t") (.lit (.i32 4#32)))
          [("t", .i32 t), ("x", .i32 x)] emptyMem [] =
          .ok (.i32 r) := by
        rw [memEvalExpr_add_var_lit _ _ _ _ _ _ ht, h2]
        exact i32_map_ok r
      have hret : memEvalStmtFuel F
          (.return_ (.add (.var "t") (.lit (.i32 4))))
          [("t", .i32 t), ("x", .i32 x)] emptyMem [] =
          .ok (([("t", .i32 t), ("x", .i32 x)], emptyMem, []),
            .returned (.i32 r)) := by
        cases F with
        | zero =>
          simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, hme2]
        | succ n =>
          simp [memEvalStmtFuel, memEvalStmtWith, hme2]
      rw [memEvalStmtFuel_seq_fallthrough _ _ _ _ _ _ _ _ _ hlet, hret]
      exact (reborrow34Fwd_ok x t r h1 h2).symm

/-- Transfer for `reborrow34`: both sides equal the forward function. -/
theorem memTransfer_reborrow34 (F : Nat) (x : BitVec 32)
    (_h : oracleNoalias reborrow34Func [.i32 x]) :
    memEvalFuncFuel F reborrow34Func [.i32 x] =
      evalFuncFuel F reborrow34Func [.i32 x] := by
  rw [memEvalFuncFuel_reborrow34 F x, evalFuncFuel_reborrow34 F x]

/-! ## G2: writer-pair transfer (memory threaded untouched) -/

/-- Memory evaluation of `wr_pair`: the body has no `Mem` ops (both
    writes are value-level; the cells are addressed gate-side via the
    dataflow pin plus the `noalias` verdict), so `Mem` threads
    through both adds untouched and the result is the forward
    function. Per-side lemmas plus `rw` (F1 transfer lesson:
    monolithic `simp` misaligns the sides). -/
theorem memEvalFuncFuel_wrPair (F : Nat) (p q : BitVec 32) :
    memEvalFuncFuel F wrPairFunc [.i32 p, .i32 q] = wrPairFwd p q := by
  have hbf : wrPairFunc.args =
      [{ name := "p", ty := .i 32, role := .mutBorrow 0 },
       { name := "q", ty := .i 32, role := .mutBorrow 0 }] := rfl
  have hbody : wrPairFunc.body =
      .seq (.let_ "a" (.i 32) (.add (.var "p") (.lit (.i32 1))))
      (.seq (.let_ "b" (.i 32) (.add (.var "q") (.lit (.i32 2))))
            (.return_ (.pair (.var "a") (.var "b")))) := rfl
  have hb := bindMemArgs_wrPair p q
  have hx : envLookup [("p", .i32 p), ("q", .i32 q)] "p" =
      some (.i32 p) := by
    simp [envLookup]
  simp only [memEvalFuncFuel, bindArgs, hbf, hbody, hb]
  cases h1 : checkedAddI32 p 1 with
  | error e =>
    have hme : memEvalExpr (.add (.var "p") (.lit (.i32 1)))
        [("p", .i32 p), ("q", .i32 q)] emptyMem [] = .error e := by
      rw [memEvalExpr_add_var_lit _ _ _ _ _ _ hx, h1]
      exact i32_map_error e
    have hlet := memEvalStmtFuel_let_err F "a" (.i 32) _ _ _ _ e
      (fun _ h => by cases h) (fun _ h => by cases h)
      (fun _ h => by cases h) hme
    rw [memEvalStmtFuel_seq_err _ _ _ _ _ _ _ hlet]
    exact (wrPairFwd_err1 p q e h1).symm
  | ok a =>
    have hagree : memEvalExpr (.add (.var "p") (.lit (.i32 1)))
        [("p", .i32 p), ("q", .i32 q)] emptyMem [] =
        evalExpr (.add (.var "p") (.lit (.i32 1)))
          [("p", .i32 p), ("q", .i32 q)] := by
      rw [memEvalExpr_add_var_lit _ _ _ _ _ _ hx,
        evalExpr_add_var_lit _ _ _ _ hx]
    have hv : evalExpr (.add (.var "p") (.lit (.i32 1)))
        [("p", .i32 p), ("q", .i32 q)] = .ok (.i32 a) := by
      rw [evalExpr_add_var_lit _ _ _ _ hx, h1]
      exact i32_map_ok a
    have hlet := memEvalStmtFuel_let_pure F "a" (.i 32) _ _ _ _
      (.i32 a) (fun _ h => by cases h) (fun _ h => by cases h)
      (fun _ h => by cases h) hagree hv
    -- NOTE: `memEvalStmtFuel_let_pure` concludes with `::`-cons
    -- envs (not `envExtend`), so every fact below the first `let`
    -- uses the literal cons form (F1 precedent).
    have hq : envLookup [("a", .i32 a), ("p", .i32 p), ("q", .i32 q)]
        "q" = some (.i32 q) := by
      simp [envLookup, show ("q" : String) ≠ "a" by decide]
    cases h2 : checkedAddI32 q 2 with
    | error e =>
      have hme2 : memEvalExpr (.add (.var "q") (.lit (.i32 2)))
          [("a", .i32 a), ("p", .i32 p), ("q", .i32 q)]
          emptyMem [] = .error e := by
        rw [memEvalExpr_add_var_lit _ _ _ _ _ _ hq, h2]
        exact i32_map_error e
      have hlet2 := memEvalStmtFuel_let_err F "b" (.i 32) _ _ _ _ e
        (fun _ h => by cases h) (fun _ h => by cases h)
        (fun _ h => by cases h) hme2
      rw [memEvalStmtFuel_seq_fallthrough _ _ _ _ _ _ _ _ _ hlet,
        memEvalStmtFuel_seq_err _ _ _ _ _ _ _ hlet2]
      exact (wrPairFwd_err2 p q a e h1 h2).symm
    | ok b =>
      have hagree2 : memEvalExpr (.add (.var "q") (.lit (.i32 2)))
          [("a", .i32 a), ("p", .i32 p), ("q", .i32 q)]
          emptyMem [] =
          evalExpr (.add (.var "q") (.lit (.i32 2)))
            [("a", .i32 a), ("p", .i32 p), ("q", .i32 q)] := by
        rw [memEvalExpr_add_var_lit _ _ _ _ _ _ hq,
          evalExpr_add_var_lit _ _ _ _ hq]
      have hv2 : evalExpr (.add (.var "q") (.lit (.i32 2)))
          [("a", .i32 a), ("p", .i32 p), ("q", .i32 q)] =
          .ok (.i32 b) := by
        rw [evalExpr_add_var_lit _ _ _ _ hq, h2]
        exact i32_map_ok b
      have hlet2 := memEvalStmtFuel_let_pure F "b" (.i 32) _ _ _ _
        (.i32 b) (fun _ h => by cases h) (fun _ h => by cases h)
        (fun _ h => by cases h) hagree2 hv2
      have ha2 : envLookup [("b", .i32 b), ("a", .i32 a),
          ("p", .i32 p), ("q", .i32 q)] "a" = some (.i32 a) := by
        simp [envLookup, show ("a" : String) ≠ "b" by decide]
      have hb2 : envLookup [("b", .i32 b), ("a", .i32 a),
          ("p", .i32 p), ("q", .i32 q)] "b" = some (.i32 b) :=
        envExtend_hit _ _ _
      have hva : memEvalExpr (.var "a")
          [("b", .i32 b), ("a", .i32 a), ("p", .i32 p), ("q", .i32 q)]
          emptyMem [] = .ok (.i32 a) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ ha2
      have hvb : memEvalExpr (.var "b")
          [("b", .i32 b), ("a", .i32 a), ("p", .i32 p), ("q", .i32 q)]
          emptyMem [] = .ok (.i32 b) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ hb2
      have hmeP : memEvalExpr (.pair (.var "a") (.var "b"))
          [("b", .i32 b), ("a", .i32 a), ("p", .i32 p), ("q", .i32 q)]
          emptyMem [] =
          .ok (.structVal "IPair" [("a", a), ("b", b)]) :=
        memEvalExpr_pair_ok _ _ _ _ _ _ _ hva hvb
      have hret : memEvalStmtFuel F
          (.return_ (.pair (.var "a") (.var "b")))
          [("b", .i32 b), ("a", .i32 a), ("p", .i32 p), ("q", .i32 q)]
          emptyMem [] =
          .ok ((([("b", .i32 b), ("a", .i32 a), ("p", .i32 p),
            ("q", .i32 q)], emptyMem, [])),
            .returned (.structVal "IPair" [("a", a), ("b", b)])) := by
        cases F with
        | zero =>
          simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, hmeP]
        | succ n =>
          simp [memEvalStmtFuel, memEvalStmtWith, hmeP]
      rw [memEvalStmtFuel_seq_fallthrough _ _ _ _ _ _ _ _ _ hlet,
        memEvalStmtFuel_seq_fallthrough _ _ _ _ _ _ _ _ _ hlet2, hret]
      exact (wrPairFwd_ok p q a b h1 h2).symm

/-- Transfer for `wr_pair`: both sides equal the forward function. -/
theorem memTransfer_wrPair (F : Nat) (p q : BitVec 32)
    (_h : oracleNoalias wrPairFunc [.i32 p, .i32 q]) :
    memEvalFuncFuel F wrPairFunc [.i32 p, .i32 q] =
      evalFuncFuel F wrPairFunc [.i32 p, .i32 q] := by
  rw [memEvalFuncFuel_wrPair F p q, evalFuncFuel_wrPair F p q]

/-! ## G2b: branch-writer transfer (memory threaded untouched) -/

/-- Memory evaluation of `cond_pair`: the `tif` is branch-lazy on
    both sides (the existing `memEvalExpr_tif_*` agreement), then
    the second let and the `pair` return run as in G2. Post-let
    facts use the literal `::`-cons env form (G2 transfer lesson). -/
theorem memEvalFuncFuel_condPair (F : Nat) (p q : BitVec 32)
    (c : Bool) :
    memEvalFuncFuel F condPairFunc [.i32 p, .i32 q, .b c] =
      condPairFwd p q c := by
  have hbf : condPairFunc.args =
      [{ name := "p", ty := .i 32, role := .mutBorrow 0 },
       { name := "q", ty := .i 32, role := .mutBorrow 0 },
       { name := "c", ty := .bool, role := .owned }] := rfl
  have hbody : condPairFunc.body =
      .seq (.let_ "a" (.i 32)
        (.tif (.var "c") (.add (.var "p") (.lit (.i32 1))) (.var "p")))
      (.seq (.let_ "b" (.i 32) (.add (.var "q") (.lit (.i32 2))))
            (.return_ (.pair (.var "a") (.var "b")))) := rfl
  have hb := bindMemArgs_condPair p q c
  have hx : envLookup [("p", .i32 p), ("q", .i32 q), ("c", .b c)]
      "p" = some (.i32 p) := by
    simp [envLookup]
  have hc0 : envLookup [("p", .i32 p), ("q", .i32 q), ("c", .b c)]
      "c" = some (.b c) := by
    simp [envLookup]
  simp only [memEvalFuncFuel, bindArgs, hbf, hbody, hb]
  have hcm : memEvalExpr (.var "c")
      [("p", .i32 p), ("q", .i32 q), ("c", .b c)] emptyMem [] =
      evalExpr (.var "c")
        [("p", .i32 p), ("q", .i32 q), ("c", .b c)] :=
    memEvalExpr_var _ _ _ _
  cases c with
  | true =>
    have hvc : evalExpr (.var "c")
        [("p", .i32 p), ("q", .i32 q), ("c", .b true)] =
        .ok (.b true) :=
      evalExpr_var_hit _ _ _ hc0
    have htAgree : memEvalExpr (.add (.var "p") (.lit (.i32 1)))
        [("p", .i32 p), ("q", .i32 q), ("c", .b true)] emptyMem [] =
        evalExpr (.add (.var "p") (.lit (.i32 1)))
          [("p", .i32 p), ("q", .i32 q), ("c", .b true)] := by
      rw [memEvalExpr_add_var_lit _ _ _ _ _ _ hx,
        evalExpr_add_var_lit _ _ _ _ hx]
    have hagree : memEvalExpr
        (.tif (.var "c") (.add (.var "p") (.lit (.i32 1))) (.var "p"))
        [("p", .i32 p), ("q", .i32 q), ("c", .b true)] emptyMem [] =
        evalExpr
          (.tif (.var "c") (.add (.var "p") (.lit (.i32 1)))
            (.var "p"))
          [("p", .i32 p), ("q", .i32 q), ("c", .b true)] :=
      memEvalExpr_tif_true _ _ _ _ _ _ hcm hvc htAgree
    cases h1 : checkedAddI32 p 1 with
    | error e =>
      have hme : memEvalExpr
          (.tif (.var "c") (.add (.var "p") (.lit (.i32 1)))
            (.var "p"))
          [("p", .i32 p), ("q", .i32 q), ("c", .b true)] emptyMem [] =
          .error e := by
        rw [hagree, evalExpr_tif_true _ _ _ _
          (evalExpr_var_hit _ _ _ hc0)]
        rw [evalExpr_add_var_lit _ _ _ _ hx, h1]
        exact i32_map_error e
      have hlet := memEvalStmtFuel_let_err F "a" (.i 32) _ _ _ _ e
        (fun _ h => by cases h) (fun _ h => by cases h)
        (fun _ h => by cases h) hme
      rw [memEvalStmtFuel_seq_err _ _ _ _ _ _ _ hlet]
      exact (condPairFwd_err_p p q e h1).symm
    | ok a =>
      have hvT : evalExpr (.add (.var "p") (.lit (.i32 1)))
          [("p", .i32 p), ("q", .i32 q), ("c", .b true)] =
          .ok (.i32 a) := by
        rw [evalExpr_add_var_lit _ _ _ _ hx, h1]
        exact i32_map_ok a
      have hv : evalExpr
          (.tif (.var "c") (.add (.var "p") (.lit (.i32 1)))
            (.var "p"))
          [("p", .i32 p), ("q", .i32 q), ("c", .b true)] =
          .ok (.i32 a) := by
        rw [evalExpr_tif_true _ _ _ _
          (evalExpr_var_hit _ _ _ hc0), hvT]
      have hlet := memEvalStmtFuel_let_pure F "a" (.i 32) _ _ _ _
        (.i32 a) (fun _ h => by cases h) (fun _ h => by cases h)
        (fun _ h => by cases h) hagree hv
      have hq : envLookup [("a", .i32 a), ("p", .i32 p),
          ("q", .i32 q), ("c", .b true)] "q" = some (.i32 q) := by
        simp [envLookup, show ("q" : String) ≠ "a" by decide]
      cases h2 : checkedAddI32 q 2 with
      | error e =>
        have hme2 : memEvalExpr (.add (.var "q") (.lit (.i32 2)))
            [("a", .i32 a), ("p", .i32 p), ("q", .i32 q),
              ("c", .b true)] emptyMem [] = .error e := by
          rw [memEvalExpr_add_var_lit _ _ _ _ _ _ hq, h2]
          exact i32_map_error e
        have hlet2 := memEvalStmtFuel_let_err F "b" (.i 32) _ _ _ _ e
          (fun _ h => by cases h) (fun _ h => by cases h)
          (fun _ h => by cases h) hme2
        rw [memEvalStmtFuel_seq_fallthrough _ _ _ _ _ _ _ _ _ hlet,
          memEvalStmtFuel_seq_err _ _ _ _ _ _ _ hlet2]
        exact (condPairFwd_err_q_true p q a e h1 h2).symm
      | ok b =>
        have hagree2 : memEvalExpr (.add (.var "q") (.lit (.i32 2)))
            [("a", .i32 a), ("p", .i32 p), ("q", .i32 q),
              ("c", .b true)] emptyMem [] =
            evalExpr (.add (.var "q") (.lit (.i32 2)))
              [("a", .i32 a), ("p", .i32 p), ("q", .i32 q),
                ("c", .b true)] := by
          rw [memEvalExpr_add_var_lit _ _ _ _ _ _ hq,
            evalExpr_add_var_lit _ _ _ _ hq]
        have hv2 : evalExpr (.add (.var "q") (.lit (.i32 2)))
            [("a", .i32 a), ("p", .i32 p), ("q", .i32 q),
              ("c", .b true)] = .ok (.i32 b) := by
          rw [evalExpr_add_var_lit _ _ _ _ hq, h2]
          exact i32_map_ok b
        have hlet2 := memEvalStmtFuel_let_pure F "b" (.i 32) _ _ _ _
          (.i32 b) (fun _ h => by cases h) (fun _ h => by cases h)
          (fun _ h => by cases h) hagree2 hv2
        have ha2 : envLookup [("b", .i32 b), ("a", .i32 a),
            ("p", .i32 p), ("q", .i32 q), ("c", .b true)] "a" =
            some (.i32 a) := by
          simp [envLookup, show ("a" : String) ≠ "b" by decide]
        have hb2 : envLookup [("b", .i32 b), ("a", .i32 a),
            ("p", .i32 p), ("q", .i32 q), ("c", .b true)] "b" =
            some (.i32 b) :=
          envExtend_hit _ _ _
        have hva : memEvalExpr (.var "a")
            [("b", .i32 b), ("a", .i32 a), ("p", .i32 p),
              ("q", .i32 q), ("c", .b true)] emptyMem [] =
            .ok (.i32 a) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _ ha2
        have hvb : memEvalExpr (.var "b")
            [("b", .i32 b), ("a", .i32 a), ("p", .i32 p),
              ("q", .i32 q), ("c", .b true)] emptyMem [] =
            .ok (.i32 b) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _ hb2
        have hmeP : memEvalExpr (.pair (.var "a") (.var "b"))
            [("b", .i32 b), ("a", .i32 a), ("p", .i32 p),
              ("q", .i32 q), ("c", .b true)] emptyMem [] =
            .ok (.structVal "IPair" [("a", a), ("b", b)]) :=
          memEvalExpr_pair_ok _ _ _ _ _ _ _ hva hvb
        have hret : memEvalStmtFuel F
            (.return_ (.pair (.var "a") (.var "b")))
            [("b", .i32 b), ("a", .i32 a), ("p", .i32 p),
              ("q", .i32 q), ("c", .b true)] emptyMem [] =
            .ok ((([("b", .i32 b), ("a", .i32 a), ("p", .i32 p),
              ("q", .i32 q), ("c", .b true)], emptyMem, [])),
              .returned (.structVal "IPair" [("a", a), ("b", b)])) := by
          cases F with
          | zero =>
            simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, hmeP]
          | succ n =>
            simp [memEvalStmtFuel, memEvalStmtWith, hmeP]
        rw [memEvalStmtFuel_seq_fallthrough _ _ _ _ _ _ _ _ _ hlet,
          memEvalStmtFuel_seq_fallthrough _ _ _ _ _ _ _ _ _ hlet2,
          hret]
        exact (condPairFwd_ok_true p q a b h1 h2).symm
  | false =>
    have hvc : evalExpr (.var "c")
        [("p", .i32 p), ("q", .i32 q), ("c", .b false)] =
        .ok (.b false) :=
      evalExpr_var_hit _ _ _ hc0
    have heAgree : memEvalExpr (.var "p")
        [("p", .i32 p), ("q", .i32 q), ("c", .b false)] emptyMem [] =
        evalExpr (.var "p")
          [("p", .i32 p), ("q", .i32 q), ("c", .b false)] :=
      memEvalExpr_var _ _ _ _
    have hagree : memEvalExpr
        (.tif (.var "c") (.add (.var "p") (.lit (.i32 1))) (.var "p"))
        [("p", .i32 p), ("q", .i32 q), ("c", .b false)] emptyMem [] =
        evalExpr
          (.tif (.var "c") (.add (.var "p") (.lit (.i32 1)))
            (.var "p"))
          [("p", .i32 p), ("q", .i32 q), ("c", .b false)] :=
      memEvalExpr_tif_false _ _ _ _ _ _ hcm hvc heAgree
    have hpE : evalExpr (.var "p")
        [("p", .i32 p), ("q", .i32 q), ("c", .b false)] =
        .ok (.i32 p) :=
      evalExpr_var_hit _ _ _ hx
    have hv : evalExpr
        (.tif (.var "c") (.add (.var "p") (.lit (.i32 1))) (.var "p"))
        [("p", .i32 p), ("q", .i32 q), ("c", .b false)] =
        .ok (.i32 p) := by
      rw [evalExpr_tif_false _ _ _ _
        (evalExpr_var_hit _ _ _ hc0), hpE]
    have hlet := memEvalStmtFuel_let_pure F "a" (.i 32) _ _ _ _
      (.i32 p) (fun _ h => by cases h) (fun _ h => by cases h)
      (fun _ h => by cases h) hagree hv
    have hq : envLookup [("a", .i32 p), ("p", .i32 p),
        ("q", .i32 q), ("c", .b false)] "q" = some (.i32 q) := by
      simp [envLookup, show ("q" : String) ≠ "a" by decide]
    cases h2 : checkedAddI32 q 2 with
    | error e =>
      have hme2 : memEvalExpr (.add (.var "q") (.lit (.i32 2)))
          [("a", .i32 p), ("p", .i32 p), ("q", .i32 q),
            ("c", .b false)] emptyMem [] = .error e := by
        rw [memEvalExpr_add_var_lit _ _ _ _ _ _ hq, h2]
        exact i32_map_error e
      have hlet2 := memEvalStmtFuel_let_err F "b" (.i 32) _ _ _ _ e
        (fun _ h => by cases h) (fun _ h => by cases h)
        (fun _ h => by cases h) hme2
      rw [memEvalStmtFuel_seq_fallthrough _ _ _ _ _ _ _ _ _ hlet,
        memEvalStmtFuel_seq_err _ _ _ _ _ _ _ hlet2]
      exact (condPairFwd_err_q_false p q e h2).symm
    | ok b =>
      have hagree2 : memEvalExpr (.add (.var "q") (.lit (.i32 2)))
          [("a", .i32 p), ("p", .i32 p), ("q", .i32 q),
            ("c", .b false)] emptyMem [] =
          evalExpr (.add (.var "q") (.lit (.i32 2)))
            [("a", .i32 p), ("p", .i32 p), ("q", .i32 q),
              ("c", .b false)] := by
        rw [memEvalExpr_add_var_lit _ _ _ _ _ _ hq,
          evalExpr_add_var_lit _ _ _ _ hq]
      have hv2 : evalExpr (.add (.var "q") (.lit (.i32 2)))
          [("a", .i32 p), ("p", .i32 p), ("q", .i32 q),
            ("c", .b false)] = .ok (.i32 b) := by
        rw [evalExpr_add_var_lit _ _ _ _ hq, h2]
        exact i32_map_ok b
      have hlet2 := memEvalStmtFuel_let_pure F "b" (.i 32) _ _ _ _
        (.i32 b) (fun _ h => by cases h) (fun _ h => by cases h)
        (fun _ h => by cases h) hagree2 hv2
      have ha2 : envLookup [("b", .i32 b), ("a", .i32 p),
          ("p", .i32 p), ("q", .i32 q), ("c", .b false)] "a" =
          some (.i32 p) := by
        simp [envLookup, show ("a" : String) ≠ "b" by decide]
      have hb2 : envLookup [("b", .i32 b), ("a", .i32 p),
          ("p", .i32 p), ("q", .i32 q), ("c", .b false)] "b" =
          some (.i32 b) :=
        envExtend_hit _ _ _
      have hva : memEvalExpr (.var "a")
          [("b", .i32 b), ("a", .i32 p), ("p", .i32 p),
            ("q", .i32 q), ("c", .b false)] emptyMem [] =
          .ok (.i32 p) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ ha2
      have hvb : memEvalExpr (.var "b")
          [("b", .i32 b), ("a", .i32 p), ("p", .i32 p),
            ("q", .i32 q), ("c", .b false)] emptyMem [] =
          .ok (.i32 b) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ hb2
      have hmeP : memEvalExpr (.pair (.var "a") (.var "b"))
          [("b", .i32 b), ("a", .i32 p), ("p", .i32 p),
            ("q", .i32 q), ("c", .b false)] emptyMem [] =
          .ok (.structVal "IPair" [("a", p), ("b", b)]) :=
        memEvalExpr_pair_ok _ _ _ _ _ _ _ hva hvb
      have hret : memEvalStmtFuel F
          (.return_ (.pair (.var "a") (.var "b")))
          [("b", .i32 b), ("a", .i32 p), ("p", .i32 p),
            ("q", .i32 q), ("c", .b false)] emptyMem [] =
          .ok ((([("b", .i32 b), ("a", .i32 p), ("p", .i32 p),
            ("q", .i32 q), ("c", .b false)], emptyMem, [])),
            .returned (.structVal "IPair" [("a", p), ("b", b)])) := by
        cases F with
        | zero =>
          simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, hmeP]
        | succ n =>
          simp [memEvalStmtFuel, memEvalStmtWith, hmeP]
      rw [memEvalStmtFuel_seq_fallthrough _ _ _ _ _ _ _ _ _ hlet,
        memEvalStmtFuel_seq_fallthrough _ _ _ _ _ _ _ _ _ hlet2,
        hret]
      exact (condPairFwd_ok_false p q b h2).symm

/-- Transfer for `cond_pair`: both sides equal the forward function. -/
theorem memTransfer_condPair (F : Nat) (p q : BitVec 32) (c : Bool)
    (_h : oracleNoalias condPairFunc [.i32 p, .i32 q, .b c]) :
    memEvalFuncFuel F condPairFunc [.i32 p, .i32 q, .b c] =
      evalFuncFuel F condPairFunc [.i32 p, .i32 q, .b c] := by
  rw [memEvalFuncFuel_condPair F p q c, evalFuncFuel_condPair F p q c]

/-! ## G3 open-contract transfer (`alias_cond`, S3).

No pure equality is owed (the S1 `mstore` arm is `AssertFail`
pure-side by design): each leg evaluates the emitted body
symbolically, then closes the cell posts with the S0 arm lemmas in
`Circe.CondFrame`. Store equations stay hypotheses (S0 contract
style); the S4 Diff harness covers success factually. -/

/-- Pinned entry, branch taken: both stores land, the re-read
    frames across the first store (gate-side `hne` is
    `pinnedCell_pair_fresh`). -/
theorem memEvalStmt_aliasCond_true (F : Nat) (p q r₁ r₂ : BitVec 32)
    (hp1 : checkedAddI32 p 1 = .ok r₁)
    (hq2 : checkedAddI32 q 2 = .ok r₂)
    (m₁ m' : Mem)
    (hsto1 : memStore ⟨2, [(1, ⟨1, true, [p]⟩),
      (0, ⟨0, true, [q]⟩)], []⟩ 1 1 0 r₁ = .ok m₁)
    (hsto2 : memStore m₁ 0 0 0 r₂ = .ok m') :
    memEvalStmtFuel F aliasCondFunc.body
      [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
      ⟨2, [(1, ⟨1, true, [p]⟩), (0, ⟨0, true, [q]⟩)], []⟩
      [("p", 1, 1), ("q", 0, 0)] =
      .ok (([("p", .i32 p), ("q", .i32 q), ("c", .b true)], m',
        [("p", 1, 1), ("q", 0, 0)]), .returned (.u32 0)) ∧
    cellAt m' 1 1 r₁ ∧ cellAt m' 0 0 r₂ := by
  have hbody : aliasCondFunc.body =
      .seq (.if_ (.var "c")
        (.mstore "p" (.lit (.u64 0))
          (.add (.mload "p" (.lit (.u64 0))) (.lit (.i32 1))))
        .skip)
      (.seq (.mstore "q" (.lit (.u64 0))
        (.add (.mload "q" (.lit (.u64 0))) (.lit (.i32 2))))
      (.return_ (.lit (.u32 0)))) := rfl
  have hcl : envLookup [("p", .i32 p), ("q", .i32 q),
      ("c", .b true)] "c" = some (.b true) := by
    simp [envLookup]
  have hc : memEvalExpr (.var "c") [("p", .i32 p), ("q", .i32 q),
      ("c", .b true)] ⟨2, [(1, ⟨1, true, [p]⟩),
      (0, ⟨0, true, [q]⟩)], []⟩ [("p", 1, 1), ("q", 0, 0)] =
      .ok (.b true) := by
    rw [memEvalExpr_var, evalExpr_var_hit _ _ _ hcl]
  have hlit0 : memEvalExpr (.lit (.u64 0))
      [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
      ⟨2, [(1, ⟨1, true, [p]⟩), (0, ⟨0, true, [q]⟩)], []⟩
      [("p", 1, 1), ("q", 0, 0)] = .ok (.u64 0) := by
    simp [memEvalExpr, litVal]
  have hfindp : memFind ⟨2, [(1, ⟨1, true, [p]⟩),
      (0, ⟨0, true, [q]⟩)], []⟩ 1 = some ⟨1, true, [p]⟩ :=
    (pinnedCell_pair_find p q _ rfl).1
  have hmemp : memLoad ⟨2, [(1, ⟨1, true, [p]⟩),
      (0, ⟨0, true, [q]⟩)], []⟩ 1 1 0 = .ok p := by
    simp [memLoad, hfindp]
  have hloadp : memEvalExpr
      (.mload "p" (.lit (.u64 0)))
      [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
      ⟨2, [(1, ⟨1, true, [p]⟩), (0, ⟨0, true, [q]⟩)], []⟩
      [("p", 1, 1), ("q", 0, 0)] = .ok (.i32 p) :=
    memEvalExpr_mload_hit "p" (.lit (.u64 0))
      [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
      ⟨2, [(1, ⟨1, true, [p]⟩), (0, ⟨0, true, [q]⟩)], []⟩
      [("p", 1, 1), ("q", 0, 0)] 0 p 1 1
      (pinnedCell_pair_lookup).1 hlit0 hmemp
  have hlitI32_1 : memEvalExpr (.lit (.i32 1))
      [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
      ⟨2, [(1, ⟨1, true, [p]⟩), (0, ⟨0, true, [q]⟩)], []⟩
      [("p", 1, 1), ("q", 0, 0)] = .ok (.i32 1) := by
    simp [memEvalExpr, litVal]
  have haddp : memEvalExpr
      (.add (.mload "p" (.lit (.u64 0)))
        (.lit (.i32 1)))
      [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
      ⟨2, [(1, ⟨1, true, [p]⟩), (0, ⟨0, true, [q]⟩)], []⟩
      [("p", 1, 1), ("q", 0, 0)] = .ok (.i32 r₁) := by
    rw [memEvalExpr_add_ok _ _ _ _ _ p 1 hloadp hlitI32_1, hp1]
    exact i32_map_ok r₁
  have hmp := memEvalStmtFuel_mstore_ok F "p"
    (.lit (.u64 0))
    (.add (.mload "p" (.lit (.u64 0)))
      (.lit (.i32 1)))
    [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
    ⟨2, [(1, ⟨1, true, [p]⟩), (0, ⟨0, true, [q]⟩)], []⟩
    [("p", 1, 1), ("q", 0, 0)] 0 r₁ 1 1 m₁
    hlit0 haddp (pinnedCell_pair_lookup).1 hsto1
  have hfind1 : memFind m₁ 0 = some ⟨0, true, [q]⟩ := by
    rw [memFind_memStore_other _ _ 1 0 1 0 _ hsto1
      pinnedCell_pair_fresh]
    exact (pinnedCell_pair_find p q _ rfl).2
  have hmemq : memLoad m₁ 0 0 0 = .ok q := by
    simp [memLoad, hfind1]
  have hq1 : loadCell m₁ 0 0 = .ok q := by
    simp [loadCell, hfind1]
  have hlit1 : memEvalExpr (.lit (.u64 0))
      [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
      m₁ [("p", 1, 1), ("q", 0, 0)] = .ok (.u64 0) := by
    simp [memEvalExpr, litVal]
  have hloadq : memEvalExpr
      (.mload "q" (.lit (.u64 0)))
      [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
      m₁ [("p", 1, 1), ("q", 0, 0)] = .ok (.i32 q) :=
    memEvalExpr_mload_hit "q" (.lit (.u64 0))
      [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
      m₁ [("p", 1, 1), ("q", 0, 0)] 0 q 0 0
      (pinnedCell_pair_lookup).2 hlit1 hmemq
  have hlitI32_2 : memEvalExpr (.lit (.i32 2))
      [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
      m₁ [("p", 1, 1), ("q", 0, 0)] = .ok (.i32 2) := by
    simp [memEvalExpr, litVal]
  have haddq : memEvalExpr
      (.add (.mload "q" (.lit (.u64 0)))
        (.lit (.i32 2)))
      [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
      m₁ [("p", 1, 1), ("q", 0, 0)] = .ok (.i32 r₂) := by
    rw [memEvalExpr_add_ok _ _ _ _ _ q 2 hloadq hlitI32_2, hq2]
    exact i32_map_ok r₂
  have hmq := memEvalStmtFuel_mstore_ok F "q"
    (.lit (.u64 0))
    (.add (.mload "q" (.lit (.u64 0)))
      (.lit (.i32 2)))
    [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
    m₁ [("p", 1, 1), ("q", 0, 0)] 0 r₂ 0 0 m'
    hlit1 haddq (pinnedCell_pair_lookup).2 hsto2
  have hret : memEvalStmtFuel F (.return_ (.lit (.u32 0)))
      [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
      m' [("p", 1, 1), ("q", 0, 0)] =
      .ok (([("p", .i32 p), ("q", .i32 q), ("c", .b true)], m',
        [("p", 1, 1), ("q", 0, 0)]), .returned (.u32 0)) := by
    cases F <;>
      simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
        memEvalExpr, litVal]
  have hp : cellAt ⟨2, [(1, ⟨1, true, [p]⟩),
      (0, ⟨0, true, [q]⟩)], []⟩ 1 1 p := hfindp
  have hq : cellAt ⟨2, [(1, ⟨1, true, [p]⟩),
      (0, ⟨0, true, [q]⟩)], []⟩ 0 0 q :=
    (pinnedCell_pair_find p q _ rfl).2
  have hposts := condExec_disjoint_true _ m₁ m' 1 0 1 0 p q r₁ r₂
    hp hq pinnedCell_pair_fresh hsto1 hq1 hsto2
  have ha : memEvalStmtFuel F
      (.if_ (.var "c")
        (.mstore "p" (.lit (.u64 0))
          (.add (.mload "p" (.lit (.u64 0))) (.lit (.i32 1))))
        .skip)
      [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
      ⟨2, [(1, ⟨1, true, [p]⟩), (0, ⟨0, true, [q]⟩)], []⟩
      [("p", 1, 1), ("q", 0, 0)] =
      .ok (([("p", .i32 p), ("q", .i32 q), ("c", .b true)], m₁,
        [("p", 1, 1), ("q", 0, 0)]), .fellThrough) := by
    rw [memEvalStmtFuel_if_true _ _ _ _ _ _ _ hc]
    exact hmp
  have hrest : memEvalStmtFuel F
      (.seq (.mstore "q" (.lit (.u64 0))
        (.add (.mload "q" (.lit (.u64 0))) (.lit (.i32 2))))
      (.return_ (.lit (.u32 0))))
      [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
      m₁ [("p", 1, 1), ("q", 0, 0)] =
      .ok (([("p", .i32 p), ("q", .i32 q), ("c", .b true)], m',
        [("p", 1, 1), ("q", 0, 0)]), .returned (.u32 0)) := by
    rw [memEvalStmtFuel_seq_fallthrough _ _ _ _ _ _ _ _ _ hmq]
    exact hret
  refine ⟨?_, hposts.1, hposts.2⟩
  rw [hbody, memEvalStmtFuel_seq _ _ _ _ _ _ _ _ _ _ _ _ _ ha hrest]

/-- Pinned entry, branch masked: the `p`-store never runs, `p`
    keeps its value, the `q`-store lands. -/
theorem memEvalStmt_aliasCond_false (F : Nat) (p q r₂ : BitVec 32)
    (hq2 : checkedAddI32 q 2 = .ok r₂)
    (m' : Mem)
    (hsto : memStore ⟨2, [(1, ⟨1, true, [p]⟩),
      (0, ⟨0, true, [q]⟩)], []⟩ 0 0 0 r₂ = .ok m') :
    memEvalStmtFuel F aliasCondFunc.body
      [("p", .i32 p), ("q", .i32 q), ("c", .b false)]
      ⟨2, [(1, ⟨1, true, [p]⟩), (0, ⟨0, true, [q]⟩)], []⟩
      [("p", 1, 1), ("q", 0, 0)] =
      .ok (([("p", .i32 p), ("q", .i32 q), ("c", .b false)], m',
        [("p", 1, 1), ("q", 0, 0)]), .returned (.u32 0)) ∧
    cellAt m' 1 1 p ∧ cellAt m' 0 0 r₂ := by
  have hbody : aliasCondFunc.body =
      .seq (.if_ (.var "c")
        (.mstore "p" (.lit (.u64 0))
          (.add (.mload "p" (.lit (.u64 0))) (.lit (.i32 1))))
        .skip)
      (.seq (.mstore "q" (.lit (.u64 0))
        (.add (.mload "q" (.lit (.u64 0))) (.lit (.i32 2))))
      (.return_ (.lit (.u32 0)))) := rfl
  have hcl : envLookup [("p", .i32 p), ("q", .i32 q),
      ("c", .b false)] "c" = some (.b false) := by
    simp [envLookup]
  have hc : memEvalExpr (.var "c") [("p", .i32 p), ("q", .i32 q),
      ("c", .b false)] ⟨2, [(1, ⟨1, true, [p]⟩),
      (0, ⟨0, true, [q]⟩)], []⟩ [("p", 1, 1), ("q", 0, 0)] =
      .ok (.b false) := by
    rw [memEvalExpr_var, evalExpr_var_hit _ _ _ hcl]
  have hskip : memEvalStmtFuel F .skip
      [("p", .i32 p), ("q", .i32 q), ("c", .b false)]
      ⟨2, [(1, ⟨1, true, [p]⟩), (0, ⟨0, true, [q]⟩)], []⟩
      [("p", 1, 1), ("q", 0, 0)] =
      .ok (([("p", .i32 p), ("q", .i32 q), ("c", .b false)],
        ⟨2, [(1, ⟨1, true, [p]⟩), (0, ⟨0, true, [q]⟩)], []⟩,
        [("p", 1, 1), ("q", 0, 0)]), .fellThrough) := by
    cases F <;> rfl
  have hlit0 : memEvalExpr (.lit (.u64 0))
      [("p", .i32 p), ("q", .i32 q), ("c", .b false)]
      ⟨2, [(1, ⟨1, true, [p]⟩), (0, ⟨0, true, [q]⟩)], []⟩
      [("p", 1, 1), ("q", 0, 0)] = .ok (.u64 0) := by
    simp [memEvalExpr, litVal]
  have hfindq : memFind ⟨2, [(1, ⟨1, true, [p]⟩),
      (0, ⟨0, true, [q]⟩)], []⟩ 0 = some ⟨0, true, [q]⟩ :=
    (pinnedCell_pair_find p q _ rfl).2
  have hmemq : memLoad ⟨2, [(1, ⟨1, true, [p]⟩),
      (0, ⟨0, true, [q]⟩)], []⟩ 0 0 0 = .ok q := by
    simp [memLoad, hfindq]
  have hloadq : memEvalExpr
      (.mload "q" (.lit (.u64 0)))
      [("p", .i32 p), ("q", .i32 q), ("c", .b false)]
      ⟨2, [(1, ⟨1, true, [p]⟩), (0, ⟨0, true, [q]⟩)], []⟩
      [("p", 1, 1), ("q", 0, 0)] = .ok (.i32 q) :=
    memEvalExpr_mload_hit "q" (.lit (.u64 0))
      [("p", .i32 p), ("q", .i32 q), ("c", .b false)]
      ⟨2, [(1, ⟨1, true, [p]⟩), (0, ⟨0, true, [q]⟩)], []⟩
      [("p", 1, 1), ("q", 0, 0)] 0 q 0 0
      (pinnedCell_pair_lookup).2 hlit0 hmemq
  have hlitI32_2 : memEvalExpr (.lit (.i32 2))
      [("p", .i32 p), ("q", .i32 q), ("c", .b false)]
      ⟨2, [(1, ⟨1, true, [p]⟩), (0, ⟨0, true, [q]⟩)], []⟩
      [("p", 1, 1), ("q", 0, 0)] = .ok (.i32 2) := by
    simp [memEvalExpr, litVal]
  have haddq : memEvalExpr
      (.add (.mload "q" (.lit (.u64 0)))
        (.lit (.i32 2)))
      [("p", .i32 p), ("q", .i32 q), ("c", .b false)]
      ⟨2, [(1, ⟨1, true, [p]⟩), (0, ⟨0, true, [q]⟩)], []⟩
      [("p", 1, 1), ("q", 0, 0)] = .ok (.i32 r₂) := by
    rw [memEvalExpr_add_ok _ _ _ _ _ q 2 hloadq hlitI32_2, hq2]
    exact i32_map_ok r₂
  have hmq := memEvalStmtFuel_mstore_ok F "q"
    (.lit (.u64 0))
    (.add (.mload "q" (.lit (.u64 0)))
      (.lit (.i32 2)))
    [("p", .i32 p), ("q", .i32 q), ("c", .b false)]
    ⟨2, [(1, ⟨1, true, [p]⟩), (0, ⟨0, true, [q]⟩)], []⟩
    [("p", 1, 1), ("q", 0, 0)] 0 r₂ 0 0 m'
    hlit0 haddq (pinnedCell_pair_lookup).2 hsto
  have hret : memEvalStmtFuel F (.return_ (.lit (.u32 0)))
      [("p", .i32 p), ("q", .i32 q), ("c", .b false)]
      m' [("p", 1, 1), ("q", 0, 0)] =
      .ok (([("p", .i32 p), ("q", .i32 q), ("c", .b false)], m',
        [("p", 1, 1), ("q", 0, 0)]), .returned (.u32 0)) := by
    cases F <;>
      simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
        memEvalExpr, litVal]
  have hp : cellAt ⟨2, [(1, ⟨1, true, [p]⟩),
      (0, ⟨0, true, [q]⟩)], []⟩ 1 1 p :=
    (pinnedCell_pair_find p q _ rfl).1
  have hpostp : cellAt m' 1 1 p := by
    unfold cellAt
    rw [memFind_memStore_other _ _ 0 1 0 0 _ hsto
      (Ne.symm pinnedCell_pair_fresh)]
    exact hp
  have hq : cellAt ⟨2, [(1, ⟨1, true, [p]⟩),
      (0, ⟨0, true, [q]⟩)], []⟩ 0 0 q :=
    (pinnedCell_pair_find p q _ rfl).2
  have hpostq : cellAt m' 0 0 r₂ :=
    memFind_cell_store _ _ _ _ _ hq _ hsto
  have ha : memEvalStmtFuel F
      (.if_ (.var "c")
        (.mstore "p" (.lit (.u64 0))
          (.add (.mload "p" (.lit (.u64 0))) (.lit (.i32 1))))
        .skip)
      [("p", .i32 p), ("q", .i32 q), ("c", .b false)]
      ⟨2, [(1, ⟨1, true, [p]⟩), (0, ⟨0, true, [q]⟩)], []⟩
      [("p", 1, 1), ("q", 0, 0)] =
      .ok (([("p", .i32 p), ("q", .i32 q), ("c", .b false)],
        ⟨2, [(1, ⟨1, true, [p]⟩), (0, ⟨0, true, [q]⟩)], []⟩,
        [("p", 1, 1), ("q", 0, 0)]), .fellThrough) := by
    rw [memEvalStmtFuel_if_false _ _ _ _ _ _ _ hc]
    exact hskip
  have hrest : memEvalStmtFuel F
      (.seq (.mstore "q" (.lit (.u64 0))
        (.add (.mload "q" (.lit (.u64 0))) (.lit (.i32 2))))
      (.return_ (.lit (.u32 0))))
      [("p", .i32 p), ("q", .i32 q), ("c", .b false)]
      ⟨2, [(1, ⟨1, true, [p]⟩), (0, ⟨0, true, [q]⟩)], []⟩
      [("p", 1, 1), ("q", 0, 0)] =
      .ok (([("p", .i32 p), ("q", .i32 q), ("c", .b false)], m',
        [("p", 1, 1), ("q", 0, 0)]), .returned (.u32 0)) := by
    rw [memEvalStmtFuel_seq_fallthrough _ _ _ _ _ _ _ _ _ hmq]
    exact hret
  refine ⟨?_, hpostp, hpostq⟩
  rw [hbody, memEvalStmtFuel_seq _ _ _ _ _ _ _ _ _ _ _ _ _ ha hrest]

/-- Caller-`Mem` entry, branch taken, aliased addresses: the re-read
    observes the first store, so the second addition runs on the
    stored value and the second store wins. Shared-address pins
    (`("p",a,_)`, `("q",a,_)`) are well-defined — `layoutLookup` is
    per-name, first match wins, and the names differ. -/
theorem memEvalStmt_aliasCond_aliased_true (F : Nat) (a b t₁ t₂ : Nat)
    (m : Mem) (p q r₁ r₂ : BitVec 32)
    (hp : cellAt m a t₁ p) (hq : cellAt m b t₂ q) (heq : b = a)
    (hp1 : checkedAddI32 p 1 = .ok r₁)
    (hpa2 : checkedAddI32 r₁ 2 = .ok r₂)
    (m₁ m' : Mem)
    (hsto1 : memStore m a t₁ 0 r₁ = .ok m₁)
    (hsto2 : memStore m₁ b t₂ 0 r₂ = .ok m') :
    memEvalStmtFuel F aliasCondFunc.body
      [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
      m [("p", a, t₁), ("q", b, t₂)] =
      .ok (([("p", .i32 p), ("q", .i32 q), ("c", .b true)], m',
        [("p", a, t₁), ("q", b, t₂)]), .returned (.u32 0)) ∧
    cellAt m' a t₁ r₂ := by
  have hbody : aliasCondFunc.body =
      .seq (.if_ (.var "c")
        (.mstore "p" (.lit (.u64 0))
          (.add (.mload "p" (.lit (.u64 0))) (.lit (.i32 1))))
        .skip)
      (.seq (.mstore "q" (.lit (.u64 0))
        (.add (.mload "q" (.lit (.u64 0))) (.lit (.i32 2))))
      (.return_ (.lit (.u32 0)))) := rfl
  have hcl : envLookup [("p", .i32 p), ("q", .i32 q),
      ("c", .b true)] "c" = some (.b true) := by
    simp [envLookup]
  have hc : memEvalExpr (.var "c") [("p", .i32 p), ("q", .i32 q),
      ("c", .b true)] m [("p", a, t₁), ("q", b, t₂)] =
      .ok (.b true) := by
    rw [memEvalExpr_var, evalExpr_var_hit _ _ _ hcl]
  have hlayp : layoutLookup [("p", a, t₁), ("q", b, t₂)] "p" =
      some (a, t₁) := by
    simp [layoutLookup]
  have hlit0 : memEvalExpr (.lit (.u64 0))
      [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
      m [("p", a, t₁), ("q", b, t₂)] = .ok (.u64 0) := by
    simp [memEvalExpr, litVal]
  have hfm : memFind m a = some ⟨t₁, true, [p]⟩ := hp
  have hmemp : memLoad m a t₁ 0 = .ok p := by
    simp [memLoad, hfm]
  have hloadp : memEvalExpr
      (.mload "p" (.lit (.u64 0)))
      [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
      m [("p", a, t₁), ("q", b, t₂)] = .ok (.i32 p) :=
    memEvalExpr_mload_hit "p" (.lit (.u64 0))
      [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
      m [("p", a, t₁), ("q", b, t₂)] 0 p a t₁
      hlayp hlit0 hmemp
  have hlitI32_1 : memEvalExpr (.lit (.i32 1))
      [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
      m [("p", a, t₁), ("q", b, t₂)] = .ok (.i32 1) := by
    simp [memEvalExpr, litVal]
  have haddp : memEvalExpr
      (.add (.mload "p" (.lit (.u64 0)))
        (.lit (.i32 1)))
      [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
      m [("p", a, t₁), ("q", b, t₂)] = .ok (.i32 r₁) := by
    rw [memEvalExpr_add_ok _ _ _ _ _ p 1 hloadp hlitI32_1, hp1]
    exact i32_map_ok r₁
  have hmp := memEvalStmtFuel_mstore_ok F "p"
    (.lit (.u64 0))
    (.add (.mload "p" (.lit (.u64 0)))
      (.lit (.i32 1)))
    [("p", .i32 p), ("q", .i32 q), ("c", .b true)]
    m [("p", a, t₁), ("q", b, t₂)] 0 r₁ a t₁ m₁
    hlit0 haddp hlayp hsto1
  have hcell : cellAt m₁ a t₁ r₁ :=
    memFind_cell_store _ _ _ _ _ hp _ hsto1
  have hsame : (⟨t₁, true, [p]⟩ : Block) = ⟨t₂, true, [q]⟩ := by
    have h1 := hp
    have h2 := hq
    unfold cellAt at h1 h2
    rw [heq] at h2
    rw [h1] at h2
    exact (Option.some_inj.mp h2)
  cases hsame
  have hlayq : layoutLookup [("p", a, t₁), ("q", b, t₁)] "q" =
      some (b, t₁) := by
    simp [layoutLookup, show ("q" : String) ≠ "p" by decide]
  have hfm1 : memFind m₁ a = some ⟨t₁, true, [r₁]⟩ := hcell
  have hmemq : memLoad m₁ b t₁ 0 = .ok r₁ := by
    have hfb : memFind m₁ b = some ⟨t₁, true, [r₁]⟩ := by
      rw [heq]
      exact hfm1
    simp [memLoad, hfb]
  have hlit1 : memEvalExpr (.lit (.u64 0))
      [("p", .i32 p), ("q", .i32 p), ("c", .b true)]
      m₁ [("p", a, t₁), ("q", b, t₁)] = .ok (.u64 0) := by
    simp [memEvalExpr, litVal]
  have hloadq : memEvalExpr
      (.mload "q" (.lit (.u64 0)))
      [("p", .i32 p), ("q", .i32 p), ("c", .b true)]
      m₁ [("p", a, t₁), ("q", b, t₁)] = .ok (.i32 r₁) :=
    memEvalExpr_mload_hit "q" (.lit (.u64 0))
      [("p", .i32 p), ("q", .i32 p), ("c", .b true)]
      m₁ [("p", a, t₁), ("q", b, t₁)] 0 r₁ b t₁
      hlayq hlit1 hmemq
  have hlitI32_2 : memEvalExpr (.lit (.i32 2))
      [("p", .i32 p), ("q", .i32 p), ("c", .b true)]
      m₁ [("p", a, t₁), ("q", b, t₁)] = .ok (.i32 2) := by
    simp [memEvalExpr, litVal]
  have haddq : memEvalExpr
      (.add (.mload "q" (.lit (.u64 0)))
        (.lit (.i32 2)))
      [("p", .i32 p), ("q", .i32 p), ("c", .b true)]
      m₁ [("p", a, t₁), ("q", b, t₁)] = .ok (.i32 r₂) := by
    rw [memEvalExpr_add_ok _ _ _ _ _ r₁ 2 hloadq hlitI32_2, hpa2]
    exact i32_map_ok r₂
  have hmq := memEvalStmtFuel_mstore_ok F "q"
    (.lit (.u64 0))
    (.add (.mload "q" (.lit (.u64 0)))
      (.lit (.i32 2)))
    [("p", .i32 p), ("q", .i32 p), ("c", .b true)]
    m₁ [("p", a, t₁), ("q", b, t₁)] 0 r₂ b t₁ m'
    hlit1 haddq hlayq hsto2
  have hret : memEvalStmtFuel F (.return_ (.lit (.u32 0)))
      [("p", .i32 p), ("q", .i32 p), ("c", .b true)]
      m' [("p", a, t₁), ("q", b, t₁)] =
      .ok (([("p", .i32 p), ("q", .i32 p), ("c", .b true)], m',
        [("p", a, t₁), ("q", b, t₁)]), .returned (.u32 0)) := by
    cases F <;>
      simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
        memEvalExpr, litVal]
  have hpost : cellAt m' a t₁ r₂ := by
    rw [heq] at hsto2
    exact memFind_cell_store _ _ _ _ _ hcell _ hsto2
  have ha : memEvalStmtFuel F
      (.if_ (.var "c")
        (.mstore "p" (.lit (.u64 0))
          (.add (.mload "p" (.lit (.u64 0))) (.lit (.i32 1))))
        .skip)
      [("p", .i32 p), ("q", .i32 p), ("c", .b true)]
      m [("p", a, t₁), ("q", b, t₁)] =
      .ok (([("p", .i32 p), ("q", .i32 p), ("c", .b true)], m₁,
        [("p", a, t₁), ("q", b, t₁)]), .fellThrough) := by
    have hc' : memEvalExpr (.var "c") [("p", .i32 p), ("q", .i32 p),
        ("c", .b true)] m [("p", a, t₁), ("q", b, t₁)] =
        .ok (.b true) := by
      rw [memEvalExpr_var, evalExpr_var_hit _ _ _ hcl]
    rw [memEvalStmtFuel_if_true _ _ _ _ _ _ _ hc']
    exact hmp
  have hrest : memEvalStmtFuel F
      (.seq (.mstore "q" (.lit (.u64 0))
        (.add (.mload "q" (.lit (.u64 0))) (.lit (.i32 2))))
      (.return_ (.lit (.u32 0))))
      [("p", .i32 p), ("q", .i32 p), ("c", .b true)]
      m₁ [("p", a, t₁), ("q", b, t₁)] =
      .ok (([("p", .i32 p), ("q", .i32 p), ("c", .b true)], m',
        [("p", a, t₁), ("q", b, t₁)]), .returned (.u32 0)) := by
    rw [memEvalStmtFuel_seq_fallthrough _ _ _ _ _ _ _ _ _ hmq]
    exact hret
  refine ⟨?_, hpost⟩
  rw [hbody, memEvalStmtFuel_seq _ _ _ _ _ _ _ _ _ _ _ _ _ ha hrest]

/-- Caller-`Mem` entry, branch masked, aliased addresses: only the
    `q`-store runs, on the shared cell. -/
theorem memEvalStmt_aliasCond_aliased_false (F : Nat) (a b t₁ t₂ : Nat)
    (m : Mem) (p q r₂ : BitVec 32)
    (hp : cellAt m a t₁ p) (hq : cellAt m b t₂ q) (heq : b = a)
    (hq2 : checkedAddI32 q 2 = .ok r₂)
    (m' : Mem)
    (hsto : memStore m b t₂ 0 r₂ = .ok m') :
    memEvalStmtFuel F aliasCondFunc.body
      [("p", .i32 p), ("q", .i32 q), ("c", .b false)]
      m [("p", a, t₁), ("q", b, t₂)] =
      .ok (([("p", .i32 p), ("q", .i32 q), ("c", .b false)], m',
        [("p", a, t₁), ("q", b, t₂)]), .returned (.u32 0)) ∧
    cellAt m' a t₁ r₂ := by
  have hbody : aliasCondFunc.body =
      .seq (.if_ (.var "c")
        (.mstore "p" (.lit (.u64 0))
          (.add (.mload "p" (.lit (.u64 0))) (.lit (.i32 1))))
        .skip)
      (.seq (.mstore "q" (.lit (.u64 0))
        (.add (.mload "q" (.lit (.u64 0))) (.lit (.i32 2))))
      (.return_ (.lit (.u32 0)))) := rfl
  have hcl : envLookup [("p", .i32 p), ("q", .i32 q),
      ("c", .b false)] "c" = some (.b false) := by
    simp [envLookup]
  have hc : memEvalExpr (.var "c") [("p", .i32 p), ("q", .i32 q),
      ("c", .b false)] m [("p", a, t₁), ("q", b, t₂)] =
      .ok (.b false) := by
    rw [memEvalExpr_var, evalExpr_var_hit _ _ _ hcl]
  have hskip : memEvalStmtFuel F .skip
      [("p", .i32 p), ("q", .i32 q), ("c", .b false)]
      m [("p", a, t₁), ("q", b, t₂)] =
      .ok (([("p", .i32 p), ("q", .i32 q), ("c", .b false)],
        m, [("p", a, t₁), ("q", b, t₂)]), .fellThrough) := by
    cases F <;> rfl
  have hlayq : layoutLookup [("p", a, t₁), ("q", b, t₂)] "q" =
      some (b, t₂) := by
    simp [layoutLookup, show ("q" : String) ≠ "p" by decide]
  have hlit0 : memEvalExpr (.lit (.u64 0))
      [("p", .i32 p), ("q", .i32 q), ("c", .b false)]
      m [("p", a, t₁), ("q", b, t₂)] = .ok (.u64 0) := by
    simp [memEvalExpr, litVal]
  have hfm : memFind m b = some ⟨t₂, true, [q]⟩ := hq
  have hmemq : memLoad m b t₂ 0 = .ok q := by
    simp [memLoad, hfm]
  have hloadq : memEvalExpr
      (.mload "q" (.lit (.u64 0)))
      [("p", .i32 p), ("q", .i32 q), ("c", .b false)]
      m [("p", a, t₁), ("q", b, t₂)] = .ok (.i32 q) :=
    memEvalExpr_mload_hit "q" (.lit (.u64 0))
      [("p", .i32 p), ("q", .i32 q), ("c", .b false)]
      m [("p", a, t₁), ("q", b, t₂)] 0 q b t₂
      hlayq hlit0 hmemq
  have hlitI32_2 : memEvalExpr (.lit (.i32 2))
      [("p", .i32 p), ("q", .i32 q), ("c", .b false)]
      m [("p", a, t₁), ("q", b, t₂)] = .ok (.i32 2) := by
    simp [memEvalExpr, litVal]
  have haddq : memEvalExpr
      (.add (.mload "q" (.lit (.u64 0)))
        (.lit (.i32 2)))
      [("p", .i32 p), ("q", .i32 q), ("c", .b false)]
      m [("p", a, t₁), ("q", b, t₂)] = .ok (.i32 r₂) := by
    rw [memEvalExpr_add_ok _ _ _ _ _ q 2 hloadq hlitI32_2, hq2]
    exact i32_map_ok r₂
  have hmq := memEvalStmtFuel_mstore_ok F "q"
    (.lit (.u64 0))
    (.add (.mload "q" (.lit (.u64 0)))
      (.lit (.i32 2)))
    [("p", .i32 p), ("q", .i32 q), ("c", .b false)]
    m [("p", a, t₁), ("q", b, t₂)] 0 r₂ b t₂ m'
    hlit0 haddq hlayq hsto
  have hret : memEvalStmtFuel F (.return_ (.lit (.u32 0)))
      [("p", .i32 p), ("q", .i32 q), ("c", .b false)]
      m' [("p", a, t₁), ("q", b, t₂)] =
      .ok (([("p", .i32 p), ("q", .i32 q), ("c", .b false)], m',
        [("p", a, t₁), ("q", b, t₂)]), .returned (.u32 0)) := by
    cases F <;>
      simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
        memEvalExpr, litVal]
  have hsame : (⟨t₁, true, [p]⟩ : Block) = ⟨t₂, true, [q]⟩ := by
    have h1 := hp
    have h2 := hq
    unfold cellAt at h1 h2
    rw [heq] at h2
    rw [h1] at h2
    exact (Option.some_inj.mp h2)
  cases hsame
  have hpost : cellAt m' a t₁ r₂ := by
    rw [←heq]
    exact memFind_cell_store _ _ _ _ _ hq _ hsto
  have ha : memEvalStmtFuel F
      (.if_ (.var "c")
        (.mstore "p" (.lit (.u64 0))
          (.add (.mload "p" (.lit (.u64 0))) (.lit (.i32 1))))
        .skip)
      [("p", .i32 p), ("q", .i32 p), ("c", .b false)]
      m [("p", a, t₁), ("q", b, t₁)] =
      .ok (([("p", .i32 p), ("q", .i32 p), ("c", .b false)],
        m, [("p", a, t₁), ("q", b, t₁)]), .fellThrough) := by
    have hc' : memEvalExpr (.var "c") [("p", .i32 p), ("q", .i32 p),
        ("c", .b false)] m [("p", a, t₁), ("q", b, t₁)] =
        .ok (.b false) := by
      rw [memEvalExpr_var, evalExpr_var_hit _ _ _ hcl]
    rw [memEvalStmtFuel_if_false _ _ _ _ _ _ _ hc']
    exact hskip
  have hrest : memEvalStmtFuel F
      (.seq (.mstore "q" (.lit (.u64 0))
        (.add (.mload "q" (.lit (.u64 0))) (.lit (.i32 2))))
      (.return_ (.lit (.u32 0))))
      [("p", .i32 p), ("q", .i32 p), ("c", .b false)]
      m [("p", a, t₁), ("q", b, t₁)] =
      .ok (([("p", .i32 p), ("q", .i32 p), ("c", .b false)], m',
        [("p", a, t₁), ("q", b, t₁)]), .returned (.u32 0)) := by
    have hmq' : memEvalStmtFuel F
        (.mstore "q" (.lit (.u64 0))
          (.add (.mload "q" (.lit (.u64 0))) (.lit (.i32 2))))
        [("p", .i32 p), ("q", .i32 p), ("c", .b false)]
        m [("p", a, t₁), ("q", b, t₁)] =
        .ok (([("p", .i32 p), ("q", .i32 p), ("c", .b false)], m',
          [("p", a, t₁), ("q", b, t₁)]), .fellThrough) := hmq
    rw [memEvalStmtFuel_seq_fallthrough _ _ _ _ _ _ _ _ _ hmq']
    exact hret
  refine ⟨?_, hpost⟩
  rw [hbody, memEvalStmtFuel_seq _ _ _ _ _ _ _ _ _ _ _ _ _ ha hrest]
