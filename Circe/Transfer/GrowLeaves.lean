/-
Circe.Transfer.GrowLeaves — N4d-iv-b1 growth-leaf transfers (pure and mutating).
Over `Circe.Transfer.Acc`.
-/
import Circe.Transfer.Acc

/-! ## N4d-iv-b1 growth leaves: pure-leaf transfer -/

/-- Entry memory for one owned triple: the `bindMemArgs` two-block
    form (the `memAllocData` shadow plus the liveness-correct head;
    first-hit wins, so loads see `!b.freed`). -/
def tripleMem (b : Vec32) (len cap : Nat) : Mem :=
  ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
    (BitVec.ofNat 32 cap) :: b.val⟩),
    (0, ⟨0, true, (BitVec.ofNat 32 len) ::
    (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩

/-- The same memory after the consume: `memFree` head-conses the dead
    block, keeping the header words. -/
def tripleMemFreed (b : Vec32) (len cap : Nat) : Mem :=
  ⟨1, [(0, ⟨0, false, (BitVec.ofNat 32 len) ::
    (BitVec.ofNat 32 cap) :: b.val⟩),
    (0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
    (BitVec.ofNat 32 cap) :: b.val⟩),
    (0, ⟨0, true, (BitVec.ofNat 32 len) ::
    (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩

/-- `memEval` for the default ctor: `vgrowNew` over `0` runs `vecNew`
    on both sides (no memory interaction). -/
theorem memEvalFuncFuel_stdVecEmptyCtor (F : Nat) :
    memEvalFuncFuel F stdVecEmptyCtorFunc [] = stdVecEmptyCtorFwd := by
  have hb : bindMemArgs stdVecEmptyCtorFunc.args [] emptyMem =
      some ([], emptyMem, []) := bindMemArgs_stdVecEmptyCtor
  have hbody : stdVecEmptyCtorFunc.body =
      .return_ (.vgrowNew (.lit (.u64 (BitVec.ofNat 64 0)))) := rfl
  have h0 : (0 : Nat) < 2 ^ 64 := by decide
  have hnew : evalExpr (.vgrowNew (.lit (.u64 (BitVec.ofNat 64 0)))) [] =
      .ok (.stdVecOwned ⟨[], false⟩ 0 0) := by
    have h := evalExpr_vgrowNew_lit (BitVec.ofNat 64 0) []
    rw [ofNat64_toNat 0 h0] at h
    simpa using h
  have hlit : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0))) []
      emptyMem [] = evalExpr (.lit (.u64 (BitVec.ofNat 64 0))) [] :=
    memEvalExpr_lit _ _ _ _
  have hagree := memEvalExpr_vgrowNew_agree
    (.lit (.u64 (BitVec.ofNat 64 0))) [] emptyMem [] hlit
  have hret := memEvalStmtFuel_return F
    (.vgrowNew (.lit (.u64 (BitVec.ofNat 64 0)))) _ _ _ _ hagree hnew
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  rfl

/-- Transfer for the default ctor. -/
theorem memTransfer_stdVecEmptyCtor (F : Nat)
    (_h : oracleNoalias stdVecEmptyCtorFunc []) :
    memEvalFuncFuel F stdVecEmptyCtorFunc [] =
      evalFuncFuel F stdVecEmptyCtorFunc [] := by
  rw [memEvalFuncFuel_stdVecEmptyCtor F, evalFuncFuel_stdVecEmptyCtor F]

/-- `memEval` for the empty-effect leaves (pure `i32 0` literal). -/
theorem memEvalFuncFuel_stdVecUnit (F : Nat) :
    memEvalFuncFuel F stdVecUnitFunc [] = stdVecUnitFwd := by
  have hb : bindMemArgs stdVecUnitFunc.args [] emptyMem =
      some ([], emptyMem, []) := bindMemArgs_stdVecUnit
  have hbody : stdVecUnitFunc.body =
      .return_ (.lit (.i32 (BitVec.ofNat 32 0))) := rfl
  have hlit : evalExpr (.lit (.i32 (BitVec.ofNat 32 0))) [] =
      .ok (.i32 (BitVec.ofNat 32 0)) := by
    simp [evalExpr, litVal]
  have hagree : memEvalExpr (.lit (.i32 (BitVec.ofNat 32 0))) []
      emptyMem [] = evalExpr (.lit (.i32 (BitVec.ofNat 32 0))) [] :=
    memEvalExpr_lit _ _ _ _
  have hret := memEvalStmtFuel_return F
    (.lit (.i32 (BitVec.ofNat 32 0))) _ _ _ _ hagree hlit
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  rfl

/-- Transfer for the empty-effect leaves. -/
theorem memTransfer_stdVecUnit (F : Nat)
    (_h : oracleNoalias stdVecUnitFunc []) :
    memEvalFuncFuel F stdVecUnitFunc [] =
      evalFuncFuel F stdVecUnitFunc [] := by
  rw [memEvalFuncFuel_stdVecUnit F, evalFuncFuel_stdVecUnit F]

/-- `memEval` for the destroy range (pure `i32 0` literal; the two
    owned offsets pin nothing). -/
theorem memEvalFuncFuel_stdVecDestroyNoop (F : Nat) (a b : BitVec 64) :
    memEvalFuncFuel F stdVecDestroyNoopFunc [.u64 a, .u64 b] =
      stdVecDestroyNoopFwd := by
  have hb : bindMemArgs stdVecDestroyNoopFunc.args [.u64 a, .u64 b]
      emptyMem =
      some ([("a", .u64 a), ("b", .u64 b)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "a", ty := .u 64, role := .owned },
       { name := "b", ty := .u 64, role := .owned }]
      [.u64 a, .u64 b] emptyMem = _
    exact bindMemArgs_stdVecDestroyNoop a b
  have hbody : stdVecDestroyNoopFunc.body =
      .return_ (.lit (.i32 (BitVec.ofNat 32 0))) := rfl
  have hlit : evalExpr (.lit (.i32 (BitVec.ofNat 32 0)))
      [("a", .u64 a), ("b", .u64 b)] =
      .ok (.i32 (BitVec.ofNat 32 0)) := by
    simp [evalExpr, litVal]
  have hagree : memEvalExpr (.lit (.i32 (BitVec.ofNat 32 0)))
      [("a", .u64 a), ("b", .u64 b)] emptyMem [] =
      evalExpr (.lit (.i32 (BitVec.ofNat 32 0)))
        [("a", .u64 a), ("b", .u64 b)] :=
    memEvalExpr_lit _ _ _ _
  have hret := memEvalStmtFuel_return F
    (.lit (.i32 (BitVec.ofNat 32 0))) _ _ _ _ hagree hlit
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  rfl

/-- Transfer for the destroy range. -/
theorem memTransfer_stdVecDestroyNoop (F : Nat) (a b : BitVec 64)
    (_h : oracleNoalias stdVecDestroyNoopFunc [.u64 a, .u64 b]) :
    memEvalFuncFuel F stdVecDestroyNoopFunc [.u64 a, .u64 b] =
      evalFuncFuel F stdVecDestroyNoopFunc [.u64 a, .u64 b] := by
  rw [memEvalFuncFuel_stdVecDestroyNoop F a b,
    evalFuncFuel_stdVecDestroyNoop F a b]

/-- `memEval` for element destroy (pure `i32 0` literal). -/
theorem memEvalFuncFuel_stdVecDestroyPtr (F : Nat) (p : BitVec 64) :
    memEvalFuncFuel F stdVecDestroyPtrFunc [.u64 p] =
      stdVecDestroyPtrFwd := by
  have hb : bindMemArgs stdVecDestroyPtrFunc.args [.u64 p] emptyMem =
      some ([("p", .u64 p)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "p", ty := .u 64, role := .owned }]
      [.u64 p] emptyMem = _
    exact bindMemArgs_stdVecDestroyPtr p
  have hbody : stdVecDestroyPtrFunc.body =
      .return_ (.lit (.i32 (BitVec.ofNat 32 0))) := rfl
  have hlit : evalExpr (.lit (.i32 (BitVec.ofNat 32 0)))
      [("p", .u64 p)] = .ok (.i32 (BitVec.ofNat 32 0)) := by
    simp [evalExpr, litVal]
  have hagree : memEvalExpr (.lit (.i32 (BitVec.ofNat 32 0)))
      [("p", .u64 p)] emptyMem [] =
      evalExpr (.lit (.i32 (BitVec.ofNat 32 0))) [("p", .u64 p)] :=
    memEvalExpr_lit _ _ _ _
  have hret := memEvalStmtFuel_return F
    (.lit (.i32 (BitVec.ofNat 32 0))) _ _ _ _ hagree hlit
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  rfl

/-- Transfer for element destroy. -/
theorem memTransfer_stdVecDestroyPtr (F : Nat) (p : BitVec 64)
    (_h : oracleNoalias stdVecDestroyPtrFunc [.u64 p]) :
    memEvalFuncFuel F stdVecDestroyPtrFunc [.u64 p] =
      evalFuncFuel F stdVecDestroyPtrFunc [.u64 p] := by
  rw [memEvalFuncFuel_stdVecDestroyPtr F p,
    evalFuncFuel_stdVecDestroyPtr F p]

/-- `memEval` for the allocator projection (pure `i32 0` literal; the
    pinned triple is ignored on both sides). -/
theorem memEvalFuncFuel_stdVecGetTp (F : Nat) (b : Vec32)
    (len cap : Nat) :
    memEvalFuncFuel F stdVecGetTpFunc [.stdVecOwned b len cap] =
      stdVecGetTpFwd := by
  have hb : bindMemArgs stdVecGetTpFunc.args [.stdVecOwned b len cap]
      emptyMem =
      some ([("t", .stdVecOwned b len cap)],
        (tripleMem b len cap),
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned }]
      [.stdVecOwned b len cap] emptyMem = _
    exact bindMemArgs_stdVecGetTp b len cap
  have hbody : stdVecGetTpFunc.body =
      .return_ (.lit (.i32 (BitVec.ofNat 32 0))) := rfl
  have hlit : evalExpr (.lit (.i32 (BitVec.ofNat 32 0)))
      [("t", .stdVecOwned b len cap)] =
      .ok (.i32 (BitVec.ofNat 32 0)) := by
    simp [evalExpr, litVal]
  have hagree : memEvalExpr (.lit (.i32 (BitVec.ofNat 32 0)))
      [("t", .stdVecOwned b len cap)]
      (tripleMem b len cap)
      [("t", 0, 0)] =
      evalExpr (.lit (.i32 (BitVec.ofNat 32 0)))
        [("t", .stdVecOwned b len cap)] :=
    memEvalExpr_lit _ _ _ _
  have hret := memEvalStmtFuel_return F
    (.lit (.i32 (BitVec.ofNat 32 0))) _ _ _ _ hagree hlit
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  rfl

/-- Transfer for the allocator projection. -/
theorem memTransfer_stdVecGetTp (F : Nat) (b : Vec32) (len cap : Nat)
    (_h : oracleNoalias stdVecGetTpFunc [.stdVecOwned b len cap]) :
    memEvalFuncFuel F stdVecGetTpFunc [.stdVecOwned b len cap] =
      evalFuncFuel F stdVecGetTpFunc [.stdVecOwned b len cap] := by
  rw [memEvalFuncFuel_stdVecGetTp F b len cap,
    evalFuncFuel_stdVecGetTp F b len cap]

/-- `memEval` for the max-size chain (pure const literal). -/
theorem memEvalFuncFuel_stdVecDiffMax (F : Nat) :
    memEvalFuncFuel F stdVecDiffMaxFunc [] = stdVecDiffMaxFwd := by
  have hb : bindMemArgs stdVecDiffMaxFunc.args [] emptyMem =
      some ([], emptyMem, []) := bindMemArgs_stdVecDiffMax
  have hbody : stdVecDiffMaxFunc.body =
      .return_ (.lit (.u64 stdVecMaxDiffBV)) := rfl
  have hlit : evalExpr (.lit (.u64 stdVecMaxDiffBV)) [] =
      .ok (.u64 stdVecMaxDiffBV) := by
    simp [evalExpr, litVal]
  have hagree : memEvalExpr (.lit (.u64 stdVecMaxDiffBV)) []
      emptyMem [] = evalExpr (.lit (.u64 stdVecMaxDiffBV)) [] :=
    memEvalExpr_lit _ _ _ _
  have hret := memEvalStmtFuel_return F
    (.lit (.u64 stdVecMaxDiffBV)) _ _ _ _ hagree hlit
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  rfl

/-- Transfer for the max-size chain. -/
theorem memTransfer_stdVecDiffMax (F : Nat)
    (_h : oracleNoalias stdVecDiffMaxFunc []) :
    memEvalFuncFuel F stdVecDiffMaxFunc [] =
      evalFuncFuel F stdVecDiffMaxFunc [] := by
  rw [memEvalFuncFuel_stdVecDiffMax F, evalFuncFuel_stdVecDiffMax F]

/-- `memEval` for the iterator identities (pure variable). -/
theorem memEvalFuncFuel_stdVecIterId (F : Nat) (x : BitVec 64) :
    memEvalFuncFuel F stdVecIterIdFunc [.u64 x] = stdVecIterIdFwd x := by
  have hb : bindMemArgs stdVecIterIdFunc.args [.u64 x] emptyMem =
      some ([("p", .u64 x)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "p", ty := .u 64, role := .owned }]
      [.u64 x] emptyMem = _
    exact bindMemArgs_stdVecIterId x
  have hbody : stdVecIterIdFunc.body = .return_ (.var "p") := rfl
  have hp := envLookup_stdVecIterId_p x
  have hvar : evalExpr (.var "p") [("p", .u64 x)] = .ok (.u64 x) := by
    simp [evalExpr, hp]
  have hagree : memEvalExpr (.var "p") [("p", .u64 x)] emptyMem [] =
      evalExpr (.var "p") [("p", .u64 x)] :=
    memEvalExpr_var _ _ _ _
  have hret := memEvalStmtFuel_return F (.var "p") _ _ _ _ hagree hvar
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  simp [stdVecIterIdFwd]

/-- Transfer for the iterator identities. -/
theorem memTransfer_stdVecIterId (F : Nat) (x : BitVec 64)
    (_h : oracleNoalias stdVecIterIdFunc [.u64 x]) :
    memEvalFuncFuel F stdVecIterIdFunc [.u64 x] =
      evalFuncFuel F stdVecIterIdFunc [.u64 x] := by
  rw [memEvalFuncFuel_stdVecIterId F x, evalFuncFuel_stdVecIterId F x]

/-- `memEval` for `miEl` (wrapping `usub` agrees on both sides). -/
theorem memEvalFuncFuel_stdVecMinusEl (F : Nat) (it n : BitVec 64) :
    memEvalFuncFuel F stdVecMinusElFunc [.u64 it, .u64 n] =
      stdVecMinusElFwd it n := by
  have hb : bindMemArgs stdVecMinusElFunc.args [.u64 it, .u64 n] emptyMem =
      some ([("it", .u64 it), ("n", .u64 n)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "it", ty := .u 64, role := .owned },
       { name := "n", ty := .u 64, role := .owned }]
      [.u64 it, .u64 n] emptyMem = _
    exact bindMemArgs_stdVecMinusEl it n
  have hbody : stdVecMinusElFunc.body =
      .return_ (.usub (.var "it") (.var "n")) := rfl
  have hit := envLookup_stdVecMinusEl_it it n
  have hn := envLookup_stdVecMinusEl_n it n
  have hvit : evalExpr (.var "it") [("it", .u64 it), ("n", .u64 n)] =
      .ok (.u64 it) := by
    simp [evalExpr, hit]
  have hvn : evalExpr (.var "n") [("it", .u64 it), ("n", .u64 n)] =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  have hsub : evalExpr (.usub (.var "it") (.var "n"))
      [("it", .u64 it), ("n", .u64 n)] = .ok (.u64 (it - n)) :=
    evalExpr_usub_u64u64 _ _ _ _ _ hvit hvn
  have hmit : memEvalExpr (.var "it") [("it", .u64 it), ("n", .u64 n)]
      emptyMem [] = evalExpr (.var "it")
        [("it", .u64 it), ("n", .u64 n)] :=
    memEvalExpr_var _ _ _ _
  have hmn : memEvalExpr (.var "n") [("it", .u64 it), ("n", .u64 n)]
      emptyMem [] = evalExpr (.var "n")
        [("it", .u64 it), ("n", .u64 n)] :=
    memEvalExpr_var _ _ _ _
  have hagree := memEvalExpr_usub_agree (.var "it") (.var "n") _ _ _ hmit hmn
  have hret := memEvalStmtFuel_return F
    (.usub (.var "it") (.var "n")) _ _ _ _ hagree hsub
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  simp [stdVecMinusElFwd]

/-- Transfer for `miEl`. -/
theorem memTransfer_stdVecMinusEl (F : Nat) (it n : BitVec 64)
    (_h : oracleNoalias stdVecMinusElFunc [.u64 it, .u64 n]) :
    memEvalFuncFuel F stdVecMinusElFunc [.u64 it, .u64 n] =
      evalFuncFuel F stdVecMinusElFunc [.u64 it, .u64 n] := by
  rw [memEvalFuncFuel_stdVecMinusEl F it n,
    evalFuncFuel_stdVecMinusEl F it n]

/-- `memEval` for `mi` (bit-exact `s64diff` agrees on both sides). -/
theorem memEvalFuncFuel_stdVecMinus (F : Nat) (a b : BitVec 64) :
    memEvalFuncFuel F stdVecMinusFunc [.u64 a, .u64 b] =
      stdVecMinusFwd a b := by
  have hb : bindMemArgs stdVecMinusFunc.args [.u64 a, .u64 b] emptyMem =
      some ([("a", .u64 a), ("b", .u64 b)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "a", ty := .u 64, role := .owned },
       { name := "b", ty := .u 64, role := .owned }]
      [.u64 a, .u64 b] emptyMem = _
    exact bindMemArgs_stdVecMinus a b
  have hbody : stdVecMinusFunc.body =
      .return_ (.s64diff (.var "a") (.var "b")) := rfl
  have ha := envLookup_stdVecMinus_a a b
  have hbb := envLookup_stdVecMinus_b a b
  have hva : evalExpr (.var "a") [("a", .u64 a), ("b", .u64 b)] =
      .ok (.u64 a) := by
    simp [evalExpr, ha]
  have hvb : evalExpr (.var "b") [("a", .u64 a), ("b", .u64 b)] =
      .ok (.u64 b) := by
    simp [evalExpr, hbb]
  have hdiff : evalExpr (.s64diff (.var "a") (.var "b"))
      [("a", .u64 a), ("b", .u64 b)] = .ok (.i64 (a - b)) :=
    evalExpr_s64diff_u64u64 _ _ _ _ _ hva hvb
  have hma : memEvalExpr (.var "a") [("a", .u64 a), ("b", .u64 b)]
      emptyMem [] = evalExpr (.var "a") [("a", .u64 a), ("b", .u64 b)] :=
    memEvalExpr_var _ _ _ _
  have hmb : memEvalExpr (.var "b") [("a", .u64 a), ("b", .u64 b)]
      emptyMem [] = evalExpr (.var "b") [("a", .u64 a), ("b", .u64 b)] :=
    memEvalExpr_var _ _ _ _
  have hagree := memEvalExpr_s64diff_agree (.var "a") (.var "b") _ _ _ hma hmb
  have hret := memEvalStmtFuel_return F
    (.s64diff (.var "a") (.var "b")) _ _ _ _ hagree hdiff
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  simp [stdVecMinusFwd]

/-- Transfer for `mi`. -/
theorem memTransfer_stdVecMinus (F : Nat) (a b : BitVec 64)
    (_h : oracleNoalias stdVecMinusFunc [.u64 a, .u64 b]) :
    memEvalFuncFuel F stdVecMinusFunc [.u64 a, .u64 b] =
      evalFuncFuel F stdVecMinusFunc [.u64 a, .u64 b] := by
  rw [memEvalFuncFuel_stdVecMinus F a b, evalFuncFuel_stdVecMinus F a b]

/-- `memEval` for `plEl` (wrapping `uadd` agrees on both sides). -/
theorem memEvalFuncFuel_stdVecPlusEl (F : Nat) (it n : BitVec 64) :
    memEvalFuncFuel F stdVecPlusElFunc [.u64 it, .u64 n] =
      stdVecPlusElFwd it n := by
  have hb : bindMemArgs stdVecPlusElFunc.args [.u64 it, .u64 n] emptyMem =
      some ([("it", .u64 it), ("n", .u64 n)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "it", ty := .u 64, role := .owned },
       { name := "n", ty := .u 64, role := .owned }]
      [.u64 it, .u64 n] emptyMem = _
    exact bindMemArgs_stdVecPlusEl it n
  have hbody : stdVecPlusElFunc.body =
      .return_ (.uadd (.var "it") (.var "n")) := rfl
  have hit := envLookup_stdVecPlusEl_it it n
  have hn := envLookup_stdVecPlusEl_n it n
  have hvit : evalExpr (.var "it") [("it", .u64 it), ("n", .u64 n)] =
      .ok (.u64 it) := by
    simp [evalExpr, hit]
  have hvn : evalExpr (.var "n") [("it", .u64 it), ("n", .u64 n)] =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  have hadd : evalExpr (.uadd (.var "it") (.var "n"))
      [("it", .u64 it), ("n", .u64 n)] = .ok (.u64 (it + n)) :=
    evalExpr_uadd_u64 _ _ _ _ _ hvit hvn
  have hmit : memEvalExpr (.var "it") [("it", .u64 it), ("n", .u64 n)]
      emptyMem [] = evalExpr (.var "it")
        [("it", .u64 it), ("n", .u64 n)] :=
    memEvalExpr_var _ _ _ _
  have hmn : memEvalExpr (.var "n") [("it", .u64 it), ("n", .u64 n)]
      emptyMem [] = evalExpr (.var "n")
        [("it", .u64 it), ("n", .u64 n)] :=
    memEvalExpr_var _ _ _ _
  have hagree := memEvalExpr_uadd_agree (.var "it") (.var "n") _ _ _ hmit hmn
  have hret := memEvalStmtFuel_return F
    (.uadd (.var "it") (.var "n")) _ _ _ _ hagree hadd
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  simp [stdVecPlusElFwd]

/-- Transfer for `plEl`. -/
theorem memTransfer_stdVecPlusEl (F : Nat) (it n : BitVec 64)
    (_h : oracleNoalias stdVecPlusElFunc [.u64 it, .u64 n]) :
    memEvalFuncFuel F stdVecPlusElFunc [.u64 it, .u64 n] =
      evalFuncFuel F stdVecPlusElFunc [.u64 it, .u64 n] := by
  rw [memEvalFuncFuel_stdVecPlusEl F it n,
    evalFuncFuel_stdVecPlusEl F it n]

/-- `memEval` for const-iterator `operator==` (`ueq` agrees on both
    sides). -/
theorem memEvalFuncFuel_stdVecIterEq (F : Nat) (a b : BitVec 64) :
    memEvalFuncFuel F stdVecIterEqFunc [.u64 a, .u64 b] =
      stdVecIterEqFwd a b := by
  have hb : bindMemArgs stdVecIterEqFunc.args [.u64 a, .u64 b] emptyMem =
      some ([("a", .u64 a), ("b", .u64 b)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "a", ty := .u 64, role := .owned },
       { name := "b", ty := .u 64, role := .owned }]
      [.u64 a, .u64 b] emptyMem = _
    exact bindMemArgs_stdVecIterEq a b
  have hbody : stdVecIterEqFunc.body =
      .return_ (.ueq (.var "a") (.var "b")) := rfl
  have ha := envLookup_stdVecIterEq_a a b
  have hbb := envLookup_stdVecIterEq_b a b
  have hva : evalExpr (.var "a") [("a", .u64 a), ("b", .u64 b)] =
      .ok (.u64 a) := by
    simp [evalExpr, ha]
  have hvb : evalExpr (.var "b") [("a", .u64 a), ("b", .u64 b)] =
      .ok (.u64 b) := by
    simp [evalExpr, hbb]
  have heq : evalExpr (.ueq (.var "a") (.var "b"))
      [("a", .u64 a), ("b", .u64 b)] = .ok (.b (a == b)) := by
    simp [evalExpr, ha, hbb]
  have hma : memEvalExpr (.var "a") [("a", .u64 a), ("b", .u64 b)]
      emptyMem [] = evalExpr (.var "a") [("a", .u64 a), ("b", .u64 b)] :=
    memEvalExpr_var _ _ _ _
  have hmb : memEvalExpr (.var "b") [("a", .u64 a), ("b", .u64 b)]
      emptyMem [] = evalExpr (.var "b") [("a", .u64 a), ("b", .u64 b)] :=
    memEvalExpr_var _ _ _ _
  have hagree := memEvalExpr_ueq_agree (.var "a") (.var "b") _ _ _ hma hmb
  have hret := memEvalStmtFuel_return F
    (.ueq (.var "a") (.var "b")) _ _ _ _ hagree heq
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  simp [stdVecIterEqFwd]

/-- Transfer for const-iterator `operator==`. -/
theorem memTransfer_stdVecIterEq (F : Nat) (a b : BitVec 64)
    (_h : oracleNoalias stdVecIterEqFunc [.u64 a, .u64 b]) :
    memEvalFuncFuel F stdVecIterEqFunc [.u64 a, .u64 b] =
      evalFuncFuel F stdVecIterEqFunc [.u64 a, .u64 b] := by
  rw [memEvalFuncFuel_stdVecIterEq F a b, evalFuncFuel_stdVecIterEq F a b]

/-- `memEval` for `begin` (pure `0` literal; the pinned triple is
    ignored on both sides). -/
theorem memEvalFuncFuel_stdVecBegin (F : Nat) (b : Vec32)
    (len cap : Nat) :
    memEvalFuncFuel F stdVecBeginFunc [.stdVecOwned b len cap] =
      stdVecBeginFwd := by
  have hb : bindMemArgs stdVecBeginFunc.args [.stdVecOwned b len cap]
      emptyMem =
      some ([("t", .stdVecOwned b len cap)],
        (tripleMem b len cap),
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned }]
      [.stdVecOwned b len cap] emptyMem = _
    exact bindMemArgs_stdVecBegin b len cap
  have hbody : stdVecBeginFunc.body =
      .return_ (.lit (.u64 (BitVec.ofNat 64 0))) := rfl
  have hagree : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("t", .stdVecOwned b len cap)]
      (tripleMem b len cap)
      [("t", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("t", .stdVecOwned b len cap)] :=
    memEvalExpr_lit _ _ _ _
  have hlit : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("t", .stdVecOwned b len cap)] =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  have hret := memEvalStmtFuel_return F
    (.lit (.u64 (BitVec.ofNat 64 0))) _ _ _ _ hagree hlit
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  rfl

/-- Transfer for `begin`. -/
theorem memTransfer_stdVecBegin (F : Nat) (b : Vec32) (len cap : Nat)
    (_h : oracleNoalias stdVecBeginFunc [.stdVecOwned b len cap]) :
    memEvalFuncFuel F stdVecBeginFunc [.stdVecOwned b len cap] =
      evalFuncFuel F stdVecBeginFunc [.stdVecOwned b len cap] := by
  rw [memEvalFuncFuel_stdVecBegin F b len cap,
    evalFuncFuel_stdVecBegin F b len cap]

/-- `memEval` for `end` (the length header word agrees in memory;
    the triple must be live — a use-after-free `len` read is the one
    silent value/memory divergence, loud nowhere on this path). -/
theorem memEvalFuncFuel_stdVecEnd (F : Nat) (b : Vec32)
    (len cap : Nat) (hlive : b.freed = false) :
    memEvalFuncFuel F stdVecEndFunc [.stdVecOwned b len cap] =
      stdVecEndFwd len := by
  have hb : bindMemArgs stdVecEndFunc.args [.stdVecOwned b len cap]
      emptyMem =
      some ([("t", .stdVecOwned b len cap)],
        (tripleMem b len cap),
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned }]
      [.stdVecOwned b len cap] emptyMem = _
    exact bindMemArgs_stdVecEnd b len cap
  have hbody : stdVecEndFunc.body = .return_ (.vgrowLen "t") := rfl
  have ht := envLookup_stdVecEnd_t b len cap
  have hlen : evalExpr (.vgrowLen "t") [("t", .stdVecOwned b len cap)] =
      .ok (.u64 (BitVec.ofNat 64 len)) :=
    evalExpr_vgrowLen_some "t" _ b len cap ht
  have hlay : layoutLookup [("t", 0, 0)] "t" = some (0, 0) := by
    simp [layoutLookup]
  have hmem : memLoad
      (tripleMem b len cap)
      0 0 0 = .ok (BitVec.ofNat 32 len) := by
    simp [tripleMem, memLoad, memFind, hlive]
  have hagree := memEvalExpr_vgrowLen_hit "t" _ _ _ b len cap 0 0
    hlay ht hmem
  have hret := memEvalStmtFuel_return F (.vgrowLen "t") _ _ _ _
    hagree hlen
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  simp [stdVecEndFwd]

/-- Transfer for `end`. -/
theorem memTransfer_stdVecEnd (F : Nat) (b : Vec32) (len cap : Nat)
    (hlive : b.freed = false)
    (_h : oracleNoalias stdVecEndFunc [.stdVecOwned b len cap]) :
    memEvalFuncFuel F stdVecEndFunc [.stdVecOwned b len cap] =
      evalFuncFuel F stdVecEndFunc [.stdVecOwned b len cap] := by
  rw [memEvalFuncFuel_stdVecEnd F b len cap hlive,
    evalFuncFuel_stdVecEnd F b len cap]

/-- `memEval` for `capacity` (liveness as in `end`: the header read
    needs a live block; the capacity word sits at header index `1`). -/
theorem memEvalFuncFuel_stdVecGrowCapacity (F : Nat) (b : Vec32)
    (len cap : Nat) (hlive : b.freed = false) :
    memEvalFuncFuel F stdVecGrowCapacityFunc [.stdVecOwned b len cap] =
      stdVecGrowCapacityFwd cap := by
  have hb : bindMemArgs stdVecGrowCapacityFunc.args [.stdVecOwned b len cap]
      emptyMem =
      some ([("t", .stdVecOwned b len cap)],
        (tripleMem b len cap),
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned }]
      [.stdVecOwned b len cap] emptyMem = _
    exact bindMemArgs_stdVecGrowCapacity b len cap
  have hbody : stdVecGrowCapacityFunc.body = .return_ (.vgrowCap "t") := rfl
  have ht := envLookup_stdVecGrowCapacity_t b len cap
  have hcap : evalExpr (.vgrowCap "t") [("t", .stdVecOwned b len cap)] =
      .ok (.u64 (BitVec.ofNat 64 cap)) :=
    evalExpr_vgrowCap_some "t" _ b len cap ht
  have hlay : layoutLookup [("t", 0, 0)] "t" = some (0, 0) := by
    simp [layoutLookup]
  have hmem : memLoad
      (tripleMem b len cap)
      0 0 1 = .ok (BitVec.ofNat 32 cap) := by
    simp [tripleMem, memLoad, memFind, hlive]
  have hagree := memEvalExpr_vgrowCap_hit "t" _ _ _ b len cap 0 0
    hlay ht hmem
  have hret := memEvalStmtFuel_return F (.vgrowCap "t") _ _ _ _
    hagree hcap
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  simp [stdVecGrowCapacityFwd]

/-- Transfer for `capacity`. -/
theorem memTransfer_stdVecGrowCapacity (F : Nat) (b : Vec32) (len cap : Nat)
    (hlive : b.freed = false)
    (_h : oracleNoalias stdVecGrowCapacityFunc [.stdVecOwned b len cap]) :
    memEvalFuncFuel F stdVecGrowCapacityFunc [.stdVecOwned b len cap] =
      evalFuncFuel F stdVecGrowCapacityFunc [.stdVecOwned b len cap] := by
  rw [memEvalFuncFuel_stdVecGrowCapacity F b len cap hlive,
    evalFuncFuel_stdVecGrowCapacity F b len cap]

/-- `memEval` for `back` (liveness as in `end`: the header read
    needs a live block). -/
theorem memEvalFuncFuel_stdVecBack (F : Nat) (b : Vec32)
    (len cap : Nat) (hlive : b.freed = false) :
    memEvalFuncFuel F stdVecBackFunc [.stdVecOwned b len cap] =
      stdVecBackFwd len := by
  have hb : bindMemArgs stdVecBackFunc.args [.stdVecOwned b len cap]
      emptyMem =
      some ([("t", .stdVecOwned b len cap)],
        (tripleMem b len cap),
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned }]
      [.stdVecOwned b len cap] emptyMem = _
    exact bindMemArgs_stdVecBack b len cap
  have hbody : stdVecBackFunc.body =
      .return_ (.usub (.vgrowLen "t") (.lit (.u64 (BitVec.ofNat 64 1)))) :=
    rfl
  have ht := envLookup_stdVecBack_t b len cap
  have hlen : evalExpr (.vgrowLen "t") [("t", .stdVecOwned b len cap)] =
      .ok (.u64 (BitVec.ofNat 64 len)) :=
    evalExpr_vgrowLen_some "t" _ b len cap ht
  have hback : evalExpr
      (.usub (.vgrowLen "t") (.lit (.u64 (BitVec.ofNat 64 1))))
      [("t", .stdVecOwned b len cap)] =
      .ok (.u64 (BitVec.ofNat 64 len - 1)) :=
    evalExpr_u64_usub _ _ _ _ hlen
  have hlay : layoutLookup [("t", 0, 0)] "t" = some (0, 0) := by
    simp [layoutLookup]
  have hmem : memLoad
      (tripleMem b len cap)
      0 0 0 = .ok (BitVec.ofNat 32 len) := by
    simp [tripleMem, memLoad, memFind, hlive]
  have hmlen := memEvalExpr_vgrowLen_hit "t" _ _ _ b len cap 0 0
    hlay ht hmem
  have hlit : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      [("t", .stdVecOwned b len cap)]
      (tripleMem b len cap)
      [("t", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        [("t", .stdVecOwned b len cap)] :=
    memEvalExpr_lit _ _ _ _
  have hagree := memEvalExpr_usub_agree (.vgrowLen "t")
    (.lit (.u64 (BitVec.ofNat 64 1))) _ _ _ hmlen hlit
  have hret := memEvalStmtFuel_return F
    (.usub (.vgrowLen "t") (.lit (.u64 (BitVec.ofNat 64 1)))) _ _ _ _
    hagree hback
  simp only [memEvalFuncFuel, hb, hbody]
  rw [hret]
  simp [stdVecBackFwd]

/-- Transfer for `back`. -/
theorem memTransfer_stdVecBack (F : Nat) (b : Vec32) (len cap : Nat)
    (hlive : b.freed = false)
    (_h : oracleNoalias stdVecBackFunc [.stdVecOwned b len cap]) :
    memEvalFuncFuel F stdVecBackFunc [.stdVecOwned b len cap] =
      evalFuncFuel F stdVecBackFunc [.stdVecOwned b len cap] := by
  rw [memEvalFuncFuel_stdVecBack F b len cap hlive,
    evalFuncFuel_stdVecBack F b len cap]

/-- `memEval` for `max` (both branch polarities). -/
theorem memEvalFuncFuel_stdVecMax (F : Nat) (a b : BitVec 64) :
    memEvalFuncFuel F stdVecMaxFunc [.u64 a, .u64 b] =
      stdVecMaxFwd a b := by
  have hb : bindMemArgs stdVecMaxFunc.args [.u64 a, .u64 b] emptyMem =
      some ([("a", .u64 a), ("b", .u64 b)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "a", ty := .u 64, role := .owned },
       { name := "b", ty := .u 64, role := .owned }]
      [.u64 a, .u64 b] emptyMem = _
    exact bindMemArgs_stdVecMax a b
  have hbody : stdVecMaxFunc.body =
      .if_ (.ult (.var "a") (.var "b"))
        (.return_ (.var "b"))
        (.return_ (.var "a")) := rfl
  have ha := envLookup_stdVecMax_a a b
  have hbb := envLookup_stdVecMax_b a b
  have hva : evalExpr (.var "a") [("a", .u64 a), ("b", .u64 b)] =
      .ok (.u64 a) := by
    simp [evalExpr, ha]
  have hvb : evalExpr (.var "b") [("a", .u64 a), ("b", .u64 b)] =
      .ok (.u64 b) := by
    simp [evalExpr, hbb]
  have hma : memEvalExpr (.var "a") [("a", .u64 a), ("b", .u64 b)]
      emptyMem [] = evalExpr (.var "a") [("a", .u64 a), ("b", .u64 b)] :=
    memEvalExpr_var _ _ _ _
  have hmb : memEvalExpr (.var "b") [("a", .u64 a), ("b", .u64 b)]
      emptyMem [] = evalExpr (.var "b") [("a", .u64 a), ("b", .u64 b)] :=
    memEvalExpr_var _ _ _ _
  have hcond : evalExpr (.ult (.var "a") (.var "b"))
      [("a", .u64 a), ("b", .u64 b)] = .ok (.b (a.ult b)) := by
    simp [evalExpr, ha, hbb]
  have hmcond := memEvalExpr_ult_agree (.var "a") (.var "b") _ _ _ hma hmb
  by_cases h : a.ult b
  · have hc : memEvalExpr (.ult (.var "a") (.var "b"))
        [("a", .u64 a), ("b", .u64 b)] emptyMem [] = .ok (.b true) := by
      rw [hmcond]
      simp [hcond, h]
    have hmax : stdVecMaxFwd a b = .ok (.u64 b) := by
      simp [stdVecMaxFwd, h]
    have hret := memEvalStmtFuel_return F (.var "b") _ _ _ _
      hmb hvb
    have hstmt : memEvalStmtFuel F stdVecMaxFunc.body
        [("a", .u64 a), ("b", .u64 b)] emptyMem [] =
        .ok ((([("a", .u64 a), ("b", .u64 b)], emptyMem, [])),
          .returned (.u64 b)) := by
      rw [hbody, memEvalStmtFuel_if_true F _ _ _ _ _ _ hc]
      exact hret
    simp only [memEvalFuncFuel, hb, hstmt]
    simp [hmax]
  · have hc : memEvalExpr (.ult (.var "a") (.var "b"))
        [("a", .u64 a), ("b", .u64 b)] emptyMem [] = .ok (.b false) := by
      rw [hmcond]
      simp [hcond, h]
    have hmax : stdVecMaxFwd a b = .ok (.u64 a) := by
      simp [stdVecMaxFwd, h]
    have hret := memEvalStmtFuel_return F (.var "a") _ _ _ _
      hma hva
    have hstmt : memEvalStmtFuel F stdVecMaxFunc.body
        [("a", .u64 a), ("b", .u64 b)] emptyMem [] =
        .ok ((([("a", .u64 a), ("b", .u64 b)], emptyMem, [])),
          .returned (.u64 a)) := by
      rw [hbody, memEvalStmtFuel_if_false F _ _ _ _ _ _ hc]
      exact hret
    simp only [memEvalFuncFuel, hb, hstmt]
    simp [hmax]

/-- Transfer for `max`. -/
theorem memTransfer_stdVecMax (F : Nat) (a b : BitVec 64)
    (_h : oracleNoalias stdVecMaxFunc [.u64 a, .u64 b]) :
    memEvalFuncFuel F stdVecMaxFunc [.u64 a, .u64 b] =
      evalFuncFuel F stdVecMaxFunc [.u64 a, .u64 b] := by
  rw [memEvalFuncFuel_stdVecMax F a b, evalFuncFuel_stdVecMax F a b]

/-- `memEval` for `min` (both branch polarities). -/
theorem memEvalFuncFuel_stdVecMin (F : Nat) (a b : BitVec 64) :
    memEvalFuncFuel F stdVecMinFunc [.u64 a, .u64 b] =
      stdVecMinFwd a b := by
  have hb : bindMemArgs stdVecMinFunc.args [.u64 a, .u64 b] emptyMem =
      some ([("a", .u64 a), ("b", .u64 b)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "a", ty := .u 64, role := .owned },
       { name := "b", ty := .u 64, role := .owned }]
      [.u64 a, .u64 b] emptyMem = _
    exact bindMemArgs_stdVecMin a b
  have hbody : stdVecMinFunc.body =
      .if_ (.ult (.var "b") (.var "a"))
        (.return_ (.var "b"))
        (.return_ (.var "a")) := rfl
  have ha := envLookup_stdVecMax_a a b
  have hbb := envLookup_stdVecMax_b a b
  have hva : evalExpr (.var "a") [("a", .u64 a), ("b", .u64 b)] =
      .ok (.u64 a) := by
    simp [evalExpr, ha]
  have hvb : evalExpr (.var "b") [("a", .u64 a), ("b", .u64 b)] =
      .ok (.u64 b) := by
    simp [evalExpr, hbb]
  have hma : memEvalExpr (.var "a") [("a", .u64 a), ("b", .u64 b)]
      emptyMem [] = evalExpr (.var "a") [("a", .u64 a), ("b", .u64 b)] :=
    memEvalExpr_var _ _ _ _
  have hmb : memEvalExpr (.var "b") [("a", .u64 a), ("b", .u64 b)]
      emptyMem [] = evalExpr (.var "b") [("a", .u64 a), ("b", .u64 b)] :=
    memEvalExpr_var _ _ _ _
  have hcond : evalExpr (.ult (.var "b") (.var "a"))
      [("a", .u64 a), ("b", .u64 b)] = .ok (.b (b.ult a)) := by
    simp [evalExpr, ha, hbb]
  have hmcond := memEvalExpr_ult_agree (.var "b") (.var "a") _ _ _ hmb hma
  by_cases h : b.ult a
  · have hc : memEvalExpr (.ult (.var "b") (.var "a"))
        [("a", .u64 a), ("b", .u64 b)] emptyMem [] = .ok (.b true) := by
      rw [hmcond]
      simp [hcond, h]
    have hmin : stdVecMinFwd a b = .ok (.u64 b) := by
      simp [stdVecMinFwd, h]
    have hret := memEvalStmtFuel_return F (.var "b") _ _ _ _
      hmb hvb
    have hstmt : memEvalStmtFuel F stdVecMinFunc.body
        [("a", .u64 a), ("b", .u64 b)] emptyMem [] =
        .ok ((([("a", .u64 a), ("b", .u64 b)], emptyMem, [])),
          .returned (.u64 b)) := by
      rw [hbody, memEvalStmtFuel_if_true F _ _ _ _ _ _ hc]
      exact hret
    simp only [memEvalFuncFuel, hb, hstmt]
    simp [hmin]
  · have hc : memEvalExpr (.ult (.var "b") (.var "a"))
        [("a", .u64 a), ("b", .u64 b)] emptyMem [] = .ok (.b false) := by
      rw [hmcond]
      simp [hcond, h]
    have hmin : stdVecMinFwd a b = .ok (.u64 a) := by
      simp [stdVecMinFwd, h]
    have hret := memEvalStmtFuel_return F (.var "a") _ _ _ _
      hma hva
    have hstmt : memEvalStmtFuel F stdVecMinFunc.body
        [("a", .u64 a), ("b", .u64 b)] emptyMem [] =
        .ok ((([("a", .u64 a), ("b", .u64 b)], emptyMem, [])),
          .returned (.u64 a)) := by
      rw [hbody, memEvalStmtFuel_if_false F _ _ _ _ _ _ hc]
      exact hret
    simp only [memEvalFuncFuel, hb, hstmt]
    simp [hmin]

/-- Transfer for `min`. -/
theorem memTransfer_stdVecMin (F : Nat) (a b : BitVec 64)
    (_h : oracleNoalias stdVecMinFunc [.u64 a, .u64 b]) :
    memEvalFuncFuel F stdVecMinFunc [.u64 a, .u64 b] =
      evalFuncFuel F stdVecMinFunc [.u64 a, .u64 b] := by
  rw [memEvalFuncFuel_stdVecMin F a b, evalFuncFuel_stdVecMin F a b]

/-! ## N4d-iv-b1 growth leaves: mutating-leaf transfer -/

/-- `memEval` for the destructor: the capacity header read agrees on
    a live triple, then the consume runs in lockstep (the `vecFree`
    error path is vacuous on live input). -/
theorem memEvalFuncFuel_stdVecDtor (F : Nat) (b : Vec32) (len cap : Nat)
    (hcap64 : cap < 2 ^ 64) (hlive : b.freed = false) :
    memEvalFuncFuel F stdVecDtorFunc [.stdVecOwned b len cap] =
      stdVecDtorFwd b len cap := by
  have hb : bindMemArgs stdVecDtorFunc.args [.stdVecOwned b len cap]
      emptyMem =
      some ([("t", .stdVecOwned b len cap)],
        (tripleMem b len cap),
        [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned }]
      [.stdVecOwned b len cap] emptyMem = _
    exact bindMemArgs_stdVecDtor b len cap
  have hbody : stdVecDtorFunc.body =
      .if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.vgrowCap "t"))
        (.seq (.vgrowFree "t") (.return_ (.var "t")))
        (.return_ (.var "t")) := rfl
  have ht := envLookup_stdVecDtor_t b len cap
  have hlay : layoutLookup [("t", 0, 0)] "t" = some (0, 0) := by
    simp [layoutLookup]
  have hmemCap : memLoad
      (tripleMem b len cap)
      0 0 1 = .ok (BitVec.ofNat 32 cap) := by
    simp [tripleMem, memLoad, memFind, hlive]
  have hmcap := memEvalExpr_vgrowCap_hit "t" _ _ _ b len cap 0 0
    hlay ht hmemCap
  have hlit : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("t", .stdVecOwned b len cap)]
      (tripleMem b len cap)
      [("t", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("t", .stdVecOwned b len cap)] :=
    memEvalExpr_lit _ _ _ _
  have hmcond := memEvalExpr_ult_agree
    (.lit (.u64 (BitVec.ofNat 64 0))) (.vgrowCap "t") _ _ _ hlit hmcap
  have hcapv : evalExpr (.vgrowCap "t")
      [("t", .stdVecOwned b len cap)] =
      .ok (.u64 (BitVec.ofNat 64 cap)) :=
    evalExpr_vgrowCap_some "t" _ b len cap ht
  have hcond : evalExpr
      (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.vgrowCap "t"))
      [("t", .stdVecOwned b len cap)] =
      .ok (.b (decide (0 < cap))) := by
    simp [evalExpr, litVal, ht, hcapv, BitVec.ult_eq_decide,
      ofNat64_toNat cap hcap64]
  by_cases hlt : 0 < cap
  · have hc : memEvalExpr
        (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.vgrowCap "t"))
        [("t", .stdVecOwned b len cap)] (tripleMem b len cap)
          [("t", 0, 0)] = .ok (.b true) := by
      rw [hmcond]
      simp [hcond, hlt]
    cases hfb : vecFree b with
    | error e =>
      rw [vecFree_ok b hlive] at hfb
      cases hfb
    | ok b' =>
      have hfree : vecFree b = .ok b' := hfb
      have hfind : memFind (tripleMem b len cap) 0 =
          some ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
            (BitVec.ofNat 32 cap) :: b.val⟩ := by
        show memFind ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩ 0 = _
        simp [memFind]
      have hmfree : memFree (tripleMem b len cap) 0 0 =
          .ok (tripleMemFreed b len cap) := by
        simp only [memFree, hfind, hlive]
        rfl
      have hup : envUpdate [("t", .stdVecOwned b len cap)] "t"
          (.stdVecOwned b' len cap) =
          some [("t", .stdVecOwned b' len cap)] := by
        simp [envUpdate]
      have hret : envLookup [("t", .stdVecOwned b' len cap)] "t" =
          some (.stdVecOwned b' len cap) := by
        simp [envLookup]
      have hvar : evalExpr (.var "t") [("t", .stdVecOwned b' len cap)] =
          .ok (.stdVecOwned b' len cap) := by
        simp [evalExpr, hret]
      have hmvar : memEvalExpr (.var "t")
          [("t", .stdVecOwned b' len cap)] (tripleMemFreed b len cap)
          [("t", 0, 0)] =
          evalExpr (.var "t") [("t", .stdVecOwned b' len cap)] :=
        memEvalExpr_var _ _ _ _
      have hmret := memEvalStmtFuel_return F (.var "t") _ _ _ _
        hmvar hvar
      have hstep : memEvalStmtFuel F (.vgrowFree "t")
          [("t", .stdVecOwned b len cap)] (tripleMem b len cap)
          [("t", 0, 0)] =
          .ok ((([("t", .stdVecOwned b' len cap)],
            (tripleMemFreed b len cap), [("t", 0, 0)])),
            .fellThrough) :=
        memEvalStmtFuel_vgrowFree F "t" _ _ _ 0 0 b b'
          len cap _ _ ht hlay hfree hmfree hup
      have hdtor : stdVecDtorFwd b len cap =
          .ok (.stdVecOwned b' len cap) := by
        simp [stdVecDtorFwd, hlt, hfb]
      have hstmt : memEvalStmtFuel F stdVecDtorFunc.body
          [("t", .stdVecOwned b len cap)]
          (tripleMem b len cap)
          [("t", 0, 0)] =
          .ok ((([("t", .stdVecOwned b' len cap)],
            (tripleMemFreed b len cap),
            [("t", 0, 0)])),
            .returned (.stdVecOwned b' len cap)) := by
        rw [hbody, memEvalStmtFuel_if_true F _ _ _ _ _ _ hc]
        exact (memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _
          hstep).trans hmret
      simp only [memEvalFuncFuel, hb, hstmt, hdtor]
  · have hc : memEvalExpr
        (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.vgrowCap "t"))
        [("t", .stdVecOwned b len cap)] (tripleMem b len cap)
          [("t", 0, 0)] = .ok (.b false) := by
      rw [hmcond]
      simp [hcond, hlt]
    have hvar0 : evalExpr (.var "t") [("t", .stdVecOwned b len cap)] =
        .ok (.stdVecOwned b len cap) := by
      simp [evalExpr, ht]
    have hmvar0 : memEvalExpr (.var "t")
        [("t", .stdVecOwned b len cap)] (tripleMem b len cap)
        [("t", 0, 0)] =
        evalExpr (.var "t") [("t", .stdVecOwned b len cap)] :=
      memEvalExpr_var _ _ _ _
    have hmret0 := memEvalStmtFuel_return F (.var "t") _ _ _ _
      hmvar0 hvar0
    have hskip : stdVecDtorFwd b len cap =
        .ok (.stdVecOwned b len cap) := by
      simp [stdVecDtorFwd, hlt]
    have hstmt : memEvalStmtFuel F stdVecDtorFunc.body
        [("t", .stdVecOwned b len cap)]
        (tripleMem b len cap)
        [("t", 0, 0)] =
        .ok ((([("t", .stdVecOwned b len cap)],
          (tripleMem b len cap),
          [("t", 0, 0)])),
          .returned (.stdVecOwned b len cap)) := by
      rw [hbody, memEvalStmtFuel_if_false F _ _ _ _ _ _ hc]
      exact hmret0
    simp only [memEvalFuncFuel, hb, hstmt, hskip]

/-- Transfer for the destructor. -/
theorem memTransfer_stdVecDtor (F : Nat) (b : Vec32) (len cap : Nat)
    (hcap64 : cap < 2 ^ 64) (hlive : b.freed = false)
    (_h : oracleNoalias stdVecDtorFunc [.stdVecOwned b len cap]) :
    memEvalFuncFuel F stdVecDtorFunc [.stdVecOwned b len cap] =
      evalFuncFuel F stdVecDtorFunc [.stdVecOwned b len cap] := by
  rw [memEvalFuncFuel_stdVecDtor F b len cap hcap64 hlive,
    evalFuncFuel_stdVecDtor F b len cap hcap64]

/-- `memEval` for `_M_allocate` (no triple reads: the request word is
    owned and `vgrowNew` runs purely on both sides). -/
theorem memEvalFuncFuel_stdVecAlloc (F : Nat) (n : BitVec 64) :
    memEvalFuncFuel F stdVecAllocFunc [.u64 n] = stdVecAllocFwd n := by
  have hb : bindMemArgs stdVecAllocFunc.args [.u64 n] emptyMem =
      some ([("n", .u64 n)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "n", ty := .u 64, role := .owned }]
      [.u64 n] emptyMem = _
    exact bindMemArgs_stdVecAlloc n
  have hbody : stdVecAllocFunc.body =
      .if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "n"))
        (.if_ (.ult (.lit (.u64 stdVecMaxDiffBV)) (.var "n"))
          .fail
          (.return_ (.vgrowNew (.var "n"))))
        (.return_ (.vgrowNew (.lit (.u64 (BitVec.ofNat 64 0))))) := rfl
  have hn := envLookup_stdVecAlloc_n n
  have hnv : evalExpr (.var "n") [("n", .u64 n)] = .ok (.u64 n) := by
    simp [evalExpr, hn]
  have hmnv : memEvalExpr (.var "n") [("n", .u64 n)] emptyMem [] =
      evalExpr (.var "n") [("n", .u64 n)] :=
    memEvalExpr_var _ _ _ _
  have hlit0 : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("n", .u64 n)] emptyMem [] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0))) [("n", .u64 n)] :=
    memEvalExpr_lit _ _ _ _
  have hlitD : memEvalExpr (.lit (.u64 stdVecMaxDiffBV))
      [("n", .u64 n)] emptyMem [] =
      evalExpr (.lit (.u64 stdVecMaxDiffBV)) [("n", .u64 n)] :=
    memEvalExpr_lit _ _ _ _
  have hmzc := memEvalExpr_ult_agree
    (.lit (.u64 (BitVec.ofNat 64 0))) (.var "n") _ _ _ hlit0 hmnv
  have hmom := memEvalExpr_ult_agree
    (.lit (.u64 stdVecMaxDiffBV)) (.var "n") _ _ _ hlitD hmnv
  have hzc : evalExpr
      (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "n"))
      [("n", .u64 n)] =
      .ok (.b ((BitVec.ofNat 64 0).ult n)) :=
    evalExpr_ult_u64lit _ _ _ _ hnv
  have hom : evalExpr
      (.ult (.lit (.u64 stdVecMaxDiffBV)) (.var "n"))
      [("n", .u64 n)] =
      .ok (.b (stdVecMaxDiffBV.ult n)) :=
    evalExpr_ult_u64lit _ _ _ _ hnv
  by_cases hz : (BitVec.ofNat 64 0).ult n
  · have hc : memEvalExpr
        (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "n"))
        [("n", .u64 n)] emptyMem [] = .ok (.b true) := by
      rw [hmzc]
      simp [hzc, hz]
    by_cases hm : stdVecMaxDiffBV.ult n
    · have hcm : memEvalExpr
          (.ult (.lit (.u64 stdVecMaxDiffBV)) (.var "n"))
          [("n", .u64 n)] emptyMem [] = .ok (.b true) := by
        rw [hmom]
        simp [hom, hm]
      have hfwd : stdVecAllocFwd n = .error .AssertFail := by
        simp [stdVecAllocFwd, hz, hm]
      have hfail : memEvalStmtFuel F .fail [("n", .u64 n)] emptyMem [] =
          .error .AssertFail :=
        memEvalStmtFuel_fail F _ _ _
      have hstmt : memEvalStmtFuel F stdVecAllocFunc.body
          [("n", .u64 n)] emptyMem [] = .error .AssertFail := by
        rw [hbody, memEvalStmtFuel_if_true F _ _ _ _ _ _ hc,
          memEvalStmtFuel_if_true F _ _ _ _ _ _ hcm]
        exact hfail
      simp only [memEvalFuncFuel, hb, hstmt, hfwd]
    · have hcm : memEvalExpr
          (.ult (.lit (.u64 stdVecMaxDiffBV)) (.var "n"))
          [("n", .u64 n)] emptyMem [] = .ok (.b false) := by
        rw [hmom]
        simp [hom, hm]
      have hnew : evalExpr (.vgrowNew (.var "n")) [("n", .u64 n)] =
          .ok (.stdVecOwned ⟨List.replicate n.toNat 0, false⟩ 0
            n.toNat) :=
        evalExpr_vgrowNew_u64 _ _ _ hnv
      have hmnew := memEvalExpr_vgrowNew_agree (.var "n") _ _ _ hmnv
      have hmret := memEvalStmtFuel_return F (.vgrowNew (.var "n"))
        _ _ _ _ hmnew hnew
      have hfwd : stdVecAllocFwd n =
          .ok (.stdVecOwned ⟨List.replicate n.toNat 0, false⟩ 0
            n.toNat) := by
        simp [stdVecAllocFwd, hz, hm]
      have hstmt : memEvalStmtFuel F stdVecAllocFunc.body
          [("n", .u64 n)] emptyMem [] =
          .ok ((([("n", .u64 n)], emptyMem, [])),
            .returned (.stdVecOwned ⟨List.replicate n.toNat 0, false⟩
              0 n.toNat)) := by
        rw [hbody, memEvalStmtFuel_if_true F _ _ _ _ _ _ hc,
          memEvalStmtFuel_if_false F _ _ _ _ _ _ hcm]
        exact hmret
      simp only [memEvalFuncFuel, hb, hstmt, hfwd]
  · have hcf : memEvalExpr
        (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "n"))
        [("n", .u64 n)] emptyMem [] = .ok (.b false) := by
      rw [hmzc]
      simp [hzc, hz]
    have hempty : evalExpr
        (.vgrowNew (.lit (.u64 (BitVec.ofNat 64 0)))) [("n", .u64 n)] =
        .ok (.stdVecOwned
          ⟨List.replicate (BitVec.ofNat 64 0).toNat 0, false⟩ 0
          (BitVec.ofNat 64 0).toNat) :=
      evalExpr_vgrowNew_lit _ _
    have hlit0e : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("n", .u64 n)] emptyMem [] =
        evalExpr (.lit (.u64 (BitVec.ofNat 64 0))) [("n", .u64 n)] :=
      memEvalExpr_lit _ _ _ _
    have hempty_mem := memEvalExpr_vgrowNew_agree
      (.lit (.u64 (BitVec.ofNat 64 0))) _ _ _ hlit0e
    have hmret := memEvalStmtFuel_return F
      (.vgrowNew (.lit (.u64 (BitVec.ofNat 64 0)))) _ _ _ _
      hempty_mem hempty
    have hfwd : stdVecAllocFwd n =
        .ok (.stdVecOwned
          ⟨List.replicate (BitVec.ofNat 64 0).toNat 0, false⟩ 0
          (BitVec.ofNat 64 0).toNat) := by
      simp [stdVecAllocFwd, hz]
    have hstmt : memEvalStmtFuel F stdVecAllocFunc.body
        [("n", .u64 n)] emptyMem [] =
        .ok ((([("n", .u64 n)], emptyMem, [])),
          .returned (.stdVecOwned
            ⟨List.replicate (BitVec.ofNat 64 0).toNat 0, false⟩ 0
            (BitVec.ofNat 64 0).toNat)) := by
      rw [hbody, memEvalStmtFuel_if_false F _ _ _ _ _ _ hcf]
      exact hmret
    simp only [memEvalFuncFuel, hb, hstmt, hfwd]

/-- Transfer for `_M_allocate`. -/
theorem memTransfer_stdVecAlloc (F : Nat) (n : BitVec 64)
    (_h : oracleNoalias stdVecAllocFunc [.u64 n]) :
    memEvalFuncFuel F stdVecAllocFunc [.u64 n] =
      evalFuncFuel F stdVecAllocFunc [.u64 n] := by
  rw [memEvalFuncFuel_stdVecAlloc F n, evalFuncFuel_stdVecAlloc F n]

/-- `memEval` for the unconditional consume: the error path needs no
    memory touch (value and memory `vecFree` agree first), the ok path
    runs the free in lockstep. -/
theorem memEvalFuncFuel_stdVecDealloc (F : Nat) (b : Vec32)
    (len cap : Nat) :
    memEvalFuncFuel F stdVecDeallocFunc [.stdVecOwned b len cap] =
      stdVecDeallocFwd b len cap := by
  have hb : bindMemArgs stdVecDeallocFunc.args [.stdVecOwned b len cap]
      emptyMem =
      some ([("t", .stdVecOwned b len cap)],
        (tripleMem b len cap), [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned }]
      [.stdVecOwned b len cap] emptyMem = _
    exact bindMemArgs_stdVecDealloc b len cap
  have hbody : stdVecDeallocFunc.body =
      .seq (.vgrowFree "t") (.return_ (.var "t")) := rfl
  have ht := envLookup_stdVecDealloc_t b len cap
  have hlay : layoutLookup [("t", 0, 0)] "t" = some (0, 0) := by
    simp [layoutLookup]
  cases hfb : vecFree b with
  | error e =>
    have hfwd : stdVecDeallocFwd b len cap = .error e := by
      simp [stdVecDeallocFwd, hfb]
    have herr : memEvalStmtFuel F (.vgrowFree "t")
        [("t", .stdVecOwned b len cap)] (tripleMem b len cap)
        [("t", 0, 0)] = .error e := by
      have hmemerr : memEvalStmtFuel F (.vgrowFree "t")
          [("t", .stdVecOwned b len cap)] (tripleMem b len cap)
          [("t", 0, 0)] = .error e :=
        memEvalStmtFuel_vgrowFree_err F "t" _ _ _
          0 0 b len cap e ht hlay hfb
      exact hmemerr
    have hstmt : memEvalStmtFuel F stdVecDeallocFunc.body
        [("t", .stdVecOwned b len cap)] (tripleMem b len cap)
        [("t", 0, 0)] = .error e := by
      rw [hbody]
      exact memEvalStmtFuel_seq_err F _ _ _ _ _ _ herr
    simp only [memEvalFuncFuel, hb, hstmt, hfwd]
  | ok b' =>
    have hlive : b.freed = false := by
      cases hf : b.freed with
      | true =>
        rw [vecFree_double b hf] at hfb
        cases hfb
      | false => rfl
    have hfind : memFind (tripleMem b len cap) 0 =
        some ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩ := by
      show memFind ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
        (BitVec.ofNat 32 cap) :: b.val⟩),
        (0, ⟨0, true, (BitVec.ofNat 32 len) ::
        (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩ 0 = _
      simp [memFind]
    have hmfree : memFree (tripleMem b len cap) 0 0 =
        .ok (tripleMemFreed b len cap) := by
      simp only [memFree, hfind, hlive]
      rfl
    have hup : envUpdate [("t", .stdVecOwned b len cap)] "t"
        (.stdVecOwned b' len cap) =
        some [("t", .stdVecOwned b' len cap)] := by
      simp [envUpdate]
    have hret : envLookup [("t", .stdVecOwned b' len cap)] "t" =
        some (.stdVecOwned b' len cap) := by
      simp [envLookup]
    have hvar : evalExpr (.var "t")
        [("t", .stdVecOwned b' len cap)] =
        .ok (.stdVecOwned b' len cap) := by
      simp [evalExpr, hret]
    have hmvar : memEvalExpr (.var "t")
        [("t", .stdVecOwned b' len cap)] (tripleMemFreed b len cap)
        [("t", 0, 0)] =
        evalExpr (.var "t") [("t", .stdVecOwned b' len cap)] :=
      memEvalExpr_var _ _ _ _
    have hmret := memEvalStmtFuel_return F (.var "t") _ _ _ _
      hmvar hvar
    have hstep : memEvalStmtFuel F (.vgrowFree "t")
        [("t", .stdVecOwned b len cap)] (tripleMem b len cap)
        [("t", 0, 0)] =
        .ok ((([("t", .stdVecOwned b' len cap)],
          (tripleMemFreed b len cap), [("t", 0, 0)])),
          .fellThrough) :=
      memEvalStmtFuel_vgrowFree F "t" _ _ _ 0 0 b b'
        len cap _ _ ht hlay hfb hmfree hup
    have hfwd : stdVecDeallocFwd b len cap =
        .ok (.stdVecOwned b' len cap) := by
      simp [stdVecDeallocFwd, hfb]
    have hstmt : memEvalStmtFuel F stdVecDeallocFunc.body
        [("t", .stdVecOwned b len cap)] (tripleMem b len cap)
        [("t", 0, 0)] =
        .ok ((([("t", .stdVecOwned b' len cap)],
          (tripleMemFreed b len cap), [("t", 0, 0)])),
          .returned (.stdVecOwned b' len cap)) := by
      rw [hbody]
      exact (memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _
        hstep).trans hmret
    simp only [memEvalFuncFuel, hb, hstmt, hfwd]

/-- Transfer for the unconditional consume. -/
theorem memTransfer_stdVecDealloc (F : Nat) (b : Vec32) (len cap : Nat)
    (_h : oracleNoalias stdVecDeallocFunc [.stdVecOwned b len cap]) :
    memEvalFuncFuel F stdVecDeallocFunc [.stdVecOwned b len cap] =
      evalFuncFuel F stdVecDeallocFunc [.stdVecOwned b len cap] := by
  rw [memEvalFuncFuel_stdVecDealloc F b len cap,
    evalFuncFuel_stdVecDealloc F b len cap]

/-- `memEval` for `_M_deallocate` (liveness as in `end`: the `n == 0`
    guard reads no memory, but the consume path does). -/
theorem memEvalFuncFuel_stdVecDeallocGuard (F : Nat) (b : Vec32)
    (len cap : Nat) (n : BitVec 64) (hlive : b.freed = false) :
    memEvalFuncFuel F stdVecDeallocGuardFunc
      [.stdVecOwned b len cap, .u64 n] =
      stdVecDeallocGuardFwd b len cap n := by
  have hb : bindMemArgs stdVecDeallocGuardFunc.args
      [.stdVecOwned b len cap, .u64 n] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("n", .u64 n)],
        (tripleMem b len cap), [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "n", ty := .u 64, role := .owned }]
      [.stdVecOwned b len cap, .u64 n] emptyMem = _
    exact bindMemArgs_stdVecDeallocGuard b len cap n
  have hbody : stdVecDeallocGuardFunc.body =
      .if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "n"))
        (.seq (.vgrowFree "t") (.return_ (.var "t")))
        (.return_ (.var "t")) := rfl
  have ht := envLookup_stdVecDeallocGuard_t b len cap n
  have hn := envLookup_stdVecDeallocGuard_n b len cap n
  have hlay : layoutLookup [("t", 0, 0)] "t" = some (0, 0) := by
    simp [layoutLookup]
  have hnv : evalExpr (.var "n")
      [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  have hmnv : memEvalExpr (.var "n")
      [("t", .stdVecOwned b len cap), ("n", .u64 n)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.var "n")
        [("t", .stdVecOwned b len cap), ("n", .u64 n)] :=
    memEvalExpr_var _ _ _ _
  have hlit0 : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      [("t", .stdVecOwned b len cap), ("n", .u64 n)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        [("t", .stdVecOwned b len cap), ("n", .u64 n)] :=
    memEvalExpr_lit _ _ _ _
  have hmcond := memEvalExpr_ult_agree
    (.lit (.u64 (BitVec.ofNat 64 0))) (.var "n") _ _ _ hlit0 hmnv
  have hzc : evalExpr
      (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "n"))
      [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
      .ok (.b ((BitVec.ofNat 64 0).ult n)) :=
    evalExpr_ult_u64lit _ _ _ _ hnv
  by_cases hz : (BitVec.ofNat 64 0).ult n
  · have hc : memEvalExpr
        (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "n"))
        [("t", .stdVecOwned b len cap), ("n", .u64 n)]
        (tripleMem b len cap) [("t", 0, 0)] = .ok (.b true) := by
      rw [hmcond]
      simp [hzc, hz]
    cases hfb : vecFree b with
    | error e =>
      rw [vecFree_ok b hlive] at hfb
      cases hfb
    | ok b' =>
      have hfree : vecFree b = .ok b' := hfb
      have hfind : memFind (tripleMem b len cap) 0 =
          some ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
            (BitVec.ofNat 32 cap) :: b.val⟩ := by
        show memFind ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩),
          (0, ⟨0, true, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩ 0 = _
        simp [memFind]
      have hmfree : memFree (tripleMem b len cap) 0 0 =
          .ok (tripleMemFreed b len cap) := by
        simp only [memFree, hfind, hlive]
        rfl
      have hup : envUpdate [("t", .stdVecOwned b len cap),
          ("n", .u64 n)] "t" (.stdVecOwned b' len cap) =
          some [("t", .stdVecOwned b' len cap), ("n", .u64 n)] := by
        simp [envUpdate]
      have hret : envLookup [("t", .stdVecOwned b' len cap),
          ("n", .u64 n)] "t" =
          some (.stdVecOwned b' len cap) := by
        simp [envLookup]
      have hvar : evalExpr (.var "t")
          [("t", .stdVecOwned b' len cap), ("n", .u64 n)] =
          .ok (.stdVecOwned b' len cap) := by
        simp [evalExpr, hret]
      have hmvar : memEvalExpr (.var "t")
          [("t", .stdVecOwned b' len cap), ("n", .u64 n)]
          (tripleMemFreed b len cap) [("t", 0, 0)] =
          evalExpr (.var "t") [("t", .stdVecOwned b' len cap),
            ("n", .u64 n)] :=
        memEvalExpr_var _ _ _ _
      have hmret := memEvalStmtFuel_return F (.var "t") _ _ _ _
        hmvar hvar
      have hstep : memEvalStmtFuel F (.vgrowFree "t")
          [("t", .stdVecOwned b len cap), ("n", .u64 n)]
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok ((([("t", .stdVecOwned b' len cap), ("n", .u64 n)],
            (tripleMemFreed b len cap), [("t", 0, 0)])),
            .fellThrough) :=
        memEvalStmtFuel_vgrowFree F "t" _ _ _ 0 0 b b'
          len cap _ _ ht hlay hfree hmfree hup
      have hfwd : stdVecDeallocGuardFwd b len cap n =
          .ok (.stdVecOwned b' len cap) := by
        simp [stdVecDeallocGuardFwd, hz, hfb]
      have hstmt : memEvalStmtFuel F stdVecDeallocGuardFunc.body
          [("t", .stdVecOwned b len cap), ("n", .u64 n)]
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok ((([("t", .stdVecOwned b' len cap), ("n", .u64 n)],
            (tripleMemFreed b len cap), [("t", 0, 0)])),
            .returned (.stdVecOwned b' len cap)) := by
        rw [hbody, memEvalStmtFuel_if_true F _ _ _ _ _ _ hc]
        exact (memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _
          hstep).trans hmret
      simp only [memEvalFuncFuel, hb, hstmt, hfwd]
  · have hcf : memEvalExpr
        (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "n"))
        [("t", .stdVecOwned b len cap), ("n", .u64 n)]
        (tripleMem b len cap) [("t", 0, 0)] = .ok (.b false) := by
      rw [hmcond]
      simp [hzc, hz]
    have hvar0 : evalExpr (.var "t")
        [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
        .ok (.stdVecOwned b len cap) := by
      simp [evalExpr, ht]
    have hmvar0 : memEvalExpr (.var "t")
        [("t", .stdVecOwned b len cap), ("n", .u64 n)]
        (tripleMem b len cap) [("t", 0, 0)] =
        evalExpr (.var "t") [("t", .stdVecOwned b len cap),
          ("n", .u64 n)] :=
      memEvalExpr_var _ _ _ _
    have hmret0 := memEvalStmtFuel_return F (.var "t") _ _ _ _
      hmvar0 hvar0
    have hfwd : stdVecDeallocGuardFwd b len cap n =
        .ok (.stdVecOwned b len cap) := by
      simp [stdVecDeallocGuardFwd, hz]
    have hstmt : memEvalStmtFuel F stdVecDeallocGuardFunc.body
        [("t", .stdVecOwned b len cap), ("n", .u64 n)]
        (tripleMem b len cap) [("t", 0, 0)] =
        .ok ((([("t", .stdVecOwned b len cap), ("n", .u64 n)],
          (tripleMem b len cap), [("t", 0, 0)])),
          .returned (.stdVecOwned b len cap)) := by
      rw [hbody, memEvalStmtFuel_if_false F _ _ _ _ _ _ hcf]
      exact hmret0
    simp only [memEvalFuncFuel, hb, hstmt, hfwd]

/-- Transfer for `_M_deallocate`. -/
theorem memTransfer_stdVecDeallocGuard (F : Nat) (b : Vec32)
    (len cap : Nat) (n : BitVec 64) (hlive : b.freed = false)
    (_h : oracleNoalias stdVecDeallocGuardFunc
      [.stdVecOwned b len cap, .u64 n]) :
    memEvalFuncFuel F stdVecDeallocGuardFunc
      [.stdVecOwned b len cap, .u64 n] =
      evalFuncFuel F stdVecDeallocGuardFunc
        [.stdVecOwned b len cap, .u64 n] := by
  rw [memEvalFuncFuel_stdVecDeallocGuard F b len cap n hlive,
    evalFuncFuel_stdVecDeallocGuard F b len cap n]

/-- `memEval` for `construct`: the error path needs no memory touch,
    the ok path stores in lockstep (header-shifted `memStore`). -/
theorem memEvalFuncFuel_stdVecConstruct (F : Nat) (b : Vec32)
    (len cap : Nat) (p : BitVec 64) (x : BitVec 32) :
    memEvalFuncFuel F stdVecConstructFunc
      [.stdVecOwned b len cap, .u64 p, .i32 x] =
      stdVecConstructFwd b len cap p x := by
  have hb : bindMemArgs stdVecConstructFunc.args
      [.stdVecOwned b len cap, .u64 p, .i32 x] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("p", .u64 p),
        ("v", .i32 x)],
        (tripleMem b len cap), [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "p", ty := .u 64, role := .owned },
       { name := "v", ty := .i 32, role := .owned }]
      [.stdVecOwned b len cap, .u64 p, .i32 x] emptyMem = _
    exact bindMemArgs_stdVecConstruct b len cap p x
  have hbody : stdVecConstructFunc.body =
      .seq (.vgrowSet "t" (.var "p") (.var "v"))
        (.return_ (.var "t")) := rfl
  have ht := envLookup_stdVecConstruct_t b len cap p x
  have hp := envLookup_stdVecConstruct_p b len cap p x
  have hv := envLookup_stdVecConstruct_v b len cap p x
  have hlay : layoutLookup [("t", 0, 0)] "t" = some (0, 0) := by
    simp [layoutLookup]
  have hpv : evalExpr (.var "p")
      [("t", .stdVecOwned b len cap), ("p", .u64 p),
        ("v", .i32 x)] =
      .ok (.u64 p) := by
    simp [evalExpr, hp]
  have hvv : evalExpr (.var "v")
      [("t", .stdVecOwned b len cap), ("p", .u64 p),
        ("v", .i32 x)] =
      .ok (.i32 x) := by
    simp [evalExpr, hv]
  have hmpv : memEvalExpr (.var "p")
      [("t", .stdVecOwned b len cap), ("p", .u64 p),
        ("v", .i32 x)] (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.var "p")
        [("t", .stdVecOwned b len cap), ("p", .u64 p),
          ("v", .i32 x)] :=
    memEvalExpr_var _ _ _ _
  have hmv : memEvalExpr (.var "v")
      [("t", .stdVecOwned b len cap), ("p", .u64 p),
        ("v", .i32 x)] (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.var "v")
        [("t", .stdVecOwned b len cap), ("p", .u64 p),
          ("v", .i32 x)] :=
    memEvalExpr_var _ _ _ _
  cases hset : vecSet b p.toNat x with
  | error e =>
    have hfwd : stdVecConstructFwd b len cap p x = .error e := by
      simp [stdVecConstructFwd, hset]
    have herr : memEvalStmtFuel F
        (.vgrowSet "t" (.var "p") (.var "v"))
        [("t", .stdVecOwned b len cap), ("p", .u64 p),
          ("v", .i32 x)] (tripleMem b len cap) [("t", 0, 0)] =
        .error e := by
      have hmemerr : memEvalStmtFuel F
          (.vgrowSet "t" (.var "p") (.var "v"))
          [("t", .stdVecOwned b len cap), ("p", .u64 p),
            ("v", .i32 x)] (tripleMem b len cap)
          [("t", 0, 0)] = .error e :=
        memEvalStmtFuel_vgrowSet_err F "t" (.var "p") (.var "v")
          _ _ _ p x 0 0 b len cap e hmpv hmv ht hlay hset
      exact hmemerr
    have hstmt : memEvalStmtFuel F stdVecConstructFunc.body
        [("t", .stdVecOwned b len cap), ("p", .u64 p),
          ("v", .i32 x)] (tripleMem b len cap) [("t", 0, 0)] =
        .error e := by
      rw [hbody]
      exact memEvalStmtFuel_seq_err F _ _ _ _ _ _ herr
    simp only [memEvalFuncFuel, hb, hstmt, hfwd]
  | ok b' =>
    have hunfreed : b.freed = false := by
      cases hf : b.freed with
      | true =>
        rw [vecSet_freed b _ _ hf] at hset
        cases hset
      | false => rfl
    have hfind : memFind (tripleMem b len cap) 0 =
        some ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
          (BitVec.ofNat 32 cap) :: b.val⟩ := by
      show memFind ⟨1, [(0, ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
        (BitVec.ofNat 32 cap) :: b.val⟩),
        (0, ⟨0, true, (BitVec.ofNat 32 len) ::
        (BitVec.ofNat 32 cap) :: b.val⟩)], []⟩ 0 = _
      simp [memFind]
    obtain ⟨m', hmstore, -⟩ := vgrowSet_lockstep (tripleMem b len cap)
      0 0 b len cap p.toNat x
      ⟨0, !b.freed, (BitVec.ofNat 32 len) ::
        (BitVec.ofNat 32 cap) :: b.val⟩ b'
      hfind rfl (by simp [hunfreed]) rfl hunfreed hset
    have hup : envUpdate [("t", .stdVecOwned b len cap),
        ("p", .u64 p), ("v", .i32 x)] "t"
        (.stdVecOwned b' len cap) =
        some [("t", .stdVecOwned b' len cap), ("p", .u64 p),
          ("v", .i32 x)] := by
      simp [envUpdate]
    have hret : envLookup [("t", .stdVecOwned b' len cap),
        ("p", .u64 p), ("v", .i32 x)] "t" =
        some (.stdVecOwned b' len cap) := by
      simp [envLookup]
    have hvar : evalExpr (.var "t")
        [("t", .stdVecOwned b' len cap), ("p", .u64 p),
          ("v", .i32 x)] =
        .ok (.stdVecOwned b' len cap) := by
      simp [evalExpr, hret]
    have hmvar : memEvalExpr (.var "t")
        [("t", .stdVecOwned b' len cap), ("p", .u64 p),
          ("v", .i32 x)] m' [("t", 0, 0)] =
        evalExpr (.var "t") [("t", .stdVecOwned b' len cap),
          ("p", .u64 p), ("v", .i32 x)] :=
      memEvalExpr_var _ _ _ _
    have hmret := memEvalStmtFuel_return F (.var "t") _ _ _ _
      hmvar hvar
    have hs : memEvalStmtFuel F
        (.vgrowSet "t" (.var "p") (.var "v"))
        [("t", .stdVecOwned b len cap), ("p", .u64 p),
          ("v", .i32 x)] (tripleMem b len cap) [("t", 0, 0)] =
        .ok ((([("t", .stdVecOwned b' len cap), ("p", .u64 p),
          ("v", .i32 x)], m', [("t", 0, 0)])),
          .fellThrough) :=
      memEvalStmtFuel_vgrowSet F "t" (.var "p") (.var "v")
        _ _ _ p x 0 0 b b' len cap m' _ hmpv hmv ht hlay
        hset hmstore hup
    have hfwd : stdVecConstructFwd b len cap p x =
        .ok (.stdVecOwned b' len cap) := by
      simp [stdVecConstructFwd, hset]
    have hstmt : memEvalStmtFuel F stdVecConstructFunc.body
        [("t", .stdVecOwned b len cap), ("p", .u64 p),
          ("v", .i32 x)] (tripleMem b len cap) [("t", 0, 0)] =
        .ok ((([("t", .stdVecOwned b' len cap), ("p", .u64 p),
          ("v", .i32 x)], m', [("t", 0, 0)])),
          .returned (.stdVecOwned b' len cap)) := by
      rw [hbody]
      exact (memEvalStmtFuel_seq_fallthrough F _ _ _ _ _ _ _ _
        hs).trans hmret
    simp only [memEvalFuncFuel, hb, hstmt, hfwd]

/-- Transfer for `construct`. -/
theorem memTransfer_stdVecConstruct (F : Nat) (b : Vec32)
    (len cap : Nat) (p : BitVec 64) (x : BitVec 32)
    (_h : oracleNoalias stdVecConstructFunc
      [.stdVecOwned b len cap, .u64 p, .i32 x]) :
    memEvalFuncFuel F stdVecConstructFunc
      [.stdVecOwned b len cap, .u64 p, .i32 x] =
      evalFuncFuel F stdVecConstructFunc
        [.stdVecOwned b len cap, .u64 p, .i32 x] := by
  rw [memEvalFuncFuel_stdVecConstruct F b len cap p x,
    evalFuncFuel_stdVecConstruct F b len cap p x]

/-- `memEval` for `_M_check_len` (liveness as in `end`: every path
    reads the length header; the throw path is loud on both sides). -/
theorem memEvalFuncFuel_stdVecCheckLen (F : Nat) (b : Vec32)
    (len cap : Nat) (n : BitVec 64) (hlive : b.freed = false) :
    memEvalFuncFuel F stdVecCheckLenFunc
      [.stdVecOwned b len cap, .u64 n] =
      stdVecCheckLenFwd len n := by
  have hb : bindMemArgs stdVecCheckLenFunc.args
      [.stdVecOwned b len cap, .u64 n] emptyMem =
      some ([("t", .stdVecOwned b len cap), ("n", .u64 n)],
        (tripleMem b len cap), [("t", 0, 0)]) := by
    show bindMemArgs
      [{ name := "t", ty := .vecBlock, role := .owned },
       { name := "n", ty := .u 64, role := .owned }]
      [.stdVecOwned b len cap, .u64 n] emptyMem = _
    exact bindMemArgs_stdVecCheckLen b len cap n
  have hbody : stdVecCheckLenFunc.body =
      .if_ (.ult (.usub (.lit (.u64 stdVecMaxDiffBV)) (.vgrowLen "t"))
              (.var "n"))
        .fail
        (.if_ (.ult stdVecNewLenExpr (.vgrowLen "t"))
          (.return_ (.lit (.u64 stdVecMaxDiffBV)))
          (.if_ (.ult (.lit (.u64 stdVecMaxDiffBV)) stdVecNewLenExpr)
            (.return_ (.lit (.u64 stdVecMaxDiffBV)))
            (.return_ stdVecNewLenExpr))) := rfl
  have ht := envLookup_stdVecCheckLen_t b len cap n
  have hn := envLookup_stdVecCheckLen_n b len cap n
  have hlay : layoutLookup [("t", 0, 0)] "t" = some (0, 0) := by
    simp [layoutLookup]
  have hmem : memLoad (tripleMem b len cap) 0 0 0 =
      .ok (BitVec.ofNat 32 len) := by
    simp [tripleMem, memLoad, memFind, hlive]
  have hlen : evalExpr (.vgrowLen "t")
      [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
      .ok (.u64 (BitVec.ofNat 64 len)) :=
    evalExpr_vgrowLen_some "t" _ b len cap ht
  have hmlen : memEvalExpr (.vgrowLen "t")
      [("t", .stdVecOwned b len cap), ("n", .u64 n)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.vgrowLen "t")
        [("t", .stdVecOwned b len cap), ("n", .u64 n)] :=
    memEvalExpr_vgrowLen_hit "t" _ _ _ b len cap 0 0 hlay ht hmem
  have hmaxlit : evalExpr (.lit (.u64 stdVecMaxDiffBV))
      [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
      .ok (.u64 stdVecMaxDiffBV) := by
    simp [evalExpr, litVal]
  have hmmaxlit : memEvalExpr (.lit (.u64 stdVecMaxDiffBV))
      [("t", .stdVecOwned b len cap), ("n", .u64 n)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.lit (.u64 stdVecMaxDiffBV))
        [("t", .stdVecOwned b len cap), ("n", .u64 n)] :=
    memEvalExpr_lit _ _ _ _
  have hnv : evalExpr (.var "n")
      [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
      .ok (.u64 n) := by
    simp [evalExpr, hn]
  have hmnv : memEvalExpr (.var "n")
      [("t", .stdVecOwned b len cap), ("n", .u64 n)]
      (tripleMem b len cap) [("t", 0, 0)] =
      evalExpr (.var "n")
        [("t", .stdVecOwned b len cap), ("n", .u64 n)] :=
    memEvalExpr_var _ _ _ _
  have hsub : evalExpr
      (.usub (.lit (.u64 stdVecMaxDiffBV)) (.vgrowLen "t"))
      [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
      .ok (.u64 (stdVecMaxDiffBV - BitVec.ofNat 64 len)) :=
    evalExpr_usub_u64 _ _ _ _ hlen
  have hmsub := memEvalExpr_usub_agree
    (.lit (.u64 stdVecMaxDiffBV)) (.vgrowLen "t") _ _ _ hmmaxlit hmlen
  have hc1 : evalExpr
      (.ult (.usub (.lit (.u64 stdVecMaxDiffBV)) (.vgrowLen "t"))
        (.var "n"))
      [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
      .ok (.b ((stdVecMaxDiffBV - BitVec.ofNat 64 len).ult n)) :=
    evalExpr_ult_u64 _ _ _ _ _ hsub hnv
  have hmc1 := memEvalExpr_ult_agree
    (.usub (.lit (.u64 stdVecMaxDiffBV)) (.vgrowLen "t")) (.var "n")
    _ _ _ hmsub hmnv
  by_cases h1 : (stdVecMaxDiffBV - BitVec.ofNat 64 len).ult n
  · have hc : memEvalExpr
        (.ult (.usub (.lit (.u64 stdVecMaxDiffBV)) (.vgrowLen "t"))
          (.var "n"))
        [("t", .stdVecOwned b len cap), ("n", .u64 n)]
        (tripleMem b len cap) [("t", 0, 0)] =
        .ok (.b true) := by
      rw [hmc1]
      simp [hc1, h1]
    have hfail : stdVecCheckLenFwd len n = .error .AssertFail := by
      simp [stdVecCheckLenFwd, h1]
    have hmfail : memEvalStmtFuel F .fail
        [("t", .stdVecOwned b len cap), ("n", .u64 n)]
        (tripleMem b len cap) [("t", 0, 0)] = .error .AssertFail :=
      memEvalStmtFuel_fail F _ _ _
    have hstmt : memEvalStmtFuel F stdVecCheckLenFunc.body
        [("t", .stdVecOwned b len cap), ("n", .u64 n)]
        (tripleMem b len cap) [("t", 0, 0)] = .error .AssertFail := by
      rw [hbody, memEvalStmtFuel_if_true F _ _ _ _ _ _ hc]
      exact hmfail
    simp only [memEvalFuncFuel, hb, hstmt, hfail]
  · have hc : memEvalExpr
        (.ult (.usub (.lit (.u64 stdVecMaxDiffBV)) (.vgrowLen "t"))
          (.var "n"))
        [("t", .stdVecOwned b len cap), ("n", .u64 n)]
        (tripleMem b len cap) [("t", 0, 0)] =
        .ok (.b false) := by
      rw [hmc1]
      simp [hc1, h1]
    have hmaxc : evalExpr (.ult (.vgrowLen "t") (.var "n"))
        [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
        .ok (.b ((BitVec.ofNat 64 len).ult n)) :=
        evalExpr_ult_u64 _ _ _ _ _ hlen hnv
    have hmmaxc := memEvalExpr_ult_agree (.vgrowLen "t") (.var "n")
      _ _ _ hmlen hmnv
    by_cases h2 : (BitVec.ofNat 64 len).ult n
    · have hmct : memEvalExpr (.ult (.vgrowLen "t") (.var "n"))
          [("t", .stdVecOwned b len cap), ("n", .u64 n)]
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok (.b true) := by
        rw [hmmaxc]
        simp [hmaxc, h2]
      have hct : evalExpr (.ult (.vgrowLen "t") (.var "n"))
          [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
          .ok (.b true) := by
        simp [hmaxc, h2]
      have hm : evalExpr (.tif (.ult (.vgrowLen "t") (.var "n"))
            (.var "n") (.vgrowLen "t"))
          [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
          .ok (.u64 n) :=
        (evalExpr_tif_true _ _ _ _ hct).trans hnv
      have hmtif := memEvalExpr_tif_true
        (.ult (.vgrowLen "t") (.var "n")) (.var "n") (.vgrowLen "t")
        _ _ _ hmmaxc hct hmnv
      have hnew : evalExpr stdVecNewLenExpr
          [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
          .ok (.u64 (BitVec.ofNat 64 len + n)) := by
        simp only [stdVecNewLenExpr]
        exact evalExpr_uadd_u64 _ _ _ _ _ hlen hm
      have hmnew : memEvalExpr stdVecNewLenExpr
          [("t", .stdVecOwned b len cap), ("n", .u64 n)]
          (tripleMem b len cap) [("t", 0, 0)] =
          evalExpr stdVecNewLenExpr
            [("t", .stdVecOwned b len cap), ("n", .u64 n)] := by
        simp only [stdVecNewLenExpr]
        exact memEvalExpr_uadd_agree _ _ _ _ _ hmlen hmtif
      have hc2raw : evalExpr (.ult stdVecNewLenExpr (.vgrowLen "t"))
          [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
          .ok (.b ((BitVec.ofNat 64 len + n).ult
            (BitVec.ofNat 64 len))) :=
        evalExpr_ult_u64 _ _ _ _ _ hnew hlen
      have hmc2 := memEvalExpr_ult_agree stdVecNewLenExpr
        (.vgrowLen "t") _ _ _ hmnew hmlen
      by_cases h3 : (BitVec.ofNat 64 len + n).ult (BitVec.ofNat 64 len)
      · have hc2 : memEvalExpr (.ult stdVecNewLenExpr (.vgrowLen "t"))
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            (tripleMem b len cap) [("t", 0, 0)] =
            .ok (.b true) := by
          rw [hmc2]
          simp [hc2raw, h3]
        have hfwd : stdVecCheckLenFwd len n =
            .ok (.u64 stdVecMaxDiffBV) := by
          simp [stdVecCheckLenFwd, h1, h2, h3]
        have hmret := memEvalStmtFuel_return F
          (.lit (.u64 stdVecMaxDiffBV)) _ _ _ _ hmmaxlit hmaxlit
        have hstmt : memEvalStmtFuel F stdVecCheckLenFunc.body
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            (tripleMem b len cap) [("t", 0, 0)] =
            .ok ((([("t", .stdVecOwned b len cap), ("n", .u64 n)],
              (tripleMem b len cap), [("t", 0, 0)])),
              .returned (.u64 stdVecMaxDiffBV)) := by
          rw [hbody, memEvalStmtFuel_if_false F _ _ _ _ _ _ hc,
            memEvalStmtFuel_if_true F _ _ _ _ _ _ hc2]
          exact hmret
        simp only [memEvalFuncFuel, hb, hstmt, hfwd]
      · have hc2 : memEvalExpr (.ult stdVecNewLenExpr (.vgrowLen "t"))
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            (tripleMem b len cap) [("t", 0, 0)] =
            .ok (.b false) := by
          rw [hmc2]
          simp [hc2raw, h3]
        have hc3raw : evalExpr
            (.ult (.lit (.u64 stdVecMaxDiffBV)) stdVecNewLenExpr)
            [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
            .ok (.b (stdVecMaxDiffBV.ult
              (BitVec.ofNat 64 len + n))) :=
          evalExpr_ult_u64lit _ _ _ _ hnew
        have hmc3 := memEvalExpr_ult_agree
          (.lit (.u64 stdVecMaxDiffBV)) stdVecNewLenExpr _ _ _
          hmmaxlit hmnew
        by_cases h4 : stdVecMaxDiffBV.ult (BitVec.ofNat 64 len + n)
        · have hc3 : memEvalExpr
              (.ult (.lit (.u64 stdVecMaxDiffBV)) stdVecNewLenExpr)
              [("t", .stdVecOwned b len cap), ("n", .u64 n)]
              (tripleMem b len cap) [("t", 0, 0)] =
              .ok (.b true) := by
            rw [hmc3]
            simp [hc3raw, h4]
          have hfwd : stdVecCheckLenFwd len n =
              .ok (.u64 stdVecMaxDiffBV) := by
            simp [stdVecCheckLenFwd, h1, h2, h3, h4]
          have hmret := memEvalStmtFuel_return F
            (.lit (.u64 stdVecMaxDiffBV)) _ _ _ _ hmmaxlit hmaxlit
          have hstmt : memEvalStmtFuel F stdVecCheckLenFunc.body
              [("t", .stdVecOwned b len cap), ("n", .u64 n)]
              (tripleMem b len cap) [("t", 0, 0)] =
              .ok ((([("t", .stdVecOwned b len cap), ("n", .u64 n)],
                (tripleMem b len cap), [("t", 0, 0)])),
                .returned (.u64 stdVecMaxDiffBV)) := by
            rw [hbody, memEvalStmtFuel_if_false F _ _ _ _ _ _ hc,
              memEvalStmtFuel_if_false F _ _ _ _ _ _ hc2,
              memEvalStmtFuel_if_true F _ _ _ _ _ _ hc3]
            exact hmret
          simp only [memEvalFuncFuel, hb, hstmt, hfwd]
        · have hc3 : memEvalExpr
              (.ult (.lit (.u64 stdVecMaxDiffBV)) stdVecNewLenExpr)
              [("t", .stdVecOwned b len cap), ("n", .u64 n)]
              (tripleMem b len cap) [("t", 0, 0)] =
              .ok (.b false) := by
            rw [hmc3]
            simp [hc3raw, h4]
          have hfwd : stdVecCheckLenFwd len n =
              .ok (.u64 (BitVec.ofNat 64 len + n)) := by
            simp [stdVecCheckLenFwd, h1, h2, h3, h4]
          have hmret := memEvalStmtFuel_return F stdVecNewLenExpr
            _ _ _ _ hmnew hnew
          have hstmt : memEvalStmtFuel F stdVecCheckLenFunc.body
              [("t", .stdVecOwned b len cap), ("n", .u64 n)]
              (tripleMem b len cap) [("t", 0, 0)] =
              .ok ((([("t", .stdVecOwned b len cap), ("n", .u64 n)],
                (tripleMem b len cap), [("t", 0, 0)])),
                .returned (.u64 (BitVec.ofNat 64 len + n))) := by
            rw [hbody, memEvalStmtFuel_if_false F _ _ _ _ _ _ hc,
              memEvalStmtFuel_if_false F _ _ _ _ _ _ hc2,
              memEvalStmtFuel_if_false F _ _ _ _ _ _ hc3]
            exact hmret
          simp only [memEvalFuncFuel, hb, hstmt, hfwd]
    · have hmct : memEvalExpr (.ult (.vgrowLen "t") (.var "n"))
          [("t", .stdVecOwned b len cap), ("n", .u64 n)]
          (tripleMem b len cap) [("t", 0, 0)] =
          .ok (.b false) := by
        rw [hmmaxc]
        simp [hmaxc, h2]
      have hct : evalExpr (.ult (.vgrowLen "t") (.var "n"))
          [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
          .ok (.b false) := by
        simp [hmaxc, h2]
      have hm : evalExpr (.tif (.ult (.vgrowLen "t") (.var "n"))
            (.var "n") (.vgrowLen "t"))
          [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
          .ok (.u64 (BitVec.ofNat 64 len)) :=
        (evalExpr_tif_false _ _ _ _ hct).trans hlen
      have hmtif := memEvalExpr_tif_false
        (.ult (.vgrowLen "t") (.var "n")) (.var "n") (.vgrowLen "t")
        _ _ _ hmmaxc hct hmlen
      have hnew : evalExpr stdVecNewLenExpr
          [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
          .ok (.u64 (BitVec.ofNat 64 len + BitVec.ofNat 64 len)) := by
        simp only [stdVecNewLenExpr]
        exact evalExpr_uadd_u64 _ _ _ _ _ hlen hm
      have hmnew : memEvalExpr stdVecNewLenExpr
          [("t", .stdVecOwned b len cap), ("n", .u64 n)]
          (tripleMem b len cap) [("t", 0, 0)] =
          evalExpr stdVecNewLenExpr
            [("t", .stdVecOwned b len cap), ("n", .u64 n)] := by
        simp only [stdVecNewLenExpr]
        exact memEvalExpr_uadd_agree _ _ _ _ _ hmlen hmtif
      have hc2raw : evalExpr (.ult stdVecNewLenExpr (.vgrowLen "t"))
          [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
          .ok (.b ((BitVec.ofNat 64 len + BitVec.ofNat 64 len).ult
            (BitVec.ofNat 64 len))) :=
        evalExpr_ult_u64 _ _ _ _ _ hnew hlen
      have hmc2 := memEvalExpr_ult_agree stdVecNewLenExpr
        (.vgrowLen "t") _ _ _ hmnew hmlen
      by_cases h3 : (BitVec.ofNat 64 len + BitVec.ofNat 64 len).ult
          (BitVec.ofNat 64 len)
      · have hc2 : memEvalExpr (.ult stdVecNewLenExpr (.vgrowLen "t"))
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            (tripleMem b len cap) [("t", 0, 0)] =
            .ok (.b true) := by
          rw [hmc2]
          simp [hc2raw, h3]
        have hfwd : stdVecCheckLenFwd len n =
            .ok (.u64 stdVecMaxDiffBV) := by
          simp [stdVecCheckLenFwd, h1, h2, h3]
        have hmret := memEvalStmtFuel_return F
          (.lit (.u64 stdVecMaxDiffBV)) _ _ _ _ hmmaxlit hmaxlit
        have hstmt : memEvalStmtFuel F stdVecCheckLenFunc.body
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            (tripleMem b len cap) [("t", 0, 0)] =
            .ok ((([("t", .stdVecOwned b len cap), ("n", .u64 n)],
              (tripleMem b len cap), [("t", 0, 0)])),
              .returned (.u64 stdVecMaxDiffBV)) := by
          rw [hbody, memEvalStmtFuel_if_false F _ _ _ _ _ _ hc,
            memEvalStmtFuel_if_true F _ _ _ _ _ _ hc2]
          exact hmret
        simp only [memEvalFuncFuel, hb, hstmt, hfwd]
      · have hc2 : memEvalExpr (.ult stdVecNewLenExpr (.vgrowLen "t"))
            [("t", .stdVecOwned b len cap), ("n", .u64 n)]
            (tripleMem b len cap) [("t", 0, 0)] =
            .ok (.b false) := by
          rw [hmc2]
          simp [hc2raw, h3]
        have hc3raw : evalExpr
            (.ult (.lit (.u64 stdVecMaxDiffBV)) stdVecNewLenExpr)
            [("t", .stdVecOwned b len cap), ("n", .u64 n)] =
            .ok (.b (stdVecMaxDiffBV.ult
              (BitVec.ofNat 64 len + BitVec.ofNat 64 len))) :=
          evalExpr_ult_u64lit _ _ _ _ hnew
        have hmc3 := memEvalExpr_ult_agree
          (.lit (.u64 stdVecMaxDiffBV)) stdVecNewLenExpr _ _ _
          hmmaxlit hmnew
        by_cases h4 : stdVecMaxDiffBV.ult
            (BitVec.ofNat 64 len + BitVec.ofNat 64 len)
        · have hc3 : memEvalExpr
              (.ult (.lit (.u64 stdVecMaxDiffBV)) stdVecNewLenExpr)
              [("t", .stdVecOwned b len cap), ("n", .u64 n)]
              (tripleMem b len cap) [("t", 0, 0)] =
              .ok (.b true) := by
            rw [hmc3]
            simp [hc3raw, h4]
          have hfwd : stdVecCheckLenFwd len n =
              .ok (.u64 stdVecMaxDiffBV) := by
            simp [stdVecCheckLenFwd, h1, h2, h3, h4]
          have hmret := memEvalStmtFuel_return F
            (.lit (.u64 stdVecMaxDiffBV)) _ _ _ _ hmmaxlit hmaxlit
          have hstmt : memEvalStmtFuel F stdVecCheckLenFunc.body
              [("t", .stdVecOwned b len cap), ("n", .u64 n)]
              (tripleMem b len cap) [("t", 0, 0)] =
              .ok ((([("t", .stdVecOwned b len cap), ("n", .u64 n)],
                (tripleMem b len cap), [("t", 0, 0)])),
                .returned (.u64 stdVecMaxDiffBV)) := by
            rw [hbody, memEvalStmtFuel_if_false F _ _ _ _ _ _ hc,
              memEvalStmtFuel_if_false F _ _ _ _ _ _ hc2,
              memEvalStmtFuel_if_true F _ _ _ _ _ _ hc3]
            exact hmret
          simp only [memEvalFuncFuel, hb, hstmt, hfwd]
        · have hc3 : memEvalExpr
              (.ult (.lit (.u64 stdVecMaxDiffBV)) stdVecNewLenExpr)
              [("t", .stdVecOwned b len cap), ("n", .u64 n)]
              (tripleMem b len cap) [("t", 0, 0)] =
              .ok (.b false) := by
            rw [hmc3]
            simp [hc3raw, h4]
          have hfwd : stdVecCheckLenFwd len n =
              .ok (.u64 (BitVec.ofNat 64 len +
                BitVec.ofNat 64 len)) := by
            simp [stdVecCheckLenFwd, h1, h2, h3, h4]
          have hmret := memEvalStmtFuel_return F stdVecNewLenExpr
            _ _ _ _ hmnew hnew
          have hstmt : memEvalStmtFuel F stdVecCheckLenFunc.body
              [("t", .stdVecOwned b len cap), ("n", .u64 n)]
              (tripleMem b len cap) [("t", 0, 0)] =
              .ok ((([("t", .stdVecOwned b len cap), ("n", .u64 n)],
                (tripleMem b len cap), [("t", 0, 0)])),
                .returned (.u64 (BitVec.ofNat 64 len +
                  BitVec.ofNat 64 len))) := by
            rw [hbody, memEvalStmtFuel_if_false F _ _ _ _ _ _ hc,
              memEvalStmtFuel_if_false F _ _ _ _ _ _ hc2,
              memEvalStmtFuel_if_false F _ _ _ _ _ _ hc3]
            exact hmret
          simp only [memEvalFuncFuel, hb, hstmt, hfwd]

/-- Transfer for `_M_check_len`. -/
theorem memTransfer_stdVecCheckLen (F : Nat) (b : Vec32)
    (len cap : Nat) (n : BitVec 64) (hlive : b.freed = false)
    (_h : oracleNoalias stdVecCheckLenFunc
      [.stdVecOwned b len cap, .u64 n]) :
    memEvalFuncFuel F stdVecCheckLenFunc
      [.stdVecOwned b len cap, .u64 n] =
      evalFuncFuel F stdVecCheckLenFunc
        [.stdVecOwned b len cap, .u64 n] := by
  rw [memEvalFuncFuel_stdVecCheckLen F b len cap n hlive,
    evalFuncFuel_stdVecCheckLen F b len cap n]

