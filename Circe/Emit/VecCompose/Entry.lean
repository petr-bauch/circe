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

/-- `findFunc` resolves the `begin` leaf in the grown program. -/
theorem findFunc_stdVecBegin :
    findFunc vecGrowProg stdVecBeginName =
      some stdVecBeginFunc := by
  unfold vecGrowProg
  rw [findFunc_miss _ _ _ (by decide)]
  exact findFunc_hit _ _

/-- `findFunc` resolves the iterator-advance leaf in the grown program. -/
theorem findFunc_stdVecPlusEl :
    findFunc vecGrowProg stdVecPlusElName =
      some stdVecPlusElFunc := by
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

/-- `emit_correct` for `vec_push_sum`: the closed entry over the
    frozen leaves plus the proved composers agrees with the
    compute-to-`6` forward.

    N8c: this was a ~1100-line hand evaluation (one `have` per script
    step with fully transcribed envs). Both sides are closed terms —
    `#eval` reduces each to `.ok 6` — so the proof is `cir_eval_closed`
    (see `Circe.Eval.Core` for why `native_decide` and not `rfl`, and
    why the statement is at concrete fuel `6`). -/
theorem evalProgFunc_vecPushSumEntry :
    evalProgFunc vecGrowProg 6 vecPushSumEntryFunc [] =
      vecPushSumEntryFwd := by
  cir_eval_closed
