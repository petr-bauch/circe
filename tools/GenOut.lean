-- Generator for the emitted files (Phases 4+7, S1 callers, S2 structs,
-- S3a control flow, S3b 64-bit widths, S4 spec stubs, M1a two-block heap,
-- M1b u64 heap, M1c grown heap, M2a const-methods, M2b ctors/dtors,
-- M2c new/delete).
-- Run from the repo root: `lake env lean --run tools/GenOut.lean`
-- Writes `out/{Add,Incr,Choose,SumArray,SumNorestrict,VecAlloc,VecAllocU64,VecCopySum,VecRealloc,AddCaller,SumCaller,StructByValue,MethodSum,PointSumRef,AccCtor,AccAdd,AccGet,AccDtor,AccTwo,BoxThrough,NestedSum,SkipSum,FindEq,Cls,Add64,Addu64,Neg,Sdiv}.lean`
-- plus `out/{Add,Incr,Choose,SumArray,SumNorestrict,VecAlloc,VecAllocU64,VecCopySum,VecRealloc,AddCaller,SumCaller,StructByValue,MethodSum,PointSumRef,AccCtor,AccAdd,AccGet,AccDtor,AccTwo,BoxThrough,NestedSum,SkipSum,FindEq,Cls,Add64,Addu64,Neg,Sdiv}_Spec.lean`
-- from `Circe.Emit.emitFunc` / `Circe.Emit.emitSpec` (single source of truth;
-- `tests/golden/*.lean` pins the forward bytes).
import Circe.Emit

set_option maxRecDepth 2048

def emitOrDie (f : Func) : IO EmittedFunc := do
  match emitFunc f with
  | .ok e => pure e
  | .error (.notFragment msg) => throw (IO.userError s!"rejected: {msg}")

def specOrDie (f : Func) : IO String := do
  match emitSpec f with
  | .ok s => pure s
  | .error (.notFragment msg) => throw (IO.userError s!"rejected: {msg}")

def main : IO Unit := do
  let add ← emitOrDie addFunc
  let incr ← emitOrDie incrFunc
  let choose ← emitOrDie chooseFunc
  let sum ← emitOrDie sumFunc
  let sumNr ← emitOrDie { sumFunc with name := "sum_norestrict" }
  let vec ← emitOrDie vecFunc
  let vec64 ← emitOrDie vec64Func
  let vec2 ← emitOrDie vec2Func
  let vecRealloc ← emitOrDie vecReallocFunc
  let addCaller ← emitOrDie addCallerFunc
  let sumCaller ← emitOrDie sumCallerFunc
  let translate ← emitOrDie translateFunc
  let methodSum ← emitOrDie methodSumFunc
  let pointSumRef ← emitOrDie pointSumRefFunc
  let accCtor ← emitOrDie accCtorFunc
  let accAdd ← emitOrDie accAddFunc
  let accGet ← emitOrDie accGetFunc
  let accDtor ← emitOrDie accDtorFunc
  let accTwo ← emitOrDie accTwoFunc
  let boxThrough ← emitOrDie boxThroughFunc
  let nested ← emitOrDie nestedFunc
  let skip ← emitOrDie skipFunc
  let findEq ← emitOrDie findEqFunc
  let cls ← emitOrDie clsFunc
  let clsFall ← emitOrDie clsFallFunc
  let clsDense ← emitOrDie clsDenseFunc
  let add64 ← emitOrDie add64Func
  let addu64 ← emitOrDie addu64Func
  let neg ← emitOrDie negFunc
  let sdiv ← emitOrDie sdivFunc
  let overloadAdd ← emitOrDie { addFunc with name := "_Z3addii" }
  let add3 ← emitOrDie add3Func
  let useAdd ← emitOrDie useAddFunc
  let nsAdd ← emitOrDie { addFunc with name := "_ZN2ns3addEii" }
  let useNsAdd ← emitOrDie useNsAddFunc
  let moveInt ← emitOrDie { addFunc with name := "_Z8move_intii" }
  let moveCtor ← emitOrDie accMoveCtorFunc
  let moveAcc ← emitOrDie moveAccFunc
  let scopeEarly ← emitOrDie scopeEarlyFunc
  let tadd32 ← emitOrDie { addFunc with name := "_Z4taddIiET_S0_S0_" }
  let tadd64 ← emitOrDie { add64Func with name := "_Z4taddIlET_S0_S0_" }
  let useTadd32 ← emitOrDie useTadd32Func
  let useTadd64 ← emitOrDie useTadd64Func
  let arrayRef ← emitOrDie arrayRefFunc
  let arrayAt ← emitOrDie arrayAtFunc
  let arraySum ← emitOrDie arraySumFunc
  let optHas ← emitOrDie optHasFunc
  let optHasValue ← emitOrDie optHasValueFunc
  let optGet ← emitOrDie optGetFunc
  let optImplGet ← emitOrDie optImplGetFunc
  let optDerefOp ← emitOrDie optDerefOpFunc
  let optDeref ← emitOrDie optDerefFunc
  let spanExtent ← emitOrDie spanExtentFunc
  let spanSize ← emitOrDie spanSizeFunc
  let spanIndex ← emitOrDie spanIndexFunc
  let spanSum ← emitOrDie spanSumFunc
  let vecSize ← emitOrDie stdVecSizeFunc
  let vecIndex ← emitOrDie stdVecIndexFunc
  let vecReadSum ← emitOrDie stdVecReadSumFunc
  let vecEmptyCtor ← emitOrDie stdVecEmptyCtorFunc
  let vecUnit ← emitOrDie stdVecUnitFunc
  let vecDtor ← emitOrDie stdVecDtorFunc
  let vecDestroyNoop ← emitOrDie stdVecDestroyNoopFunc
  let vecDestroyPtr ← emitOrDie stdVecDestroyPtrFunc
  let vecGetTp ← emitOrDie stdVecGetTpFunc
  let vecDiffMax ← emitOrDie stdVecDiffMaxFunc
  let vecMax ← emitOrDie stdVecMaxFunc
  let vecMin ← emitOrDie stdVecMinFunc
  let vecCheckLen ← emitOrDie stdVecCheckLenFunc
  let vecBegin ← emitOrDie stdVecBeginFunc
  let vecEnd ← emitOrDie stdVecEndFunc
  let vecBack ← emitOrDie stdVecBackFunc
  let vecIterId ← emitOrDie stdVecIterIdFunc
  let vecMinusEl ← emitOrDie stdVecMinusElFunc
  let vecMinus ← emitOrDie stdVecMinusFunc
  let vecAlloc ← emitOrDie stdVecAllocFunc
  let vecDealloc ← emitOrDie stdVecDeallocFunc
  let vecDeallocGuard ← emitOrDie stdVecDeallocGuardFunc
  let vecConstruct ← emitOrDie stdVecConstructFunc
  let vecReloc ← emitOrDie stdVecRelocFunc
  let vecGrowRealloc ← emitOrDie stdVecGrowReallocFunc
  let vecGrowEmplace ← emitOrDie stdVecEmplaceBackFunc
  let vecGrowPushBack ← emitOrDie stdVecPushBackFunc
  let vecGrowEntry ← emitOrDie vecPushSumEntryFunc
  IO.FS.writeFile "out/Add.lean" add.forward
  IO.FS.writeFile "out/Incr.lean" incr.forward
  IO.FS.writeFile "out/Choose.lean" (emitFileText (.ok choose))
  IO.FS.writeFile "out/SumArray.lean" (emitFileText (.ok sum))
  IO.FS.writeFile "out/SumNorestrict.lean" (emitFileText (.ok sumNr))
  IO.FS.writeFile "out/VecAlloc.lean" (emitFileText (.ok vec))
  IO.FS.writeFile "out/VecAllocU64.lean" (emitFileText (.ok vec64))
  IO.FS.writeFile "out/VecCopySum.lean" (emitFileText (.ok vec2))
  IO.FS.writeFile "out/VecRealloc.lean" (emitFileText (.ok vecRealloc))
  IO.FS.writeFile "out/AddCaller.lean" (emitFileText (.ok addCaller))
  IO.FS.writeFile "out/SumCaller.lean" (emitFileText (.ok sumCaller))
  IO.FS.writeFile "out/StructByValue.lean" (emitFileText (.ok translate))
  IO.FS.writeFile "out/MethodSum.lean" (emitFileText (.ok methodSum))
  IO.FS.writeFile "out/PointSumRef.lean" (emitFileText (.ok pointSumRef))
  IO.FS.writeFile "out/AccCtor.lean" (emitFileText (.ok accCtor))
  IO.FS.writeFile "out/AccAdd.lean" (emitFileText (.ok accAdd))
  IO.FS.writeFile "out/AccGet.lean" (emitFileText (.ok accGet))
  IO.FS.writeFile "out/AccDtor.lean" (emitFileText (.ok accDtor))
  IO.FS.writeFile "out/AccTwo.lean" (emitFileText (.ok accTwo))
  IO.FS.writeFile "out/BoxThrough.lean" (emitFileText (.ok boxThrough))
  IO.FS.writeFile "out/NestedSum.lean" (emitFileText (.ok nested))
  IO.FS.writeFile "out/SkipSum.lean" (emitFileText (.ok skip))
  IO.FS.writeFile "out/FindEq.lean" (emitFileText (.ok findEq))
  IO.FS.writeFile "out/Cls.lean" (emitFileText (.ok cls))
  IO.FS.writeFile "out/ClsFall.lean" (emitFileText (.ok clsFall))
  IO.FS.writeFile "out/ClsDense.lean" (emitFileText (.ok clsDense))
  IO.FS.writeFile "out/Add64.lean" (emitFileText (.ok add64))
  IO.FS.writeFile "out/Addu64.lean" (emitFileText (.ok addu64))
  IO.FS.writeFile "out/Neg.lean" (emitFileText (.ok neg))
  IO.FS.writeFile "out/Sdiv.lean" (emitFileText (.ok sdiv))
  IO.FS.writeFile "out/OverloadAdd.lean" (emitFileText (.ok overloadAdd))
  IO.FS.writeFile "out/Add3.lean" (emitFileText (.ok add3))
  IO.FS.writeFile "out/UseAdd.lean" (emitFileText (.ok useAdd))
  IO.FS.writeFile "out/NsAdd.lean" (emitFileText (.ok nsAdd))
  IO.FS.writeFile "out/UseNsAdd.lean" (emitFileText (.ok useNsAdd))
  IO.FS.writeFile "out/MoveInt.lean" (emitFileText (.ok moveInt))
  IO.FS.writeFile "out/MoveCtor.lean" (emitFileText (.ok moveCtor))
  IO.FS.writeFile "out/MoveAcc.lean" (emitFileText (.ok moveAcc))
  IO.FS.writeFile "out/ScopeEarly.lean" (emitFileText (.ok scopeEarly))
  IO.FS.writeFile "out/Tadd32.lean" (emitFileText (.ok tadd32))
  IO.FS.writeFile "out/Tadd64.lean" (emitFileText (.ok tadd64))
  IO.FS.writeFile "out/UseTadd32.lean" (emitFileText (.ok useTadd32))
  IO.FS.writeFile "out/UseTadd64.lean" (emitFileText (.ok useTadd64))
  IO.FS.writeFile "out/ArrayRef.lean" (emitFileText (.ok arrayRef))
  IO.FS.writeFile "out/ArrayAt.lean" (emitFileText (.ok arrayAt))
  IO.FS.writeFile "out/ArraySum.lean" (emitFileText (.ok arraySum))
  IO.FS.writeFile "out/OptHas.lean" (emitFileText (.ok optHas))
  IO.FS.writeFile "out/OptHasValue.lean" (emitFileText (.ok optHasValue))
  IO.FS.writeFile "out/OptGet.lean" (emitFileText (.ok optGet))
  IO.FS.writeFile "out/OptImplGet.lean" (emitFileText (.ok optImplGet))
  IO.FS.writeFile "out/OptDerefOp.lean" (emitFileText (.ok optDerefOp))
  IO.FS.writeFile "out/OptDeref.lean" (emitFileText (.ok optDeref))
  IO.FS.writeFile "out/SpanExtent.lean" (emitFileText (.ok spanExtent))
  IO.FS.writeFile "out/SpanSize.lean" (emitFileText (.ok spanSize))
  IO.FS.writeFile "out/SpanIndex.lean" (emitFileText (.ok spanIndex))
  IO.FS.writeFile "out/SpanSum.lean" (emitFileText (.ok spanSum))
  IO.FS.writeFile "out/VecSize.lean" (emitFileText (.ok vecSize))
  IO.FS.writeFile "out/VecIndex.lean" (emitFileText (.ok vecIndex))
  IO.FS.writeFile "out/VecReadSum.lean" (emitFileText (.ok vecReadSum))
  IO.FS.writeFile "out/VecGrowEmptyCtor.lean" (emitFileText (.ok vecEmptyCtor))
  IO.FS.writeFile "out/VecGrowUnit.lean" (emitFileText (.ok vecUnit))
  IO.FS.writeFile "out/VecGrowDtor.lean" (emitFileText (.ok vecDtor))
  IO.FS.writeFile "out/VecGrowDestroyNoop.lean" (emitFileText (.ok vecDestroyNoop))
  IO.FS.writeFile "out/VecGrowDestroyPtr.lean" (emitFileText (.ok vecDestroyPtr))
  IO.FS.writeFile "out/VecGrowGetTp.lean" (emitFileText (.ok vecGetTp))
  IO.FS.writeFile "out/VecGrowDiffMax.lean" (emitFileText (.ok vecDiffMax))
  IO.FS.writeFile "out/VecGrowMax.lean" (emitFileText (.ok vecMax))
  IO.FS.writeFile "out/VecGrowMin.lean" (emitFileText (.ok vecMin))
  IO.FS.writeFile "out/VecGrowCheckLen.lean" (emitFileText (.ok vecCheckLen))
  IO.FS.writeFile "out/VecGrowBegin.lean" (emitFileText (.ok vecBegin))
  IO.FS.writeFile "out/VecGrowEnd.lean" (emitFileText (.ok vecEnd))
  IO.FS.writeFile "out/VecGrowBack.lean" (emitFileText (.ok vecBack))
  IO.FS.writeFile "out/VecGrowIterId.lean" (emitFileText (.ok vecIterId))
  IO.FS.writeFile "out/VecGrowMinusEl.lean" (emitFileText (.ok vecMinusEl))
  IO.FS.writeFile "out/VecGrowMinus.lean" (emitFileText (.ok vecMinus))
  IO.FS.writeFile "out/VecGrowAlloc.lean" (emitFileText (.ok vecAlloc))
  IO.FS.writeFile "out/VecGrowDealloc.lean" (emitFileText (.ok vecDealloc))
  IO.FS.writeFile "out/VecGrowDeallocGuard.lean" (emitFileText (.ok vecDeallocGuard))
  IO.FS.writeFile "out/VecGrowConstruct.lean" (emitFileText (.ok vecConstruct))
  IO.FS.writeFile "out/VecGrowReloc.lean" (emitFileText (.ok vecReloc))
  IO.FS.writeFile "out/VecGrowComposerRealloc.lean" (emitFileText (.ok vecGrowRealloc))
  IO.FS.writeFile "out/VecGrowComposerEmplace.lean" (emitFileText (.ok vecGrowEmplace))
  IO.FS.writeFile "out/VecGrowComposerPushBack.lean" (emitFileText (.ok vecGrowPushBack))
  IO.FS.writeFile "out/VecGrowComposerEntry.lean" (emitFileText (.ok vecGrowEntry))
  let addSpec ← specOrDie addFunc
  let incrSpec ← specOrDie incrFunc
  let chooseSpec ← specOrDie chooseFunc
  let sumSpec ← specOrDie sumFunc
  let sumNrSpec ← specOrDie { sumFunc with name := "sum_norestrict" }
  let vecSpec ← specOrDie vecFunc
  let vec64Spec ← specOrDie vec64Func
  let vec2Spec ← specOrDie vec2Func
  let vecReallocSpec ← specOrDie vecReallocFunc
  let addCallerSpec ← specOrDie addCallerFunc
  let sumCallerSpec ← specOrDie sumCallerFunc
  let translateSpec ← specOrDie translateFunc
  let methodSumSpec ← specOrDie methodSumFunc
  let pointSumRefSpec ← specOrDie pointSumRefFunc
  let accCtorSpec ← specOrDie accCtorFunc
  let accAddSpec ← specOrDie accAddFunc
  let accGetSpec ← specOrDie accGetFunc
  let accDtorSpec ← specOrDie accDtorFunc
  let accTwoSpec ← specOrDie accTwoFunc
  let boxThroughSpec ← specOrDie boxThroughFunc
  let nestedSpec ← specOrDie nestedFunc
  let skipSpec ← specOrDie skipFunc
  let findEqSpec ← specOrDie findEqFunc
  let clsSpec ← specOrDie clsFunc
  let clsFallSpec ← specOrDie clsFallFunc
  let clsDenseSpec ← specOrDie clsDenseFunc
  let add64Spec ← specOrDie add64Func
  let addu64Spec ← specOrDie addu64Func
  let negSpec ← specOrDie negFunc
  let sdivSpec ← specOrDie sdivFunc
  let overloadAddSpec ← specOrDie { addFunc with name := "_Z3addii" }
  let add3Spec ← specOrDie add3Func
  let useAddSpec ← specOrDie useAddFunc
  let nsAddSpec ← specOrDie { addFunc with name := "_ZN2ns3addEii" }
  let useNsAddSpec ← specOrDie useNsAddFunc
  let moveIntSpec ← specOrDie { addFunc with name := "_Z8move_intii" }
  let moveCtorSpec ← specOrDie accMoveCtorFunc
  let moveAccSpec ← specOrDie moveAccFunc
  let scopeEarlySpec ← specOrDie scopeEarlyFunc
  let tadd32Spec ← specOrDie { addFunc with name := "_Z4taddIiET_S0_S0_" }
  let tadd64Spec ← specOrDie { add64Func with name := "_Z4taddIlET_S0_S0_" }
  let useTadd32Spec ← specOrDie useTadd32Func
  let useTadd64Spec ← specOrDie useTadd64Func
  let arrayRefSpec ← specOrDie arrayRefFunc
  let arrayAtSpec ← specOrDie arrayAtFunc
  let arraySumSpec ← specOrDie arraySumFunc
  let optHasSpec ← specOrDie optHasFunc
  let optHasValueSpec ← specOrDie optHasValueFunc
  let optGetSpec ← specOrDie optGetFunc
  let optImplGetSpec ← specOrDie optImplGetFunc
  let optDerefOpSpec ← specOrDie optDerefOpFunc
  let optDerefSpec ← specOrDie optDerefFunc
  let spanExtentSpec ← specOrDie spanExtentFunc
  let spanSizeSpec ← specOrDie spanSizeFunc
  let spanIndexSpec ← specOrDie spanIndexFunc
  let spanSumSpec ← specOrDie spanSumFunc
  let vecSizeSpec ← specOrDie stdVecSizeFunc
  let vecIndexSpec ← specOrDie stdVecIndexFunc
  let vecReadSumSpec ← specOrDie stdVecReadSumFunc
  let vecEmptyCtorSpec ← specOrDie stdVecEmptyCtorFunc
  let vecUnitSpec ← specOrDie stdVecUnitFunc
  let vecDtorSpec ← specOrDie stdVecDtorFunc
  let vecDestroyNoopSpec ← specOrDie stdVecDestroyNoopFunc
  let vecDestroyPtrSpec ← specOrDie stdVecDestroyPtrFunc
  let vecGetTpSpec ← specOrDie stdVecGetTpFunc
  let vecDiffMaxSpec ← specOrDie stdVecDiffMaxFunc
  let vecMaxSpec ← specOrDie stdVecMaxFunc
  let vecMinSpec ← specOrDie stdVecMinFunc
  let vecCheckLenSpec ← specOrDie stdVecCheckLenFunc
  let vecBeginSpec ← specOrDie stdVecBeginFunc
  let vecEndSpec ← specOrDie stdVecEndFunc
  let vecBackSpec ← specOrDie stdVecBackFunc
  let vecIterIdSpec ← specOrDie stdVecIterIdFunc
  let vecMinusElSpec ← specOrDie stdVecMinusElFunc
  let vecMinusSpec ← specOrDie stdVecMinusFunc
  let vecAllocSpec ← specOrDie stdVecAllocFunc
  let vecDeallocSpec ← specOrDie stdVecDeallocFunc
  let vecDeallocGuardSpec ← specOrDie stdVecDeallocGuardFunc
  let vecConstructSpec ← specOrDie stdVecConstructFunc
  let vecRelocSpec ← specOrDie stdVecRelocFunc
  let vecGrowReallocSpec ← specOrDie stdVecGrowReallocFunc
  let vecGrowEmplaceSpec ← specOrDie stdVecEmplaceBackFunc
  let vecGrowPushBackSpec ← specOrDie stdVecPushBackFunc
  let vecGrowEntrySpec ← specOrDie vecPushSumEntryFunc
  IO.FS.writeFile "out/Add_Spec.lean" addSpec
  IO.FS.writeFile "out/Incr_Spec.lean" incrSpec
  IO.FS.writeFile "out/Choose_Spec.lean" chooseSpec
  IO.FS.writeFile "out/SumArray_Spec.lean" sumSpec
  IO.FS.writeFile "out/SumNorestrict_Spec.lean" sumNrSpec
  IO.FS.writeFile "out/VecAlloc_Spec.lean" vecSpec
  IO.FS.writeFile "out/VecAllocU64_Spec.lean" vec64Spec
  IO.FS.writeFile "out/VecCopySum_Spec.lean" vec2Spec
  IO.FS.writeFile "out/VecRealloc_Spec.lean" vecReallocSpec
  IO.FS.writeFile "out/AddCaller_Spec.lean" addCallerSpec
  IO.FS.writeFile "out/SumCaller_Spec.lean" sumCallerSpec
  IO.FS.writeFile "out/StructByValue_Spec.lean" translateSpec
  IO.FS.writeFile "out/MethodSum_Spec.lean" methodSumSpec
  IO.FS.writeFile "out/PointSumRef_Spec.lean" pointSumRefSpec
  IO.FS.writeFile "out/AccCtor_Spec.lean" accCtorSpec
  IO.FS.writeFile "out/AccAdd_Spec.lean" accAddSpec
  IO.FS.writeFile "out/AccGet_Spec.lean" accGetSpec
  IO.FS.writeFile "out/AccDtor_Spec.lean" accDtorSpec
  IO.FS.writeFile "out/AccTwo_Spec.lean" accTwoSpec
  IO.FS.writeFile "out/BoxThrough_Spec.lean" boxThroughSpec
  IO.FS.writeFile "out/NestedSum_Spec.lean" nestedSpec
  IO.FS.writeFile "out/SkipSum_Spec.lean" skipSpec
  IO.FS.writeFile "out/FindEq_Spec.lean" findEqSpec
  IO.FS.writeFile "out/Cls_Spec.lean" clsSpec
  IO.FS.writeFile "out/ClsFall_Spec.lean" clsFallSpec
  IO.FS.writeFile "out/ClsDense_Spec.lean" clsDenseSpec
  IO.FS.writeFile "out/Add64_Spec.lean" add64Spec
  IO.FS.writeFile "out/Addu64_Spec.lean" addu64Spec
  IO.FS.writeFile "out/Neg_Spec.lean" negSpec
  IO.FS.writeFile "out/Sdiv_Spec.lean" sdivSpec
  IO.FS.writeFile "out/OverloadAdd_Spec.lean" overloadAddSpec
  IO.FS.writeFile "out/Add3_Spec.lean" add3Spec
  IO.FS.writeFile "out/UseAdd_Spec.lean" useAddSpec
  IO.FS.writeFile "out/NsAdd_Spec.lean" nsAddSpec
  IO.FS.writeFile "out/UseNsAdd_Spec.lean" useNsAddSpec
  IO.FS.writeFile "out/MoveInt_Spec.lean" moveIntSpec
  IO.FS.writeFile "out/MoveCtor_Spec.lean" moveCtorSpec
  IO.FS.writeFile "out/MoveAcc_Spec.lean" moveAccSpec
  IO.FS.writeFile "out/ScopeEarly_Spec.lean" scopeEarlySpec
  IO.FS.writeFile "out/Tadd32_Spec.lean" tadd32Spec
  IO.FS.writeFile "out/Tadd64_Spec.lean" tadd64Spec
  IO.FS.writeFile "out/UseTadd32_Spec.lean" useTadd32Spec
  IO.FS.writeFile "out/UseTadd64_Spec.lean" useTadd64Spec
  IO.FS.writeFile "out/ArrayRef_Spec.lean" arrayRefSpec
  IO.FS.writeFile "out/ArrayAt_Spec.lean" arrayAtSpec
  IO.FS.writeFile "out/ArraySum_Spec.lean" arraySumSpec
  IO.FS.writeFile "out/OptHas_Spec.lean" optHasSpec
  IO.FS.writeFile "out/OptHasValue_Spec.lean" optHasValueSpec
  IO.FS.writeFile "out/OptGet_Spec.lean" optGetSpec
  IO.FS.writeFile "out/OptImplGet_Spec.lean" optImplGetSpec
  IO.FS.writeFile "out/OptDerefOp_Spec.lean" optDerefOpSpec
  IO.FS.writeFile "out/OptDeref_Spec.lean" optDerefSpec
  IO.FS.writeFile "out/SpanExtent_Spec.lean" spanExtentSpec
  IO.FS.writeFile "out/SpanSize_Spec.lean" spanSizeSpec
  IO.FS.writeFile "out/SpanIndex_Spec.lean" spanIndexSpec
  IO.FS.writeFile "out/SpanSum_Spec.lean" spanSumSpec
  IO.FS.writeFile "out/VecSize_Spec.lean" vecSizeSpec
  IO.FS.writeFile "out/VecIndex_Spec.lean" vecIndexSpec
  IO.FS.writeFile "out/VecReadSum_Spec.lean" vecReadSumSpec
  IO.FS.writeFile "out/VecGrowEmptyCtor_Spec.lean" vecEmptyCtorSpec
  IO.FS.writeFile "out/VecGrowUnit_Spec.lean" vecUnitSpec
  IO.FS.writeFile "out/VecGrowDtor_Spec.lean" vecDtorSpec
  IO.FS.writeFile "out/VecGrowDestroyNoop_Spec.lean" vecDestroyNoopSpec
  IO.FS.writeFile "out/VecGrowDestroyPtr_Spec.lean" vecDestroyPtrSpec
  IO.FS.writeFile "out/VecGrowGetTp_Spec.lean" vecGetTpSpec
  IO.FS.writeFile "out/VecGrowDiffMax_Spec.lean" vecDiffMaxSpec
  IO.FS.writeFile "out/VecGrowMax_Spec.lean" vecMaxSpec
  IO.FS.writeFile "out/VecGrowMin_Spec.lean" vecMinSpec
  IO.FS.writeFile "out/VecGrowCheckLen_Spec.lean" vecCheckLenSpec
  IO.FS.writeFile "out/VecGrowBegin_Spec.lean" vecBeginSpec
  IO.FS.writeFile "out/VecGrowEnd_Spec.lean" vecEndSpec
  IO.FS.writeFile "out/VecGrowBack_Spec.lean" vecBackSpec
  IO.FS.writeFile "out/VecGrowIterId_Spec.lean" vecIterIdSpec
  IO.FS.writeFile "out/VecGrowMinusEl_Spec.lean" vecMinusElSpec
  IO.FS.writeFile "out/VecGrowMinus_Spec.lean" vecMinusSpec
  IO.FS.writeFile "out/VecGrowAlloc_Spec.lean" vecAllocSpec
  IO.FS.writeFile "out/VecGrowDealloc_Spec.lean" vecDeallocSpec
  IO.FS.writeFile "out/VecGrowDeallocGuard_Spec.lean" vecDeallocGuardSpec
  IO.FS.writeFile "out/VecGrowConstruct_Spec.lean" vecConstructSpec
  IO.FS.writeFile "out/VecGrowReloc_Spec.lean" vecRelocSpec
  IO.FS.writeFile "out/VecGrowComposerRealloc_Spec.lean" vecGrowReallocSpec
  IO.FS.writeFile "out/VecGrowComposerEmplace_Spec.lean" vecGrowEmplaceSpec
  IO.FS.writeFile "out/VecGrowComposerPushBack_Spec.lean" vecGrowPushBackSpec
  IO.FS.writeFile "out/VecGrowComposerEntry_Spec.lean" vecGrowEntrySpec
  match choose.backward with
  | some _ => pure ()
  | none => throw (IO.userError "choose must have a backward definition")
  if sum.backward.isSome then
    throw (IO.userError "sum must not have a backward definition")
  if sumNr.backward.isSome then
    throw (IO.userError "sum_norestrict must not have a backward definition")
  if vec.backward.isSome then
    throw (IO.userError "vec must not have a backward definition")
  if vec2.backward.isSome then
    throw (IO.userError "vec2 must not have a backward definition")
  if vec64.backward.isSome then
    throw (IO.userError "vec64 must not have a backward definition")
  if vecRealloc.backward.isSome then
    throw (IO.userError "vecRealloc must not have a backward definition")
  if addCaller.backward.isSome then
    throw (IO.userError "addCaller must not have a backward definition")
  if sumCaller.backward.isSome then
    throw (IO.userError "sumCaller must not have a backward definition")
  if translate.backward.isSome then
    throw (IO.userError "translate must not have a backward definition")
  if methodSum.backward.isSome then
    throw (IO.userError "methodSum must not have a backward definition")
  if pointSumRef.backward.isSome then
    throw (IO.userError "pointSumRef must not have a backward definition")
  if accCtor.backward.isSome then
    throw (IO.userError "accCtor must not have a backward definition")
  if accAdd.backward.isSome then
    throw (IO.userError "accAdd must not have a backward definition")
  if accGet.backward.isSome then
    throw (IO.userError "accGet must not have a backward definition")
  if accDtor.backward.isSome then
    throw (IO.userError "accDtor must not have a backward definition")
  if accTwo.backward.isSome then
    throw (IO.userError "accTwo must not have a backward definition")
  if boxThrough.backward.isSome then
    throw (IO.userError "boxThrough must not have a backward definition")
  if nested.backward.isSome then
    throw (IO.userError "nested must not have a backward definition")
  if skip.backward.isSome then
    throw (IO.userError "skip must not have a backward definition")
  if findEq.backward.isSome then
    throw (IO.userError "findEq must not have a backward definition")
  if cls.backward.isSome then
    throw (IO.userError "cls must not have a backward definition")
  if clsFall.backward.isSome then
    throw (IO.userError "clsFall must not have a backward definition")
  if clsDense.backward.isSome then
    throw (IO.userError "clsDense must not have a backward definition")
  if add64.backward.isSome then
    throw (IO.userError "add64 must not have a backward definition")
  if addu64.backward.isSome then
    throw (IO.userError "addu64 must not have a backward definition")
  if neg.backward.isSome then
    throw (IO.userError "neg must not have a backward definition")
  if sdiv.backward.isSome then
    throw (IO.userError "sdiv must not have a backward definition")
  if arrayRef.backward.isSome then
    throw (IO.userError "arrayRef must not have a backward definition")
  if arrayAt.backward.isSome then
    throw (IO.userError "arrayAt must not have a backward definition")
  if arraySum.backward.isSome then
    throw (IO.userError "arraySum must not have a backward definition")
  if vecEmptyCtor.backward.isSome then
    throw (IO.userError "vecEmptyCtor must not have a backward definition")
  if vecUnit.backward.isSome then
    throw (IO.userError "vecUnit must not have a backward definition")
  if vecDtor.backward.isSome then
    throw (IO.userError "vecDtor must not have a backward definition")
  if vecDestroyNoop.backward.isSome then
    throw (IO.userError "vecDestroyNoop must not have a backward definition")
  if vecDestroyPtr.backward.isSome then
    throw (IO.userError "vecDestroyPtr must not have a backward definition")
  if vecGetTp.backward.isSome then
    throw (IO.userError "vecGetTp must not have a backward definition")
  if vecDiffMax.backward.isSome then
    throw (IO.userError "vecDiffMax must not have a backward definition")
  if vecMax.backward.isSome then
    throw (IO.userError "vecMax must not have a backward definition")
  if vecMin.backward.isSome then
    throw (IO.userError "vecMin must not have a backward definition")
  if vecCheckLen.backward.isSome then
    throw (IO.userError "vecCheckLen must not have a backward definition")
  if vecBegin.backward.isSome then
    throw (IO.userError "vecBegin must not have a backward definition")
  if vecEnd.backward.isSome then
    throw (IO.userError "vecEnd must not have a backward definition")
  if vecBack.backward.isSome then
    throw (IO.userError "vecBack must not have a backward definition")
  if vecIterId.backward.isSome then
    throw (IO.userError "vecIterId must not have a backward definition")
  if vecMinusEl.backward.isSome then
    throw (IO.userError "vecMinusEl must not have a backward definition")
  if vecMinus.backward.isSome then
    throw (IO.userError "vecMinus must not have a backward definition")
  if vecAlloc.backward.isSome then
    throw (IO.userError "vecAlloc must not have a backward definition")
  if vecDealloc.backward.isSome then
    throw (IO.userError "vecDealloc must not have a backward definition")
  if vecDeallocGuard.backward.isSome then
    throw (IO.userError "vecDeallocGuard must not have a backward definition")
  if vecConstruct.backward.isSome then
    throw (IO.userError "vecConstruct must not have a backward definition")
  if vecReloc.backward.isSome then
    throw (IO.userError "vecReloc must not have a backward definition")
  if vecGrowRealloc.backward.isSome then
    throw (IO.userError "vecGrowRealloc must not have a backward definition")
  if vecGrowEmplace.backward.isSome then
    throw (IO.userError "vecGrowEmplace must not have a backward definition")
  if vecGrowPushBack.backward.isSome then
    throw (IO.userError "vecGrowPushBack must not have a backward definition")
  if vecGrowEntry.backward.isSome then
    throw (IO.userError "vecGrowEntry must not have a backward definition")
  IO.println "wrote out/Add.lean out/Incr.lean out/Choose.lean out/SumArray.lean out/SumNorestrict.lean out/VecAlloc.lean out/VecAllocU64.lean out/VecCopySum.lean out/VecRealloc.lean out/AddCaller.lean out/SumCaller.lean out/StructByValue.lean out/MethodSum.lean out/PointSumRef.lean out/AccCtor.lean out/AccAdd.lean out/AccGet.lean out/AccDtor.lean out/AccTwo.lean out/BoxThrough.lean out/NestedSum.lean out/SkipSum.lean out/FindEq.lean out/Cls.lean out/ClsFall.lean out/ClsDense.lean out/Add64.lean out/Addu64.lean out/OverloadAdd.lean out/Add3.lean out/UseAdd.lean out/NsAdd.lean out/UseNsAdd.lean out/MoveInt.lean out/MoveCtor.lean out/MoveAcc.lean out/ScopeEarly.lean out/Tadd32.lean out/Tadd64.lean out/UseTadd32.lean out/UseTadd64.lean out/ArrayRef.lean out/ArrayAt.lean out/ArraySum.lean out/OptHas.lean out/OptHasValue.lean out/OptGet.lean out/OptImplGet.lean out/OptDerefOp.lean out/OptDeref.lean out/SpanExtent.lean out/SpanSize.lean out/SpanIndex.lean out/SpanSum.lean out/VecSize.lean out/VecIndex.lean out/VecReadSum.lean out/VecGrowEmptyCtor.lean out/VecGrowUnit.lean out/VecGrowDtor.lean out/VecGrowDestroyNoop.lean out/VecGrowDestroyPtr.lean out/VecGrowGetTp.lean out/VecGrowDiffMax.lean out/VecGrowMax.lean out/VecGrowMin.lean out/VecGrowCheckLen.lean out/VecGrowBegin.lean out/VecGrowEnd.lean out/VecGrowBack.lean out/VecGrowIterId.lean out/VecGrowMinusEl.lean out/VecGrowMinus.lean out/VecGrowAlloc.lean out/VecGrowDealloc.lean out/VecGrowDeallocGuard.lean out/VecGrowConstruct.lean out/VecGrowReloc.lean out/VecGrowComposerRealloc.lean out/VecGrowComposerEmplace.lean out/VecGrowComposerPushBack.lean out/VecGrowComposerEntry.lean + 84 *_Spec.lean stubs"
