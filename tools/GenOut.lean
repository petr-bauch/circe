-- Generator for the emitted files (Phases 4+7, S1 callers, S2 structs,
-- S3a control flow, S3b 64-bit widths, S4 spec stubs, M1a two-block heap).
-- Run from the repo root: `lake env lean --run tools/GenOut.lean`
-- Writes `out/{Add,Incr,Choose,SumArray,VecAlloc,VecCopySum,AddCaller,SumCaller,StructByValue,NestedSum,SkipSum,FindEq,Cls,Add64,Addu64}.lean`
-- plus `out/{Add,Incr,Choose,SumArray,VecAlloc,VecCopySum,AddCaller,SumCaller,StructByValue,NestedSum,SkipSum,FindEq,Cls,Add64,Addu64}_Spec.lean`
-- from `Circe.Emit.emitFunc` / `Circe.Emit.emitSpec` (single source of truth;
-- `tests/golden/*.lean` pins the forward bytes).
import Circe.Emit

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
  let vec ← emitOrDie vecFunc
  let vec2 ← emitOrDie vec2Func
  let addCaller ← emitOrDie addCallerFunc
  let sumCaller ← emitOrDie sumCallerFunc
  let translate ← emitOrDie translateFunc
  let nested ← emitOrDie nestedFunc
  let skip ← emitOrDie skipFunc
  let findEq ← emitOrDie findEqFunc
  let cls ← emitOrDie clsFunc
  let add64 ← emitOrDie add64Func
  let addu64 ← emitOrDie addu64Func
  IO.FS.writeFile "out/Add.lean" add.forward
  IO.FS.writeFile "out/Incr.lean" incr.forward
  IO.FS.writeFile "out/Choose.lean" (emitFileText (.ok choose))
  IO.FS.writeFile "out/SumArray.lean" (emitFileText (.ok sum))
  IO.FS.writeFile "out/VecAlloc.lean" (emitFileText (.ok vec))
  IO.FS.writeFile "out/VecCopySum.lean" (emitFileText (.ok vec2))
  IO.FS.writeFile "out/AddCaller.lean" (emitFileText (.ok addCaller))
  IO.FS.writeFile "out/SumCaller.lean" (emitFileText (.ok sumCaller))
  IO.FS.writeFile "out/StructByValue.lean" (emitFileText (.ok translate))
  IO.FS.writeFile "out/NestedSum.lean" (emitFileText (.ok nested))
  IO.FS.writeFile "out/SkipSum.lean" (emitFileText (.ok skip))
  IO.FS.writeFile "out/FindEq.lean" (emitFileText (.ok findEq))
  IO.FS.writeFile "out/Cls.lean" (emitFileText (.ok cls))
  IO.FS.writeFile "out/Add64.lean" (emitFileText (.ok add64))
  IO.FS.writeFile "out/Addu64.lean" (emitFileText (.ok addu64))
  let addSpec ← specOrDie addFunc
  let incrSpec ← specOrDie incrFunc
  let chooseSpec ← specOrDie chooseFunc
  let sumSpec ← specOrDie sumFunc
  let vecSpec ← specOrDie vecFunc
  let vec2Spec ← specOrDie vec2Func
  let addCallerSpec ← specOrDie addCallerFunc
  let sumCallerSpec ← specOrDie sumCallerFunc
  let translateSpec ← specOrDie translateFunc
  let nestedSpec ← specOrDie nestedFunc
  let skipSpec ← specOrDie skipFunc
  let findEqSpec ← specOrDie findEqFunc
  let clsSpec ← specOrDie clsFunc
  let add64Spec ← specOrDie add64Func
  let addu64Spec ← specOrDie addu64Func
  IO.FS.writeFile "out/Add_Spec.lean" addSpec
  IO.FS.writeFile "out/Incr_Spec.lean" incrSpec
  IO.FS.writeFile "out/Choose_Spec.lean" chooseSpec
  IO.FS.writeFile "out/SumArray_Spec.lean" sumSpec
  IO.FS.writeFile "out/VecAlloc_Spec.lean" vecSpec
  IO.FS.writeFile "out/VecCopySum_Spec.lean" vec2Spec
  IO.FS.writeFile "out/AddCaller_Spec.lean" addCallerSpec
  IO.FS.writeFile "out/SumCaller_Spec.lean" sumCallerSpec
  IO.FS.writeFile "out/StructByValue_Spec.lean" translateSpec
  IO.FS.writeFile "out/NestedSum_Spec.lean" nestedSpec
  IO.FS.writeFile "out/SkipSum_Spec.lean" skipSpec
  IO.FS.writeFile "out/FindEq_Spec.lean" findEqSpec
  IO.FS.writeFile "out/Cls_Spec.lean" clsSpec
  IO.FS.writeFile "out/Add64_Spec.lean" add64Spec
  IO.FS.writeFile "out/Addu64_Spec.lean" addu64Spec
  match choose.backward with
  | some _ => pure ()
  | none => throw (IO.userError "choose must have a backward definition")
  if sum.backward.isSome then
    throw (IO.userError "sum must not have a backward definition")
  if vec.backward.isSome then
    throw (IO.userError "vec must not have a backward definition")
  if vec2.backward.isSome then
    throw (IO.userError "vec2 must not have a backward definition")
  if addCaller.backward.isSome then
    throw (IO.userError "addCaller must not have a backward definition")
  if sumCaller.backward.isSome then
    throw (IO.userError "sumCaller must not have a backward definition")
  if translate.backward.isSome then
    throw (IO.userError "translate must not have a backward definition")
  if nested.backward.isSome then
    throw (IO.userError "nested must not have a backward definition")
  if skip.backward.isSome then
    throw (IO.userError "skip must not have a backward definition")
  if findEq.backward.isSome then
    throw (IO.userError "findEq must not have a backward definition")
  if cls.backward.isSome then
    throw (IO.userError "cls must not have a backward definition")
  if add64.backward.isSome then
    throw (IO.userError "add64 must not have a backward definition")
  if addu64.backward.isSome then
    throw (IO.userError "addu64 must not have a backward definition")
  IO.println "wrote out/Add.lean out/Incr.lean out/Choose.lean out/SumArray.lean out/VecAlloc.lean out/VecCopySum.lean out/AddCaller.lean out/SumCaller.lean out/StructByValue.lean out/NestedSum.lean out/SkipSum.lean out/FindEq.lean out/Cls.lean out/Add64.lean out/Addu64.lean + 15 *_Spec.lean stubs"
