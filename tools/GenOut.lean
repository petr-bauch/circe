-- Generator for the emitted files (Phases 4+7, S1 callers).
-- Run from the repo root: `lake env lean --run tools/GenOut.lean`
-- Writes `out/{Add,Incr,Choose,SumArray,VecAlloc,AddCaller,SumCaller}.lean`
-- from `Circe.Emit.emitFunc` (single source of truth;
-- `tests/golden/*.lean` pins the bytes).
import Circe.Emit

def emitOrDie (f : Func) : IO EmittedFunc := do
  match emitFunc f with
  | .ok e => pure e
  | .error (.notFragment msg) => throw (IO.userError s!"rejected: {msg}")

def main : IO Unit := do
  let add ← emitOrDie addFunc
  let incr ← emitOrDie incrFunc
  let choose ← emitOrDie chooseFunc
  let sum ← emitOrDie sumFunc
  let vec ← emitOrDie vecFunc
  let addCaller ← emitOrDie addCallerFunc
  let sumCaller ← emitOrDie sumCallerFunc
  IO.FS.writeFile "out/Add.lean" add.forward
  IO.FS.writeFile "out/Incr.lean" incr.forward
  IO.FS.writeFile "out/Choose.lean" (emitFileText (.ok choose))
  IO.FS.writeFile "out/SumArray.lean" (emitFileText (.ok sum))
  IO.FS.writeFile "out/VecAlloc.lean" (emitFileText (.ok vec))
  IO.FS.writeFile "out/AddCaller.lean" (emitFileText (.ok addCaller))
  IO.FS.writeFile "out/SumCaller.lean" (emitFileText (.ok sumCaller))
  match choose.backward with
  | some _ => pure ()
  | none => throw (IO.userError "choose must have a backward definition")
  if sum.backward.isSome then
    throw (IO.userError "sum must not have a backward definition")
  if vec.backward.isSome then
    throw (IO.userError "vec must not have a backward definition")
  if addCaller.backward.isSome then
    throw (IO.userError "addCaller must not have a backward definition")
  if sumCaller.backward.isSome then
    throw (IO.userError "sumCaller must not have a backward definition")
  IO.println "wrote out/Add.lean out/Incr.lean out/Choose.lean out/SumArray.lean out/VecAlloc.lean out/AddCaller.lean out/SumCaller.lean"
