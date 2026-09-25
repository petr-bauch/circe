-- Generator for the Phase 4 emitted files.
-- Run from the repo root: `lake env lean --run tools/GenOut.lean`
-- Writes `out/{Add,Incr,Choose,SumArray}.lean` from `Circe.Emit.emitFunc`
-- (single source of truth; `tests/golden/*.lean` pins the bytes).
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
  IO.FS.writeFile "out/Add.lean" add.forward
  IO.FS.writeFile "out/Incr.lean" incr.forward
  IO.FS.writeFile "out/Choose.lean" (emitFileText (.ok choose))
  IO.FS.writeFile "out/SumArray.lean" (emitFileText (.ok sum))
  match choose.backward with
  | some _ => pure ()
  | none => throw (IO.userError "choose must have a backward definition")
  if sum.backward.isSome then
    throw (IO.userError "sum must not have a backward definition")
  IO.println "wrote out/Add.lean out/Incr.lean out/Choose.lean out/SumArray.lean"
