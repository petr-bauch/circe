-- Generator for the Phase 3 emitted files.
-- Run from the repo root: `lake env lean --run tools/GenOut.lean`
-- Writes `out/Add.lean` + `out/Incr.lean` from `Circe.Emit.emitFunc`
-- (single source of truth; `tests/golden/*.lean` pins the bytes).
import Circe.Emit

def emitOrDie (f : Func) : IO EmittedFunc := do
  match emitFunc f with
  | .ok e => pure e
  | .error (.notFragment msg) => throw (IO.userError s!"rejected: {msg}")

def main : IO Unit := do
  let add ← emitOrDie addFunc
  let incr ← emitOrDie incrFunc
  IO.FS.writeFile "out/Add.lean" add.forward
  IO.FS.writeFile "out/Incr.lean" incr.forward
  if add.backward.isSome || incr.backward.isSome then
    throw (IO.userError "Phase 3 fragment has no backward functions")
  IO.println "wrote out/Add.lean out/Incr.lean"
