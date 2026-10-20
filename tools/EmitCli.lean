-- `circe-emit`: the user-facing emission CLI (frontend MVP).
--
-- Usage:
--   lake exe circe-emit -- --in <file.cir> --out <file.lean> [--func <name>]
--
-- Reads raw CIRGen text, validates every defined function, and
-- writes the selected function's emitted Lean file. Oracle facts:
-- repeatable `--fact name=verdict` flags win; every defined
-- function without one defaults to `.unknown` (the N4a precedent
-- — pure by-value functions need no aliasing fact; shape
-- validation still enforces everything). `--func` picks one
-- definition out of a multi-def module; with a single definition
-- it is optional. Anything outside the admitted subset rejects
-- loudly with the gate's dedicated message (never silently
-- modeled). Same `emitFunc` path as `tools/GenOut.lean` (single
-- source of truth); the user writes their own spec + proof
-- against the output (see `examples/hello/`).
import Circe.Validator
import Circe.Emit

/-- `--flag value` lookup. -/
def getArg : List String → String → Option String
  | [], _ => none
  | [_], _ => none
  | f :: v :: rest, flag =>
    if f == flag then some v else getArg (v :: rest) flag

/-- All `--flag value` occurrences. -/
def getArgs : List String → String → List String
  | [], _ => []
  | [_], _ => []
  | f :: v :: rest, flag =>
    if f == flag then v :: getArgs rest flag else getArgs (v :: rest) flag

def usage : String :=
  "usage: circe-emit -- --in <file.cir> --out <file.lean> [--func <name>] [--fact <name>=<unknown|noalias|mayAlias>]..."

/-- `name=verdict` flag value. -/
def parseFact (s : String) : IO OracleFact := do
  match s.splitOn "=" with
  | [n, v] =>
    match parseVerdict v with
    | some verdict => pure ⟨n, verdict⟩
    | none => throw (IO.userError s!"circe-emit: bad --fact '{s}'\n{usage}")
  | _ => throw (IO.userError s!"circe-emit: bad --fact '{s}'\n{usage}")

def main (args : List String) : IO Unit := do
  let some inF := getArg args "--in" | throw (IO.userError usage)
  let some outF := getArg args "--out" | throw (IO.userError usage)
  let text ← IO.FS.readFile inF
  let some mod := parseModule text
    | throw (IO.userError
        "circe-emit: rejected:\nmodule: [outOfSubset] out-of-subset: parse failed: no `cir.func` signature found")
  let mut facts : List OracleFact := []
  for fs in getArgs args "--fact" do
    facts := (← parseFact fs) :: facts
  -- Default: `.unknown` for every defined function without an
  -- explicit fact (the N4a precedent — pure by-value functions
  -- have no single-ref params, so the module default cannot kick
  -- in; shape validation still enforces everything).
  for raw in mod.funcs.filter isFuncDef do
    if !(facts.any (fun f => f.funcName == raw.name)) then
      facts := ⟨raw.name, .unknown⟩ :: facts
  let results := validateModule text facts
  let errs := results.filterMap fun (name, res) =>
    match res with
    | .error rej =>
      some s!"{name}: [{(repr rej.code).pretty}] {rej.message}"
    | .ok _ => none
  if !errs.isEmpty then
    throw (IO.userError ("circe-emit: rejected:\n" ++ "\n".intercalate errs))
  let oks := results.filterMap fun (name, res) =>
    match res with
    | .ok f => some (name, f)
    | .error _ => none
  let (name, f) ← match getArg args "--func" with
    | some want =>
      match oks.find? (fun (n, _) => n == want) with
      | some p => pure p
      | none => throw (IO.userError
          s!"circe-emit: no validated function '{want}' (have: {oks.map (·.1)})")
    | none =>
      match oks with
      | [p] => pure p
      | _ => throw (IO.userError
          s!"circe-emit: --func required (module defines: {oks.map (·.1)})")
  match emitFunc f with
  | .error (.notFragment msg) =>
    throw (IO.userError s!"circe-emit: rejected: {msg}")
  | .ok e =>
    IO.FS.writeFile outF (emitFileText (.ok e))
    IO.println s!"circe-emit: {name} → {outF}"
