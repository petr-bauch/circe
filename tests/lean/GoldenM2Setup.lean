-- Golden test for the M2 cross-cutting setup (no new shapes admitted).
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenM2Setup.lean`
-- 1. `cir.cleanup` / `cir.trap` reject loudly via `forbiddenOp`
--    (`outOfSubset`; both passed silently before this gate).
-- 2. `validateModule` validates every *defined* func in a file and skips
--    declarations (`add_caller` + `vec_alloc` modules each yield exactly
--    their entry, `ok`).
-- 3. A defined func without an oracle fact is a loud wiring error.
--    (A shell `grep` in `tools/check.sh` asserts no checked-in C `.cir`
--    contains the newly-gated ops, so the gates break no existing entry.)
--    Mismatch policy: any in-subset divergence is P0; out-of-subset must
--    reject loudly.
import Circe.Validator

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectSetup (name text : String) (verdict : Verdict) (code substr : String) :
    IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-suite-setup: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-suite-setup: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-suite-setup: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-setup {name} [{code}]"
    pure 1

/-- A `cir.cleanup` region outside any admitted shape rejects. -/
def advCleanup : String :=
  "module {\n  cir.func @cl(%arg0: !s32i {llvm.noundef}) -> !s32i {\n    cir.cleanup.scope {\n      cir.return %arg0 : !s32i\n    } cleanup normal {\n    }\n  }\n}"

/-- A bare `cir.trap` outside any admitted shape rejects. -/
def advTrap : String :=
  "module {\n  cir.func @tr(%arg0: !s32i {llvm.noundef}) -> !s32i {\n    cir.trap loc(#loc)\n  }\n}"

/-- `validateModule` on a file must yield exactly the named defined funcs,
    each validating to `.ok`. -/
def checkModuleDefs (cir : String) (facts : List OracleFact) (want : List String) :
    IO Nat := do
  let text ← IO.FS.readFile cir
  let got := validateModule text facts
  let names := got.map (·.1)
  if names != want then
    throw (IO.userError s!"module {cir}: expected defs {want}, got {names}")
  for (name, res) in got do
    match res with
    | .ok _ => IO.println s!"PASS module-def {cir}:{name} [ok]"
    | .error rej =>
      throw (IO.userError s!"module {cir}:{name} unexpectedly rejected: {(repr rej.code).pretty} {rej.message}")
  pure got.length

/-- A defined func without an oracle fact is a loud wiring error. -/
def checkModuleMissingFact : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/add.cir"
  match validateModule text [] with
  | [("add", .error rej)] =>
    if rej.code != .outOfSubset then
      throw (IO.userError s!"module-missing-fact: expected outOfSubset, got {(repr rej.code).pretty}")
    if !containsSubstr rej.message "no oracle fact" then
      throw (IO.userError s!"module-missing-fact: expected 'no oracle fact' in: {rej.message}")
    IO.println "PASS module-missing-fact [outOfSubset]"
    pure 1
  | other =>
    throw (IO.userError s!"module-missing-fact: unexpected result shape: {other.length} entries")

def main : IO Unit := do
  let verdictText ← IO.FS.readFile "tests/oracle/verdicts.txt"
  let verdicts := parseOracleFacts verdictText
  let mut passed := 0
  let c1 ← checkRejectSetup "cl" advCleanup .unknown "out-of-subset" "cir.cleanup"
  passed := passed + c1
  let c2 ← checkRejectSetup "tr" advTrap .unknown "out-of-subset" "cir.trap"
  passed := passed + c2
  let c3 ← checkModuleDefs "tests/cir/add_caller.cir" verdicts ["add_caller"]
  passed := passed + c3
  let c4 ← checkModuleDefs "tests/cir/vec_alloc.cir" verdicts ["vec_alloc"]
  passed := passed + c4
  let c5 ← checkModuleMissingFact
  passed := passed + c5
  IO.println s!"GOLDENM2SETUP-OK passed={passed}"
