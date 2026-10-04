-- Golden test for N4c: template-instantiation pipeline + rejection suite.
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenTadd.lean`
-- 1. Corpus pipeline: `tests/cir/tadd.cir` (two instantiation leaves +
--    two resolving entries) validates via `runModulePipeline` with
--    explicit `unknown` facts (int-only: pure, so the verdict is
--    unchecked but the wiring entry is still required) and emits
--    byte-identical text to
--    `tests/golden/{Tadd32,Tadd64,UseTadd32,UseTadd64}.lean`.
--    The leaves reuse the existing `.add` / `.add64` shapes under their
--    mangled instantiation names (the gate is name-agnostic); the two
--    entries are new N4c shapes.
-- 2. Rejection suite: call to an unknown mangled callee (generic),
--    call to a known instantiation with the wrong arity, double call
--    into a known instantiation, call plus local arithmetic, 64-bit
--    instantiation called at the wrong width — the first is generic,
--    the rest hit the dedicated template wrong-shape rejection.
--    Mismatch policy: any in-subset divergence is P0; out-of-subset must
--    reject loudly.
import Circe.Validator

namespace GoldenTadd

/-- Int-only leaves need explicit `unknown` facts (pure functions skip
    the oracle check but the wiring still requires the entry). -/
def lookupFacts (names : List String) : IO (List OracleFact) := do
  let verdictText ← IO.FS.readFile "tests/oracle/verdicts.txt"
  let verdicts := parseOracleFacts verdictText
  let mut out : List OracleFact := []
  for n in names do
    match lookupOracle verdicts n with
    | none => throw (IO.userError s!"no oracle fact for {n}")
    | some o =>
      if !decide (o.verdict = .unknown) then
        throw (IO.userError s!"unexpected verdict for {n}")
      out := out ++ [o]
  pure out

def checkTaddPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/tadd.cir"
  let want32 ← IO.FS.readFile "tests/golden/Tadd32.lean"
  let want64 ← IO.FS.readFile "tests/golden/Tadd64.lean"
  let wantU32 ← IO.FS.readFile "tests/golden/UseTadd32.lean"
  let wantU64 ← IO.FS.readFile "tests/golden/UseTadd64.lean"
  let facts ← lookupFacts ["_Z4taddIiET_S0_S0_", "_Z4taddIlET_S0_S0_",
    "_Z10use_tadd32ii", "_Z10use_tadd64ll"]
  match runModulePipeline text facts with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected tadd: {msg}")
  | .ok [("_Z4taddIiET_S0_S0_", got32), ("_Z4taddIlET_S0_S0_", got64),
         ("_Z10use_tadd32ii", gotU32), ("_Z10use_tadd64ll", gotU64)] =>
    if got32 != want32 then
      throw (IO.userError "golden mismatch for 32-bit instantiation leaf")
    if got64 != want64 then
      throw (IO.userError "golden mismatch for 64-bit instantiation leaf")
    if gotU32 != wantU32 then
      throw (IO.userError "golden mismatch for use_tadd32 entry")
    if gotU64 != wantU64 then
      throw (IO.userError "golden mismatch for use_tadd64 entry")
    IO.println "PASS pipeline tadd (2 leaves + 2 entries, explicit unknown facts)"
    pure 4
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectTadd (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-tadd: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-tadd: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-tadd: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-tadd {name} [{code}]"
    pure 1

/-- Caller prologue shared by the adversarial entries (two allocas,
    loads into `%2`/`%3`; `w` selects the width). -/
def advPrologueT (ty : String) : String :=
  "    %0 = cir.alloca \"x\" : " ++ ty ++ "\n    %1 = cir.alloca \"y\" : " ++ ty ++ "\n    %2 = cir.load %0 : " ++ ty ++ ", " ++ ty ++ "\n    %3 = cir.load %1 : " ++ ty ++ ", " ++ ty ++ "\n"

/-- Caller epilogue: store the call result through `__retval`. -/
def advEpilogueT (ty r : String) : String :=
  "    %4 = cir.alloca \"__retval\" : " ++ ty ++ "\n    cir.store " ++ r ++ ", %4 : " ++ ty ++ ", " ++ ty ++ "\n    %5 = cir.load %4 : " ++ ty ++ ", " ++ ty ++ "\n    cir.return %5 : " ++ ty ++ "\n"

def advEntryT (name pty call : String) : String :=
  "module {\n  cir.func @" ++ name ++ "(%arg0: " ++ pty ++ " {llvm.noundef}, %arg1: " ++ pty ++ " {llvm.noundef}) -> " ++ pty ++ " attributes {\"nothrow\"} {\n"
  ++ advPrologueT pty ++ "    " ++ call ++ "\n" ++ advEpilogueT pty "%s" ++ "  }\n}"

/-- Call to an unknown mangled callee: generic call-shape rejection. -/
def advUnknownCallee : String :=
  advEntryT "tcall" "!s32i" "%s = cir.call @_Z4taddIiET_S0_S0_X(%2, %3) : (!s32i, !s32i) -> !s32i"

/-- Call to the known 32-bit instantiation with 3 params: dedicated
    template wrong-shape rejection (no admitted caller targets it). -/
def advWrongArity : String :=
  "module {\n  cir.func @tbada(%arg0: !s32i {llvm.noundef}, %arg1: !s32i {llvm.noundef}, %arg2: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n"
  ++ advPrologueT "!s32i"
  ++ "    %s = cir.call @_Z4taddIiET_S0_S0_(%2, %3) : (!s32i, !s32i) -> !s32i\n" ++ advEpilogueT "!s32i" "%s" ++ "  }\n}"

/-- Two call sites into a known instantiation: single-site pin rejects. -/
def advDoubleCall : String :=
  "module {\n  cir.func @tdouble(%arg0: !s32i {llvm.noundef}, %arg1: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n"
  ++ advPrologueT "!s32i"
  ++ "    %a = cir.call @_Z4taddIiET_S0_S0_(%2, %3) : (!s32i, !s32i) -> !s32i\n    %b = cir.call @_Z4taddIiET_S0_S0_(%2, %3) : (!s32i, !s32i) -> !s32i\n    %s = cir.add nsw %a, %b : !s32i\n" ++ advEpilogueT "!s32i" "%s" ++ "  }\n}"

/-- Call plus local arithmetic: arithmetic must live in the callee. -/
def advLocalArith : String :=
  "module {\n  cir.func @tarith(%arg0: !s32i {llvm.noundef}, %arg1: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n"
  ++ advPrologueT "!s32i"
  ++ "    %a = cir.call @_Z4taddIiET_S0_S0_(%2, %3) : (!s32i, !s32i) -> !s32i\n    %s = cir.add nsw %a, %2 : !s32i\n" ++ advEpilogueT "!s32i" "%s" ++ "  }\n}"

/-- 64-bit instantiation called at 32-bit width: the 64-bit gate pins
    `i64`, so the dedicated template rejection fires. -/
def advWrongWidth : String :=
  advEntryT "twidth" "!s32i" "%s = cir.call @_Z4taddIlET_S0_S0_(%2, %3) : (!s32i, !s32i) -> !s32i"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkTaddPipeline
  passed := passed + c0
  let r1 ← checkRejectTadd "tcall" advUnknownCallee .unknown
    "out-of-subset" "outside the admitted call shapes"
  passed := passed + r1
  let r2 ← checkRejectTadd "tbada" advWrongArity .unknown
    "out-of-subset" "calls a known template-instantiation leaf"
  passed := passed + r2
  let r3 ← checkRejectTadd "tdouble" advDoubleCall .unknown
    "out-of-subset" "calls a known template-instantiation leaf"
  passed := passed + r3
  let r4 ← checkRejectTadd "tarith" advLocalArith .unknown
    "out-of-subset" "calls a known template-instantiation leaf"
  passed := passed + r4
  let r5 ← checkRejectTadd "twidth" advWrongWidth .unknown
    "out-of-subset" "calls a known template-instantiation leaf"
  passed := passed + r5
  IO.println s!"GOLDENTADD-OK passed={passed}"

end GoldenTadd
