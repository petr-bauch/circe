-- Golden test for N4a: overload + namespace pipeline + rejection suite.
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenOverload.lean`
-- 1. Corpus pipelines: `tests/cir/overload_add.cir` (two `add` overloads
--    + the resolving entry) and `tests/cir/ns_add.cir` (namespaced leaf +
--    entry) validate via `validateModule` with explicit `unknown` facts
--    (int-only: pure, so the verdict is unchecked but the wiring entry
--    is still required) and emit byte-identical text to the five
--    `tests/golden/{OverloadAdd,Add3,UseAdd,NsAdd,UseNsAdd}.lean`.
--    The 2-`i32` leaves reuse the existing `.add` shape under their
--    mangled names (the gate is name-agnostic); the 3-`i32` leaf and the
--    two entries are new N4a shapes.
-- 2. Rejection suite: call to an unknown mangled callee, call to a
--    known leaf with the wrong arity, double call into a known leaf,
--    call plus local arithmetic — the first is generic, the rest hit
--    the dedicated overload wrong-shape rejection.
--    Mismatch policy: any in-subset divergence is P0; out-of-subset must
--    reject loudly.
import Circe.Validator

namespace GoldenOverload

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

def checkOverloadPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/overload_add.cir"
  let want2 ← IO.FS.readFile "tests/golden/OverloadAdd.lean"
  let want3 ← IO.FS.readFile "tests/golden/Add3.lean"
  let wantU ← IO.FS.readFile "tests/golden/UseAdd.lean"
  let facts ← lookupFacts ["_Z3addii", "_Z3addiii", "_Z7use_addii"]
  match runModulePipeline text facts with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected overload_add: {msg}")
  | .ok [("_Z3addii", got2), ("_Z3addiii", got3), ("_Z7use_addii", gotU)] =>
    if got2 != want2 then
      throw (IO.userError "golden mismatch for 2-i32 overload leaf")
    if got3 != want3 then
      throw (IO.userError "golden mismatch for 3-i32 overload leaf")
    if gotU != wantU then
      throw (IO.userError "golden mismatch for use_add entry")
    IO.println "PASS pipeline overload_add (2 leaves + entry, explicit unknown facts)"
    pure 3
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

def checkNsPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/ns_add.cir"
  let wantLeaf ← IO.FS.readFile "tests/golden/NsAdd.lean"
  let wantEntry ← IO.FS.readFile "tests/golden/UseNsAdd.lean"
  let facts ← lookupFacts ["_ZN2ns3addEii", "_Z10use_ns_addii"]
  match runModulePipeline text facts with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected ns_add: {msg}")
  | .ok [("_ZN2ns3addEii", gotLeaf), ("_Z10use_ns_addii", gotEntry)] =>
    if gotLeaf != wantLeaf then
      throw (IO.userError "golden mismatch for namespaced leaf")
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for use_ns_add entry")
    IO.println "PASS pipeline ns_add (leaf + entry, explicit unknown facts)"
    pure 2
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectOverload (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-overload: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-overload: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-overload: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-overload {name} [{code}]"
    pure 1

/-- Caller prologue shared by the adversarial entries (two `i32`
    allocas, loads into `%2`/`%3`). -/
def advPrologue : String :=
  "    %0 = cir.alloca \"x\" align(4) : !cir.ptr<!s32i>\n    %1 = cir.alloca \"y\" align(4) : !cir.ptr<!s32i>\n    %2 = cir.load %0 : !cir.ptr<!s32i>, !s32i\n    %3 = cir.load %1 : !cir.ptr<!s32i>, !s32i\n"

/-- Caller epilogue: store the call result through `__retval`. -/
def advEpilogue (r : String) : String :=
  "    %4 = cir.alloca \"__retval\" align(4) : !cir.ptr<!s32i>\n    cir.store " ++ r ++ ", %4 : !s32i, !cir.ptr<!s32i>\n    %5 = cir.load %4 : !cir.ptr<!s32i>, !s32i\n    cir.return %5 : !s32i\n"

def advEntry (name call : String) : String :=
  "module {\n  cir.func @" ++ name ++ "(%arg0: !s32i {llvm.noundef}, %arg1: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n"
  ++ advPrologue ++ "    " ++ call ++ "\n" ++ advEpilogue "%s" ++ "  }\n}"

/-- Call to an unknown mangled callee: generic call-shape rejection. -/
def advUnknownCallee : String :=
  advEntry "wcall" "%s = cir.call @_Z3addiiii(%2, %3) : (!s32i, !s32i) -> !s32i"

/-- Call to the known 3-`i32` leaf with 2 args: dedicated overload
    wrong-shape rejection (no admitted caller targets it). -/
def advWrongArity : String :=
  advEntry "wbad" "%s = cir.call @_Z3addiii(%2, %3) : (!s32i, !s32i) -> !s32i"

/-- Two call sites into a known leaf: single-site pin rejects. -/
def advDoubleCall : String :=
  "module {\n  cir.func @wdouble(%arg0: !s32i {llvm.noundef}, %arg1: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n"
  ++ advPrologue
  ++ "    %a = cir.call @_Z3addii(%2, %3) : (!s32i, !s32i) -> !s32i\n    %b = cir.call @_Z3addii(%2, %3) : (!s32i, !s32i) -> !s32i\n    %s = cir.add nsw %a, %b : !s32i\n" ++ advEpilogue "%s" ++ "  }\n}"

/-- Call plus local arithmetic: arithmetic must live in the callee. -/
def advLocalArith : String :=
  "module {\n  cir.func @warith(%arg0: !s32i {llvm.noundef}, %arg1: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n"
  ++ advPrologue
  ++ "    %a = cir.call @_Z3addii(%2, %3) : (!s32i, !s32i) -> !s32i\n    %s = cir.add nsw %a, %2 : !s32i\n" ++ advEpilogue "%s" ++ "  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkOverloadPipeline
  passed := passed + c0
  let c1 ← checkNsPipeline
  passed := passed + c1
  let r1 ← checkRejectOverload "wcall" advUnknownCallee .unknown
    "out-of-subset" "outside the admitted call shapes"
  passed := passed + r1
  let r2 ← checkRejectOverload "wbad" advWrongArity .unknown
    "out-of-subset" "calls a known overload leaf"
  passed := passed + r2
  let r3 ← checkRejectOverload "wdouble" advDoubleCall .unknown
    "out-of-subset" "calls a known overload leaf"
  passed := passed + r3
  let r4 ← checkRejectOverload "warith" advLocalArith .unknown
    "out-of-subset" "calls a known overload leaf"
  passed := passed + r4
  IO.println s!"GOLDENOVERLOAD-OK passed={passed}"

end GoldenOverload
