-- Golden test for S1: DAG-call pipeline + call rejection suite.
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenCalls.lean`
-- 1. Corpus pipeline: `tests/cir/add_caller.cir` and
--    `tests/cir/sum_caller.cir` parse, validate under their
--    `tests/oracle/verdicts.txt` verdicts, and emit byte-identical text
--    to `tests/golden/AddCaller.lean` / `SumCaller.lean`.
-- 2. Rejection suite: recursion (self-call), unknown callee, misshapen
--    caller (known callee, wrong shape), and call-in-leaf (recursive
--    `add`) hit exact codes + message substrings, so every new
--    `validate` branch is exercised. Mismatch policy: any in-subset
--    divergence is P0; out-of-subset must reject loudly.
import Circe.Validator

def checkCallPipeline (name cir golden : String) (verdict : Verdict) : IO Nat := do
  let text ← IO.FS.readFile cir
  let want ← IO.FS.readFile golden
  let verdictText ← IO.FS.readFile "tests/oracle/verdicts.txt"
  let verdicts := parseOracleFacts verdictText
  let oracle ← match lookupOracle verdicts name with
    | none => throw (IO.userError s!"no oracle fact for {name}")
    | some o => pure o
  if !decide (oracle.verdict = verdict) then
    throw (IO.userError s!"unexpected verdict for {name}")
  match runPipeline text oracle with
  | .ok got =>
    if got != want then
      throw (IO.userError s!"golden mismatch for {name}")
    IO.println s!"PASS pipeline {name}"
    pure 1
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected {name}: {msg}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectCall (name text : String) (verdict : Verdict) (code substr : String) :
    IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-calls: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-calls: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-calls: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-call {name} [{code}]"
    pure 1

/-- Self-call: recursion is rejected (DAG only). -/
def advRecursion : String :=
  "module {\n  cir.func @rec(%arg0: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %r = cir.call @rec(%arg0) : (!s32i) -> !s32i\n    cir.return %r : !s32i\n  }\n}"

/-- Unknown callee: outside the admitted leaf set. -/
def advUnknownCallee : String :=
  "module {\n  cir.func @uc(%arg0: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %r = cir.call @mystery(%arg0) : (!s32i) -> !s32i\n    cir.return %r : !s32i\n  }\n}"

/-- Misshapen caller: calls known leaf `@add` but with the wrong arity
    (two params instead of the three-param `add_caller` shape). -/
def advMisshapenCaller : String :=
  "module {\n  cir.func @mc(%arg0: !s32i {llvm.noundef}, %arg1: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %r = cir.call @add(%arg0, %arg1) : (!s32i, !s32i) -> !s32i\n    cir.return %r : !s32i\n  }\n}"

/-- Call in a leaf: recursive `add` (local `nsw` plus self-call) is
    rejected as recursion, never admitted as a leaf. -/
def advCallInLeaf : String :=
  "module {\n  cir.func @add(%arg0: !s32i {llvm.noundef}, %arg1: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %s = cir.add nsw %arg0, %arg1 : !s32i\n    %r = cir.call @add(%s, %arg1) : (!s32i, !s32i) -> !s32i\n    cir.return %r : !s32i\n  }\n}"

/-- Callee-shaped call with a pointer return outside `choose`: escape. -/
def advCallEscape : String :=
  "module {\n  cir.func @ce(%arg0: !cir.ptr<!s32i> {llvm.noalias, llvm.noundef}) -> !cir.ptr<!s32i> attributes {\"nothrow\"} {\n    %r = cir.call @idptr(%arg0) : (!cir.ptr<!s32i>) -> !cir.ptr<!s32i>\n    cir.return %r : !cir.ptr<!s32i>\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c1 ← checkCallPipeline "add_caller" "tests/cir/add_caller.cir"
    "tests/golden/AddCaller.lean" .unknown
  passed := passed + c1
  let c2 ← checkCallPipeline "sum_caller" "tests/cir/sum_caller.cir"
    "tests/golden/SumCaller.lean" .noalias
  passed := passed + c2
  let c3 ← checkRejectCall "rec" advRecursion .unknown
    "out-of-subset" "recursive"
  passed := passed + c3
  let c4 ← checkRejectCall "uc" advUnknownCallee .unknown
    "out-of-subset" "outside the admitted call shapes"
  passed := passed + c4
  let c5 ← checkRejectCall "mc" advMisshapenCaller .unknown
    "out-of-subset" "outside the admitted call shapes"
  passed := passed + c5
  let c6 ← checkRejectCall "add" advCallInLeaf .unknown
    "out-of-subset" "recursive"
  passed := passed + c6
  let c7 ← checkRejectCall "ce" advCallEscape .noalias
    "out-of-subset" "outside the admitted call shapes"
  passed := passed + c7
  IO.println s!"GOLDENCALLS-OK passed={passed}"
