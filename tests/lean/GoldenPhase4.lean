-- Golden test for Phase 4: `.cir` → validated CoreIR → emitted Lean,
-- plus the rejection suite.
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenPhase4.lean`
-- 1. Corpus pipeline: each `tests/cir/*.cir` parses, validates under its
--    `tests/oracle/verdicts.txt` verdict, and emits byte-identical text to
--    `tests/golden/*.lean` (`struct_by_value` must reject with
--    `outOfSubset` mentioning struct fields).
-- 2. Rejection suite: adversarial inline CIR snippets hit exact codes +
--    message substrings (alias/escape/oob/out-of-subset), so every
--    `validate` branch is exercised.
import Circe.Validator

def checkPipeline (verdicts : List OracleFact) (cir golden func : String) :
    IO Nat := do
  let text ← IO.FS.readFile cir
  let want ← IO.FS.readFile golden
  let oracle ← match lookupOracle verdicts func with
    | none => throw (IO.userError s!"no oracle fact for {func}")
    | some o => pure o
  match runPipeline text oracle with
  | .ok got =>
    if got != want then
      throw (IO.userError s!"golden mismatch for {func} ({cir} vs {golden})")
    IO.println s!"PASS pipeline {func}"
    pure 1
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected {func}: {msg}")

def checkStructReject (verdicts : List OracleFact) : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/struct_by_value.cir"
  let oracle ← match lookupOracle verdicts "translate" with
    | none => throw (IO.userError "no oracle fact for translate")
    | some o => pure o
  match runPipeline text oracle with
  | .ok _ => throw (IO.userError "struct corpus unexpectedly accepted")
  | .error msg =>
    if !containsSubstr msg "out-of-subset" then
      throw (IO.userError s!"struct: expected out-of-subset, got: {msg}")
    if !containsSubstr msg "get_member" then
      throw (IO.userError s!"struct: expected struct-field message, got: {msg}")
    IO.println "PASS reject struct_by_value [out-of-subset]"
    pure 1

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr` (`code == ""` skips the code check, for parse failures). -/
def checkReject (name text : String) (verdict : Verdict) (code substr : String) :
    IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-suite: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if code != "" && !containsSubstr msg code then
      throw (IO.userError s!"reject-suite: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-suite: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject {name} [{code}]"
    pure 1

def advNoRestrict : String :=
  "module {\n  cir.func @bad(%arg0: !cir.ptr<!s32i> {llvm.noundef}) attributes {\"nothrow\"} {\n    cir.return\n  }\n}"

def advChooseBody : String :=
  "  cir.func @ch(%arg0: !cir.bool {llvm.noundef}, %arg1: !cir.ptr<!s32i> {llvm.noalias, llvm.noundef}, %arg2: !cir.ptr<!s32i> {llvm.noalias, llvm.noundef}) -> !cir.ptr<!s32i> attributes {\"nothrow\"} {\n    %t = cir.ternary(%arg0) : (!cir.bool) -> !cir.ptr<!s32i>\n    cir.return %t : !cir.ptr<!s32i>\n  }"

def advEscape : String :=
  "module {\n  cir.func @esc(%arg0: !cir.ptr<!s32i> {llvm.noalias, llvm.noundef}) -> !cir.ptr<!s32i> attributes {\"nothrow\"} {\n    cir.return %arg0 : !cir.ptr<!s32i>\n  }\n}"

def advOob : String :=
  "module {\n  cir.func @idx(%arg0: !cir.ptr<!u32i> {llvm.noalias, llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    %p = cir.ptr_stride %arg0, %c0 : (!cir.ptr<!u32i>, !u64i) -> !cir.ptr<!u32i>\n    %v = cir.load %p : !cir.ptr<!u32i>, !u32i\n    cir.return %v : !u32i\n  }\n}"

def advTry : String :=
  "module {\n  cir.func @add(%arg0: !s32i {llvm.noundef}, %arg1: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %s = cir.add nsw %arg0, %arg1 : !s32i\n    %t = cir.try %s : !s32i\n    cir.return %t : !s32i\n  }\n}"

def advVoidStar : String :=
  "module {\n  cir.func @vw(%arg0: !cir.ptr<!cir.void> {llvm.noalias, llvm.noundef}) attributes {\"nothrow\"} {\n    cir.return\n  }\n}"

def advIntPtrCast : String :=
  "module {\n  cir.func @ipc(%arg0: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %p = cir.cast ptr_to_int %arg0 : !s32i -> !s32i\n    cir.return %p : !s32i\n  }\n}"

def advFloat : String :=
  "module {\n  cir.func @fl(%arg0: !cir.float {llvm.noundef}) -> !cir.float attributes {\"nothrow\"} {\n    cir.return %arg0 : !cir.float\n  }\n}"

def advCall : String :=
  "module {\n  cir.func @callee(%arg0: !s32i {llvm.noundef}, %arg1: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %r = cir.call @add(%arg0, %arg1) : (!s32i, !s32i) -> !s32i\n    cir.return %r : !s32i\n  }\n}"

def advBranchInAdd : String :=
  "module {\n  cir.func @br(%arg0: !s32i {llvm.noundef}, %arg1: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %t = cir.ternary(%arg0) : (!cir.bool) -> !s32i\n    cir.return %t : !s32i\n  }\n}"

def advAddText : String :=
  "module {\n  cir.func @add(%arg0: !s32i {llvm.noundef}, %arg1: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n    %s = cir.add nsw %arg0, %arg1 : !s32i\n    cir.return %s : !s32i\n  }\n}"

def main : IO Unit := do
  let verdictText ← IO.FS.readFile "tests/oracle/verdicts.txt"
  let verdicts := parseOracleFacts verdictText
  let mut passed := 0
  let c1 ← checkPipeline verdicts
    "tests/cir/add.cir" "tests/golden/Add.lean" "add"
  passed := passed + c1
  let c2 ← checkPipeline verdicts
    "tests/cir/incr_ptr.cir" "tests/golden/Incr.lean" "incr"
  passed := passed + c2
  let c3 ← checkPipeline verdicts
    "tests/cir/choose_ptr.cir" "tests/golden/Choose.lean" "choose"
  passed := passed + c3
  let c4 ← checkPipeline verdicts
    "tests/cir/sum_array.cir" "tests/golden/SumArray.lean" "sum_array"
  passed := passed + c4
  let c5 ← checkStructReject verdicts
  passed := passed + c5
  let c6 ← checkReject "bad" advNoRestrict .noalias
    "alias-reject" "__restrict__"
  passed := passed + c6
  let c7 ← checkReject "ch" advChooseBody .mayAlias
    "alias-reject" "mayAlias"
  passed := passed + c7
  let c8 ← checkReject "ch" advChooseBody .unknown
    "alias-reject" "inconclusive"
  passed := passed + c8
  let c9 ← checkReject "esc" advEscape .noalias
    "escape-reject" "borrow-return"
  passed := passed + c9
  let c10 ← checkReject "idx" advOob .noalias
    "oob-possible" "length-paired"
  passed := passed + c10
  let c11 ← checkReject "add" advTry .unknown
    "out-of-subset" "exception"
  passed := passed + c11
  let c12 ← checkReject "vw" advVoidStar .noalias
    "out-of-subset" "void*"
  passed := passed + c12
  let c13 ← checkReject "ipc" advIntPtrCast .unknown
    "out-of-subset" "cast"
  passed := passed + c13
  let c14 ← checkReject "fl" advFloat .unknown
    "out-of-subset" "float"
  passed := passed + c14
  let c15 ← checkReject "callee" advCall .unknown
    "out-of-subset" "call"
  passed := passed + c15
  let c16 ← checkReject "br" advBranchInAdd .unknown
    "out-of-subset" "admitted"
  passed := passed + c16
  -- oracle wiring case needs a mismatched fact: redo with name "other"
  let oracleOther : OracleFact := ⟨"other", .unknown⟩
  match runPipeline advAddText oracleOther with
  | .ok _ => throw (IO.userError "wiring case unexpectedly accepted")
  | .error msg =>
    if !containsSubstr msg "wiring" then
      throw (IO.userError s!"wiring case: expected wiring message, got: {msg}")
    IO.println "PASS reject wiring [out-of-subset]"
    passed := passed + 1
  match runPipeline "this is not CIR at all" ⟨"x", .unknown⟩ with
  | .ok _ => throw (IO.userError "garbage unexpectedly accepted")
  | .error msg =>
    if !containsSubstr msg "parse failed" then
      throw (IO.userError s!"parse case: expected parse failure, got: {msg}")
    IO.println "PASS reject garbage [parse]"
    passed := passed + 1
  IO.println s!"GOLDEN4-OK passed={passed}"
