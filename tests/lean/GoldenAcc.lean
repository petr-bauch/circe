-- Golden test for M2b: value-ctor + trivial-dtor pipeline + rejection suite.
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenAcc.lean`
-- 1. Corpus pipeline: `tests/cir/acc_two.cir` (real CIRGen output with
--    `-fno-exceptions`: int-only entry + ctor/add/get/dtor leaves)
--    validates via `validateModule` with ONE oracle fact (the int-only
--    entry; leaf uniqueness comes from the `nonnull + dereferenceable +
--    noundef` attr triple) and emits byte-identical text to the five
--    `tests/golden/Acc*.lean` goldens.
-- 2. Rejection suite: missing ctor call (cleanup gate strictness),
--    unknown callee, non-trivial dtor (field store), wrapping add in
--    the `add` leaf, bare `Acc*` without the attr triple, `cir.try`
--    (no-EH absolute), ctor initializing to `1` (const-0 pin) — all loud
--    with exact codes + message substrings.
--    Mismatch policy: any in-subset divergence is P0; out-of-subset must
--    reject loudly.
import Circe.Validator

namespace GoldenAcc

def accTripleAttrs : String :=
  "{llvm.align = 4 : i64, llvm.dereferenceable = 4 : i64, llvm.nonnull, llvm.noundef}"

def accEntryFact : OracleFact := ⟨"_Z7acc_twoii", .unknown⟩

def checkAccPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/acc_two.cir"
  let wantTwo ← IO.FS.readFile "tests/golden/AccTwo.lean"
  let wantCtor ← IO.FS.readFile "tests/golden/AccCtor.lean"
  let wantAdd ← IO.FS.readFile "tests/golden/AccAdd.lean"
  let wantGet ← IO.FS.readFile "tests/golden/AccGet.lean"
  let wantDtor ← IO.FS.readFile "tests/golden/AccDtor.lean"
  match runModulePipeline text [accEntryFact] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected acc_two: {msg}")
  | .ok [("_Z7acc_twoii", gotTwo), ("_ZN3AccC2Ev", gotCtor),
         ("_ZN3Acc3addEi", gotAdd), ("_ZNK3Acc3getEv", gotGet),
         ("_ZN3AccD2Ev", gotDtor)] =>
    if gotTwo != wantTwo then
      throw (IO.userError "golden mismatch for acc_two entry")
    if gotCtor != wantCtor then
      throw (IO.userError "golden mismatch for ctor leaf")
    if gotAdd != wantAdd then
      throw (IO.userError "golden mismatch for add leaf")
    if gotGet != wantGet then
      throw (IO.userError "golden mismatch for get leaf")
    if gotDtor != wantDtor then
      throw (IO.userError "golden mismatch for dtor leaf")
    IO.println "PASS pipeline acc_two (entry + 4 leaves, one oracle fact)"
    pure 5
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectAcc (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-acc: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-acc: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-acc: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-acc {name} [{code}]"
    pure 1

/-- Entry missing the ctor call: the `cleanup` / `trap` scope is only
    exempt with the exact call multiset, so the general gate fires. -/
def advNoCtor : String :=
  "module {\n  cir.func @noctor(%arg0: !s32i {llvm.noundef}, %arg1: !s32i {llvm.noundef}) -> (!s32i {llvm.noundef}) attributes {\"nothrow\"} {\n"
  ++ "    cir.cleanup.scope {\n"
  ++ "      %a = cir.call @_ZN3Acc3addEi(%arg0, %arg0) : (!s32i, !s32i) -> ()\n"
  ++ "      %b = cir.call @_ZN3Acc3addEi(%arg0, %arg1) : (!s32i, !s32i) -> ()\n"
  ++ "      %g = cir.call @_ZNK3Acc3getEv(%arg0) : (!s32i) -> !s32i\n"
  ++ "      cir.return %g : !s32i\n"
  ++ "    } cleanup normal {\n"
  ++ "      cir.call @_ZN3AccD2Ev(%arg0) : (!s32i) -> ()\n"
  ++ "    }\n    cir.trap\n  }\n}"

/-- Unknown callee (no cleanup region): the generic call-shape branch. -/
def advUnknownAccCall : String :=
  "module {\n  cir.func @ufoo(%arg0: !s32i {llvm.noundef}, %arg1: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %r = cir.call @_ZN3Acc3fooEi(%arg0, %arg1) : (!s32i, !s32i) -> !s32i\n    cir.return %r : !s32i\n  }\n}"

/-- Non-trivial dtor: a field store is not the empty (no-op) body. -/
def advDtorStore : String :=
  "module {\n  cir.func @dstore(%arg0: !cir.ptr<!rec_Acc> " ++ accTripleAttrs ++ ") func_info<#cir.cxx_dtor<!rec_Acc>> attributes {\"nothrow\"} {\n"
  ++ "    %m = cir.get_member %arg0[0] {name = \"s\"} : !cir.ptr<!rec_Acc> -> !cir.ptr<!s32i>\n"
  ++ "    %z = cir.const #cir.int<0> : !s32i\n"
  ++ "    cir.store %z, %m : !s32i, !cir.ptr<!s32i>\n    cir.return\n  }\n}"

/-- Wrapping (non-`nsw`) add in the `add` leaf: signed overflow is UB. -/
def advAddWrap : String :=
  "module {\n  cir.func @awrap(%arg0: !cir.ptr<!rec_Acc> " ++ accTripleAttrs ++ ", %arg1: !s32i {llvm.noundef}) attributes {\"nothrow\"} {\n"
  ++ "    %m = cir.get_member %arg0[0] {name = \"s\"} : !cir.ptr<!rec_Acc> -> !cir.ptr<!s32i>\n"
  ++ "    %v = cir.load %m : !cir.ptr<!s32i>, !s32i\n"
  ++ "    %s = cir.add %v, %arg1 : !s32i\n    cir.store %s, %m : !s32i, !cir.ptr<!s32i>\n    cir.return\n  }\n}"

/-- Bare `Acc*` without the attr triple: uniqueness unestablished. -/
def advBareAcc : String :=
  "module {\n  cir.func @bacc(%arg0: !cir.ptr<!rec_Acc> {llvm.noundef}, %arg1: !s32i {llvm.noundef}) attributes {\"nothrow\"} {\n"
  ++ "    %m = cir.get_member %arg0[0] {name = \"s\"} : !cir.ptr<!rec_Acc> -> !cir.ptr<!s32i>\n"
  ++ "    %v = cir.load %m : !cir.ptr<!s32i>, !s32i\n"
  ++ "    %s = cir.add nsw %v, %arg1 : !s32i\n    cir.store %s, %m : !s32i, !cir.ptr<!s32i>\n    cir.return\n  }\n}"

/-- `cir.try` (EH) is absolutely rejected, even beside a valid scope. -/
def advTryAcc : String :=
  "module {\n  cir.func @tacc(%arg0: !s32i {llvm.noundef}, %arg1: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %r = cir.try {\n      cir.return %arg0 : !s32i\n    }\n    cir.return %r : !s32i\n  }\n}"

/-- Ctor initializing to `1`: the field-init value is pinned to `0`. -/
def advCtorOne : String :=
  "module {\n  cir.func @cone(%arg0: !cir.ptr<!rec_Acc> " ++ accTripleAttrs ++ ") func_info<#cir.cxx_ctor<!rec_Acc, default>> attributes {\"nothrow\"} {\n"
  ++ "    %m = cir.get_member %arg0[0] {name = \"s\"} : !cir.ptr<!rec_Acc> -> !cir.ptr<!s32i>\n"
  ++ "    %c = cir.const #cir.int<1> : !s32i\n"
  ++ "    cir.store %c, %m : !s32i, !cir.ptr<!s32i>\n    cir.return\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkAccPipeline
  passed := passed + c0
  let c1 ← checkRejectAcc "noctor" advNoCtor .unknown
    "out-of-subset" "cir.cleanup"
  passed := passed + c1
  let c2 ← checkRejectAcc "ufoo" advUnknownAccCall .unknown
    "out-of-subset" "outside the admitted call shapes"
  passed := passed + c2
  let c3 ← checkRejectAcc "dstore" advDtorStore .unknown
    "out-of-subset" "get_member"
  passed := passed + c3
  let c4 ← checkRejectAcc "awrap" advAddWrap .unknown
    "out-of-subset" "nsw"
  passed := passed + c4
  let c5 ← checkRejectAcc "bacc" advBareAcc .unknown
    "alias-reject" "single-reference triple"
  passed := passed + c5
  let c6 ← checkRejectAcc "tacc" advTryAcc .unknown
    "out-of-subset" "cir.try"
  passed := passed + c6
  let c7 ← checkRejectAcc "cone" advCtorOne .unknown
    "out-of-subset" "get_member"
  passed := passed + c7
  IO.println s!"GOLDENACC-OK passed={passed}"

end GoldenAcc
