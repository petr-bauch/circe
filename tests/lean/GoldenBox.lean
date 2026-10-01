-- Golden test for M2c: `new` / `delete` as ownership ops pipeline +
-- rejection suite.
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenBox.lean`
-- 1. Corpus pipeline: `tests/cir/box_through.cir` (real CIRGen output with
--    `-fno-exceptions`: int-only entry + `@_Znwm` / `@_ZdlPvm`
--    declarations) validates via `validateModule` with ONE oracle fact
--    (the int-only entry, like the M2b entry) and emits byte-identical
--    text to `tests/golden/BoxThrough.lean`.
-- 2. Leak acceptance (M1d): the 1-`new` / 0-`delete` spelling validates
--    to the byte-identical golden (leak = forgetting a value, sound).
-- 3. Rejection suite: missing `new` (exemption strictness), unguarded
--    `delete` (exemption strictness), double-`delete` (affine gate),
--    wrong size const (shape pin), `cir.try` (no-EH absolute) — all loud
--    with exact codes + message substrings.
-- 4. Token checks: use-after-`delete` read + double-`delete` are
--    `AssertFail` at the value level.
--    Mismatch policy: any in-subset divergence is P0; out-of-subset must
--    reject loudly.
import Circe.Validator

def boxEntryFact : OracleFact := ⟨"_Z11box_throughi", .unknown⟩

def checkBoxPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/box_through.cir"
  let want ← IO.FS.readFile "tests/golden/BoxThrough.lean"
  match runModulePipeline text [boxEntryFact] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected box_through: {msg}")
  | .ok [("_Z11box_throughi", got)] =>
    if got != want then
      throw (IO.userError "golden mismatch for box_through entry")
    IO.println "PASS pipeline box_through (entry, one oracle fact)"
    pure 1
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectBox (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-box: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-box: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-box: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-box {name} [{code}]"
    pure 1

/-- Leak acceptance (M1d): 1 `new`, 0 `delete`, no `cleanup` — validates
    to the byte-identical golden. -/
def checkLeakBox : IO Nat := do
  let leakText :=
    "module {\n  cir.func @_Z11box_throughi(%arg0: !s32i {llvm.noundef}) -> (!s32i {llvm.noundef}) attributes {\"nothrow\"} {\n"
    ++ "    %s = cir.const #cir.int<4> : !u64i\n"
    ++ "    %p = cir.call @_Znwm(%s) {allocsize = array<i32: 0>, builtin} : (!u64i) -> (!cir.ptr<!void>)\n"
    ++ "    %b = cir.cast bitcast %p : !cir.ptr<!void> -> !cir.ptr<!rec_Box>\n"
    ++ "    %m = cir.get_member %b[0] {name = \"x\"} : !cir.ptr<!rec_Box> -> !cir.ptr<!s32i>\n"
    ++ "    cir.store %arg0, %m : !s32i, !cir.ptr<!s32i>\n"
    ++ "    %v = cir.load %m : !cir.ptr<!s32i>, !s32i\n"
    ++ "    cir.return %v : !s32i\n  }\n}"
    ++ "  cir.func private @_Znwm(!u64i) -> (!cir.ptr<!void>) attributes {allocsize = array<i32: 0>} loc(#loc)\n}"
  let want ← IO.FS.readFile "tests/golden/BoxThrough.lean"
  match runPipeline leakText boxEntryFact with
  | .error msg =>
    throw (IO.userError s!"leak spelling unexpectedly rejected: {msg}")
  | .ok got =>
    if got != want then
      throw (IO.userError s!"leak spelling golden mismatch:\n{got}")
    IO.println "PASS leak box_through (1 new, 0 delete, same golden)"
    pure 1

/-- Token check: the value-level op must be `AssertFail`. -/
def checkTokenBox (name : String) (got : Result α) : IO Nat := do
  match got with
  | .error .AssertFail =>
    IO.println s!"PASS token-box {name} [AssertFail]"
    pure 1
  | _ => throw (IO.userError s!"token-box: {name} unexpectedly succeeded")

/-- Missing `new`: a `cleanup`-scoped delete without `_Znwm` is not
    exempt, so the general `cleanup` gate fires. -/
def advNoNew : String :=
  "module {\n  cir.func @nnew(%arg0: !s32i {llvm.noundef}) -> (!s32i {llvm.noundef}) attributes {\"nothrow\"} {\n"
  ++ "    %n = cir.const #cir.ptr<null> : !cir.ptr<!rec_Box>\n"
  ++ "    %c = cir.cmp ne %arg0, %n : !cir.ptr<!rec_Box>\n"
  ++ "    cir.if %c {\n"
  ++ "      cir.cleanup.scope {\n        cir.yield\n      } cleanup normal {\n"
  ++ "        %b = cir.cast bitcast %arg0 : !s32i -> !cir.ptr<!void>\n"
  ++ "        %s = cir.const #cir.int<4> : !u64i\n"
  ++ "        cir.call @_ZdlPvm(%b, %s) : (!cir.ptr<!void>, !u64i) -> ()\n"
  ++ "        cir.yield\n      }\n    }\n"
  ++ "    cir.return %arg0 : !s32i\n  }\n}"

/-- Unguarded `delete`: `cleanup`-scoped delete without the null guard
    (`cir.cmp ne` + `#cir.ptr<null>` + `cir.if`) is not exempt. -/
def advNoGuard : String :=
  "module {\n  cir.func @ngrd(%arg0: !s32i {llvm.noundef}) -> (!s32i {llvm.noundef}) attributes {\"nothrow\"} {\n"
  ++ "    %s = cir.const #cir.int<4> : !u64i\n"
  ++ "    %p = cir.call @_Znwm(%s) : (!u64i) -> (!cir.ptr<!void>)\n"
  ++ "    %b = cir.cast bitcast %p : !cir.ptr<!void> -> !cir.ptr<!rec_Box>\n"
  ++ "    %m = cir.get_member %b[0] {name = \"x\"} : !cir.ptr<!rec_Box> -> !cir.ptr<!s32i>\n"
  ++ "    cir.store %arg0, %m : !s32i, !cir.ptr<!s32i>\n"
  ++ "    cir.cleanup.scope {\n      cir.yield\n    } cleanup normal {\n"
  ++ "      %d = cir.cast bitcast %b : !cir.ptr<!rec_Box> -> !cir.ptr<!void>\n"
  ++ "      cir.call @_ZdlPvm(%d, %s) : (!cir.ptr<!void>, !u64i) -> ()\n"
  ++ "      cir.yield\n    }\n"
  ++ "    %v = cir.load %m : !cir.ptr<!s32i>, !s32i\n"
  ++ "    cir.return %v : !s32i\n  }\n}"

/-- Double-`delete`: two sized deletes for one `new` (no `cleanup`, so
    the affine gate — not the `cleanup` gate — fires). -/
def advDoubleDelete : String :=
  "module {\n  cir.func @ddel(%arg0: !s32i {llvm.noundef}) -> (!s32i {llvm.noundef}) attributes {\"nothrow\"} {\n"
  ++ "    %s = cir.const #cir.int<4> : !u64i\n"
  ++ "    %p = cir.call @_Znwm(%s) : (!u64i) -> (!cir.ptr<!void>)\n"
  ++ "    %b = cir.cast bitcast %p : !cir.ptr<!void> -> !cir.ptr<!rec_Box>\n"
  ++ "    %m = cir.get_member %b[0] {name = \"x\"} : !cir.ptr<!rec_Box> -> !cir.ptr<!s32i>\n"
  ++ "    cir.store %arg0, %m : !s32i, !cir.ptr<!s32i>\n"
  ++ "    %d = cir.cast bitcast %b : !cir.ptr<!rec_Box> -> !cir.ptr<!void>\n"
  ++ "    cir.call @_ZdlPvm(%d, %s) : (!cir.ptr<!void>, !u64i) -> ()\n"
  ++ "    cir.call @_ZdlPvm(%d, %s) : (!cir.ptr<!void>, !u64i) -> ()\n"
  ++ "    %v = cir.load %m : !cir.ptr<!s32i>, !s32i\n"
  ++ "    cir.return %v : !s32i\n  }\n}"

/-- Wrong size const: an 8-byte `new` is not the 4-byte `Box` shape
    (leak-style, no `cleanup`, so the shape pin — not the `cleanup`
    gate — fires). -/
def advWrongSize : String :=
  "module {\n  cir.func @wsz(%arg0: !s32i {llvm.noundef}) -> (!s32i {llvm.noundef}) attributes {\"nothrow\"} {\n"
  ++ "    %s = cir.const #cir.int<8> : !u64i\n"
  ++ "    %p = cir.call @_Znwm(%s) : (!u64i) -> (!cir.ptr<!void>)\n"
  ++ "    %b = cir.cast bitcast %p : !cir.ptr<!void> -> !cir.ptr<!rec_Box>\n"
  ++ "    %m = cir.get_member %b[0] {name = \"x\"} : !cir.ptr<!rec_Box> -> !cir.ptr<!s32i>\n"
  ++ "    cir.store %arg0, %m : !s32i, !cir.ptr<!s32i>\n"
  ++ "    %v = cir.load %m : !cir.ptr<!s32i>, !s32i\n"
  ++ "    cir.return %v : !s32i\n  }\n}"

/-- `cir.try` (EH) is absolutely rejected, even beside a valid shape. -/
def advTryBox : String :=
  "module {\n  cir.func @tbox(%arg0: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %r = cir.try {\n      cir.return %arg0 : !s32i\n    }\n    cir.return %r : !s32i\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkBoxPipeline
  passed := passed + c0
  let c1 ← checkLeakBox
  passed := passed + c1
  let c2 ← checkRejectBox "nnew" advNoNew .unknown
    "out-of-subset" "cir.cleanup"
  passed := passed + c2
  let c3 ← checkRejectBox "ngrd" advNoGuard .unknown
    "out-of-subset" "cir.cleanup"
  passed := passed + c3
  let c4 ← checkRejectBox "ddel" advDoubleDelete .unknown
    "out-of-subset" "double-`delete`"
  passed := passed + c4
  let c5 ← checkRejectBox "wsz" advWrongSize .unknown
    "out-of-subset" "box_through"
  passed := passed + c5
  let c6 ← checkRejectBox "tbox" advTryBox .unknown
    "out-of-subset" "cir.try"
  passed := passed + c6
  let c7 ← checkTokenBox "use-after-delete" (boxGet ⟨5, true⟩)
  passed := passed + c7
  let c8 ← checkTokenBox "double-delete" (boxFree ⟨5, true⟩)
  passed := passed + c8
  IO.println s!"GOLDENBOX-OK passed={passed}"
