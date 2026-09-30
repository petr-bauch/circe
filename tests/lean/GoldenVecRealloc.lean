-- Golden test for M1c: `vec_realloc` pipeline + grown-heap rejection suite.
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenVecRealloc.lean`
-- 1. Corpus pipeline: `tests/cir/vec_realloc.cir` parses, validates under its
--    `tests/oracle/verdicts.txt` verdict (`unknown`: no pointer params),
--    and emits byte-identical text to `tests/golden/VecRealloc.lean`.
-- 2. Rejection suite: `realloc` adversarial snippets hit exact codes +
--    message substrings (`realloc(p, 0)` and `realloc(NULL, n)` spellings,
--    double-`realloc`, missing-`free` with `realloc`, heap-shape for
--    `malloc`+`free` without `realloc`), plus an Eval-level width check
--    (`vrealloc` with a non-`u32` size is `AssertFail`: u32 sizes only).
--    Mismatch policy: any in-subset divergence is P0; out-of-subset must
--    reject loudly.
import Circe.Validator

def checkVecReallocPipeline (verdicts : List OracleFact) : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_realloc.cir"
  let want ← IO.FS.readFile "tests/golden/VecRealloc.lean"
  let oracle ← match lookupOracle verdicts "vec_realloc" with
    | none => throw (IO.userError "no oracle fact for vec_realloc")
    | some o => pure o
  match runPipeline text oracle with
  | .ok got =>
    if got != want then
      throw (IO.userError "golden mismatch for vec_realloc")
    IO.println "PASS pipeline vec_realloc"
    pure 1
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_realloc: {msg}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectVecRealloc (name text : String) (verdict : Verdict) (code substr : String) :
    IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-suite-vecrealloc: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-suite-vecrealloc: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-suite-vecrealloc: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-vecrealloc {name} [{code}]"
    pure 1

/-- `vrealloc` with a non-`u32` size is `AssertFail` (M1c: u32 sizes only,
    like `vec`; other widths never silently resize). -/
def checkEvalVreallocWidth : IO Nat := do
  let env : Env := [("v", .vecVal ⟨[1, 2], false⟩)]
  match evalStmt (.vrealloc "v" (.lit (.u64 0))) env with
  | .error .AssertFail =>
    IO.println "PASS eval-vrealloc-width [AssertFail]"
    pure 1
  | r =>
    throw (IO.userError s!"eval-vrealloc-width: expected AssertFail, got {(repr r).pretty}")

/-- `realloc(p, 0)` (= `free`) spelling: rejected, never admitted. -/
def advReallocZero : String :=
  "module {\n  cir.func @rz(%arg0: !u64i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    %p = cir.call @malloc(%arg0) : (!u64i) -> !cir.ptr<!u8i>\n    %z = cir.const #cir.int<0> : !u64i\n    %q = cir.call @realloc(%p, %z) : (!cir.ptr<!u8i>, !u64i) -> !cir.ptr<!u8i>\n    cir.call @free(%q) : (!cir.ptr<!u8i>) -> ()\n    %c = cir.const #cir.int<0> : !u32i\n    cir.return %c : !u32i\n  }\n}"

/-- `realloc(NULL, n)` (= `malloc`) spelling: no `malloc`, rejected. -/
def advReallocNull : String :=
  "module {\n  cir.func @rn(%arg0: !u64i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    %z = cir.const #cir.int<0> : !u64i\n    %q = cir.call @realloc(%z, %arg0) : (!u64i, !u64i) -> !cir.ptr<!u8i>\n    cir.call @free(%q) : (!cir.ptr<!u8i>) -> ()\n    %c = cir.const #cir.int<0> : !u32i\n    cir.return %c : !u32i\n  }\n}"

/-- Two `realloc` growths: outside the single-growth shape. -/
def advReallocTwice : String :=
  "module {\n  cir.func @rr(%arg0: !u64i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    %p = cir.call @malloc(%arg0) : (!u64i) -> !cir.ptr<!u8i>\n    %q = cir.call @realloc(%p, %arg0) : (!cir.ptr<!u8i>, !u64i) -> !cir.ptr<!u8i>\n    %r = cir.call @realloc(%q, %arg0) : (!cir.ptr<!u8i>, !u64i) -> !cir.ptr<!u8i>\n    cir.call @free(%r) : (!cir.ptr<!u8i>) -> ()\n    %c = cir.const #cir.int<0> : !u32i\n    cir.return %c : !u32i\n  }\n}"

/-- `malloc` + `realloc` without `free`: the leak gate fires first. -/
def advReallocNoFree : String :=
  "module {\n  cir.func @rnf(%arg0: !u64i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    %p = cir.call @malloc(%arg0) : (!u64i) -> !cir.ptr<!u8i>\n    %q = cir.call @realloc(%p, %arg0) : (!cir.ptr<!u8i>, !u64i) -> !cir.ptr<!u8i>\n    %c = cir.const #cir.int<0> : !u32i\n    cir.return %c : !u32i\n  }\n}"

/-- Balanced `malloc` + `free` without `realloc` or loops: heap-shape
    (the admitted heap shapes are exactly `vec_alloc` / `vec_copy_sum` /
    `vec_alloc_u64` / `vec_realloc`). -/
def advMallocFreeNoRealloc : String :=
  "module {\n  cir.func @m1f1nr(%arg0: !u64i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    %p = cir.call @malloc(%arg0) : (!u64i) -> !cir.ptr<!u8i>\n    cir.call @free(%p) : (!cir.ptr<!u8i>) -> ()\n    %c = cir.const #cir.int<0> : !u32i\n    cir.return %c : !u32i\n  }\n}"

def main : IO Unit := do
  let verdictText ← IO.FS.readFile "tests/oracle/verdicts.txt"
  let verdicts := parseOracleFacts verdictText
  let mut passed := 0
  let c1 ← checkVecReallocPipeline verdicts
  passed := passed + c1
  let c2 ← checkRejectVecRealloc "rz" advReallocZero .unknown
    "out-of-subset" "`realloc(p, 0)`"
  passed := passed + c2
  let c3 ← checkRejectVecRealloc "rn" advReallocNull .unknown
    "out-of-subset" "`realloc(NULL, n)`"
  passed := passed + c3
  let c4 ← checkRejectVecRealloc "rr" advReallocTwice .unknown
    "out-of-subset" "one `realloc`"
  passed := passed + c4
  let c5 ← checkRejectVecRealloc "rnf" advReallocNoFree .unknown
    "out-of-subset" "matching `free`"
  passed := passed + c5
  let c6 ← checkRejectVecRealloc "m1f1nr" advMallocFreeNoRealloc .unknown
    "out-of-subset" "`vec_realloc`"
  passed := passed + c6
  let c7 ← checkEvalVreallocWidth
  passed := passed + c7
  IO.println s!"GOLDENVECREALLOC-OK passed={passed}"
