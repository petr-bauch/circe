-- Golden test for M1b: `vec_alloc_u64` pipeline + `u64`-heap rejection suite.
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenVec64.lean`
-- 1. Corpus pipeline: `tests/cir/vec_alloc_u64.cir` parses, validates under
--    its `tests/oracle/verdicts.txt` verdict (`unknown`: no pointer params),
--    and emits byte-identical text to `tests/golden/VecAllocU64.lean`.
-- 2. Rejection suite: `u64`-heap adversarial snippets hit exact codes +
--    message substrings (genuine double-`free`, heap-shape for
--    balanced-but-misshapen counts — M1d: leak allowed, so `malloc`
--    without `free` and without loops is heap-shape, not missing-`free`),
--    plus Eval-level mixed-width `AssertFail` checks (S3b policy:
--    `u32` block × `u64` index and back).
--    Mismatch policy: any in-subset divergence is P0; out-of-subset must
--    reject loudly.
import Circe.Validator

def checkVec64Pipeline (verdicts : List OracleFact) : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_alloc_u64.cir"
  let want ← IO.FS.readFile "tests/golden/VecAllocU64.lean"
  let oracle ← match lookupOracle verdicts "vec_alloc_u64" with
    | none => throw (IO.userError "no oracle fact for vec_alloc_u64")
    | some o => pure o
  match runPipeline text oracle with
  | .ok got =>
    if got != want then
      throw (IO.userError "golden mismatch for vec_alloc_u64")
    IO.println "PASS pipeline vec_alloc_u64"
    pure 1
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_alloc_u64: {msg}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectVec64 (name text : String) (verdict : Verdict) (code substr : String) :
    IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-suite-vec64: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-suite-vec64: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-suite-vec64: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-vec64 {name} [{code}]"
    pure 1

/-- Mixed-width heap access must be `AssertFail` (S3b policy), never
    silently modeled: `u32` block read with a `u64` index. -/
def checkEvalMixGet : IO Nat := do
  let env : Env := [("v", .vecVal ⟨[1, 2], false⟩)]
  match evalExpr (.vget "v" (.lit (.u64 0))) env with
  | .error .AssertFail =>
    IO.println "PASS eval-mix-get [AssertFail]"
    pure 1
  | r =>
    throw (IO.userError s!"eval-mix-get: expected AssertFail, got {(repr r).pretty}")

/-- Mixed-width heap access must be `AssertFail`: `u64` block written
    with `u32` index/value. -/
def checkEvalMixSet : IO Nat := do
  let env : Env := [("v", .vecVal64 ⟨[1, 2], false⟩)]
  match evalStmt (.vset "v" (.lit (.u32 0)) (.lit (.u32 9))) env with
  | .error .AssertFail =>
    IO.println "PASS eval-mix-set [AssertFail]"
    pure 1
  | r =>
    throw (IO.userError s!"eval-mix-set: expected AssertFail, got {(repr r).pretty}")

def advMissingFree64 : String :=
  "module {\n  cir.func @mf64(%arg0: !u64i {llvm.noundef}) -> !u64i attributes {\"nothrow\"} {\n    %p = cir.call @malloc(%arg0) : (!u64i) -> !cir.ptr<!u8i>\n    %c = cir.const #cir.int<0> : !u64i\n    cir.return %c : !u64i\n  }\n}"

def advDoubleFree64 : String :=
  "module {\n  cir.func @df64(%arg0: !u64i {llvm.noundef}) -> !u64i attributes {\"nothrow\"} {\n    %p = cir.call @malloc(%arg0) : (!u64i) -> !cir.ptr<!u8i>\n    cir.call @free(%p) : (!cir.ptr<!u8i>) -> ()\n    cir.call @free(%p) : (!cir.ptr<!u8i>) -> ()\n    %c = cir.const #cir.int<0> : !u64i\n    cir.return %c : !u64i\n  }\n}"

def advHeapShape64 : String :=
  "module {\n  cir.func @hs64(%arg0: !u64i {llvm.noundef}) -> !u64i attributes {\"nothrow\"} {\n    %p = cir.call @malloc(%arg0) : (!u64i) -> !cir.ptr<!u8i>\n    cir.call @free(%p) : (!cir.ptr<!u8i>) -> ()\n    %c = cir.const #cir.int<0> : !u64i\n    cir.return %c : !u64i\n  }\n}"

def main : IO Unit := do
  let verdictText ← IO.FS.readFile "tests/oracle/verdicts.txt"
  let verdicts := parseOracleFacts verdictText
  let mut passed := 0
  let c1 ← checkVec64Pipeline verdicts
  passed := passed + c1
  let c2 ← checkRejectVec64 "mf64" advMissingFree64 .unknown
    "out-of-subset" "outside the admitted"
  passed := passed + c2
  let c3 ← checkRejectVec64 "df64" advDoubleFree64 .unknown
    "out-of-subset" "double-`free`"
  passed := passed + c3
  let c4 ← checkRejectVec64 "hs64" advHeapShape64 .unknown
    "out-of-subset" "outside the admitted"
  passed := passed + c4
  let c5 ← checkEvalMixGet
  passed := passed + c5
  let c6 ← checkEvalMixSet
  passed := passed + c6
  IO.println s!"GOLDENVEC64-OK passed={passed}"
