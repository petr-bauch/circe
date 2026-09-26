-- Golden test for Phase 7: `vec_alloc` pipeline + heap rejection suite.
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenPhase7.lean`
-- 1. Corpus pipeline: `tests/cir/vec_alloc.cir` parses, validates under its
--    `tests/oracle/verdicts.txt` verdict (`unknown`: no pointer params),
--    and emits byte-identical text to `tests/golden/VecAlloc.lean`.
-- 2. Rejection suite: heap-specific adversarial snippets hit exact codes +
--    message substrings (missing-`free`, double-`free`, heap-shape), so
--    every new `validate` branch is exercised. Mismatch policy: any
--    in-subset divergence is P0; out-of-subset must reject loudly.
import Circe.Validator

def checkVecPipeline (verdicts : List OracleFact) : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_alloc.cir"
  let want ← IO.FS.readFile "tests/golden/VecAlloc.lean"
  let oracle ← match lookupOracle verdicts "vec_alloc" with
    | none => throw (IO.userError "no oracle fact for vec_alloc")
    | some o => pure o
  match runPipeline text oracle with
  | .ok got =>
    if got != want then
      throw (IO.userError "golden mismatch for vec_alloc")
    IO.println "PASS pipeline vec_alloc"
    pure 1
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_alloc: {msg}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkReject7 (name text : String) (verdict : Verdict) (code substr : String) :
    IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-suite7: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-suite7: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-suite7: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject7 {name} [{code}]"
    pure 1

def advMissingFree : String :=
  "module {\n  cir.func @mf(%arg0: !u64i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    %p = cir.call @malloc(%arg0) : (!u64i) -> !cir.ptr<!u8i>\n    %c = cir.const #cir.int<0> : !u32i\n    cir.return %c : !u32i\n  }\n}"

def advDoubleFree : String :=
  "module {\n  cir.func @df(%arg0: !u64i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    %p = cir.call @malloc(%arg0) : (!u64i) -> !cir.ptr<!u8i>\n    cir.call @free(%p) : (!cir.ptr<!u8i>) -> ()\n    cir.call @free(%p) : (!cir.ptr<!u8i>) -> ()\n    %c = cir.const #cir.int<0> : !u32i\n    cir.return %c : !u32i\n  }\n}"

def advHeapShape : String :=
  "module {\n  cir.func @hs(%arg0: !u64i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    %p = cir.call @malloc(%arg0) : (!u64i) -> !cir.ptr<!u8i>\n    cir.call @free(%p) : (!cir.ptr<!u8i>) -> ()\n    %c = cir.const #cir.int<0> : !u32i\n    cir.return %c : !u32i\n  }\n}"

def advFreeOnly : String :=
  "module {\n  cir.func @fo(%arg0: !cir.ptr<!u32i> {llvm.noalias, llvm.noundef}) attributes {\"nothrow\"} {\n    cir.call @free(%arg0) : (!cir.ptr<!u32i>) -> ()\n    cir.return\n  }\n}"

def advVecPtrRet : String :=
  "module {\n  cir.func @vr(%arg0: !u64i {llvm.noundef}) -> !cir.ptr<!u32i> attributes {\"nothrow\"} {\n    %p = cir.call @malloc(%arg0) : (!u64i) -> !cir.ptr<!u8i>\n    cir.call @free(%p) : (!cir.ptr<!u8i>) -> ()\n    cir.return %p : !cir.ptr<!u8i>\n  }\n}"

def main : IO Unit := do
  let verdictText ← IO.FS.readFile "tests/oracle/verdicts.txt"
  let verdicts := parseOracleFacts verdictText
  let mut passed := 0
  let c1 ← checkVecPipeline verdicts
  passed := passed + c1
  let c2 ← checkReject7 "mf" advMissingFree .unknown
    "out-of-subset" "matching `free`"
  passed := passed + c2
  let c3 ← checkReject7 "df" advDoubleFree .unknown
    "out-of-subset" "twice"
  passed := passed + c3
  let c4 ← checkReject7 "hs" advHeapShape .unknown
    "out-of-subset" "outside the admitted"
  passed := passed + c4
  let c5 ← checkReject7 "fo" advFreeOnly .noalias
    "out-of-subset" "free"
  passed := passed + c5
  let c6 ← checkReject7 "vr" advVecPtrRet .unknown
    "out-of-subset" "admitted"
  passed := passed + c6
  IO.println s!"GOLDEN7-OK passed={passed}"
