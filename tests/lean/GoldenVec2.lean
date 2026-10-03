-- Golden test for M1a: `vec_copy_sum` pipeline + two-block rejection suite.
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenVec2.lean`
-- 1. Corpus pipeline: `tests/cir/vec_copy_sum.cir` parses, validates under its
--    `tests/oracle/verdicts.txt` verdict (`unknown`: no pointer params),
--    and emits byte-identical text to `tests/golden/VecCopySum.lean`.
-- 2. Rejection suite: two-block adversarial snippets hit exact codes +
--    message substrings (genuine double-`free`, heap-shape for
--    balanced-but-misshapen counts — M1d: leak allowed, so unbalanced
--    counts without loops are heap-shape, not missing-`free`), so every
--    new `validate` branch is exercised. Mismatch policy: any in-subset
--    divergence is P0; out-of-subset must reject loudly.
import Circe.Validator

namespace GoldenVec2

def checkVec2Pipeline (verdicts : List OracleFact) : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_copy_sum.cir"
  let want ← IO.FS.readFile "tests/golden/VecCopySum.lean"
  let oracle ← match lookupOracle verdicts "vec_copy_sum" with
    | none => throw (IO.userError "no oracle fact for vec_copy_sum")
    | some o => pure o
  match runPipeline text oracle with
  | .ok got =>
    if got != want then
      throw (IO.userError "golden mismatch for vec_copy_sum")
    IO.println "PASS pipeline vec_copy_sum"
    pure 1
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_copy_sum: {msg}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectVec2 (name text : String) (verdict : Verdict) (code substr : String) :
    IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-suite-vec2: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-suite-vec2: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-suite-vec2: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-vec2 {name} [{code}]"
    pure 1

def advTwoMallocNoFree : String :=
  "module {\n  cir.func @m2f0(%arg0: !u64i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    %p = cir.call @malloc(%arg0) : (!u64i) -> !cir.ptr<!u8i>\n    %q = cir.call @malloc(%arg0) : (!u64i) -> !cir.ptr<!u8i>\n    %c = cir.const #cir.int<0> : !u32i\n    cir.return %c : !u32i\n  }\n}"

def advThreeFree : String :=
  "module {\n  cir.func @f3m2(%arg0: !u64i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    %p = cir.call @malloc(%arg0) : (!u64i) -> !cir.ptr<!u8i>\n    %q = cir.call @malloc(%arg0) : (!u64i) -> !cir.ptr<!u8i>\n    cir.call @free(%p) : (!cir.ptr<!u8i>) -> ()\n    cir.call @free(%q) : (!cir.ptr<!u8i>) -> ()\n    cir.call @free(%p) : (!cir.ptr<!u8i>) -> ()\n    %c = cir.const #cir.int<0> : !u32i\n    cir.return %c : !u32i\n  }\n}"

def advBalancedNoLoop : String :=
  "module {\n  cir.func @f2m2nf(%arg0: !u64i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    %p = cir.call @malloc(%arg0) : (!u64i) -> !cir.ptr<!u8i>\n    %q = cir.call @malloc(%arg0) : (!u64i) -> !cir.ptr<!u8i>\n    cir.call @free(%p) : (!cir.ptr<!u8i>) -> ()\n    cir.call @free(%q) : (!cir.ptr<!u8i>) -> ()\n    %c = cir.const #cir.int<0> : !u32i\n    cir.return %c : !u32i\n  }\n}"

def advDoubleFreeOneBlock : String :=
  "module {\n  cir.func @f2m1(%arg0: !u64i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    %p = cir.call @malloc(%arg0) : (!u64i) -> !cir.ptr<!u8i>\n    cir.call @free(%p) : (!cir.ptr<!u8i>) -> ()\n    cir.call @free(%p) : (!cir.ptr<!u8i>) -> ()\n    %c = cir.const #cir.int<0> : !u32i\n    cir.return %c : !u32i\n  }\n}"

def advSingleNoLoop : String :=
  "module {\n  cir.func @m1f1nf(%arg0: !u64i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    %p = cir.call @malloc(%arg0) : (!u64i) -> !cir.ptr<!u8i>\n    cir.call @free(%p) : (!cir.ptr<!u8i>) -> ()\n    %c = cir.const #cir.int<0> : !u32i\n    cir.return %c : !u32i\n  }\n}"

def main : IO Unit := do
  let verdictText ← IO.FS.readFile "tests/oracle/verdicts.txt"
  let verdicts := parseOracleFacts verdictText
  let mut passed := 0
  let c1 ← checkVec2Pipeline verdicts
  passed := passed + c1
  let c2 ← checkRejectVec2 "m2f0" advTwoMallocNoFree .unknown
    "out-of-subset" "outside the admitted"
  passed := passed + c2
  let c3 ← checkRejectVec2 "f3m2" advThreeFree .unknown
    "out-of-subset" "double-`free`"
  passed := passed + c3
  let c4 ← checkRejectVec2 "f2m2nf" advBalancedNoLoop .unknown
    "out-of-subset" "outside the admitted"
  passed := passed + c4
  let c5 ← checkRejectVec2 "f2m1" advDoubleFreeOneBlock .unknown
    "out-of-subset" "double-`free`"
  passed := passed + c5
  let c6 ← checkRejectVec2 "m1f1nf" advSingleNoLoop .unknown
    "out-of-subset" "outside the admitted"
  passed := passed + c6
  IO.println s!"GOLDENVEC2-OK passed={passed}"

end GoldenVec2
