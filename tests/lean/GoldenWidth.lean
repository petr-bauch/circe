-- Golden test for S3b: 64-bit pipeline + misshapen-width rejection
-- suite.
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenWidth.lean`
-- 1. Corpus pipeline: `tests/cir/{add64,addu64}.cir` parse, validate
--    under their `tests/oracle/verdicts.txt` verdicts, and emit
--    byte-identical text to `tests/golden/{Add64,Addu64}.lean`.
-- 2. Rejection suite: width-mixed adds, `nsw`-less signed-64 adds, and
--    small-width (promotion) shapes hit exact codes + message
--    substrings, so the new `validate` branches are exercised.
--    Mismatch policy: any in-subset divergence is P0; out-of-subset
--    must reject loudly.
import Circe.Validator

def checkWidthPipeline (verdicts : List OracleFact) (cir golden func : String) :
    IO Nat := do
  let text ← IO.FS.readFile cir
  let want ← IO.FS.readFile golden
  let oracle ← match lookupOracle verdicts func with
    | none => throw (IO.userError s!"no oracle fact for {func}")
    | some o => pure o
  match runPipeline text oracle with
  | .ok got =>
    if got != want then
      throw (IO.userError s!"golden mismatch for {func}")
    IO.println s!"PASS pipeline {func}"
    pure 1
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected {func}: {msg}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectWidth (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-width: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-width: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-width: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-width {name} [{code}]"
    pure 1

/-- Width-mixed add (`i32` + `i64`): neither the 32- nor the 64-bit
    shape matches (mixed widths are `AssertFail` in `Eval`, so no shape
    may admit them). -/
def advWidthMix : String :=
  "module {\n  cir.func @wmix(%arg0: !s32i {llvm.noundef}, %arg1: !s64i {llvm.noundef}) -> !s64i attributes {\"nothrow\"} {\n    %5 = cir.add nsw %3, %4 : !s64i\n    cir.return %5 : !s64i\n  }\n}"

/-- Signed-64 add without `nsw` (wrapping signed overflow: UB, no
    translation exists). -/
def advMissingNsw64 : String :=
  "module {\n  cir.func @wnsw(%arg0: !s64i {llvm.noundef}, %arg1: !s64i {llvm.noundef}) -> !s64i attributes {\"nothrow\"} {\n    %5 = cir.add %3, %4 : !s64i\n    cir.return %5 : !s64i\n  }\n}"

/-- Small-width add (CIRGen promotes `i16` through `i32` casts: no
    native small-width arithmetic to model). -/
def advSmallWidth : String :=
  "module {\n  cir.func @wsmall(%arg0: !s16i {llvm.noundef}, %arg1: !s16i {llvm.noundef}) -> !s16i attributes {\"nothrow\"} {\n    %6 = cir.cast integral %5 : !s16i -> !s32i\n    %7 = cir.add nsw %4, %6 : !s32i\n    %8 = cir.cast integral %7 : !s32i -> !s16i\n    cir.return %8 : !s16i\n  }\n}"

def main : IO Unit := do
  let verdictText ← IO.FS.readFile "tests/oracle/verdicts.txt"
  let verdicts := parseOracleFacts verdictText
  let mut passed := 0
  let c1 ← checkWidthPipeline verdicts "tests/cir/add64.cir"
    "tests/golden/Add64.lean" "add64"
  passed := passed + c1
  let c2 ← checkWidthPipeline verdicts "tests/cir/addu64.cir"
    "tests/golden/Addu64.lean" "addu64"
  passed := passed + c2
  let r1 ← checkRejectWidth "wmix" advWidthMix .unknown
    "out-of-subset" "fragment"
  passed := passed + r1
  let r2 ← checkRejectWidth "wnsw" advMissingNsw64 .unknown
    "out-of-subset" "nsw"
  passed := passed + r2
  let r3 ← checkRejectWidth "wsmall" advSmallWidth .unknown
    "out-of-subset" "8/16-bit"
  passed := passed + r3
  IO.println s!"GOLDENWIDTH-OK passed={passed}"
