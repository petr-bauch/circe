-- Golden test for N2a: read-only sharing discipline, rejection side.
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenReadOnly.lean`
-- 1. Writer + reader still rejects loudly (N2a keeps the line that N2b will
--    turn into per-cause messages): a two-pointer shape outside the admitted
--    `choose` borrow-return form rejects under a `noalias` verdict
--    (out-of-subset: no two-reader shape is admitted yet), under `mayAlias`
--    (alias-reject: oracle reports), and without `llvm.noalias` text
--    (alias-reject: rule 1).
-- 2. `derivedNoalias` stays `false` on the two-reader shape (text-gate
--    admission is N2b/N2c work; N2a is the model-side discipline in
--    `Circe.ReadOnly`, imported here so the test holds the integration).
-- Mismatch policy: any in-subset divergence is P0; out-of-subset must
-- reject loudly.
import Circe.Validator
import Circe.ReadOnly

def checkRejectReadOnly (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-readonly: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-readonly: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-readonly: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-readonly {name} [{code}]"
    pure 1

/-- Two live pointers (writer + reader) with full `noalias` text but no
    admitted shape: even a clean oracle verdict cannot admit what has no
    footprint proof (N2a admits no two-reader `Func` yet). -/
def advWriterReaderNoalias : String :=
  "module {\n  cir.func @wr(%arg0: !cir.ptr<!u32i> {llvm.noalias, llvm.noundef}, %arg1: !cir.ptr<!u32i> {llvm.noalias, llvm.noundef}, %arg2: !u32i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    %c = cir.const 0 : !u32i\n    cir.return %c : !u32i\n  }\n}"

/-- Same shape, oracle inconclusive: the verdict gate fires first. -/
def advWriterReaderMayAlias : String := advWriterReaderNoalias

/-- Same shape, reader text missing `llvm.noalias`: rule-1 gate fires. -/
def advWriterReaderBare : String :=
  "module {\n  cir.func @wr(%arg0: !cir.ptr<!u32i> {llvm.noalias, llvm.noundef}, %arg1: !cir.ptr<!u32i> {llvm.noundef}, %arg2: !u32i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n    %c = cir.const 0 : !u32i\n    cir.return %c : !u32i\n  }\n}"

/-- Two-reader `RawFunc`: `derivedNoalias` must stay `false` (only the
    `choose` two-pointer shape derives; text-gate admission is N2b/N2c). -/
def twoReaderRaw : RawFunc :=
  { name := "sum_two", params :=
    [{ name := "a", ctype := "!cir.ptr<!u32i>", noalias := true, singleRef := false },
     { name := "b", ctype := "!cir.ptr<!u32i>", noalias := true, singleRef := false },
     { name := "n", ctype := "!u32i", noalias := false, singleRef := false }],
    ret := "!u32i",
    text := "cir.func @sum_two(%arg0: !cir.ptr<!u32i> {llvm.noalias}, %arg1: !cir.ptr<!u32i> {llvm.noalias}) { cir.return }" }

/-- Compile-time linkage: the canonical two-reader footprint proof lives
    in `Circe.ReadOnly` (its theorems are verified by `lake env lean` in
    `check.sh`; this def fails to compile if the footprint drifts). -/
theorem _readonlyFootprintLinked : LayoutNoAlias [("a", 1, 1), ("b", 0, 0)] :=
  twoShared_noalias

def main : IO Unit := do
  let mut passed := 0
  -- N2b re-categorized this case: two live pointers outside `choose` now
  -- report the writer+reader cause instead of the generic fragment message.
  let c1 ← checkRejectReadOnly "wr" advWriterReaderNoalias .noalias
    "alias-reject" "writer+reader"
  passed := passed + c1
  let c2 ← checkRejectReadOnly "wr" advWriterReaderMayAlias .mayAlias
    "alias-reject" "reports `mayAlias`"
  passed := passed + c2
  let c3 ← checkRejectReadOnly "wr" advWriterReaderBare .unknown
    "alias-reject" "without `__restrict__`"
  passed := passed + c3
  if derivedNoalias twoReaderRaw != false then
    throw (IO.userError "reject-readonly: two-reader shape must not derive (N2b/N2c work)")
  IO.println "PASS reject-readonly two-reader no-derive"
  passed := passed + 1
  let _ := _readonlyFootprintLinked
  IO.println "PASS readonly two-reader footprint linked"
  passed := passed + 1
  IO.println s!"GOLDENREADONLY-OK passed={passed}"
