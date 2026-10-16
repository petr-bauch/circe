-- Golden test for the second writer admission (L1b):
-- `alias_reborrow34` pipeline + rejection suite.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenReborrow34.main`).
-- 1. Corpus pipeline: `tests/cir/alias_reborrow34.cir` (real CIRGen
--    output: one single-reference root, three writer allocas, two
--    `nsw` adds consuming the `3`/`4` consts in order, L2-disjoint
--    ranges over one F0-resolved address) validates via
--    `runModulePipeline` with NO oracle facts and emits byte-identical
--    text to `tests/golden/Reborrow34.lean`.
-- 2. Rejection suite: wrong const (`3`/`5`, still
--    sequential-writer-shaped — the deferred message, not admission),
--    wrapping adds (same), the `alias_reborrow` F1 entry is not
--    34-shaped and vice versa (const-use pins disagree), a bare
--    root pointer without the attr triple (`alias-reject`), and the
--    `incr` leaf (shape-exactness).
-- 3. Admission row: `validateModule` on the 34 corpus admits the
--    entry (single row) — the deferred branch no longer fires for
--    this shape.
import Circe.Validator

namespace GoldenReborrow34

def reborrowTriple : String :=
  "{llvm.align = 4 : i64, llvm.dereferenceable = 4 : i64, llvm.nonnull, llvm.noundef}"

def checkReborrow34Pipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/alias_reborrow34.cir"
  let want ← IO.FS.readFile "tests/golden/Reborrow34.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected reborrow34: {msg}")
  | .ok [("_Z16alias_reborrow34Ri", got)] =>
    if got != want then
      throw (IO.userError "golden mismatch for reborrow34 entry")
    IO.println "PASS pipeline reborrow34 (no oracle facts)"
    pure 1
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectReborrow34 (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-reborrow34: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-reborrow34: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-reborrow34: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-reborrow34 {name} [{code}]"
    pure 1

/-- Shape probe: `name` in `file` must (or must not) match `shape`. -/
def checkShape34 (file entry : String) (shape : RawFunc → Bool)
    (want : Bool) (tag : String) : IO Nat := do
  let text ← IO.FS.readFile file
  match parseModule text with
  | none =>
    throw (IO.userError s!"reject-reborrow34: {file} failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == entry) with
    | none => throw (IO.userError s!"reject-reborrow34: {entry} not found")
    | some raw =>
      if shape raw != want then
        throw (IO.userError s!"reject-reborrow34: {tag} shape verdict wrong")
      IO.println s!"PASS reject-reborrow34 {tag} [shape-exact]"
      pure 1

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkReborrow34Pipeline
  passed := passed + c0
  let corpus ← IO.FS.readFile "tests/cir/alias_reborrow34.cir"
  -- Wrong const (`3`/`5`): still sequential-writer-shaped, so the
  -- deferred message — but never admission (the fused `x + 3 + 4`
  -- would lie about the second increment).
  let r1 ← checkRejectReborrow34 "_Z16alias_reborrow34Ri"
    (corpus.replace "cir.const #cir.int<4> : !s32i"
      "cir.const #cir.int<5> : !s32i") .unknown
    "out-of-subset" "sequential writers"
  passed := passed + r1
  -- Wrapping adds: the `nsw` pin is load-bearing — caught earlier
  -- by the wrapping-arithmetic guard.
  let r2 ← checkRejectReborrow34 "_Z16alias_reborrow34Ri"
    (corpus.replace "cir.add nsw" "cir.add") .unknown
    "out-of-subset" "wrapping arithmetic"
  passed := passed + r2
  -- Bare root pointer without the attr triple.
  let r3 ← checkRejectReborrow34 "_Z16alias_reborrow34Ri"
    (corpus.replace reborrowTriple "{llvm.noundef}") .unknown
    "alias-reject" "single-reference triple"
  passed := passed + r3
  -- Cross-exactness: the F1 entry is not 34-shaped and vice versa.
  let r4 ← checkShape34 "tests/cir/alias_reborrow.cir" "_Z14alias_reborrowRi"
    isReborrow34Shape false "reborrow-not-34-shaped"
  passed := passed + r4
  let r5 ← checkShape34 "tests/cir/alias_reborrow34.cir" "_Z16alias_reborrow34Ri"
    isReborrowShape false "reborrow34-not-reborrow-shaped"
  passed := passed + r5
  let r6 ← checkShape34 "tests/cir/alias_reborrow34.cir" "_Z16alias_reborrow34Ri"
    isReborrow34Shape true "reborrow34-accepts"
  passed := passed + r6
  -- Shape-exactness: the single-add `incr` leaf is not the fusion.
  let incrText ← IO.FS.readFile "tests/cir/incr_ptr.cir"
  match parseModule incrText with
  | none =>
    throw (IO.userError "reject-reborrow34: incr corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "incr") with
    | none => throw (IO.userError "reject-reborrow34: incr not found")
    | some raw =>
      if isReborrow34Shape raw then
        throw (IO.userError "reject-reborrow34: incr wrongly 34-shaped")
      IO.println "PASS reject-reborrow34 incr-not-34 [shape-exact]"
      passed := passed + 1
  -- Admission row: the 34 corpus validates to a single admission
  -- (the deferred branch no longer fires for this shape).
  match validateModule corpus [] with
  | [(n, .ok _)] =>
    if n != "_Z16alias_reborrow34Ri" then
      throw (IO.userError s!"reject-reborrow34: admitted {n} != reborrow34")
    IO.println "PASS reborrow34-admit _Z16alias_reborrow34Ri"
    passed := passed + 1
  | rows =>
    throw (IO.userError s!"reject-reborrow34: expected single admission, got {rows.length} rows")
  IO.println s!"GOLDENREBORROW34-OK passed={passed}"

end GoldenReborrow34
