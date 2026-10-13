-- Golden test for the first writer admission (F1): `alias_reborrow`
-- pipeline + rejection suite.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenReborrow.main`).
-- 1. Corpus pipeline: `tests/cir/alias_reborrow.cir` (real CIRGen
--    output: one single-reference root, three writer allocas, two
--    `nsw` adds consuming the `1`/`2` consts in order, L2-disjoint
--    ranges over one F0-resolved address) validates via
--    `runModulePipeline` with NO oracle facts (uniqueness comes from
--    the `nonnull + dereferenceable + noundef` attr triple, the M2a
--    single-reference precedent) and emits byte-identical text to
--    `tests/golden/Reborrow.lean`.
-- 2. Rejection suite (adversaries by corpus transformation, so the
--    skeleton stays real): wrong const (`1`/`3`, still
--    sequential-writer-shaped — the deferred message, not admission),
--    wrapping adds (same), the overlapping `alias_cond` corpus (not
--    reborrow-shaped at all — the generic fragment message), a bare
--    root pointer without the attr triple (`alias-reject` before
--    shapes are consulted), and the `incr` leaf (shape-exactness:
--    one add is not the two-add fusion).
import Circe.Validator

namespace GoldenReborrow

def reborrowTriple : String :=
  "{llvm.align = 4 : i64, llvm.dereferenceable = 4 : i64, llvm.nonnull, llvm.noundef}"

def checkReborrowPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/alias_reborrow.cir"
  let want ← IO.FS.readFile "tests/golden/Reborrow.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected reborrow: {msg}")
  | .ok [("_Z14alias_reborrowRi", got)] =>
    if got != want then
      throw (IO.userError "golden mismatch for reborrow entry")
    IO.println "PASS pipeline reborrow (no oracle facts)"
    pure 1
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectReborrow (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-reborrow: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-reborrow: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-reborrow: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-reborrow {name} [{code}]"
    pure 1

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkReborrowPipeline
  passed := passed + c0
  let corpus ← IO.FS.readFile "tests/cir/alias_reborrow.cir"
  -- Wrong const (`1`/`3`): still sequential-writer-shaped, so the
  -- deferred message — but never admission (the fused `x + 1 + 2`
  -- would lie about the second increment).
  let r1 ← checkRejectReborrow "_Z14alias_reborrowRi"
    (corpus.replace "cir.const #cir.int<2> : !s32i"
      "cir.const #cir.int<3> : !s32i") .unknown
    "out-of-subset" "sequential writers"
  passed := passed + r1
  -- Wrapping adds: the `nsw` pin is load-bearing (overflow must be
  -- loud) — caught earlier by the wrapping-arithmetic guard with its
  -- own actionable message (never reaches the writer branches).
  let r2 ← checkRejectReborrow "_Z14alias_reborrowRi"
    (corpus.replace "cir.add nsw" "cir.add") .unknown
    "out-of-subset" "wrapping arithmetic"
  passed := passed + r2
  -- Overlapping writers: not reborrow-shaped at all (L2 comparison
  -- fails) — the generic fragment message.
  let cond ← IO.FS.readFile "tests/cir/alias_cond.cir"
  let r3 ← checkRejectReborrow "_Z10alias_condRiS_b" cond .unknown
    "out-of-subset" "admitted Phase-4 fragment"
  passed := passed + r3
  -- Bare root pointer without the attr triple: the alias discipline
  -- rejects before shapes are even consulted.
  let r4 ← checkRejectReborrow "_Z14alias_reborrowRi"
    (corpus.replace reborrowTriple "{llvm.noundef}") .unknown
    "alias-reject" "single-reference triple"
  passed := passed + r4
  -- Shape-exactness the other way: the single-add `incr` leaf is not
  -- the two-add fusion.
  let incrText ← IO.FS.readFile "tests/cir/incr_ptr.cir"
  match parseModule incrText with
  | none =>
    throw (IO.userError "reject-reborrow: incr corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "incr") with
    | none => throw (IO.userError "reject-reborrow: incr not found")
    | some raw =>
      if isReborrowShape raw then
        throw (IO.userError "reject-reborrow: incr wrongly reborrow-shaped")
      IO.println "PASS reject-reborrow incr-not-reborrow [shape-exact]"
      passed := passed + 1
  IO.println s!"GOLDENREBORROW-OK passed={passed}"

end GoldenReborrow
