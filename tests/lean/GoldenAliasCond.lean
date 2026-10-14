-- Golden test for the unknown-verdict branch-writer admission (G3/S3):
-- `alias_cond` pipeline + rejection suite.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenAliasCond.main`).
-- 1. Corpus pipeline: `tests/cir/alias_cond.cir` (real CIRGen output:
--    two single-reference-triple params plus `bool`, one
--    scope-wrapped `cir.if` firing the first writer run, the second
--    run at top level, five loads) validates via `runPipeline` under
--    the `unknown` verdict and emits byte-identical text to
--    `tests/golden/AliasCond.lean` (and the spec twin).
-- 2. Rejection suite (adversaries by corpus transformation, so the
--    skeleton stays real): missing triple (rule 1), wrapping adds
--    (the `nsw` pin is load-bearing), wrong const (`2`/`3` — the
--    dataflow pin is gone, so the verdict gate fires), and the
--    `cond_pair` leaf (shape-exactness: seven loads plus no triple
--    is not the open-contract shape).
import Circe.Emit
import Circe.Emit.AliasCond
import Circe.Validator

namespace GoldenAliasCond

def aliasCondUnknown : OracleFact := ⟨"_Z10alias_condRiS_b", .unknown⟩
def aliasCondMayAlias : OracleFact := ⟨"_Z10alias_condRiS_b", .mayAlias⟩

def checkAliasCondPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/alias_cond.cir"
  let want ← IO.FS.readFile "tests/golden/AliasCond.lean"
  match runPipeline text aliasCondUnknown with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected alias_cond: {msg}")
  | .ok got =>
    if got != want then
      throw (IO.userError s!"golden mismatch for alias_cond")
    IO.println s!"PASS pipeline alias_cond"
    pure 1

def checkAliasCondSpecPipeline : IO Nat := do
  let want ← IO.FS.readFile "tests/golden/AliasCond_Spec.lean"
  match emitSpec aliasCondFunc with
  | .error (.notFragment msg) =>
    throw (IO.userError s!"spec unexpectedly rejected alias_cond: {msg}")
  | .ok got =>
    if got != want then
      throw (IO.userError s!"spec golden mismatch for alias_cond")
    IO.println s!"PASS pipeline alias_cond_spec"
    pure 1

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. Variants derive from the real corpus by string
    surgery (no new corpus files; the gate is text-level). -/
def checkRejectAliasCond (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-aliascond: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-aliascond: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-aliascond: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-aliascond {name} [{code}]"
    pure 1

def aliasCondBase : IO String :=
  IO.FS.readFile "tests/cir/alias_cond.cir"

/-- Missing triple on writer `p`: rule-1 param check. -/
def advNoTripleP : IO String := do
  let base ← aliasCondBase
  pure (base.replace
    "%arg0: !cir.ptr<!s32i> {llvm.align = 4 : i64, llvm.dereferenceable = 4 : i64, llvm.nonnull, llvm.noundef}"
    "%arg0: !cir.ptr<!s32i> {llvm.align = 4 : i64, llvm.noundef}")

/-- Wrapping adds: the `nsw` pin is load-bearing. -/
def advWrappingAdds : IO String := do
  let base ← aliasCondBase
  pure (base.replace "cir.add nsw" "cir.add")

/-- Wrong const (`2`/`3`): the dataflow pin no longer matches, so no
    open contract — and since the triple params never reach the
    verdict gate (`oracleParams` excludes the triple), the generic
    fragment tail fires. -/
def advWrongConst : IO String := do
  let base ← aliasCondBase
  pure (base.replace "cir.const #cir.int<2> : !s32i"
    "cir.const #cir.int<3> : !s32i")

/-- The `noalias` `cond_pair` leaf is not the open-contract shape
    (shape-exactness, checked at the predicate level, both
    directions). -/
def checkCondPairNotAliasCond : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/cond_pair.cir"
  match parseModule text with
  | none =>
    throw (IO.userError s!"reject-aliascond: cond_pair corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "cond_pair") with
    | none => throw (IO.userError s!"reject-aliascond: cond_pair not found")
    | some raw =>
      if isAliasCondShape raw then
        throw (IO.userError s!"reject-aliascond: cond_pair wrongly aliascond-shaped")
      match parseModule (← aliasCondBase) with
      | none => throw (IO.userError s!"reject-aliascond: alias_cond corpus failed to parse")
      | some m2 =>
        match m2.funcs.find? (fun f => f.name == "_Z10alias_condRiS_b") with
        | none => throw (IO.userError s!"reject-aliascond: alias_cond not found")
        | some raw2 =>
          if isCondPairShape raw2 then
            throw (IO.userError s!"reject-aliascond: alias_cond wrongly cond-shaped")
          IO.println s!"PASS reject-aliascond condpair-not-aliascond [shape-exact]"
          pure 1

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkAliasCondPipeline
  passed := passed + c0
  let c1 ← checkAliasCondSpecPipeline
  passed := passed + c1
  -- Verdict-independence: `mayAlias` emits the identical open contract.
  let text ← IO.FS.readFile "tests/cir/alias_cond.cir"
  let want ← IO.FS.readFile "tests/golden/AliasCond.lean"
  match runPipeline text aliasCondMayAlias with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected alias_cond under mayAlias: {msg}")
  | .ok got =>
    if got != want then
      throw (IO.userError s!"golden mismatch for alias_cond under mayAlias")
    IO.println s!"PASS pipeline alias_cond_mayalias"
    passed := passed + 1
  let v1 ← advNoTripleP
  let r1 ← checkRejectAliasCond "_Z10alias_condRiS_b" v1 .unknown
    "alias-reject" "uniqueness cannot be established"
  passed := passed + r1
  let v2 ← advWrappingAdds
  let r2 ← checkRejectAliasCond "_Z10alias_condRiS_b" v2 .unknown
    "out-of-subset" "wrapping arithmetic"
  passed := passed + r2
  let v3 ← advWrongConst
  let r3 ← checkRejectAliasCond "_Z10alias_condRiS_b" v3 .unknown
    "out-of-subset" "admitted Phase-4 fragment"
  passed := passed + r3
  let c5 ← checkCondPairNotAliasCond
  passed := passed + c5
  IO.println s!"GOLDENALIASCOND-OK passed={passed}"

end GoldenAliasCond
