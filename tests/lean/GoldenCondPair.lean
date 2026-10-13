-- Golden test for the branch-writer admission (G2b): `cond_pair`
-- pipeline + rejection suite.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenCondPair.main`).
-- 1. Corpus pipeline: `tests/cir/cond_pair.cir` (real CIRGen output:
--    two `__restrict__` params plus `bool`, one scope-wrapped
--    `cir.if` firing the first writer run, the second run at top
--    level) validates via `runPipeline` under the `noalias` verdict
--    and emits byte-identical text to `tests/golden/CondPair.lean`.
-- 2. Rejection suite (adversaries by corpus transformation, so the
--    skeleton stays real): inconclusive/`mayAlias` verdicts (attrs
--    are claims, the verdict confirms), missing `__restrict__`
--    (rule 1), wrapping adds (the `nsw` pin is load-bearing),
--    wrong const (`1`/`3` — the dataflow pin is gone, so the
--    pair-check exemption is gone too), and the `wr_pair` leaf
--    (shape-exactness: no branch is not the branch-writer).
import Circe.Emit
import Circe.Validator

namespace GoldenCondPair

def condPairFact : OracleFact := ⟨"cond_pair", .noalias⟩

def checkCondPairPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/cond_pair.cir"
  let want ← IO.FS.readFile "tests/golden/CondPair.lean"
  match runPipeline text condPairFact with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected cond_pair: {msg}")
  | .ok got =>
    if got != want then
      throw (IO.userError s!"golden mismatch for cond_pair")
    IO.println s!"PASS pipeline cond_pair"
    pure 1

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. Variants derive from the real corpus by string
    surgery (no new corpus files; the gate is text-level). -/
def checkRejectCondPair (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-condpair: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-condpair: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-condpair: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-condpair {name} [{code}]"
    pure 1

def condPairBase : IO String :=
  IO.FS.readFile "tests/cir/cond_pair.cir"

/-- Missing `__restrict__` on writer `p`: rule-1 param check. -/
def advNoRestrictP : IO String := do
  let base ← condPairBase
  pure (base.replace
    "%arg0: !cir.ptr<!s32i> {llvm.noalias, llvm.noundef}"
    "%arg0: !cir.ptr<!s32i> {llvm.noundef}")

/-- Wrapping adds: the `nsw` pin is load-bearing. -/
def advWrappingAdds : IO String := do
  let base ← condPairBase
  pure (base.replace "cir.add nsw" "cir.add")

/-- Wrong const (`1`/`3`): the dataflow pin no longer matches. -/
def advWrongConst : IO String := do
  let base ← condPairBase
  pure (base.replace "cir.const #cir.int<2> : !s32i"
    "cir.const #cir.int<3> : !s32i")

/-- The unbranched `wr_pair` leaf is not the branch-writer
    (shape-exactness, checked at the predicate level). -/
def checkWrPairNotCondPair : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/wr_pair.cir"
  match parseModule text with
  | none =>
    throw (IO.userError s!"reject-condpair: wr_pair corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "wr_pair") with
    | none => throw (IO.userError s!"reject-condpair: wr_pair not found")
    | some raw =>
      if isCondPairShape raw then
        throw (IO.userError s!"reject-condpair: wr_pair wrongly cond-shaped")
      IO.println s!"PASS reject-condpair wr-pair-not-condpair [shape-exact]"
      pure 1

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkCondPairPipeline
  passed := passed + c0
  let base ← condPairBase
  let r1 ← checkRejectCondPair "cond_pair" base .unknown
    "alias-reject" "oracle is inconclusive"
  passed := passed + r1
  let r1b ← checkRejectCondPair "cond_pair" base .mayAlias
    "alias-reject" "explicit `noalias` verdict"
  passed := passed + r1b
  let v2 ← advNoRestrictP
  let r2 ← checkRejectCondPair "cond_pair" v2 .noalias
    "alias-reject" "uniqueness cannot be established"
  passed := passed + r2
  let v3 ← advWrappingAdds
  let r3 ← checkRejectCondPair "cond_pair" v3 .noalias
    "out-of-subset" "wrapping arithmetic"
  passed := passed + r3
  let v4 ← advWrongConst
  let r4 ← checkRejectCondPair "cond_pair" v4 .noalias
    "alias-reject" "live pointer parameters"
  passed := passed + r4
  let c5 ← checkWrPairNotCondPair
  passed := passed + c5
  IO.println s!"GOLDENCONDPAIR-OK passed={passed}"

end GoldenCondPair
