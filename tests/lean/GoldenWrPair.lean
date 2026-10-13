-- Golden test for the writer-pair admission (G2): `wr_pair`
-- pipeline + rejection suite.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenWrPair.main`).
-- 1. Corpus pipeline: `tests/cir/wr_pair.cir` (real CIRGen output:
--    two `__restrict__` params, two writer runs with the `1`/`2`
--    consts feeding the in-order stores into the in-order param
--    cells) validates via `runPipeline` under the `noalias` verdict
--    and emits byte-identical text to `tests/golden/WrPair.lean`.
-- 2. Rejection suite (adversaries by corpus transformation, so the
--    skeleton stays real): inconclusive/`mayAlias` verdicts (attrs
--    are claims, the verdict confirms), missing `__restrict__`
--    (rule 1), wrapping adds (the `nsw` pin is load-bearing —
--    overflow must be loud), wrong const (`1`/`3` — the dataflow
--    pin,Pair check rejects since the shape no longer matches), and
--    the `incr` leaf (shape-exactness: one writer is not the pair).
import Circe.Emit
import Circe.Validator

namespace GoldenWrPair

def wrPairFact : OracleFact := ⟨"wr_pair", .noalias⟩

def checkWrPairPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/wr_pair.cir"
  let want ← IO.FS.readFile "tests/golden/WrPair.lean"
  match runPipeline text wrPairFact with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected wr_pair: {msg}")
  | .ok got =>
    if got != want then
      throw (IO.userError s!"golden mismatch for wr_pair")
    IO.println s!"PASS pipeline wr_pair"
    pure 1

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. Variants derive from the real corpus by string
    surgery (no new corpus files; the gate is text-level). -/
def checkRejectWrPair (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-wrpair: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-wrpair: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-wrpair: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-wrpair {name} [{code}]"
    pure 1

def wrPairBase : IO String :=
  IO.FS.readFile "tests/cir/wr_pair.cir"

/-- Missing `__restrict__` on writer `p`: rule-1 param check (attrs
    are claims; without the attr the verdict cannot confirm). -/
def advNoRestrictP : IO String := do
  let base ← wrPairBase
  pure (base.replace
    "%arg0: !cir.ptr<!s32i> {llvm.noalias, llvm.noundef}"
    "%arg0: !cir.ptr<!s32i> {llvm.noundef}")

/-- Wrapping adds: the `nsw` pin is load-bearing (signed overflow
    must be loud, never silently wrapped). -/
def advWrappingAdds : IO String := do
  let base ← wrPairBase
  pure (base.replace "cir.add nsw" "cir.add")

/-- Wrong const (`1`/`3`): the dataflow pin no longer matches, so the
    pair-check exemption is gone and the pair rejects (the `+3`
    would lie about the second increment). -/
def advWrongConst : IO String := do
  let base ← wrPairBase
  pure (base.replace "cir.const #cir.int<2> : !s32i"
    "cir.const #cir.int<3> : !s32i")

/-- The single-writer `incr` leaf is not the writer pair
    (shape-exactness, checked at the predicate level). -/
def checkIncrNotWrPair : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/incr_ptr.cir"
  match parseModule text with
  | none =>
    throw (IO.userError s!"reject-wrpair: incr corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "incr") with
    | none => throw (IO.userError s!"reject-wrpair: incr not found")
    | some raw =>
      if isWrPairShape raw then
        throw (IO.userError s!"reject-wrpair: incr wrongly wr-pair-shaped")
      IO.println s!"PASS reject-wrpair incr-not-wrpair [shape-exact]"
      pure 1

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkWrPairPipeline
  passed := passed + c0
  let base ← wrPairBase
  let r1 ← checkRejectWrPair "wr_pair" base .unknown
    "alias-reject" "oracle is inconclusive"
  passed := passed + r1
  let r1b ← checkRejectWrPair "wr_pair" base .mayAlias
    "alias-reject" "explicit `noalias` verdict"
  passed := passed + r1b
  let v2 ← advNoRestrictP
  let r2 ← checkRejectWrPair "wr_pair" v2 .noalias
    "alias-reject" "uniqueness cannot be established"
  passed := passed + r2
  let v3 ← advWrappingAdds
  let r3 ← checkRejectWrPair "wr_pair" v3 .noalias
    "out-of-subset" "wrapping arithmetic"
  passed := passed + r3
  let v4 ← advWrongConst
  let r4 ← checkRejectWrPair "wr_pair" v4 .noalias
    "alias-reject" "live pointer parameters"
  passed := passed + r4
  let c5 ← checkIncrNotWrPair
  passed := passed + c5
  IO.println s!"GOLDENWRPAIR-OK passed={passed}"

end GoldenWrPair
