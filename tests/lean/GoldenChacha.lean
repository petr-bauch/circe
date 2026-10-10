-- Golden test for K4: `chacha20_block` corpus pipeline +
-- containment-boundary rejection suite (single-`&mut` admission is
-- shape-exact: verdict required, attrs required, exact op counts).
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenChacha.lean`
-- 1. Corpus pipeline: `tests/cir/chacha_block.cir` (real CIRGen output:
--    single `__restrict__` u32 state buffer, void return, three
--    `cir.for` over the QR arithmetic, no calls) validates under the
--    explicit `noalias` verdict (attrs are claims, the verdict
--    confirms) and emits byte-identical text to
--    `tests/golden/ChachaBlock.lean`.
-- 2. Rename acceptance: the gate pins shapes, not C names.
-- 3. Rejection suite: inconclusive verdict, missing `__restrict__`,
--    two-param arity — all hit dedicated `alias-reject` codes.
--    Mismatch policy: any in-subset divergence is P0; out-of-subset
--    must reject loudly.
import Circe.Validator

namespace GoldenChacha

def chachaFact : OracleFact := ⟨"chacha20_block", .noalias⟩

def checkChachaPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/chacha_block.cir"
  let want ← IO.FS.readFile "tests/golden/ChachaBlock.lean"
  match runPipeline text chachaFact with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected chacha20_block: {msg}")
  | .ok got =>
    if got != want then
      throw (IO.userError s!"golden mismatch for chacha20_block")
    IO.println s!"PASS pipeline chacha20_block"
    pure 1

/-- Renamed corpus still validates (no name pinning); the emitted
    forward carries the new name. -/
def checkChachaRename : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/chacha_block.cir"
  let renamed := text.replace "@chacha20_block(" "@chachaX("
  match runPipeline renamed ⟨"chachaX", .noalias⟩ with
  | .error msg =>
    throw (IO.userError s!"renamed chacha unexpectedly rejected: {msg}")
  | .ok got =>
    if !containsSubstr got "chachaX_fwd" then
      throw (IO.userError s!"renamed emit missing chachaX_fwd")
    IO.println s!"PASS rename chachaX"
    pure 1

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. Variants derive from the real corpus by string
    surgery (no new corpus files; the gate is text-level). -/
def checkRejectChacha (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-chacha: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-chacha: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-chacha: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-chacha {name} [{code}]"
    pure 1

def chachaBase : IO String :=
  IO.FS.readFile "tests/cir/chacha_block.cir"

/-- Missing `__restrict__` on `state`: rule-1 param check. -/
def advNoRestrict : IO String := do
  let base ← chachaBase
  pure ((base.replace "@chacha20_block(" "@chnorestr(").replace
    "%arg0: !cir.ptr<!u32i> {llvm.noalias, llvm.noundef}"
    "%arg0: !cir.ptr<!u32i> {llvm.noundef}")

/-- Two live buffers: arity pin at the pair check (the block kernel
    takes exactly one writer). -/
def advTwoParams : IO String := do
  let base ← chachaBase
  pure ((base.replace "@chacha20_block(" "@ch2params(").replace
    "%arg0: !cir.ptr<!u32i> {llvm.noalias, llvm.noundef} loc("
    "%arg0: !cir.ptr<!u32i> {llvm.noalias, llvm.noundef}, %arg1: !cir.ptr<!u32i> {llvm.noalias, llvm.noundef} loc(")

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkChachaPipeline
  passed := passed + c0
  let c1 ← checkChachaRename
  passed := passed + c1
  let base ← chachaBase
  let r1 ← checkRejectChacha "chacha20_block" base .unknown
    "alias-reject" "oracle is inconclusive"
  passed := passed + r1
  let v2 ← advNoRestrict
  let r2 ← checkRejectChacha "chnorestr" v2 .unknown
    "alias-reject" "uniqueness cannot be established"
  passed := passed + r2
  let v3 ← advTwoParams
  let r3 ← checkRejectChacha "ch2params" v3 .noalias
    "alias-reject" "live pointer parameters"
  passed := passed + r3
  IO.println s!"GOLDENCHACHA-OK passed={passed}"

end GoldenChacha
