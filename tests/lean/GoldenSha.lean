-- Golden test for K5c: `sha256_compress` corpus pipeline +
-- containment-boundary rejection suite (single-`&mut` admission is
-- shape-exact: verdict required, attrs required, exact op counts).
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenSha.lean`
-- 1. Corpus pipeline: `tests/cir/sha256_compress.cir` (real CIRGen output:
--    single `__restrict__` u32 state buffer (24 words: 8 digest + 16
--    block), void return, five `cir.for` (block-init, schedule,
--    work-init, 64 compress rounds, add-back), no calls) validates under
--    the explicit `noalias` verdict (attrs are claims, the verdict
--    confirms) and emits byte-identical text to
--    `tests/golden/Sha256Compress.lean`.
-- 2. Rename acceptance: the gate pins shapes, not C names.
-- 3. Rejection suite: inconclusive verdict, missing `__restrict__`,
--    two-param arity — all hit dedicated `alias-reject` codes.
--    Mismatch policy: any in-subset divergence is P0; out-of-subset
--    must reject loudly.
import Circe.Validator

namespace GoldenSha

def shaFact : OracleFact := ⟨"sha256_compress", .noalias⟩

def checkShaPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/sha256_compress.cir"
  let want ← IO.FS.readFile "tests/golden/Sha256Compress.lean"
  match runPipeline text shaFact with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected sha256_compress: {msg}")
  | .ok got =>
    if got != want then
      throw (IO.userError s!"golden mismatch for sha256_compress")
    IO.println s!"PASS pipeline sha256_compress"
    pure 1

/-- Renamed corpus still validates (no name pinning); the emitted
    forward carries the new name. -/
def checkShaRename : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/sha256_compress.cir"
  let renamed := text.replace "@sha256_compress(" "@shaX("
  match runPipeline renamed ⟨"shaX", .noalias⟩ with
  | .error msg =>
    throw (IO.userError s!"renamed sha unexpectedly rejected: {msg}")
  | .ok got =>
    if !containsSubstr got "shaX_fwd" then
      throw (IO.userError s!"renamed emit missing shaX_fwd")
    IO.println s!"PASS rename shaX"
    pure 1

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. Variants derive from the real corpus by string
    surgery (no new corpus files; the gate is text-level). -/
def checkRejectSha (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-sha: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-sha: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-sha: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-sha {name} [{code}]"
    pure 1

def shaBase : IO String :=
  IO.FS.readFile "tests/cir/sha256_compress.cir"

/-- Missing `__restrict__` on `st`: rule-1 param check. -/
def advNoRestrict : IO String := do
  let base ← shaBase
  pure ((base.replace "@sha256_compress(" "@shanorestr(").replace
    "%arg0: !cir.ptr<!u32i> {llvm.noalias, llvm.noundef}"
    "%arg0: !cir.ptr<!u32i> {llvm.noundef}")

/-- Two live buffers: arity pin at the pair check (the compress kernel
    takes exactly one writer). -/
def advTwoParams : IO String := do
  let base ← shaBase
  pure ((base.replace "@sha256_compress(" "@sh2params(").replace
    "%arg0: !cir.ptr<!u32i> {llvm.noalias, llvm.noundef} loc("
    "%arg0: !cir.ptr<!u32i> {llvm.noalias, llvm.noundef}, %arg1: !cir.ptr<!u32i> {llvm.noalias, llvm.noundef} loc(")

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkShaPipeline
  passed := passed + c0
  let c1 ← checkShaRename
  passed := passed + c1
  let base ← shaBase
  let r1 ← checkRejectSha "sha256_compress" base .unknown
    "alias-reject" "oracle is inconclusive"
  passed := passed + r1
  let v2 ← advNoRestrict
  let r2 ← checkRejectSha "shanorestr" v2 .unknown
    "alias-reject" "uniqueness cannot be established"
  passed := passed + r2
  let v3 ← advTwoParams
  let r3 ← checkRejectSha "sh2params" v3 .noalias
    "alias-reject" "live pointer parameters"
  passed := passed + r3
  IO.println s!"GOLDENSHA-OK passed={passed}"

end GoldenSha
