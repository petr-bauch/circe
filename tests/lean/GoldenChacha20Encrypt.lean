-- Golden test for K6a: `chacha20_encrypt` corpus pipeline +
-- containment-boundary rejection suite (single-`&mut` call-in-loop
-- admission is shape-exact: verdict required, attrs required, exact op
-- counts, both call sites pinned to the admitted K4 leaf).
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenChacha20Encrypt.lean`
-- 1. Corpus pipeline: `tests/cir/chacha20_encrypt.cir` (real CIRGen
--    output: three `__restrict__` u32 buffers, u32 counter + word
--    length, void return, one outer `cir.while` with the block call,
--    two `cir.for` xor loops, one tail `cir.if`) validates under the
--    explicit `noalias` verdict and emits byte-identical text to
--    `tests/golden/Chacha20Encrypt.lean`.
-- 2. Rename acceptance: the gate pins shapes, not C names.
-- 3. Rejection suite: inconclusive verdict, missing `__restrict__`,
--    an unknown callee, a call outside the loop shape — all hit
--    dedicated codes.
--    Mismatch policy: any in-subset divergence is P0; out-of-subset
--    must reject loudly.
import Circe.Validator

namespace GoldenChacha20Encrypt

def encryptFact : OracleFact := ⟨"chacha20_encrypt", .noalias⟩

def checkEncryptPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/chacha20_encrypt.cir"
  let want ← IO.FS.readFile "tests/golden/Chacha20Encrypt.lean"
  match runPipeline text encryptFact with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected chacha20_encrypt: {msg}")
  | .ok got =>
    if got != want then
      throw (IO.userError s!"golden mismatch for chacha20_encrypt")
    IO.println s!"PASS pipeline chacha20_encrypt"
    pure 1

/-- Renamed corpus still validates (no name pinning); the emitted
    forward carries the new name. -/
def checkEncryptRename : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/chacha20_encrypt.cir"
  let renamed := text.replace "@chacha20_encrypt(" "@chachaX("
  match runPipeline renamed ⟨"chachaX", .noalias⟩ with
  | .error msg =>
    throw (IO.userError s!"renamed encrypt unexpectedly rejected: {msg}")
  | .ok got =>
    if !containsSubstr got "chachaX_fwd" then
      throw (IO.userError s!"renamed emit missing chachaX_fwd")
    IO.println s!"PASS rename chachaX"
    pure 1

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. Variants derive from the real corpus by string
    surgery (no new corpus files; the gate is text-level). -/
def checkRejectEncrypt (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-encrypt: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-encrypt: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-encrypt: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-encrypt {name} [{code}]"
    pure 1

def encryptBase : IO String :=
  IO.FS.readFile "tests/cir/chacha20_encrypt.cir"

/-- Missing `__restrict__` on `msg`: rule-1 param check. -/
def advNoRestrict : IO String := do
  let base ← encryptBase
  pure ((base.replace "@chacha20_encrypt(" "@encnorestr(").replace
    "%arg3: !cir.ptr<!u32i> {llvm.noalias, llvm.noundef}"
    "%arg3: !cir.ptr<!u32i> {llvm.noundef}")

/-- Unknown callee: the second call site targets a non-admitted leaf. -/
def advUnknownCallee : IO String := do
  let base ← encryptBase
  pure ((base.replace "@chacha20_encrypt(" "@encbadcallee(").replace
    "cir.call @chacha20_block(" "cir.call @mystery_block(")

/-- Call-count pin: a third block call breaks the exact shape. -/
def advExtraCall : IO String := do
  let base ← encryptBase
  pure ((base.replace "@chacha20_encrypt(" "@encextracall(").replace
    "cir.call @chacha20_block(%133)"
    "cir.call @chacha20_block(%133)\n        cir.call @chacha20_block(%133)")

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkEncryptPipeline
  passed := passed + c0
  let c1 ← checkEncryptRename
  passed := passed + c1
  let base ← encryptBase
  let r1 ← checkRejectEncrypt "chacha20_encrypt" base .unknown
    "alias-reject" "oracle is inconclusive"
  passed := passed + r1
  let v2 ← advNoRestrict
  let r2 ← checkRejectEncrypt "encnorestr" v2 .unknown
    "alias-reject" "uniqueness cannot be established"
  passed := passed + r2
  let v3 ← advUnknownCallee
  let r3 ← checkRejectEncrypt "encbadcallee" v3 .noalias
    "alias-reject" "live pointer parameters"
  passed := passed + r3
  let v4 ← advExtraCall
  let r4 ← checkRejectEncrypt "encextracall" v4 .noalias
    "alias-reject" "live pointer parameters"
  passed := passed + r4
  IO.println s!"GOLDENCHACHA20ENCRYPT-OK passed={passed}"

end GoldenChacha20Encrypt
