-- Alias-oracle boundary probe (A-track): real CIRGen corpus through the
-- oracle decision procedure (`validate`: rule-1 param check → verdict
-- gate → pair check → shape arms; see `Circe/Validator/Gate.lean`).
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenAliasProbe.lean`
-- Each row runs `runPipeline` on one real `.cir` file with a STATED
-- advisory `OracleFact` (synthetic by construction — the probe pins
-- oracle *policy*, mirroring `llvm.noalias` attr presence or an explicit
-- "oracle abstains" `unknown`). Controls on already-admitted corpus
-- (`add`, `sum_norestrict`, `alias_reborrow`) prove the harness can
-- observe acceptance; every boundary row must reject at its predicted
-- stage with its predicted code. Any in-subset divergence is P0; any
-- ACCEPT outside the three controls is a soundness P0.
import Circe.Validator

namespace GoldenAliasProbe

/-- Real-`.cir` probe row: must reject with `code` + `substr`. -/
def checkProbeReject (name cirFile : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let text ← IO.FS.readFile cirFile
  match runPipeline text ⟨name, verdict⟩ with
  | .ok got =>
    throw (IO.userError s!"probe-alias: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"probe-alias: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"probe-alias: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS probe-alias {name} [{code}]"
    pure 1

/-- Real-`.cir` probe row: must validate (admit controls only). -/
def checkProbeAccept (name cirFile : String) (verdict : Verdict) :
    IO Nat := do
  let text ← IO.FS.readFile cirFile
  match runPipeline text ⟨name, verdict⟩ with
  | .ok _ =>
    IO.println s!"PASS probe-alias {name} [admit]"
    pure 1
  | .error msg =>
    throw (IO.userError s!"probe-alias: {name} unexpectedly rejected: {msg}")

def main : IO Unit := do
  let mut passed := 0
  -- Controls: already-admitted shapes accept under `unknown`.
  let c1 ← checkProbeAccept "add" "tests/cir/add.cir" .unknown
  passed := passed + c1
  let c2 ← checkProbeAccept "sum_norestrict" "tests/cir/sum_norestrict.cir"
    .unknown
  passed := passed + c2
  -- Attr text present, oracle abstains: verdict gate rejects (step 4).
  let b1 ← checkProbeReject "_Z18alias_add_restrictPKiS0_"
    "tests/cir/alias_add_restrict.cir" .unknown
    "alias-reject" "oracle is inconclusive"
  passed := passed + b1
  -- Attr text + `noalias` verdict: pair check rejects (step 5, not choose).
  let b2 ← checkProbeReject "_Z18alias_add_restrictPKiS0_"
    "tests/cir/alias_add_restrict.cir" .noalias
    "alias-reject" "live pointer parameters"
  passed := passed + b2
  -- No attr text: rule-1 param check rejects whatever the verdict (step 3).
  let b3 ← checkProbeReject "_Z15alias_add_plainPKiS0_"
    "tests/cir/alias_add_plain.cir" .unknown
    "alias-reject" "uniqueness cannot be established"
  passed := passed + b3
  let b4 ← checkProbeReject "_Z15alias_add_plainPKiS0_"
    "tests/cir/alias_add_plain.cir" .noalias
    "alias-reject" "uniqueness cannot be established"
  passed := passed + b4
  -- Triple params: oracle vacuous. The sequential reborrow is
  -- admitted since F1 (the third admit control): exact two-phase
  -- computation over L2-disjoint ranges through one F0-resolved
  -- address, functionalized value in / updated value out.
  let b5 ← checkProbeAccept "_Z14alias_reborrowRi"
    "tests/cir/alias_reborrow.cir" .unknown
  passed := passed + b5
  -- Unknown-verdict branch-writer: admitted since G3/S3 via the
  -- open contract (the fourth admit control): exact branch/dataflow
  -- skeleton with the fused C++ deref chain over two
  -- single-reference-triple writers; transfer case-splits on the
  -- addresses, covering `unknown` and `mayAlias` alike.
  let b6 ← checkProbeAccept "_Z10alias_condRiS_b"
    "tests/cir/alias_cond.cir" .unknown
  passed := passed + b6
  let b7 ← checkProbeReject "_Z19alias_readonly_pairRKiS0_"
    "tests/cir/alias_readonly_pair.cir" .unknown
    "out-of-subset" "admitted Phase-4 fragment"
  passed := passed + b7
  let b8 ← checkProbeReject "_Z14alias_disjointv"
    "tests/cir/alias_disjoint.cir" .unknown
    "out-of-subset" "admitted Phase-4 fragment"
  passed := passed + b8
  -- Escaping return rejects loudly (real-CIR escape control).
  let b9 ← checkProbeReject "_Z12alias_escapeRi"
    "tests/cir/alias_escape.cir" .unknown
    "escape-reject" "returns pointer type"
  passed := passed + b9
  -- Single-`&mut` free-function writer: oracle vacuous, shape novel.
  let b10 ← checkProbeReject "_Z14alias_incr_refRi"
    "tests/cir/alias_incr_ref.cir" .unknown
    "out-of-subset" "admitted Phase-4 fragment"
  passed := passed + b10
  IO.println s!"GOLDENALIASPROBE-OK passed={passed}"

end GoldenAliasProbe
