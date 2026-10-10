-- Golden test for K2: `xor_n` buffer-xor kernel pipeline +
-- containment-boundary rejection suite (single-`&mut` admission is
-- shape-exact: verdict required, attrs required, exact op counts).
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenXorN.lean`
-- 1. Corpus pipeline: `tests/cir/xor_n.cir` (real CIRGen output:
--    `__restrict__` out + two `__restrict__` readers + `u64` length,
--    single bounded `cir.for`, one `cir.xor` + one word-store)
--    validates under the explicit `noalias` verdict (attrs are
--    claims, the verdict confirms) and emits byte-identical text to
--    `tests/golden/XorN.lean`.
-- 2. Rejection suite: inconclusive verdict, missing `__restrict__`
--    on a reader, double-`cir.xor` body, 3-param arity, `u32`
--    length — all hit dedicated `alias-reject` codes.
--    Mismatch policy: any in-subset divergence is P0; out-of-subset
--    must reject loudly.
import Circe.Validator

namespace GoldenXorN

def xorNFact : OracleFact := ⟨"xor_n", .noalias⟩

def checkXorNPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/xor_n.cir"
  let want ← IO.FS.readFile "tests/golden/XorN.lean"
  match runPipeline text xorNFact with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected xor_n: {msg}")
  | .ok got =>
    if got != want then
      throw (IO.userError s!"golden mismatch for xor_n")
    IO.println s!"PASS pipeline xor_n"
    pure 1

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. Variants derive from the real corpus by string
    surgery (no new corpus files; the gate is text-level). -/
def checkRejectXorN (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-xorn: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-xorn: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-xorn: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-xorn {name} [{code}]"
    pure 1

def xorNBase : IO String :=
  IO.FS.readFile "tests/cir/xor_n.cir"

/-- Missing `__restrict__` on reader `a`: rule-1 param check. -/
def advNoRestrictA : IO String := do
  let base ← xorNBase
  pure ((base.replace "@xor_n(" "@xnorestr(").replace
    "%arg1: !cir.ptr<!u32i> {llvm.noalias, llvm.noundef}"
    "%arg1: !cir.ptr<!u32i> {llvm.noundef}")

/-- Double-`cir.xor` body: the pair-check exemption is shape-exact
    (two xors are not the kernel). -/
def advDoubleXor : IO String := do
  let base ← xorNBase
  pure ((base.replace "@xor_n(" "@xdbxor(").replace
    "%15 = cir.xor %10, %14 : !u32i loc(#loc39)"
    "%15 = cir.xor %10, %14 : !u32i loc(#loc39)\n          %15b = cir.xor %10, %14 : !u32i loc(#loc39)")

/-- Three params (no length): arity pin at the pair check. -/
def advThreeParams : IO String := do
  let base ← xorNBase
  pure ((base.replace "@xor_n(" "@x3params(").replace
    ", %arg3: !u64i {llvm.noundef} loc(fused[#loc9, #loc10])" "")

/-- `u32` length instead of `u64` (`size_t`): width pin. -/
def advU32N : IO String := do
  let base ← xorNBase
  pure ((base.replace "@xor_n(" "@xu32n(").replace
    "%arg3: !u64i {llvm.noundef}" "%arg3: !u32i {llvm.noundef}")

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkXorNPipeline
  passed := passed + c0
  let base ← xorNBase
  let r1 ← checkRejectXorN "xor_n" base .unknown
    "alias-reject" "oracle is inconclusive"
  passed := passed + r1
  let v2 ← advNoRestrictA
  let r2 ← checkRejectXorN "xnorestr" v2 .unknown
    "alias-reject" "uniqueness cannot be established"
  passed := passed + r2
  let v3 ← advDoubleXor
  let r3 ← checkRejectXorN "xdbxor" v3 .noalias
    "alias-reject" "live pointer parameters"
  passed := passed + r3
  let v4 ← advThreeParams
  let r4 ← checkRejectXorN "x3params" v4 .noalias
    "alias-reject" "live pointer parameters"
  passed := passed + r4
  let v5 ← advU32N
  let r5 ← checkRejectXorN "xu32n" v5 .noalias
    "alias-reject" "live pointer parameters"
  passed := passed + r5
  IO.println s!"GOLDENXORN-OK passed={passed}"

end GoldenXorN
