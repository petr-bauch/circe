-- Golden test for the two-reader admission (`sum_two`): the corpus
-- pipeline (real `.cir` validates to `sumTwoFunc` and emits
-- byte-identical text to the golden) plus adversarial rejections
-- pinning the shape-exactness (two plain adds, two readers, `noalias`
-- verdict still required).
--
-- Run: `lake env lean --run tests/lean/GoldenSumTwo.lean`
import Circe.Emit
import Circe.Validator

namespace GoldenSumTwo

def sumTwoFact : OracleFact := ⟨"sum_two", .noalias⟩

def checkSumTwoPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/sum_two.cir"
  let want ← IO.FS.readFile "tests/golden/SumTwo.lean"
  match runPipeline text sumTwoFact with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected sum_two: {msg}")
  | .ok got =>
    if got != want then
      throw (IO.userError s!"golden mismatch for sum_two")
    IO.println s!"PASS pipeline sum_two"
    pure 1

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. Variants derive from the real corpus by string
    surgery (no new corpus files; the gate is text-level). -/
def checkRejectSumTwo (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-sumtwo: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-sumtwo: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-sumtwo: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-sumtwo {name} [{code}]"
    pure 1

def sumTwoBase : IO String :=
  IO.FS.readFile "tests/cir/sum_two.cir"

/-- Missing `__restrict__` on reader `a`: rule-1 param check (attrs
    are claims; without the attr the verdict cannot confirm). -/
def advNoRestrictA : IO String := do
  let base ← sumTwoBase
  pure ((base.replace "@sum_two(" "@s2norestr(").replace
    "%arg0: !cir.ptr<!u32i> {llvm.noalias, llvm.noundef}"
    "%arg0: !cir.ptr<!u32i> {llvm.noundef}")

/-- Signed (`nsw`) adds: the no-`nsw` clause keeps signed two-reader
    loops out (wrapping is the verified arithmetic). -/
def advNswAdds : IO String := do
  let base ← sumTwoBase
  pure ((base.replace "@sum_two(" "@s2nsw(").replace
    "cir.add " "cir.add nsw ")

/-- Single-add body (`sum`-shaped loop over two pointers): the
    two-`cir.add` pin keeps one-reader-shaped text out. -/
def advSingleAdd : IO String := do
  let base ← sumTwoBase
  pure ((base.replace "@sum_two(" "@s2oneadd(").replace
    "%22 = cir.add %21, %20 : !u32i loc(#loc41)" "")

/-- `sum_array` text is not `sum_two`-shaped (one reader, one add):
    the exemption is shape-exact, not arity-only. -/
def checkSumArrayNotSumTwo : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/sum_array.cir"
  match parseModule text with
  | none =>
    throw (IO.userError s!"reject-sumtwo: sum_array corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "sum_array") with
    | none => throw (IO.userError s!"reject-sumtwo: sum_array not found")
    | some raw =>
      if isSumTwoShape raw then
        throw (IO.userError s!"reject-sumtwo: sum_array text wrongly sum-two-shaped")
      IO.println s!"PASS reject-sumtwo sum_array-not-sumtwo [shape-exact]"
      pure 1

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkSumTwoPipeline
  passed := passed + c0
  let base ← sumTwoBase
  let r1 ← checkRejectSumTwo "sum_two" base .unknown
    "alias-reject" "oracle is inconclusive"
  passed := passed + r1
  let r1b ← checkRejectSumTwo "sum_two" base .mayAlias
    "alias-reject" "explicit `noalias` verdict"
  passed := passed + r1b
  let v2 ← advNoRestrictA
  let r2 ← checkRejectSumTwo "s2norestr" v2 .noalias
    "alias-reject" "uniqueness cannot be established"
  passed := passed + r2
  let v3 ← advNswAdds
  let r3 ← checkRejectSumTwo "s2nsw" v3 .noalias
    "alias-reject" "live pointer parameters"
  passed := passed + r3
  let v4 ← advSingleAdd
  let r4 ← checkRejectSumTwo "s2oneadd" v4 .noalias
    "alias-reject" "live pointer parameters"
  passed := passed + r4
  let r5 ← checkRejectSumTwo "_Z18alias_add_restrictPKiS0_"
    (← IO.FS.readFile "tests/cir/alias_add_restrict.cir") .noalias
    "alias-reject" "live pointer parameters"
  passed := passed + r5
  let c6 ← checkSumArrayNotSumTwo
  passed := passed + c6
  IO.println s!"GOLDENSUMTWO-OK passed={passed}"

end GoldenSumTwo
