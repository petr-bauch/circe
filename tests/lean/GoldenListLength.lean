-- Golden test for read-only node count (`list_length` over
-- caller-owned `Node {val, next}`): the L-ptr second shape, admitted
-- via the single-pointer exemption (one bare pointer cannot alias
-- itself, so the restrict/triple demand is lifted and the shape arm
-- decides).
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenListLength.main`).
-- 1. Corpus pipeline: `tests/cir/list_length.cir` (real CIRGen
--    output: `Node* head` in (bare `!cir.ptr<!rec_Node>`, nullable
--    by design — no `__restrict__`/triple), `u64` count out; the
--    single `while (cur != nullptr)` chase reading `cur->next`
--    (one `cir.get_member` `[1]` projection) while a `u64`
--    counter accumulates) validates via `runModulePipeline` with
--    NO oracle facts (single-pointer exemption: synthetic
--    `unknown` verdict) and emits byte-identical text to
--    `tests/golden/ListLength.lean`.
-- 2. Rejection suite: two-pointer `list_length` variant (second
--    bare `Node*` param added — the alias discipline still fires:
--    `alias-reject`); one-pointer void variant (no shape matches —
--    the exemption is not blanket admission: `out-of-subset`);
--    `list_rev` text is not listlength-shaped and
--    `list_length` text is not listrev-shaped (shape-exactness
--    both directions).
import Circe.Validator

namespace GoldenListLength

def checkListLengthPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_length.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/ListLength.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected list_length: {msg}")
  | .ok [("_Z11list_lengthP4Node", gotEntry)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for list_length entry")
    IO.println "PASS pipeline list_length (entry, no oracle facts)"
    pure 1
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the
    message plus `substr`. -/
def checkRejectListLength (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-listlen: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-listlen: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-listlen: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-listlen {name} [{code}]"
    pure 1

/-- Two-pointer variant: the corpus signature plus a second bare
    `Node*` param. Same body, one more live pointer — the alias
    discipline still fires before shapes are consulted. -/
def advTwoPtr (text : String) : String :=
  text.replace "%arg0: !cir.ptr<!rec_Node> {llvm.noundef} loc(fused[#loc3, #loc4])"
    "%arg0: !cir.ptr<!rec_Node> {llvm.noundef} loc(fused[#loc3, #loc4]), %arg1: !cir.ptr<!rec_Node> {llvm.noundef} loc(fused[#loc3, #loc4])"

def checkTwoPtrRejects : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_length.cir"
  checkRejectListLength "_Z11list_lengthP4Node" (advTwoPtr text) .unknown
    "alias-reject" "uniqueness cannot be established"

/-- One-pointer void variant: the exemption lifts alias discipline,
    but no shape arm matches a body that is not the count chase —
    the fragment gate rejects. Exemption is not blanket admission. -/
def advOnePtrVoid : String :=
  "module {\n  cir.func @llvoid(%arg0: !cir.ptr<!rec_Node> {llvm.noundef}) -> () attributes {\"nothrow\"} {\n    cir.return\n  }\n}"

/-- `list_rev` text is not listlength-shaped (index-linked chase
    over vectors, not a raw-pointer count). -/
def checkListRevNotListLength : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_rev.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-listlen: list_rev corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z8list_revRSt6vectorIiSaIiEES2_mm") with
    | none => throw (IO.userError "reject-listlen: list_rev not found")
    | some raw =>
      if isListLengthShape raw then
        throw (IO.userError "reject-listlen: list_rev text wrongly listlength-shaped")
      IO.println "PASS reject-listlen listrev-not-listlength [shape-exact]"
      pure 1

/-- `list_length` text is not listrev-shaped (raw-pointer count,
    not the vector link chase) and not linkedreverse-shaped (no
    link swing). -/
def checkListLengthNotListRev : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_length.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-listlen: list_length corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z11list_lengthP4Node") with
    | none => throw (IO.userError "reject-listlen: list_length not found")
    | some raw =>
      if isListRevShape raw then
        throw (IO.userError "reject-listlen: list_length text wrongly listrev-shaped")
      if isLinkedReverseShape raw then
        throw (IO.userError "reject-listlen: list_length text wrongly linkedreverse-shaped")
      IO.println "PASS reject-listlen listlength-not-listrev [shape-exact]"
      pure 1

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkListLengthPipeline
  passed := passed + c0
  let r1 ← checkTwoPtrRejects
  passed := passed + r1
  let r2 ← checkRejectListLength "llvoid" advOnePtrVoid .unknown
    "out-of-subset" "admitted Phase-4 fragment"
  passed := passed + r2
  let r3 ← checkListRevNotListLength
  passed := passed + r3
  let r4 ← checkListLengthNotListRev
  passed := passed + r4
  IO.println s!"GOLDENLISTLENGTH-OK passed={passed}"

end GoldenListLength
