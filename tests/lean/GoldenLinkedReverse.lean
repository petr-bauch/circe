-- Golden test for raw-pointer in-place list reversal (`list_reverse`
-- over caller-owned `Node {val, next}`): the first dynamic
-- (pointer-chasing) shape, admitted via the single-pointer exemption
-- (L-ptr: one live pointer cannot alias itself, so the restrict/triple
-- demand is lifted and the shape arm decides).
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenLinkedReverse.main`).
-- 1. Corpus pipeline: `tests/cir/linked_reverse.cir` (real CIRGen
--    output: `Node* head` in (bare `!cir.ptr<!rec_Node>`, nullable
--    by design — no `__restrict__`/triple), `Node*` out; the single
--    `while (cur != nullptr)` chase reading `cur->next` (two
--    `cir.get_member` `[1]` projections), swinging each link to its
--    predecessor) validates via `runModulePipeline` with NO oracle
--    facts (single-pointer exemption: synthetic `unknown` verdict)
--    and emits byte-identical text to
--    `tests/golden/LinkedReverse.lean`.
-- 2. Rejection suite: two-pointer `linked_reverse` variant (second
--    bare `Node*` param added — the alias discipline still fires:
--    `alias-reject`); one-pointer void variant (no shape matches —
--    the exemption is not blanket admission: `out-of-subset`);
--    `list_rev` text is not linkedreverse-shaped and
--    `linked_reverse` text is not listrev-shaped (shape-exactness
--    both directions).
import Circe.Validator

namespace GoldenLinkedReverse

def checkLinkedReversePipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/linked_reverse.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/LinkedReverse.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected linked_reverse: {msg}")
  | .ok [("_Z12list_reverseP4Node", gotEntry)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for linked_reverse entry")
    IO.println "PASS pipeline linked_reverse (entry, no oracle facts)"
    pure 1
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectLinkedReverse (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-linkedrev: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-linkedrev: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-linkedrev: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-linkedrev {name} [{code}]"
    pure 1

/-- Two-pointer variant: the corpus signature plus a second bare
    `Node*` param. Same body, one more live pointer — the alias
    discipline still fires before shapes are consulted. -/
def advTwoPtr (text : String) : String :=
  text.replace "%arg0: !cir.ptr<!rec_Node> {llvm.noundef} loc(fused[#loc3, #loc4])"
    "%arg0: !cir.ptr<!rec_Node> {llvm.noundef} loc(fused[#loc3, #loc4]), %arg1: !cir.ptr<!rec_Node> {llvm.noundef} loc(fused[#loc3, #loc4])"

def checkTwoPtrRejects : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/linked_reverse.cir"
  checkRejectLinkedReverse "_Z12list_reverseP4Node" (advTwoPtr text) .unknown
    "alias-reject" "uniqueness cannot be established"

/-- One-pointer void variant: the exemption lifts alias discipline,
    but no shape arm matches a body that is not the link chase —
    the fragment gate rejects. Exemption is not blanket admission. -/
def advOnePtrVoid : String :=
  "module {\n  cir.func @lrvoid(%arg0: !cir.ptr<!rec_Node> {llvm.noundef}) -> () attributes {\"nothrow\"} {\n    cir.return\n  }\n}"

/-- `list_rev` text is not linkedreverse-shaped (index-linked chase
    over vectors, not a raw-pointer link swing). -/
def checkListRevNotLinkedRev : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_rev.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-linkedrev: list_rev corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z8list_revRSt6vectorIiSaIiEES2_mm") with
    | none => throw (IO.userError "reject-linkedrev: list_rev not found")
    | some raw =>
      if isLinkedReverseShape raw then
        throw (IO.userError "reject-linkedrev: list_rev text wrongly linkedreverse-shaped")
      IO.println "PASS reject-linkedrev listrev-not-linkedrev [shape-exact]"
      pure 1

/-- `linked_reverse` text is not listrev-shaped (raw-pointer swing,
    not the vector link chase). -/
def checkLinkedRevNotListRev : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/linked_reverse.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-linkedrev: linked_reverse corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z12list_reverseP4Node") with
    | none => throw (IO.userError "reject-linkedrev: linked_reverse not found")
    | some raw =>
      if isListRevShape raw then
        throw (IO.userError "reject-linkedrev: linked_reverse text wrongly listrev-shaped")
      IO.println "PASS reject-linkedrev linkedrev-not-listrev [shape-exact]"
      pure 1

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkLinkedReversePipeline
  passed := passed + c0
  let r1 ← checkTwoPtrRejects
  passed := passed + r1
  let r2 ← checkRejectLinkedReverse "lrvoid" advOnePtrVoid .unknown
    "out-of-subset" "admitted Phase-4 fragment"
  passed := passed + r2
  let r3 ← checkListRevNotLinkedRev
  passed := passed + r3
  let r4 ← checkLinkedRevNotListRev
  passed := passed + r4
  IO.println s!"GOLDENLINKEDREV-OK passed={passed}"

end GoldenLinkedReverse
