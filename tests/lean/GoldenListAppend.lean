-- Golden test for tail insertion (`list_append` over caller-owned
-- `Node {val, next}`): the L-ptr second shape, writer leg, admitted
-- via the blessed multi-pointer listing (two `noalias` params with a
-- `noalias` oracle verdict — the single-pointer exemption does not
-- apply, so the text must corroborate the `__restrict__` claims and
-- the shape arm decides admission).
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenListAppend.main`).
-- 1. Corpus pipeline: `tests/cir/list_append.cir` (real CIRGen
--    output: `Node* head, Node* nd` in (both `!cir.ptr<!rec_Node>`
--    with `llvm.noalias`), `Node*` out; the normalize store, the
--    null-head early return (`cir.if`), and the single `cir.while`
--    chasing `cur` while `cur->next != nullptr` (four `cir.get_member`
--    `[1]` projections, no `[0]` — payloads ride along untouched))
--    validates via `runModulePipeline` with a `noalias` oracle fact
--    and emits byte-identical text to `tests/golden/ListAppend.lean`.
-- 2. Rejection suite: three-pointer `list_append` variant (one more
--    live pointer — the blessed listing is exact: `alias-reject`);
--    one-pointer void variant (no shape matches — the blessed
--    listing is not blanket admission: `out-of-subset`);
--    `list_rev` text is not listappend-shaped and `list_append`
--    text is not listrev-shaped (shape-exactness both directions).
import Circe.Validator

namespace GoldenListAppend

def appendFact : OracleFact := ⟨"_Z11list_appendP4NodeS0_", .noalias⟩

def checkListAppendPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_append.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/ListAppend.lean"
  match runModulePipeline text [appendFact] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected list_append: {msg}")
  | .ok [("_Z11list_appendP4NodeS0_", gotEntry)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for list_append entry")
    IO.println "PASS pipeline list_append (entry, noalias oracle fact)"
    pure 1
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the
    message plus `substr`. -/
def checkRejectListAppend (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-listapp: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-listapp: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-listapp: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-listapp {name} [{code}]"
    pure 1

/-- Three-pointer variant: the corpus signature plus a third
    `noalias` `Node*` param. Same body, one more live pointer — the
    blessed multi-pointer listing is exact, so the alias discipline
    still fires before shapes are consulted: `alias-reject`. -/
def advThreePtr (text : String) : String :=
  text.replace "%arg1: !cir.ptr<!rec_Node> {llvm.noalias, llvm.noundef} loc(fused[#loc5, #loc6])"
    "%arg1: !cir.ptr<!rec_Node> {llvm.noalias, llvm.noundef} loc(fused[#loc5, #loc6]), %arg2: !cir.ptr<!rec_Node> {llvm.noalias, llvm.noundef} loc(fused[#loc5, #loc6])"

def checkThreePtrRejects : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_append.cir"
  checkRejectListAppend "_Z11list_appendP4NodeS0_" (advThreePtr text) .noalias
    "alias-reject" "live pointer parameters"

/-- One-pointer void variant: the blessed listing admits the exact
    two-pointer chase only, and no shape arm matches a body that is
    not the normalize-then-swing insertion — the fragment gate
    rejects. The listing is not blanket admission: `out-of-subset`. -/
def advOnePtrVoid : String :=
  "module {\n  cir.func @laone(%arg0: !cir.ptr<!rec_Node> {llvm.noundef}) -> () attributes {\"nothrow\"} {\n    cir.return\n  }\n}"

/-- `list_rev` text is not listappend-shaped (index-linked chase
    over vectors, not a raw-pointer swing). -/
def checkListRevNotListAppend : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_rev.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-listapp: list_rev corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z8list_revRSt6vectorIiSaIiEES2_mm") with
    | none => throw (IO.userError "reject-listapp: list_rev not found")
    | some raw =>
      if isListAppendShape raw then
        throw (IO.userError "reject-listapp: list_rev text wrongly listappend-shaped")
      IO.println "PASS reject-listapp listrev-not-listappend [shape-exact]"
      pure 1

/-- `list_append` text is not listrev-shaped (raw-pointer swing,
    not the vector link chase), not linkedreverse-shaped (no
    in-place rewiring chase), and not listlength-shaped (writer,
    not the read-only count). -/
def checkListAppendNotOthers : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_append.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-listapp: list_append corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z11list_appendP4NodeS0_") with
    | none => throw (IO.userError "reject-listapp: list_append not found")
    | some raw =>
      if isListRevShape raw then
        throw (IO.userError "reject-listapp: list_append text wrongly listrev-shaped")
      if isLinkedReverseShape raw then
        throw (IO.userError "reject-listapp: list_append text wrongly linkedreverse-shaped")
      if isListLengthShape raw then
        throw (IO.userError "reject-listapp: list_append text wrongly listlength-shaped")
      IO.println "PASS reject-listapp listappend-not-others [shape-exact]"
      pure 1

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkListAppendPipeline
  passed := passed + c0
  let r1 ← checkThreePtrRejects
  passed := passed + r1
  let r2 ← checkRejectListAppend "laone" advOnePtrVoid .unknown
    "out-of-subset" "admitted Phase-4 fragment"
  passed := passed + r2
  let r3 ← checkListRevNotListAppend
  passed := passed + r3
  let r4 ← checkListAppendNotOthers
  passed := passed + r4
  IO.println s!"GOLDENLISTAPPEND-OK passed={passed}"

end GoldenListAppend
