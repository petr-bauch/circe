-- Golden test for deep copy (`list_copy` over caller-owned
-- `Node {val, next}`): pillar-1 goal #4, allocating traversal leg
-- (one fresh 2-word cell per node; payload copied, fresh link
-- cleared, appended to the new tail; the input chain is never
-- written; empty input returns null).
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenListCopy.main`).
-- 1. Corpus pipeline: `tests/cir/list_copy.cir` (real CIRGen
--    output: `Node* head` in, `Node*` out; 6 allocas, 15 loads,
--    12 stores, one `while`, one `cir.if`, 2 `cir.cmp`
--    (ne guard + eq), 5 `cir.get_member` (`[0]`x2, `[1]`x3),
--    6 `cir.const` (5 nulls + 16 size), 1 cast (bitcast),
--    1 `cir.call @malloc`, 0 `cir.call @free`, 1 `get_global`
--    (malloc decl), 1 `cir.return`, 1 `yield`)
--    validates via `runModulePipeline` with an `unknown`
--    oracle fact and emits byte-identical text to
--    `tests/golden/ListCopy.lean`.
-- 2. Rejection suite: three-pointer variant (one more live
--    pointer — the offender gate fires: `alias-reject`);
--    free-added variant (the fresh head is freed, then
--    returned — the escape gate fires: `escape-reject`);
--    sibling texts are not copy-shaped and `list_copy` text
--    is not sibling-shaped (shape-exactness both directions).
import Circe.Validator

namespace GoldenListCopy

def copyFact : OracleFact := ⟨"_Z9list_copyP4Node", .unknown⟩

def checkListCopyPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_copy.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/ListCopy.lean"
  match runModulePipeline text [copyFact] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected list_copy: {msg}")
  | .ok [("_Z9list_copyP4Node", gotEntry)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for list_copy entry")
    IO.println "PASS pipeline list_copy (entry, unknown oracle fact)"
    pure 1
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the
    message plus `substr`. -/
def checkRejectListCopy (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-copy: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-copy: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-copy: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-copy {name} [{code}]"
    pure 1

/-- Three-pointer variant: the corpus signature plus a third bare
    `Node*` param. Same body, one more live pointer — the offender
    gate fires first (a bare pointer among two live ones cannot be
    discharged): `alias-reject`. -/
def advThreePtr (text : String) : String :=
  text.replace "%arg0: !cir.ptr<!rec_Node> {llvm.noundef} loc(fused[#loc3, #loc4])"
    "%arg0: !cir.ptr<!rec_Node> {llvm.noundef} loc(fused[#loc3, #loc4]), %arg1: !cir.ptr<!rec_Node> {llvm.noundef} loc(fused[#loc3, #loc4])"

def checkThreePtrRejects : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_copy.cir"
  checkRejectListCopy "_Z9list_copyP4Node" (advThreePtr text) .unknown
    "alias-reject" "__restrict__"

/-- Free-added variant: the fresh head is freed at the return,
    then the freed node is returned. The escape gate fires: a
    freed heap block's address cannot be returned. -/
def advFreeAdded (text : String) : String :=
  text.replace "cir.return %9 : !cir.ptr<!rec_Node> loc(#loc71)"
    "cir.call @free(%9) nothrow : (!cir.ptr<!void> {llvm.noundef}) -> () loc(#loc71)\n              cir.return %9 : !cir.ptr<!rec_Node> loc(#loc71)"

def checkFreeAddedRejects : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_copy.cir"
  checkRejectListCopy "_Z9list_copyP4Node" (advFreeAdded text) .unknown
    "escape-reject" "frees a heap block"

/-- Sibling texts are not copy-shaped (writer legs with
    caller-provided nodes / freeing unlinks / read-only chases,
    not the allocating deep copy). -/
def checkSibsNotListCopy : IO Nat := do
  let mut n := 0
  for (f, nm) in [("tests/cir/list_erase.cir", "list_erase"),
      ("tests/cir/list_append.cir", "list_append"),
      ("tests/cir/list_length.cir", "list_length"),
      ("tests/cir/linked_reverse.cir", "linked_reverse"),
      ("tests/cir/list_rev.cir", "list_rev"),
      ("tests/cir/push_front.cir", "push_front")] do
    let text ← IO.FS.readFile f
    match parseModule text with
    | none =>
      throw (IO.userError s!"reject-copy: {nm} corpus failed to parse")
    | some m =>
      if m.funcs.any isListCopyShape then
        throw (IO.userError s!"reject-copy: {nm} text wrongly copier-shaped")
      IO.println s!"PASS reject-copy {nm}-not-copy [shape-exact]"
      n := n + 1
  pure n

/-- `list_copy` text is not sibling-shaped (allocating deep copy,
    not an unlink + free, a caller-node swing, a read-only count
    or query, an in-place chase, or an allocating cons). -/
def checkListCopyNotSibs : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_copy.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-copy: list_copy corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z9list_copyP4Node") with
    | none =>
      throw (IO.userError "reject-copy: list_copy not found")
    | some raw =>
      if isListEraseShape raw then
        throw (IO.userError "reject-copy: list_copy text wrongly erase-shaped")
      if isListAppendShape raw then
        throw (IO.userError "reject-copy: list_copy text wrongly listappend-shaped")
      if isListLengthShape raw then
        throw (IO.userError "reject-copy: list_copy text wrongly listlength-shaped")
      if isLinkedReverseShape raw then
        throw (IO.userError "reject-copy: list_copy text wrongly linkedreverse-shaped")
      if isPushFrontShape raw then
        throw (IO.userError "reject-copy: list_copy text wrongly pushfront-shaped")
      if isListFindShape raw then
        throw (IO.userError "reject-copy: list_copy text wrongly finder-shaped")
      IO.println "PASS reject-copy copy-not-sibs [shape-exact]"
      pure 1

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkListCopyPipeline
  passed := passed + c0
  let r1 ← checkThreePtrRejects
  passed := passed + r1
  let r2 ← checkFreeAddedRejects
  passed := passed + r2
  let r3 ← checkSibsNotListCopy
  passed := passed + r3
  let r4 ← checkListCopyNotSibs
  passed := passed + r4
  IO.println s!"GOLDENLISTCOPY-OK passed={passed}"

end GoldenListCopy
