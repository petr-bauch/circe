-- Golden test for sorted merge (`list_merge` over caller-owned
-- `Node {val, next}`): pillar-1 goal #1, first multi-input
-- traversal leg (two-cursor chase swinging `tail.next` at the
-- smaller head, stable take-from-`a` on ties, remainder splice;
-- destructive relink only, no allocation; both inputs ascending
-- and disjoint, output reuses exactly the input cells).
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenListMerge.main`).
-- 1. Corpus pipeline: `tests/cir/list_merge.cir` (real CIRGen
--    output: `Node *a, Node *b` in (both `!cir.ptr<!rec_Node>`
--    with `llvm.noalias`), `Node*` out; 5 allocas, 40 loads,
--    17 stores, one `while`, 5 `cir.if`, 7 `cir.cmp`,
--    13 `cir.get_member` (`[0]`x4, `[1]`x9), 6 `cir.const`,
--    3 `cir.return`, 3 yield, 0 calls)
--    validates via `runModulePipeline` with a `noalias` oracle
--    fact and emits byte-identical text to
--    `tests/golden/ListMerge.lean`.
-- 2. Rejection suite: bare third-pointer variant (one more live
--    pointer without `__restrict__` — the offender gate fires:
--    `alias-reject`); `unknown`-verdict variant (two live `__restrict__`
--    pointers with an inconclusive oracle — the verdict demand
--    fires: `alias-reject`); free-added variant (the returned
--    register is freed — the exact shape no longer matches:
--    `alias-reject`); sibling texts are not merge-shaped and
--    `list_merge` text is not sibling-shaped (shape-exactness
--    both directions).
import Circe.Validator

namespace GoldenListMerge

def mergeFact : OracleFact := ⟨"_Z10list_mergeP4NodeS0_", .noalias⟩

def checkListMergePipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_merge.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/ListMerge.lean"
  match runModulePipeline text [mergeFact] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected list_merge: {msg}")
  | .ok [("_Z10list_mergeP4NodeS0_", gotEntry)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for list_merge entry")
    IO.println "PASS pipeline list_merge (entry, noalias oracle fact)"
    pure 1
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the
    message plus `substr`. -/
def checkRejectListMerge (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-merge: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-merge: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-merge: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-merge {name} [{code}]"
    pure 1

/-- Bare third-pointer variant: the corpus signature plus a third
    bare `Node*` param. Same body, one more live pointer without
    `__restrict__` — the offender gate fires: `alias-reject`. -/
def advThreePtr (text : String) : String :=
  text.replace "%arg1: !cir.ptr<!rec_Node> {llvm.noalias, llvm.noundef} loc(fused[#loc5, #loc6]))"
    "%arg1: !cir.ptr<!rec_Node> {llvm.noalias, llvm.noundef} loc(fused[#loc5, #loc6]), %arg2: !cir.ptr<!rec_Node> {llvm.noundef} loc(fused[#loc5, #loc6]))"

def checkThreePtrRejects : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_merge.cir"
  checkRejectListMerge "_Z10list_mergeP4NodeS0_" (advThreePtr text) .noalias
    "alias-reject" "__restrict__"

/-- Inconclusive-oracle variant: the corpus with an `unknown`
    verdict. Two live `__restrict__` pointers demand an explicit
    `noalias` verdict — the verdict gate fires: `alias-reject`. -/
def checkUnknownRejects : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_merge.cir"
  checkRejectListMerge "_Z10list_mergeP4NodeS0_" text .unknown
    "alias-reject" "inconclusive"

/-- Free-added variant: the returned register is freed at the
    return, then returned. The exact merge shape no longer
    matches (a `free` appears), so the multi-pointer gate fires:
    `alias-reject`. -/
def advFreeAdded (text : String) : String :=
  text.replace "cir.return %7 : !cir.ptr<!rec_Node> loc(#loc130)"
    "cir.call @free(%7) nothrow : (!cir.ptr<!void> {llvm.noundef}) -> () loc(#loc130)\n    cir.return %7 : !cir.ptr<!rec_Node> loc(#loc130)"

def checkFreeAddedRejects : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_merge.cir"
  checkRejectListMerge "_Z10list_mergeP4NodeS0_" (advFreeAdded text) .noalias
    "alias-reject" "2 live pointer parameters"

/-- Sibling texts are not merge-shaped (single-chain chases,
    allocating copy, unlink + free, finder, counter — not the
    two-cursor destructive splice). -/
def checkSibsNotListMerge : IO Nat := do
  let mut n := 0
  for (f, nm) in [("tests/cir/list_erase.cir", "list_erase"),
      ("tests/cir/list_append.cir", "list_append"),
      ("tests/cir/list_length.cir", "list_length"),
      ("tests/cir/list_copy.cir", "list_copy"),
      ("tests/cir/list_clear.cir", "list_clear"),
      ("tests/cir/list_find.cir", "list_find"),
      ("tests/cir/list_rev.cir", "list_rev")] do
    let text ← IO.FS.readFile f
    match parseModule text with
    | none =>
      throw (IO.userError s!"reject-merge: {nm} corpus failed to parse")
    | some m =>
      if m.funcs.any isListMergeShape then
        throw (IO.userError s!"reject-merge: {nm} text wrongly merger-shaped")
      IO.println s!"PASS reject-merge {nm}-not-merge [shape-exact]"
      n := n + 1
  pure n

/-- `list_merge` text is not sibling-shaped (two-cursor splice,
    not a single-chain chase, copy, unlink, finder, or counter). -/
def checkListMergeNotSibs : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_merge.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-merge: list_merge corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z10list_mergeP4NodeS0_") with
    | none =>
      throw (IO.userError "reject-merge: list_merge not found")
    | some raw =>
      if isListEraseShape raw then
        throw (IO.userError "reject-merge: list_merge text wrongly erase-shaped")
      if isListAppendShape raw then
        throw (IO.userError "reject-merge: list_merge text wrongly listappend-shaped")
      if isListLengthShape raw then
        throw (IO.userError "reject-merge: list_merge text wrongly listlength-shaped")
      if isListCopyShape raw then
        throw (IO.userError "reject-merge: list_merge text wrongly copy-shaped")
      if isListClearShape raw then
        throw (IO.userError "reject-merge: list_merge text wrongly clear-shaped")
      if isListFindShape raw then
        throw (IO.userError "reject-merge: list_merge text wrongly finder-shaped")
      if isListSortedInsertShape raw then
        throw (IO.userError "reject-merge: list_merge text wrongly sortedinsert-shaped")
      IO.println "PASS reject-merge merge-not-sibs [shape-exact]"
      pure 1

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkListMergePipeline
  passed := passed + c0
  let r1 ← checkThreePtrRejects
  passed := passed + r1
  let r2 ← checkUnknownRejects
  passed := passed + r2
  let r3 ← checkFreeAddedRejects
  passed := passed + r3
  let r4 ← checkSibsNotListMerge
  passed := passed + r4
  let r5 ← checkListMergeNotSibs
  passed := passed + r5
  IO.println s!"GOLDENLISTMERGE-OK passed={passed}"

end GoldenListMerge
