-- Golden test for first-match query (`list_find` over caller-owned
-- `Node {val, next}`): pillar-1 goal #3, read-only traversal leg
-- (the chain is never written; hit returns the node, miss
-- returns null).
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenListFind.main`).
-- 1. Corpus pipeline: `tests/cir/list_find.cir` (real CIRGen
--    output: `Node* head` + `i32 val` in, `Node*` out; 4 allocas,
--    10 loads, 6 stores, one `while`, one `cir.if`, 2 `cir.cmp`
--    (guard `ne` + payload `eq`), 2 `cir.get_member` (`[0]`
--    payload, `[1]` link), 2 `cir.const`, no casts, no calls)
--    validates via `runModulePipeline` with an `unknown`
--    oracle fact and emits byte-identical text to
--    `tests/golden/ListFind.lean`.
-- 2. Rejection suite: three-pointer variant (one more live
--    pointer — the offender gate fires: `alias-reject`);
--    free-added variant (the read-only chain is freed, then
--    its node returned — the escape gate fires:
--    `escape-reject`); sibling texts are not find-shaped and
--    `list_find` text is not sibling-shaped (shape-exactness
--    both directions).
import Circe.Validator

namespace GoldenListFind

def findFact : OracleFact := ⟨"_Z9list_findP4Nodei", .unknown⟩

def checkListFindPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_find.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/ListFind.lean"
  match runModulePipeline text [findFact] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected list_find: {msg}")
  | .ok [("_Z9list_findP4Nodei", gotEntry)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for list_find entry")
    IO.println "PASS pipeline list_find (entry, unknown oracle fact)"
    pure 1
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the
    message plus `substr`. -/
def checkRejectListFind (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-find: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-find: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-find: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-find {name} [{code}]"
    pure 1

/-- Three-pointer variant: the corpus signature plus a third bare
    `Node*` param. Same body, one more live pointer — the offender
    gate fires first (a bare pointer among two live ones cannot be
    discharged): `alias-reject`. -/
def advThreePtr (text : String) : String :=
  text.replace "%arg1: !s32i {llvm.noundef} loc(fused[#loc5, #loc6])"
    "%arg1: !s32i {llvm.noundef} loc(fused[#loc5, #loc6]), %arg2: !cir.ptr<!rec_Node> {llvm.noundef} loc(fused[#loc5, #loc6])"

def checkThreePtrRejects : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_find.cir"
  checkRejectListFind "_Z9list_findP4Nodei" (advThreePtr text) .unknown
    "alias-reject" "__restrict__"

/-- Free-added variant: the read-only chain is freed at the hit,
    then the node returned. The escape gate fires: a freed heap
    block's address cannot be returned. -/
def advFreeAdded (text : String) : String :=
  text.replace "cir.return %16 : !cir.ptr<!rec_Node> loc(#loc40)"
    "cir.call @free(%16) nothrow : (!cir.ptr<!void> {llvm.noundef}) -> () loc(#loc40)\n              cir.return %16 : !cir.ptr<!rec_Node> loc(#loc40)"

def checkFreeAddedRejects : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_find.cir"
  checkRejectListFind "_Z9list_findP4Nodei" (advFreeAdded text) .unknown
    "escape-reject" "frees a heap block"

/-- Sibling texts are not find-shaped (writer legs with
    caller-provided nodes / the allocating cons / the freeing
    unlink, not the read-only first-match chase). -/
def checkSibsNotListFind : IO Nat := do
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
      throw (IO.userError s!"reject-find: {nm} corpus failed to parse")
    | some m =>
      if m.funcs.any isListFindShape then
        throw (IO.userError s!"reject-find: {nm} text wrongly finder-shaped")
      IO.println s!"PASS reject-find {nm}-not-find [shape-exact]"
      n := n + 1
  pure n

/-- `list_find` text is not sibling-shaped (first-match query
    returning the node or null, not an unlink + free, a
    caller-node swing, a read-only count, an in-place chase,
    or an allocating cons). -/
def checkListFindNotSibs : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_find.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-find: list_find corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z9list_findP4Nodei") with
    | none =>
      throw (IO.userError "reject-find: list_find not found")
    | some raw =>
      if isListEraseShape raw then
        throw (IO.userError "reject-find: list_find text wrongly erase-shaped")
      if isListAppendShape raw then
        throw (IO.userError "reject-find: list_find text wrongly listappend-shaped")
      if isListLengthShape raw then
        throw (IO.userError "reject-find: list_find text wrongly listlength-shaped")
      if isLinkedReverseShape raw then
        throw (IO.userError "reject-find: list_find text wrongly linkedreverse-shaped")
      if isPushFrontShape raw then
        throw (IO.userError "reject-find: list_find text wrongly pushfront-shaped")
      IO.println "PASS reject-find find-not-sibs [shape-exact]"
      pure 1

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkListFindPipeline
  passed := passed + c0
  let r1 ← checkThreePtrRejects
  passed := passed + r1
  let r2 ← checkFreeAddedRejects
  passed := passed + r2
  let r3 ← checkSibsNotListFind
  passed := passed + r3
  let r4 ← checkListFindNotSibs
  passed := passed + r4
  IO.println s!"GOLDENLISTFIND-OK passed={passed}"

end GoldenListFind
