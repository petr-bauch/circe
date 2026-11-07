-- Golden test for ordered insert (`list_sorted_insert` over caller-owned
-- `Node {val, next}`): pillar-1 goal #6, find + link swing over a sorted
-- chain (upper-bound rule, single `malloc`, no `free`).
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenListSortedInsert.main`).
-- 1. Corpus pipeline: `tests/cir/list_sorted_insert.cir` (real CIRGen
--    output: `Node* head` + `i32 val` in, `Node*` out = possibly-new
--    head; 6 allocas, 18 loads, 12 stores, 5 consts, one `while`,
--    one `cir.ternary` (`&&` short-circuit) + one `cir.if`
--    (prev-null head case), 3 `cir.cmp` (guard `ne`, keep-advancing
--    signed `le`, prev-null `eq`), 5 `cir.get_member` (two `[0]`
--    payload, three `[1]` link), 1 bitcast, 1 call (`@malloc`),
--    no `@free`, single tail `cir.return`) validates via
--    `runModulePipeline` with an `unknown` oracle fact and emits
--    byte-identical text to `tests/golden/ListSortedInsert.lean`.
-- 2. Rejection suite: three-pointer variant (one more live
--    pointer — the offender gate fires: `alias-reject`);
--    free-added-at-return variant (the escape gate fires:
--    `escape-reject`); upper-bound-flip variant (`le` to `lt` —
--    the text matches no admitted shape, so the heap-allocation
--    subset gate fires: `out-of-subset`); sibling texts are not
--    sorted-insert-shaped
--    and `list_sorted_insert` text is not sibling-shaped
--    (shape-exactness both directions).
import Circe.Validator

namespace GoldenListSortedInsert

def sortedInsertFact : OracleFact := ⟨"_Z18list_sorted_insertP4Nodei", .unknown⟩

def checkListSortedInsertPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_sorted_insert.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/ListSortedInsert.lean"
  match runModulePipeline text [sortedInsertFact] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected list_sorted_insert: {msg}")
  | .ok [("_Z18list_sorted_insertP4Nodei", gotEntry)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for list_sorted_insert entry")
    IO.println "PASS pipeline list_sorted_insert (entry, unknown oracle fact)"
    pure 1
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the
    message plus `substr`. -/
def checkRejectListSortedInsert (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-sortedinsert: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-sortedinsert: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-sortedinsert: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-sortedinsert {name} [{code}]"
    pure 1

/-- Three-pointer variant: the corpus signature plus a second bare
    `Node*` param. Same body, one more live pointer — the offender
    gate fires first (a bare pointer among two live ones cannot be
    discharged): `alias-reject`. -/
def advThreePtr (text : String) : String :=
  text.replace "%arg1: !s32i {llvm.noundef} loc(fused[#loc5, #loc6])"
    "%arg1: !s32i {llvm.noundef} loc(fused[#loc5, #loc6]), %arg2: !cir.ptr<!rec_Node> {llvm.noundef} loc(fused[#loc5, #loc6])"

def checkThreePtrRejects : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_sorted_insert.cir"
  checkRejectListSortedInsert "_Z18list_sorted_insertP4Nodei" (advThreePtr text) .unknown
    "alias-reject" "__restrict__"

/-- Free-added variant: the returned head is freed at the return,
    then the freed node is returned. The escape gate fires: a
    freed heap block's address cannot be returned. -/
def advFreeAdded (text : String) : String :=
  text.replace "cir.return %19 : !cir.ptr<!rec_Node> loc(#loc75)"
    "cir.call @free(%19) nothrow : (!cir.ptr<!void> {llvm.noundef}) -> () loc(#loc75)\n    cir.return %19 : !cir.ptr<!rec_Node> loc(#loc75)"

def checkFreeAddedRejects : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_sorted_insert.cir"
  checkRejectListSortedInsert "_Z18list_sorted_insertP4Nodei" (advFreeAdded text) .unknown
    "escape-reject" "frees a heap block"

/-- Upper-bound-flip variant: the keep-advancing signed `le`
    becomes `lt` (insert-before-equals: the fresh node would land
    before existing equals, breaking the upper-bound rule). No
    shape arm matches the flipped text, so the subset
    heap-allocation gate fires: a `malloc` text outside every
    admitted shape. -/
def advUpperBoundFlip (text : String) : String :=
  text.replace "cir.cmp le %26, %27 : !s32i loc(#loc30)"
    "cir.cmp lt %26, %27 : !s32i loc(#loc30)"

def checkUpperBoundFlipRejects : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_sorted_insert.cir"
  checkRejectListSortedInsert "_Z18list_sorted_insertP4Nodei" (advUpperBoundFlip text) .unknown
    "out-of-subset" "uses heap allocation"

/-- Sibling texts are not sorted-insert-shaped (no upper-bound
    chase + single-`malloc` swing: read-only traversals, the
    unlink + free, the allocating deep copy, the whole-chain
    free). -/
def checkSibsNotListSortedInsert : IO Nat := do
  let mut n := 0
  for (f, nm) in [("tests/cir/list_copy.cir", "list_copy"),
      ("tests/cir/list_find.cir", "list_find"),
      ("tests/cir/list_erase.cir", "list_erase"),
      ("tests/cir/list_clear.cir", "list_clear"),
      ("tests/cir/list_append.cir", "list_append"),
      ("tests/cir/list_length.cir", "list_length"),
      ("tests/cir/linked_reverse.cir", "linked_reverse"),
      ("tests/cir/list_rev.cir", "list_rev"),
      ("tests/cir/push_front.cir", "push_front")] do
    let text ← IO.FS.readFile f
    match parseModule text with
    | none =>
      throw (IO.userError s!"reject-sortedinsert: {nm} corpus failed to parse")
    | some m =>
      if m.funcs.any isListSortedInsertShape then
        throw (IO.userError s!"reject-sortedinsert: {nm} text wrongly sortedinsert-shaped")
      IO.println s!"PASS reject-sortedinsert {nm}-not-sortedinsert [shape-exact]"
      n := n + 1
  pure n

/-- `list_sorted_insert` text is not sibling-shaped (a sorted
    chase with the upper-bound `le` compare plus the allocating
    swing: no plain find hit, no unlink + free, no deep copy,
    no whole-chain free). -/
def checkListSortedInsertNotSibs : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_sorted_insert.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-sortedinsert: list_sorted_insert corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z18list_sorted_insertP4Nodei") with
    | none =>
      throw (IO.userError "reject-sortedinsert: list_sorted_insert not found")
    | some raw =>
      if isListCopyShape raw then
        throw (IO.userError "reject-sortedinsert: list_sorted_insert text wrongly copy-shaped")
      if isListFindShape raw then
        throw (IO.userError "reject-sortedinsert: list_sorted_insert text wrongly find-shaped")
      if isListEraseShape raw then
        throw (IO.userError "reject-sortedinsert: list_sorted_insert text wrongly erase-shaped")
      if isListClearShape raw then
        throw (IO.userError "reject-sortedinsert: list_sorted_insert text wrongly clear-shaped")
      if isListAppendShape raw then
        throw (IO.userError "reject-sortedinsert: list_sorted_insert text wrongly listappend-shaped")
      if isListLengthShape raw then
        throw (IO.userError "reject-sortedinsert: list_sorted_insert text wrongly listlength-shaped")
      if isLinkedReverseShape raw then
        throw (IO.userError "reject-sortedinsert: list_sorted_insert text wrongly linkedreverse-shaped")
      if isPushFrontShape raw then
        throw (IO.userError "reject-sortedinsert: list_sorted_insert text wrongly pushfront-shaped")
      IO.println "PASS reject-sortedinsert sortedinsert-not-sibs [shape-exact]"
      pure 1

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkListSortedInsertPipeline
  passed := passed + c0
  let r1 ← checkThreePtrRejects
  passed := passed + r1
  let r2 ← checkFreeAddedRejects
  passed := passed + r2
  let r3 ← checkUpperBoundFlipRejects
  passed := passed + r3
  let r4 ← checkSibsNotListSortedInsert
  passed := passed + r4
  let r5 ← checkListSortedInsertNotSibs
  passed := passed + r5
  IO.println s!"GOLDENLISTSORTEDINSERT-OK passed={passed}"

end GoldenListSortedInsert
