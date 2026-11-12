-- Golden test for iterative BST insert (`bst_insert` over
-- caller-owned 3-word nodes): pillar-1 tree-kit second shape.
-- The signed key test (`key < cur->key`, `slt` on `!s32i`)
-- steers a read-only descent recording parent and side; a
-- duplicate key returns the old root untouched, otherwise one
-- fresh 3-word node (`key`, null, null) is attached at the
-- empty child link (left at index 1, right at index 2) and the
-- old root returned. An empty tree returns the fresh node.
-- The write leg runs after the loop: one `nnew3`, one
-- `psetVal`, one `psetNext`, one `psetRight`, one attach
-- store. A null/missing/dead link is loud.
-- Correctness needs the BST invariant (a proof hypothesis, not
-- a runtime check); the pure oracle is `BTree.binsert`, and
-- the memory predicate is `TreeSeg`.
--
-- Run from the repo root via the driver (`lake exe circe-test`
-- runs `GoldenBstInsert.main`).
-- 1. Corpus pipeline: `tests/cir/bst_insert.cir` (real CIRGen
--    output: raw `Node*` root + `i32` key in, `Node*` root
--    out; the entry text carries 7 allocas, 30 loads, 20
--    stores, one `cir.while`, four `cir.if`s (hit test +
--    signed left/right descent + null-parent + side swing),
--    4 `cir.cmp` (`ne` null guard + 2 `eq` hit/parent tests +
--    `lt` descent test on `!s32i`), 9 `cir.const`, 12
--    `cir.cast`, 3 `cir.return` (early dup + fresh-node +
--    tail root), one `cir.call @malloc` (the fresh node),
--    one `cir.get_global`, `cir.get_member` `[0]` key /
--    `[1]` left / `[2]` right, one `#cir.ptr<null>`, no
--    `free`/`new`/`delete`/`sub`/`mul`/`ternary`/`nsw`/`for`/
--    `switch`/`try`/`unreachable`)
--    validates via `runModulePipeline` with no oracle facts and
--    emits byte-identical text to
--    `tests/golden/BstInsert.lean` (single-func module: the
--    entry calls nothing, so there are no shared leaves).
-- 2. Shape-exactness both directions: sibling list texts (and
--    the search text) are not bst-insert-shaped (no fresh-node
--    `malloc`, store-light, or miss-only footprints) and the
--    `bst_insert` text is not sibling-shaped (three-field
--    nodes, two guarded link loads, signed `slt` descent,
--    plus the allocating attach leg).
import Circe.Validator

namespace GoldenBstInsert

def checkBstInsertPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/bst_insert.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/BstInsert.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected bst_insert: {msg}")
  | .ok [("bst_insert", gotEntry)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for bst_insert entry")
    IO.println "PASS pipeline bst_insert (entry, no oracle facts)"
    pure 1
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Sibling list texts (and the search text) are not
    bst-insert-shaped (no allocating attach leg: malloc-free,
    store-light, miss-only footprints). -/
def checkSibsNotBstInsert : IO Nat := do
  let mut n := 0
  for (f, nm) in [("tests/cir/list_length.cir", "list_length"),
      ("tests/cir/list_find.cir", "list_find"),
      ("tests/cir/list_append.cir", "list_append"),
      ("tests/cir/list_merge.cir", "list_merge"),
      ("tests/cir/list_erase.cir", "list_erase"),
      ("tests/cir/list_copy.cir", "list_copy"),
      ("tests/cir/list_clear.cir", "list_clear"),
      ("tests/cir/list_sorted_insert.cir", "list_sorted_insert"),
      ("tests/cir/list_unique.cir", "list_unique"),
      ("tests/cir/list_filter.cir", "list_filter"),
      ("tests/cir/bst_search.cir", "bst_search"),
      ("tests/cir/list_rev.cir", "list_rev")] do
    let text ← IO.FS.readFile f
    match parseModule text with
    | none =>
      throw (IO.userError s!"reject-bstinsert: {nm} corpus failed to parse")
    | some m =>
      if m.funcs.any isBstInsertShape then
        throw (IO.userError s!"reject-bstinsert: {nm} text wrongly bst-insert-shaped")
      IO.println s!"PASS reject-bstinsert {nm}-not-bstinsert [shape-exact]"
      n := n + 1
  pure n

/-- `bst_insert` text is not sibling-shaped (three-field nodes
    with a signed two-way descent plus the allocating attach
    leg, not a linear spine or a read-only query). -/
def checkBstInsertNotSibs : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/bst_insert.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-bstinsert: bst_insert corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "bst_insert") with
    | none =>
      throw (IO.userError "reject-bstinsert: bst_insert not found")
    | some raw =>
      if isBstSearchShape raw then
        throw (IO.userError "reject-bstinsert: bst_insert text wrongly bst-search-shaped")
      if isListFindShape raw then
        throw (IO.userError "reject-bstinsert: bst_insert text wrongly list-find-shaped")
      if isListCopyShape raw then
        throw (IO.userError "reject-bstinsert: bst_insert text wrongly list-copy-shaped")
      IO.println "PASS reject-bstinsert bstinsert-not-sibs [shape-exact]"
      pure 1

/-- Tamper probes (report-only shape checks, no gate
    involved): flipping the descent/hit compares or the
    right-link projection each still parse but break the
    per-predicate compare / projection pins (`/tmp` probed:
    all parse, all `isBstInsertShape = false`). -/
def checkTamperBstInsert : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/bst_insert.cir"
  let badLt := text.replace "cir.cmp lt" "cir.cmp ge"
  let badEq := text.replace "cir.cmp eq" "cir.cmp ne"
  let badIdx := text.replace "[2]" "[1]"
  for (bad, nm) in [(badLt, "lt-flip"), (badEq, "eq-flip"),
      (badIdx, "idx-flip")] do
    match parseModule bad with
    | none => throw (IO.userError s!"tamper-bstinsert: {nm} tampered corpus failed to parse")
    | some m =>
      match m.funcs.find? (fun f => f.name == "bst_insert") with
      | none => throw (IO.userError s!"tamper-bstinsert: {nm} entry missing after tamper")
      | some raw =>
        if isBstInsertShape raw then
          throw (IO.userError s!"tamper-bstinsert: {nm} still bst-insert-shaped")
        IO.println s!"PASS tamper-bstinsert {nm}-not-bstinsert [shape-exact]"
  pure 3

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkBstInsertPipeline
  passed := passed + c0
  let r1 ← checkSibsNotBstInsert
  passed := passed + r1
  let r2 ← checkBstInsertNotSibs
  passed := passed + r2
  let t3 ← checkTamperBstInsert
  passed := passed + t3
  IO.println s!"GOLDENBSTINSERT-OK passed={passed}"

end GoldenBstInsert
