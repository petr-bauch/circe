-- Golden test for iterative BST inorder (`bst_inorder` over
-- caller-owned 3-word nodes + caller out buffer): the explicit
-- 64-word stack traversal (push left spine, pop-emit-swing-right).
-- Both pointer params carry `__restrict__` (tree and out buffer
-- are disjoint, a proof hypothesis); the capacity guard is
-- unsigned (`n < capU`), the stack guard is `top >= 64`; either
-- overflow leg returns `-1`, never a silent truncation.
-- A null/missing/dead link is loud; cycles are out of contract
-- (the proof assumes an acyclic BST input). Correctness needs
-- the BST invariant (a proof hypothesis, not a runtime check);
-- the pure oracle is the inorder flatten, and the memory
-- predicate is `TreeSeg` plus the out-buffer prefix.
--
-- Run from the repo root via the driver (`lake exe circe-test`
-- runs `GoldenBstInorder.main`).
-- 1. Corpus pipeline: `tests/cir/bst_inorder.cir` (real CIRGen
--    output: `Node*` root + `i32*` out + `i32` cap in, `i32`
--    count out; the entry text carries 8 allocas, 26 loads, 17
--    stores, two `cir.while`, two `cir.if`s, one `cir.ternary`
--    (guard disjunction), 5 `cir.cmp` (2 `ne` null guards + 1
--    `gt` capacity test + 2 `ge` stack/capacity tests, no `eq`
--    or `lt`), 14 `cir.const`, 17 `cir.cast`, 2 `cir.add`
--    (`nsw`), 1 `cir.sub`, 3 `cir.return`, 4 `cir.yield`,
--    `cir.get_member` `[0]` key / `[1]` left / `[2]` right, no
--    `cir.call`, no `malloc`/`free`/`new`/`delete`/`switch`/
--    `try`/`unreachable`)
--    validates via `runModulePipeline` with the `noalias`
--    oracle fact and emits byte-identical text to
--    `tests/golden/BstInorder.lean` (single-func module: the
--    entry calls nothing, so there are no shared leaves).
-- 2. Shape-exactness both directions: sibling list texts (and
--    the search/insert texts) are not bst-inorder-shaped (no
--    explicit 64-word stack, no pop-emit leg, no `restrict`
--    pair), and the `bst_inorder` text is not sibling-shaped
--    (three-field nodes, two `cir.while`s, capacity-then-stack
--    unsigned guards, out-buffer emit).
import Circe.Validator

namespace GoldenBstInorder

/-- The oracle fact pinning the two-pointer disjointness
    (root tree vs out buffer, both `__restrict__`). -/
def inorderFact : OracleFact := ⟨"bst_inorder", .noalias⟩

def checkBstInorderPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/bst_inorder.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/BstInorder.lean"
  match runModulePipeline text [inorderFact] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected bst_inorder: {msg}")
  | .ok [("bst_inorder", gotEntry)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for bst_inorder entry")
    IO.println "PASS pipeline bst_inorder (entry, noalias fact)"
    pure 1
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Sibling list texts (and the search/insert texts) are not
    bst-inorder-shaped (no explicit stack with pop-emit leg,
    no `restrict` reader+writer pair). -/
def checkSibsNotBstInorder : IO Nat := do
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
      ("tests/cir/bst_insert.cir", "bst_insert"),
      ("tests/cir/list_rev.cir", "list_rev")] do
    let text ← IO.FS.readFile f
    match parseModule text with
    | none =>
      throw (IO.userError s!"reject-bstinorder: {nm} corpus failed to parse")
    | some m =>
      if m.funcs.any isBstInorderShape then
        throw (IO.userError s!"reject-bstinorder: {nm} text wrongly bst-inorder-shaped")
      IO.println s!"PASS reject-bstinorder {nm}-not-bstinorder [shape-exact]"
      n := n + 1
  pure n

/-- `bst_inorder` text is not sibling-shaped (three-field nodes
    with an explicit stack and an out-buffer emit leg, not a
    linear spine or a read-only query). -/
def checkBstInorderNotSibs : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/bst_inorder.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-bstinorder: bst_inorder corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "bst_inorder") with
    | none =>
      throw (IO.userError "reject-bstinorder: bst_inorder not found")
    | some raw =>
      if isBstSearchShape raw then
        throw (IO.userError "reject-bstinorder: bst_inorder text wrongly bst-search-shaped")
      if isBstInsertShape raw then
        throw (IO.userError "reject-bstinorder: bst_inorder text wrongly bst-insert-shaped")
      if isListFindShape raw then
        throw (IO.userError "reject-bstinorder: bst_inorder text wrongly list-find-shaped")
      IO.println "PASS reject-bstinorder bstinorder-not-sibs [shape-exact]"
      pure 1

/-- Tamper probes (report-only shape checks, no gate
    involved): flipping the capacity/stack compares or the
    right-link projection each still parse but break the
    per-predicate compare / projection pins (`/tmp` probed:
    all parse, all `isBstInorderShape = false`). -/
def checkTamperBstInorder : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/bst_inorder.cir"
  let badGe := text.replace "cir.cmp ge" "cir.cmp lt"
  let badNe := text.replace "cir.cmp ne" "cir.cmp eq"
  let badIdx := text.replace "[2]" "[1]"
  for (bad, nm) in [(badGe, "ge-flip"), (badNe, "ne-flip"),
      (badIdx, "idx-flip")] do
    match parseModule bad with
    | none => throw (IO.userError s!"tamper-bstinorder: {nm} tampered corpus failed to parse")
    | some m =>
      match m.funcs.find? (fun f => f.name == "bst_inorder") with
      | none => throw (IO.userError s!"tamper-bstinorder: {nm} entry missing after tamper")
      | some raw =>
        if isBstInorderShape raw then
          throw (IO.userError s!"tamper-bstinorder: {nm} still bst-inorder-shaped")
        IO.println s!"PASS tamper-bstinorder {nm}-not-bstinorder [shape-exact]"
  pure 3

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkBstInorderPipeline
  passed := passed + c0
  let r1 ← checkSibsNotBstInorder
  passed := passed + r1
  let r2 ← checkBstInorderNotSibs
  passed := passed + r2
  let t3 ← checkTamperBstInorder
  passed := passed + t3
  IO.println s!"GOLDENBSTINORDER-OK passed={passed}"

end GoldenBstInorder
