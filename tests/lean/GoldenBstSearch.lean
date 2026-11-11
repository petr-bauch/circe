-- Golden test for iterative BST search (`bst_search` over
-- caller-owned 3-word nodes): pillar-1 tree-kit first shape.
-- The signed key test (`key < cur->key`, `slt` on `!s32i`)
-- steers a read-only descent with an explicit `cur != nullptr`
-- guard; hit returns `1`, miss (or empty input) returns `0`.
-- The entry never allocates; a null/missing/dead read is loud.
-- Correctness needs the BST invariant (a proof hypothesis, not
-- a runtime check); the pure oracle is `BTree.contains` over
-- `flatten`, and the memory predicate is `TreeSeg`.
--
-- Run from the repo root via the driver (`lake exe circe-test`
-- runs `GoldenBstSearch.main`).
-- 1. Corpus pipeline: `tests/c/bst_search.cir` (real CIRGen
--    output: raw `Node*` root + `i32` key in, `i32` found-flag
--    out; the entry text carries 4 allocas, 14 loads, 7 stores,
--    one `cir.while`, two `cir.if`s (hit test + signed
--    left/right descent), 3 `cir.cmp` (`ne` null guard + `eq`
--    hit test + `lt` descent test on `!s32i`), 3 `cir.const`,
--    7 `cir.cast`, 2 `cir.return` (early `1` + tail `0`),
--    `cir.get_member` `[0]` key (twice: eq test + descent
--    test), `[1]` left link, `[2]` right link (the `[2]`
--    projection plus the per-predicate compare pins separate it
--    from every linear list shape), one `#cir.ptr<null>`, no
--    calls, no `malloc`/`free`, no `cir.sub`/`cir.mul`/
--    `cir.ternary`/`nsw`/`for`/`switch`/`unreachable`)
--    validates via `runModulePipeline` with no oracle facts and
--    emits byte-identical text to
--    `tests/golden/BstSearch.lean` (single-func module: the
--    entry calls nothing, so there are no shared leaves).
-- 2. Shape-exactness both directions: sibling list texts are
--    not bst-search-shaped (different footprints: two-field
--    nodes, single-link chase, no signed descent) and the
--    `bst_search` text is not sibling-shaped (three-field
--    nodes, two guarded link loads, signed `slt` branch).
import Circe.Validator

namespace GoldenBstSearch

def checkBstSearchPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/bst_search.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/BstSearch.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected bst_search: {msg}")
  | .ok [("bst_search", gotEntry)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for bst_search entry")
    IO.println "PASS pipeline bst_search (entry, no oracle facts)"
    pure 1
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Sibling list texts are not bst-search-shaped (two-field
    nodes, single-link chase, signed descent absent). -/
def checkSibsNotBstSearch : IO Nat := do
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
      ("tests/cir/list_rev.cir", "list_rev")] do
    let text ← IO.FS.readFile f
    match parseModule text with
    | none =>
      throw (IO.userError s!"reject-bstsearch: {nm} corpus failed to parse")
    | some m =>
      if m.funcs.any isBstSearchShape then
        throw (IO.userError s!"reject-bstsearch: {nm} text wrongly bst-search-shaped")
      IO.println s!"PASS reject-bstsearch {nm}-not-bstsearch [shape-exact]"
      n := n + 1
  pure n

/-- `bst_search` text is not sibling-shaped (three-field nodes
    with a signed two-way descent, not a linear spine). -/
def checkBstSearchNotSibs : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/bst_search.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-bstsearch: bst_search corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "bst_search") with
    | none =>
      throw (IO.userError "reject-bstsearch: bst_search not found")
    | some raw =>
      if isListLengthShape raw then
        throw (IO.userError "reject-bstsearch: bst_search text wrongly list-length-shaped")
      if isListFindShape raw then
        throw (IO.userError "reject-bstsearch: bst_search text wrongly list-find-shaped")
      if isListCopyShape raw then
        throw (IO.userError "reject-bstsearch: bst_search text wrongly list-copy-shaped")
      IO.println "PASS reject-bstsearch bstsearch-not-sibs [shape-exact]"
      pure 1

/-- Tamper probes (report-only shape checks, no gate
    involved): flipping the bound/predicate compares or the
    right-link projection each still parse but break the
    per-predicate compare / projection pins (`/tmp` probed:
    all parse, all `isBstSearchShape = false`). -/
def checkTamperBst : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/bst_search.cir"
  let badLt := text.replace "cir.cmp lt" "cir.cmp ge"
  let badEq := text.replace "cir.cmp eq" "cir.cmp ne"
  let badIdx := text.replace "[2]" "[1]"
  for (bad, nm) in [(badLt, "lt-flip"), (badEq, "eq-flip"),
      (badIdx, "idx-flip")] do
    match parseModule bad with
    | none => throw (IO.userError s!"tamper-bstsearch: {nm} tampered corpus failed to parse")
    | some m =>
      match m.funcs.find? (fun f => f.name == "bst_search") with
      | none => throw (IO.userError s!"tamper-bstsearch: {nm} entry missing after tamper")
      | some raw =>
        if isBstSearchShape raw then
          throw (IO.userError s!"tamper-bstsearch: {nm} still bst-search-shaped")
        IO.println s!"PASS tamper-bstsearch {nm}-not-bstsearch [shape-exact]"
  pure 3

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkBstSearchPipeline
  passed := passed + c0
  let r1 ← checkSibsNotBstSearch
  passed := passed + r1
  let r2 ← checkBstSearchNotSibs
  passed := passed + r2
  let t3 ← checkTamperBst
  passed := passed + t3
  IO.println s!"GOLDENBSTSEARCH-OK passed={passed}"

end GoldenBstSearch
