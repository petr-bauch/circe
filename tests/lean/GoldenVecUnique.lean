-- Golden test for adjacent-duplicate squeeze (`vec_unique`, the
-- `std::unique` idiom): pillar-2 P2-M13, the keep-iff-different
-- scan over `std::vector<int>` — each element survives iff it
-- differs from the previous survivor, the write cursor seeds at
-- `1` so the predecessor read is guard-justified, the new
-- logical length returns (caller owes the erase).
--
-- Run from the repo root via the driver (`lake exe circe-test`
-- runs `GoldenVecUnique.main`).
-- 1. Corpus pipeline: `tests/cir/vec_unique.cir` (real CIRGen
--    output: `std::vector<int>&` in, `u64` out; the entry text
--    carries 4 allocas, 19 loads, 8 stores, one `cir.while`,
--    two `cir.if`, 3 `cir.cmp` (`ueq` empty check + `ult` bound
--    + `ne` keep test), 14 `cir.const`, 2 `cir.return`, 6
--    calls (two `size` + four non-const `at()`))
--    validates via `runModulePipeline` with no oracle facts and
--    emits byte-identical text to `tests/golden/VecUnique.lean`
--    (shared leaves — `size`, non-const `at()`,
--    `_M_range_check`, non-const `operator[]` — reuse their
--    existing goldens, one admission pin, no duplicate gold).
-- 2. Shape-exactness both directions: sibling texts are not
--    unique-shaped and `vec_unique` text is not sibling-shaped
--    (the erase-compress `vec_remove` is the closest analog:
--    same borrow footprint and `ne` keep test, but the keep
--    compares against the value argument with a single `if`
--    and seeds both cursors at `0`; the entry `if`, the `1`
--    seeds, and the predecessor `sub` separate `vec_unique`
--    from `vec_remove` with no `if`-free confusion).
import Circe.Validator

namespace GoldenVecUnique

def checkUniquePipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_unique.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/VecUnique.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  let wantAtMut ← IO.FS.readFile "tests/golden/VecAtMut.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndexMut ← IO.FS.readFile "tests/golden/VecIndexMut.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_unique: {msg}")
  | .ok [("_Z10vec_uniqueRSt6vectorIiSaIiEE", gotEntry),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize),
         ("_ZNSt6vectorIiSaIiEE2atEm", gotAtMut),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNSt6vectorIiSaIiEEixEm", gotIndexMut)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for vec_unique entry")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    if gotAtMut != wantAtMut then
      throw (IO.userError "golden mismatch for non-const at() composer")
    if gotRange != wantRange then
      throw (IO.userError "golden mismatch for _M_range_check leaf")
    if gotIndexMut != wantIndexMut then
      throw (IO.userError "golden mismatch for non-const operator[] leaf")
    IO.println "PASS pipeline vec_unique (entry + size + at-mut + range_check + index-mut, no oracle facts)"
    pure 5
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Sibling texts are not unique-shaped (different signatures,
    entry profiles, and cursor discipline: erase-compress shares
    the `ne` keep test but compares against the value argument
    with one `if` and `0` seeds, the out-of-place filter adds a
    caller record, the merge/partition/transform scans differ in
    footprint and guard, the scalar reads differ in return
    contract). -/
def checkSibsNotVecUnique : IO Nat := do
  let mut n := 0
  for (f, nm) in [("tests/cir/vec_remove.cir", "vec_remove"),
      ("tests/cir/vec_copy_if.cir", "vec_copy_if"),
      ("tests/cir/vec_partition.cir", "vec_partition"),
      ("tests/cir/vec_transform_add.cir", "vec_transform_add"),
      ("tests/cir/vec_two_sum.cir", "vec_two_sum"),
      ("tests/cir/vec_at_set.cir", "vec_at_set"),
      ("tests/cir/vec_reverse.cir", "vec_reverse"),
      ("tests/cir/max_subarray.cir", "max_subarray"),
      ("tests/cir/heap_sort.cir", "heap_sort"),
      ("tests/cir/vec_merge_sort.cir", "vec_merge_sort")] do
    let text ← IO.FS.readFile f
    match parseModule text with
    | none =>
      throw (IO.userError s!"reject-unique: {nm} corpus failed to parse")
    | some m =>
      if m.funcs.any isVecUniqueShape then
        throw (IO.userError s!"reject-unique: {nm} text wrongly unique-shaped")
      IO.println s!"PASS reject-unique {nm}-not-unique [shape-exact]"
      n := n + 1
  pure n

/-- `vec_unique` text is not sibling-shaped (a single-borrow
    squeeze with entry check and predecessor-kept survivors,
    not an in-place value-compare compaction, a two-counter
    partition, or an out-of-place filter). -/
def checkVecUniqueNotSibs : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_unique.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-unique: vec_unique corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z10vec_uniqueRSt6vectorIiSaIiEE") with
    | none =>
      throw (IO.userError "reject-unique: vec_unique not found")
    | some raw =>
      if isVecRemoveShape raw then
        throw (IO.userError "reject-unique: vec_unique text wrongly remove-shaped")
      if isVecPartitionShape raw then
        throw (IO.userError "reject-unique: vec_unique text wrongly partition-shaped")
      if isVecCopyIfShape raw then
        throw (IO.userError "reject-unique: vec_unique text wrongly copy-if-shaped")
      IO.println "PASS reject-unique unique-not-sibs [shape-exact]"
      pure 1

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkUniquePipeline
  passed := passed + c0
  let r1 ← checkSibsNotVecUnique
  passed := passed + r1
  let r2 ← checkVecUniqueNotSibs
  passed := passed + r2
  IO.println s!"GOLDENVECUNIQUE-OK passed={passed}"

end GoldenVecUnique
