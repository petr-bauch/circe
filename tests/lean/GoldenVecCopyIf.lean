-- Golden test for out-of-place filter (`vec_copy_if`,
-- the `std::copy_if` idiom): pillar-2 P2-M12, the single read-cursor
-- scan over `std::vector<int>` writing non-`x` elements into the
-- caller-sized `out` — read-only `a`, owned `i32` value, survivor
-- count returned, short-`out` leg loud (`AssertFail` via the inner
-- `ult` guard + `.fail`).
--
-- Run from the repo root via the driver (`lake exe circe-test`
-- runs `GoldenVecCopyIf.main`).
-- 1. Corpus pipeline: `tests/cir/vec_copy_if.cir` (real CIRGen
--    output: read-only `a` + caller-sized `out` + owned `x`; the
--    entry text carries 1 `cir.while`, 1 `cir.if`, 2 `cir.cmp`
--    (one `lt` bound check + one signed `ne` keep test), 8
--    `cir.const`, 1 `cir.return`, 6 `cir.alloca`, 15 `cir.load`,
--    9 `cir.store`, 2 plain `u64` adds, 4 `cir.call @` (one
--    `size` + two const `at()` + one non-const `at()`), no
--    `cir.ternary` / `nsw` / `for` / `unreachable`)
--    validates via `runModulePipeline` with no oracle facts and
--    emits byte-identical text to `tests/golden/VecCopyIf.lean`
--    (new entry; shared leaves — const `at()`, non-const `at()`,
--    `_M_range_check`, const/non-const `operator[]`, `size` —
--    reuse their existing goldens, no duplicate gold).
-- 2. Shape-exactness both directions: sibling texts are not
--    copy-if-shaped and `vec_copy_if` text is not
--    sibling-shaped (the erase-compress `vec_remove` is the
--    closest analog: same borrow/value footprint and `ne` keep
--    test, but single borrow with three `at()` calls and no
--    caller-sized `out`; the four calls plus `if` separate it
--    from `vec_transform_add` with no `if`).
import Circe.Validator

namespace GoldenVecCopyIf

def checkCopyIfPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_copy_if.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/VecCopyIf.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  let wantAt ← IO.FS.readFile "tests/golden/VecAt.lean"
  let wantAtMut ← IO.FS.readFile "tests/golden/VecAtMut.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndex ← IO.FS.readFile "tests/golden/VecIndex.lean"
  let wantIndexMut ← IO.FS.readFile "tests/golden/VecIndexMut.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_copy_if: {msg}")
  | .ok [("_Z11vec_copy_ifRKSt6vectorIiSaIiEERS1_i", gotEntry),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize),
         ("_ZNKSt6vectorIiSaIiEE2atEm", gotAt),
         ("_ZNSt6vectorIiSaIiEE2atEm", gotAtMut),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNKSt6vectorIiSaIiEEixEm", gotIndex),
         ("_ZNSt6vectorIiSaIiEEixEm", gotIndexMut)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for vec_copy_if entry")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    if gotAt != wantAt then
      throw (IO.userError "golden mismatch for const at() composer")
    if gotAtMut != wantAtMut then
      throw (IO.userError "golden mismatch for non-const at() composer")
    if gotRange != wantRange then
      throw (IO.userError "golden mismatch for _M_range_check leaf")
    if gotIndex != wantIndex then
      throw (IO.userError "golden mismatch for const operator[] leaf")
    if gotIndexMut != wantIndexMut then
      throw (IO.userError "golden mismatch for non-const operator[] leaf")
    IO.println "PASS pipeline vec_copy_if (entry + size + at + at-mut + range_check + index + index-mut, no oracle facts)"
    pure 7
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Sibling texts are not copy-if-shaped (different signatures,
    guards, and cursor discipline: erase-compress shares the `ne`
    keep test but compacts in place, the merge/partition/transform
    scans differ in footprint and guard, the scalar reads differ
    in return contract). -/
def checkSibsNotVecCopyIf : IO Nat := do
  let mut n := 0
  for (f, nm) in [("tests/cir/vec_remove.cir", "vec_remove"),
      ("tests/cir/vec_merge_into.cir", "vec_merge_into"),
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
      throw (IO.userError s!"reject-copyif: {nm} corpus failed to parse")
    | some m =>
      if m.funcs.any isVecCopyIfShape then
        throw (IO.userError s!"reject-copyif: {nm} text wrongly copy-if-shaped")
      IO.println s!"PASS reject-copyif {nm}-not-copyif [shape-exact]"
      n := n + 1
  pure n

/-- `vec_copy_if` text is not sibling-shaped (an out-of-place
    filter with caller-sized record and count return, not an
    in-place compaction, a two-counter partition, a checked-`add`
    transform, or a scalar search). -/
def checkVecCopyIfNotSibs : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_copy_if.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-copyif: vec_copy_if corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z11vec_copy_ifRKSt6vectorIiSaIiEERS1_i") with
    | none =>
      throw (IO.userError "reject-copyif: vec_copy_if not found")
    | some raw =>
      if isVecRemoveShape raw then
        throw (IO.userError "reject-copyif: vec_copy_if text wrongly remove-shaped")
      if isVecPartitionShape raw then
        throw (IO.userError "reject-copyif: vec_copy_if text wrongly partition-shaped")
      if isVecTransformAddShape raw then
        throw (IO.userError "reject-copyif: vec_copy_if text wrongly transform-shaped")
      if isVecTwoSumShape raw then
        throw (IO.userError "reject-copyif: vec_copy_if text wrongly twosum-shaped")
      IO.println "PASS reject-copyif copyif-not-sibs [shape-exact]"
      pure 1

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkCopyIfPipeline
  passed := passed + c0
  let r1 ← checkSibsNotVecCopyIf
  passed := passed + r1
  let r2 ← checkVecCopyIfNotSibs
  passed := passed + r2
  IO.println s!"GOLDENVECCOPYIF-OK passed={passed}"

end GoldenVecCopyIf
