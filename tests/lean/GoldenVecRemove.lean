-- Golden test for erase-compress (`vec_remove`, the
-- `std::remove` idiom): pillar-2 proposed goal #1 / P2-M9, the
-- first length-changing write — compact survivors forward,
-- return the new logical length (caller owes the erase).
--
-- Run from the repo root via the driver (`lake exe circe-test`
-- runs `GoldenVecRemove.main`).
-- 1. Corpus pipeline: `tests/cir/vec_remove.cir` (real CIRGen
--    output: `std::vector<int>&` + `i32` in, `u64` out; the
--    entry text carries 5 allocas, 15 loads, 8 stores, one
--    `cir.while`, one `cir.if`, 2 `cir.cmp` (`lt` guard + `ne`
--    keep test), 4 calls (one `size` + three non-const `at()`))
--    validates via `runModulePipeline` with no oracle facts and
--    emits byte-identical text to `tests/golden/VecRemove.lean`
--    (shared leaves — `size`, non-const `at()`,
--    `_M_range_check`, non-const `operator[]` — reuse their
--    existing goldens, one admission pin, no duplicate gold).
-- 2. Shape-exactness both directions: sibling texts are not
--    remove-shaped and `vec_remove` text is not sibling-shaped.
import Circe.Validator

namespace GoldenVecRemove

def checkRemovePipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_remove.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/VecRemove.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  let wantAtMut ← IO.FS.readFile "tests/golden/VecAtMut.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndexMut ← IO.FS.readFile "tests/golden/VecIndexMut.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_remove: {msg}")
  | .ok [("_Z10vec_removeRSt6vectorIiSaIiEEi", gotEntry),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize),
         ("_ZNSt6vectorIiSaIiEE2atEm", gotAtMut),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNSt6vectorIiSaIiEEixEm", gotIndexMut)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for vec_remove entry")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    if gotAtMut != wantAtMut then
      throw (IO.userError "golden mismatch for non-const at() composer")
    if gotRange != wantRange then
      throw (IO.userError "golden mismatch for _M_range_check leaf")
    if gotIndexMut != wantIndexMut then
      throw (IO.userError "golden mismatch for non-const operator[] leaf")
    IO.println "PASS pipeline vec_remove (entry + size + at-mut + range_check + index-mut, no oracle facts)"
    pure 5
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Sibling texts are not remove-shaped (different signatures,
    compares, and call counts: the `slt` swap scan, the
    checked-`add` transform, the two-vector merge, sorts). -/
def checkSibsNotVecRemove : IO Nat := do
  let mut n := 0
  for (f, nm) in [("tests/cir/vec_partition.cir", "vec_partition"),
      ("tests/cir/vec_transform_add.cir", "vec_transform_add"),
      ("tests/cir/vec_two_sum.cir", "vec_two_sum"),
      ("tests/cir/vec_selection_sort.cir", "vec_selection_sort"),
      ("tests/cir/vec_at_set.cir", "vec_at_set"),
      ("tests/cir/vec_reverse.cir", "vec_reverse"),
      ("tests/cir/max_subarray.cir", "max_subarray"),
      ("tests/cir/heap_sort.cir", "heap_sort"),
      ("tests/cir/vec_merge_sort.cir", "vec_merge_sort")] do
    let text ← IO.FS.readFile f
    match parseModule text with
    | none =>
      throw (IO.userError s!"reject-remove: {nm} corpus failed to parse")
    | some m =>
      if m.funcs.any isVecRemoveShape then
        throw (IO.userError s!"reject-remove: {nm} text wrongly remove-shaped")
      IO.println s!"PASS reject-remove {nm}-not-remove [shape-exact]"
      n := n + 1
  pure n

/-- `vec_remove` text is not sibling-shaped (a two-cursor
    `ne`-test compaction returning a length, not a swap scan, a
    checked-`add` transform, or a scalar read). -/
def checkVecRemoveNotSibs : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_remove.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-remove: vec_remove corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z10vec_removeRSt6vectorIiSaIiEEi") with
    | none =>
      throw (IO.userError "reject-remove: vec_remove not found")
    | some raw =>
      if isVecPartitionShape raw then
        throw (IO.userError "reject-remove: vec_remove text wrongly partition-shaped")
      if isVecTransformAddShape raw then
        throw (IO.userError "reject-remove: vec_remove text wrongly transform-shaped")
      if isVecTwoSumShape raw then
        throw (IO.userError "reject-remove: vec_remove text wrongly twosum-shaped")
      IO.println "PASS reject-remove remove-not-sibs [shape-exact]"
      pure 1

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkRemovePipeline
  passed := passed + c0
  let r1 ← checkSibsNotVecRemove
  passed := passed + r1
  let r2 ← checkVecRemoveNotSibs
  passed := passed + r2
  IO.println s!"GOLDENVECREMOVE-OK passed={passed}"

end GoldenVecRemove
