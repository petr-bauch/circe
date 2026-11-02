-- Golden test for in-place prefix-sum scan (`vec_partial_sum`,
-- the `std::partial_sum` idiom): pillar-2 P2-M10, the first
-- read-after-write scan through the vector — `v.at(i)` is
-- rewritten as the checked sum of the current value and the
-- already-written predecessor, failing loudly on overflow.
--
-- Run from the repo root via the driver (`lake exe circe-test`
-- runs `GoldenVecPartialSum.main`).
-- 1. Corpus pipeline: `tests/cir/vec_partial_sum.cir` (real CIRGen
--    output: `std::vector<int>&` in, vector out; the entry text
--    carries 1 alloca, loads, stores, one `cir.while`, `lt`
--    guard, `sub` predecessor index, checked `add`, calls (one
--    `size` + two non-const `at()`))
--    validates via `runModulePipeline` with no oracle facts and
--    emits byte-identical text to `tests/golden/VecPartialSum.lean`
--    (shared leaves — `size`, non-const `at()`,
--    `_M_range_check`, non-const `operator[]` — reuse their
--    existing goldens, one admission pin, no duplicate gold).
-- 2. Shape-exactness both directions: sibling texts are not
--    partial-sum-shaped and `vec_partial_sum` text is not
--    sibling-shaped.
import Circe.Validator

namespace GoldenVecPartialSum

def checkPartialSumPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_partial_sum.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/VecPartialSum.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  let wantAtMut ← IO.FS.readFile "tests/golden/VecAtMut.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndexMut ← IO.FS.readFile "tests/golden/VecIndexMut.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_partial_sum: {msg}")
  | .ok [("_Z15vec_partial_sumRSt6vectorIiSaIiEE", gotEntry),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize),
         ("_ZNSt6vectorIiSaIiEE2atEm", gotAtMut),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNSt6vectorIiSaIiEEixEm", gotIndexMut)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for vec_partial_sum entry")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    if gotAtMut != wantAtMut then
      throw (IO.userError "golden mismatch for non-const at() composer")
    if gotRange != wantRange then
      throw (IO.userError "golden mismatch for _M_range_check leaf")
    if gotIndexMut != wantIndexMut then
      throw (IO.userError "golden mismatch for non-const operator[] leaf")
    IO.println "PASS pipeline vec_partial_sum (entry + size + at-mut + range_check + index-mut, no oracle facts)"
    pure 5
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Sibling texts are not partial-sum-shaped (different signatures,
    compares, and call counts: the swap scan, the checked-`add`
    transform, the two-vector merge, sorts). -/
def checkSibsNotVecPartialSum : IO Nat := do
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
      throw (IO.userError s!"reject-partialsum: {nm} corpus failed to parse")
    | some m =>
      if m.funcs.any isVecPartialSumShape then
        throw (IO.userError s!"reject-partialsum: {nm} text wrongly partial-sum-shaped")
      IO.println s!"PASS reject-partialsum {nm}-not-partialsum [shape-exact]"
      n := n + 1
  pure n

/-- `vec_partial_sum` text is not sibling-shaped (an in-place
    read-after-write checked scan returning words, not a swap
    scan, a checked-`add` transform, or a scalar read). -/
def checkVecPartialSumNotSibs : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_partial_sum.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-partialsum: vec_partial_sum corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z15vec_partial_sumRSt6vectorIiSaIiEE") with
    | none =>
      throw (IO.userError "reject-partialsum: vec_partial_sum not found")
    | some raw =>
      if isVecPartitionShape raw then
        throw (IO.userError "reject-partialsum: vec_partial_sum text wrongly partition-shaped")
      if isVecTransformAddShape raw then
        throw (IO.userError "reject-partialsum: vec_partial_sum text wrongly transform-shaped")
      if isVecTwoSumShape raw then
        throw (IO.userError "reject-partialsum: vec_partial_sum text wrongly twosum-shaped")
      IO.println "PASS reject-partialsum partialsum-not-sibs [shape-exact]"
      pure 1

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkPartialSumPipeline
  passed := passed + c0
  let r1 ← checkSibsNotVecPartialSum
  passed := passed + r1
  let r2 ← checkVecPartialSumNotSibs
  passed := passed + r2
  IO.println s!"GOLDENVECPARTIALSUM-OK passed={passed}"

end GoldenVecPartialSum
