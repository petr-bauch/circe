-- Golden test for sorted-range intersection (`vec_intersect`,
-- the `std::set_intersection` idiom): pillar-2 P2-M11, the first
-- two-cursor scan over sorted `std::vector<int>` inputs — `a`/`b`
-- read-only, common heads recorded once into the caller-sized
-- `out`, survivor count returned, no overflow leg (guard-justified,
-- total).
--
-- Run from the repo root via the driver (`lake exe circe-test`
-- runs `GoldenVecIntersect.main`).
-- 1. Corpus pipeline: `tests/cir/vec_intersect.cir` (real CIRGen
--    output: two `const vector&` in, one `vector&` out; the entry
--    text carries 1 `cir.while`, 1 `cir.ternary`, 2 `cir.if`,
--    4 `lt` compares, 5 plain `u64` adds, 8 `cir.call @`)
--    validates via `runModulePipeline` with no oracle facts and
--    emits byte-identical text to `tests/golden/VecIntersect.lean`
--    (shared leaves — `size`, non-const `at()`,
--    `_M_range_check`, non-const `operator[]` — reuse their
--    existing goldens, no duplicate gold).
-- 2. Shape-exactness both directions: sibling texts are not
--    intersect-shaped and `vec_intersect` text is not
--    sibling-shaped (the two-vector merge is the closest analog:
--    same three-block footprint, different guard and lockstep).
import Circe.Validator

namespace GoldenVecIntersect

def checkIntersectPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_intersect.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/VecIntersect.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  let wantAtMut ← IO.FS.readFile "tests/golden/VecAtMut.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndexMut ← IO.FS.readFile "tests/golden/VecIndexMut.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_intersect: {msg}")
  | .ok [("_Z13vec_intersectRSt6vectorIiSaIiEES2_S2_", gotEntry),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize),
         ("_ZNSt6vectorIiSaIiEE2atEm", gotAtMut),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNSt6vectorIiSaIiEEixEm", gotIndexMut)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for vec_intersect entry")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    if gotAtMut != wantAtMut then
      throw (IO.userError "golden mismatch for non-const at() composer")
    if gotRange != wantRange then
      throw (IO.userError "golden mismatch for _M_range_check leaf")
    if gotIndexMut != wantIndexMut then
      throw (IO.userError "golden mismatch for non-const operator[] leaf")
    IO.println "PASS pipeline vec_intersect (entry + size + at-mut + range_check + index-mut, no oracle facts)"
    pure 5
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Sibling texts are not intersect-shaped (different signatures,
    guards, and cursor discipline: the two-vector merge, the swap
    scan, the checked-`add` transform, sorts). -/
def checkSibsNotVecIntersect : IO Nat := do
  let mut n := 0
  for (f, nm) in [("tests/cir/vec_merge_into.cir", "vec_merge_into"),
      ("tests/cir/vec_partition.cir", "vec_partition"),
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
      throw (IO.userError s!"reject-intersect: {nm} corpus failed to parse")
    | some m =>
      if m.funcs.any isVecIntersectShape then
        throw (IO.userError s!"reject-intersect: {nm} text wrongly intersect-shaped")
      IO.println s!"PASS reject-intersect {nm}-not-intersect [shape-exact]"
      n := n + 1
  pure n

/-- `vec_intersect` text is not sibling-shaped (a two-cursor
    sorted merge returning a count, not a three-block merge
    returning words, a swap scan, a checked-`add` transform, or a
    scalar read). -/
def checkVecIntersectNotSibs : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_intersect.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-intersect: vec_intersect corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z13vec_intersectRSt6vectorIiSaIiEES2_S2_") with
    | none =>
      throw (IO.userError "reject-intersect: vec_intersect not found")
    | some raw =>
      if isVecMergeIntoShape raw then
        throw (IO.userError "reject-intersect: vec_intersect text wrongly merge-into-shaped")
      if isVecPartitionShape raw then
        throw (IO.userError "reject-intersect: vec_intersect text wrongly partition-shaped")
      if isVecTransformAddShape raw then
        throw (IO.userError "reject-intersect: vec_intersect text wrongly transform-shaped")
      if isVecTwoSumShape raw then
        throw (IO.userError "reject-intersect: vec_intersect text wrongly twosum-shaped")
      IO.println "PASS reject-intersect intersect-not-sibs [shape-exact]"
      pure 1

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkIntersectPipeline
  passed := passed + c0
  let r1 ← checkSibsNotVecIntersect
  passed := passed + r1
  let r2 ← checkVecIntersectNotSibs
  passed := passed + r2
  IO.println s!"GOLDENVECINTERSECT-OK passed={passed}"

end GoldenVecIntersect
