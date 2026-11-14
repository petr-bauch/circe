-- Golden test for first-difference query (`vec_mismatch`,
-- the `std::mismatch` idiom): pillar-2 P2-M19, the first dual-read
-- query returning a position. Single cursor `i` walks both
-- read-only inputs under the short-circuit `&&` guard; the first
-- unequal `at()` pair returns `i`, exhaustion returns the shorter
-- length. No writes, no records, no loud leg on valid input.
--
-- Run from the repo root via the driver (`lake exe circe-test`
-- runs `GoldenVecMismatch.main`).
-- 1. Corpus pipeline: `tests/cir/vec_mismatch.cir` (real CIRGen
--    output: two read-only `vector<int>`; the entry text carries
--    1 `cir.while`, 1 `cir.if`, 3 `cir.cmp` (two `lt` bound checks
--    + one `ne` difference test), 1 `cir.ternary`, 5 `cir.const`,
--    2 `cir.return`, 4 `cir.alloca`, 15 `cir.load`, 6 `cir.store`,
--    3 `cir.yield`, 4 `cir.call @` (one `size` + two const
--    `at()`), no `nsw` / `sub` / `mul` / `for` / `unreachable` /
--    `switch` / `try` / `operator[]` / non-const `at()`)
--    validates via `runModulePipeline` with no oracle facts and
--    emits byte-identical text to `tests/golden/VecMismatch.lean`
--    (new entry; shared leaves — `size`, const `at()`,
--    `_M_range_check`, const `operator[]` — reuse their existing
--    goldens, no duplicate gold).
-- 2. Shape-exactness both directions: sibling texts are not
--    mismatch-shaped and `vec_mismatch` text is not
--    sibling-shaped (the dual-read `vec_intersect` is the closest
--    analog: same borrow footprint but three params, a write
--    record, and a signed-compare guard; the `copy_if` filter
--    shares the single cursor and `ne` test but writes through a
--    caller record).
import Circe.Validator

namespace GoldenVecMismatch

def checkMismatchPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_mismatch.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/VecMismatch.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  let wantAt ← IO.FS.readFile "tests/golden/VecAt.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndex ← IO.FS.readFile "tests/golden/VecIndex.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_mismatch: {msg}")
  | .ok [("_Z12vec_mismatchRKSt6vectorIiSaIiEES3_", gotEntry),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize),
         ("_ZNKSt6vectorIiSaIiEE2atEm", gotAt),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNKSt6vectorIiSaIiEEixEm", gotIndex)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for vec_mismatch entry")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    if gotAt != wantAt then
      throw (IO.userError "golden mismatch for const at() composer")
    if gotRange != wantRange then
      throw (IO.userError "golden mismatch for _M_range_check leaf")
    if gotIndex != wantIndex then
      throw (IO.userError "golden mismatch for const operator[] leaf")
    IO.println "PASS pipeline vec_mismatch (entry + size + at + range_check + index, no oracle facts)"
    pure 5
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Sibling texts are not mismatch-shaped (different signatures,
    guards, and cursor discipline: the dual-read intersection
    shares the two-borrow footprint but writes a record under a
    signed guard, the copy-if filter shares the cursor and `ne`
    test but writes through a caller record, the scalar scans
    differ in footprint and return contract). -/
def checkSibsNotVecMismatch : IO Nat := do
  let mut n := 0
  for (f, nm) in [("tests/cir/vec_intersect.cir", "vec_intersect"),
      ("tests/cir/vec_copy_if.cir", "vec_copy_if"),
      ("tests/cir/vec_remove.cir", "vec_remove"),
      ("tests/cir/vec_difference.cir", "vec_difference"),
      ("tests/cir/vec_union.cir", "vec_union"),
      ("tests/cir/vec_two_sum.cir", "vec_two_sum"),
      ("tests/cir/vec_reverse.cir", "vec_reverse"),
      ("tests/cir/max_subarray.cir", "max_subarray"),
      ("tests/cir/heap_sort.cir", "heap_sort"),
      ("tests/cir/vec_merge_sort.cir", "vec_merge_sort")] do
    let text ← IO.FS.readFile f
    match parseModule text with
    | none =>
      throw (IO.userError s!"reject-mismatch: {nm} corpus failed to parse")
    | some m =>
      if m.funcs.any isVecMismatchShape then
        throw (IO.userError s!"reject-mismatch: {nm} text wrongly mismatch-shaped")
      IO.println s!"PASS reject-mismatch {nm}-not-mismatch [shape-exact]"
      n := n + 1
  pure n

/-- `vec_mismatch` text is not sibling-shaped (a read-only
    dual-input position query with a ternary guard and `ne` early
    return, not a record writer, an in-place compaction, or a
    scalar search). -/
def checkVecMismatchNotSibs : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_mismatch.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-mismatch: vec_mismatch corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z12vec_mismatchRKSt6vectorIiSaIiEES3_") with
    | none =>
      throw (IO.userError "reject-mismatch: vec_mismatch not found")
    | some raw =>
      if isVecIntersectShape raw then
        throw (IO.userError "reject-mismatch: vec_mismatch text wrongly intersect-shaped")
      if isVecCopyIfShape raw then
        throw (IO.userError "reject-mismatch: vec_mismatch text wrongly copyif-shaped")
      if isVecRemoveShape raw then
        throw (IO.userError "reject-mismatch: vec_mismatch text wrongly remove-shaped")
      if isVecTwoSumShape raw then
        throw (IO.userError "reject-mismatch: vec_mismatch text wrongly twosum-shaped")
      IO.println "PASS reject-mismatch mismatch-not-sibs [shape-exact]"
      pure 1

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkMismatchPipeline
  passed := passed + c0
  let r1 ← checkSibsNotVecMismatch
  passed := passed + r1
  let r2 ← checkVecMismatchNotSibs
  passed := passed + r2
  IO.println s!"GOLDENVECMISMATCH-OK passed={passed}"

end GoldenVecMismatch
