-- Golden test for caller-record squeeze (`vec_unique_copy`, the
-- `std::unique_copy` idiom): pillar-2 P2-M16, the P2-M13
-- predecessor-kept squeeze scan writing into a caller-sized
-- record — M12's out-borrow discipline composed with the M13
-- squeeze. The `(1, 1)` seed plants the first survivor (loud
-- when the record is empty); every kept element differs from
-- the last recorded survivor; the survivor count returns with
-- the input untouched and the record prefix squeezed.
--
-- Run from the repo root via the driver (`lake exe circe-test`
-- runs `GoldenVecUniqueCopy.main`).
-- 1. Corpus pipeline: `tests/cir/vec_unique_copy.cir` (real
--    CIRGen output: read-only `a` + caller-sized `out`, `u64`
--    out; the entry text carries 5 allocas, 22 loads,
--    10 stores, one `cir.while`, two `cir.if`, 3 `cir.cmp`
--    (`eq` empty check + `lt` guard + `ne` squeeze test
--    against the record), 18 `cir.const`, 2 `cir.return`,
--    2 plain `u64` adds, 1 `cir.sub` (the `w - 1`
--    predecessor), 8 calls (two `size` + three const `at()`
--    + three non-const `at()`))
--    validates via `runModulePipeline` with no oracle facts and
--    emits byte-identical text to
--    `tests/golden/VecUniqueCopy.lean` (shared leaves —
--    `size`, const/non-const `at()`, `_M_range_check`,
--    const/non-const `operator[]` — reuse their existing
--    goldens, one admission pin, no duplicate gold).
-- 2. Shape-exactness both directions: sibling texts are not
--    unique-copy-shaped and the `vec_unique_copy` text is not
--    sibling-shaped (the in-place squeeze `vec_unique` shares
--    the predecessor-kept scan but compacts one vector with
--    six calls; the out-of-place filter adds an owned scalar
--    and a single `if`; the erase-compress `vec_remove`
--    compares against the value argument with `0` seeds).
import Circe.Validator

namespace GoldenVecUniqueCopy

def checkUniqueCopyPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_unique_copy.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/VecUniqueCopy.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  let wantAt ← IO.FS.readFile "tests/golden/VecAt.lean"
  let wantAtMut ← IO.FS.readFile "tests/golden/VecAtMut.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndexMut ← IO.FS.readFile "tests/golden/VecIndexMut.lean"
  let wantIndex ← IO.FS.readFile "tests/golden/VecIndex.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_unique_copy: {msg}")
  | .ok [("_Z15vec_unique_copyRKSt6vectorIiSaIiEERS1_", gotEntry),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize),
         ("_ZNKSt6vectorIiSaIiEE2atEm", gotAt),
         ("_ZNSt6vectorIiSaIiEE2atEm", gotAtMut),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNSt6vectorIiSaIiEEixEm", gotIndexMut),
         ("_ZNKSt6vectorIiSaIiEEixEm", gotIndex)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for vec_unique_copy entry")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    if gotAt != wantAt then
      throw (IO.userError "golden mismatch for const at() composer")
    if gotAtMut != wantAtMut then
      throw (IO.userError "golden mismatch for non-const at() composer")
    if gotRange != wantRange then
      throw (IO.userError "golden mismatch for _M_range_check leaf")
    if gotIndexMut != wantIndexMut then
      throw (IO.userError "golden mismatch for non-const operator[] leaf")
    if gotIndex != wantIndex then
      throw (IO.userError "golden mismatch for const operator[] leaf")
    IO.println "PASS pipeline vec_unique_copy (entry + size + const/non-const at + range_check + const/non-const index, no oracle facts)"
    pure 7
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Sibling texts are not unique-copy-shaped (different
    signatures, entry profiles, and cursor discipline: the
    in-place squeeze shares the survivor scan but compacts one
    vector with six calls, the out-of-place filter adds an
    owned scalar argument with a single `if`, the
    erase-compress compares against the value argument with
    `0` seeds, the partition/transform/two-sum scans differ in
    footprint and guard). -/
def checkSibsNotVecUniqueCopy : IO Nat := do
  let mut n := 0
  for (f, nm) in [("tests/cir/vec_unique.cir", "vec_unique"),
      ("tests/cir/vec_copy_if.cir", "vec_copy_if"),
      ("tests/cir/vec_remove.cir", "vec_remove"),
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
      throw (IO.userError s!"reject-uniquecopy: {nm} corpus failed to parse")
    | some m =>
      if m.funcs.any isVecUniqueCopyShape then
        throw (IO.userError s!"reject-uniquecopy: {nm} text wrongly unique-copy-shaped")
      IO.println s!"PASS reject-uniquecopy {nm}-not-uniquecopy [shape-exact]"
      n := n + 1
  pure n

/-- `vec_unique_copy` text is not sibling-shaped (a two-vector
    caller-record squeeze with seed store and `ne`-against-`out`
    keep test, not an in-place single-vector squeeze, an
    owned-scalar out-of-place filter, or a value-compare
    compaction). -/
def checkVecUniqueCopyNotSibs : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_unique_copy.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-uniquecopy: vec_unique_copy corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z15vec_unique_copyRKSt6vectorIiSaIiEERS1_") with
    | none =>
      throw (IO.userError "reject-uniquecopy: vec_unique_copy not found")
    | some raw =>
      if isVecUniqueShape raw then
        throw (IO.userError "reject-uniquecopy: vec_unique_copy text wrongly unique-shaped")
      if isVecCopyIfShape raw then
        throw (IO.userError "reject-uniquecopy: vec_unique_copy text wrongly copy-if-shaped")
      if isVecRemoveShape raw then
        throw (IO.userError "reject-uniquecopy: vec_unique_copy text wrongly remove-shaped")
      IO.println "PASS reject-uniquecopy uniquecopy-not-sibs [shape-exact]"
      pure 1

/-- Tamper probes (report-only shape checks, no gate
    involved): flipping the squeeze-test predicate and the
    predecessor-index subtraction each still parse but break
    the per-predicate compare / `sub` pins (`/tmp`
    probed: both parse, both `isVecUniqueCopyShape = false`). -/
def checkTamperNe : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_unique_copy.cir"
  let badNe := text.replace "cir.cmp ne" "cir.cmp eq"
  let badSub := text.replace "cir.sub " "cir.add "
  for (bad, nm) in [(badNe, "ne-flip"), (badSub, "sub-flip")] do
    match parseModule bad with
    | none =>
      throw (IO.userError s!"tamper-uniquecopy: {nm} tampered corpus failed to parse")
    | some m =>
      match m.funcs.find? (fun f => f.name == "_Z15vec_unique_copyRKSt6vectorIiSaIiEERS1_") with
      | none =>
        throw (IO.userError s!"tamper-uniquecopy: {nm} entry missing after tamper")
      | some raw =>
        if isVecUniqueCopyShape raw then
          throw (IO.userError s!"tamper-uniquecopy: {nm} still unique-copy-shaped")
        IO.println s!"PASS tamper-uniquecopy {nm}-not-uniquecopy [shape-exact]"
  pure 2

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkUniqueCopyPipeline
  passed := passed + c0
  let r1 ← checkSibsNotVecUniqueCopy
  passed := passed + r1
  let r2 ← checkVecUniqueCopyNotSibs
  passed := passed + r2
  let t3 ← checkTamperNe
  passed := passed + t3
  IO.println s!"GOLDENVECUNIQUECOPY-OK passed={passed}"

end GoldenVecUniqueCopy
