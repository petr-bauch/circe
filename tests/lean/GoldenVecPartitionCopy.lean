-- Golden test for dual-record partition (`vec_partition_copy`,
-- the `std::partition_copy` idiom): pillar-2 first dual-record
-- write — the P2-M3 Lomuto predicate test (`a.at(r) < pivot`,
-- signed `slt`) over a read-only input, writing keepers into
-- one caller-sized record and droppers into a second (the M12
-- out-borrow discipline composed twice). Read cursor `r`
-- scans from 0; write cursors `wYes` / `wNo` advance
-- independently; each store is capacity-guarded (short record
-- fails loud); the return is the keeper count (`wYes + wNo =
-- a.size()` at exit, so the dropper count is implied). Pure
-- `List.filter` oracle, twice (keepers and droppers).
--
-- Run from the repo root via the driver (`lake exe circe-test`
-- runs `GoldenVecPartitionCopy.main`).
-- 1. Corpus pipeline: `tests/cir/vec_partition_copy.cir` (real
--    CIRGen output: read-only `a` + caller-sized `yes` + `no` +
--    owned `pivot`, `u64` out; the entry text carries 8
--    allocas, 21 loads, 13 stores, one `cir.while`, one
--    `cir.if`, 2 `cir.cmp` (both `lt`: bound check + signed
--    Lomuto test), 12 `cir.const`, 1 `cir.return`, 3 plain
--    `u64` adds, 6 calls (one `size` + two const `at()` + two
--    non-const `at()` + one range check), no `cir.sub` /
--    `cir.ternary` / `nsw` / `for` / `unreachable`)
--    validates via `runModulePipeline` with no oracle facts and
--    emits byte-identical text to
--    `tests/golden/VecPartitionCopy.lean` (shared leaves —
--    `size`, const/non-const `at()`, `_M_range_check`,
--    const/non-const `operator[]` — reuse their existing
--    goldens, one admission pin, no duplicate gold).
-- 2. Shape-exactness both directions: sibling texts are not
--    partition-copy-shaped and the `vec_partition_copy` text is
--    not sibling-shaped (the out-of-place filter shares the
--    read scan and owned scalar but writes one record under a
--    single `if`; the caller-record cousins squeeze/reverse
--    into one record; the in-place scans differ in footprint
--    and guard).
import Circe.Validator

namespace GoldenVecPartitionCopy

def checkPartitionCopyPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_partition_copy.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/VecPartitionCopy.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  let wantAt ← IO.FS.readFile "tests/golden/VecAt.lean"
  let wantAtMut ← IO.FS.readFile "tests/golden/VecAtMut.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndex ← IO.FS.readFile "tests/golden/VecIndex.lean"
  let wantIndexMut ← IO.FS.readFile "tests/golden/VecIndexMut.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_partition_copy: {msg}")
  | .ok [("_Z18vec_partition_copyRKSt6vectorIiSaIiEERS1_S4_i", gotEntry),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize),
         ("_ZNKSt6vectorIiSaIiEE2atEm", gotAt),
         ("_ZNSt6vectorIiSaIiEE2atEm", gotAtMut),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNKSt6vectorIiSaIiEEixEm", gotIndex),
         ("_ZNSt6vectorIiSaIiEEixEm", gotIndexMut)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for vec_partition_copy entry")
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
    IO.println "PASS pipeline vec_partition_copy (entry + size + at + at-mut + range_check + index + index-mut, no oracle facts)"
    pure 7
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Sibling texts are not partition-copy-shaped (different
    signatures, entry profiles, and cursor discipline: the
    out-of-place filter shares the read scan and owned scalar
    but writes a single record under a single `if`; the
    caller-record squeeze/reverse cousins write one record;
    the in-place scans differ in footprint and guard). -/
def checkSibsNotVecPartitionCopy : IO Nat := do
  let mut n := 0
  for (f, nm) in [("tests/cir/vec_copy_if.cir", "vec_copy_if"),
      ("tests/cir/vec_unique_copy.cir", "vec_unique_copy"),
      ("tests/cir/vec_reverse_copy.cir", "vec_reverse_copy"),
      ("tests/cir/vec_unique.cir", "vec_unique"),
      ("tests/cir/vec_remove.cir", "vec_remove"),
      ("tests/cir/vec_partition.cir", "vec_partition"),
      ("tests/cir/vec_transform_add.cir", "vec_transform_add"),
      ("tests/cir/vec_two_sum.cir", "vec_two_sum"),
      ("tests/cir/vec_at_set.cir", "vec_at_set"),
      ("tests/cir/vec_reverse.cir", "vec_reverse"),
      ("tests/cir/max_subarray.cir", "max_subarray"),
      ("tests/cir/heap_sort.cir", "heap_sort")] do
    let text ← IO.FS.readFile f
    match parseModule text with
    | none =>
      throw (IO.userError s!"reject-partitioncopy: {nm} corpus failed to parse")
    | some m =>
      if m.funcs.any isVecPartitionCopyShape then
        throw (IO.userError s!"reject-partitioncopy: {nm} text wrongly partition-copy-shaped")
      IO.println s!"PASS reject-partitioncopy {nm}-not-partitioncopy [shape-exact]"
      n := n + 1
  pure n

/-- `vec_partition_copy` text is not sibling-shaped (a
    dual-record signed partition with two guarded stores, not a
    single-record filter, a seeded squeeze, or a one-record
    reversal). -/
def checkVecPartitionCopyNotSibs : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_partition_copy.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-partitioncopy: vec_partition_copy corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z18vec_partition_copyRKSt6vectorIiSaIiEERS1_S4_i") with
    | none =>
      throw (IO.userError "reject-partitioncopy: vec_partition_copy not found")
    | some raw =>
      if isVecCopyIfShape raw then
        throw (IO.userError "reject-partitioncopy: vec_partition_copy text wrongly copy-if-shaped")
      if isVecUniqueCopyShape raw then
        throw (IO.userError "reject-partitioncopy: vec_partition_copy text wrongly unique-copy-shaped")
      if isVecReverseCopyShape raw then
        throw (IO.userError "reject-partitioncopy: vec_partition_copy text wrongly reverse-copy-shaped")
      IO.println "PASS reject-partitioncopy partitioncopy-not-sibs [shape-exact]"
      pure 1

/-- Tamper probes (report-only shape checks, no gate
    involved): flipping the bound/predicate compares and the
    cursor bumps each still parse but break the per-predicate
    compare / plain-add pins (`/tmp` probed: all parse, all
    `isVecPartitionCopyShape = false`). -/
def checkTamperLt : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_partition_copy.cir"
  let badLt := text.replace "cir.cmp lt" "cir.cmp ge"
  let badAdd := text.replace "cir.add " "cir.sub "
  for (bad, nm) in [(badLt, "lt-flip"), (badAdd, "add-flip")] do
    match parseModule bad with
    | none =>
      throw (IO.userError s!"tamper-partitioncopy: {nm} tampered corpus failed to parse")
    | some m =>
      match m.funcs.find? (fun f => f.name == "_Z18vec_partition_copyRKSt6vectorIiSaIiEERS1_S4_i") with
      | none =>
        throw (IO.userError s!"tamper-partitioncopy: {nm} entry missing after tamper")
      | some raw =>
        if isVecPartitionCopyShape raw then
          throw (IO.userError s!"tamper-partitioncopy: {nm} still partition-copy-shaped")
        IO.println s!"PASS tamper-partitioncopy {nm}-not-partitioncopy [shape-exact]"
  pure 2

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkPartitionCopyPipeline
  passed := passed + c0
  let r1 ← checkSibsNotVecPartitionCopy
  passed := passed + r1
  let r2 ← checkVecPartitionCopyNotSibs
  passed := passed + r2
  let t3 ← checkTamperLt
  passed := passed + t3
  IO.println s!"GOLDENVECPARTITIONCOPY-OK passed={passed}"

end GoldenVecPartitionCopy
