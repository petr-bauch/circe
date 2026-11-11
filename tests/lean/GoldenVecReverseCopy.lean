-- Golden test for caller-record out-of-place reverse
-- (`vec_reverse_copy`): pillar-2 P2-M17, the M12 countdown
-- reversal writing into a caller-sized record — M12's `j`
-- discipline (seeded at `a.size()`, `0 < j` guard, unconditional
-- `sub`) meets the M16 sequential write cursor `w` (seeded at
-- 0, per-step `w < out.size()` guard, loud `AssertFail` on
-- overflow). The empty vector short-circuits up front, so there
-- is no seed leg; the invariant ties both cursors to the
-- record (`lo.take w = (la.drop j).reverse`, `w + j =
-- la.length`); at exit `j = 0` gives the full `la.reverse`
-- over the pure `List.reverse` oracle. Returns the copied
-- count with the input untouched.
--
-- Run from the repo root via the driver (`lake exe circe-test`
-- runs `GoldenVecReverseCopy.main`).
-- 1. Corpus pipeline: `tests/cir/vec_reverse_copy.cir` (real
--    CIRGen output: read-only `a` + caller-sized `out`, `u64`
--    out; the entry text carries 5 allocas, 13 loads,
--    9 stores, one `cir.while`, one `cir.if`, 2 `cir.cmp`
--    (`eq` empty check + `lt` countdown guard), 12
--    `cir.const`, 2 `cir.return`, 1 `cir.sub` (the `--j`
--    countdown), 1 plain `u64` add (the `w + 1` advance),
--    4 calls (two `size` + const `at()` + non-const `at()`))
--    validates via `runModulePipeline` with no oracle facts and
--    emits byte-identical text to
--    `tests/golden/VecReverseCopy.lean` (shared leaves —
--    `size`, const/non-const `at()`, `_M_range_check`,
--    const/non-const `operator[]` — reuse their existing
--    goldens, one admission pin, no duplicate gold).
-- 2. Shape-exactness both directions: sibling texts are not
--    reverse-copy-shaped and the `vec_reverse_copy` text is not
--    sibling-shaped (the caller-record squeeze shares the
--    two-borrow footprint and per-step guard but seeds and
--    keep-tests against the record; the in-place reversal
--    shares the countdown scan but compacts one vector; the
--    out-of-place filter adds an owned scalar and a single
--    `if`).
import Circe.Validator

namespace GoldenVecReverseCopy

def checkReverseCopyPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_reverse_copy.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/VecReverseCopy.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  let wantAt ← IO.FS.readFile "tests/golden/VecAt.lean"
  let wantAtMut ← IO.FS.readFile "tests/golden/VecAtMut.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndexMut ← IO.FS.readFile "tests/golden/VecIndexMut.lean"
  let wantIndex ← IO.FS.readFile "tests/golden/VecIndex.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_reverse_copy: {msg}")
  | .ok [("_Z16vec_reverse_copyRKSt6vectorIiSaIiEERS1_", gotEntry),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize),
         ("_ZNKSt6vectorIiSaIiEE2atEm", gotAt),
         ("_ZNSt6vectorIiSaIiEE2atEm", gotAtMut),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNSt6vectorIiSaIiEEixEm", gotIndexMut),
         ("_ZNKSt6vectorIiSaIiEEixEm", gotIndex)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for vec_reverse_copy entry")
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
    IO.println "PASS pipeline vec_reverse_copy (entry + size + const/non-const at + range_check + const/non-const index, no oracle facts)"
    pure 7
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Sibling texts are not reverse-copy-shaped (different
    signatures, entry profiles, and cursor discipline: the
    caller-record squeeze shares the two-borrow footprint but
    seeds and keep-tests against the record, the in-place
    reversal shares the countdown scan but compacts one
    vector, the out-of-place filter adds an owned scalar
    argument with a single `if`, the erase-compress compares
    against the value argument with `0` seeds, the
    partition/transform/two-sum scans differ in footprint and
    guard). -/
def checkSibsNotVecReverseCopy : IO Nat := do
  let mut n := 0
  for (f, nm) in [("tests/cir/vec_unique_copy.cir", "vec_unique_copy"),
      ("tests/cir/vec_unique.cir", "vec_unique"),
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
      throw (IO.userError s!"reject-reversecopy: {nm} corpus failed to parse")
    | some m =>
      if m.funcs.any isVecReverseCopyShape then
        throw (IO.userError s!"reject-reversecopy: {nm} text wrongly reverse-copy-shaped")
      IO.println s!"PASS reject-reversecopy {nm}-not-reversecopy [shape-exact]"
      n := n + 1
  pure n

/-- `vec_reverse_copy` text is not sibling-shaped (a countdown
    record fill with a `0 < j` guard and `w`-only capacity
    check, not a seeded squeeze with a keep test against the
    record, an in-place single-vector reversal, or an
    owned-scalar out-of-place filter). -/
def checkVecReverseCopyNotSibs : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_reverse_copy.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-reversecopy: vec_reverse_copy corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z16vec_reverse_copyRKSt6vectorIiSaIiEERS1_") with
    | none =>
      throw (IO.userError "reject-reversecopy: vec_reverse_copy not found")
    | some raw =>
      if isVecUniqueCopyShape raw then
        throw (IO.userError "reject-reversecopy: vec_reverse_copy text wrongly unique-copy-shaped")
      if isVecUniqueShape raw then
        throw (IO.userError "reject-reversecopy: vec_reverse_copy text wrongly unique-shaped")
      if isVecReverseShape raw then
        throw (IO.userError "reject-reversecopy: vec_reverse_copy text wrongly reverse-shaped")
      IO.println "PASS reject-reversecopy reversecopy-not-sibs [shape-exact]"
      pure 1

/-- Tamper probes (report-only shape checks, no gate
    involved): flipping the countdown-guard predicate and the
    countdown subtraction each still parse but break the
    per-predicate compare / `sub` pins (`/tmp`
    probed: both parse, both `isVecReverseCopyShape = false`). -/
def checkTamperLt : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_reverse_copy.cir"
  let badLt := text.replace "cir.cmp lt" "cir.cmp ge"
  let badSub := text.replace "cir.sub " "cir.add "
  for (bad, nm) in [(badLt, "lt-flip"), (badSub, "sub-flip")] do
    match parseModule bad with
    | none =>
      throw (IO.userError s!"tamper-reversecopy: {nm} tampered corpus failed to parse")
    | some m =>
      match m.funcs.find? (fun f => f.name == "_Z16vec_reverse_copyRKSt6vectorIiSaIiEERS1_") with
      | none =>
        throw (IO.userError s!"tamper-reversecopy: {nm} entry missing after tamper")
      | some raw =>
        if isVecReverseCopyShape raw then
          throw (IO.userError s!"tamper-reversecopy: {nm} still reverse-copy-shaped")
        IO.println s!"PASS tamper-reversecopy {nm}-not-reversecopy [shape-exact]"
  pure 2

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkReverseCopyPipeline
  passed := passed + c0
  let r1 ← checkSibsNotVecReverseCopy
  passed := passed + r1
  let r2 ← checkVecReverseCopyNotSibs
  passed := passed + r2
  let t3 ← checkTamperLt
  passed := passed + t3
  IO.println s!"GOLDENVECREVERSECOPY-OK passed={passed}"

end GoldenVecReverseCopy
