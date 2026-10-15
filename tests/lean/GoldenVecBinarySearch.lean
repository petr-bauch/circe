-- Golden test for binary search over `const std::vector<int>&`:
-- `vec_binary_search` pipeline + rejection suite.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenVecBinarySearch.main`).
-- 1. Corpus pipeline: `tests/cir/vec_binary_search.cir` (real CIRGen
--    output: the `const&` + `int` binary-search entry with the
--    half-open `[lo, hi)` `cir.while` loop, safe-midpoint `sub` +
--    `shift(right` + `add`, one `at()` read, `eq`/`lt` branches, miss
--    returns `size()`; plus the `size` leaf + the fused `at()`
--    composer + the fused `_M_range_check` guard + the call-free
--    `operator[]` leaf) validates via `runModulePipeline` with NO
--    oracle facts (uniqueness comes from the `nonnull +
--    dereferenceable + noundef` attr triple, the M2a
--    single-reference precedent) and emits byte-identical text to
--    `tests/golden/{VecBinarySearch,VecSize,VecAt,VecRangeCheck,
--    VecIndex}.lean` (file order: entry, size, at, range_check,
--    index).
-- 2. Rejection suite: `operator[]`-direct entry (bypasses `at()`),
--    `vec_at_sum` text is not binsearch-shaped (for-loop, not
--    while: shape-exactness), `vec_read_sum` text is not
--    binsearch-shaped, self-recursive entry, bare vector pointer
--    without the attr triple (alias discipline) — the first and
--    fourth hit the dedicated vector wrong-shape rejection, the
--    second and third the shape predicate directly, the last
--    `alias-reject`.
import Circe.Validator

namespace GoldenVecBinarySearch

def vecTriple : String :=
  "{llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}"

def vecRec : String :=
  "!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E"

def checkVecBinarySearchPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_binary_search.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/VecBinarySearch.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  let wantAt ← IO.FS.readFile "tests/golden/VecAt.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndex ← IO.FS.readFile "tests/golden/VecIndex.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_binary_search: {msg}")
  | .ok [("_Z17vec_binary_searchRKSt6vectorIiSaIiEEi", gotEntry),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize),
         ("_ZNKSt6vectorIiSaIiEE2atEm", gotAt),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNKSt6vectorIiSaIiEEixEm", gotIndex)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for vec_binary_search entry")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    if gotAt != wantAt then
      throw (IO.userError "golden mismatch for at() composer")
    if gotRange != wantRange then
      throw (IO.userError "golden mismatch for _M_range_check leaf")
    if gotIndex != wantIndex then
      throw (IO.userError "golden mismatch for operator[] leaf")
    IO.println "PASS pipeline vec_binary_search (entry + size + at + range_check + index, no oracle facts)"
    pure 5
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectVecBinarySearch (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-vecbinsearch: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-vecbinsearch: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-vecbinsearch: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-vecbinsearch {name} [{code}]"
    pure 1

def vecSizeEv : String :=
  "_ZNKSt6vectorIiSaIiEE4sizeEv"

def vecIndexEv : String :=
  "_ZNKSt6vectorIiSaIiEEixEm"

/-- `operator[]`-direct entry: reads through the fused leaf in a
    `while` loop, bypassing `at()` — the encapsulation pin rejects. -/
def advDirectIndex : String :=
  "module {\n  cir.func @vdirectindex(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !s32i) -> !u64i attributes {\"nothrow\"} {\n"
  ++ "    %s = cir.call @" ++ vecSizeEv ++ "(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> !u64i\n"
  ++ "    %z = cir.const #cir.int<0> : !u64i\n"
  ++ "    %p = cir.call @" ++ vecIndexEv ++ "(%arg0, %z) : (!cir.ptr<" ++ vecRec ++ ">, !u64i) -> !cir.ptr<!s32i>\n"
  ++ "    %v = cir.load %p : !cir.ptr<!s32i>, !s32i\n"
  ++ "    cir.return %z : !u64i\n  }\n}"

/-- Self-recursive entry: the call-multiset pin (no self-call)
    rejects via the wrong-shape branch. -/
def advRecursive : String :=
  "module {\n  cir.func @vrec(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !s32i) -> !u64i attributes {\"nothrow\"} {\n"
  ++ "    %s = cir.call @" ++ vecSizeEv ++ "(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> !u64i\n"
  ++ "    %r = cir.call @vrec(%arg0, %arg1) : (!cir.ptr<" ++ vecRec ++ ">, !s32i) -> !u64i\n"
  ++ "    cir.return %r : !u64i\n  }\n}"

/-- `vec_at_sum` text is not binsearch-shaped (`cir.for`, not
    `cir.while`; one `size` call, not two): the admission is
    shape-exact, not loop-only. -/
def checkAtSumNotBinSearch : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_at_sum.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-vecbinsearch: vec_at_sum corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z10vec_at_sumRKSt6vectorIiSaIiEE") with
    | none => throw (IO.userError "reject-vecbinsearch: vec_at_sum not found")
    | some raw =>
      if isVecBinarySearchShape raw then
        throw (IO.userError "reject-vecbinsearch: vec_at_sum text wrongly binsearch-shaped")
      IO.println "PASS reject-vecbinsearch vec_at_sum-not-binsearch [shape-exact]"
      pure 1

/-- `vec_read_sum` text is not binsearch-shaped either (no `at()`
    call at all). -/
def checkReadSumNotBinSearch : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_read_sum.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-vecbinsearch: vec_read_sum corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z12vec_read_sumRKSt6vectorIiSaIiEE") with
    | none => throw (IO.userError "reject-vecbinsearch: vec_read_sum not found")
    | some raw =>
      if isVecBinarySearchShape raw then
        throw (IO.userError "reject-vecbinsearch: vec_read_sum text wrongly binsearch-shaped")
      IO.println "PASS reject-vecbinsearch vec_read_sum-not-binsearch [shape-exact]"
      pure 1

/-- Bare vector pointer without the attr triple: the alias
    discipline rejects before shapes are even consulted. -/
def advBareVecPtr : String :=
  "module {\n  cir.func @vbare(%arg0: !cir.ptr<" ++ vecRec ++ "> {llvm.noundef}, %arg1: !s32i) -> !u64i attributes {\"nothrow\"} {\n"
  ++ "    %z = cir.const #cir.int<0> : !u64i\n"
  ++ "    cir.return %z : !u64i\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkVecBinarySearchPipeline
  passed := passed + c0
  let r1 ← checkRejectVecBinarySearch "vdirectindex" advDirectIndex .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r1
  let r2 ← checkAtSumNotBinSearch
  passed := passed + r2
  let r3 ← checkReadSumNotBinSearch
  passed := passed + r3
  let r4 ← checkRejectVecBinarySearch "vrec" advRecursive .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r4
  let r5 ← checkRejectVecBinarySearch "vbare" advBareVecPtr .unknown
    "alias-reject" "single-reference triple"
  passed := passed + r5
  IO.println s!"GOLDENVECBINARYSEARCH-OK passed={passed}"

end GoldenVecBinarySearch
