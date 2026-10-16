-- Golden test for bottom-up merge sort over `std::vector<int>`
-- (the ranged `merge_runs` callee + the `vec_merge_sort` entry:
-- first pipeline whose loop bodies contain calls).
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenVecMergeSort.main`).
-- 1. Corpus pipeline: `tests/cir/vec_merge_sort.cir` (real CIRGen
--    output: the 5-param ranged `merge_runs` callee with 10 `at()`
--    calls, three `cir.while` loops, one `cir.ternary`
--    short-circuit `&&`; plus the 2-param `vec_merge_sort` entry
--    with 4 calls (one `size`, one `merge_runs`, two mut `at()`),
--    three `cir.while` loops, two `cir.if` clamps; plus the
--    const/non-const `at()` composers + the fused `_M_range_check`
--    guard + both `operator[]` leaves + the `size` leaf) validates
--    via `runModulePipeline` with NO oracle facts (uniqueness comes
--    from the `nonnull + dereferenceable + noundef` attr triple,
--    the M2a single-reference precedent) and emits byte-identical
--    text to `tests/golden/VecMergeRuns.lean` and
--    `tests/golden/VecMergeSort.lean` (new: callee + entry) and the
--    shared leaves (file order: merge_runs, const-at, mut-at,
--    vec_merge_sort, size, range_check, const-index, mut-index).
-- 2. Rejection suite: the `merge_runs` text is not sort-shaped and
--    vice versa (arity/call-targets), `vec_merge_into` /
--    `vec_two_sum` / `vec_binary_search` / `vec_at_set` texts are
--    neither runs- nor sort-shaped, a self-recursive 2-vector entry
--    hits the dedicated vector wrong-shape rejection, a bare vector
--    pointer without the attr triple hits `alias-reject`.
import Circe.Validator

namespace GoldenVecMergeSort

def vecTriple : String :=
  "{llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}"

def vecRec : String :=
  "!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E"

def vecSizeEv : String :=
  "_ZNKSt6vectorIiSaIiEE4sizeEv"

def checkSortPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_merge_sort.cir"
  let wantRuns ← IO.FS.readFile "tests/golden/VecMergeRuns.lean"
  let wantAt ← IO.FS.readFile "tests/golden/VecAt.lean"
  let wantAtMut ← IO.FS.readFile "tests/golden/VecAtMut.lean"
  let wantSort ← IO.FS.readFile "tests/golden/VecMergeSort.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndex ← IO.FS.readFile "tests/golden/VecIndex.lean"
  let wantIndexMut ← IO.FS.readFile "tests/golden/VecIndexMut.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_merge_sort: {msg}")
  | .ok [("_Z10merge_runsRKSt6vectorIiSaIiEERS1_mmm", gotRuns),
         ("_ZNKSt6vectorIiSaIiEE2atEm", gotAt),
         ("_ZNSt6vectorIiSaIiEE2atEm", gotAtMut),
         ("_Z14vec_merge_sortRSt6vectorIiSaIiEES2_", gotSort),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNKSt6vectorIiSaIiEEixEm", gotIndex),
         ("_ZNSt6vectorIiSaIiEEixEm", gotIndexMut)] =>
    if gotRuns != wantRuns then
      throw (IO.userError "golden mismatch for merge_runs callee")
    if gotAt != wantAt then
      throw (IO.userError "golden mismatch for const at() composer")
    if gotAtMut != wantAtMut then
      throw (IO.userError "golden mismatch for non-const at() composer")
    if gotSort != wantSort then
      throw (IO.userError "golden mismatch for vec_merge_sort entry")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    if gotRange != wantRange then
      throw (IO.userError "golden mismatch for _M_range_check leaf")
    if gotIndex != wantIndex then
      throw (IO.userError "golden mismatch for const operator[] leaf")
    if gotIndexMut != wantIndexMut then
      throw (IO.userError "golden mismatch for non-const operator[] leaf")
    IO.println "PASS pipeline vec_merge_sort (merge_runs + at + at-mut + sort + size + range_check + index + index-mut, no oracle facts)"
    pure 8
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Shape probe: `name` in `file` must (or must not) match `shape`. -/
def checkShape (file entry : String) (shape : RawFunc → Bool)
    (want : Bool) (tag : String) : IO Nat := do
  let text ← IO.FS.readFile file
  match parseModule text with
  | none =>
    throw (IO.userError s!"reject-vecsort: {file} failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == entry) with
    | none => throw (IO.userError s!"reject-vecsort: {entry} not found")
    | some raw =>
      if shape raw != want then
        throw (IO.userError s!"reject-vecsort: {tag} shape verdict wrong")
      IO.println s!"PASS reject-vecsort {tag} [shape-exact]"
      pure 1

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectSort (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-vecsort: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-vecsort: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-vecsort: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-vecsort {name} [{code}]"
    pure 1

/-- Self-recursive 2-vector entry: the call-multiset pin (no
    self-call) rejects via the wrong-shape branch. -/
def advRecursiveSort : String :=
  "module {\n  cir.func @vwsrecsort(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ") attributes {\"nothrow\"} {\n"
  ++ "    %s = cir.call @" ++ vecSizeEv ++ "(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> !u64i\n"
  ++ "    cir.call @vwsrecsort(%arg0, %arg1) : (!cir.ptr<" ++ vecRec ++ ">, !cir.ptr<" ++ vecRec ++ ">) -> ()\n"
  ++ "    cir.return\n  }\n}"

/-- Bare vector pointers without the attr triple: the alias
    discipline rejects before shapes are even consulted. -/
def advBareSortPtr : String :=
  "module {\n  cir.func @vwsbaresort(%arg0: !cir.ptr<" ++ vecRec ++ "> {llvm.noundef}, %arg1: !cir.ptr<" ++ vecRec ++ "> {llvm.noundef}) attributes {\"nothrow\"} {\n"
  ++ "    cir.return\n  }\n}"

def sortCir : String := "tests/cir/vec_merge_sort.cir"

def mergeIntoCir : String := "tests/cir/vec_merge_into.cir"

def twoSumCir : String := "tests/cir/vec_two_sum.cir"

def binSearchCir : String := "tests/cir/vec_binary_search.cir"

def atSetCir : String := "tests/cir/vec_at_set.cir"

def runsName : String :=
  "_Z10merge_runsRKSt6vectorIiSaIiEERS1_mmm"

def sortName : String :=
  "_Z14vec_merge_sortRSt6vectorIiSaIiEES2_"

def mergeIntoName : String :=
  "_Z14vec_merge_intoRKSt6vectorIiSaIiEES3_RS1_"

def twoSumName : String :=
  "_Z11vec_two_sumRKSt6vectorIiSaIiEEi"

def binSearchName : String :=
  "_Z17vec_binary_searchRKSt6vectorIiSaIiEEi"

def atSetName : String :=
  "_Z10vec_at_setRSt6vectorIiSaIiEEmi"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkSortPipeline
  passed := passed + c0
  let r1 ← checkShape sortCir runsName isVecMergeRunsShape true "runs-accepts-merge_runs"
  passed := passed + r1
  let r2 ← checkShape sortCir sortName isVecMergeSortShape true "sort-accepts-vec_merge_sort"
  passed := passed + r2
  let r3 ← checkShape sortCir runsName isVecMergeSortShape false "runs-not-sort-shaped"
  passed := passed + r3
  let r4 ← checkShape sortCir sortName isVecMergeRunsShape false "sort-not-runs-shaped"
  passed := passed + r4
  let r5 ← checkShape mergeIntoCir mergeIntoName isVecMergeRunsShape false "merge_into-not-runs-shaped"
  passed := passed + r5
  let r6 ← checkShape mergeIntoCir mergeIntoName isVecMergeSortShape false "merge_into-not-sort-shaped"
  passed := passed + r6
  let r7 ← checkShape twoSumCir twoSumName isVecMergeRunsShape false "two_sum-not-runs-shaped"
  passed := passed + r7
  let r8 ← checkShape twoSumCir twoSumName isVecMergeSortShape false "two_sum-not-sort-shaped"
  passed := passed + r8
  let r9 ← checkShape binSearchCir binSearchName isVecMergeRunsShape false "binsearch-not-runs-shaped"
  passed := passed + r9
  let r10 ← checkShape binSearchCir binSearchName isVecMergeSortShape false "binsearch-not-sort-shaped"
  passed := passed + r10
  let r11 ← checkShape atSetCir atSetName isVecMergeRunsShape false "atset-not-runs-shaped"
  passed := passed + r11
  let r12 ← checkShape atSetCir atSetName isVecMergeSortShape false "atset-not-sort-shaped"
  passed := passed + r12
  let r13 ← checkRejectSort "vwsrecsort" advRecursiveSort .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r13
  let r14 ← checkRejectSort "vwsbaresort" advBareSortPtr .unknown
    "alias-reject" "single-reference triple"
  passed := passed + r14
  IO.println s!"GOLDENVECMERGESORT-OK passed={passed}"

end GoldenVecMergeSort
