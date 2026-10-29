-- Golden test for iterative in-place heapsort over
-- `std::vector<int>` (the single-function `heap_sort` entry: seed,
-- heapify drain, extract drain, two shared sift loops; no calls).
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenVecHeapSort.main`).
-- 1. Corpus pipeline: `tests/cir/heap_sort.cir` (real CIRGen
--    output: the 2-param `heap_sort` entry with 4 `cir.while`, 6
--    `cir.if`, 2 `cir.ternary`, 10 `cir.cmp`, 2 `cir.mul`, 4
--    `cir.add`, 2 `cir.sub`, 30 `cir.const`, no casts, 13 `alloca` /
--    78 `load` / 25 `store`, 4 `break`; plus the non-const `at()`
--    composer + the fused `_M_range_check` guard + the non-const
--    `operator[]` leaf + the `size` leaf) validates via
--    `runModulePipeline` with NO oracle facts (uniqueness comes
--    from the single-reference triple on `&`, the M2a
--    single-reference precedent) and emits byte-identical text to
--    `tests/golden/VecHeapSort.lean` (new: entry) and the shared
--    leaves (file order: heap_sort, mut-at, range_check,
--    mut-index, size).
-- 2. Rejection suite: `heap_sort` is not
--    partition/quicksort/merge-shaped and vice versa
--    (arity/call-multiset/op-count); a call inside the would-be
--    heap body hits the call-shape rejection; a wrong-multiset
--    loop hits the fragment rejection.
import Circe.Validator

namespace GoldenVecHeapSort

def checkHeapSortPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/heap_sort.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/VecHeapSort.lean"
  let wantAtMut ← IO.FS.readFile "tests/golden/VecAtMut.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndexMut ← IO.FS.readFile "tests/golden/VecIndexMut.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected heap_sort: {msg}")
  | .ok [("_Z9heap_sortRSt6vectorIiSaIiEEm", gotEntry),
         ("_ZNSt6vectorIiSaIiEE2atEm", gotAtMut),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNSt6vectorIiSaIiEEixEm", gotIndexMut),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for heap_sort entry")
    if gotAtMut != wantAtMut then
      throw (IO.userError "golden mismatch for non-const at() composer")
    if gotRange != wantRange then
      throw (IO.userError "golden mismatch for _M_range_check leaf")
    if gotIndexMut != wantIndexMut then
      throw (IO.userError "golden mismatch for non-const operator[] leaf")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    IO.println "PASS pipeline heap_sort (entry + at-mut + range_check + index-mut + size, no oracle facts)"
    pure 5
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Shape probe: `name` in `file` must (or must not) match `shape`. -/
def checkHeapShape (file entry : String) (shape : RawFunc → Bool)
    (want : Bool) (tag : String) : IO Nat := do
  let text ← IO.FS.readFile file
  match parseModule text with
  | none =>
    throw (IO.userError s!"reject-vecheap: {file} failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == entry) with
    | none => throw (IO.userError s!"reject-vecheap: {entry} not found")
    | some raw =>
      if shape raw != want then
        throw (IO.userError s!"reject-vecheap: {tag} shape verdict wrong")
      IO.println s!"PASS reject-vecheap {tag} [shape-exact]"
      pure 1

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectHeap (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-vecheap: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-vecheap: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-vecheap: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-vecheap {name} [{code}]"
    pure 1

/-- A call inside the would-be heap body: the call-shape rejection
    fires (heap admits no calls). -/
def advHeapCall : String :=
  "module {\n  cir.func @heapcall(%arg0: !cir.ptr<!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E> {llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}, %arg1: !u64i {llvm.noundef}) attributes {\"nothrow\"} {\n    cir.call @other(%arg0) : (!cir.ptr<!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E>) -> ()\n    cir.return\n  }\n}\n"

/-- A wrong-multiset loop: not in the admitted fragment. -/
def advHeapWrong : String :=
  "module {\n  cir.func @heapwrong(%arg0: !u64i {llvm.noundef}) attributes {\"nothrow\"} {\n    %c0 = cir.const 0 : !u64i\n    cir.return\n  }\n}\n"

def heapCir : String := "tests/cir/heap_sort.cir"

def heapName : String :=
  "_Z9heap_sortRSt6vectorIiSaIiEEm"

def partitionCIR : String := "tests/cir/vec_partition.cir"

def partitionName : String :=
  "_Z13vec_partitionRSt6vectorIiSaIiEEi"

def sortCir : String := "tests/cir/vec_merge_sort.cir"

def sortName : String :=
  "_Z14vec_merge_sortRSt6vectorIiSaIiEES2_"

def qsCir : String := "tests/cir/vec_quicksort.cir"

def qsName : String :=
  "_Z13vec_quicksortRSt6vectorIiSaIiEEmm"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkHeapSortPipeline
  passed := passed + c0
  let r1 ← checkHeapShape heapCir heapName isHeapSortShape true "hs-accepts-heap_sort"
  passed := passed + r1
  let r2 ← checkHeapShape partitionCIR partitionName isHeapSortShape false "partition-not-hs-shaped"
  passed := passed + r2
  let r3 ← checkHeapShape heapCir heapName isVecPartitionShape false "hs-not-partition-shaped"
  passed := passed + r3
  let r4 ← checkHeapShape qsCir qsName isHeapSortShape false "qs-not-hs-shaped"
  passed := passed + r4
  let r5 ← checkHeapShape heapCir heapName isVecQuicksortShape false "hs-not-qs-shaped"
  passed := passed + r5
  let r6 ← checkHeapShape sortCir sortName isHeapSortShape false "sort-not-hs-shaped"
  passed := passed + r6
  let r7 ← checkHeapShape heapCir heapName isVecMergeSortShape false "hs-not-sort-shaped"
  passed := passed + r7
  let r8 ← checkRejectHeap "heapcall" advHeapCall .noalias
    "out-of-subset" "admitted call shapes"
  passed := passed + r8
  let r9 ← checkRejectHeap "heapwrong" advHeapWrong .noalias
    "out-of-subset" "admitted Phase-4 fragment"
  passed := passed + r9
  IO.println s!"GOLDENVECHEAPSORT-OK passed={passed}"

end GoldenVecHeapSort
