-- Golden test for recursive quicksort over `std::vector<int>`
-- (the single-function `vec_quicksort` entry: two early returns, an
-- inline Lomuto scan loop, the pivot place, two self-calls).
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenVecQuicksort.main`).
-- 1. Corpus pipeline: `tests/cir/vec_quicksort.cir` (real CIRGen
--    output: the 3-param `vec_quicksort` entry with 11 calls (nine
--    mut `at()` + two self), one `cir.while`, three `cir.if`,
--    three `cir.return`; plus the non-const `at()` composer + the
--    fused `_M_range_check` guard + the non-const `operator[]`
--    leaf + the `size` leaf) validates via `runModulePipeline`
--    with NO oracle facts (uniqueness comes from the `nonnull +
--    dereferenceable + noundef` attr triple, the M2a
--    single-reference precedent) and emits byte-identical text to
--    `tests/golden/VecQuicksort.lean` (new: entry) and the shared
--    leaves (file order: quicksort, mut-at, range_check,
--    mut-index, size).
-- 2. Rejection suite: the `vec_quicksort` text is not
--    partition-shaped and vice versa (arity/call-multiset); a
--    self-call with the wrong multiset hits the dedicated
--    recursion rejection; mutual recursion hits the call-shape
--    rejection.
import Circe.Validator

namespace GoldenVecQuicksort

def vecTriple : String :=
  "{llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}"

def vecRecFull : String :=
  "!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E"

def checkQuicksortPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_quicksort.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/VecQuicksort.lean"
  let wantAtMut ← IO.FS.readFile "tests/golden/VecAtMut.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndexMut ← IO.FS.readFile "tests/golden/VecIndexMut.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_quicksort: {msg}")
  | .ok [("_Z13vec_quicksortRSt6vectorIiSaIiEEmm", gotEntry),
         ("_ZNSt6vectorIiSaIiEE2atEm", gotAtMut),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNSt6vectorIiSaIiEEixEm", gotIndexMut),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for vec_quicksort entry")
    if gotAtMut != wantAtMut then
      throw (IO.userError "golden mismatch for non-const at() composer")
    if gotRange != wantRange then
      throw (IO.userError "golden mismatch for _M_range_check leaf")
    if gotIndexMut != wantIndexMut then
      throw (IO.userError "golden mismatch for non-const operator[] leaf")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    IO.println "PASS pipeline vec_quicksort (entry + at-mut + range_check + index-mut + size, no oracle facts)"
    pure 5
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Shape probe: `name` in `file` must (or must not) match `shape`. -/
def checkQsShape (file entry : String) (shape : RawFunc → Bool)
    (want : Bool) (tag : String) : IO Nat := do
  let text ← IO.FS.readFile file
  match parseModule text with
  | none =>
    throw (IO.userError s!"reject-vecqs: {file} failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == entry) with
    | none => throw (IO.userError s!"reject-vecqs: {entry} not found")
    | some raw =>
      if shape raw != want then
        throw (IO.userError s!"reject-vecqs: {tag} shape verdict wrong")
      IO.println s!"PASS reject-vecqs {tag} [shape-exact]"
      pure 1

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectQs (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-vecqs: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-vecqs: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-vecqs: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-vecqs {name} [{code}]"
    pure 1

/-- Self-call with the wrong multiset (no `at()` calls, so not the
    quicksort shape): falls through to the dedicated rule-9
    recursion rejection. -/
def advSelfWrongShape : String :=
  "module {\n  cir.func @qsrec(%arg0: !cir.ptr<" ++ vecRecFull ++ "> " ++ vecTriple ++ ", %arg1: !u64i {llvm.noundef}, %arg2: !u64i {llvm.noundef}) attributes {\"nothrow\"} {\n"
  ++ "    cir.call @qsrec(%arg0, %arg1, %arg2) : (!cir.ptr<" ++ vecRecFull ++ ">, !u64i, !u64i) -> ()\n"
  ++ "    cir.call @qsrec(%arg0, %arg1, %arg2) : (!cir.ptr<" ++ vecRecFull ++ ">, !u64i, !u64i) -> ()\n"
  ++ "    cir.return\n  }\n}"

/-- Mutual recursion (`a` calls `b`): no self-call, no admitted
    shape — the call-shape rejection fires. -/
def advMutual : String :=
  "module {\n  cir.func @ma(%arg0: !u64i {llvm.noundef}) attributes {\"nothrow\"} {\n"
  ++ "    cir.call @mb(%arg0) : (!u64i) -> ()\n"
  ++ "    cir.return\n  }\n"
  ++ "  cir.func @mb(%arg0: !u64i {llvm.noundef}) attributes {\"nothrow\"} {\n"
  ++ "    cir.return\n  }\n}"

def qsCir : String := "tests/cir/vec_quicksort.cir"

def qsName : String :=
  "_Z13vec_quicksortRSt6vectorIiSaIiEEmm"

def partitionCIR : String := "tests/cir/vec_partition.cir"

def partitionName : String :=
  "_Z13vec_partitionRSt6vectorIiSaIiEEi"

def sortCir : String := "tests/cir/vec_merge_sort.cir"

def sortName : String :=
  "_Z14vec_merge_sortRSt6vectorIiSaIiEES2_"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkQuicksortPipeline
  passed := passed + c0
  let r1 ← checkQsShape qsCir qsName isVecQuicksortShape true "qs-accepts-vec_quicksort"
  passed := passed + r1
  let r2 ← checkQsShape partitionCIR partitionName isVecQuicksortShape false "partition-not-qs-shaped"
  passed := passed + r2
  let r3 ← checkQsShape qsCir qsName isVecPartitionShape false "qs-not-partition-shaped"
  passed := passed + r3
  let r4 ← checkQsShape sortCir sortName isVecQuicksortShape false "sort-not-qs-shaped"
  passed := passed + r4
  let r5 ← checkQsShape qsCir qsName isVecMergeSortShape false "qs-not-sort-shaped"
  passed := passed + r5
  let r6 ← checkRejectQs "qsrec" advSelfWrongShape .noalias
    "out-of-subset" "calls itself"
  passed := passed + r6
  let r7 ← checkRejectQs "ma" advMutual .noalias
    "out-of-subset" "admitted call shapes"
  passed := passed + r7
  IO.println s!"GOLDENVECQUICKSORT-OK passed={passed}"

end GoldenVecQuicksort
