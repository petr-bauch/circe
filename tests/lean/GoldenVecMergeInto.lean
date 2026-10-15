-- Golden test for the out-of-place two-pointer `std::vector<int>`
-- merge (`vec_merge_into` pipeline + rejection suite).
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenVecMergeInto.main`).
-- 1. Corpus pipeline: `tests/cir/vec_merge_into.cir` (real CIRGen
--    output: the two-`sharedBorrow` + one-`mutBorrow` merge entry with
--    14 calls (6 const `at()` + 4 `size` + 4 non-const `at()`), three
--    `cir.while` loops, one `cir.ternary` short-circuit `&&`; plus
--    the const/non-const `at()` composers + the fused
--    `_M_range_check` guard + both `operator[]` leaves + the `size`
--    leaf) validates via `runModulePipeline` with NO oracle facts
--    (uniqueness comes from the `nonnull + dereferenceable +
--    noundef` attr triple, the M2a single-reference precedent) and
--    emits byte-identical text to `tests/golden/VecMergeInto.lean`
--    (new: entry) and the shared leaves
--    `tests/golden/{VecSize,VecAt,VecAtMut,VecRangeCheck,VecIndex,VecIndexMut}.lean`
--    (file order: entry, size, const-at, mut-at, range_check,
--    const-index, mut-index).
-- 2. Rejection suite: `vec_two_sum` / `vec_binary_search` /
--    `vec_at_set` texts are not merge-shaped (arity/loops/ternary),
--    a self-recursive 3-vector entry hits the dedicated vector
--    wrong-shape rejection, a bare vector pointer without the attr
--    triple hits `alias-reject`.
import Circe.Validator

namespace GoldenVecMergeInto

def vecTriple : String :=
  "{llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}"

def vecRec : String :=
  "!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E"

def vecSizeEv : String :=
  "_ZNKSt6vectorIiSaIiEE4sizeEv"

def checkMergePipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_merge_into.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/VecMergeInto.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  let wantAt ← IO.FS.readFile "tests/golden/VecAt.lean"
  let wantAtMut ← IO.FS.readFile "tests/golden/VecAtMut.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndex ← IO.FS.readFile "tests/golden/VecIndex.lean"
  let wantIndexMut ← IO.FS.readFile "tests/golden/VecIndexMut.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_merge_into: {msg}")
  | .ok [("_Z14vec_merge_intoRKSt6vectorIiSaIiEES3_RS1_", gotEntry),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize),
         ("_ZNKSt6vectorIiSaIiEE2atEm", gotAt),
         ("_ZNSt6vectorIiSaIiEE2atEm", gotAtMut),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNKSt6vectorIiSaIiEEixEm", gotIndex),
         ("_ZNSt6vectorIiSaIiEEixEm", gotIndexMut)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for vec_merge_into entry")
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
    IO.println "PASS pipeline vec_merge_into (entry + size + at + at-mut + range_check + index + index-mut, no oracle facts)"
    pure 7
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectMerge (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-vecmerge: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-vecmerge: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-vecmerge: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-vecmerge {name} [{code}]"
    pure 1

/-- Self-recursive 3-vector merge-shaped entry: the call-multiset pin
    (no self-call) rejects via the wrong-shape branch. -/
def advRecursive : String :=
  "module {\n  cir.func @vwsrec(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg2: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ") attributes {\"nothrow\"} {\n"
  ++ "    %s = cir.call @" ++ vecSizeEv ++ "(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> !u64i\n"
  ++ "    cir.call @vwsrec(%arg0, %arg1, %arg2) : (!cir.ptr<" ++ vecRec ++ ">, !cir.ptr<" ++ vecRec ++ ">, !cir.ptr<" ++ vecRec ++ ">) -> ()\n"
  ++ "    cir.return\n  }\n}"

/-- `vec_two_sum` text is not merge-shaped (2 params, no ternary). -/
def checkTwoSumNotMerge : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_two_sum.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-vecmerge: vec_two_sum corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z11vec_two_sumRKSt6vectorIiSaIiEEi") with
    | none => throw (IO.userError "reject-vecmerge: vec_two_sum not found")
    | some raw =>
      if isVecMergeIntoShape raw then
        throw (IO.userError "reject-vecmerge: vec_two_sum text wrongly merge-shaped")
      IO.println "PASS reject-vecmerge vec_two_sum-not-merge [shape-exact]"
      pure 1

/-- `vec_binary_search` text is not merge-shaped either (2 params,
    single loop, no ternary). -/
def checkBinSearchNotMerge : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_binary_search.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-vecmerge: vec_binary_search corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z17vec_binary_searchRKSt6vectorIiSaIiEEi") with
    | none => throw (IO.userError "reject-vecmerge: vec_binary_search not found")
    | some raw =>
      if isVecMergeIntoShape raw then
        throw (IO.userError "reject-vecmerge: vec_binary_search text wrongly merge-shaped")
      IO.println "PASS reject-vecmerge vec_binary_search-not-merge [shape-exact]"
      pure 1

/-- `vec_at_set` text is not merge-shaped (straight-line store, no
    loops, no ternary). -/
def checkAtSetNotMerge : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_at_set.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-vecmerge: vec_at_set corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z10vec_at_setRSt6vectorIiSaIiEEmi") with
    | none => throw (IO.userError "reject-vecmerge: vec_at_set not found")
    | some raw =>
      if isVecMergeIntoShape raw then
        throw (IO.userError "reject-vecmerge: vec_at_set text wrongly merge-shaped")
      IO.println "PASS reject-vecmerge vec_at_set-not-merge [shape-exact]"
      pure 1

/-- Bare vector pointers without the attr triple: the alias
    discipline rejects before shapes are even consulted. -/
def advBareVecPtr : String :=
  "module {\n  cir.func @vwsbare(%arg0: !cir.ptr<" ++ vecRec ++ "> {llvm.noundef}, %arg1: !cir.ptr<" ++ vecRec ++ "> {llvm.noundef}, %arg2: !cir.ptr<" ++ vecRec ++ "> {llvm.noundef}) attributes {\"nothrow\"} {\n"
  ++ "    cir.return\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkMergePipeline
  passed := passed + c0
  let r1 ← checkTwoSumNotMerge
  passed := passed + r1
  let r2 ← checkBinSearchNotMerge
  passed := passed + r2
  let r3 ← checkAtSetNotMerge
  passed := passed + r3
  let r4 ← checkRejectMerge "vwsrec" advRecursive .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r4
  let r5 ← checkRejectMerge "vwsbare" advBareVecPtr .unknown
    "alias-reject" "single-reference triple"
  passed := passed + r5
  IO.println s!"GOLDENVECMERGEINTO-OK passed={passed}"

end GoldenVecMergeInto
