-- Golden test for in-place `std::vector<int>` reverse (the
-- countdown two-pointer swap entry: first loop whose body both calls
-- checked leaves and stores through `vecSet`).
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenVecReverse.main`).
-- 1. Corpus pipeline: `tests/cir/vec_reverse.cir` (real CIRGen
--    output: the 1-param `vec_reverse` entry with one `size` call,
--    two mut `at()` calls and one `cir.while` countdown loop; plus
--    the `size` leaf, the non-const `at()` composer, the fused
--    `_M_range_check` guard and the non-const `operator[]` leaf)
--    validates via `runModulePipeline` with NO oracle facts
--    (uniqueness comes from the `nonnull + dereferenceable +
--    noundef` attr triple, the M2a single-reference precedent) and
--    emits byte-identical text to `tests/golden/VecReverse.lean`
--    (new: the entry) and the shared leaves
--    (`tests/golden/{VecSize,VecAtMut,VecRangeCheck,VecIndexMut}.lean`,
--    file order: vec_reverse, size, at-mut, range_check, index-mut).
-- 2. Rejection suite: the mut `at()` text is not reverse-shaped and
--    vice versa (arity/call-targets), `vec_merge_into` /
--    `vec_merge_sort` / `vec_two_sum` texts are not reverse-shaped,
--    a self-recursive 1-vector entry hits the dedicated vector
--    wrong-shape rejection, a bare vector pointer without the attr
--    triple hits `alias-reject`.
import Circe.Validator

namespace GoldenVecReverse

def vecTriple : String :=
  "{llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}"

def vecRec : String :=
  "!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E"

def vecSizeEv : String :=
  "_ZNKSt6vectorIiSaIiEE4sizeEv"

def checkReversePipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_reverse.cir"
  let wantRev ← IO.FS.readFile "tests/golden/VecReverse.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  let wantAtMut ← IO.FS.readFile "tests/golden/VecAtMut.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndexMut ← IO.FS.readFile "tests/golden/VecIndexMut.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_reverse: {msg}")
  | .ok [("_Z11vec_reverseRSt6vectorIiSaIiEE", gotRev),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize),
         ("_ZNSt6vectorIiSaIiEE2atEm", gotAtMut),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNSt6vectorIiSaIiEEixEm", gotIndexMut)] =>
    if gotRev != wantRev then
      throw (IO.userError "golden mismatch for vec_reverse entry")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    if gotAtMut != wantAtMut then
      throw (IO.userError "golden mismatch for non-const at() composer")
    if gotRange != wantRange then
      throw (IO.userError "golden mismatch for _M_range_check leaf")
    if gotIndexMut != wantIndexMut then
      throw (IO.userError "golden mismatch for non-const operator[] leaf")
    IO.println "PASS pipeline vec_reverse (entry + size + at-mut + range_check + index-mut, no oracle facts)"
    pure 5
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Shape probe: `name` in `file` must (or must not) match `shape`. -/
def checkShape (file entry : String) (shape : RawFunc → Bool)
    (want : Bool) (tag : String) : IO Nat := do
  let text ← IO.FS.readFile file
  match parseModule text with
  | none =>
    throw (IO.userError s!"reject-vecrev: {file} failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == entry) with
    | none => throw (IO.userError s!"reject-vecrev: {entry} not found")
    | some raw =>
      if shape raw != want then
        throw (IO.userError s!"reject-vecrev: {tag} shape verdict wrong")
      IO.println s!"PASS reject-vecrev {tag} [shape-exact]"
      pure 1

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectRev (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-vecrev: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-vecrev: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-vecrev: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-vecrev {name} [{code}]"
    pure 1

/-- Self-recursive 1-vector entry: the call-multiset pin (no
    self-call) rejects via the wrong-shape branch. -/
def advRecursiveRev : String :=
  "module {\n  cir.func @vwrecrev(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ") attributes {\"nothrow\"} {\n"
  ++ "    %s = cir.call @" ++ vecSizeEv ++ "(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> !u64i\n"
  ++ "    cir.call @vwrecrev(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> ()\n"
  ++ "    cir.return\n  }\n}"

/-- Bare vector pointers without the attr triple: the alias
    discipline rejects before shapes are even consulted. -/
def advBareRevPtr : String :=
  "module {\n  cir.func @vwbarerev(%arg0: !cir.ptr<" ++ vecRec ++ "> {llvm.noundef}) attributes {\"nothrow\"} {\n"
  ++ "    cir.return\n  }\n}"

def reverseCir : String := "tests/cir/vec_reverse.cir"

def mergeIntoCir : String := "tests/cir/vec_merge_into.cir"

def sortCir : String := "tests/cir/vec_merge_sort.cir"

def twoSumCir : String := "tests/cir/vec_two_sum.cir"

def reverseName : String :=
  "_Z11vec_reverseRSt6vectorIiSaIiEE"

def atMutName : String :=
  "_ZNSt6vectorIiSaIiEE2atEm"

def mergeIntoName : String :=
  "_Z14vec_merge_intoRKSt6vectorIiSaIiEES3_RS1_"

def sortName : String :=
  "_Z14vec_merge_sortRSt6vectorIiSaIiEES2_"

def twoSumName : String :=
  "_Z11vec_two_sumRKSt6vectorIiSaIiEEi"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkReversePipeline
  passed := passed + c0
  let r1 ← checkShape reverseCir reverseName isVecReverseShape true "reverse-accepts-vec_reverse"
  passed := passed + r1
  let r2 ← checkShape reverseCir atMutName isVecReverseShape false "atmut-not-reverse-shaped"
  passed := passed + r2
  let r3 ← checkShape reverseCir reverseName isVecMergeSortShape false "reverse-not-sort-shaped"
  passed := passed + r3
  let r4 ← checkShape sortCir sortName isVecReverseShape false "sort-not-reverse-shaped"
  passed := passed + r4
  let r5 ← checkShape mergeIntoCir mergeIntoName isVecReverseShape false "merge_into-not-reverse-shaped"
  passed := passed + r5
  let r6 ← checkShape twoSumCir twoSumName isVecReverseShape false "two_sum-not-reverse-shaped"
  passed := passed + r6
  let r7 ← checkRejectRev "vwrecrev" advRecursiveRev .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r7
  let r8 ← checkRejectRev "vwbarerev" advBareRevPtr .unknown
    "alias-reject" "single-reference triple"
  passed := passed + r8
  IO.println s!"GOLDENVECREVERSE-OK passed={passed}"

end GoldenVecReverse
