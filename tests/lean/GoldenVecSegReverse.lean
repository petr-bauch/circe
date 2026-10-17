-- Golden test for in-place `std::vector<int>` segment reverse (the
-- countdown two-pointer swap entry over `[lo, hi)`: same loop body as
-- the whole-range reverse, only the prelude binds `i ← lo`, `j ← hi`).
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenVecSegReverse.main`).
-- 1. Corpus pipeline: `tests/cir/vec_seg_reverse.cir` (real CIRGen
--    output: the 3-param `vec_seg_reverse` entry with two mut `at()`
--    calls and one `cir.while` countdown loop; plus the non-const
--    `at()` composer, the fused `_M_range_check` guard, the non-const
--    `operator[]` leaf and the `size` leaf) validates via
--    `runModulePipeline` with NO oracle facts (uniqueness comes from
--    the `nonnull + dereferenceable + noundef` attr triple, the M2a
--    single-reference precedent) and emits byte-identical text to
--    `tests/golden/VecSegReverse.lean` (new: the entry) and the shared
--    leaves (`tests/golden/{VecAtMut,VecRangeCheck,VecIndexMut,
--    VecSize}.lean`, file order: entry, at-mut, range_check,
--    index-mut, size).
-- 2. Rejection suite: the mut `at()` text is not seg-shaped and vice
--    versa (arity/call-targets), the whole-range `vec_reverse` /
--    `vec_merge_sort` / `vec_merge_into` texts are not seg-shaped, a
--    self-recursive 3-param entry hits the dedicated vector
--    wrong-shape rejection, a bare vector pointer without the attr
--    triple hits `alias-reject`.
import Circe.Validator

namespace GoldenVecSegReverse

def vecTriple : String :=
  "{llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}"

def vecRec : String :=
  "!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E"

def vecSizeEv : String :=
  "_ZNKSt6vectorIiSaIiEE4sizeEv"

def checkSegPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_seg_reverse.cir"
  let wantSeg ← IO.FS.readFile "tests/golden/VecSegReverse.lean"
  let wantAtMut ← IO.FS.readFile "tests/golden/VecAtMut.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndexMut ← IO.FS.readFile "tests/golden/VecIndexMut.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_seg_reverse: {msg}")
  | .ok [("_Z15vec_seg_reverseRSt6vectorIiSaIiEEmm", gotSeg),
         ("_ZNSt6vectorIiSaIiEE2atEm", gotAtMut),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNSt6vectorIiSaIiEEixEm", gotIndexMut),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize)] =>
    if gotSeg != wantSeg then
      throw (IO.userError "golden mismatch for vec_seg_reverse entry")
    if gotAtMut != wantAtMut then
      throw (IO.userError "golden mismatch for non-const at() composer")
    if gotRange != wantRange then
      throw (IO.userError "golden mismatch for _M_range_check leaf")
    if gotIndexMut != wantIndexMut then
      throw (IO.userError "golden mismatch for non-const operator[] leaf")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    IO.println "PASS pipeline vec_seg_reverse (entry + at-mut + range_check + index-mut + size, no oracle facts)"
    pure 5
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Shape probe: `name` in `file` must (or must not) match `shape`. -/
def checkShape (file entry : String) (shape : RawFunc → Bool)
    (want : Bool) (tag : String) : IO Nat := do
  let text ← IO.FS.readFile file
  match parseModule text with
  | none =>
    throw (IO.userError s!"reject-vecsegrev: {file} failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == entry) with
    | none => throw (IO.userError s!"reject-vecsegrev: {entry} not found")
    | some raw =>
      if shape raw != want then
        throw (IO.userError s!"reject-vecsegrev: {tag} shape verdict wrong")
      IO.println s!"PASS reject-vecsegrev {tag} [shape-exact]"
      pure 1

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectSeg (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-vecsegrev: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-vecsegrev: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-vecsegrev: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-vecsegrev {name} [{code}]"
    pure 1

/-- Self-recursive 3-param entry: the call-multiset pin (no
    self-call) rejects via the wrong-shape branch. -/
def advRecursiveSeg : String :=
  "module {\n  cir.func @vwrecseg(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !u64i {llvm.noundef}, %arg2: !u64i {llvm.noundef}) attributes {\"nothrow\"} {\n"
  ++ "    %s = cir.call @" ++ vecSizeEv ++ "(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> !u64i\n"
  ++ "    cir.call @vwrecseg(%arg0, %arg1, %arg2) : (!cir.ptr<" ++ vecRec ++ ">, !u64i, !u64i) -> ()\n"
  ++ "    cir.return\n  }\n}"

/-- Bare vector pointer (plus two `u64` params) without the attr
    triple: the alias discipline rejects before shapes are even
    consulted. -/
def advBareSegPtr : String :=
  "module {\n  cir.func @vwbareseg(%arg0: !cir.ptr<" ++ vecRec ++ "> {llvm.noundef}, %arg1: !u64i {llvm.noundef}, %arg2: !u64i {llvm.noundef}) attributes {\"nothrow\"} {\n"
  ++ "    cir.return\n  }\n}"

def segCir : String := "tests/cir/vec_seg_reverse.cir"

def reverseCir : String := "tests/cir/vec_reverse.cir"

def mergeIntoCir : String := "tests/cir/vec_merge_into.cir"

def sortCir : String := "tests/cir/vec_merge_sort.cir"

def segName : String :=
  "_Z15vec_seg_reverseRSt6vectorIiSaIiEEmm"

def atMutName : String :=
  "_ZNSt6vectorIiSaIiEE2atEm"

def reverseName : String :=
  "_Z11vec_reverseRSt6vectorIiSaIiEE"

def mergeIntoName : String :=
  "_Z14vec_merge_intoRKSt6vectorIiSaIiEES3_RS1_"

def sortName : String :=
  "_Z14vec_merge_sortRSt6vectorIiSaIiEES2_"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkSegPipeline
  passed := passed + c0
  let r1 ← checkShape segCir segName isVecSegReverseShape true "seg-accepts-vec_seg_reverse"
  passed := passed + r1
  let r2 ← checkShape segCir atMutName isVecSegReverseShape false "atmut-not-seg-shaped"
  passed := passed + r2
  let r3 ← checkShape segCir segName isVecReverseShape false "seg-not-reverse-shaped"
  passed := passed + r3
  let r4 ← checkShape reverseCir reverseName isVecSegReverseShape false "reverse-not-seg-shaped"
  passed := passed + r4
  let r5 ← checkShape mergeIntoCir mergeIntoName isVecSegReverseShape false "merge_into-not-seg-shaped"
  passed := passed + r5
  let r6 ← checkShape sortCir sortName isVecSegReverseShape false "sort-not-seg-shaped"
  passed := passed + r6
  let r7 ← checkRejectSeg "vwrecseg" advRecursiveSeg .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r7
  let r8 ← checkRejectSeg "vwbareseg" advBareSegPtr .unknown
    "alias-reject" "single-reference triple"
  passed := passed + r8
  IO.println s!"GOLDENVECSEGREVERSE-OK passed={passed}"

end GoldenVecSegReverse
