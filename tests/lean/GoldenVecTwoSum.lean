-- Golden test for brute-force two-sum over `const std::vector<int>&`:
-- `vec_two_sum` pipeline + rejection suite.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenVecTwoSum.main`).
-- 1. Corpus pipeline: `tests/cir/vec_two_sum.cir` (real CIRGen
--    output: the `const&` + `int` two-sum entry with nested `cir.while`
--    loops, two `at()` reads, the checked `nsw` add, `IPair` hit/miss
--    returns; plus the `size` leaf + the fused `at()` composer + the
--    fused `_M_range_check` guard + the call-free `operator[]` leaf)
--    validates via `runModulePipeline` with NO oracle facts
--    (uniqueness comes from the `nonnull + dereferenceable + noundef`
--    attr triple, the M2a single-reference precedent) and emits
--    byte-identical text to `tests/golden/VecTwoSum.lean` (entry) and
--    the shared `tests/golden/{VecSize,VecAt,VecRangeCheck,
--    VecIndex}.lean` leaves (file order: entry, size, at,
--    range_check, index).
-- 2. Rejection suite: `operator[]`-direct pair entry (bypasses
--    `at()`), `vec_at_sum` text is not two-sum-shaped (for-loop, not
--    nested while), `vec_binary_search` text is not two-sum-shaped
--    (single while, `u64` return), self-recursive entry, bare vector
--    pointer without the attr triple (alias discipline) — the first
--    and fourth hit the dedicated vector wrong-shape rejection, the
--    second and third the shape predicate directly, the last
--    `alias-reject`.
import Circe.Validator

namespace GoldenVecTwoSum

def vecTriple : String :=
  "{llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}"

def vecRec : String :=
  "!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E"

def iPairRec : String :=
  "!rec_IPair"

def checkVecTwoSumPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_two_sum.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/VecTwoSum.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  let wantAt ← IO.FS.readFile "tests/golden/VecAt.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndex ← IO.FS.readFile "tests/golden/VecIndex.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_two_sum: {msg}")
  | .ok [("_Z11vec_two_sumRKSt6vectorIiSaIiEEi", gotEntry),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize),
         ("_ZNKSt6vectorIiSaIiEE2atEm", gotAt),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNKSt6vectorIiSaIiEEixEm", gotIndex)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for vec_two_sum entry")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    if gotAt != wantAt then
      throw (IO.userError "golden mismatch for at() composer")
    if gotRange != wantRange then
      throw (IO.userError "golden mismatch for _M_range_check leaf")
    if gotIndex != wantIndex then
      throw (IO.userError "golden mismatch for operator[] leaf")
    IO.println "PASS pipeline vec_two_sum (entry + size + at + range_check + index, no oracle facts)"
    pure 5
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectVecTwoSum (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-vectwosum: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-vectwosum: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-vectwosum: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-vectwosum {name} [{code}]"
    pure 1

def vecSizeEv : String :=
  "_ZNKSt6vectorIiSaIiEE4sizeEv"

def vecIndexEv : String :=
  "_ZNKSt6vectorIiSaIiEEixEm"

/-- `operator[]`-direct pair entry: reads through the fused leaf,
    bypassing `at()` — the encapsulation pin rejects (same path as
    the V1 direct-index adversarial, pair return included). -/
def advDirectIndex : String :=
  "module {\n  cir.func @v2direct(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !s32i) -> " ++ iPairRec ++ " attributes {\"nothrow\"} {\n"
  ++ "    %r = cir.alloca \"__retval\" align(4) : !cir.ptr<" ++ iPairRec ++ ">\n"
  ++ "    %s = cir.call @" ++ vecSizeEv ++ "(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> !u64i\n"
  ++ "    %z = cir.const #cir.int<0> : !u64i\n"
  ++ "    %p = cir.call @" ++ vecIndexEv ++ "(%arg0, %z) : (!cir.ptr<" ++ vecRec ++ ">, !u64i) -> !cir.ptr<!s32i>\n"
  ++ "    %v = cir.load %p : !cir.ptr<!s32i>, !s32i\n"
  ++ "    %a = cir.get_member %r[0] {name = \"a\"} : !cir.ptr<" ++ iPairRec ++ "> -> !cir.ptr<!s32i>\n"
  ++ "    cir.store %v, %a : !s32i, !cir.ptr<!s32i>\n"
  ++ "    %b = cir.get_member %r[1] {name = \"b\"} : !cir.ptr<" ++ iPairRec ++ "> -> !cir.ptr<!s32i>\n"
  ++ "    cir.store %v, %b : !s32i, !cir.ptr<!s32i>\n"
  ++ "    %rv = cir.load %r : !cir.ptr<" ++ iPairRec ++ ">, " ++ iPairRec ++ "\n"
  ++ "    cir.return %rv : " ++ iPairRec ++ "\n  }\n}"

/-- Self-recursive pair entry: the call-multiset pin (no self-call)
    rejects via the wrong-shape branch. -/
def advRecursive : String :=
  "module {\n  cir.func @v2rec(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !s32i) -> " ++ iPairRec ++ " attributes {\"nothrow\"} {\n"
  ++ "    %s = cir.call @" ++ vecSizeEv ++ "(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> !u64i\n"
  ++ "    %r = cir.call @v2rec(%arg0, %arg1) : (!cir.ptr<" ++ vecRec ++ ">, !s32i) -> " ++ iPairRec ++ "\n"
  ++ "    cir.return %r : " ++ iPairRec ++ "\n  }\n}"

/-- `vec_at_sum` text is not two-sum-shaped (`cir.for`, not nested
    `cir.while`; one `size` call, not two `at()` reads): the admission
    is shape-exact, not loop-only. -/
def checkAtSumNotTwoSum : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_at_sum.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-vectwosum: vec_at_sum corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z10vec_at_sumRKSt6vectorIiSaIiEE") with
    | none => throw (IO.userError "reject-vectwosum: vec_at_sum not found")
    | some raw =>
      if isVecTwoSumShape raw then
        throw (IO.userError "reject-vectwosum: vec_at_sum text wrongly two-sum-shaped")
      IO.println "PASS reject-vectwosum vec_at_sum-not-twosum [shape-exact]"
      pure 1

/-- `vec_binary_search` text is not two-sum-shaped either (single
    `cir.while`, `u64` return, one `at()` call). -/
def checkBinSearchNotTwoSum : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_binary_search.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-vectwosum: vec_binary_search corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z17vec_binary_searchRKSt6vectorIiSaIiEEi") with
    | none => throw (IO.userError "reject-vectwosum: vec_binary_search not found")
    | some raw =>
      if isVecTwoSumShape raw then
        throw (IO.userError "reject-vectwosum: vec_binary_search text wrongly two-sum-shaped")
      IO.println "PASS reject-vectwosum vec_binary_search-not-twosum [shape-exact]"
      pure 1

/-- Bare vector pointer without the attr triple: the alias
    discipline rejects before shapes are even consulted. -/
def advBareVecPtr : String :=
  "module {\n  cir.func @v2bare(%arg0: !cir.ptr<" ++ vecRec ++ "> {llvm.noundef}, %arg1: !s32i) -> " ++ iPairRec ++ " attributes {\"nothrow\"} {\n"
  ++ "    %r = cir.alloca \"__retval\" align(4) : !cir.ptr<" ++ iPairRec ++ ">\n"
  ++ "    %z = cir.const #cir.int<0> : !s32i\n"
  ++ "    %a = cir.get_member %r[0] {name = \"a\"} : !cir.ptr<" ++ iPairRec ++ "> -> !cir.ptr<!s32i>\n"
  ++ "    cir.store %z, %a : !s32i, !cir.ptr<!s32i>\n"
  ++ "    %b = cir.get_member %r[1] {name = \"b\"} : !cir.ptr<" ++ iPairRec ++ "> -> !cir.ptr<!s32i>\n"
  ++ "    cir.store %z, %b : !s32i, !cir.ptr<!s32i>\n"
  ++ "    %rv = cir.load %r : !cir.ptr<" ++ iPairRec ++ ">, " ++ iPairRec ++ "\n"
  ++ "    cir.return %rv : " ++ iPairRec ++ "\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkVecTwoSumPipeline
  passed := passed + c0
  let r1 ← checkRejectVecTwoSum "v2direct" advDirectIndex .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r1
  let r2 ← checkAtSumNotTwoSum
  passed := passed + r2
  let r3 ← checkBinSearchNotTwoSum
  passed := passed + r3
  let r4 ← checkRejectVecTwoSum "v2rec" advRecursive .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r4
  let r5 ← checkRejectVecTwoSum "v2bare" advBareVecPtr .unknown
    "alias-reject" "single-reference triple"
  passed := passed + r5
  IO.println s!"GOLDENVECTWOSUM-OK passed={passed}"

end GoldenVecTwoSum
