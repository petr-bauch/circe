-- Golden test for the checked `at()` store over `std::vector<int>&`:
-- `vec_at_set` pipeline + rejection suite.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenVecAtSet.main`).
-- 1. Corpus pipeline: `tests/cir/vec_at_set.cir` (real CIRGen
--    output: the mutable-borrow + `u64` + `i32` store entry with one
--    non-const `at()` call and the store through its result; plus the
--    non-const `at()` composer + the fused `_M_range_check` guard +
--    the non-const `operator[]` leaf + the `size` leaf) validates via
--    `runModulePipeline` with NO oracle facts (uniqueness comes from
--    the `nonnull + dereferenceable + noundef` attr triple, the M2a
--    single-reference precedent) and emits byte-identical text to
--    `tests/golden/{VecAtSet,VecAtMut,VecIndexMut}.lean` (new: entry,
--    mutable composer, mutable index leaf) and the shared
--    `tests/golden/{VecRangeCheck,VecSize}.lean` leaves (file order:
--    entry, at-mut, range_check, index-mut, size).
-- 2. Rejection suite: `operator[]`-direct store (bypasses `at()`),
--    `vec_at_one` text is not at-set-shaped (read, not store),
--    `vec_binary_search` text is not at-set-shaped (search, not
--    store), self-recursive entry, bare vector pointer without the
--    attr triple (alias discipline) — the first and fourth hit the
--    dedicated vector wrong-shape rejection, the second and third
--    the shape predicate directly, the last `alias-reject`.
import Circe.Validator

namespace GoldenVecAtSet

def vecTriple : String :=
  "{llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}"

def vecRec : String :=
  "!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E"

def checkVecAtSetPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_at_set.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/VecAtSet.lean"
  let wantAtMut ← IO.FS.readFile "tests/golden/VecAtMut.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndexMut ← IO.FS.readFile "tests/golden/VecIndexMut.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_at_set: {msg}")
  | .ok [("_Z10vec_at_setRSt6vectorIiSaIiEEmi", gotEntry),
         ("_ZNSt6vectorIiSaIiEE2atEm", gotAtMut),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNSt6vectorIiSaIiEEixEm", gotIndexMut),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for vec_at_set entry")
    if gotAtMut != wantAtMut then
      throw (IO.userError "golden mismatch for non-const at() composer")
    if gotRange != wantRange then
      throw (IO.userError "golden mismatch for _M_range_check leaf")
    if gotIndexMut != wantIndexMut then
      throw (IO.userError "golden mismatch for non-const operator[] leaf")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    IO.println "PASS pipeline vec_at_set (entry + at-mut + range_check + index-mut + size, no oracle facts)"
    pure 5
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectVecAtSet (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-vecatset: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-vecatset: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-vecatset: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-vecatset {name} [{code}]"
    pure 1

def vecSizeEv : String :=
  "_ZNKSt6vectorIiSaIiEE4sizeEv"

def vecIndexMutEv : String :=
  "_ZNSt6vectorIiSaIiEEixEm"

/-- `operator[]`-direct store: writes through the mutable leaf,
    bypassing `at()` — the encapsulation pin rejects. -/
def advDirectIndex : String :=
  "module {\n  cir.func @vwsdirect(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !u64i, %arg2: !s32i) attributes {\"nothrow\"} {\n"
  ++ "    %p = cir.call @" ++ vecIndexMutEv ++ "(%arg0, %arg1) : (!cir.ptr<" ++ vecRec ++ ">, !u64i) -> !cir.ptr<!s32i>\n"
  ++ "    cir.store %arg2, %p : !s32i, !cir.ptr<!s32i>\n"
  ++ "    cir.return\n  }\n}"

/-- Self-recursive store entry: the call-multiset pin (no self-call)
    rejects via the wrong-shape branch. -/
def advRecursive : String :=
  "module {\n  cir.func @vwsrec(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !u64i, %arg2: !s32i) attributes {\"nothrow\"} {\n"
  ++ "    %s = cir.call @" ++ vecSizeEv ++ "(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> !u64i\n"
  ++ "    cir.call @vwsrec(%arg0, %arg1, %arg2) : (!cir.ptr<" ++ vecRec ++ ">, !u64i, !s32i) -> ()\n"
  ++ "    cir.return\n  }\n}"

/-- `vec_at_one` text is not at-set-shaped (checked read, not store;
    different arity and leaf). -/
def checkAtOneNotAtSet : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_at_one.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-vecatset: vec_at_one corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z10vec_at_oneRKSt6vectorIiSaIiEE") with
    | none => throw (IO.userError "reject-vecatset: vec_at_one not found")
    | some raw =>
      if isVecAtSetShape raw then
        throw (IO.userError "reject-vecatset: vec_at_one text wrongly at-set-shaped")
      IO.println "PASS reject-vecatset vec_at_one-not-atset [shape-exact]"
      pure 1

/-- `vec_binary_search` text is not at-set-shaped either (search with
    loops, not a straight-line store). -/
def checkBinSearchNotAtSet : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_binary_search.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-vecatset: vec_binary_search corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z17vec_binary_searchRKSt6vectorIiSaIiEEi") with
    | none => throw (IO.userError "reject-vecatset: vec_binary_search not found")
    | some raw =>
      if isVecAtSetShape raw then
        throw (IO.userError "reject-vecatset: vec_binary_search text wrongly at-set-shaped")
      IO.println "PASS reject-vecatset vec_binary_search-not-atset [shape-exact]"
      pure 1

/-- Bare vector pointer without the attr triple: the alias
    discipline rejects before shapes are even consulted. -/
def advBareVecPtr : String :=
  "module {\n  cir.func @vwsbare(%arg0: !cir.ptr<" ++ vecRec ++ "> {llvm.noundef}, %arg1: !u64i, %arg2: !s32i) attributes {\"nothrow\"} {\n"
  ++ "    cir.return\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkVecAtSetPipeline
  passed := passed + c0
  let r1 ← checkRejectVecAtSet "vwsdirect" advDirectIndex .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r1
  let r2 ← checkAtOneNotAtSet
  passed := passed + r2
  let r3 ← checkBinSearchNotAtSet
  passed := passed + r3
  let r4 ← checkRejectVecAtSet "vwsrec" advRecursive .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r4
  let r5 ← checkRejectVecAtSet "vwsbare" advBareVecPtr .unknown
    "alias-reject" "single-reference triple"
  passed := passed + r5
  IO.println s!"GOLDENVECATSET-OK passed={passed}"

end GoldenVecAtSet
