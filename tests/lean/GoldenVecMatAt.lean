-- Golden test for the flat-2D index read: `mat_at` pipeline +
-- rejection suite.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenVecMatAt.main`).
-- 1. Corpus pipeline: `tests/cir/mat_at.cir` (real CIRGen output:
--    the `const vector<int>&` matrix + three `u64` (`ncols`, `i`,
--    `j`) entry with the single const-`at()` call on the wrapped
--    `i * ncols + j` index (one wrapping `cir.mul` + one wrapping
--    `cir.add`, no `nsw`) + the const-`at()` composer + the fused
--    `_M_range_check` guard + the `operator[]` leaf + the `size`
--    leaf) validates via `runModulePipeline` with NO oracle facts
--    (uniqueness comes from the `nonnull + dereferenceable +
--    noundef` attr triple, the M2a single-reference precedent)
--    and emits byte-identical text to
--    `tests/golden/VecMatAt.lean` (new: entry) and the shared
--    `tests/golden/{VecAt,VecRangeCheck,VecIndex,VecSize}.lean`
--    leaves (file order: entry, at, range_check, index, size).
-- 2. Rejection suite: `at()`-direct read with a plain index
--    (bypasses the 2D computation), `vec_at_one` text is not
--    mat-shaped and `mat_at` text is not at-one-shaped
--    (shape-exactness both directions), bare vector pointer without
--    the attr triple (alias discipline) — the first hits the
--    dedicated vector wrong-shape rejection, the second and third
--    the shape predicates directly, the last `alias-reject`.
import Circe.Validator

namespace GoldenVecMatAt

def vecTriple : String :=
  "{llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}"

def vecRec : String :=
  "!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E"

def vecAtEv : String :=
  "_ZNKSt6vectorIiSaIiEE2atEm"

def checkVecMatAtPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/mat_at.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/VecMatAt.lean"
  let wantAt ← IO.FS.readFile "tests/golden/VecAt.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndex ← IO.FS.readFile "tests/golden/VecIndex.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected mat_at: {msg}")
  | .ok [("_Z6mat_atRKSt6vectorIiSaIiEEmmm", gotEntry),
         ("_ZNKSt6vectorIiSaIiEE2atEm", gotAt),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNKSt6vectorIiSaIiEEixEm", gotIndex),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for mat_at entry")
    if gotAt != wantAt then
      throw (IO.userError "golden mismatch for const at() composer")
    if gotRange != wantRange then
      throw (IO.userError "golden mismatch for _M_range_check leaf")
    if gotIndex != wantIndex then
      throw (IO.userError "golden mismatch for operator[] leaf")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    IO.println "PASS pipeline mat_at (entry + at + range_check + index + size, no oracle facts)"
    pure 5
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectVecMatAt (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-vecmatat: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-vecmatat: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-vecmatat: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-vecmatat {name} [{code}]"
    pure 1

/-- `at()`-direct read with a plain (non-2D) index: the single `at()`
    call without the wrapping index computation — the admission is
    the fused 2D index, not any read. -/
def advDirectIndex : String :=
  "module {\n  cir.func @vdirect(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !u64i, %arg2: !u64i, %arg3: !u64i) attributes {\"nothrow\"} {\n"
  ++ "    %p = cir.call @" ++ vecAtEv ++ "(%arg0, %arg2) : (!cir.ptr<" ++ vecRec ++ ">, !u64i) -> !cir.ptr<!s32i>\n"
  ++ "    %v = cir.load %p : !cir.ptr<!s32i>, !s32i\n"
  ++ "    cir.return %v : !s32i\n  }\n}"

/-- `vec_at_one` text is not mat-shaped (no index computation, fixed
    literal index). -/
def checkAtOneNotMatAt : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_at_one.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-vecmatat: vec_at_one corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z10vec_at_oneRKSt6vectorIiSaIiEE") with
    | none => throw (IO.userError "reject-vecmatat: vec_at_one not found")
    | some raw =>
      if isMatAtShape raw then
        throw (IO.userError "reject-vecmatat: vec_at_one text wrongly mat-shaped")
      IO.println "PASS reject-vecmatat vec_at_one-not-matat [shape-exact]"
      pure 1

/-- `mat_at` text is not at-one-shaped either (computed index, four
    params). -/
def checkMatAtNotAtOne : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/mat_at.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-vecmatat: mat_at corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z6mat_atRKSt6vectorIiSaIiEEmmm") with
    | none => throw (IO.userError "reject-vecmatat: mat_at not found")
    | some raw =>
      if isVecAtOneShape raw then
        throw (IO.userError "reject-vecmatat: mat_at text wrongly at-one-shaped")
      IO.println "PASS reject-vecmatat mat_at-not-atone [shape-exact]"
      pure 1

/-- Bare vector pointer without the attr triple: the alias
    discipline rejects before shapes are even consulted. -/
def advBareVecPtr : String :=
  "module {\n  cir.func @vmbare(%arg0: !cir.ptr<" ++ vecRec ++ "> {llvm.noundef}, %arg1: !u64i, %arg2: !u64i, %arg3: !u64i) attributes {\"nothrow\"} {\n"
  ++ "    %z = cir.const #cir.int<0> : !s32i\n"
  ++ "    cir.return %z : !s32i\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkVecMatAtPipeline
  passed := passed + c0
  let r1 ← checkRejectVecMatAt "vdirect" advDirectIndex .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r1
  let r2 ← checkAtOneNotMatAt
  passed := passed + r2
  let r3 ← checkMatAtNotAtOne
  passed := passed + r3
  let r4 ← checkRejectVecMatAt "vmbare" advBareVecPtr .unknown
    "alias-reject" "single-reference triple"
  passed := passed + r4
  IO.println s!"GOLDENVECMATAT-OK passed={passed}"

end GoldenVecMatAt
