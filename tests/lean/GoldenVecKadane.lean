-- Golden test for Kadane maximum subarray: `max_subarray`
-- pipeline + rejection suite.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenVecKadane.main`).
-- 1. Corpus pipeline: `tests/cir/max_subarray.cir` (real CIRGen
--    output: the `const&` `max_subarray` Kadane entry with the
--    `at(0)` seed pair + the `size` leaf + the fused `at()`
--    composer + the fused `_M_range_check` guard + the call-free
--    `operator[]` leaf) validates via `runModulePipeline` with NO
--    oracle facts (uniqueness comes from the `nonnull +
--    dereferenceable + noundef` attr triple, the M2a
--    single-reference precedent) and emits byte-identical text to
--    `tests/golden/{VecKadane,VecSize,VecAt,VecRangeCheck,VecIndex}.lean`
--    (file order: entry, at, size, range_check, index).
-- 2. Rejection suite: unchecked entry (calls `operator[]`
--    directly, bypassing `at()`), `vec_read_sum` text is not
--    Kadane-shaped (and `max_subarray` text is not at-sum-shaped:
--    admission is shape-exact both directions), direct-`range_check`
--    entry (guard + read without `at()`), bare vector pointer
--    without the attr triple (alias discipline) — the first and
--    third hit the dedicated vector wrong-shape rejection, the
--    shape pair the shape predicates directly, the last
--    `alias-reject`.
import Circe.Validator

namespace GoldenVecKadane

def vecTriple : String :=
  "{llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}"

def vecRec : String :=
  "!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E"

def vecSizeEv : String :=
  "_ZNKSt6vectorIiSaIiEE4sizeEv"

def vecIndexEv : String :=
  "_ZNKSt6vectorIiSaIiEEixEm"

def vecRangeEv : String :=
  "_ZNKSt6vectorIiSaIiEE14_M_range_checkEm"

def vecAtEv : String :=
  "_ZNKSt6vectorIiSaIiEE2atEm"

def checkVecKadanePipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/max_subarray.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/VecKadane.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  let wantAt ← IO.FS.readFile "tests/golden/VecAt.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndex ← IO.FS.readFile "tests/golden/VecIndex.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected max_subarray: {msg}")
  | .ok [("_Z12max_subarrayRKSt6vectorIiSaIiEE", gotEntry),
         ("_ZNKSt6vectorIiSaIiEE2atEm", gotAt),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNKSt6vectorIiSaIiEEixEm", gotIndex)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for max_subarray entry")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    if gotAt != wantAt then
      throw (IO.userError "golden mismatch for at() composer")
    if gotRange != wantRange then
      throw (IO.userError "golden mismatch for _M_range_check leaf")
    if gotIndex != wantIndex then
      throw (IO.userError "golden mismatch for operator[] leaf")
    IO.println "PASS pipeline max_subarray (entry + size + at + range_check + index, no oracle facts)"
    pure 5
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectVecKadane (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-veckadane: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-veckadane: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-veckadane: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-veckadane {name} [{code}]"
    pure 1

/-- Unchecked entry: calls `operator[]` directly in a `for` loop with
    an `nsw` add, bypassing `at()` — the encapsulation pin rejects. -/
def advEntryUnchecked : String :=
  "module {\n  cir.func @kentryunchecked(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ") -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %s = cir.call @" ++ vecSizeEv ++ "(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> !u64i\n"
  ++ "    %z = cir.const #cir.int<0> : !u64i\n"
  ++ "    %p = cir.call @" ++ vecIndexEv ++ "(%arg0, %z) : (!cir.ptr<" ++ vecRec ++ ">, !u64i) -> !cir.ptr<!s32i>\n"
  ++ "    %v = cir.load %p : !cir.ptr<!s32i>, !s32i\n"
  ++ "    %w = cir.add nsw %v, %v : !s32i\n"
  ++ "    cir.return %w : !s32i\n  }\n}"

/-- `vec_read_sum` text is not Kadane-shaped (no `at()` seed pair,
    no dual accumulators): the admission is shape-exact, not
    loop-only. -/
def checkReadSumNotKadane : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_read_sum.cir"
  match parseModule text with
  | none =>
    throw (IO.userError s!"reject-veckadane: vec_read_sum corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z12vec_read_sumRKSt6vectorIiSaIiEE") with
    | none => throw (IO.userError s!"reject-veckadane: vec_read_sum not found")
    | some raw =>
      if isMaxSubarrayShape raw then
        throw (IO.userError s!"reject-veckadane: vec_read_sum text wrongly Kadane-shaped")
      IO.println s!"PASS reject-veckadane vec_read_sum-not-kadane [shape-exact]"
      pure 1

/-- `max_subarray` text is not at-sum-shaped (seed pair + dual
    accumulators + two max-updates): shape-exactness the other
    direction. -/
def checkKadaneNotAtSum : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/max_subarray.cir"
  match parseModule text with
  | none =>
    throw (IO.userError s!"reject-veckadane: max_subarray corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z12max_subarrayRKSt6vectorIiSaIiEE") with
    | none => throw (IO.userError s!"reject-veckadane: max_subarray not found")
    | some raw =>
      if isVecAtSumShape raw then
        throw (IO.userError s!"reject-veckadane: max_subarray text wrongly at-sum-shaped")
      IO.println s!"PASS reject-veckadane max_subarray-not-at-sum [shape-exact]"
      pure 1

/-- Direct-`range_check` entry: guard + read without `at()` — the
    composer pin (exactly guard-encapsulating `at()`) rejects. -/
def advDirectRange : String :=
  "module {\n  cir.func @kdirectrange(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ") -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %z = cir.const #cir.int<0> : !u64i\n"
  ++ "    cir.call @" ++ vecRangeEv ++ "(%arg0, %z) : (!cir.ptr<" ++ vecRec ++ ">, !u64i) -> ()\n"
  ++ "    %p = cir.call @" ++ vecIndexEv ++ "(%arg0, %z) : (!cir.ptr<" ++ vecRec ++ ">, !u64i) -> !cir.ptr<!s32i>\n"
  ++ "    %v = cir.load %p : !cir.ptr<!s32i>, !s32i\n"
  ++ "    cir.return %v : !s32i\n  }\n}"

/-- Bare vector pointer without the attr triple: the alias
    discipline rejects before shapes are even consulted. -/
def advBareVecPtr : String :=
  "module {\n  cir.func @kbare(%arg0: !cir.ptr<" ++ vecRec ++ "> {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %z = cir.const #cir.int<0> : !u64i\n"
  ++ "    %p = cir.call @" ++ vecAtEv ++ "(%arg0, %z) : (!cir.ptr<" ++ vecRec ++ ">, !u64i) -> !cir.ptr<!s32i>\n"
  ++ "    %v = cir.load %p : !cir.ptr<!s32i>, !s32i\n"
  ++ "    cir.return %v : !s32i\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkVecKadanePipeline
  passed := passed + c0
  let r1 ← checkRejectVecKadane "kentryunchecked" advEntryUnchecked .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r1
  let r2 ← checkReadSumNotKadane
  passed := passed + r2
  let r3 ← checkKadaneNotAtSum
  passed := passed + r3
  let r4 ← checkRejectVecKadane "kdirectrange" advDirectRange .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r4
  let r5 ← checkRejectVecKadane "kbare" advBareVecPtr .unknown
    "alias-reject" "single-reference triple"
  passed := passed + r5
  IO.println s!"GOLDENVECKADANE-OK passed={passed}"

end GoldenVecKadane
