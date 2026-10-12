-- Golden test for `std::vector::at` checked read: `vec_at_one`
-- pipeline + rejection suite.
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenVecAt.lean`
-- 1. Corpus pipeline: `tests/cir/vec_at_one.cir` (real CIRGen
--    output: the `const&` `vec_at_one` entry + the fused `at()`
--    composer + the fused `_M_range_check` guard leaf + the
--    call-free `operator[]` leaf + the `size` projection leaf)
--    validates via `runModulePipeline` with NO oracle facts
--    (uniqueness comes from the `nonnull + dereferenceable +
--    noundef` attr triple, the M2a single-reference precedent)
--    and emits byte-identical text to
--    `tests/golden/{VecAtOne,VecAt,VecRangeCheck,VecIndex,VecSize}.lean`
--    (file order: entry, at, range_check, index, size).
-- 2. Rejection suite: guard-stripped `at()` (calls guard + read,
--    no `cmp`/`if`), throw-less range check (`ge` + `if` but no
--    throw), `lt`-flavor guard (exemption-exactness: the fused
--    throw arm pins `ge`), `at()` calling the throw directly
--    (bypassing `_M_range_check`), unchecked entry (entry calling
--    `operator[]`, not `at()`), bare vector pointer without the
--    attr triple (alias discipline) — the first, second, fourth,
--    and sixth hit the dedicated vector wrong-shape rejection,
--    the third the `forbiddenOp` global-access message, the last
--    `alias-reject`.
import Circe.Validator

namespace GoldenVecAt

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

def vecThrowEv : String :=
  "_ZSt24__throw_out_of_range_fmtPKcz"

def checkVecAtPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_at_one.cir"
  let wantOne ← IO.FS.readFile "tests/golden/VecAtOne.lean"
  let wantAt ← IO.FS.readFile "tests/golden/VecAt.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndex ← IO.FS.readFile "tests/golden/VecIndex.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected vec_at_one: {msg}")
  | .ok [("_Z10vec_at_oneRKSt6vectorIiSaIiEE", gotOne),
         ("_ZNKSt6vectorIiSaIiEE2atEm", gotAt),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNKSt6vectorIiSaIiEEixEm", gotIndex),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize)] =>
    if gotOne != wantOne then
      throw (IO.userError "golden mismatch for vec_at_one entry")
    if gotAt != wantAt then
      throw (IO.userError "golden mismatch for at() composer")
    if gotRange != wantRange then
      throw (IO.userError "golden mismatch for _M_range_check leaf")
    if gotIndex != wantIndex then
      throw (IO.userError "golden mismatch for operator[] leaf")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    IO.println "PASS pipeline vec_at_one (entry + at + range_check + index + size, no oracle facts)"
    pure 5
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectVecAt (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-vecat: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-vecat: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-vecat: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-vecat {name} [{code}]"
    pure 1

/-- Guard-stripped `at()`: calls the guard and the read but returns
    the element with no `cmp`/`if` — the fused-guard pin rejects. -/
def advAtNoGuard : String :=
  "module {\n  cir.func @vatnoguard(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !u64i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    cir.call @" ++ vecRangeEv ++ "(%arg0, %arg1) : (!cir.ptr<" ++ vecRec ++ ">, !u64i) -> ()\n"
  ++ "    %p = cir.call @" ++ vecIndexEv ++ "(%arg0, %arg1) : (!cir.ptr<" ++ vecRec ++ ">, !u64i) -> !cir.ptr<!s32i>\n"
  ++ "    %v = cir.load %p : !cir.ptr<!s32i>, !s32i\n    cir.return %v : !s32i\n  }\n}"

/-- Throw-less range check: `ge` + `if` + two `size` calls but no
    throw — the `2 × size + 1 × throw` pin rejects. -/
def advRangeNoThrow : String :=
  "module {\n  cir.func @vrangenothrow(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !u64i {llvm.noundef}) attributes {\"nothrow\"} {\n"
  ++ "    %s = cir.call @" ++ vecSizeEv ++ "(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> !u64i\n"
  ++ "    %c = cir.cmp ge %arg1, %s : !u64i\n"
  ++ "    cir.if %c {\n      %z = cir.const #cir.int<0> : !s32i\n    }\n    cir.return\n  }\n}"

/-- `lt`-flavor guard with the full throw materialization: the
    exemption pins `ge`, so the general global-access message fires. -/
def advRangeLtCmp : String :=
  "module {\n  cir.func @vrangelt(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !u64i {llvm.noundef}) attributes {\"nothrow\"} {\n"
  ++ "    %s = cir.call @" ++ vecSizeEv ++ "(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> !u64i\n"
  ++ "    %c = cir.cmp lt %arg1, %s : !u64i\n"
  ++ "    cir.if %c {\n"
  ++ "      %g = cir.get_global @\".str\" : !cir.ptr<!cir.array<!s8i x 74>>\n"
  ++ "      %m = cir.cast array_to_ptrdecay %g : !cir.ptr<!cir.array<!s8i x 74>> -> !cir.ptr<!s8i>\n"
  ++ "      cir.call @" ++ vecThrowEv ++ "(%m, %arg1, %s) {noreturn} : (!cir.ptr<!s8i>, !u64i, !u64i) -> ()\n"
  ++ "    }\n    cir.return\n  }\n}"

/-- `at()` calling the throw directly, bypassing `_M_range_check`:
    the composer pin (exactly guard + read) rejects. -/
def advAtDirectThrow : String :=
  "module {\n  cir.func @vatdirect(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !u64i {llvm.noundef}) -> !cir.ptr<!s32i> attributes {\"nothrow\"} {\n"
  ++ "    %m = cir.const #cir.ptr<null> : !cir.ptr<!s8i>\n"
  ++ "    %p = cir.call @" ++ vecIndexEv ++ "(%arg0, %arg1) : (!cir.ptr<" ++ vecRec ++ ">, !u64i) -> !cir.ptr<!s32i>\n"
  ++ "    cir.call @" ++ vecThrowEv ++ "(%m, %arg1, %arg1) {noreturn} : (!cir.ptr<!s8i>, !u64i, !u64i) -> ()\n"
  ++ "    cir.return %p : !cir.ptr<!s32i>\n  }\n}"

/-- Unchecked entry: calls `operator[]` directly instead of `at()` —
    the entry pin (exactly one `at()` call) rejects. -/
def advEntryUnchecked : String :=
  "module {\n  cir.func @ventryunchecked(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ") -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %z = cir.const #cir.int<0> : !u64i\n"
  ++ "    %p = cir.call @" ++ vecIndexEv ++ "(%arg0, %z) : (!cir.ptr<" ++ vecRec ++ ">, !u64i) -> !cir.ptr<!s32i>\n"
  ++ "    %v = cir.load %p : !cir.ptr<!s32i>, !s32i\n    cir.return %v : !s32i\n  }\n}"

/-- Bare vector pointer without the attr triple: the alias
    discipline rejects before shapes are even consulted. -/
def advBareVecPtr : String :=
  "module {\n  cir.func @vbare(%arg0: !cir.ptr<" ++ vecRec ++ "> {llvm.noundef}, %arg1: !u64i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %p = cir.call @" ++ vecAtEv ++ "(%arg0, %arg1) : (!cir.ptr<" ++ vecRec ++ ">, !u64i) -> !cir.ptr<!s32i>\n"
  ++ "    %v = cir.load %p : !cir.ptr<!s32i>, !s32i\n    cir.return %v : !s32i\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkVecAtPipeline
  passed := passed + c0
  let r1 ← checkRejectVecAt "vatnoguard" advAtNoGuard .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r1
  let r2 ← checkRejectVecAt "vrangenothrow" advRangeNoThrow .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r2
  let r3 ← checkRejectVecAt "vrangelt" advRangeLtCmp .unknown
    "out-of-subset" "global access"
  passed := passed + r3
  let r4 ← checkRejectVecAt "vatdirect" advAtDirectThrow .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r4
  let r5 ← checkRejectVecAt "ventryunchecked" advEntryUnchecked .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r5
  let r6 ← checkRejectVecAt "vbare" advBareVecPtr .unknown
    "alias-reject" "single-reference triple"
  passed := passed + r6
  IO.println s!"GOLDENVECAT-OK passed={passed}"

end GoldenVecAt
