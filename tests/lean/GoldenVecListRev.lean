-- Golden test for index-linked in-place reversal over two
-- `std::vector<int>&`: `list_rev` pipeline + rejection suite.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenVecListRev.main`).
-- 1. Corpus pipeline: `tests/cir/list_rev.cir` (real CIRGen
--    output: the mut `data` + mut `nxt` vectors + `u64` head/n entry
--    with the `prev = n`, `cur = head`, `nxt_cur = 0` seed, the
--    `while cur != n` chase whose body reads `nxt[cur]` (widened
--    into `nxt_cur`), rewires `nxt[cur]` to the predecessor
--    (narrowed `(int)prev`), and advances, plus the two mutable
--    `at()` composers + the fused `_M_range_check` guard + the
--    `operator[]` leaf + the `size` leaf) validates via
--    `runModulePipeline` with NO oracle facts (uniqueness comes from
--    the `nonnull + dereferenceable + noundef` attr triple, the M2a
--    single-reference precedent) and emits byte-identical text to
--    `tests/golden/VecListRev.lean` (entry) and the shared
--    `tests/golden/{VecAtMut,VecRangeCheck,VecIndexMut,VecSize}.lean`
--    leaves (file order: entry, at-mut, range_check, index-mut,
--    size).
-- 2. Rejection suite: `operator[]`-direct pair entry (bypasses
--    `at()`), `mark_count` text is not listrev-shaped (gated fold,
--    not the seeded link chase with predecessor rewire),
--    `list_rev` text is not mark-count-shaped (shape-exactness both
--    directions), self-recursive entry, bare vector pointer without
--    the attr triple (alias discipline) — the first and fourth hit
--    the dedicated vector wrong-shape rejection, the second and
--    third the shape predicate directly, the last `alias-reject`.
import Circe.Validator

namespace GoldenVecListRev

def vecTriple : String :=
  "{llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}"

def vecRec : String :=
  "!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E"

def vecSizeEv : String :=
  "_ZNKSt6vectorIiSaIiEE4sizeEv"

def vecIndexEv : String :=
  "_ZNSt6vectorIiSaIiEEixEm"

def checkVecListRevPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_rev.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/VecListRev.lean"
  let wantAtMut ← IO.FS.readFile "tests/golden/VecAtMut.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndexMut ← IO.FS.readFile "tests/golden/VecIndexMut.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected list_rev: {msg}")
  | .ok [("_Z8list_revRSt6vectorIiSaIiEES2_mm", gotEntry),
         ("_ZNSt6vectorIiSaIiEE2atEm", gotAtMut),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNSt6vectorIiSaIiEEixEm", gotIndexMut),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for list_rev entry")
    if gotAtMut != wantAtMut then
      throw (IO.userError "golden mismatch for non-const at() composer")
    if gotRange != wantRange then
      throw (IO.userError "golden mismatch for _M_range_check leaf")
    if gotIndexMut != wantIndexMut then
      throw (IO.userError "golden mismatch for non-const operator[] leaf")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    IO.println "PASS pipeline list_rev (entry + at-mut + range_check + index-mut + size, no oracle facts)"
    pure 5
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectVecListRev (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-veclistrev: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-veclistrev: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-veclistrev: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-veclistrev {name} [{code}]"
    pure 1

/-- `operator[]`-direct entry: reads through the mutable leaf,
    bypassing `at()` — the encapsulation pin rejects. -/
def advDirectIndex : String :=
  "module {\n  cir.func @vbdirect(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg2: !u64i) -> !u64i attributes {\"nothrow\"} {\n"
  ++ "    %s = cir.call @" ++ vecSizeEv ++ "(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> !u64i\n"
  ++ "    %z = cir.const #cir.int<0> : !u64i\n"
  ++ "    %p = cir.call @" ++ vecIndexEv ++ "(%arg0, %z) : (!cir.ptr<" ++ vecRec ++ ">, !u64i) -> !cir.ptr<!s32i>\n"
  ++ "    %v = cir.load %p : !cir.ptr<!s32i>, !s32i\n"
  ++ "    %w = cir.cast integral %v : !s32i -> !u64i\n"
  ++ "    cir.return %w : !u64i\n  }\n}"

/-- `mark_count` text is not listrev-shaped (gated fold, not the
    seeded link chase with predecessor rewire). -/
def checkMarkCountNotListRev : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/mark_count.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-veclistrev: mark_count corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z10mark_countRKSt6vectorIiSaIiEERS1_m") with
    | none => throw (IO.userError "reject-veclistrev: mark_count not found")
    | some raw =>
      if isListRevShape raw then
        throw (IO.userError "reject-veclistrev: mark_count text wrongly listrev-shaped")
      IO.println "PASS reject-veclistrev mark_count-not-listrev [shape-exact]"
      pure 1

/-- `list_rev` text is not mark-count-shaped either (seeded chase,
    not the gated fold). -/
def checkListRevNotMarkCount : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_rev.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-veclistrev: list_rev corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z8list_revRSt6vectorIiSaIiEES2_mm") with
    | none => throw (IO.userError "reject-veclistrev: list_rev not found")
    | some raw =>
      if isMarkCountShape raw then
        throw (IO.userError "reject-veclistrev: list_rev text wrongly mark-count-shaped")
      IO.println "PASS reject-veclistrev listrev-not-markcount [shape-exact]"
      pure 1

/-- Self-recursive entry: the call-multiset pin (no self-call)
    rejects via the wrong-shape branch. -/
def advRecursive : String :=
  "module {\n  cir.func @vbrec(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !u64i) -> !u64i attributes {\"nothrow\"} {\n"
  ++ "    cir.call @vbrec(%arg0, %arg1) : (!cir.ptr<" ++ vecRec ++ ">, !u64i) -> !u64i\n"
  ++ "    %z = cir.const #cir.int<0> : !u64i\n"
  ++ "    cir.return %z : !u64i\n  }\n}"

/-- Bare vector pointer without the attr triple: the alias
    discipline rejects before shapes are even consulted. -/
def advBareVecPtr : String :=
  "module {\n  cir.func @vbbare(%arg0: !cir.ptr<" ++ vecRec ++ "> {llvm.noundef}, %arg1: !u64i) -> !u64i attributes {\"nothrow\"} {\n"
  ++ "    %z = cir.const #cir.int<0> : !u64i\n"
  ++ "    cir.return %z : !u64i\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkVecListRevPipeline
  passed := passed + c0
  let r1 ← checkRejectVecListRev "vbdirect" advDirectIndex .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r1
  let r2 ← checkMarkCountNotListRev
  passed := passed + r2
  let r3 ← checkListRevNotMarkCount
  passed := passed + r3
  let r4 ← checkRejectVecListRev "vbrec" advRecursive .unknown
    "out-of-subset" "calls itself"
  passed := passed + r4
  let r5 ← checkRejectVecListRev "vbbare" advBareVecPtr .unknown
    "alias-reject" "single-reference triple"
  passed := passed + r5
  IO.println s!"GOLDENVECLISTREV-OK passed={passed}"

end GoldenVecListRev
