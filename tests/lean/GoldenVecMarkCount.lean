-- Golden test for the visited-mark idiom over two live vectors:
-- `mark_count` pipeline + rejection suite.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenVecMarkCount.main`).
-- 1. Corpus pipeline: `tests/cir/mark_count.cir` (real CIRGen
--    output: the `const&` mask + `&` visited + `u64` vertex entry with
--    the `vis.at(u) = 1` seed through the mutable `at()` checked
--    write, then the size-bounded `for` counting the gated `vis`
--    words (`nsw` adds, `at()` checked reads) + the mutable `at()`
--    composer + the `size` leaf + the const `at()` composer + the
--    fused `_M_range_check` guard + both `operator[]` leaves)
--    validates via `runModulePipeline` with NO oracle facts
--    (uniqueness comes from the `nonnull + dereferenceable +
--    noundef` attr triple, the M2a single-reference precedent)
--    and emits byte-identical text to
--    `tests/golden/VecMarkCount.lean` (new: entry) and the shared
--    `tests/golden/{VecAtMut,VecSize,VecAt,VecRangeCheck,VecIndexMut,
--    VecIndex}.lean` leaves (file order: entry, at-mut, size,
--    at-const, range_check, index-mut, index-const).
-- 2. Rejection suite: `operator[]`-direct loop (bypasses `at()`),
--    `vec_at_sum` text is not mark-count-shaped (single-vector sum,
--    not the two-vector gated fold), `mark_count` text is not
--    at-sum-shaped (shape-exactness both directions), self-recursive
--    entry, bare vector pointer without the attr triple (alias
--    discipline) — the first and fourth hit the dedicated vector
--    wrong-shape rejection, the second and third the shape predicate
--    directly, the last `alias-reject`.
import Circe.Validator

namespace GoldenVecMarkCount

def vecTriple : String :=
  "{llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}"

def vecRec : String :=
  "!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E"

def vecSizeEv : String :=
  "_ZNKSt6vectorIiSaIiEE4sizeEv"

def vecIndexEv : String :=
  "_ZNSt6vectorIiSaIiEEixEm"

def checkVecMarkCountPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/mark_count.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/VecMarkCount.lean"
  let wantAtMut ← IO.FS.readFile "tests/golden/VecAtMut.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  let wantAt ← IO.FS.readFile "tests/golden/VecAt.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndexMut ← IO.FS.readFile "tests/golden/VecIndexMut.lean"
  let wantIndex ← IO.FS.readFile "tests/golden/VecIndex.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected mark_count: {msg}")
  | .ok [("_Z10mark_countRKSt6vectorIiSaIiEERS1_m", gotEntry),
         ("_ZNSt6vectorIiSaIiEE2atEm", gotAtMut),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize),
         ("_ZNKSt6vectorIiSaIiEE2atEm", gotAt),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNSt6vectorIiSaIiEEixEm", gotIndexMut),
         ("_ZNKSt6vectorIiSaIiEEixEm", gotIndex)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for mark_count entry")
    if gotAtMut != wantAtMut then
      throw (IO.userError "golden mismatch for non-const at() composer")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    if gotAt != wantAt then
      throw (IO.userError "golden mismatch for const at() composer")
    if gotRange != wantRange then
      throw (IO.userError "golden mismatch for _M_range_check leaf")
    if gotIndexMut != wantIndexMut then
      throw (IO.userError "golden mismatch for non-const operator[] leaf")
    if gotIndex != wantIndex then
      throw (IO.userError "golden mismatch for const operator[] leaf")
    IO.println "PASS pipeline mark_count (entry + at-mut + size + at + range_check + index-mut + index, no oracle facts)"
    pure 7
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectVecMarkCount (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-vecmarkcount: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-vecmarkcount: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-vecmarkcount: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-vecmarkcount {name} [{code}]"
    pure 1

/-- `operator[]`-direct loop: reads through the mutable leaf and
    accumulates with an `nsw` add, bypassing `at()` — the
    encapsulation pin rejects. -/
def advDirectIndex : String :=
  "module {\n  cir.func @vmdirect(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg2: !u64i) -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %s = cir.call @" ++ vecSizeEv ++ "(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> !u64i\n"
  ++ "    %z = cir.const #cir.int<0> : !u64i\n"
  ++ "    %p = cir.call @" ++ vecIndexEv ++ "(%arg0, %z) : (!cir.ptr<" ++ vecRec ++ ">, !u64i) -> !cir.ptr<!s32i>\n"
  ++ "    %v = cir.load %p : !cir.ptr<!s32i>, !s32i\n"
  ++ "    %w = cir.add nsw %v, %v : !s32i\n"
  ++ "    cir.return %w : !s32i\n  }\n}"

/-- `vec_at_sum` text is not mark-count-shaped (single-vector
    checked-add fold, not the two-vector gated fold with a seed). -/
def checkAtSumNotMarkCount : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_at_sum.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-vecmarkcount: vec_at_sum corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z10vec_at_sumRKSt6vectorIiSaIiEE") with
    | none => throw (IO.userError "reject-vecmarkcount: vec_at_sum not found")
    | some raw =>
      if isMarkCountShape raw then
        throw (IO.userError "reject-vecmarkcount: vec_at_sum text wrongly mark-count-shaped")
      IO.println "PASS reject-vecmarkcount vec_at_sum-not-markcount [shape-exact]"
      pure 1

/-- `mark_count` text is not at-sum-shaped either (seed + gated
    two-vector fold, not the single-vector sum). -/
def checkMarkCountNotAtSum : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/mark_count.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-vecmarkcount: mark_count corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z10mark_countRKSt6vectorIiSaIiEERS1_m") with
    | none => throw (IO.userError "reject-vecmarkcount: mark_count not found")
    | some raw =>
      if isVecAtSumShape raw then
        throw (IO.userError "reject-vecmarkcount: mark_count text wrongly at-sum-shaped")
      IO.println "PASS reject-vecmarkcount mark_count-not-atsum [shape-exact]"
      pure 1

/-- Self-recursive entry: the call-multiset pin (no self-call)
    rejects via the wrong-shape branch. -/
def advRecursive : String :=
  "module {\n  cir.func @vmrec(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg2: !u64i) -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    cir.call @vmrec(%arg0, %arg1, %arg2) : (!cir.ptr<" ++ vecRec ++ ">, !cir.ptr<" ++ vecRec ++ ">, !u64i) -> !s32i\n"
  ++ "    %z = cir.const #cir.int<0> : !s32i\n"
  ++ "    cir.return %z : !s32i\n  }\n}"

/-- Bare vector pointer without the attr triple: the alias
    discipline rejects before shapes are even consulted. -/
def advBareVecPtr : String :=
  "module {\n  cir.func @vmbare(%arg0: !cir.ptr<" ++ vecRec ++ "> {llvm.noundef}, %arg1: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg2: !u64i) -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %z = cir.const #cir.int<0> : !s32i\n"
  ++ "    cir.return %z : !s32i\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkVecMarkCountPipeline
  passed := passed + c0
  let r1 ← checkRejectVecMarkCount "vmdirect" advDirectIndex .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r1
  let r2 ← checkAtSumNotMarkCount
  passed := passed + r2
  let r3 ← checkMarkCountNotAtSum
  passed := passed + r3
  let r4 ← checkRejectVecMarkCount "vmrec" advRecursive .unknown
    "out-of-subset" "calls itself"
  passed := passed + r4
  let r5 ← checkRejectVecMarkCount "vmbare" advBareVecPtr .unknown
    "alias-reject" "single-reference triple"
  passed := passed + r5
  IO.println s!"GOLDENVECMARKCOUNT-OK passed={passed}"

end GoldenVecMarkCount
