-- Golden test for the char-width visited-mark idiom:
-- `mark_count_c` pipeline + rejection suite.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenVecMarkCountC.main`).
-- 1. Corpus pipeline: `tests/cir/mark_count_c.cir` (real CIRGen
--    output: the `const vector<char>&` mask + `vector<char>&`
--    visited + `u64` vertex entry with the `vis.at(u) = 1` seed
--    through the char mut-`at()` checked write, then the
--    size-bounded `for` counting the gated `vis` words with two
--    `s8i -> s32i` promotions (gate compare + accumulation),
--    `nsw` adds, `at()` checked reads; plus the char mut-`at()`
--    composer + the char `size` leaf + the char const-`at()`
--    composer + the char `_M_range_check` guard + both char
--    `operator[]` leaves) validates via `runModulePipeline` with NO
--    oracle facts (uniqueness comes from the `nonnull +
--    dereferenceable + noundef` attr triple, the M2a
--    single-reference precedent) and emits byte-identical text to
--    `tests/golden/VecMarkCountC.lean` (new: entry) and the new
--    `tests/golden/VecChar{AtMut,Size,At,RangeCheck,IndexMut,
--    Index}.lean` leaves (the leaf CoreIR is the width-agnostic
--    int family under the char mangled names; only Gate dispatch is
--    width-aware — file order: entry, at-mut, size, at-const,
--    range_check, index-mut, index-const).
-- 2. Rejection suite: `operator[]`-direct loop (bypasses `at()`),
--    `mark_count` (int) text is not char-mark-shaped and
--    `mark_count_c` text is not int-mark-shaped (shape-exactness
--    both directions across the width boundary), bare vector
--    pointer without the attr triple (alias discipline) — the first
--    hits the dedicated vector wrong-shape rejection, the second
--    and third the shape predicates directly, the last
--    `alias-reject`.
import Circe.Validator

namespace GoldenVecMarkCountC

def vecTriple : String :=
  "{llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}"

def vecRecC : String :=
  "!rec_std3A3Avector3Cchar2C_std3A3Aallocator3Cchar3E3E"

def vecSizeCEv : String :=
  "_ZNKSt6vectorIcSaIcEE4sizeEv"

def vecIndexMutCEv : String :=
  "_ZNSt6vectorIcSaIcEEixEm"

def checkVecMarkCountCPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/mark_count_c.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/VecMarkCountC.lean"
  let wantAtMut ← IO.FS.readFile "tests/golden/VecCharAtMut.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecCharSize.lean"
  let wantAt ← IO.FS.readFile "tests/golden/VecCharAt.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecCharRangeCheck.lean"
  let wantIndexMut ← IO.FS.readFile "tests/golden/VecCharIndexMut.lean"
  let wantIndex ← IO.FS.readFile "tests/golden/VecCharIndex.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected mark_count_c: {msg}")
  | .ok [("_Z12mark_count_cRKSt6vectorIcSaIcEERS1_m", gotEntry),
         ("_ZNSt6vectorIcSaIcEE2atEm", gotAtMut),
         ("_ZNKSt6vectorIcSaIcEE4sizeEv", gotSize),
         ("_ZNKSt6vectorIcSaIcEE2atEm", gotAt),
         ("_ZNKSt6vectorIcSaIcEE14_M_range_checkEm", gotRange),
         ("_ZNSt6vectorIcSaIcEEixEm", gotIndexMut),
         ("_ZNKSt6vectorIcSaIcEEixEm", gotIndex)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for mark_count_c entry")
    if gotAtMut != wantAtMut then
      throw (IO.userError "golden mismatch for char non-const at() composer")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    if gotAt != wantAt then
      throw (IO.userError "golden mismatch for char const at() composer")
    if gotRange != wantRange then
      throw (IO.userError "golden mismatch for char _M_range_check leaf")
    if gotIndexMut != wantIndexMut then
      throw (IO.userError "golden mismatch for char non-const operator[] leaf")
    if gotIndex != wantIndex then
      throw (IO.userError "golden mismatch for char const operator[] leaf")
    IO.println "PASS pipeline mark_count_c (entry + at-mut + size + at + range_check + index-mut + index, no oracle facts)"
    pure 7
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectVecMarkCountC (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-vecmarkcountc: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-vecmarkcountc: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-vecmarkcountc: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-vecmarkcountc {name} [{code}]"
    pure 1

/-- `operator[]`-direct loop over `vector<char>`: reads through the
    char mut leaf and accumulates, bypassing `at()` — the
    encapsulation pin rejects. -/
def advDirectIndexC : String :=
  "module {\n  cir.func @vmcdirect(%arg0: !cir.ptr<" ++ vecRecC ++ "> " ++ vecTriple ++ ", %arg1: !cir.ptr<" ++ vecRecC ++ "> " ++ vecTriple ++ ", %arg2: !u64i) -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %s = cir.call @" ++ vecSizeCEv ++ "(%arg0) : (!cir.ptr<" ++ vecRecC ++ ">) -> !u64i\n"
  ++ "    %z = cir.const #cir.int<0> : !u64i\n"
  ++ "    %p = cir.call @" ++ vecIndexMutCEv ++ "(%arg0, %z) : (!cir.ptr<" ++ vecRecC ++ ">, !u64i) -> !cir.ptr<!s8i>\n"
  ++ "    %v = cir.load %p : !cir.ptr<!s8i>, !s8i\n"
  ++ "    %c = cir.cast integral %v : !s8i -> !s32i\n"
  ++ "    %w = cir.add nsw %c, %c : !s32i\n"
  ++ "    cir.return %w : !s32i\n  }\n}"

/-- `mark_count` (int) text is not char-mark-shaped (same fold at a
    different width, no promotion casts). -/
def checkIntNotCharMark : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/mark_count.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-vecmarkcountc: mark_count corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z10mark_countRKSt6vectorIiSaIiEERS1_m") with
    | none => throw (IO.userError "reject-vecmarkcountc: mark_count not found")
    | some raw =>
      if isCharMarkCountShape raw then
        throw (IO.userError "reject-vecmarkcountc: mark_count text wrongly char-mark-shaped")
      IO.println "PASS reject-vecmarkcountc mark_count-not-charmark [shape-exact]"
      pure 1

/-- `mark_count_c` text is not int-mark-shaped either (the promotion
    casts keep the widths apart). -/
def checkCharNotIntMark : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/mark_count_c.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-vecmarkcountc: mark_count_c corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z12mark_count_cRKSt6vectorIcSaIcEERS1_m") with
    | none => throw (IO.userError "reject-vecmarkcountc: mark_count_c not found")
    | some raw =>
      if isMarkCountShape raw then
        throw (IO.userError "reject-vecmarkcountc: mark_count_c text wrongly int-mark-shaped")
      IO.println "PASS reject-vecmarkcountc mark_count_c-not-intmark [shape-exact]"
      pure 1

/-- Bare char vector pointer without the attr triple: the alias
    discipline rejects before shapes are even consulted. -/
def advBareVecPtrC : String :=
  "module {\n  cir.func @vmcbare(%arg0: !cir.ptr<" ++ vecRecC ++ "> {llvm.noundef}, %arg1: !cir.ptr<" ++ vecRecC ++ "> " ++ vecTriple ++ ", %arg2: !u64i) -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %z = cir.const #cir.int<0> : !s32i\n"
  ++ "    cir.return %z : !s32i\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkVecMarkCountCPipeline
  passed := passed + c0
  let r1 ← checkRejectVecMarkCountC "vmcdirect" advDirectIndexC .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r1
  let r2 ← checkIntNotCharMark
  passed := passed + r2
  let r3 ← checkCharNotIntMark
  passed := passed + r3
  let r4 ← checkRejectVecMarkCountC "vmcbare" advBareVecPtrC .unknown
    "alias-reject" "single-reference triple"
  passed := passed + r4
  IO.println s!"GOLDENVECMARKCOUNTC-OK passed={passed}"

end GoldenVecMarkCountC
