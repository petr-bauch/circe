-- Golden test for the cursor-stack push kernel: `stack_push`
-- pipeline + rejection suite.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenVecStackPush.main`).
-- 1. Corpus pipeline: `tests/cir/stack_push.cir` (real CIRGen
--    output: the `vector<int>&` workspace + `u64` cursor + `i32`
--    value entry with the single mut-`at()` guarded store plus one
--    wrapping `u64` cursor add + the mut-`at()` composer + the fused
--    `_M_range_check` guard + the non-const `operator[]` leaf + the
--    `size` leaf) validates via `runModulePipeline` with NO oracle
--    facts (uniqueness comes from the `nonnull + dereferenceable +
--    noundef` attr triple, the M2a single-reference precedent)
--    and emits byte-identical text to
--    `tests/golden/VecStackPush.lean` (new: entry) and the shared
--    `tests/golden/{VecAtMut,VecRangeCheck,VecIndexMut,VecSize}.lean`
--    leaves (file order: entry, at-mut, range_check, index-mut,
--    size).
-- 2. Rejection suite: `operator[]`-direct store (bypasses `at()`),
--    `vec_at_set` text is not push-shaped (different arity and
--    return) and `stack_push` text is not at-set-shaped
--    (shape-exactness both directions), bare vector pointer without
--    the attr triple (alias discipline) — the first hits the
--    dedicated vector wrong-shape rejection, the second and third
--    the shape predicates directly, the last `alias-reject`.
import Circe.Validator

namespace GoldenVecStackPush

def vecTriple : String :=
  "{llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}"

def vecRec : String :=
  "!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E"

def vecIndexMutEv : String :=
  "_ZNSt6vectorIiSaIiEEixEm"

def checkVecStackPushPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/stack_push.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/VecStackPush.lean"
  let wantAtMut ← IO.FS.readFile "tests/golden/VecAtMut.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndexMut ← IO.FS.readFile "tests/golden/VecIndexMut.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected stack_push: {msg}")
  | .ok [("_Z10stack_pushRSt6vectorIiSaIiEEmi", gotEntry),
         ("_ZNSt6vectorIiSaIiEE2atEm", gotAtMut),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNSt6vectorIiSaIiEEixEm", gotIndexMut),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for stack_push entry")
    if gotAtMut != wantAtMut then
      throw (IO.userError "golden mismatch for non-const at() composer")
    if gotRange != wantRange then
      throw (IO.userError "golden mismatch for _M_range_check leaf")
    if gotIndexMut != wantIndexMut then
      throw (IO.userError "golden mismatch for non-const operator[] leaf")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    IO.println "PASS pipeline stack_push (entry + at-mut + range_check + index-mut + size, no oracle facts)"
    pure 5
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectVecStackPush (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-vecstackpush: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-vecstackpush: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-vecstackpush: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-vecstackpush {name} [{code}]"
    pure 1

/-- `operator[]`-direct store: writes through the mutable leaf,
    bypassing `at()` — the encapsulation pin rejects. -/
def advDirectIndex : String :=
  "module {\n  cir.func @vwdirect(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !u64i, %arg2: !s32i) attributes {\"nothrow\"} {\n"
  ++ "    %p = cir.call @" ++ vecIndexMutEv ++ "(%arg0, %arg1) : (!cir.ptr<" ++ vecRec ++ ">, !u64i) -> !cir.ptr<!s32i>\n"
  ++ "    cir.store %arg2, %p : !s32i, !cir.ptr<!s32i>\n"
  ++ "    cir.return %arg1 : !u64i\n  }\n}"

/-- `vec_at_set` text is not push-shaped (void store with no cursor
    return: different arity and return type). -/
def checkAtSetNotPush : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/vec_at_set.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-vecstackpush: vec_at_set corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z10vec_at_setRSt6vectorIiSaIiEEmi") with
    | none => throw (IO.userError "reject-vecstackpush: vec_at_set not found")
    | some raw =>
      if isStackPushShape raw then
        throw (IO.userError "reject-vecstackpush: vec_at_set text wrongly push-shaped")
      IO.println "PASS reject-vecstackpush vec_at_set-not-push [shape-exact]"
      pure 1

/-- `stack_push` text is not at-set-shaped either (`u64` return plus
    the cursor increment). -/
def checkPushNotAtSet : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/stack_push.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-vecstackpush: stack_push corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z10stack_pushRSt6vectorIiSaIiEEmi") with
    | none => throw (IO.userError "reject-vecstackpush: stack_push not found")
    | some raw =>
      if isVecAtSetShape raw then
        throw (IO.userError "reject-vecstackpush: stack_push text wrongly at-set-shaped")
      IO.println "PASS reject-vecstackpush stack_push-not-atset [shape-exact]"
      pure 1

/-- Bare vector pointer without the attr triple: the alias
    discipline rejects before shapes are even consulted. -/
def advBareVecPtr : String :=
  "module {\n  cir.func @vwbare(%arg0: !cir.ptr<" ++ vecRec ++ "> {llvm.noundef}, %arg1: !u64i, %arg2: !s32i) attributes {\"nothrow\"} {\n"
  ++ "    %z = cir.const #cir.int<0> : !u64i\n"
  ++ "    cir.return %z : !u64i\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkVecStackPushPipeline
  passed := passed + c0
  let r1 ← checkRejectVecStackPush "vwdirect" advDirectIndex .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r1
  let r2 ← checkAtSetNotPush
  passed := passed + r2
  let r3 ← checkPushNotAtSet
  passed := passed + r3
  let r4 ← checkRejectVecStackPush "vwbare" advBareVecPtr .unknown
    "alias-reject" "single-reference triple"
  passed := passed + r4
  IO.println s!"GOLDENVECSTACKPUSH-OK passed={passed}"

end GoldenVecStackPush
