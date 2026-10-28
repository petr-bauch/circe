-- Golden test for breadth-first traversal over `const std::vector<int>&`:
-- `bfs_order` pipeline + rejection suite.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenVecBfs.main`).
-- 1. Corpus pipeline: `tests/cir/bfs_order.cir` (real CIRGen
--    output: the `const&` matrix + `&` visited + `&` queue +
--    `&` visit-order record + `u64` n/src entry with the
--    `vis[src] = 1` + `q[0] = src` seed, the `while head != tail`
--    drain that dequeues into `v` and records the visit in
--    `order[head]`, and the inner `for u in 0..n` row scan with the
--    `m[v*n+u] != 0` + `vis[u] == 0` gates, the `vis[u] = 1` mark,
--    and the guarded `q[tail] = u` enqueue with `tail/count` wrap
--    counting; plus the mutable `at()` composer + the const `at()`
--    composer + the fused `_M_range_check` guard + both
--    `operator[]` leaves + the `size` leaf) validates via
--    `runModulePipeline` with NO oracle facts (uniqueness comes from
--    the `nonnull + dereferenceable + noundef` attr triple, the M2a
--    single-reference precedent) and emits byte-identical text to
--    `tests/golden/VecBfs.lean` (entry) and the shared
--    `tests/golden/{VecAtMut,VecAt,VecRangeCheck,VecIndexMut,
--    VecSize,VecIndex}.lean` leaves (file order: entry, at-mut,
--    at-const, range_check, index-mut, size, index-const).
-- 2. Rejection suite: `operator[]`-direct pair entry (bypasses
--    `at()`), `mark_count` text is not bfs-shaped (gated fold, not
--    the seeded queue drain with visit record), `bfs_order` text is
--    not mark-count-shaped (shape-exactness both directions),
--    self-recursive entry, bare vector pointer without the attr
--    triple (alias discipline) — the first and fourth hit the
--    dedicated vector wrong-shape rejection, the second and third
--    the shape predicate directly, the last `alias-reject`.
import Circe.Validator

namespace GoldenVecBfs

def vecTriple : String :=
  "{llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}"

def vecRec : String :=
  "!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E"

def vecSizeEv : String :=
  "_ZNKSt6vectorIiSaIiEE4sizeEv"

def vecIndexEv : String :=
  "_ZNSt6vectorIiSaIiEEixEm"

def checkVecBfsPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/bfs_order.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/VecBfs.lean"
  let wantAtMut ← IO.FS.readFile "tests/golden/VecAtMut.lean"
  let wantAt ← IO.FS.readFile "tests/golden/VecAt.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndexMut ← IO.FS.readFile "tests/golden/VecIndexMut.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  let wantIndex ← IO.FS.readFile "tests/golden/VecIndex.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected bfs_order: {msg}")
  | .ok [("_Z9bfs_orderRKSt6vectorIiSaIiEERS1_S4_S4_mm", gotEntry),
         ("_ZNSt6vectorIiSaIiEE2atEm", gotAtMut),
         ("_ZNKSt6vectorIiSaIiEE2atEm", gotAt),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNSt6vectorIiSaIiEEixEm", gotIndexMut),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize),
         ("_ZNKSt6vectorIiSaIiEEixEm", gotIndex)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for bfs_order entry")
    if gotAtMut != wantAtMut then
      throw (IO.userError "golden mismatch for non-const at() composer")
    if gotAt != wantAt then
      throw (IO.userError "golden mismatch for const at() composer")
    if gotRange != wantRange then
      throw (IO.userError "golden mismatch for _M_range_check leaf")
    if gotIndexMut != wantIndexMut then
      throw (IO.userError "golden mismatch for non-const operator[] leaf")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    if gotIndex != wantIndex then
      throw (IO.userError "golden mismatch for const operator[] leaf")
    IO.println "PASS pipeline bfs_order (entry + at-mut + at + range_check + index-mut + size + index, no oracle facts)"
    pure 7
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectVecBfs (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-vecbfs: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-vecbfs: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-vecbfs: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-vecbfs {name} [{code}]"
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

/-- `mark_count` text is not bfs-shaped (gated fold, not the seeded
    queue drain with visit record). -/
def checkMarkCountNotBfs : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/mark_count.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-vecbfs: mark_count corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z10mark_countRKSt6vectorIiSaIiEERS1_m") with
    | none => throw (IO.userError "reject-vecbfs: mark_count not found")
    | some raw =>
      if isBfsOrderShape raw then
        throw (IO.userError "reject-vecbfs: mark_count text wrongly bfs-shaped")
      IO.println "PASS reject-vecbfs mark_count-not-bfs [shape-exact]"
      pure 1

/-- `bfs_order` text is not mark-count-shaped either (seeded drain,
    not the gated fold). -/
def checkBfsNotMarkCount : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/bfs_order.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-vecbfs: bfs_order corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z9bfs_orderRKSt6vectorIiSaIiEERS1_S4_S4_mm") with
    | none => throw (IO.userError "reject-vecbfs: bfs_order not found")
    | some raw =>
      if isMarkCountShape raw then
        throw (IO.userError "reject-vecbfs: bfs_order text wrongly mark-count-shaped")
      IO.println "PASS reject-vecbfs bfs-not-markcount [shape-exact]"
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
  let c0 ← checkVecBfsPipeline
  passed := passed + c0
  let r1 ← checkRejectVecBfs "vbdirect" advDirectIndex .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r1
  let r2 ← checkMarkCountNotBfs
  passed := passed + r2
  let r3 ← checkBfsNotMarkCount
  passed := passed + r3
  let r4 ← checkRejectVecBfs "vbrec" advRecursive .unknown
    "out-of-subset" "calls itself"
  passed := passed + r4
  let r5 ← checkRejectVecBfs "vbbare" advBareVecPtr .unknown
    "alias-reject" "single-reference triple"
  passed := passed + r5
  IO.println s!"GOLDENVECBFS-OK passed={passed}"

end GoldenVecBfs
