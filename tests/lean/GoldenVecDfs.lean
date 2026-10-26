-- Golden test for iterative DFS over `const std::vector<int>&`:
-- `dfs_reachable` pipeline + rejection suite.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenVecDfs.main`).
-- 1. Corpus pipeline: `tests/cir/dfs_reachable.cir` (real CIRGen
--    output: the `const&` matrix + `&` visited + `&` stack +
--    `u64` n/src entry with the `vis[src] = 1` + `st[0] = src` seed,
--    the `while top != 0` drain that pops into `v`, and the inner
--    `for u in 0..n` row scan with the `m[v*n+u] != 0` + `vis[u]
--    == 0` gates, the `vis[u] = 1` mark, and the guarded `st[top] =
--    u` push with `top/count` wrap counting; plus the mutable `at()`
--    composer + the const `at()` composer + the fused
--    `_M_range_check` guard + both `operator[]` leaves + the `size`
--    leaf) validates via `runModulePipeline` with NO oracle facts
--    (uniqueness comes from the `nonnull + dereferenceable +
--    noundef` attr triple, the M2a single-reference precedent) and
--    emits byte-identical text to `tests/golden/VecDfs.lean` (entry)
--    and the shared `tests/golden/{VecAtMut,VecAt,VecRangeCheck,
--    VecIndexMut,VecSize,VecIndex}.lean` leaves (file order: entry,
--    at-mut, at-const, range_check, index-mut, size, index-const).
-- 2. Rejection suite: `operator[]`-direct pair entry (bypasses
--    `at()`), `mark_count` text is not dfs-shaped (gated fold, not
--    the seeded stack drain), `dfs_reachable` text is not
--    mark-count-shaped (shape-exactness both directions),
--    self-recursive entry, bare vector pointer without the attr
--    triple (alias discipline) — the first and fourth hit the
--    dedicated vector wrong-shape rejection, the second and third
--    the shape predicate directly, the last `alias-reject`.
import Circe.Validator

namespace GoldenVecDfs

def vecTriple : String :=
  "{llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}"

def vecRec : String :=
  "!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E"

def vecSizeEv : String :=
  "_ZNKSt6vectorIiSaIiEE4sizeEv"

def vecIndexEv : String :=
  "_ZNSt6vectorIiSaIiEEixEm"

def checkVecDfsPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/dfs_reachable.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/VecDfs.lean"
  let wantAtMut ← IO.FS.readFile "tests/golden/VecAtMut.lean"
  let wantAt ← IO.FS.readFile "tests/golden/VecAt.lean"
  let wantRange ← IO.FS.readFile "tests/golden/VecRangeCheck.lean"
  let wantIndexMut ← IO.FS.readFile "tests/golden/VecIndexMut.lean"
  let wantSize ← IO.FS.readFile "tests/golden/VecSize.lean"
  let wantIndex ← IO.FS.readFile "tests/golden/VecIndex.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected dfs_reachable: {msg}")
  | .ok [("_Z13dfs_reachableRKSt6vectorIiSaIiEERS1_S4_mm", gotEntry),
         ("_ZNSt6vectorIiSaIiEE2atEm", gotAtMut),
         ("_ZNKSt6vectorIiSaIiEE2atEm", gotAt),
         ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", gotRange),
         ("_ZNSt6vectorIiSaIiEEixEm", gotIndexMut),
         ("_ZNKSt6vectorIiSaIiEE4sizeEv", gotSize),
         ("_ZNKSt6vectorIiSaIiEEixEm", gotIndex)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for dfs_reachable entry")
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
    IO.println "PASS pipeline dfs_reachable (entry + at-mut + at + range_check + index-mut + size + index, no oracle facts)"
    pure 7
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectVecDfs (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-vecdfs: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-vecdfs: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-vecdfs: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-vecdfs {name} [{code}]"
    pure 1

/-- `operator[]`-direct entry: reads through the mutable leaf,
    bypassing `at()` — the encapsulation pin rejects. -/
def advDirectIndex : String :=
  "module {\n  cir.func @vddirect(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg2: !u64i) -> !u64i attributes {\"nothrow\"} {\n"
  ++ "    %s = cir.call @" ++ vecSizeEv ++ "(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> !u64i\n"
  ++ "    %z = cir.const #cir.int<0> : !u64i\n"
  ++ "    %p = cir.call @" ++ vecIndexEv ++ "(%arg0, %z) : (!cir.ptr<" ++ vecRec ++ ">, !u64i) -> !cir.ptr<!s32i>\n"
  ++ "    %v = cir.load %p : !cir.ptr<!s32i>, !s32i\n"
  ++ "    %w = cir.cast integral %v : !s32i -> !u64i\n"
  ++ "    cir.return %w : !u64i\n  }\n}"

/-- `mark_count` text is not dfs-shaped (gated fold, not the seeded
    stack drain with nested scan). -/
def checkMarkCountNotDfs : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/mark_count.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-vecdfs: mark_count corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z10mark_countRKSt6vectorIiSaIiEERS1_m") with
    | none => throw (IO.userError "reject-vecdfs: mark_count not found")
    | some raw =>
      if isDfsReachableShape raw then
        throw (IO.userError "reject-vecdfs: mark_count text wrongly dfs-shaped")
      IO.println "PASS reject-vecdfs mark_count-not-dfs [shape-exact]"
      pure 1

/-- `dfs_reachable` text is not mark-count-shaped either (seeded
    drain, not the gated fold). -/
def checkDfsNotMarkCount : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/dfs_reachable.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-vecdfs: dfs_reachable corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z13dfs_reachableRKSt6vectorIiSaIiEERS1_S4_mm") with
    | none => throw (IO.userError "reject-vecdfs: dfs_reachable not found")
    | some raw =>
      if isMarkCountShape raw then
        throw (IO.userError "reject-vecdfs: dfs_reachable text wrongly mark-count-shaped")
      IO.println "PASS reject-vecdfs dfs-not-markcount [shape-exact]"
      pure 1

/-- Self-recursive entry: the call-multiset pin (no self-call)
    rejects via the wrong-shape branch. -/
def advRecursive : String :=
  "module {\n  cir.func @vdrec(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !u64i) -> !u64i attributes {\"nothrow\"} {\n"
  ++ "    cir.call @vdrec(%arg0, %arg1) : (!cir.ptr<" ++ vecRec ++ ">, !u64i) -> !u64i\n"
  ++ "    %z = cir.const #cir.int<0> : !u64i\n"
  ++ "    cir.return %z : !u64i\n  }\n}"

/-- Bare vector pointer without the attr triple: the alias
    discipline rejects before shapes are even consulted. -/
def advBareVecPtr : String :=
  "module {\n  cir.func @vdbare(%arg0: !cir.ptr<" ++ vecRec ++ "> {llvm.noundef}, %arg1: !u64i) -> !u64i attributes {\"nothrow\"} {\n"
  ++ "    %z = cir.const #cir.int<0> : !u64i\n"
  ++ "    cir.return %z : !u64i\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkVecDfsPipeline
  passed := passed + c0
  let r1 ← checkRejectVecDfs "vddirect" advDirectIndex .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r1
  let r2 ← checkMarkCountNotDfs
  passed := passed + r2
  let r3 ← checkDfsNotMarkCount
  passed := passed + r3
  let r4 ← checkRejectVecDfs "vdrec" advRecursive .unknown
    "out-of-subset" "calls itself"
  passed := passed + r4
  let r5 ← checkRejectVecDfs "vdbare" advBareVecPtr .unknown
    "alias-reject" "single-reference triple"
  passed := passed + r5
  IO.println s!"GOLDENVECDFS-OK passed={passed}"

end GoldenVecDfs
