-- Golden test for iterative DFS over a caller-grown stack:
-- `dfs_grow` pipeline + rejection suite.
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenVecDfsGrow.main`).
-- 1. Corpus pipeline: `tests/cir/dfs_grow.cir` (real CIRGen
--    output: the `const&` matrix + `&` visited + `&` caller-grown
--    stack + `u64` n/src entry with the `vis[src] = 1` + seed
--    `push_back`, the `while top != 0` drain that pops into `v`,
--    and the inner `for u in 0..n` row scan with the `m[v*n+u] !=
--    0` + `vis[u] == 0` gates, the `vis[u] = 1` mark, and the
--    slot-reuse/grow push with `top`/`count` wrap counting; plus
--    the mutable `at()` composer + the const `at()` composer + the
--    `size` leaf + the fused `_M_range_check` guard + the mutable
--    `operator[]` leaf + the `push_back`/`emplace_back` composers +
--    the `_M_realloc_insert` slow-path machinery) validates via
--    `validateModule` with explicit `.noalias` facts (the growth
--    leaves carry no attr triple) and emits byte-identical text to
--    `tests/golden/VecDfsGrow.lean` (entry) and the shared
--    `tests/golden/{VecAtMut,VecGrowComposerPushBack,VecAt,VecSize,
--    VecRangeCheck,VecIndexMut,VecGrowComposerEmplace,
--    VecGrowConstruct,VecGrowComposerRealloc,VecGrowEnd,VecGrowBack,
--    VecGrowCheckLen,VecGrowMinus,VecGrowBegin,VecGrowAlloc,
--    VecGrowReloc,VecGrowGetTp,VecGrowDestroyNoop,VecGrowDeallocGuard,
--    VecGrowMax,VecGrowMin,VecGrowDiffMax,VecGrowIterId,
--    VecGrowDestroyPtr}.lean` leaves (module order).
-- 2. Rejection suite: `operator[]`-direct pair entry (bypasses
--    `at()`), `mark_count` text is not dfs-grow-shaped (gated fold,
--    not the seeded stack drain), `dfs_grow` text is not
--    mark-count-shaped (shape-exactness both directions),
--    `dfs_reachable` text is not dfs-grow-shaped (reserve-upfront
--    push vs the slot/grow branch — the G4 count pins), `dfs_grow`
--    text is not dfs-reachable-shaped, self-recursive entry, bare
--    vector pointer without the attr triple (alias discipline) —
--    the first and fourth hit the dedicated vector wrong-shape
--    rejection, the second/third/fifth/sixth the shape predicates
--    directly, the last `alias-reject`.
import Circe.Validator

namespace GoldenVecDfsGrow

def vecTriple : String :=
  "{llvm.align = 8 : i64, llvm.dereferenceable = 24 : i64, llvm.nonnull, llvm.noundef}"

def vecRec : String :=
  "!rec_std3A3Avector3Cint2C_std3A3Aallocator3Cint3E3E"

def vecSizeEv : String :=
  "_ZNKSt6vectorIiSaIiEE4sizeEv"

def vecIndexEv : String :=
  "_ZNSt6vectorIiSaIiEEixEm"

/-- Per-def `.noalias` facts for the 46-def `dfs_grow` frontier
    (the `vecGrowFacts` discipline: every defined def carries an
    explicit fact; erased params need no uniqueness inside pinned
    shapes). -/
def vecDfsGrowFacts : List OracleFact :=
  [⟨"_Z8dfs_growRKSt6vectorIiSaIiEERS1_S4_mm", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE2atEm", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE9push_backEOi", .noalias⟩,
   ⟨"_ZNKSt6vectorIiSaIiEE2atEm", .noalias⟩,
   ⟨"_ZNKSt6vectorIiSaIiEE4sizeEv", .noalias⟩,
   ⟨"_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEEixEm", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE12emplace_backIJiEEERiDpOT_", .noalias⟩,
   ⟨"_ZNSt16allocator_traitsISaIiEE9constructIiJiEEEvRS0_PT_DpOT0_", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE17_M_realloc_insertIJiEEEvN9__gnu_cxx17__normal_iteratorIPiS1_EEDpOT_", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE3endEv", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE4backEv", .noalias⟩,
   ⟨"_ZN9__gnu_cxx13new_allocatorIiE9constructIiJiEEEvPT_DpOT0_", .noalias⟩,
   ⟨"_ZNKSt6vectorIiSaIiEE12_M_check_lenEmPKc", .noalias⟩,
   ⟨"_ZN9__gnu_cxxmiIPiSt6vectorIiSaIiEEEENS_17__normal_iteratorIT_T0_E15difference_typeERKS8_SB_", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE5beginEv", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEE11_M_allocateEm", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE11_S_relocateEPiS2_S2_RS0_", .noalias⟩,
   ⟨"_ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEE4baseEv", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEE19_M_get_Tp_allocatorEv", .noalias⟩,
   ⟨"_ZNSt16allocator_traitsISaIiEE7destroyIiEEvRS0_PT_", .noalias⟩,
   ⟨"_ZSt8_DestroyIPiiEvT_S1_RSaIT0_E", .noalias⟩,
   ⟨"_ZNSt12_Vector_baseIiSaIiEE13_M_deallocateEPim", .noalias⟩,
   ⟨"_ZNKSt6vectorIiSaIiEE8max_sizeEv", .noalias⟩,
   ⟨"_ZSt3maxImERKT_S2_S2_", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE11_S_max_sizeERKS0_", .noalias⟩,
   ⟨"_ZNKSt12_Vector_baseIiSaIiEE19_M_get_Tp_allocatorEv", .noalias⟩,
   ⟨"_ZNSt16allocator_traitsISaIiEE8max_sizeERKS0_", .noalias⟩,
   ⟨"_ZSt3minImERKT_S2_S2_", .noalias⟩,
   ⟨"_ZNK9__gnu_cxx13new_allocatorIiE8max_sizeEv", .noalias⟩,
   ⟨"_ZNK9__gnu_cxx13new_allocatorIiE11_M_max_sizeEv", .noalias⟩,
   ⟨"_ZN9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEC2ERKS1_", .noalias⟩,
   ⟨"_ZNSt16allocator_traitsISaIiEE8allocateERS0_m", .noalias⟩,
   ⟨"_ZN9__gnu_cxx13new_allocatorIiE8allocateEmPKv", .noalias⟩,
   ⟨"_ZNSt6vectorIiSaIiEE14_S_do_relocateEPiS2_S2_RS0_St17integral_constantIbLb1EE", .noalias⟩,
   ⟨"_ZSt12__relocate_aIPiS0_SaIiEET0_T_S3_S2_RT1_", .noalias⟩,
   ⟨"_ZSt14__relocate_a_1IiiENSt9enable_ifIXsr3std24__is_bitwise_relocatableIT_EE5valueEPS1_E4typeES2_S2_S2_RSaIT0_E", .noalias⟩,
   ⟨"_ZSt12__niter_baseIPiET_S1_", .noalias⟩,
   ⟨"_ZN9__gnu_cxx13new_allocatorIiE7destroyIiEEvPT_", .noalias⟩,
   ⟨"_ZSt8_DestroyIPiEvT_S1_", .noalias⟩,
   ⟨"_ZNSt12_Destroy_auxILb1EE9__destroyIPiEEvT_S3_", .noalias⟩,
   ⟨"_ZNSt16allocator_traitsISaIiEE10deallocateERS0_Pim", .noalias⟩,
   ⟨"_ZN9__gnu_cxx13new_allocatorIiE10deallocateEPim", .noalias⟩,
   ⟨"_ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEmiEl", .noalias⟩,
   ⟨"_ZNK9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEdeEv", .noalias⟩,
   ⟨"_ZNKSt6vectorIiSaIiEEixEm", .noalias⟩]

/-- The pinned `dfs_grow` leaves: corpus def name × golden stem
    (each validates and emits byte-identical text to the shared
    golden). -/
def vecDfsGrowLeaves : List (String × String) :=
  [("_ZNSt6vectorIiSaIiEE2atEm", "VecAtMut"),
   ("_ZNSt6vectorIiSaIiEE9push_backEOi", "VecGrowComposerPushBack"),
   ("_ZNKSt6vectorIiSaIiEE2atEm", "VecAt"),
   ("_ZNKSt6vectorIiSaIiEE4sizeEv", "VecSize"),
   ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", "VecRangeCheck"),
   ("_ZNSt6vectorIiSaIiEEixEm", "VecIndexMut"),
   ("_ZNSt6vectorIiSaIiEE12emplace_backIJiEEERiDpOT_", "VecGrowComposerEmplace"),
   ("_ZNSt16allocator_traitsISaIiEE9constructIiJiEEEvRS0_PT_DpOT0_", "VecGrowConstruct"),
   ("_ZNSt6vectorIiSaIiEE17_M_realloc_insertIJiEEEvN9__gnu_cxx17__normal_iteratorIPiS1_EEDpOT_", "VecGrowComposerRealloc"),
   ("_ZNSt6vectorIiSaIiEE3endEv", "VecGrowEnd"),
   ("_ZNSt6vectorIiSaIiEE4backEv", "VecGrowBack"),
   ("_ZNKSt6vectorIiSaIiEE12_M_check_lenEmPKc", "VecGrowCheckLen"),
   ("_ZN9__gnu_cxxmiIPiSt6vectorIiSaIiEEEENS_17__normal_iteratorIT_T0_E15difference_typeERKS8_SB_", "VecGrowMinus"),
   ("_ZNSt6vectorIiSaIiEE5beginEv", "VecGrowBegin"),
   ("_ZNSt12_Vector_baseIiSaIiEE11_M_allocateEm", "VecGrowAlloc"),
   ("_ZNSt6vectorIiSaIiEE11_S_relocateEPiS2_S2_RS0_", "VecGrowReloc"),
   ("_ZNSt12_Vector_baseIiSaIiEE19_M_get_Tp_allocatorEv", "VecGrowGetTp"),
   ("_ZSt8_DestroyIPiiEvT_S1_RSaIT0_E", "VecGrowDestroyNoop"),
   ("_ZNSt12_Vector_baseIiSaIiEE13_M_deallocateEPim", "VecGrowDeallocGuard"),
   ("_ZSt3maxImERKT_S2_S2_", "VecGrowMax"),
   ("_ZSt3minImERKT_S2_S2_", "VecGrowMin"),
   ("_ZNK9__gnu_cxx13new_allocatorIiE11_M_max_sizeEv", "VecGrowDiffMax"),
   ("_ZN9__gnu_cxx17__normal_iteratorIPiSt6vectorIiSaIiEEEC2ERKS1_", "VecGrowIterId"),
   ("_ZN9__gnu_cxx13new_allocatorIiE7destroyIiEEvPT_", "VecGrowDestroyPtr")]

/-- The admitted `dfs_grow` entry: corpus def name × golden stem
    (validates to `dfsGrowFunc` and emits byte-identical text, entry
    plus spec). -/
def vecDfsGrowAdmitted : List (String × String) :=
  [("_Z8dfs_growRKSt6vectorIiSaIiEERS1_S4_mm", "VecDfsGrow")]

def checkVecDfsGrowPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/dfs_grow.cir"
  let res := validateModule text vecDfsGrowFacts
  if res.length != 46 then
    throw (IO.userError s!"dfs-grow frontier drift: {res.length} defs, expected 46")
  let errs := res.filter (fun (_, v) => !v.isOk)
  if errs.length != 0 then
    throw (IO.userError s!"dfs-grow rejects drift: {errs.length} errors, expected 0 (entry admitted)")
  for (name, g) in vecDfsGrowLeaves do
    match res.find? (fun (m, _) => m == name) with
    | none =>
      throw (IO.userError s!"dfs-grow leaf missing from corpus: {name}")
    | some (_, .error rej) =>
      throw (IO.userError s!"dfs-grow leaf unexpectedly rejected: {name}: {rej.message}")
    | some (_, .ok f) =>
      let want ← IO.FS.readFile s!"tests/golden/{g}.lean"
      let got := emitFileText (emitFunc f)
      if got != want then
        throw (IO.userError s!"golden mismatch for {g} ({name})")
  IO.println "PASS pipeline dfs_grow (24 pinned leaves byte-identical)"
  for (name, g) in vecDfsGrowAdmitted do
    match res.find? (fun (m, _) => m == name) with
    | none =>
      throw (IO.userError s!"dfs-grow admitted entry missing: {name}")
    | some (_, .error rej) =>
      throw (IO.userError s!"dfs-grow admitted entry rejected: {name}: {rej.message}")
    | some (_, .ok f) =>
      let want ← IO.FS.readFile s!"tests/golden/{g}.lean"
      let got := emitFileText (emitFunc f)
      if got != want then
        throw (IO.userError s!"golden mismatch for {g} ({name})")
      let wantSpec ← IO.FS.readFile s!"tests/golden/{g}_Spec.lean"
      let gotSpec ← match emitSpec f with
        | .ok s => pure s
        | .error _ => throw (IO.userError s!"spec emit failed for {g} ({name})")
      if gotSpec != wantSpec then
        throw (IO.userError s!"spec golden mismatch for {g} ({name})")
  IO.println "PASS pipeline dfs_grow (entry + spec byte-identical)"
  pure (vecDfsGrowLeaves.length + vecDfsGrowAdmitted.length)

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectVecDfsGrow (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-vecdfsgrow: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-vecdfsgrow: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-vecdfsgrow: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-vecdfsgrow {name} [{code}]"
    pure 1

/-- `operator[]`-direct entry: reads through the mutable leaf,
    bypassing `at()` — the encapsulation pin rejects. -/
def advDirectIndex : String :=
  "module {\n  cir.func @dgdirect(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg2: !u64i) -> !u64i attributes {\"nothrow\"} {\n"
  ++ "    %s = cir.call @" ++ vecSizeEv ++ "(%arg0) : (!cir.ptr<" ++ vecRec ++ ">) -> !u64i\n"
  ++ "    %z = cir.const #cir.int<0> : !u64i\n"
  ++ "    %p = cir.call @" ++ vecIndexEv ++ "(%arg0, %z) : (!cir.ptr<" ++ vecRec ++ ">, !u64i) -> !cir.ptr<!s32i>\n"
  ++ "    %v = cir.load %p : !cir.ptr<!s32i>, !s32i\n"
  ++ "    %w = cir.cast integral %v : !s32i -> !u64i\n"
  ++ "    cir.return %w : !u64i\n  }\n}"

/-- `mark_count` text is not dfs-grow-shaped (gated fold, not the
    seeded stack drain with nested scan). -/
def checkMarkCountNotDfsGrow : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/mark_count.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-vecdfsgrow: mark_count corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z10mark_countRKSt6vectorIiSaIiEERS1_m") with
    | none => throw (IO.userError "reject-vecdfsgrow: mark_count not found")
    | some raw =>
      if isDfsGrowShape raw then
        throw (IO.userError "reject-vecdfsgrow: mark_count text wrongly dfs-grow-shaped")
      IO.println "PASS reject-vecdfsgrow mark_count-not-dfsgrow [shape-exact]"
      pure 1

/-- `dfs_grow` text is not mark-count-shaped either (seeded drain,
    not the gated fold). -/
def checkDfsGrowNotMarkCount : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/dfs_grow.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-vecdfsgrow: dfs_grow corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z8dfs_growRKSt6vectorIiSaIiEERS1_S4_mm") with
    | none => throw (IO.userError "reject-vecdfsgrow: dfs_grow not found")
    | some raw =>
      if isMarkCountShape raw then
        throw (IO.userError "reject-vecdfsgrow: dfs_grow text wrongly mark-count-shaped")
      IO.println "PASS reject-vecdfsgrow dfsgrow-not-markcount [shape-exact]"
      pure 1

/-- `dfs_reachable` text is not dfs-grow-shaped (reserve-upfront
    guarded push, not the slot-reuse/grow branch — the G4 op-count
    pins separate them). -/
def checkDfsNotDfsGrow : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/dfs_reachable.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-vecdfsgrow: dfs_reachable corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z13dfs_reachableRKSt6vectorIiSaIiEERS1_S4_mm") with
    | none => throw (IO.userError "reject-vecdfsgrow: dfs_reachable not found")
    | some raw =>
      if isDfsGrowShape raw then
        throw (IO.userError "reject-vecdfsgrow: dfs_reachable text wrongly dfs-grow-shaped")
      IO.println "PASS reject-vecdfsgrow dfs-not-dfsgrow [shape-exact]"
      pure 1

/-- `dfs_grow` text is not dfs-reachable-shaped either (slot/grow
    branch, not the reserve-upfront push). -/
def checkDfsGrowNotDfs : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/dfs_grow.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-vecdfsgrow: dfs_grow corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z8dfs_growRKSt6vectorIiSaIiEERS1_S4_mm") with
    | none => throw (IO.userError "reject-vecdfsgrow: dfs_grow not found")
    | some raw =>
      if isDfsReachableShape raw then
        throw (IO.userError "reject-vecdfsgrow: dfs_grow text wrongly dfs-shaped")
      IO.println "PASS reject-vecdfsgrow dfsgrow-not-dfs [shape-exact]"
      pure 1

/-- Self-recursive entry: the call-multiset pin (no self-call)
    rejects via the wrong-shape branch. -/
def advRecursive : String :=
  "module {\n  cir.func @dgrec(%arg0: !cir.ptr<" ++ vecRec ++ "> " ++ vecTriple ++ ", %arg1: !u64i) -> !u64i attributes {\"nothrow\"} {\n"
  ++ "    cir.call @dgrec(%arg0, %arg1) : (!cir.ptr<" ++ vecRec ++ ">, !u64i) -> !u64i\n"
  ++ "    %z = cir.const #cir.int<0> : !u64i\n"
  ++ "    cir.return %z : !u64i\n  }\n}"

/-- Bare vector pointer without the attr triple: the alias
    discipline rejects before shapes are even consulted. -/
def advBareVecPtr : String :=
  "module {\n  cir.func @dgbare(%arg0: !cir.ptr<" ++ vecRec ++ "> {llvm.noundef}, %arg1: !u64i) -> !u64i attributes {\"nothrow\"} {\n"
  ++ "    %z = cir.const #cir.int<0> : !u64i\n"
  ++ "    cir.return %z : !u64i\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkVecDfsGrowPipeline
  passed := passed + c0
  let r1 ← checkRejectVecDfsGrow "dgdirect" advDirectIndex .unknown
    "out-of-subset" "calls a known `std::vector` leaf"
  passed := passed + r1
  let r2 ← checkMarkCountNotDfsGrow
  passed := passed + r2
  let r3 ← checkDfsGrowNotMarkCount
  passed := passed + r3
  let r4 ← checkDfsNotDfsGrow
  passed := passed + r4
  let r5 ← checkDfsGrowNotDfs
  passed := passed + r5
  let r6 ← checkRejectVecDfsGrow "dgrec" advRecursive .unknown
    "out-of-subset" "calls itself"
  passed := passed + r6
  let r7 ← checkRejectVecDfsGrow "dgbare" advBareVecPtr .unknown
    "alias-reject" "single-reference triple"
  passed := passed + r7
  IO.println s!"GOLDENVECDFSGROW-OK passed={passed}"

end GoldenVecDfsGrow
