-- Golden test for remove-if (`list_filter` over caller-owned
-- `Node {val, next}` with `free`): pillar-1 goal, every-match
-- deallocating sweep (dangling-loud discipline: each victim is
-- unlinked and freed, survivors keep order, and the (possibly new)
-- head is returned; a miss returns the head untouched).
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenListFilter.main`).
-- 1. Corpus pipeline: `tests/cir/list_filter.cir` (real CIRGen output:
--    `Node* head` + `i32 val` in, `Node*` out; 6 allocas, 18 loads,
--    11 stores, one `while`, two `cir.if`, 3 `cir.cmp`, one
--    `cir.call @free` + `get_global`, 3 `cir.const`, one `cast`,
--    single tail `cir.return`) validates via `runModulePipeline`
--    with an `unknown` oracle fact and emits byte-identical text to
--    `tests/golden/ListFilter.lean`.
-- 2. Rejection suite: three-pointer variant (one more live pointer
--    — the offender gate fires: `alias-reject`); double-free
--    variant (a victim is freed twice — the count gate fires:
--    `out-of-subset`); sibling texts are not filter-shaped and
--    `list_filter` text is not sibling-shaped (shape-exactness both
--    directions, including the erase/clear deallocating confusions).
import Circe.Validator

namespace GoldenListFilter

def filterFact : OracleFact := ⟨"_Z11list_filterP4Nodei", .unknown⟩

def checkListFilterPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_filter.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/ListFilter.lean"
  match runModulePipeline text [filterFact] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected list_filter: {msg}")
  | .ok [("_Z11list_filterP4Nodei", gotEntry)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for list_filter entry")
    IO.println "PASS pipeline list_filter (entry, unknown oracle fact)"
    pure 1
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the
    message plus `substr`. -/
def checkRejectListFilter (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-filter: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-filter: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-filter: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-filter {name} [{code}]"
    pure 1

/-- Three-pointer variant: the corpus signature plus a third bare
    `Node*` param. Same body, one more live pointer — the offender
    gate fires first (a bare pointer among live ones cannot be
    discharged): `alias-reject`. -/
def advThreePtr (text : String) : String :=
  text.replace "%arg1: !s32i {llvm.noundef} loc(fused[#loc5, #loc6])"
    "%arg1: !s32i {llvm.noundef} loc(fused[#loc5, #loc6]), %arg2: !cir.ptr<!rec_Node> {llvm.noundef} loc(fused[#loc5, #loc6])"

def checkThreePtrRejects : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_filter.cir"
  checkRejectListFilter "_Z11list_filterP4Nodei" (advThreePtr text) .unknown
    "alias-reject" "__restrict__"

/-- Double-free variant: a victim is freed twice. The count
    gate fires (`out-of-subset`): heap blocks are freed at most
    once — the dangling-loud discipline for the sweeping shape. -/
def advDoubleFree (text : String) : String :=
  text.replace "cir.call @free(%20) nothrow : (!cir.ptr<!void> {llvm.noundef}) -> () loc(#loc73)"
    "cir.call @free(%20) nothrow : (!cir.ptr<!void> {llvm.noundef}) -> () loc(#loc73)\n              cir.call @free(%20) nothrow : (!cir.ptr<!void> {llvm.noundef}) -> () loc(#loc73)"

def checkDoubleFreeRejects : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_filter.cir"
  checkRejectListFilter "_Z11list_filterP4Nodei" (advDoubleFree text) .unknown
    "out-of-subset" "more times than"

/-- Sibling texts are not filter-shaped (writer legs with
    caller-provided nodes / read-only chases / the allocating cons
    / the single-hit unlink-free-return, not the
    chase-unlink-every-match-free sweep). -/
def checkSibsNotListFilter : IO Nat := do
  let mut n := 0
  for (f, nm) in [("tests/cir/list_append.cir", "list_append"),
      ("tests/cir/list_length.cir", "list_length"),
      ("tests/cir/linked_reverse.cir", "linked_reverse"),
      ("tests/cir/list_rev.cir", "list_rev"),
      ("tests/cir/push_front.cir", "push_front")] do
    let text ← IO.FS.readFile f
    match parseModule text with
    | none =>
      throw (IO.userError s!"reject-filter: {nm} corpus failed to parse")
    | some m =>
      if m.funcs.any isListFilterShape then
        throw (IO.userError s!"reject-filter: {nm} text wrongly filtershaped")
      IO.println s!"PASS reject-filter {nm}-not-filter [shape-exact]"
      n := n + 1
  pure n

/-- `list_filter` text is not sibling-shaped (every-match sweep,
    not a caller-node swing, a read-only count, an in-place chase,
    an allocating cons, a single-hit erase, or a payload-blind
    free-all). -/
def checkListFilterNotSibs : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_filter.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-filter: list_filter corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z11list_filterP4Nodei") with
    | none =>
      throw (IO.userError "reject-filter: list_filter not found")
    | some raw =>
      if isListAppendShape raw then
        throw (IO.userError "reject-filter: list_filter text wrongly listappend-shaped")
      if isListLengthShape raw then
        throw (IO.userError "reject-filter: list_filter text wrongly listlength-shaped")
      if isLinkedReverseShape raw then
        throw (IO.userError "reject-filter: list_filter text wrongly linkedreverse-shaped")
      if isPushFrontShape raw then
        throw (IO.userError "reject-filter: list_filter text wrongly pushfront-shaped")
      if isListEraseShape raw then
        throw (IO.userError "reject-filter: list_filter text wrongly listerase-shaped")
      if isListClearShape raw then
        throw (IO.userError "reject-filter: list_filter text wrongly listclear-shaped")
      IO.println "PASS reject-filter filter-not-sibs [shape-exact]"
      pure 1

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkListFilterPipeline
  passed := passed + c0
  let r1 ← checkThreePtrRejects
  passed := passed + r1
  let r2 ← checkDoubleFreeRejects
  passed := passed + r2
  let r3 ← checkSibsNotListFilter
  passed := passed + r3
  let r4 ← checkListFilterNotSibs
  passed := passed + r4
  IO.println s!"GOLDENLISTFILTER-OK passed={passed}"

end GoldenListFilter
