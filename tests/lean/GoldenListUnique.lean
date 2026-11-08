-- Golden test for adjacent-duplicate squeeze (`list_unique`
-- over caller-owned `Node {val, next}` with `free`): pillar-1
-- goal, every predecessor-equal node unlinked and freed
-- (dangling-loud discipline: survivors keep order, the head
-- never moves and is returned unchanged; a miss returns the
-- head untouched).
--
-- Run from the repo root via the driver (`lake exe circe-test` runs
-- `GoldenListUnique.main`).
-- 1. Corpus pipeline: `tests/cir/list_unique.cir` (real CIRGen output:
--    single `Node*` head in, `Node*` out; 5 allocas, 18 loads,
--    9 stores, one `while`, one `cir.if`, one `cir.ternary` (the
--    `prev != nullptr &&` short-circuit), 3 `cir.cmp`, one
--    `cir.call @free` + `get_global`, 4 `cir.const`, one `cast`,
--    single tail `cir.return`) validates via `runModulePipeline`
--    with an `unknown` oracle fact and emits byte-identical text to
--    `tests/golden/ListUnique.lean`.
-- 2. Rejection suite: three-pointer variant (one more live pointer
--    — the offender gate fires: `alias-reject`); double-free
--    variant (a victim is freed twice — the count gate fires:
--    `out-of-subset`); sibling texts are not unique-shaped and
--    `list_unique` text is not sibling-shaped (shape-exactness both
--    directions, including the filter/erase/clear deallocating
--    confusions).
import Circe.Validator

namespace GoldenListUnique

def uniqueFact : OracleFact := ⟨"_Z11list_uniqueP4Node", .unknown⟩

def checkListUniquePipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_unique.cir"
  let wantEntry ← IO.FS.readFile "tests/golden/ListUnique.lean"
  match runModulePipeline text [uniqueFact] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected list_unique: {msg}")
  | .ok [("_Z11list_uniqueP4Node", gotEntry)] =>
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for list_unique entry")
    IO.println "PASS pipeline list_unique (entry, unknown oracle fact)"
    pure 1
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the
    message plus `substr`. -/
def checkRejectListUnique (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-unique: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-unique: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-unique: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-unique {name} [{code}]"
    pure 1

/-- Three-pointer variant: the corpus signature plus a second bare
    `Node*` param. Same body, one more live pointer — the offender
    gate fires first (a bare pointer among live ones cannot be
    discharged): `alias-reject`. -/
def advThreePtr (text : String) : String :=
  text.replace "%arg0: !cir.ptr<!rec_Node> {llvm.noundef} loc(fused[#loc3, #loc4])"
    "%arg0: !cir.ptr<!rec_Node> {llvm.noundef} loc(fused[#loc3, #loc4]), %arg1: !cir.ptr<!rec_Node> {llvm.noundef} loc(fused[#loc3, #loc4])"

def checkThreePtrRejects : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_unique.cir"
  checkRejectListUnique "_Z11list_uniqueP4Node" (advThreePtr text) .unknown
    "alias-reject" "__restrict__"

/-- Double-free variant: a victim is freed twice. The count
    gate fires (`out-of-subset`): heap blocks are freed at most
    once — the dangling-loud discipline for the sweeping shape. -/
def advDoubleFree (text : String) : String :=
  text.replace "cir.call @free(%21) nothrow : (!cir.ptr<!void> {llvm.noundef}) -> () loc(#loc62)"
    "cir.call @free(%21) nothrow : (!cir.ptr<!void> {llvm.noundef}) -> () loc(#loc62)\n              cir.call @free(%21) nothrow : (!cir.ptr<!void> {llvm.noundef}) -> () loc(#loc62)"

def checkDoubleFreeRejects : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_unique.cir"
  checkRejectListUnique "_Z11list_uniqueP4Node" (advDoubleFree text) .unknown
    "out-of-subset" "more times than"

/-- Tamper probe: rewriting the dropout `cir.ternary` as `cir.if`
    still parses but breaks the ternary/`if` pins (shape-exact,
    no gate involved). Probed in `/tmp`: parses, `isListUniqueShape = false`. -/
def checkTamperTernary : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_unique.cir"
  let bad := text.replace "cir.ternary" "cir.if"
  match parseModule bad with
  | none =>
    throw (IO.userError "tamper-ternary: tampered corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z11list_uniqueP4Node") with
    | none =>
      throw (IO.userError "tamper-ternary: entry missing after tamper")
    | some raw =>
      if isListUniqueShape raw then
        throw (IO.userError "tamper-ternary: ternary-rewrite still unique-shaped")
      IO.println "PASS tamper-ternary rewrite-not-unique [shape-exact]"
      pure 1

/-- Sibling texts are not unique-shaped (writer legs with
    caller-provided nodes / read-only chases / the allocating cons
    / the single-hit unlink-free-return / the payload-blind
    free-all, not the chase-compare-predecessor squeeze). -/
def checkSibsNotListUnique : IO Nat := do
  let mut n := 0
  for (f, nm) in [("tests/cir/list_append.cir", "list_append"),
      ("tests/cir/list_length.cir", "list_length"),
      ("tests/cir/linked_reverse.cir", "linked_reverse"),
      ("tests/cir/list_rev.cir", "list_rev"),
      ("tests/cir/push_front.cir", "push_front"),
      ("tests/cir/list_filter.cir", "list_filter")] do
    let text ← IO.FS.readFile f
    match parseModule text with
    | none =>
      throw (IO.userError s!"reject-unique: {nm} corpus failed to parse")
    | some m =>
      if m.funcs.any isListUniqueShape then
        throw (IO.userError s!"reject-unique: {nm} text wrongly uniqueshaped")
      IO.println s!"PASS reject-unique {nm}-not-unique [shape-exact]"
      n := n + 1
  pure n

/-- `list_unique` text is not sibling-shaped (predecessor-equal
    squeeze, not a caller-node swing, a read-only count, an
    in-place chase, an allocating cons, a single-hit erase, a
    payload-blind free-all, or an every-match sweep). -/
def checkListUniqueNotSibs : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/list_unique.cir"
  match parseModule text with
  | none =>
    throw (IO.userError "reject-unique: list_unique corpus failed to parse")
  | some m =>
    match m.funcs.find? (fun f => f.name == "_Z11list_uniqueP4Node") with
    | none =>
      throw (IO.userError "reject-unique: list_unique not found")
    | some raw =>
      if isListAppendShape raw then
        throw (IO.userError "reject-unique: list_unique text wrongly listappend-shaped")
      if isListLengthShape raw then
        throw (IO.userError "reject-unique: list_unique text wrongly listlength-shaped")
      if isLinkedReverseShape raw then
        throw (IO.userError "reject-unique: list_unique text wrongly linkedreverse-shaped")
      if isPushFrontShape raw then
        throw (IO.userError "reject-unique: list_unique text wrongly pushfront-shaped")
      if isListEraseShape raw then
        throw (IO.userError "reject-unique: list_unique text wrongly listerase-shaped")
      if isListClearShape raw then
        throw (IO.userError "reject-unique: list_unique text wrongly listclear-shaped")
      if isListFilterShape raw then
        throw (IO.userError "reject-unique: list_unique text wrongly filter-shaped")
      IO.println "PASS reject-unique unique-not-sibs [shape-exact]"
      pure 1

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkListUniquePipeline
  passed := passed + c0
  let r1 ← checkThreePtrRejects
  passed := passed + r1
  let r2 ← checkDoubleFreeRejects
  passed := passed + r2
  let t3 ← checkTamperTernary
  passed := passed + t3
  let r4 ← checkSibsNotListUnique
  passed := passed + r4
  let r5 ← checkListUniqueNotSibs
  passed := passed + r5
  IO.println s!"GOLDENLISTUNIQUE-OK passed={passed}"

end GoldenListUnique
