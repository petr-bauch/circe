-- Golden test for N9-ii: `std::array<uint32_t, 4>` insertion-sort
-- pipeline + rejection suite.
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenArraySort.lean`
-- 1. Corpus pipeline: `tests/cir/array_sort_sum.cir` (real CIRGen
--    output: the closed `array_sort_sum` entry + `insertion_sort` +
--    mutating `operator[]` + u32 `_S_ref`) validates via
--    `runModulePipeline` (the single `&mut` array param carries the
--    single-reference triple, the M2a precedent; the closed entry
--    takes its explicit fact, the `box_through` precedent) and emits
--    byte-identical text to
--    `tests/golden/{ArraySortSum,InsertionSort,ArrayAtU32,ArrayRefU32}.lean`.
-- 2. Rejection suite: call to an unknown u32 array callee (generic),
--    double call into the u32 `_S_ref` (single-site pin), mutating
--    `operator[]` called at the wrong arity, 3-site entry (not 4),
--    two-call sort-adjacent caller (not the 6-site loop) — the first
--    is generic, the rest hit the dedicated array wrong-shape
--    rejection.
--    Mismatch policy: any in-subset divergence is P0; out-of-subset must
--    reject loudly.
import Circe.Validator

namespace GoldenArraySort

def arrayU32Triple : String :=
  "{llvm.align = 4 : i64, llvm.dereferenceable = 16 : i64, llvm.nonnull, llvm.noundef}"

def sortEntryFact : OracleFact := ⟨"_Z14array_sort_sumv", .unknown⟩

def checkSortPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/array_sort_sum.cir"
  let wantSort ← IO.FS.readFile "tests/golden/InsertionSort.lean"
  let wantAt ← IO.FS.readFile "tests/golden/ArrayAtU32.lean"
  let wantEntry ← IO.FS.readFile "tests/golden/ArraySortSum.lean"
  let wantRef ← IO.FS.readFile "tests/golden/ArrayRefU32.lean"
  match runModulePipeline text [sortEntryFact] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected array_sort_sum: {msg}")
  | .ok [("_Z14insertion_sortRSt5arrayIjLm4EE", gotSort),
         ("_ZNSt5arrayIjLm4EEixEm", gotAt),
         ("_Z14array_sort_sumv", gotEntry),
         ("_ZNSt14__array_traitsIjLm4EE6_S_refERA4_Kjm", gotRef)] =>
    if gotSort != wantSort then
      throw (IO.userError "golden mismatch for insertion_sort")
    if gotAt != wantAt then
      throw (IO.userError "golden mismatch for mutating operator[] entry")
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for array_sort_sum entry")
    if gotRef != wantRef then
      throw (IO.userError "golden mismatch for u32 _S_ref leaf")
    IO.println "PASS pipeline array_sort_sum (entry + sort + at + ref)"
    pure 4
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectSort (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-sort: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-sort: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-sort: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-sort {name} [{code}]"
    pure 1

/-- Call to an unknown u32 array callee: generic call-shape rejection. -/
def advUnknownU32Callee : String :=
  "module {\n  cir.func @scall(%arg0: !cir.ptr<!rec_std3A3Aarray3Cunsigned_int2C_4UL3E> " ++ arrayU32Triple ++ ") -> !u32i attributes {\"nothrow\"} {\n"
  ++ "    %r = cir.call @_ZNSt5arrayIjLm4EEixEmX(%arg0) : (!cir.ptr<!rec_std3A3Aarray3Cunsigned_int2C_4UL3E>) -> !u32i\n    cir.return %r : !u32i\n  }\n}"

/-- Two call sites into the u32 `_S_ref`: the single-site pin rejects. -/
def advDoubleRefU32 : String :=
  "module {\n  cir.func @sdouble(%arg0: !cir.ptr<!cir.array<!u32i x 4>> " ++ arrayU32Triple ++ ", %arg1: !u64i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n"
  ++ "    %a = cir.call @_ZNSt14__array_traitsIjLm4EE6_S_refERA4_Kjm(%arg0, %arg1) : (!cir.ptr<!cir.array<!u32i x 4>>, !u64i) -> !cir.ptr<!u32i>\n"
  ++ "    %b = cir.call @_ZNSt14__array_traitsIjLm4EE6_S_refERA4_Kjm(%arg0, %arg1) : (!cir.ptr<!cir.array<!u32i x 4>>, !u64i) -> !cir.ptr<!u32i>\n"
  ++ "    %v = cir.load %a : !cir.ptr<!u32i>, !u32i\n    %w = cir.load %b : !cir.ptr<!u32i>, !u32i\n    %s = cir.add %v, %w : !u32i\n    cir.return %s : !u32i\n  }\n}"

/-- Mutating `operator[]` called at the wrong arity: no admitted caller
    targets it with three scalar params. -/
def advAtU32WrongArity : String :=
  "module {\n  cir.func @sarod(%arg0: !u32i {llvm.noundef}, %arg1: !u32i {llvm.noundef}, %arg2: !u32i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n"
  ++ "    %a = cir.call @_ZNSt5arrayIjLm4EEixEm(%arg0) : (!u32i) -> !cir.ptr<!u32i>\n    %v = cir.load %a : !cir.ptr<!u32i>, !u32i\n    cir.return %v : !u32i\n  }\n}"

/-- Three call sites into the mutating `operator[]` (not four) plus a
    sort call: the site-count pin rejects. -/
def advThreeReadsU32 : String :=
  "module {\n  cir.func @ssites() -> !u32i attributes {\"nothrow\"} {\n"
  ++ "    %s = cir.call @_Z14insertion_sortRSt5arrayIjLm4EE() : () -> !cir.ptr<!rec_std3A3Aarray3Cunsigned_int2C_4UL3E>\n"
  ++ "    %c0 = cir.const #cir.int<0> : !u64i\n"
  ++ "    %c1 = cir.const #cir.int<1> : !u64i\n"
  ++ "    %c2 = cir.const #cir.int<2> : !u64i\n"
  ++ "    %a = cir.call @_ZNSt5arrayIjLm4EEixEm(%s, %c0) : (!cir.ptr<!rec_std3A3Aarray3Cunsigned_int2C_4UL3E>, !u64i) -> !cir.ptr<!u32i>\n"
  ++ "    %b = cir.call @_ZNSt5arrayIjLm4EEixEm(%s, %c1) : (!cir.ptr<!rec_std3A3Aarray3Cunsigned_int2C_4UL3E>, !u64i) -> !cir.ptr<!u32i>\n"
  ++ "    %c = cir.call @_ZNSt5arrayIjLm4EEixEm(%s, %c2) : (!cir.ptr<!rec_std3A3Aarray3Cunsigned_int2C_4UL3E>, !u64i) -> !cir.ptr<!u32i>\n"
  ++ "    %v = cir.load %a : !cir.ptr<!u32i>, !u32i\n    %w = cir.load %b : !cir.ptr<!u32i>, !u32i\n    %x = cir.load %c : !cir.ptr<!u32i>, !u32i\n    %t = cir.add %v, %w : !u32i\n    %u = cir.add %t, %x : !u32i\n    cir.return %u : !u32i\n  }\n}"

/-- Sort-adjacent caller with two `operator[]` sites (not the 6-site
    loop): no loop shape matches, the wrong-shape pin rejects. -/
def advSortTwoCalls : String :=
  "module {\n  cir.func @stwocalls(%arg0: !cir.ptr<!rec_std3A3Aarray3Cunsigned_int2C_4UL3E> " ++ arrayU32Triple ++ ") -> !u32i attributes {\"nothrow\"} {\n"
  ++ "    %c0 = cir.const #cir.int<0> : !u64i\n"
  ++ "    %c1 = cir.const #cir.int<1> : !u64i\n"
  ++ "    %a = cir.call @_ZNSt5arrayIjLm4EEixEm(%arg0, %c0) : (!cir.ptr<!rec_std3A3Aarray3Cunsigned_int2C_4UL3E>, !u64i) -> !cir.ptr<!u32i>\n"
  ++ "    %b = cir.call @_ZNSt5arrayIjLm4EEixEm(%arg0, %c1) : (!cir.ptr<!rec_std3A3Aarray3Cunsigned_int2C_4UL3E>, !u64i) -> !cir.ptr<!u32i>\n"
  ++ "    %v = cir.load %a : !cir.ptr<!u32i>, !u32i\n    %w = cir.load %b : !cir.ptr<!u32i>, !u32i\n    %s = cir.add %v, %w : !u32i\n    cir.return %s : !u32i\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkSortPipeline
  passed := passed + c0
  let r1 ← checkRejectSort "scall" advUnknownU32Callee .unknown
    "out-of-subset" "outside the admitted call shapes"
  passed := passed + r1
  let r2 ← checkRejectSort "sdouble" advDoubleRefU32 .unknown
    "out-of-subset" "calls a known `std::array` leaf"
  passed := passed + r2
  let r3 ← checkRejectSort "sarod" advAtU32WrongArity .unknown
    "out-of-subset" "calls a known `std::array` leaf"
  passed := passed + r3
  let r4 ← checkRejectSort "ssites" advThreeReadsU32 .unknown
    "out-of-subset" "calls a known `std::array` leaf"
  passed := passed + r4
  let r5 ← checkRejectSort "stwocalls" advSortTwoCalls .unknown
    "out-of-subset" "calls a known `std::array` leaf"
  passed := passed + r5
  IO.println s!"GOLDENARRAYSORT-OK passed={passed}"

end GoldenArraySort
