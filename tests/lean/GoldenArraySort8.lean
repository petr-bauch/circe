-- Golden test for N9b: `std::array<uint32_t, 8>` insertion-sort
-- pipeline + rejection suite (second monomorph; each monomorph is its
-- own shape, the N4c precedent).
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenArraySort8.lean`
-- 1. Corpus pipeline: `tests/cir/array_sort_sum8.cir` (real CIRGen
--    output: the closed `array_sort_sum8` entry + `insertion_sort8` +
--    mutating `operator[]` + u32 `_S_ref`) validates via
--    `runModulePipeline` (same oracle-fact convention as the N=4
--    runner) and emits byte-identical text to
--    `tests/golden/{ArraySortSum8,InsertionSort8,ArrayAtU328,ArrayRefU328}.lean`.
-- 2. Rejection suite: 7-site entry (not 8), two-call sort-adjacent
--    caller (not the 6-site loop), double call into the u32 `_S_ref`
--    (single-site pin) — all hit the dedicated array wrong-shape
--    rejection.
--    Mismatch policy: any in-subset divergence is P0; out-of-subset must
--    reject loudly.
import Circe.Validator

namespace GoldenArraySort8

def arrayU32Triple8 : String :=
  "{llvm.align = 4 : i64, llvm.dereferenceable = 32 : i64, llvm.nonnull, llvm.noundef}"

def sortEntryFact8 : OracleFact := ⟨"_Z15array_sort_sum8v", .unknown⟩

def checkSortPipeline8 : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/array_sort_sum8.cir"
  let wantSort ← IO.FS.readFile "tests/golden/InsertionSort8.lean"
  let wantAt ← IO.FS.readFile "tests/golden/ArrayAtU328.lean"
  let wantEntry ← IO.FS.readFile "tests/golden/ArraySortSum8.lean"
  let wantRef ← IO.FS.readFile "tests/golden/ArrayRefU328.lean"
  match runModulePipeline text [sortEntryFact8] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected array_sort_sum8: {msg}")
  | .ok [("_Z15insertion_sort8RSt5arrayIjLm8EE", gotSort),
         ("_ZNSt5arrayIjLm8EEixEm", gotAt),
         ("_Z15array_sort_sum8v", gotEntry),
         ("_ZNSt14__array_traitsIjLm8EE6_S_refERA8_Kjm", gotRef)] =>
    if gotSort != wantSort then
      throw (IO.userError "golden mismatch for insertion_sort8")
    if gotAt != wantAt then
      throw (IO.userError "golden mismatch for mutating operator[] entry (8)")
    if gotEntry != wantEntry then
      throw (IO.userError "golden mismatch for array_sort_sum8 entry")
    if gotRef != wantRef then
      throw (IO.userError "golden mismatch for u32 _S_ref leaf (8)")
    IO.println "PASS pipeline array_sort_sum8 (entry + sort + at + ref)"
    pure 4
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectSort8 (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-sort8: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-sort8: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-sort8: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-sort8 {name} [{code}]"
    pure 1

/-- Seven call sites into the mutating `operator[]` (not eight) plus a
    sort call: the site-count pin rejects. -/
def advSevenReadsU32 : String :=
  "module {\n  cir.func @ssites8() -> !u32i attributes {\"nothrow\"} {\n"
  ++ "    %s = cir.call @_Z15insertion_sort8RSt5arrayIjLm8EE() : () -> !cir.ptr<!rec_std3A3Aarray3Cunsigned_int2C_8UL3E>\n"
  ++ "    %c0 = cir.const #cir.int<0> : !u64i\n"
  ++ "    %c1 = cir.const #cir.int<1> : !u64i\n"
  ++ "    %c2 = cir.const #cir.int<2> : !u64i\n"
  ++ "    %c3 = cir.const #cir.int<3> : !u64i\n"
  ++ "    %c4 = cir.const #cir.int<4> : !u64i\n"
  ++ "    %c5 = cir.const #cir.int<5> : !u64i\n"
  ++ "    %c6 = cir.const #cir.int<6> : !u64i\n"
  ++ "    %a = cir.call @_ZNSt5arrayIjLm8EEixEm(%s, %c0) : (!cir.ptr<!rec_std3A3Aarray3Cunsigned_int2C_8UL3E>, !u64i) -> !cir.ptr<!u32i>\n"
  ++ "    %b = cir.call @_ZNSt5arrayIjLm8EEixEm(%s, %c1) : (!cir.ptr<!rec_std3A3Aarray3Cunsigned_int2C_8UL3E>, !u64i) -> !cir.ptr<!u32i>\n"
  ++ "    %c = cir.call @_ZNSt5arrayIjLm8EEixEm(%s, %c2) : (!cir.ptr<!rec_std3A3Aarray3Cunsigned_int2C_8UL3E>, !u64i) -> !cir.ptr<!u32i>\n"
  ++ "    %d = cir.call @_ZNSt5arrayIjLm8EEixEm(%s, %c3) : (!cir.ptr<!rec_std3A3Aarray3Cunsigned_int2C_8UL3E>, !u64i) -> !cir.ptr<!u32i>\n"
  ++ "    %e = cir.call @_ZNSt5arrayIjLm8EEixEm(%s, %c4) : (!cir.ptr<!rec_std3A3Aarray3Cunsigned_int2C_8UL3E>, !u64i) -> !cir.ptr<!u32i>\n"
  ++ "    %f = cir.call @_ZNSt5arrayIjLm8EEixEm(%s, %c5) : (!cir.ptr<!rec_std3A3Aarray3Cunsigned_int2C_8UL3E>, !u64i) -> !cir.ptr<!u32i>\n"
  ++ "    %g = cir.call @_ZNSt5arrayIjLm8EEixEm(%s, %c6) : (!cir.ptr<!rec_std3A3Aarray3Cunsigned_int2C_8UL3E>, !u64i) -> !cir.ptr<!u32i>\n"
  ++ "    %v = cir.load %a : !cir.ptr<!u32i>, !u32i\n    %t = cir.add %v, %v : !u32i\n    cir.return %t : !u32i\n  }\n}"

/-- Sort-adjacent caller with two `operator[]` sites (not the 6-site
    loop) over the 8-word array: no loop shape matches, the
    wrong-shape pin rejects. -/
def advSortTwoCalls8 : String :=
  "module {\n  cir.func @stwocalls8(%arg0: !cir.ptr<!rec_std3A3Aarray3Cunsigned_int2C_8UL3E> " ++ arrayU32Triple8 ++ ") -> !u32i attributes {\"nothrow\"} {\n"
  ++ "    %c0 = cir.const #cir.int<0> : !u64i\n"
  ++ "    %c1 = cir.const #cir.int<1> : !u64i\n"
  ++ "    %a = cir.call @_ZNSt5arrayIjLm8EEixEm(%arg0, %c0) : (!cir.ptr<!rec_std3A3Aarray3Cunsigned_int2C_8UL3E>, !u64i) -> !cir.ptr<!u32i>\n"
  ++ "    %b = cir.call @_ZNSt5arrayIjLm8EEixEm(%arg0, %c1) : (!cir.ptr<!rec_std3A3Aarray3Cunsigned_int2C_8UL3E>, !u64i) -> !cir.ptr<!u32i>\n"
  ++ "    %v = cir.load %a : !cir.ptr<!u32i>, !u32i\n    %w = cir.load %b : !cir.ptr<!u32i>, !u32i\n    %s = cir.add %v, %w : !u32i\n    cir.return %s : !u32i\n  }\n}"

/-- Two call sites into the 8-word u32 `_S_ref`: the single-site pin
    rejects. -/
def advDoubleRefU328 : String :=
  "module {\n  cir.func @sdouble8(%arg0: !cir.ptr<!cir.array<!u32i x 8>> " ++ arrayU32Triple8 ++ ", %arg1: !u64i {llvm.noundef}) -> !u32i attributes {\"nothrow\"} {\n"
  ++ "    %a = cir.call @_ZNSt14__array_traitsIjLm8EE6_S_refERA8_Kjm(%arg0, %arg1) : (!cir.ptr<!cir.array<!u32i x 8>>, !u64i) -> !cir.ptr<!u32i>\n"
  ++ "    %b = cir.call @_ZNSt14__array_traitsIjLm8EE6_S_refERA8_Kjm(%arg0, %arg1) : (!cir.ptr<!cir.array<!u32i x 8>>, !u64i) -> !cir.ptr<!u32i>\n"
  ++ "    %v = cir.load %a : !cir.ptr<!u32i>, !u32i\n    %w = cir.load %b : !cir.ptr<!u32i>, !u32i\n    %s = cir.add %v, %w : !u32i\n    cir.return %s : !u32i\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkSortPipeline8
  passed := passed + c0
  let r1 ← checkRejectSort8 "ssites8" advSevenReadsU32 .unknown
    "out-of-subset" "calls a known `std::array` leaf"
  passed := passed + r1
  let r2 ← checkRejectSort8 "stwocalls8" advSortTwoCalls8 .unknown
    "out-of-subset" "calls a known `std::array` leaf"
  passed := passed + r2
  let r3 ← checkRejectSort8 "sdouble8" advDoubleRefU328 .unknown
    "out-of-subset" "calls a known `std::array` leaf"
  passed := passed + r3
  IO.println s!"GOLDENARRAYSORT8-OK passed={passed}"

end GoldenArraySort8
