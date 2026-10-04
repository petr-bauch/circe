-- Golden test for N4d-iii: `std::span<const int32_t>` index-sum
-- pipeline + rejection suite.
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenSpan.lean`
-- 1. Corpus pipeline: `tests/cir/span_sum.cir` (real CIRGen output
--    with `-std=c++20`: the by-value-span `span_sum` index-loop entry
--    + the single-delegation `size` + the fused `operator[]` with the
--    dead disabled-assert skeleton + the `_M_extent` extent leaf)
--    validates via `runModulePipeline` with ONE oracle fact for the
--    by-value entry (no pointer param, so no synthetic-fact triple —
--    the M2b int-only-entry precedent) and emits byte-identical text
--    to `tests/golden/{SpanSum,SpanSize,SpanIndex,SpanExtent}.lean`
--    (file order: entry, size, index, extent).
-- 2. Rejection suite: call to an unknown span callee (generic),
--    double call into `size` (site-count pin), a live-assert
--    `operator[]` variant (dead-skeleton pin), `size` called at the
--    wrong arity, bare span pointer without the attr triple (alias
--    discipline) — the first is generic, the middle three hit the
--    dedicated span wrong-shape rejection, the last `alias-reject`.
-- 3. Deferral pin (the slice's containment result): the range-for
--    form lowers to `begin`/`end` iterator calls plus
--    pointer-chasing, outside the admitted call shapes — index-based
--    `size()`/`operator[]` is IN, range-for is OUT.
--    Mismatch policy: any in-subset divergence is P0; out-of-subset
--    must reject loudly.
import Circe.Validator

namespace GoldenSpan

def spanTriple : String :=
  "{llvm.align = 8 : i64, llvm.dereferenceable = 16 : i64, llvm.nonnull, llvm.noundef}"

def spanRec : String :=
  "!rec_std3A3Aspan3Cconst_int2C_18446744073709551615UL3E"

def spanEntryName : String :=
  "_Z8span_sumSt4spanIKiLm18446744073709551615EE"

def spanSizeEv : String :=
  "_ZNKSt4spanIKiLm18446744073709551615EE4sizeEv"

def spanIndexEv : String :=
  "_ZNKSt4spanIKiLm18446744073709551615EEixEm"

def spanExtentEv : String :=
  "_ZNKSt8__detail16__extent_storageILm18446744073709551615EE9_M_extentEv"

def checkSpanPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/span_sum.cir"
  let wantSum ← IO.FS.readFile "tests/golden/SpanSum.lean"
  let wantSize ← IO.FS.readFile "tests/golden/SpanSize.lean"
  let wantIndex ← IO.FS.readFile "tests/golden/SpanIndex.lean"
  let wantExtent ← IO.FS.readFile "tests/golden/SpanExtent.lean"
  match runModulePipeline text [⟨spanEntryName, .unknown⟩] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected span_sum: {msg}")
  | .ok [( "_Z8span_sumSt4spanIKiLm18446744073709551615EE", gotSum),
         ("_ZNKSt4spanIKiLm18446744073709551615EE4sizeEv", gotSize),
         ("_ZNKSt4spanIKiLm18446744073709551615EEixEm", gotIndex),
         ("_ZNKSt8__detail16__extent_storageILm18446744073709551615EE9_M_extentEv", gotExtent)] =>
    if gotSum != wantSum then
      throw (IO.userError "golden mismatch for span_sum entry")
    if gotSize != wantSize then
      throw (IO.userError "golden mismatch for size leaf")
    if gotIndex != wantIndex then
      throw (IO.userError "golden mismatch for operator[] leaf")
    if gotExtent != wantExtent then
      throw (IO.userError "golden mismatch for _M_extent leaf")
    IO.println "PASS pipeline span_sum (entry + size + index + extent, one entry fact)"
    pure 4
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectSpan (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-span: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-span: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-span: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-span {name} [{code}]"
    pure 1

/-- Call to an unknown span callee: generic call-shape rejection. -/
def advUnknownSpanCallee : String :=
  "module {\n  cir.func @scall(%arg0: !cir.ptr<" ++ spanRec ++ "> " ++ spanTriple ++ ") -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %r = cir.call @_ZNKSt4spanIKiLm18446744073709551615EE5beginEvX(%arg0) : (!cir.ptr<" ++ spanRec ++ ">) -> !cir.ptr<!s32i>\n"
  ++ "    %v = cir.load %r : !cir.ptr<!s32i>, !s32i\n    cir.return %v : !s32i\n  }\n}"

/-- Two call sites into `size`: the single-site pin rejects. -/
def advDoubleSize : String :=
  "module {\n  cir.func @ssize2(%arg0: !cir.ptr<" ++ spanRec ++ "> " ++ spanTriple ++ ") -> !u64i attributes {\"nothrow\"} {\n"
  ++ "    %a = cir.call @" ++ spanSizeEv ++ "(%arg0) : (!cir.ptr<" ++ spanRec ++ ">) -> !u64i\n"
  ++ "    %b = cir.call @" ++ spanSizeEv ++ "(%arg0) : (!cir.ptr<" ++ spanRec ++ ">) -> !u64i\n"
  ++ "    %s = cir.add %a, %b : !u64i\n    cir.return %s : !u64i\n  }\n}"

/-- Live-assert `operator[]` variant: the ternary condition is a live
    `not` over loaded index words instead of the `#false` const (two
    `#false` consts, not three; two `cmp`s and two `not`s, not one) —
    the shape a `-D_GLIBCXX_ASSERTIONS` build would approach. The
    dead-skeleton pin rejects it. -/
def advLiveAssertSpan : String :=
  "module {\n  cir.func @slive(%arg0: !cir.ptr<" ++ spanRec ++ "> " ++ spanTriple ++ ", %arg1: !u64i {llvm.noundef}) -> !cir.ptr<!s32i> attributes {\"nothrow\"} {\n"
  ++ "    %slot = cir.alloca \"i\" : !cir.ptr<!u64i>\n"
  ++ "    %9 = cir.load %slot : !cir.ptr<!u64i>, !u64i\n"
  ++ "    %9b = cir.load %slot : !cir.ptr<!u64i>, !u64i\n"
  ++ "    %9c = cir.cmp lt %9, %9b : !u64i\n"
  ++ "    %9d = cir.not %9c : !cir.bool\n"
  ++ "    %10 = cir.ternary(%9d, true {\n"
  ++ "      %11 = cir.load %slot : !cir.ptr<!u64i>, !u64i\n"
  ++ "      %12 = cir.call @" ++ spanSizeEv ++ "(%arg0) : (!cir.ptr<" ++ spanRec ++ ">) -> !u64i\n"
  ++ "      %13 = cir.cmp lt %11, %12 : !u64i\n"
  ++ "      %14 = cir.not %13 : !cir.bool\n"
  ++ "      cir.yield %14 : !cir.bool\n"
  ++ "    }, false {\n"
  ++ "      %15 = cir.const #false\n"
  ++ "      cir.yield %15 : !cir.bool\n"
  ++ "    }) : (!cir.bool) -> !cir.bool\n"
  ++ "    cir.if %10 {\n      cir.unreachable\n    }\n"
  ++ "    %4 = cir.get_member %arg0[0] {name = \"_M_ptr\"} : !cir.ptr<" ++ spanRec ++ "> -> !cir.ptr<!cir.ptr<!s32i>>\n"
  ++ "    %5 = cir.load %4 : !cir.ptr<!cir.ptr<!s32i>>, !cir.ptr<!s32i>\n"
  ++ "    %7 = cir.ptr_stride %5, %arg1 : (!cir.ptr<!s32i>, !u64i) -> !cir.ptr<!s32i>\n"
  ++ "    cir.return %7 : !cir.ptr<!s32i>\n  }\n}"

/-- `size` called at the wrong arity: no admitted shape takes three
    `i32`s into the span `size` leaf. -/
def advSizeWrongArity : String :=
  "module {\n  cir.func @sarod(%arg0: !s32i {llvm.noundef}, %arg1: !s32i {llvm.noundef}, %arg2: !s32i {llvm.noundef}) -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %a = cir.call @" ++ spanSizeEv ++ "(%arg0) : (!s32i) -> !u64i\n"
  ++ "    %b = cir.const #cir.int<0> : !s32i\n"
  ++ "    cir.return %b : !s32i\n  }\n}"

/-- Bare span pointer without the attr triple: the alias discipline
    rejects before shapes are even consulted. -/
def advBareSpanPtr : String :=
  "module {\n  cir.func @sbare(%arg0: !cir.ptr<" ++ spanRec ++ "> {llvm.noundef}) -> !u64i attributes {\"nothrow\"} {\n"
  ++ "    %r = cir.call @" ++ spanSizeEv ++ "(%arg0) : (!cir.ptr<" ++ spanRec ++ ">) -> !u64i\n"
  ++ "    cir.return %r : !u64i\n  }\n}"

/-- N4d-iii containment pin (range-for): the range-for form lowers to
    `begin`/`end` iterator calls plus pointer-chasing, outside the
    admitted call shapes — index-based `size()`/`operator[]` is IN,
    range-for is OUT. -/
def advRangeFor : String :=
  "module {\n  cir.func @srange(%arg0: !cir.ptr<" ++ spanRec ++ "> " ++ spanTriple ++ ") -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %b = cir.call @_ZNKSt4spanIKiLm18446744073709551615EE5beginEv(%arg0) : (!cir.ptr<" ++ spanRec ++ ">) -> !cir.ptr<!s32i>\n"
  ++ "    %e = cir.call @_ZNKSt4spanIKiLm18446744073709551615EE3endEv(%arg0) : (!cir.ptr<" ++ spanRec ++ ">) -> !cir.ptr<!s32i>\n"
  ++ "    %v = cir.load %b : !cir.ptr<!s32i>, !s32i\n"
  ++ "    %w = cir.load %e : !cir.ptr<!s32i>, !s32i\n"
  ++ "    %s = cir.add nsw %v, %w : !s32i\n"
  ++ "    cir.return %s : !s32i\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkSpanPipeline
  passed := passed + c0
  let r1 ← checkRejectSpan "scall" advUnknownSpanCallee .unknown
    "out-of-subset" "outside the admitted call shapes"
  passed := passed + r1
  let r2 ← checkRejectSpan "ssize2" advDoubleSize .unknown
    "out-of-subset" "calls a known `std::span` leaf"
  passed := passed + r2
  let r3 ← checkRejectSpan "slive" advLiveAssertSpan .unknown
    "out-of-subset" "calls a known `std::span` leaf"
  passed := passed + r3
  let r4 ← checkRejectSpan "sarod" advSizeWrongArity .unknown
    "out-of-subset" "calls a known `std::span` leaf"
  passed := passed + r4
  let r5 ← checkRejectSpan "sbare" advBareSpanPtr .unknown
    "alias-reject" "single-reference triple"
  passed := passed + r5
  let d1 ← checkRejectSpan "srange" advRangeFor .unknown
    "out-of-subset" "outside the admitted call shapes"
  passed := passed + d1
  IO.println s!"GOLDENSPAN-OK passed={passed}"

end GoldenSpan
