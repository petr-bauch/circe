-- Golden test for N7a: `std::string_view` range-for sum
-- pipeline + rejection suite.
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenView.lean`
-- 1. Corpus pipeline: `tests/cir/view_sum.cir` (real CIRGen output
--    with `-std=c++17`: the by-value `view_sum` range-for entry +
--    the `_M_str` `begin` leaf + the `_M_str`/`_M_len` `end` leaf)
--    validates via `runModulePipeline` with ONE oracle fact for the
--    by-value entry (no pointer param, so no synthetic-fact triple —
--    the M2b int-only-entry precedent; both leaves take the view
--    `const&` with the single-reference triple, so they validate
--    under synthetic `unknown` facts) and emits byte-identical text
--    to `tests/golden/{ViewSum,ViewBegin,ViewEnd}.lean`
--    (file order: entry, begin, end).
-- 2. Rejection suite: call to an unknown view callee (generic),
--    double call into `begin` (site-count pin), two `end` calls
--    from one caller (callee-arity pin), a `begin` body with a
--    stride (no-stride pin), an entry missing the `s8i -> s32i`
--    sext (small-width pin), bare view pointer without the attr
--    triple (alias discipline).
--    Mismatch policy: any in-subset divergence is P0; out-of-subset
--    must reject loudly.
import Circe.Validator

namespace GoldenView

def viewTriple : String :=
  "{llvm.align = 8 : i64, llvm.dereferenceable = 16 : i64, llvm.nonnull, llvm.noundef}"

def viewRec : String :=
  "!rec_std3A3Abasic_string_view3Cchar2C_std3A3Achar_traits3Cchar3E3E"

def viewEntryName : String :=
  "_Z8view_sumSt17basic_string_viewIcSt11char_traitsIcEE"

def viewBeginEv : String :=
  "_ZNKSt17basic_string_viewIcSt11char_traitsIcEE5beginEv"

def viewEndEv : String :=
  "_ZNKSt17basic_string_viewIcSt11char_traitsIcEE3endEv"

def checkViewPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/view_sum.cir"
  let wantSum ← IO.FS.readFile "tests/golden/ViewSum.lean"
  let wantBegin ← IO.FS.readFile "tests/golden/ViewBegin.lean"
  let wantEnd ← IO.FS.readFile "tests/golden/ViewEnd.lean"
  match runModulePipeline text [⟨viewEntryName, .unknown⟩] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected view_sum: {msg}")
  | .ok [("_Z8view_sumSt17basic_string_viewIcSt11char_traitsIcEE", gotSum),
         ("_ZNKSt17basic_string_viewIcSt11char_traitsIcEE5beginEv", gotBegin),
         ("_ZNKSt17basic_string_viewIcSt11char_traitsIcEE3endEv", gotEnd)] =>
    if gotSum != wantSum then
      throw (IO.userError "golden mismatch for view_sum entry")
    if gotBegin != wantBegin then
      throw (IO.userError "golden mismatch for begin leaf")
    if gotEnd != wantEnd then
      throw (IO.userError "golden mismatch for end leaf")
    IO.println "PASS pipeline view_sum (entry + begin + end, one entry fact)"
    pure 3
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectView (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-view: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-view: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-view: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-view {name} [{code}]"
    pure 1

/-- Call to an unknown view callee: generic call-shape rejection. -/
def advUnknownViewCallee : String :=
  "module {\n  cir.func @vcall(%arg0: !cir.ptr<" ++ viewRec ++ "> " ++ viewTriple ++ ") -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %r = cir.call @_ZNKSt17basic_string_viewIcSt11char_traitsIcEE5beginEvX(%arg0) : (!cir.ptr<" ++ viewRec ++ ">) -> !cir.ptr<!s8i>\n"
  ++ "    %v = cir.load %r : !cir.ptr<!s8i>, !s8i\n"
  ++ "    %w = cir.cast integral %v : !s8i -> !s32i\n"
  ++ "    cir.return %w : !s32i\n  }\n}"

/-- Two call sites into `begin`: the single-site pin rejects. -/
def advDoubleBegin : String :=
  "module {\n  cir.func @vbegin2(%arg0: !cir.ptr<" ++ viewRec ++ "> " ++ viewTriple ++ ") -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %a = cir.call @" ++ viewBeginEv ++ "(%arg0) : (!cir.ptr<" ++ viewRec ++ ">) -> !cir.ptr<!s8i>\n"
  ++ "    %b = cir.call @" ++ viewBeginEv ++ "(%arg0) : (!cir.ptr<" ++ viewRec ++ ">) -> !cir.ptr<!s8i>\n"
  ++ "    %z = cir.const #cir.int<0> : !s32i\n"
  ++ "    cir.return %z : !s32i\n  }\n}"

/-- One caller with two `end` calls: the (single-site `begin` +
    single-site `end`) entry arity pin rejects. -/
def advDoubleEnd : String :=
  "module {\n  cir.func @vend2(%arg0: !cir.ptr<" ++ viewRec ++ "> " ++ viewTriple ++ ") -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %a = cir.call @" ++ viewEndEv ++ "(%arg0) : (!cir.ptr<" ++ viewRec ++ ">) -> !cir.ptr<!s8i>\n"
  ++ "    %b = cir.call @" ++ viewEndEv ++ "(%arg0) : (!cir.ptr<" ++ viewRec ++ ">) -> !cir.ptr<!s8i>\n"
  ++ "    %z = cir.const #cir.int<0> : !s32i\n"
  ++ "    cir.return %z : !s32i\n  }\n}"

/-- A `begin`-shaped body with a stride: the no-stride pin rejects
    (one `get_member` but a `ptr_stride` the `begin` shape
    forbids). -/
def advBeginStride : String :=
  "module {\n  cir.func @vstride(%arg0: !cir.ptr<" ++ viewRec ++ "> " ++ viewTriple ++ ") -> !cir.ptr<!s8i> attributes {\"nothrow\"} {\n"
  ++ "    %g = cir.get_member %arg0[1] {name = \"_M_str\"} : !cir.ptr<" ++ viewRec ++ "> -> !cir.ptr<!cir.ptr<!s8i>>\n"
  ++ "    %b = cir.load %g : !cir.ptr<!cir.ptr<!s8i>>, !cir.ptr<!s8i>\n"
  ++ "    %o = cir.const #cir.int<1> : !u64i\n"
  ++ "    %s = cir.ptr_stride %b, %o : (!cir.ptr<!s8i>, !u64i) -> !cir.ptr<!s8i>\n"
  ++ "    cir.return %s : !cir.ptr<!s8i>\n  }\n}"

/-- Entry-shaped loop over `s8i` cells with NO sext cast: the
    small-width pin rejects (8-bit integers never model
    silently). -/
def advMissingSext : String :=
  "module {\n  cir.func @vnosext(%arg0: " ++ viewRec ++ ") -> !s32i attributes {\"nothrow\"} {\n"
  ++ "    %t = cir.alloca \"t\" : !cir.ptr<!s32i>\n"
  ++ "    %z = cir.const #cir.int<0> : !s32i\n"
  ++ "    cir.store %z, %t : !s32i, !cir.ptr<!s32i>\n"
  ++ "    %p = cir.alloca \"p\" : !cir.ptr<!cir.ptr<!s8i>>\n"
  ++ "    %l = cir.load %p : !cir.ptr<!cir.ptr<!s8i>>, !cir.ptr<!s8i>\n"
  ++ "    %v = cir.load %l : !cir.ptr<!s8i>, !s8i\n"
  ++ "    %w = cir.load %t : !cir.ptr<!s32i>, !s32i\n"
  ++ "    cir.return %w : !s32i\n  }\n}"

/-- Bare view pointer without the attr triple: the alias discipline
    rejects before shapes are even consulted. -/
def advBareViewPtr : String :=
  "module {\n  cir.func @vbare(%arg0: !cir.ptr<" ++ viewRec ++ "> {llvm.noundef}) -> !cir.ptr<!s8i> attributes {\"nothrow\"} {\n"
  ++ "    %r = cir.call @" ++ viewBeginEv ++ "(%arg0) : (!cir.ptr<" ++ viewRec ++ ">) -> !cir.ptr<!s8i>\n"
  ++ "    cir.return %r : !cir.ptr<!s8i>\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkViewPipeline
  passed := passed + c0
  let r1 ← checkRejectView "vcall" advUnknownViewCallee .unknown
    "out-of-subset" "outside the admitted call shapes"
  passed := passed + r1
  let r2 ← checkRejectView "vbegin2" advDoubleBegin .unknown
    "out-of-subset" "calls a known `std::string_view` leaf"
  passed := passed + r2
  let r3 ← checkRejectView "vend2" advDoubleEnd .unknown
    "out-of-subset" "calls a known `std::string_view` leaf"
  passed := passed + r3
  let r4 ← checkRejectView "vstride" advBeginStride .unknown
    "escape-reject" "borrow-return"
  passed := passed + r4
  let r5 ← checkRejectView "vnosext" advMissingSext .unknown
    "out-of-subset" "uses 8/16-bit integers"
  passed := passed + r5
  let r6 ← checkRejectView "vbare" advBareViewPtr .unknown
    "alias-reject" "single-reference triple"
  passed := passed + r6
  IO.println s!"GOLDENVIEW-OK passed={passed}"

end GoldenView
