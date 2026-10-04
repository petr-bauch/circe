-- Golden test for N4d-ii: `std::optional<int32_t>` guarded-deref
-- pipeline + rejection suite.
--
-- Run from the repo root: `lake env lean --run tests/lean/GoldenOptional.lean`
-- 1. Corpus pipeline: `tests/cir/opt_deref.cir` (real CIRGen output
--    with `-fno-exceptions`: the guarded entry + `has_value` +
--    `operator*` + `_M_is_engaged` + impl `_M_get` (with the dead
--    disabled-`__glibcxx_assert` skeleton) + payload `_M_get`)
--    validates via `runModulePipeline` with NO oracle facts
--    (uniqueness comes from the `nonnull + dereferenceable + noundef`
--    attr triple, the M2a single-reference precedent) and emits
--    byte-identical text to
--    `tests/golden/{OptDeref,OptHasValue,OptDerefOp,OptHas,OptImplGet,OptGet}.lean`.
-- 2. Rejection suite: call to an unknown optional callee (generic),
--    double call into payload `_M_get` (site-count pin), a
--    live-assert impl variant (dead-skeleton pin), `has_value` at the
--    wrong arity, bare optional pointer without the attr triple
--    (alias discipline) — the first is generic, the rest hit the
--    dedicated optional wrong-shape rejection (or `alias-reject`).
-- 3. Non-goals: `optional::value` (throw path) stays deferred — the
--    `otrap` pin in `GoldenArray` still covers it; guarded
--    `operator*` is the only admitted deref.
--    Mismatch policy: any in-subset divergence is P0; out-of-subset
--    must reject loudly.
import Circe.Validator

namespace GoldenOptional

def optTriple8 : String :=
  "{llvm.align = 4 : i64, llvm.dereferenceable = 8 : i64, llvm.nonnull, llvm.noundef}"

def optTriple1 : String :=
  "{llvm.align = 1 : i64, llvm.dereferenceable = 1 : i64, llvm.nonnull, llvm.noundef}"

def checkOptionalPipeline : IO Nat := do
  let text ← IO.FS.readFile "tests/cir/opt_deref.cir"
  let wantDeref ← IO.FS.readFile "tests/golden/OptDeref.lean"
  let wantHasValue ← IO.FS.readFile "tests/golden/OptHasValue.lean"
  let wantDerefOp ← IO.FS.readFile "tests/golden/OptDerefOp.lean"
  let wantHas ← IO.FS.readFile "tests/golden/OptHas.lean"
  let wantImplGet ← IO.FS.readFile "tests/golden/OptImplGet.lean"
  let wantGet ← IO.FS.readFile "tests/golden/OptGet.lean"
  match runModulePipeline text [] with
  | .error msg =>
    throw (IO.userError s!"pipeline unexpectedly rejected opt_deref: {msg}")
  | .ok [("_Z9opt_derefRKSt8optionalIiE", gotDeref),
         ("_ZNKSt8optionalIiE9has_valueEv", gotHasValue),
         ("_ZNKRSt8optionalIiEdeEv", gotDerefOp),
         ("_ZNKSt19_Optional_base_implIiSt14_Optional_baseIiLb1ELb1EEE13_M_is_engagedEv", gotHas),
         ("_ZNKSt19_Optional_base_implIiSt14_Optional_baseIiLb1ELb1EEE6_M_getEv", gotImplGet),
         ("_ZNKSt22_Optional_payload_baseIiE6_M_getEv", gotGet)] =>
    if gotDeref != wantDeref then
      throw (IO.userError "golden mismatch for opt_deref entry")
    if gotHasValue != wantHasValue then
      throw (IO.userError "golden mismatch for has_value entry")
    if gotDerefOp != wantDerefOp then
      throw (IO.userError "golden mismatch for operator* leaf")
    if gotHas != wantHas then
      throw (IO.userError "golden mismatch for _M_is_engaged leaf")
    if gotImplGet != wantImplGet then
      throw (IO.userError "golden mismatch for impl _M_get entry")
    if gotGet != wantGet then
      throw (IO.userError "golden mismatch for payload _M_get leaf")
    IO.println "PASS pipeline opt_deref (entry + 5 callees, no oracle facts)"
    pure 6
  | .ok pairs =>
    throw (IO.userError s!"pipeline unexpected module shape: {pairs.map (·.1)}")

/-- Adversarial case: inline CIR must reject with `code` in the message
    plus `substr`. -/
def checkRejectOptional (name text : String) (verdict : Verdict)
    (code substr : String) : IO Nat := do
  let oracle : OracleFact := ⟨name, verdict⟩
  match runPipeline text oracle with
  | .ok got =>
    throw (IO.userError s!"reject-optional: {name} unexpectedly accepted:\n{got}")
  | .error msg =>
    if !containsSubstr msg code then
      throw (IO.userError s!"reject-optional: {name}: expected code {code} in: {msg}")
    if !containsSubstr msg substr then
      throw (IO.userError s!"reject-optional: {name}: expected {substr} in: {msg}")
    IO.println s!"PASS reject-optional {name} [{code}]"
    pure 1

/-- Call to an unknown optional callee: generic call-shape rejection. -/
def advUnknownOptCallee : String :=
  "module {\n  cir.func @ocall(%arg0: !cir.ptr<!rec_std3A3Aoptional3Cint3E> " ++ optTriple8 ++ ") -> !cir.bool attributes {\"nothrow\"} {\n"
  ++ "    %r = cir.call @_ZNKSt8optionalIiE9has_valueEvX(%arg0) : (!cir.ptr<!rec_std3A3Aoptional3Cint3E>) -> !cir.bool\n    cir.return %r : !cir.bool\n  }\n}"

/-- Two call sites into payload `_M_get`: the single-site pin rejects. -/
def advDoubleGet : String :=
  "module {\n  cir.func @odouble(%arg0: !cir.ptr<!rec_std3A3A_Optional_payload_base3Cint3E> " ++ optTriple8 ++ ") -> !cir.ptr<!s32i> attributes {\"nothrow\"} {\n"
  ++ "    %a = cir.call @_ZNKSt22_Optional_payload_baseIiE6_M_getEv(%arg0) : (!cir.ptr<!rec_std3A3A_Optional_payload_base3Cint3E>) -> !cir.ptr<!s32i>\n"
  ++ "    %b = cir.call @_ZNKSt22_Optional_payload_baseIiE6_M_getEv(%arg0) : (!cir.ptr<!rec_std3A3A_Optional_payload_base3Cint3E>) -> !cir.ptr<!s32i>\n"
  ++ "    %v = cir.load %a : !cir.ptr<!s32i>, !s32i\n    %w = cir.load %b : !cir.ptr<!s32i>, !s32i\n    %s = cir.add nsw %v, %w : !s32i\n    cir.return %s : !s32i\n  }\n}"

/-- Live-assert impl variant: the ternary condition is a live `not`
    over a loaded bit instead of the `false` const (two `#false`
    consts, not three) — the shape a `-D_GLIBCXX_ASSERTIONS` build
    would approach. The dead-skeleton pin rejects it. -/
def advLiveAssert : String :=
  "module {\n  cir.func @olive(%arg0: !cir.ptr<!rec_std3A3A_Optional_base_impl3Cint2C_std3A3A_Optional_base3Cint2C_true2C_true3E3E> " ++ optTriple1 ++ ") -> !cir.ptr<!s32i> attributes {\"nothrow\"} {\n"
  ++ "    %e = cir.call @_ZNKSt19_Optional_base_implIiSt14_Optional_baseIiLb1ELb1EEE13_M_is_engagedEv(%arg0) : (!cir.ptr<!rec_std3A3A_Optional_base_impl3Cint2C_std3A3A_Optional_base3Cint2C_true2C_true3E3E>) -> !cir.bool\n"
  ++ "    %n = cir.not %e : !cir.bool\n"
  ++ "    %t = cir.ternary(%n, true {\n"
  ++ "      %f = cir.const #false\n      cir.yield %f : !cir.bool\n    }, false {\n"
  ++ "      %g = cir.const #false\n      cir.yield %g : !cir.bool\n    }) : (!cir.bool) -> !cir.bool\n"
  ++ "    cir.if %t {\n      cir.unreachable\n    }\n"
  ++ "    %p = cir.call @_ZNKSt22_Optional_payload_baseIiE6_M_getEv(%arg0) : (!cir.ptr<!rec_std3A3A_Optional_base_impl3Cint2C_std3A3A_Optional_base3Cint2C_true2C_true3E3E>) -> !cir.ptr<!s32i>\n"
  ++ "    cir.return %p : !cir.ptr<!s32i>\n  }\n}"

/-- `has_value` at the wrong arity: no admitted shape takes two
    optionals. -/
def advHasValueWrongArity : String :=
  "module {\n  cir.func @oarod(%arg0: !cir.ptr<!rec_std3A3Aoptional3Cint3E> " ++ optTriple8 ++ ", %arg1: !cir.ptr<!rec_std3A3Aoptional3Cint3E> " ++ optTriple8 ++ ") -> !cir.bool attributes {\"nothrow\"} {\n"
  ++ "    %r = cir.call @_ZNKSt8optionalIiE9has_valueEv(%arg0) : (!cir.ptr<!rec_std3A3Aoptional3Cint3E>) -> !cir.bool\n    cir.return %r : !cir.bool\n  }\n}"

/-- Bare optional pointer without the attr triple: the alias
    discipline rejects before shapes are even consulted. -/
def advBareOptPtr : String :=
  "module {\n  cir.func @obare(%arg0: !cir.ptr<!rec_std3A3Aoptional3Cint3E> {llvm.noundef}) -> !cir.bool attributes {\"nothrow\"} {\n"
  ++ "    %r = cir.call @_ZNKSt8optionalIiE9has_valueEv(%arg0) : (!cir.ptr<!rec_std3A3Aoptional3Cint3E>) -> !cir.bool\n    cir.return %r : !cir.bool\n  }\n}"

def main : IO Unit := do
  let mut passed := 0
  let c0 ← checkOptionalPipeline
  passed := passed + c0
  let r1 ← checkRejectOptional "ocall" advUnknownOptCallee .unknown
    "out-of-subset" "outside the admitted call shapes"
  passed := passed + r1
  let r2 ← checkRejectOptional "odouble" advDoubleGet .unknown
    "out-of-subset" "calls a known `std::optional` leaf"
  passed := passed + r2
  let r3 ← checkRejectOptional "olive" advLiveAssert .unknown
    "out-of-subset" "calls a known `std::optional` leaf"
  passed := passed + r3
  let r4 ← checkRejectOptional "oarod" advHasValueWrongArity .unknown
    "out-of-subset" "calls a known `std::optional` leaf"
  passed := passed + r4
  let r5 ← checkRejectOptional "obare" advBareOptPtr .unknown
    "alias-reject" "single-reference triple"
  passed := passed + r5
  IO.println s!"GOLDENOPTIONAL-OK passed={passed}"

end GoldenOptional
