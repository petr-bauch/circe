-- M3b verdict-cache agreement check (C only).
--
-- Run from the repo root: `lake env lean --run tests/lean/DerivedNoalias.lean`
-- For every definition in each C `tests/cir/*.cir`: `derivedNoalias` must
-- be `true` (the M3b fragment covers all admitted C shapes), and whenever
-- live pointer params exist the checked-in `tests/oracle/verdicts.txt`
-- verdict must confirm them (`noalias`: cache matches derivation).
-- For every definition in each C++ `tests/cir/*.cir`: `derivedNoalias`
-- must be `false` (by design: text-level derivation is C-only; C++
-- uniqueness is the attr triple in CIR text, and the transfer side is
-- the value-level `oracleNoalias` witnesses in `Circe.Derived`, proved
-- against `memEval` in `Circe.Transfer` — M3d). Oracle facts are not
-- required there yet. `validate` behavior is unchanged; this is a
-- parallel assert.
import Circe.Validator

def checkCFile (verdicts : List OracleFact) (cir : String) : IO Nat := do
  let text ← IO.FS.readFile cir
  let raw ← match parseModule text with
    | none => throw (IO.userError s!"derived-check: parse failed for {cir}")
    | some r => pure r
  if raw.funcs.isEmpty then
    throw (IO.userError s!"derived-check: no definitions in {cir}")
  let mut n := 0
  for func in raw.funcs do
    if derivedNoalias func != true then
      throw (IO.userError
        s!"derived-check: {cir}:{func.name}: expected derivedNoalias = true")
    match lookupOracle verdicts func.name with
    | none =>
      throw (IO.userError s!"derived-check: no oracle fact for {func.name}")
    | some o =>
      if !(oracleParams func).isEmpty then
        match o.verdict with
        | .noalias => pure ()
        | _ =>
          throw (IO.userError
            s!"derived-check: {cir}:{func.name}: live pointer params with derived evidence but cache verdict is not `noalias`")
      if !(oracleParams func).isEmpty && !verdictAdmits o.verdict then
        throw (IO.userError
          s!"derived-check: {cir}:{func.name}: verdict does not admit")
    IO.println s!"PASS derived {func.name} (C)"
    n := n + 1
  pure n

def checkCppFile (cir : String) : IO Nat := do
  let text ← IO.FS.readFile cir
  let raw ← match parseModule text with
    | none => throw (IO.userError s!"derived-check: parse failed for {cir}")
    | some r => pure r
  if raw.funcs.isEmpty then
    throw (IO.userError s!"derived-check: no definitions in {cir}")
  let mut n := 0
  for func in raw.funcs do
    if derivedNoalias func != false then
      throw (IO.userError
        s!"derived-check: {cir}:{func.name}: expected derivedNoalias = false (C++ out of derived scope by design)")
    IO.println s!"PASS derived {func.name} (C++ out of scope)"
    n := n + 1
  pure n

def threePtrRaw : RawFunc :=
  { name := "three", params :=
    [{ name := "a", ctype := "!cir.ptr<!s32i>", noalias := true, singleRef := false },
     { name := "b", ctype := "!cir.ptr<!s32i>", noalias := true, singleRef := false },
     { name := "c", ctype := "!cir.ptr<!s32i>", noalias := true, singleRef := false }],
    ret := "!s32i",
    text := "cir.func @three(%arg0: !cir.ptr<!s32i> {llvm.noalias}) { cir.return }" }

def cppRefRaw : RawFunc :=
  { name := "_ZNK5Point3sumEv", params :=
    [{ name := "this", ctype := "!cir.ptr<!rec_Point>", noalias := false, singleRef := true }],
    ret := "!s32i",
    text := "cir.func @_ZNK5Point3sumEv(%arg0: !cir.ptr<!rec_Point> {llvm.nonnull, llvm.dereferenceable, llvm.noundef}) { cir.return }" }

def main : IO Unit := do
  let verdictText ← IO.FS.readFile "tests/oracle/verdicts.txt"
  let verdicts := parseOracleFacts verdictText
  let mut passed := 0
  for cir in ["tests/cir/add.cir", "tests/cir/incr_ptr.cir",
      "tests/cir/choose_ptr.cir", "tests/cir/sum_array.cir",
      "tests/cir/struct_by_value.cir", "tests/cir/vec_alloc.cir",
      "tests/cir/vec_alloc_leak.cir", "tests/cir/vec_alloc_u64.cir",
      "tests/cir/vec_copy_sum.cir", "tests/cir/vec_realloc.cir",
      "tests/cir/add_caller.cir", "tests/cir/sum_caller.cir",
      "tests/cir/nested_sum.cir", "tests/cir/skip_sum.cir",
      "tests/cir/find_eq.cir", "tests/cir/cls.cir",
      "tests/cir/add64.cir", "tests/cir/addu64.cir"] do
    let c ← checkCFile verdicts cir
    passed := passed + c
  for cir in ["tests/cir/point_sum_ref.cir", "tests/cir/acc_two.cir",
      "tests/cir/box_through.cir"] do
    let c ← checkCppFile cir
    passed := passed + c
  if derivedNoalias threePtrRaw != false then
    throw (IO.userError "derived-check: 3-pointer shape must not derive")
  IO.println "PASS derived three-ptr rejection"
  passed := passed + 1
  if derivedNoalias cppRefRaw != false then
    throw (IO.userError "derived-check: C++ single-ref must not derive (attr triple is not text-level noalias)")
  IO.println "PASS derived single-ref exclusion"
  passed := passed + 1
  IO.println s!"DERIVED-OK passed={passed}"
