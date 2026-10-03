-- Scope evidence report (L1, extract-only).
--
-- Run from the repo root: `lake env lean --run tests/lean/ScopeReport.lean`
-- For every definition in each corpus `.cir` file, `extractScopes` must be
-- balanced with exactly the expected locals (`name@depth`, source order)
-- and maximum depth. Loop indices sit one `cir.for` region deep (`i@1`);
-- the nested-loop inner index sits four opens deep (`j@4`: func > scope >
-- for-body > scope > scope — verified against `nested_sum.cir`, and the
-- reason the inner index is re-initialized per outer iteration).
-- Nothing here feeds `validate`: this is evidence tracking with golden
-- pins, not admission. Unit negatives pin the loudness flag
-- (`balanced = false` on truncated/malformed input).
import Circe.Scope
import Circe.Validator

namespace ScopeReport

/-- One expectation: function name, locals as `(name, depth)` in source
    order, maximum depth. -/
abbrev ScopeWant := String × List (String × Nat) × Nat

def checkScopeFile (cir : String) (wants : List ScopeWant) : IO Nat := do
  let text ← IO.FS.readFile cir
  let raw ← match parseModule text with
    | none => throw (IO.userError s!"scope-report: parse failed for {cir}")
    | some r => pure r
  let mut n := 0
  for (name, locs, max) in wants do
    match raw.funcs.find? (fun f => f.name == name) with
    | none =>
      throw (IO.userError s!"scope-report: {cir}: no definition {name}")
    | some func =>
      let s := extractScopes func.text
      if s.balanced != true then
        throw (IO.userError s!"scope-report: {cir}:{name}: expected balanced")
      let got := s.locals.map (fun d => (d.name, d.depth))
      if got != locs then
        throw (IO.userError s!"scope-report: {cir}:{name}: locals {got} != {locs}")
      if s.maxDepth != max then
        throw (IO.userError s!"scope-report: {cir}:{name}: max {s.maxDepth} != {max}")
      IO.println s!"PASS scope {name} ({locs.length} locals, max {max})"
      n := n + 1
  pure n

def main : IO Unit := do
  let mut passed := 0
  let c ← checkScopeFile "tests/cir/add.cir"
    [("add", [("a", 0), ("b", 0), ("__retval", 0)], 0)]
  passed := passed + c
  let c ← checkScopeFile "tests/cir/incr_ptr.cir"
    [("incr", [("p", 0)], 0)]
  passed := passed + c
  let c ← checkScopeFile "tests/cir/choose_ptr.cir"
    [("choose", [("b", 0), ("x", 0), ("y", 0), ("__retval", 0)], 0)]
  passed := passed + c
  let c ← checkScopeFile "tests/cir/sum_array.cir"
    [("sum_array", [("a", 0), ("n", 0), ("__retval", 0), ("s", 0), ("i", 1)], 1)]
  passed := passed + c
  let c ← checkScopeFile "tests/cir/struct_by_value.cir"
    [("translate", [("p", 0), ("dx", 0), ("dy", 0), ("__retval", 0)], 0)]
  passed := passed + c
  let c ← checkScopeFile "tests/cir/vec_alloc.cir"
    [("vec_alloc", [("n", 0), ("__retval", 0), ("v", 0), ("s", 0), ("i", 1), ("j", 1)], 1)]
  passed := passed + c
  let c ← checkScopeFile "tests/cir/vec_alloc_leak.cir"
    [("vec_alloc_leak", [("n", 0), ("__retval", 0), ("v", 0), ("s", 0), ("i", 1), ("j", 1)], 1)]
  passed := passed + c
  let c ← checkScopeFile "tests/cir/vec_alloc_u64.cir"
    [("vec_alloc_u64", [("n", 0), ("__retval", 0), ("v", 0), ("s", 0), ("i", 1), ("j", 1)], 1)]
  passed := passed + c
  let c ← checkScopeFile "tests/cir/vec_copy_sum.cir"
    [("vec_copy_sum", [("n", 0), ("__retval", 0), ("a", 0), ("b", 0), ("s", 0), ("i", 1), ("j", 1), ("k", 1)], 1)]
  passed := passed + c
  let c ← checkScopeFile "tests/cir/vec_realloc.cir"
    [("vec_realloc", [("n", 0), ("__retval", 0), ("v", 0), ("m", 0), ("s", 0), ("i", 1), ("j", 1), ("k", 1)], 1)]
  passed := passed + c
  let c ← checkScopeFile "tests/cir/add_caller.cir"
    [("add_caller", [("x", 0), ("y", 0), ("z", 0), ("__retval", 0), ("t", 0)], 0)]
  passed := passed + c
  let c ← checkScopeFile "tests/cir/sum_caller.cir"
    [("sum_caller", [("a", 0), ("n", 0), ("__retval", 0)], 0)]
  passed := passed + c
  let c ← checkScopeFile "tests/cir/nested_sum.cir"
    [("nested_sum", [("n", 0), ("m", 0), ("__retval", 0), ("s", 0), ("i", 1), ("j", 4)], 4)]
  passed := passed + c
  let c ← checkScopeFile "tests/cir/skip_sum.cir"
    [("skip_sum", [("n", 0), ("__retval", 0), ("s", 0), ("i", 1)], 1)]
  passed := passed + c
  let c ← checkScopeFile "tests/cir/find_eq.cir"
    [("find_eq", [("a", 0), ("n", 0), ("k", 0), ("__retval", 0), ("i", 1)], 1)]
  passed := passed + c
  let c ← checkScopeFile "tests/cir/cls.cir"
    [("cls", [("x", 0), ("__retval", 0)], 0)]
  passed := passed + c
  let c ← checkScopeFile "tests/cir/add64.cir"
    [("add64", [("a", 0), ("b", 0), ("__retval", 0)], 0)]
  passed := passed + c
  let c ← checkScopeFile "tests/cir/addu64.cir"
    [("addu64", [("a", 0), ("b", 0), ("__retval", 0)], 0)]
  passed := passed + c
  let c ← checkScopeFile "tests/cir/sum_norestrict.cir"
    [("sum_norestrict", [("a", 0), ("n", 0), ("__retval", 0), ("s", 0), ("i", 1)], 1)]
  passed := passed + c
  let c ← checkScopeFile "tests/cir/point_sum_ref.cir"
    [("_Z13point_sum_refRK5Point", [("p", 0), ("__retval", 0)], 0),
     ("_ZNK5Point3sumEv", [("this", 0), ("__retval", 0)], 0)]
  passed := passed + c
  let c ← checkScopeFile "tests/cir/acc_two.cir"
    [("_Z7acc_twoii", [("a", 0), ("b", 0), ("__retval", 0), ("acc", 0)], 0),
     ("_ZN3AccC2Ev", [("this", 0)], 0),
     ("_ZN3Acc3addEi", [("this", 0), ("v", 0)], 0),
     ("_ZNK3Acc3getEv", [("this", 0), ("__retval", 0)], 0),
     ("_ZN3AccD2Ev", [("this", 0)], 0)]
  passed := passed + c
  let c ← checkScopeFile "tests/cir/box_through.cir"
    [("_Z11box_throughi", [("x", 0), ("__retval", 0), ("p", 0), ("r", 0)], 0)]
  passed := passed + c
  -- Unit negatives: truncated input never closes, malformed `cir.alloca`
  -- lines never parse — both report `balanced = false`, never silent.
  if (extractScopes "cir.func @t { cir.alloca \"a\"").balanced != false then
    throw (IO.userError "scope-report: truncated input must not balance")
  IO.println "PASS scope truncated-input loudness"
  passed := passed + 1
  if (extractScopes "cir.func @t { cir.alloca garbage }").balanced != false then
    throw (IO.userError "scope-report: malformed alloca must not balance")
  IO.println "PASS scope malformed-alloca loudness"
  passed := passed + 1
  IO.println s!"SCOPEREPORT-OK passed={passed}"

end ScopeReport
