-- Scope evidence report (L1 birth-depths + L2 live ranges, extract-only).
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

/-- One L2 expectation: function name, locals as
    `(name, first-use line, last-use line)` in source order
    (1-based lines within the function text; `(0, 0)` = unobserved). -/
abbrev ScopeUseWant := String × List (String × Nat × Nat)

def checkScopeUses (cir : String) (wants : List ScopeUseWant) : IO Nat := do
  let text ← IO.FS.readFile cir
  let raw ← match parseModule text with
    | none => throw (IO.userError s!"scope-report: parse failed for {cir}")
    | some r => pure r
  let mut n := 0
  for (name, locs) in wants do
    match raw.funcs.find? (fun f => f.name == name) with
    | none =>
      throw (IO.userError s!"scope-report: {cir}: no definition {name}")
    | some func =>
      let s := extractScopes func.text
      if s.balanced != true then
        throw (IO.userError s!"scope-report: {cir}:{name}: expected balanced")
      let got := s.locals.map (fun d => (d.name, d.firstUse, d.lastUse))
      if got != locs then
        throw (IO.userError s!"scope-report: {cir}:{name}: uses {got} != {locs}")
      IO.println s!"PASS scope-uses {name} ({locs.length} locals)"
      n := n + 1
  pure n

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

/-- One F0 expectation: slot name, kind (`"ref"`/`"val"`), direct
    and ultimate roots in display form (`showRoot`). -/
abbrev SlotRootWant := String × String × String × String

def checkSlotRoots (cir func : String) (wants : List SlotRootWant) :
    IO Nat := do
  let text ← IO.FS.readFile cir
  let raw ← match parseModule text with
    | none => throw (IO.userError s!"scope-report: parse failed for {cir}")
    | some r => pure r
  match raw.funcs.find? (fun f => f.name == func) with
  | none =>
    throw (IO.userError s!"scope-report: {cir}: no definition {func}")
  | some fn =>
    let lines := fn.text.splitOn "\n"
    let kinds := slotKinds lines
    let roots := contentRoots lines
    let mut n := 0
    for (nm, k, d, u) in wants do
      match kinds.find? (fun x => x.1 == nm),
          roots.find? (fun x => x.1 == nm) with
      | some (_, kk), some (_, dd, uu) =>
        let kd := match kk with | .Ref => "ref" | .Val => "val"
        if kd != k || showRoot dd != d || showRoot uu != u then
          throw (IO.userError s!"scope-report: {cir}:{func}:{nm}: roots ({kd}, {showRoot dd}, {showRoot uu}) != ({k}, {d}, {u})")
        IO.println s!"PASS slot-roots {func}:{nm}"
        n := n + 1
      | _, _ =>
        throw (IO.userError s!"scope-report: {cir}:{func}: no slot {nm}")
    pure n

def checkUnique (cir func : String) : IO Nat := do
  let text ← IO.FS.readFile cir
  let raw ← match parseModule text with
    | none => throw (IO.userError s!"scope-report: parse failed for {cir}")
    | some r => pure r
  match raw.funcs.find? (fun f => f.name == func) with
  | none =>
    throw (IO.userError s!"scope-report: {cir}: no definition {func}")
  | some fn =>
    if uniqueCopies (fn.text.splitOn "\n") != true then
      throw (IO.userError s!"scope-report: {cir}:{func}: ambiguous copies")
    IO.println s!"PASS slot-unique {func}"
    pure 1

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
  -- L-track first consumer (report-only): the two alias residues pin
  -- identically — birth-depth evidence cannot separate sequential
  -- reborrows (`x`/`r`/`s` all depth 0, no `cir.scope` around `r`/`s`)
  -- from conditionally-live writers (`p`/`q`/`c` all depth 0). So no
  -- admission consumer is possible yet: reborrow admission needs
  -- last-use/death facts L1 does not extract (L2 work, see
  -- `docs/ROADMAP.md`); `alias_cond` framing needs Iris (see the Iris
  -- spike report). These rows pin the insufficiency.
  let c ← checkScopeFile "tests/cir/alias_reborrow.cir"
    [("_Z14alias_reborrowRi", [("x", 0), ("r", 0), ("s", 0)], 0)]
  passed := passed + c
  let c ← checkScopeFile "tests/cir/alias_cond.cir"
    [("_Z10alias_condRiS_b", [("p", 0), ("q", 0), ("c", 0)], 0)]
  passed := passed + c
  -- Two-reader admission: flat two-reader loop (both arrays depth 0).
  let c ← checkScopeFile "tests/cir/sum_two.cir"
    [("sum_two", [("a", 0), ("b", 0), ("n", 0), ("__retval", 0), ("s", 0), ("i", 1)], 1)]
  passed := passed + c
  -- Writer-pair admission: flat two-writer body (both cells depth 0).
  let c ← checkScopeFile "tests/cir/wr_pair.cir"
    [("wr_pair", [("p", 0), ("q", 0)], 0)]
  passed := passed + c
  -- Checked read: entry + composers are flat (all depth 0; the
  -- `cir.scope` region in `_M_range_check` nests no allocas).
  let c ← checkScopeFile "tests/cir/vec_at_one.cir"
    [("_Z10vec_at_oneRKSt6vectorIiSaIiEE", [("v", 0), ("__retval", 0)], 0),
     ("_ZNKSt6vectorIiSaIiEE2atEm", [("this", 0), ("__n", 0), ("__retval", 0)], 0),
     ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", [("this", 0), ("__n", 0)], 0),
     ("_ZNKSt6vectorIiSaIiEEixEm", [("this", 0), ("__n", 0), ("__retval", 0)], 0),
     ("_ZNKSt6vectorIiSaIiEE4sizeEv", [("this", 0), ("__retval", 0)], 0)]
  passed := passed + c
  -- Checked sum: the loop index lives in the `cir.scope` region
  -- (depth 1, the `sum_two` precedent); everything else is flat.
  let c ← checkScopeFile "tests/cir/vec_at_sum.cir"
    [("_Z10vec_at_sumRKSt6vectorIiSaIiEE", [("v", 0), ("__retval", 0), ("s", 0), ("i", 1)], 1),
     ("_ZNKSt6vectorIiSaIiEE4sizeEv", [("this", 0), ("__retval", 0)], 0),
     ("_ZNKSt6vectorIiSaIiEE2atEm", [("this", 0), ("__n", 0), ("__retval", 0)], 0),
     ("_ZNKSt6vectorIiSaIiEE14_M_range_checkEm", [("this", 0), ("__n", 0)], 0),
     ("_ZNKSt6vectorIiSaIiEEixEm", [("this", 0), ("__n", 0), ("__retval", 0)], 0)]
  passed := passed + c
  -- L2 live ranges: sequential reborrows separate (`r` last-use
  -- line 12 precedes `s` first-use line 14 — the admission-enabling
  -- fact L1 birth-depths could not show; the load-copy closure
  -- carries `r` through its final store).
  let c ← checkScopeUses "tests/cir/alias_reborrow.cir"
    [("_Z14alias_reborrowRi",
      [("x", 5, 14), ("r", 7, 12), ("s", 14, 19)])]
  passed := passed + c
  -- L2 live ranges: the conditionally-live writer overlaps (`q`
  -- spans lines 6-22 across `p` and `c` — framing stays Iris).
  let c ← checkScopeUses "tests/cir/alias_cond.cir"
    [("_Z10alias_condRiS_b",
      [("p", 5, 15), ("q", 6, 22), ("c", 7, 10)])]
  passed := passed + c
  -- L2 live ranges: loop regression (region-aware: per-region SSA
  -- numbers resolve inward-outward, so the `cond`-region `%13`
  -- (`n`-copy) never leaks into `a`/`n` ranges).
  let c ← checkScopeUses "tests/cir/sum_two.cir"
    [("sum_two",
      [("a", 7, 29), ("b", 8, 33), ("n", 9, 21), ("__retval", 49, 51),
       ("s", 12, 49), ("i", 17, 44)])]
  passed := passed + c
  -- F0 content roots: sequential reborrows share one address (`r`/`s`
  -- chain to `x`, ultimately `param0`) — the WHERE to L2's WHEN, and
  -- the F1 sequencing license in waiting.
  let c ← checkSlotRoots "tests/cir/alias_reborrow.cir" "_Z14alias_reborrowRi"
    [("x", "ref", "param0", "param0"), ("r", "ref", "slot:x", "param0"),
     ("s", "ref", "slot:x", "param0")]
  passed := passed + c
  let c ← checkUnique "tests/cir/alias_reborrow.cir" "_Z14alias_reborrowRi"
  passed := passed + c
  -- F0 content roots: conditionally-live writers name DIFFERENT
  -- addresses (`p` → `param0`, `q` → `param1`) — caller-dependent
  -- footprints, the framing gap, made textual.
  let c ← checkSlotRoots "tests/cir/alias_cond.cir" "_Z10alias_condRiS_b"
    [("p", "ref", "param0", "param0"), ("q", "ref", "param1", "param1"),
     ("c", "val", "param2", "param2")]
  passed := passed + c
  let c ← checkUnique "tests/cir/alias_cond.cir" "_Z10alias_condRiS_b"
  passed := passed + c
  -- F0 control: two readers resolve to different params (attribute
  -- disjointness territory); value slots claim no address (`?`).
  let c ← checkSlotRoots "tests/cir/sum_two.cir" "sum_two"
    [("a", "ref", "param0", "param0"), ("b", "ref", "param1", "param1"),
     ("n", "val", "param2", "param2"), ("__retval", "val", "?", "?"),
     ("s", "val", "?", "?"), ("i", "val", "?", "?")]
  passed := passed + c
  let c ← checkUnique "tests/cir/sum_two.cir" "sum_two"
  passed := passed + c
  -- L2 live ranges: the two writers overlap (`q` spans lines 5–17
  -- across `p` — no sequencing license, unlike F1; disjointness
  -- comes from the `noalias` verdict instead).
  let c ← checkScopeUses "tests/cir/wr_pair.cir"
    [("wr_pair", [("p", 4, 11), ("q", 5, 17)])]
  passed := passed + c
  -- F0 content roots: the writers name different addresses (`p` →
  -- `param0`, `q` → `param1`) — the dataflow pin's address half,
  -- made textual.
  let c ← checkSlotRoots "tests/cir/wr_pair.cir" "wr_pair"
    [("p", "ref", "param0", "param0"), ("q", "ref", "param1", "param1")]
  passed := passed + c
  let c ← checkUnique "tests/cir/wr_pair.cir" "wr_pair"
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
