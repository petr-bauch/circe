/-
Circe.LeafTactics — low-level proof tactics for program-table
dispatch and pure-`let_` steps (R1 refactor).

Placement is load-bearing: `find_leaf` needs `findFunc_hit`/`miss`
(`Circe.Eval.Stmt`) and `let_pure_step` needs
`memEvalStmtFuel_let_pure` (`Circe.Mem.Agree`), so this module sits
directly above both — low enough that `Circe.Emit.*` (which cannot
import `Circe.Tactics`: `Tactics` imports the `Emit` umbrella) and
`Circe.Transfer.*` can all use it with no cycle. `Circe.Tactics`
re-exports this module (via import), so `import Circe.Tactics`
users see these tactics too. `cir_fold_end` names no `Emit`
constants (both equations arrive as arguments), so it lives here
for the same reason.
-/
import Circe.Eval.Stmt
import Circe.Mem.Agree
import Lean

/-- Miss-chain driver: rewrite one non-matching head, recurse;
    when no head misses (target reached, or zero-miss goal), close
    by `findFunc_hit`. The 32 bound exceeds every program table. -/
partial def missLoop : Nat → Lean.Elab.Tactic.TacticM Unit
  | 0 => do Lean.Elab.Tactic.evalTactic (← `(tactic| exact findFunc_hit _ _))
  | n + 1 => do
    try
      Lean.Elab.Tactic.evalTactic (← `(tactic| rw [findFunc_miss _ _ _ (by decide)]))
      missLoop n
    catch _ =>
      Lean.Elab.Tactic.evalTactic (← `(tactic| exact findFunc_hit _ _))

/-- Leaf dispatch in a program list: unfold the program table, skip
    every non-matching head (`decide` on the name inequality), close
    by `findFunc_hit`. Covers the zero-miss case too. Usage:
    `have hfind := by find_leaf vecGrowProg`. (An `elab` loop rather
    than a macro: `repeat tac; ...` sequencing and `(config := ...)`
    do not parse inside `(tactic| ...)` quotations on this toolchain.)
    -/
elab "find_leaf" prog:ident : tactic => do
  Lean.Elab.Tactic.evalTactic (← `(tactic| unfold $prog))
  missLoop 32

/-- Pure-`let_` program step: the standard 8-underscore application
    with the three trivial side goals discharged by `simp`.
    Usage: `have hstep := by let_pure_step (hmem, heval)`.
    (Comma-delimited: two adjacent `term` arguments parse greedily
    as one application.) -/
macro "let_pure_step" "(" hM:term "," hE:term ")" : tactic =>
  `(tactic| exact memEvalStmtFuel_let_pure _ _ _ _ _ _ _ _
    (fun _ => by simp) (fun _ => by simp) (fun _ => by simp) $hM $hE)

/-- Fold-end script: unfold a suffix fold one step on the left
    (`conv => lhs` + the drop equation), then discharge the lookup
    with `hget`. The six in-repo sites (`spanFold_*`,
    `viewFold_*`, `stdVecFold_*` step/nil pairs) share this script
    verbatim. Usage: `cir_fold_end (spanFold_drop, hget)`.
    (An `elab` in two `evalTactic` steps so the `conv => ...` /
    `simp ...` boundary keeps its original parse — one quotation
    would risk `simp` binding inside the `conv` block. Reparse, not
    splice: `rw` / `simp` arg kinds reject spliced idents, so the
    exact surface strings elaborate at the use site instead —
    `cir_step` precedent in `Circe.Eval.Stmt`.) -/
elab "cir_fold_end" "(" dropEq:ident "," hget:ident ")" : tactic => do
  let env ← Lean.MonadEnv.getEnv
  let .ok rwStx := Lean.Parser.runParserCategory env `tactic
      ("conv => lhs; rw [" ++ dropEq.getId.toString ++ "]")
    | throwError "cir_fold_end: could not parse conv step"
  Lean.Elab.Tactic.evalTactic rwStx
  let .ok simpStx := Lean.Parser.runParserCategory env `tactic
      ("simp [" ++ hget.getId.toString ++ "]")
    | throwError "cir_fold_end: could not parse simp step"
  Lean.Elab.Tactic.evalTactic simpStx

/-- T2 fuel-split step (audit #5): the `fuel_step_down` prefix shared
    verbatim by the 10 value+mem loop sites (M2c/M3c/M4c). Emits the
    N5a-mandated `have hF'` side goal (`omega`) then the `obtain`
    split. `F`/`G` are idents (loop fuel, forward fuel); `M` is the
    measure term (`l.length - (i + 1)` shape, source text reused).
    Usage: `cir_fuel_step (F, G, l.length - (i + 1))`.
    (Reparse, not splice: introduced `hF'`/`G'`/`hG'` must be
    use-site accessible — `cir_fold_end` precedent above.) -/
elab "cir_fuel_step" "(" F:ident "," G:ident "," M:term ")" : tactic => do
  let env ← Lean.MonadEnv.getEnv
  let mStr := M.raw.getSubstring?.map Substring.Raw.toString |>.getD ""
  if mStr.isEmpty then throwError "cir_fuel_step: cannot recover measure source text"
  let fStr := F.getId.toString
  let gStr := G.getId.toString
  let .ok haveStx := Lean.Parser.runParserCategory env `tactic
      s!"have hF' : {mStr} ≤ {fStr} := by omega"
    | throwError "cir_fuel_step: could not parse have step"
  Lean.Elab.Tactic.evalTactic haveStx
  let .ok obtainStx := Lean.Parser.runParserCategory env `tactic
      s!"obtain ⟨{gStr}', rfl, h{gStr}'⟩ := fuel_step_down (F := {gStr}) ({mStr}) (by omega)"
    | throwError "cir_fuel_step: could not parse obtain step"
  Lean.Elab.Tactic.evalTactic obtainStx

/-- T2 program-loop unfold (audit #4): the `have hwhile` step shared by
    the program-level loops (R/S/T/M1/M2c/M3c/M4c, value + mem). The
    rule application is `RULE PROG (F) _..._ hg` — concrete program and
    fuel, underscores elsewhere — so `LOOP`/`PROG`/`hg` are idents
    while `F` and `hbody` are terms (`F` is usually `F`, once `G + 1`;
    `hbody` is once a projection, `hstep.1`). Value vs mem
    family is read off the goal head (`evalProgStmt` /
    `memEvalProgStmt`); anything else errors loudly.
    Usage: `cir_unfold_prog (selectionSortLoop, vecSelectionSortProg, F, hguardT, hbody)`.
    (Reparse: `simp only` arg kinds reject spliced idents.) -/
elab "cir_unfold_prog" "(" loopDef:ident "," progArg:ident "," fuel:term ","
    hguard:ident "," hbody:term ")" : tactic => do
  let tgt ← Lean.Elab.Tactic.getMainTarget
  let tgt := tgt.consumeMData
  let fnName? : Option Lean.Name := do
    guard (tgt.getAppFn.constName? == some `Eq)
    let args := tgt.getAppArgs
    guard (args.size == 3)
    args[1]!.getAppFn.constName?
  let lStr := loopDef.getId.toString
  let pStr := progArg.getId.toString
  let env ← Lean.MonadEnv.getEnv
  let fStr := fuel.raw.getSubstring?.map Substring.Raw.toString |>.getD ""
  if fStr.isEmpty then throwError "cir_unfold_prog: cannot recover fuel source text"
  let hgStr := hguard.getId.toString
  let hbStr := hbody.raw.getSubstring?.map Substring.Raw.toString |>.getD ""
  if hbStr.isEmpty then throwError "cir_unfold_prog: cannot recover body source text"
  let ruleApp : String ← match fnName? with
    | some `evalProgStmt =>
      pure s!"evalProgStmt_while_true {pStr} ({fStr}) _ _ _ {hgStr}"
    | some `memEvalProgStmt =>
      pure s!"memEvalProgStmt_while_true {pStr} ({fStr}) _ _ _ _ _ {hgStr}"
    | _ => throwError "cir_unfold_prog: goal is not a program-level while equation"
  let .ok stx := Lean.Parser.runParserCategory env `tactic
      s!"simp only [{lStr}, {ruleApp}, {hbStr}]"
    | throwError "cir_unfold_prog: could not parse simp step"
  Lean.Elab.Tactic.evalTactic stx

/-- T2 leaf-loop unfold (audit #4): the fuel-level `have hwhile` step
    (`simp [LOOP, evalStmtFuel, evalStmtSuccHandler, evalStmtWith, hg,
    hbody]`, ~17 ArraySort/Vec64/Span/VecAtSum/M4c-min_index sites).
    Goal must be an `evalStmtFuel` equation; the mem fuel-level rule
    (`memEvalStmtFuel_while_true`, 2 M4c sites, concrete-arg form)
    stays prose until a third consumer earns its branch.
    Usage: `cir_unfold_leaf (minIndexLoop, hguardT, hbody)`. -/
elab "cir_unfold_leaf" "(" loopDef:ident "," hguard:ident "," hbody:term ")" : tactic => do
  let tgt ← Lean.Elab.Tactic.getMainTarget
  let tgt := tgt.consumeMData
  let fnName? : Option Lean.Name := do
    guard (tgt.getAppFn.constName? == some `Eq)
    let args := tgt.getAppArgs
    guard (args.size == 3)
    args[1]!.getAppFn.constName?
  if fnName? != some `evalStmtFuel then
    throwError "cir_unfold_leaf: goal is not a fuel-level while equation"
  let env ← Lean.MonadEnv.getEnv
  let hbodyStr := hbody.raw.getSubstring?.map Substring.Raw.toString |>.getD ""
  if hbodyStr.isEmpty then throwError "cir_unfold_leaf: cannot recover body source text"
  let cmd := s!"simp [{loopDef.getId.toString}, evalStmtFuel, evalStmtSuccHandler, evalStmtWith, {hguard.getId.toString}, {hbodyStr}]"
  let .ok stx := Lean.Parser.runParserCategory env `tactic cmd
    | throwError "cir_unfold_leaf: could not parse simp step"
  Lean.Elab.Tactic.evalTactic stx
