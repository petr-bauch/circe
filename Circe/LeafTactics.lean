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
users see these tactics too.
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
