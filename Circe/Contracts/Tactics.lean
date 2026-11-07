/-
Circe.Contracts.Tactics — small proof tactics for the contract
layer (P3-N5).

Two recurring mechanical steps, bundled once:

- `cir_mem_let hM hV`: the program-level pure-`let_` step. Every
  `memRevLet` call repeats the same four constructor-
  discrimination side proofs (`vnew`/`boxNew`/`vgrowNew`/`nnew`
  exclusion); the macro fills them, leaving only the two
  hypotheses that differ per site — the mem/value agreement
  `hM` and the value evaluation `hV`.
- `cir_lookup`: environment lookup chains over `let_` preludes.
  Tries a direct hit first, then one and two `envExtend_miss`
  rewrites with the inequality discharged by `decide` (prelude
  names are closed literals). Fails loudly when the chain is
  deeper or the names are not literals — that is a signal to
  name the intermediate environment, not to extend the macro.

Deliberately minimal: no invented middles, no goal-shape
guessing, no custom bracket syntax (probed `⦃⦄` notation
collides with the term parser even in isolation; plain
`HTriple`/`HTripleProg` applications plus the two tactics
below carry the readability). Tactics that would need to
invent an invariant or a frame stay explicit `refine`s at the
call site (see the `verify`-deferral note in
`docs/VERIFYING.md`).
-/
import Lean
import Circe.Hoare.Vec
import Circe.Transfer.VecReverse

/-- Program-level pure-`let_` step: fills the four constructor
    discriminations, leaving the agreement and value proofs.
    `memRevLet` takes the evidence last; the wrapper below
    reorders it first (`memRevLet_of`): the two agreement
    proofs (`h`, `hv`) determine the expression, so the four
    proofs (`h`, `hv`) determine the expression, so the four
    constructor discriminations elaborate with a concrete `e`.
    (Passing them last forces the discriminations to elaborate
    against a metavariable, which `cases` cannot split.) -/
theorem memRevLet_of (prog : Prog) (F : Nat)
    (x : String) (ty : CType) (e : CExpr)
    (ρ : Env) (m : Mem) (π : Layout) (v : Value)
    (h : memEvalExpr e ρ m π = evalExpr e ρ)
    (hv : evalExpr e ρ = .ok v)
    (hnot : ∀ se, e ≠ .vnew se)
    (hnotBox : ∀ se, e ≠ .boxNew se)
    (hnotGrow : ∀ ce, e ≠ .vgrowNew ce)
    (hnotN : e ≠ .nnew) :
    memEvalProgStmt prog F (.let_ x ty e) ρ m π =
      .ok ((envExtend ρ x v, m, π), .fellThrough) :=
  memRevLet prog F x ty e ρ m π v
    hnot hnotBox hnotGrow hnotN h hv

macro "cir_mem_let" "(" hM:term "," hV:term ")" : tactic =>
  `(tactic| (refine memRevLet_of _ _ _ _ _ _ _ _ _ $hM $hV ?_ ?_ ?_ ?_; all_goals (first | (intro x h; cases h) | (intro h; cases h))))

/-- Environment lookup over `let_` preludes: direct hit, then
    one- and two-deep miss chains with `decide`d inequalities
    (prelude names are closed literals). Fails loudly on deeper
    chains or non-literal names — that is a signal to name the
    intermediate environment, not to extend the macro. -/
macro "cir_lookup" : tactic =>
  `(tactic| first | exact envExtend_hit _ _ _ | (rw [envExtend_miss _ _ _ _ (by decide)]; exact envExtend_hit _ _ _) | (rw [envExtend_miss _ _ _ _ (by decide), envExtend_miss _ _ _ _ (by decide)]; exact envExtend_hit _ _ _))
