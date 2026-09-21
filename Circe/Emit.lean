/-
Circe.Emit — verified emitter `CoreIR → Lean` (forward + backward defs).

Phase 1: `emitFunc` pretty-printing stub over `Func`. Phase 3 grows this
into the real emitter for by-value `add` then `incr_fwd`, with the
`emit_correct` theorem:

  theorem emit_correct (f : Func) (ρ : Env) :
    evalLean (emitFunc f) ρ = Eval f ρ

proved by structural induction on `CStmt` (PLAN.md §6).
-/
import Circe.CoreIR

/-- Emitted Lean code for one function: forward definition text, plus an
    optional backward definition for borrow-returns (`choose`-shape). -/
structure EmittedFunc : Type where
  forward : String
  backward : Option String
  deriving DecidableEq, Repr

/-- Phase 1 stub: emits a `-- skeleton` placeholder carrying the function
    name. Real forward/backward synthesis lands in Phases 3–4 with
    `out/*.lean` pretty-printing checked by `lake build`. -/
def emitFunc (f : Func) : EmittedFunc :=
  { forward := s!"-- skeleton: forward {f.name}\n", backward := none }
