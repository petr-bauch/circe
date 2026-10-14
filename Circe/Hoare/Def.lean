import Circe.Mem

/-- Hoare triples as thin sugar over the `Mem` equation lemmas
    (H-track): total correctness over `.ok` outcomes, fuel-generic.
    From any pre-state satisfying `P`, statement `s` evaluates (at
    any fuel) to an ok outcome satisfying `Q`. Errors are excluded
    by construction — the caller discharges them through
    hypotheses, matching transfer style (store equations stay
    hypotheses). No new semantics: every rule below is a direct
    wrapper around an existing `memEvalStmtFuel_*` equation. -/
def HTripleAt (F : Nat) (P : Env × Mem × Layout → Prop) (s : CStmt)
    (Q : Env × Mem × Layout → Outcome → Prop) : Prop :=
  ∀ ρ m π, P (ρ, m, π) →
    ∃ ρ' m' π' o, memEvalStmtFuel F s ρ m π = .ok ((ρ', m', π'), o) ∧
      Q (ρ', m', π') o

def HTriple (P : Env × Mem × Layout → Prop) (s : CStmt)
    (Q : Env × Mem × Layout → Outcome → Prop) : Prop :=
  ∀ F, HTripleAt F P s Q

/-- A fuel-generic triple holds at every fixed fuel (loop bodies
    are proved with plain `HTriple`, then instantiated). -/
theorem htriple_at_of (P : Env × Mem × Layout → Prop) (s : CStmt)
    (Q : Env × Mem × Layout → Outcome → Prop)
    (h : HTriple P s Q) (F : Nat) : HTripleAt F P s Q := h F
