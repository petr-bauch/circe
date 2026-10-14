import Circe.Mem

/-- Hoare triples as thin sugar over the `Mem` equation lemmas
    (H-track): total correctness over `.ok` outcomes, fuel-generic.
    From any pre-state satisfying `P`, statement `s` evaluates (at
    any fuel) to an ok outcome satisfying `Q`. Errors are excluded
    by construction — the caller discharges them through
    hypotheses, matching transfer style (store equations stay
    hypotheses). No new semantics: every rule below is a direct
    wrapper around an existing `memEvalStmtFuel_*` equation. -/
def HTriple (P : Env × Mem × Layout → Prop) (s : CStmt)
    (Q : Env × Mem × Layout → Outcome → Prop) : Prop :=
  ∀ F ρ m π, P (ρ, m, π) →
    ∃ ρ' m' π' o, memEvalStmtFuel F s ρ m π = .ok ((ρ', m', π'), o) ∧
      Q (ρ', m', π') o
