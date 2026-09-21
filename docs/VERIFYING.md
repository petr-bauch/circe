# Verifying Functional Correctness — Phase 1 stub

Target workflow (Phase 5): pure equational specs over emitted code, à la
Aeneas — no memory model, no separation logic, no framing lemmas.

```lean
theorem incr_correct : ∀ p, incr_fwd p = checkedIncrI32 p := by simp [incr_fwd]
theorem choose_lens_laws : …  -- forward/backward round-trip
theorem sum_correct : sum_fwd a n h = .ok (a.sum …)  -- against `List.sum`
```

## Tactics (Phase 5)

`Circe.Tactics` (`cir_simp` for `Result`-bind + backward-function
unfolding): plain `simp`/`omega`/`bv_decide` suffice in the common case.
Documented here when the tactic lands.

## Current status (Phase 1)

Nothing to verify yet: the validator gate is closed (every input rejected
as `outOfSubset`) and `emitFunc` produces `-- skeleton` placeholders.
This file will grow with the first `emit_correct` fragment in Phase 3.
