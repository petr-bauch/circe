# Verifying Functional Correctness

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

## Current status (Phase 4)

`emit_correct` now covers four shapes (`Circe/Emit.lean`): `add`/`incr`
(Phase 3) plus `choose` (with `chooseBack` and machine-checked lens laws)
and `sum` (fuel-induction loop proof + OOB corollary). `emitFunc` renders
all four to `out/` (pinned by `tests/golden/*.lean`, `native_decide`
linkage, `lake env lean` typecheck) and rejects everything else.
`validate` is a real gate (`RawFunc` + oracle → canonical `Func` or a
precise `alias-reject`/`escape-reject`/`oob-possible`/`out-of-subset`);
`runPipelineOpt` + `native_decide` proves `.cir → .lean` bytes for the
whole translatable corpus at build time. `tools/check-phase4.sh` runs the
whole E2E including both differential fuzzers and the 18-case
golden/rejection suite. Remaining for Phase 5: user-facing functional
specs (`incr_correct`, `choose_lens_laws`, `sum_correct` over emitted
code) and `cir_simp` tactics.
