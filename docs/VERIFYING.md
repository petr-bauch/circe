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

## Current status (Phase 3)

First `emit_correct` fragment is proved: `emit_correct_add`/`emit_correct_incr`
(`Circe/Emit.lean`, with ok/err corollaries) relate `evalFunc` on the
canonical `addFunc`/`incrFunc` to the verified `addFwd`/`incrFwd`.
`emitFunc` renders the admitted shapes to `out/Add.lean`/`out/Incr.lean`
(trusted tag-erasing pretty-printing; pinned by `tests/golden/*.lean`,
typechecked by `lake env lean`) and rejects everything else with
`EmitError.notFragment`. `tools/check-phase3.sh` runs the whole E2E
including the `tests/lean/DiffPhase3.lean` differential fuzz vs native.
The validator gate is still closed (every input rejected as `outOfSubset`)
until Phase 4 wires `validate` to the emitter.
