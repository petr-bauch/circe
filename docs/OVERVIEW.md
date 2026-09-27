# Circe — Overview (current state, 2026-09-27)

CIR → Lean 4 verification pipeline for non-aliasing C, Aeneas-style:
C source → ClangIR (raw CIRGen) → pure, memory-free Lean 4 via a
verified emitter, with functional-correctness proofs as pure equations.

No memory model, no separation logic in the common case. Out-of-subset
input rejects loudly, never silently models memory.

## What works today

| Fragment | C example | Lean output | Proof |
|---|---|---|---|
| by-value `add` | `a + b` (`int32_t`, `nsw`) | `add_fwd = checkedAddI32` | `emit_correct_add` + ok/err |
| `mutBorrow` | `incr_ptr` | `incr_fwd = checkedIncrI32` | `emit_correct_incr` |
| borrow-return | `choose_ptr` | `choose_fwd` + `choose_back` | lens laws |
| bounded loop | `sum_array` | `prefixSumU32` over `BoundedList` | `emit_correct_sum` (fuel induction) |
| uniquely-owned heap (`u32`-only) | `vec_alloc` | `vecFillSumU32 n.toNat` | `emit_correct_vec` (two-loop induction) |
| DAG call (double-`add`) | `add_caller` | two `checkedAddI32` binds (leaf inlined; `addCallerFwd_as_calls`) | `evalProgFunc_addCaller` (program induction-free composition) |
| DAG call (`sum` delegation) | `sum_caller` | `prefixSumU32` body (`sumCallerFwd_is_call`) | `evalProgFunc_sumCaller` (fuel-generalized callee reuse) |

Plus: `Result` + checked ops (`Base`), loan-based value semantics
(`Eval`), verified gate (`validate` + oracle verdicts), emitter
(`Emit`), `cir_simp` tactic, specs (`incr_correct`,
`choose_lens_laws`, `sum_correct`, `vec_correct`).

## Pipeline

```
tests/c/*.c → tests/cir/*.cir (tools/emit-cir.sh, CIR clang)
  → Parser (trusted) → RawIR
  → Oracle verdicts (trusted, tests/oracle/verdicts.txt)
  → validate (verified gate) → CoreIR Func
  → emitFunc (verified) → out/*.lean (tests/golden/*.lean pins bytes)
```

E2E: `tools/check.sh [trials]` (single entry; superset: phase-7 pipeline
→ caller golden `diff`s → `lake env lean` typecheck → native caller
drivers → `DiffCalls` fuzz vs native → `GoldenCalls` pipeline +
rejection suite → emitted-body correspondence → `CHECK-OK`).

See `PIPELINE.md` for stages and trust, `SUBSET.md` for the admitted
subset, `VERIFYING.md` for the user workflow, `ROADMAP.md` for next
milestones, `PINS.md` for toolchain pins.

## Mid-term goal

Non-aliasing C/C++ code: more syntax, tactics that simplify working
with the Lean versions, and scaffolding for simple verification of the
input programs on the Lean side. Short-term scope (per planning):
C + struct-by-value only, calls first, `cir_simp` now + DSL next,
spec skeletons in `out/*_Spec.lean`. Details in `ROADMAP.md`.
