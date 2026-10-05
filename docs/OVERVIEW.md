# Circe — Overview (current state, 2026-10-03)

CIR → Lean 4 verification pipeline for non-aliasing C and STL-free
C++-lite, Aeneas-style: source → ClangIR (raw CIRGen) → pure,
memory-free Lean 4 via a verified emitter, with
functional-correctness proofs as pure equations.

No memory model, no separation logic in the common case. Out-of-subset
input rejects loudly, never silently models memory.

## What works today

| Fragment | C example | Lean output | Proof |
|---|---|---|---|
| by-value `add` | `a + b` (`int32_t`, `nsw`) | `add_fwd = checkedAddI32` | `emit_correct_add` + ok/err |
| `mutBorrow` | `incr_ptr` | `incr_fwd = checkedIncrI32` | `emit_correct_incr` |
| borrow-return | `choose_ptr` | `choose_fwd` + `choose_back` | lens laws |
| bounded loop | `sum_array` | `prefixSumU32` over `BoundedList` | `emit_correct_sum` (fuel induction) |
| recovered reader, no `restrict` (N2c) | `sum_norestrict` | same `prefixSumU32` body (`recoveredNoalias`: singleton footprint + read-only CoreIR) | `emit_correct_sum` + `memTransfer_sum` reused (gate-only change) |
| uniquely-owned heap (`u32`-only) | `vec_alloc` (+ M1d leak variant `vec_alloc_leak`: same body, validator-side only) | `vecFillSumU32 n.toNat` | `emit_correct_vec` (two-loop induction) |
| uniquely-owned heap (`u64`-only, M1b mirror) | `vec_alloc_u64` | `vecFillSumU64 n.toNat` | `emit_correct_vec64` (two-loop induction) |
| two live blocks (`u32`-only) | `vec_copy_sum` (M1a) | `vecFillSumU32 n.toNat` (copy value-invisible) | `emit_correct_vec2` (fill/copy/sum induction) |
| grown block via `realloc` (`u32`-only) | `vec_realloc` (M1c) | `vecReallocFillSumU32 n.toNat` (prefix preserved, growth zero-filled) | `emit_correct_vecRealloc` (fill/realloc/fill-extension/sum induction) |
| DAG call (double-`add`) | `add_caller` | two `checkedAddI32` binds (leaf inlined; `addCallerFwd_as_calls`) | `evalProgFunc_addCaller` (program induction-free composition) |
| DAG call (`sum` delegation) | `sum_caller` | `prefixSumU32` body (`sumCallerFwd_is_call`) | `evalProgFunc_sumCaller` (fuel-generalized callee reuse) |
| struct-by-value | `translate` (`struct_by_value`) | `pointTranslate` delegation (`translateFwd_*` bridges) | `evalFuncFuel_translate` (ok + both error paths) |
| nested loops | `nested_sum` | `nestedSumU32` double fold | `emit_correct_nested` (nested fuel induction) |
| break/continue | `skip_sum` | `skipSumU32` capped range | `emit_correct_skip` (unconditional: ≤9 iterations) |
| early return | `find_eq` | `findEqOut` first-match | `emit_correct_find` (hit/miss + OOB) |
| switch-as-if-chain | `cls` | if-chain on `ueq` | `emit_correct_cls` (loop-free) |
| 64-bit `add` | `add64` (`int64_t`, `nsw`) | `add64_fwd = checkedAddI64` | `emit_correct_add64` + ok/err |
| 64-bit wrapping `add` | `addu64` (`uint64_t`) | `addu64_fwd = .ok (a + b)` | `emit_correct_addu64` (always succeeds) |
| C++ const-method (M2a) | `point_sum_ref(const Point&)` | `pointSumRefFwd` → `pointSum` delegation | `emit_correct_method` (leaf + entry composition) |
| C++ ctor/dtor (M2b) | `acc_two(a, b)` | `accTwo` (init + two checked adds) | `emit_correct_accTwo` (1 ctor + 2 add + 1 get + 1 dtor) |
| C++ `new`/`delete` (M2c) | `box_through(x)` | `boxThrough` (identity; box + affine token) | `emit_correct_box` (token threading) |

Plus: `Result` + checked ops (`Base`), loan-based value semantics
(`Eval`), addressful block-map model + proved memory transfer on the
admitted C and C++-lite fragments (`Mem` / `Derived` / `Transfer`:
`oracle_noalias f → memEval f = Eval f` for every admitted `Func`, so
oracle verdicts are a checked cache, not a trust root), verified gate (`validate` + oracle verdicts), emitter
(`Emit`), grown `cir_simp` tactic (call-unfold, struct-field,
wider-width, vec rules, bind automation) + stage-2 helpers (`cir_fuel`
+ fuel-bound lemma, `cir_choose`), specs (`incr_correct`,
`choose_lens_laws`, `sum_correct`, `vec_correct`, `vec64_correct`,
`vecRealloc_correct`) plus 25 generated `out/*_Spec.lean` stubs
(signature + body reference + edge list + prop-test entry).

## Pipeline

```
tests/c/*.c → tests/cir/*.cir (tools/emit-cir.sh, CIR clang)
  → Parser (trusted) → RawIR
  → Oracle verdicts (trusted, tests/oracle/verdicts.txt)
  → validate (verified gate) → CoreIR Func
  → emitFunc (verified) → out/*.lean (tests/golden/*.lean pins bytes)
```

E2E: `tools/check.sh [trials]` (thin entry delegating to the parallel
driver `lake exe circe-test`, roster in `Test/Driver.lean`;
`check-phase*.sh` kept for compat) runs the full pipeline: C corpus →
caller golden `diff`s → `lake env lean` typecheck → native caller
drivers → `DiffCalls` fuzz vs native → `GoldenCalls` pipeline +
rejection suite → struct, control-flow, and 64-bit stages (same shape:
golden `diff` → native driver → `Diff*` fuzz → rejection suite →
emitted-body correspondence) → spec-stub regeneration (26/26 typecheck,
`cir_simp` coverage greps, 26/26 `_check` entries `true`) → S5 helper
presence + adoption greps → M1 heap stages (two-block, `u64`,
grown-block, leak discipline) → M2 C++ stages (setup gates,
const-methods, ctors/dtors, new/delete) → M3 transfer stages (mem
model, derived noalias + cache agreement, loop-free / flow / caller /
heap transfers) → N2 viability stages → L1 evidence stage → `CHECK-OK`.

See `PIPELINE.md` for stages and trust, `SUBSET.md` for the admitted
subset, `VERIFYING.md` for the user workflow, `ROADMAP.md` for next
milestones, `PINS.md` for toolchain pins.

## Mid-term goal

A viable verification platform for modern C++: the subset of C++ that
is amenable to Aeneas-style translation to Lean (value semantics +
affine tokens, no aliasing in the common case), with tactic and
spec-scaffolding support for proving properties of the emitted code.
Delivered so far: S0–S5, M1–M3, N1–N4 (including the full `vector`
growth composition), plus L1 lifetime evidence (extract-only).
Details in `DELIVERED.md`; active work in `ROADMAP.md`.
