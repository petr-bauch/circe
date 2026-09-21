# Semantics Table (CIR → CoreIR → Lean) — Phase 1 stub

Full table lands in Phase 2 alongside the loan-based `Eval`.
This stub records the fragment the skeleton already models.

## Fragment covered by the Phase 1 skeleton

| C | Raw CIRGen idiom (from `tests/cir/*.cir`) | CoreIR | Lean (`Circe.Base`) |
|---|---|---|---|
| `a + b` (`int32_t`) | `cir.add nsw` on `!cir.int<s,32>` with `__retval` alloca/store/load/return | `CStmt` skeleton over `CType.i 32` | `checkedAddI32 : BitVec 32 → BitVec 32 → Result (BitVec 32)` |
| `*p = *p + 1` | `cir.load` / `cir.add` / `cir.store` through `!cir.ptr<!s32i>` | `mutBorrow` param role (no address values) | `checkedIncrI32`, caller `y ← incr_fwd y` |

## Observed CIRGen idioms (from Phase 0 goldens)

These must all be handled by `validate`/`Emit` before admission
(see `docs/PINS.md`): `__retval` alloca + store/load/return pattern;
`bool→int→bool` cast chains around `cir.ternary` conditions and
`cir.for` `cir.condition`; `cir.for` cond/body/step regions + `cir.inc`;
`cir.ptr_stride`; `!rec_Point` record types + `cir.get_member %p[N]`;
`cir.add nsw` (signed) vs plain `cir.add` (unsigned); `cir.scope`
nesting; module attrs (`cir.triple`, `dlti.dl_spec`) to ignore.

## Deferred to Phase 2

Loan/borrow bookkeeping in `Env`, `Eval` for control flow and borrow
tracking, `emit_correct` statement, int-op correctness + env/loan
well-formedness lemmas.
