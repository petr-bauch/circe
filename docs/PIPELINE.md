# Circe — Pipeline and Trust

## Stages

```
C source (+ restrict discipline, SUBSET.md)
  → clang -fclangir -Xclang -emit-cir → foo.cir (MLIR text)
  → Parser (Lean exe, trusted): text → RawIR (signatures + op-presence)
  → Oracle verdicts (trusted): per-function noalias facts
     (tests/oracle/verdicts.txt, parsed by Circe.Oracle)
  → validate (verified): RawIR → Option CoreIR (SUBSET.md gate)
  → Emit (verified): CoreIR → Lean (forward + optional backward)
  → out/Foo.lean importing Circe.Base, checked by lake build
```

`CoreIR` is the trust-boundary output: unverified text never reaches
`Emit` without passing `validate`. Pointers never appear as values;
they become `BorrowRole` (`owned` / `mutBorrow` / `sharedBorrow`).

## Semantics

`Eval` is Aeneas-style: environments map variables to values with
loan/borrow bookkeeping (`Env` + `LoanState`); no heap, no addresses
(heap blocks are `vecVal` values + affine token). It is the spec for
`emit_correct`:

```lean
theorem emit_correct (f : Func) (ρ : Env) :
  evalLean (emitFunc f) ρ = Eval f ρ
```

Proved per canonical `Func` by structural/fuel induction; per-op
lemmas required before each op is admitted. Rendering (Value-tag
erasure to `BitVec` text) is trusted like the parser; semantics is
what is verified.

Key idioms handled: `__retval` alloca pattern, `bool→int→bool` cast
chains, `cir.for` regions + `cir.inc`, `cir.ptr_stride`,
`!rec_Point` + `cir.get_member`, `cir.add nsw` (checked) vs plain
`cir.add` (wrapping), `cir.scope`, heap idioms (`cir.call @malloc`
+ `n*sizeof`, `get_global` plumbing, two `cir.for` loops, one
`cir.call @free` counted by call site).
Caller idioms (S1, from `tests/cir/{add_caller,sum_caller}.cir`):
two `cir.call @add` sites (caller-local `t`, then final), single
`cir.call @sum_array` delegation, `cir.func private @add/@sum_array`
declarations (not call sites), no local arithmetic/loop ops (those
live in the callee).
Struct idiom (S2, from `tests/cir/struct_by_value.cir`): by-value
`!rec_Point` param + two `i32` deltas, `cir.get_member %p[N]`
field reads (`x`/`y`) + `cir.load`, two `cir.add nsw` sites,
field stores into `__retval`, whole-struct `cir.load` + return —
fused into `fget`/`pmk` CoreIR (no local calls/loops/heap).
Control-flow idioms (S3a): nested `cir.for` (cond/body/step +
`cir.inc`, inner re-initialized per outer iteration — modeled by a
trailing `j`-reset so the outer-head invariant holds); `cir.if` +
`cir.break`/`cir.continue` inside `cir.for` (the step region runs on
`continue`, modeled by an explicit increment before the signal);
early `cir.return` inside a loop body (propagates through the
`while_` handler); `cir.switch` with `cir.case(equal, [const])` +
`default` where every case is a bare const `return` (lowered to a
nested-`if_` canonical `Func`; anything else stays rejected).

## Trust boundary

Trusted: Clang/CIRGen, CIR syntax, oracle verdicts, Lean+Mathlib,
rendering, parser. Verified: `CoreIR`, `Eval`, `Emit`,
`emit_correct`, `validate` gate.
Explicit gap: oracle `noalias` + CIRGen trusted; shrinking this is a
mid-term milestone (ROADMAP.md M3). Mitigations: verdicts checked in,
validator conservative (inconclusive = reject), differential fuzz
mismatch = P0.

## E2E harness

`tools/check.sh [trials]` (single entry; `check-phase*.sh` kept for
compat): build → regenerate `out/` (`tools/GenOut.lean`,
single source of truth) → golden `diff`s (`tests/golden/*.lean`) →
`lake env lean` typecheck → native drivers → `Diff*` fuzz vs native →
`GoldenPhase*`/`GoldenCalls` pipeline + rejection suites →
emitted-body `grep` correspondence → specs typecheck → `CHECK-OK`.
`lake` does not track `include_str` deps, so `diff` enforces drift.
