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
(heap blocks are `vecVal` / `vecVal64` values + affine token). It is the spec for
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
Width idioms (S3b): same `__retval` shape as 32-bit `add`, at
`!s64i` (`cir.add nsw`, checked via `checkedAddI64`) and `!u64i`
(plain `cir.add`, wrapping); 8/16-bit params lower through `i32`
casts (integer promotion — rejected with the promotion message).

## Trust boundary

Trusted: Clang/CIRGen, CIR syntax, Lean+Mathlib,
rendering, parser. Oracle verdicts (`tests/oracle/verdicts.txt`) were a
trust root through M2; M3 (ROADMAP.md) shrinks that trust on the admitted
C fragment: `Validator.derivedNoalias` derives noalias from CIR text,
`Circe.Derived` proves per-shape footprints, and `Circe.Transfer` proves
`oracle_noalias f → memEval f = Eval f` — so for C the verdicts file is a
checked cache (CI asserts agreement) rather than a soundness argument.
C++ shapes (M2a/b/c) rest on the same transfer story since M3d:
single-ref params bind values justified by the attr triple, box tokens
thread through single-word blocks, and `cleanup`/`trap` erasure is
proved in `memEval` — the triple + call multisets are text pins for
proved transfer, not faith.
Verified: `CoreIR`, `Eval`, `Mem`, `Emit`,
`emit_correct`, `validate` gate, per-shape transfers.
Differential fuzz (`Diff*`) stays as a P0 signal throughout, but is no
longer the soundness argument where transfer is proved.

## E2E harness

`tools/check.sh [trials]` (thin entry; `check-phase*.sh` kept for
compat) delegates to the parallel Lean driver (`lake exe circe-test`,
`Test/Driver.lean`, whose roster IS the wiring): regenerate `out/`
(`tools/GenOut.lean`, single source of truth) → native drivers →
golden `diff`s (`tests/golden/*.lean`) → `lake env lean` typecheck →
`Diff*` fuzz vs native → `Golden*` pipeline + rejection suites →
emitted-body correspondence → specs typecheck (35/35) → `TEST-OK`
(`CHECK-OK` at the shell entry). Suites run as parallel `IO` tasks,
run-all-and-report (every failure prints, nonzero exit at the end).
`lake` does not track `include_str` deps, so `diff` enforces drift.
