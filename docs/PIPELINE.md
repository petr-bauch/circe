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

## Trust boundary

Trusted: Clang/CIRGen, CIR syntax, oracle verdicts, Lean+Mathlib,
rendering, parser. Verified: `CoreIR`, `Eval`, `Emit`,
`emit_correct`, `validate` gate.
Explicit gap: oracle `noalias` + CIRGen trusted; shrinking this is a
mid-term milestone (ROADMAP.md M3). Mitigations: verdicts checked in,
validator conservative (inconclusive = reject), differential fuzz
mismatch = P0.

## E2E harness

`tools/check-phase7.sh [trials]` (current superset; renamed per
ROADMAP.md S0): build → regenerate `out/` (`tools/GenOut.lean`,
single source of truth) → golden `diff` (`tests/golden/*.lean`) →
`lake env lean` typecheck → native drivers → `Diff*` fuzz vs native →
`GoldenPhase*` pipeline + rejection suites → emitted-body `grep`
correspondence → specs typecheck → `PHASE7-OK`.
`lake` does not track `include_str` deps, so `diff` enforces drift.
