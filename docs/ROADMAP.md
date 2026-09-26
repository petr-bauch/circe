# Roadmap (post-v0.1, Phase 6 follow-ups)

v0.1 rejects loudly everything it cannot functionalize. This note records
the three accepted follow-ups from `docs/PLAN.md` §7 Phase 6, in priority
order, each with an acceptance sketch. Nothing here is implemented; the
`validate` gate stays closed-by-default until each lands with proofs.

## 1. Uniquely-owned heap (`malloc` as `Vec`)

Today `malloc`/`free` are `out-of-subset` (see `forbiddenOp` in
`Circe/Validator.lean`). The plan: model a uniquely-owned heap block as a
`Vec`-like value (`BoundedList` with capacity), following the same
value-not-address discipline as arrays:

- `malloc(n)` becomes a pure constructor `vecNew n : Result (Vec T)`;
- `free` becomes a linear consumption (affine use-once, enforced by
  `validate`: the block must not be live after `free`);
- writes through the unique handle become `vecSet` (value in, value out),
  like `incr_fwd` today.

Acceptance: `validate` admits a `vecParam` shape only with an oracle
`noalias` verdict on the handle; `emit_correct` for the new ops; golden
`VecAlloc.lean`; differential fuzz vs native; `free`-after-use and
double-`free` both rejected with actionable codes.

## 2. C++-lite constructors (still no EH)

`cir.try`/cleanup/`landingpad` stay rejected. In-subset C++-lite means:

- value constructors for aggregates already in `Base` (`Point`-style
  structs) admitted through `Eval`/`Emit` (struct field ops are `Base`-ready
  but pending `Eval`/`Emit` — see the `get_member` rejection);
- no vtables, no inheritance, no templates, no exceptions;
- each admitted op needs its per-op correctness lemma before `matchFrag`
  accepts it (same bar as Phases 2–4).

Acceptance: struct-by-value corpus (`tests/c/struct_by_value.c`)
translates, verifies, and fuzzes clean instead of rejecting.

## 3. Shrinking oracle trust (Stacked Borrows justification)

Explicit soundness gap (documented, not hidden): the oracle's `noalias`
verdict and `CIRGen` are trusted in v0.1. The follow-up is a
Stacked-Borrows-style justification: formalize the ownership semantics
against a CompCert-style memory with a borrow stack, and prove that an
oracle `noalias` verdict implies the loan-based `Eval` agrees with the
memory semantics on the admitted fragment.

Acceptance: a machine-checked theorem of the form
`oracle_noalias f → memEval f = Eval f` for the §4 subset, shrinking the
trust base to Clang/CIRGen text + Lean/Mathlib. Until then: oracle verdicts
stay checked in (`tests/oracle/verdicts.txt`), differential testing stays
P0 on mismatch, and the validator stays conservative (inconclusive = reject).
