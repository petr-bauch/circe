# Semantics Table (CIR → CoreIR → Lean) — Phase 2

`Eval` is Aeneas-style: environments map variables to **values with
loan/borrow bookkeeping** (`Env` + `LoanState` in `Circe/Eval`); there is
no heap and no addresses. Statement-level control flow and the
`emit_correct` simulation proof land in Phases 3–4; this table records the
fragment with a full `Eval` semantics plus `Circe.Base` lemmas today.

## Evaluated fragment (lemmas compile, `lake build` green)

| C | Raw CIRGen idiom (from `tests/cir/*.cir`) | CoreIR / `Eval` | Lean (`Circe.Base`) |
|---|---|---|---|
| `a + b` (`int32_t`, `nsw`) | `cir.add nsw` on `!cir.int<s,32>` with `__retval` alloca/store/load/return | `CExpr.add` over `Value.i32`; `evalExpr` forwards to `checkedAddI32` | `checkedAddI32`: `.error .Overflow` off-range; lemmas `checkedAddI32_ok/err/ok_implies_range/err_implies_outside/ok_value/comm` |
| `*p = *p + 1` | `cir.load` / `cir.add` / `cir.store` through `!cir.ptr<!s32i>` | `mutBorrow` param role (no address values); caller `y ← incr_fwd y` | `checkedIncrI32 = checkedAddI32 · 1`; lemma `checkedIncrI32_ok` |
| `-a`, `a / b` (`int32_t`) | `cir.unary neg`, `cir.binop div` | `evalExpr` extension point (same `Result` plumbing) | `checkedNegI32` (fails only on `INT_MIN`), `checkedDivI32` (`DivZero` + `INT_MIN/-1`); lemmas `checkedNegI32_ok/err`, `checkedDivI32_zero` |
| `a + b` (`uint32_t`) | plain `cir.add` (no `nsw`) | `Value.u32` | `checkedAddU32` (wraps, always `ok`; lemma `checkedAddU32_ok`); `checkedAddU32Strict` (carry → `Overflow`) for bounds arithmetic |
| `a[i]`, `0 ≤ i < n` | `cir.ptr_stride` + `cir.load` | `Value.arr32` + length witness | `BoundedList α n` (`l.length = n`), `bget` (else `OOB`); lemmas `bget_ok/oob/length` |
| `struct Point` by value | `!rec_Point` + `cir.get_member %p[N]` | `Value.structVal` (named `BitVec` fields) | `Point`, `pointTranslate` (field-wise `checkedAddI32`); lemmas `pointTranslate_ok/err_x` |
| `&y` → `restrict` param | `{llvm.noalias, llvm.noundef}` attrs | `loanVar` (loan + live borrow); caller-side value update | n/a (capability only, no runtime value) |
| region end (borrow-return join) | n/a (emitter-level) | `endRegion` (expire one region); `LoanWF` preserved (`loanWF_endRegion`) | n/a |
| env hygiene | `cir.scope` nesting, `cir.alloca` locals | `envLookup/envExtend`, `EnvWF` (no duplicate bindings); `LoanWF` (every loan has a live borrow) | n/a |

## Observed CIRGen idioms (from Phase 0 goldens)

Handled-or-planned per row above: `__retval` alloca + store/load/return
pattern; `bool→int→bool` cast chains around `cir.ternary` conditions and
`cir.for` `cir.condition`; `cir.for` cond/body/step regions + `cir.inc`;
`cir.ptr_stride`; `!rec_Point` record types + `cir.get_member %p[N]`;
`cir.add nsw` (signed, checked) vs plain `cir.add` (unsigned, wrapping);
`cir.scope` nesting; module attrs (`cir.triple`, `dlti.dl_spec`) to ignore.

## Deferred to Phases 3–4

Statement-level `Eval` control flow (`if`/`while`/`for` over `CStmt`),
`validate` admission per op, `emitFunc` forward/backward synthesis, and the
`emit_correct` simulation theorem. The stub `evalStmt` never fails by
construction (`evalStmt_is_ok`); all Phase 2 failure semantics live in
`evalExpr` + `Circe.Base`.
