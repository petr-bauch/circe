# Semantics Table (CIR → CoreIR → Lean) — Phase 3

`Eval` is Aeneas-style: environments map variables to **values with
loan/borrow bookkeeping** (`Env` + `LoanState` in `Circe/Eval`); there is
no heap and no addresses. Phase 3 adds statement semantics for
`skip`/`seq`/`let_`/`return_`, whole-function `evalFunc`, and the
`emit_correct` theorems for the `add`/`incr` fragment; `if_`/`while_`/
`call`/`assign` and `validate` admission land in Phase 4.

## Evaluated fragment (lemmas compile, `lake build` green)

| C | Raw CIRGen idiom (from `tests/cir/*.cir`) | CoreIR / `Eval` | Lean (`Circe.Base` / emitted) |
|---|---|---|---|
| `a + b` (`int32_t`, `nsw`) | `cir.add nsw` on `!cir.int<s,32>` with `__retval` alloca/store/load/return | `CExpr.add` (`CoreIR`) over `Value.i32`; `evalFunc addFunc [a,b]` | `out/Add.lean`: `add_fwd = checkedAddI32`; `emit_correct_add` + ok/err corollaries |
| `*p = *p + 1` | `cir.load` / `cir.add` / `cir.store` through `!cir.ptr<!s32i>` | `mutBorrow` param; `evalFunc incrFunc [p]` (value in, updated value out) | `out/Incr.lean`: `incr_fwd = checkedIncrI32`, caller `y ← incr_fwd y`; `emit_correct_incr` + ok/err corollaries |
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

## Deferred to Phase 4

`if_`/`while_`/`for` control flow over `CStmt`, `call`/`assign`,
`validate` admission per op (+ oracle `noalias` gate), and
borrow-return (`choose`-shape) forward/backward synthesis with
`emit_correct` extensions. E2E harness: `tools/check-phase3.sh`
(build → regenerate `out/` → golden `diff` → `lake env lean` typecheck →
native drivers → `tests/lean/DiffPhase3.lean` differential fuzz).
