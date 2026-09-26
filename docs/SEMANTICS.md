# Semantics Table (CIR → CoreIR → Lean) — Phase 7

`Eval` is Aeneas-style: environments map variables to **values with
loan/borrow bookkeeping** (`Env` + `LoanState` in `Circe/Eval`); there is
no heap and no addresses. Phase 4 adds `assign`/`if_` and fuel-bounded
`while_` (`EVAL_FUEL`), `uadd`/`ult`/`idx` expressions, whole-function
`evalFuncFuel`, `choose` forward/backward with lens laws, the `sum`
bounded-loop proof, and the real `validate` + oracle gate. Phase 5 adds
the user-facing specs layer (`Circe.Specs`: `incr_correct`,
`choose_lens_laws`, `sum_correct` over `Base` ops identical to the
emitted bodies) and `cir_simp` (`Circe.Tactics`); `call` and
full struct `Eval`/`Emit` land after v0.1. Phase 7 adds the
uniquely-owned heap fragment (`vnew`/`vget`/`vset`/`vfree` over
`Value.vecVal` with an affine token; `vec_alloc` canonical program with
two-loop `emit_correct_vec`; `vec_correct` spec).

## Evaluated fragment (lemmas compile, `lake build` green)

| C | Raw CIRGen idiom (from `tests/cir/*.cir`) | CoreIR / `Eval` | Lean (`Circe.Base` / emitted) |
|---|---|---|---|
| `a + b` (`int32_t`, `nsw`) | `cir.add nsw` on `!cir.int<s,32>` with `__retval` alloca/store/load/return | `CExpr.add` (`CoreIR`) over `Value.i32`; `evalFunc addFunc [a,b]` | `out/Add.lean`: `add_fwd = checkedAddI32`; `emit_correct_add` + ok/err corollaries |
| `*p = *p + 1` | `cir.load` / `cir.add` / `cir.store` through `!cir.ptr<!s32i>` | `mutBorrow` param; `evalFunc incrFunc [p]` (value in, updated value out) | `out/Incr.lean`: `incr_fwd = checkedIncrI32`, caller `y ← incr_fwd y`; `emit_correct_incr` + ok/err corollaries |
| `b ? x : y` (`int32_t *`) | `cir.ternary` + `bool→int→bool` cast chain, `{llvm.noalias}` params | `CStmt.if_` over `Value.b`; `evalFunc chooseFunc [b,x,y]`; single-region (`r1 == r2`) | `out/Choose.lean`: `choose_fwd` + `choose_back`; `emit_correct_choose`, lens laws `choose_back_get_put/put_get` |
| `s += a[i]` (`uint32_t`, bounded) | `cir.for` cond/body/step + `cir.ptr_stride` + plain `cir.add`, length param `n` | `uadd` (wraps) / `ult` / `idx` (`OOB` off-end); `assign`; fuel-bounded `while_` (`EVAL_FUEL`); `evalFuncFuel` | `out/SumArray.lean`: `sum_fwd` over `BoundedList` via `prefixSumU32`; `emit_correct_sum` (fuel induction) + OOB corollary |
| `validate` gate | signature attrs + op-presence in CIR text | `RawFunc`/`RawParam` (trusted parse) → canonical `Func` or `RejectCode` | `runPipelineOpt` + `native_decide`: `.cir → .lean` bytes proved for all 5 translatable corpus functions |
| `malloc(n)` / `v[i]` / `free(v)` (`uint32_t`, uniquely owned) | `cir.call @malloc` / `cir.for` + `cir.ptr_stride` / `cir.call @free` (with `cir.get_global` plumbing), length param `n` | `vnew`/`vget` exprs, `vset`/`vfree` stmts over `Value.vecVal` (`Vec32` + `freed` token; use-after-free/double-free → `AssertFail`) | `out/VecAlloc.lean`: `vec_alloc_fwd = vecFillSumU32 n.toNat` (`vecNew`/`vecFillLoop`/`vecSumLoop`/`vecFree`); `emit_correct_vec` (two-loop fuel induction) |
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
Heap idioms (Phase 7, from `tests/cir/vec_alloc.cir`): `cir.call @malloc`
with `n * sizeof` (`cir.mul` on `!u64i`) + `bitcast` to the element type,
`cir.get_global @malloc/@free` address plumbing (gated by the vec shape,
not the globals rejection), `cir.func private @malloc/@free` declarations
(counted by call sites, not `@free(` occurrences), two `cir.for` loops
(fill + sum) over `cir.ptr_stride`, `cir.call @free` exactly once.

## Deferred after v0.1

`call` (function calls, Phase 5+), full struct `Eval`/`Emit`
(`cir.get_member` admitted in `Base`, rejected by `validate` with a
dedicated message), generalized `emit_correct` over all `matchFrag`-
accepted shapes (currently proved for canonical `Func`s; the pipeline only
feeds validator-produced canonical `Func`s). E2E harness:
`tools/check-phase7.sh` (superset: phase-5 pipeline → golden `diff` →
`lake env lean` typecheck → native drivers → `DiffPhase3`/`DiffPhase4`/
`DiffVec` fuzz → `GoldenPhase4`/`GoldenPhase7` pipeline + rejection suites
→ emitted-body correspondence → specs typecheck).
