# CIR Subset for v0.1 (frozen, Phase 0)

Anything not listed here is rejected by `validate`.

## Types

`void`, `_Bool`, `i8/i16/i32/i64`, `u8/u16/u32/u64`, `T*` (disciplined only,
see OWNERSHIP.md), arrays via length-paired params, structs (no bitfields).
No `void*`, no int↔ptr casts, no `volatile`/`_Atomic`, no unions/variadics/VLAs.

## Statements / expressions

Functions, locals, `if/while/for/do`, `return`, `break/continue`,
int arithmetic/logic/comparison, int↔int and bool casts, disciplined `&/*`,
array indexing `a[i]` with length param, struct field access.
No `goto`, `setjmp`, `switch` (lower to if-chain before CIR or reject),
no function pointers, no other `malloc/free` shapes, read-only `const`
globals only. Phase 7 admits the uniquely-owned heap shape: `malloc(n *
sizeof(uint32_t))` with same-function length `n`, bounded `v[i]`, exactly
one `free(v)` (OWNERSHIP.md rule 8).

## Admitted CIR ops (raw CIRGen shape)

- `cir.func`, `cir.func.type`
- `cir.alloca`, `cir.load`, `cir.store` (functionalizable shape only)
- `cir.cast` (`int`/`bool` kinds only)
- `cir.binop`, `cir.cmp`, `cir.unary`
- `cir.br`, `cir.cond_br`
- `cir.return`, `cir.call` (`@malloc`/`@free` in the admitted vec shape
  only; all other calls rejected), `cir.const`
- `cir.get_global @malloc/@free` address plumbing (vec shape only; all
  other globals rejected)
- `cir.get_member`, `cir.get_element`, `cir.ptr_stride` (bounded-index form)
- `cir.if`, `cir.ternary`, `cir.while`, `cir.for` as emitted by CIRGen
- `cir.condition`, `cir.inc` (loop machinery), `cir.scope`, `cir.yield`
- `cir.const` (`#cir.int<N>` attributes)

## Rejected (loud errors, not silent modeling)

`cir.try`, cleanup/EH ops, vtables, atomics, `volatile` ops, complex/float
(beyond bit-stub), inline asm, `void*` casts, int-ptr casts, escaping
address-of, unbounded pointer arithmetic, non-`vec_alloc` heap uses
(`malloc` without `free`, double-`free`, misshapen heap programs — each
with a dedicated message; see OWNERSHIP.md rule 8), `setjmp`/`longjmp`, globals (`cir.global`/
`cir.get_global`), function pointers (indirect calls), VLAs
(`stack_save`/`stack_restore`), variadics (`va_arg`), `switch`
(`cir.switch`; lower to an if-chain before CIR), `goto` (`cir.br`;
structured `cir.cond_br`/`cir.for` only), bitfields, and signed wrapping
arithmetic without `nsw` (per-line check: the op and its `i32` type must
share a line; unsigned wrapping `add` as in `sum_array` stays admitted).
Each rejection carries a code:
`alias-reject`, `escape-reject`, `oob-possible`, `out-of-subset`.
Full adversarial coverage in `tests/lean/GoldenPhase6.lean` (18 checks)
plus heap coverage in `tests/lean/GoldenPhase7.lean` (6 checks).
