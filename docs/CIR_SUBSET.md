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
no function pointers, no `malloc/free` (v0.1), read-only `const` globals only.

## Admitted CIR ops (raw CIRGen shape)

- `cir.func`, `cir.func.type`
- `cir.alloca`, `cir.load`, `cir.store` (functionalizable shape only)
- `cir.cast` (`int`/`bool` kinds only)
- `cir.binop`, `cir.cmp`, `cir.unary`
- `cir.br`, `cir.cond_br`
- `cir.return`, `cir.call`, `cir.const`
- `cir.get_member`, `cir.get_element`, `cir.ptr_stride` (bounded-index form)
- `cir.if`, `cir.ternary`, `cir.while`, `cir.for` as emitted by CIRGen
- `cir.condition`, `cir.inc` (loop machinery), `cir.scope`, `cir.yield`
- `cir.const` (`#cir.int<N>` attributes)

## Rejected (loud errors, not silent modeling)

`cir.try`, cleanup/EH ops, vtables, atomics, `volatile` ops, complex/float
(beyond bit-stub), inline asm, `void*` casts, int-ptr casts, escaping
address-of, unbounded pointer arithmetic. Each rejection carries a code:
`alias-reject`, `escape-reject`, `oob-possible`, `out-of-subset`.
