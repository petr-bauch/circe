# Circe — Admitted Subset (normative)

Anything not listed here is rejected by `validate` with a precise code:
`alias-reject`, `escape-reject`, `oob-possible`, `out-of-subset`.
In-subset divergence is P0; out-of-subset must reject loudly.

## Types

`void`, `_Bool`, `i8/i16/i32/i64`, `u8/u16/u32/u64` (current proofs
concentrate on `i32`/`u32`; other widths parse, generalize per
`ROADMAP.md` S3), `T*` (disciplined only, see below), arrays via
length-paired params, structs (subset pending — `Base` ready,
`Eval`/`Emit` land in `ROADMAP.md` S2; no bitfields).
No `void*`, no int↔ptr casts, no `volatile`/`_Atomic`,
no unions/variadics/VLAs.

## Statements / expressions

Functions, locals, `if`/`while`/`for`/`do`, `return`,
`break`/`continue` (simple forms; nested/early-exit hardening in S3),
int arithmetic/logic/comparison, int↔int and bool casts,
disciplined `&`/`*`, array indexing `a[i]` with length param,
struct field access (pending S2).
Uniquely-owned heap, `u32`-only: `malloc(n * sizeof(uint32_t))`
with same-function length `n`, bounded `v[i]`, exactly one `free(v)`.
No `goto`, `setjmp`, `switch` (lower first or reject),
no function pointers, no other heap shapes, read-only `const`
globals only. Calls: single-function only today; multi-function DAG
lands in S1 (recursion rejected).

## Ownership roles

- **owned**: by-value locals/params/returns (ints, structs-as-values,
  arrays-as-lists, heap blocks-as-values with affine token).
- **mutBorrow(region)**: `T *__restrict` param, unique for its region.
  Caller `f(&y)` becomes `y ← f_fwd y`.
- **sharedBorrow**: `const T *` + length param; pure `List` argument
  (copy semantics for verification).

## Rules

1. `T*` params must be `__restrict__` or oracle-proven `noalias`.
2. No two live params may alias (oracle verdict required).
3. No escaping, except the borrow-return pattern below.
4. Indexing only as `p[i]` / `*(p+i)` with `0 <= i < n`, `n` a
   same-function length argument.
5. `&x` may only feed a `restrict` call in the same scope.
6. Borrow-return (`choose`-shape): a `T*` return must be exactly one of
   the `T*` inputs. Generates forward + backward functions.
   Single-region only; nested/multiple regions rejected.
7. Loops must be length-paired (`sum_array` shape) and terminate within
   `EVAL_FUEL` (4096); exhaustion is `AssertFail` (incompleteness, never
   unsoundness); over-long lengths are `OOB`.
8. Heap (`vec_alloc` shape): `malloc(n * sizeof(uint32_t))`,
   only `v[i]` for `0 <= i < n`, `free(v)` exactly once on every path
   (missing-`free` / double-`free` rejected), no escape, single live
   allocation per function. The block is a value + affine token
   (`Vec32.freed`), not an address.

## Admitted CIR ops (raw CIRGen shape)

`cir.func`, `cir.alloca`/`load`/`store` (functionalizable shape),
`cir.cast` (int/bool), `cir.binop`/`cmp`/`unary`, `cir.cond_br`
(`cir.br` from `goto` rejected), `cir.return`, `cir.call`
(`@malloc`/`@free` in vec shape only; general calls land in S1),
`cir.const`, `cir.get_member`/`get_element`/`ptr_stride` (bounded),
`cir.if`/`ternary`/`while`/`for` + `cir.condition`/`cir.inc`,
`cir.scope`/`cir.yield`, `cir.const #cir.int<N>`.
`cir.get_global @malloc/@free` plumbing allowed in vec shape only.

## Rejected (loud, with dedicated messages)

`cir.try`/cleanup/EH, vtables, atomics, `volatile`, float,
inline asm, `void*`/int-ptr casts, escaping address-of, unbounded
pointer arithmetic, non-`vec_alloc` heap uses, `setjmp`/`longjmp`,
globals, function pointers, VLAs, variadics, `cir.switch`, `goto`,
bitfields, signed wrapping arithmetic without `nsw` (per-line check).
Coverage: `tests/lean/GoldenPhase6.lean` (18) + `GoldenPhase7.lean` (6).
