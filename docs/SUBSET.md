# Circe — Admitted Subset (normative)

Anything not listed here is rejected by `validate` with a precise code:
`alias-reject`, `escape-reject`, `oob-possible`, `out-of-subset`.
In-subset divergence is P0; out-of-subset must reject loudly.

## Types

`void`, `_Bool`, `i8/i16/i32/i64`, `u8/u16/u32/u64` (proved:
loop-free `i32`/`u32` throughout plus 64-bit `add64`/`addu64` per
`ROADMAP.md` S3b and the single-block `u64` heap shape
(`vec_alloc_u64`, M1b); 8/16-bit promote to `i32` in CIRGen and are
rejected with the promotion message; 64-bit loops/arrays/structs and
multi-block `u64` heaps are future work), `T*` (disciplined only, see
below), arrays via length-paired params, structs by value (S2: `Point
{ i32 x, y }` only; no bitfields).
No `void*`, no int↔ptr casts, no `volatile`/`_Atomic`,
no unions/variadics/VLAs.

## Statements / expressions

Functions, locals, `if`/`while`/`for`/`do`, `return`,
`break`/`continue` (S3a: `skip_sum` shape only — single bounded `u32`
loop, `continue` at `i == 2`, `break` at `i == 8`), nested loops
(S3a: `nested_sum` shape only), early return in loops (S3a: `find_eq`
shape only), `switch` (S3a: `cls` shape only — equality cases on
`0`/`1` + `default`, every case a bare const `return`).
int arithmetic/logic/comparison, int↔int and bool casts,
disciplined `&`/`*`, array indexing `a[i]` with length param,
struct field access (S2: `translate` shape — by-value `Point`
reads `p.x`/`p.y`, `nsw` field adds, by-value `Point` return).
Uniquely-owned heap, `u32`-only (`vec_alloc` shape) or `u64`-only
(`vec_alloc_u64` shape, M1b monomorphized mirror): `malloc(n *
sizeof(uint32_t))` / `malloc(n * sizeof(uint64_t))`
with same-function length `n`, bounded `v[i]`, at most one `free(v)`
(leak allowed, M1d; double-`free` rejected)
(`vec_alloc` / `vec_alloc_u64` shapes) or two `malloc`s + at most two `free`s
with a fill/copy/sum discipline (M1a `vec_copy_sum` shape, `u32`-only:
both blocks live at once, disjoint by construction) or one `malloc` +
one `realloc` (to `2*n`) + at most one `free` with a fill / fill-extension /
sum discipline (M1c `vec_realloc` shape, `u32`-only: growth preserves
the `min(old, new)` prefix, zero-fills growth, never fails; the
`realloc(p, 0)` / `realloc(NULL, n)` spellings are rejected loudly).
No `goto` (`cir.br` is matched line-aware so `cir.break` never trips
it), `setjmp`, non-lowerable `switch`, no function pointers, no other
heap shapes, read-only `const`
globals only. Calls: S1 DAG into admitted leaves (recursion rejected).

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
8. Heap (`vec_alloc` / `vec_copy_sum` / `vec_alloc_u64` / `vec_realloc`
    shapes):
   `malloc(n * sizeof(uint32_t))` / `malloc(n * sizeof(uint64_t))`,
   only `v[i]` for `0 <= i < n`, every block freed at most once on
   every path (M1d: leak is forgetting a value, sound; double-`free`
   rejected; more `free`s than `malloc`s is double-`free`), no escape.
   `vec_alloc`: single live `u32` allocation; `vec_alloc_u64` (M1b):
   single live `u64` allocation (monomorphized mirror, no `Vec α`
   polymorphism; mixed-width access is `AssertFail` per S3b policy);
   `vec_copy_sum` (M1a): two live `u32`
   allocations, fill `a` / copy `a` into `b` / sum `b`, `free(a)` then
   `free(b)` (each at most once; leak allowed, M1d) — disjoint by
   construction (two `malloc` results).
   `vec_realloc` (M1c): one live `u32` allocation grown by a single
   `realloc` to `m = n + n`, fill `[0,n)` / fill extension `[n,m)` /
   sum `[0,m)`, at most one `free` (leak allowed, M1d) — prefix preserved, growth zero-filled,
   never fails (no OOM path); `realloc(p, 0)` / `realloc(NULL, n)`
   spellings rejected (use `free` / `malloc` directly). Blocks
   are values + affine tokens (`Vec32.freed` / `Vec64.freed`), not addresses.
9. DAG calls (S1): callers target admitted call-free leaves only
   (`add`, `sum_array`); exact caller shapes (`add_caller`:
   three `i32` + two `@add` sites; `sum_caller`: `(ptr, n)` +
   one `@sum_array` site). Self-calls (recursion), unknown callees,
   and misshapen callers are rejected. DAG by construction: leaves
   exclude calls, callers only target leaves, so no cycle is
   expressible. Semantics: `callRet dst f args` binds `dst` to the
   callee return (`evalProgStmt` dispatches to `evalFuncFuel` at the
   same fuel; errors propagate).
10. Struct-by-value (S2): `translate` shape only — by-value `Point`
    + two `i32` deltas, `Point` return; `cir.get_member` reads of
    `x`/`y`, `nsw` field adds, no calls/control-flow/heap/indexing.
    Semantics: `fget o f` projects a `structVal` field, `pmk x y`
    builds the `Point` value (field-wise update functionalized).
    Misshapen struct uses (wrong arity, struct + call, passthrough,
    `get_member` on non-structs) are rejected.
11. Control flow (S3a): exact shapes only —
    `nested_sum` (two `u32` bounds, nested `cir.for`, wrapping
    `s += i * j`),
    `skip_sum` (one `u32` bound, `cir.break`/`cir.continue` at
    `i == 8`/`i == 2`, wrapping `s += i`; `continue` runs the
    `cir.for` step region, modeled by an explicit increment before
    the signal),
    `find_eq` (`noalias` pointer + length + needle, early `return` in
    a bounded loop; over-long lengths are `OOB` unless an early hit
    fires first),
    `cls` (`cir.switch` with equality cases on `0`/`1` + `default`,
    every case a bare const `return`, lowered to an `if_` chain).
    Semantics: `break_`/`continue_` are loop-scoped `Outcome` signals
    (`broke`/`continued` escaping a body is `AssertFail`); older
    shapes exclude `cir.break`/`cir.continue`/`cir.switch`/`cir.case`
    via `noBreakContinueSwitch`, so a loop-exit can never validate as
    a plain loop. Misshapen uses (break outside loops, non-lowerable
    switches, wrong-signature lowerings, single-return searches) are
    rejected with dedicated messages.
12. Widths (S3b): loop-free 64-bit adds only —
    `add64` (`!s64i` params/return, `cir.add nsw`, checked via
    `checkedAddI64`) and `addu64` (`!u64i`, plain wrapping `cir.add`).
    Semantics: `add`/`uadd`/`umul`/`ult`/`ueq` dispatch on the `Value`
    tags (`i32`/`i64`, `u32`/`u64`); mixed widths are `AssertFail`.
    Misshapen uses (width-mixed adds, `nsw`-less signed-64 arithmetic,
    8/16-bit promotion shapes) are rejected with dedicated messages.

## Admitted CIR ops (raw CIRGen shape)

`cir.func`, `cir.alloca`/`load`/`store` (functionalizable shape),
`cir.cast` (int/bool), `cir.binop`/`cmp`/`unary`, `cir.cond_br`
(`cir.br` from `goto` rejected), `cir.return`, `cir.call`
(`@malloc`/`@free` in the vec/vec2/vec64/vecRealloc shapes only,
`@realloc` in the vecRealloc shape only; `@add`/`@sum_array` in the exact
S1 caller shapes only), `cir.const`, `cir.get_member` (S2 `translate`
shape only: `Point` field reads with `nsw` adds; all other struct
uses rejected), `cir.break`/`cir.continue` (S3a `skip_sum` shape
only), `cir.switch`/`cir.case` (S3a `cls` shape only: equality cases
on pinned consts + `default`, all other switches rejected),
`cir.mul` (plain unsigned, S3a `nested_sum` shape only),
`get_element`/`ptr_stride` (bounded),
`cir.if`/`ternary`/`while`/`for` + `cir.condition`/`cir.inc`,
`cir.scope`/`cir.yield`, `cir.const #cir.int<N>`.
`cir.get_global @malloc/@free` plumbing allowed in vec/vec2/vec64/vecRealloc
shapes only (`@realloc` in vecRealloc only).
64-bit spellings (`!s64i`/`!u64i` + long forms) in the S3b `add64` /
`addu64` shapes only; 8/16-bit spellings always rejected (promotion).

## Rejected (loud, with dedicated messages)

`cir.try`/cleanup/EH, vtables, atomics, `volatile`, float,
inline asm, `void*`/int-ptr casts, escaping address-of, unbounded
pointer arithmetic, non-admitted heap uses, `setjmp`/`longjmp`,
globals, function pointers, VLAs, variadics, non-lowerable
`cir.switch`, `goto` (`cir.br`, matched line-aware so `cir.break`
never trips it), bitfields, signed wrapping arithmetic without `nsw`
(per-line check, `i32` + `i64`).
Coverage: `tests/lean/GoldenPhase6.lean` (18) + `GoldenPhase7.lean` (6)
+ `GoldenCalls.lean` (7) + `GoldenStruct.lean` (5)
+ `GoldenFlow.lean` (10) + `GoldenWidth.lean` (5) + `GoldenVec2.lean` (6)
+ `GoldenVec64.lean` (6) + `GoldenVecRealloc.lean` (7)
+ `GoldenFreeDiscipline.lean` (13).
