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
reads `p.x`/`p.y`, `nsw` field adds, by-value `Point` return; M2a:
method-leaf shape — `this` reads `x`/`y`, one `nsw` add, `i32` return).
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
   (C++ M2: `this` / `const&` params carry `nonnull + dereferenceable
   + noundef` instead — `this` cannot carry `restrict` / `noalias`;
   see `ROADMAP.md` M2 and `PINS.md`.)
   (N2c recovery: the single live array of an admitted reader shape
   (`sum` / `sum_caller` / `find_eq`, e.g. `sum_norestrict`) needs
   neither — singleton footprint + read-only CoreIR recover noalias
   from construction; writers and multi-pointer shapes still need
   attr text or a `noalias` verdict.)
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
    Semantics: `add`/`uadd`/`umul`/`ult` dispatch on the `Value`
    tags (`i32`/`i64`, `u32`/`u64`); `ueq` is width-polymorphic bit
    equality (same-width pairs always defined, N4b); mixed widths
    are `AssertFail`.
    Misshapen uses (width-mixed adds, `nsw`-less signed-64 arithmetic,
    8/16-bit promotion shapes) are rejected with dedicated messages.
13. Methods (M2a): exact shapes only —
    `_ZNK5Point3sumEv` leaf (single `this` with the single-reference
    triple, `get_member` reads of `x`/`y`, one `nsw` field add, `i32`
    return; `this` binds the `Point` value, copy semantics) and
    `_Z13point_sum_refRK5Point` entry (single `const&` with the triple,
    exactly one call site to the mangled leaf, `i32` return; S1
    `callRet` discipline with the leaf matched by (mangled) name).
    Semantics: the leaf evaluates `checkedAddI32` on the projected
    fields (`pointSum`); the entry dispatches to the leaf at the same
    fuel via `evalProgFunc`; errors propagate. Method/ctor/dtor defs
    need no oracle facts (uniqueness is the attr triple in the CIR
    text). By-value struct params (the `coerce` alloca + `bitcast`
    lowering) are deferred and rejected with a dedicated message.
    Misshapen uses (unknown callees, calls in the leaf, non-`i32`
    returns, bare pointers without the triple, extra call sites) are
    rejected with dedicated messages.
14. Ctors/dtors (M2b): exact shapes only —
    `_ZN3AccC2Ev` ctor leaf (no CoreIR params; the CIR def takes single
    `this` with the single-reference triple and the `cxx_ctor` marker,
    `get_member` + `cir.const #cir.int<0>` field-init, void return),
    `_ZN3Acc3addEi` method leaf (`this` + one `i32`, `get_member` + one
    `nsw` add, void return; the store-back is functionalized),
    `_ZNK3Acc3getEv` getter leaf (single `this`, `get_member` read with
    no arithmetic, `i32` return; identity),
    `_ZN3AccD2Ev` trivial-dtor leaf (single `this`, `cxx_dtor` marker,
    empty body, void return; no-op identity), and the `_Z7acc_twoii`
    entry (two by-value `i32`s, `i32` return; a `cleanup` scope
    sequencing 1 ctor + 2 `add` + 1 `get` + 1 dtor call closed by the
    unreachable `cir.trap`).
    Semantics: the accumulator state is a single `i32` word threaded
    functionally (`accCtor` = `0`, `accAdd` = checked add, `accGet` /
    `accDtor` = identity, `accTwo` = init + two adds); the entry
    dispatches to the leaves at the same fuel via `evalProgFunc`, with
    `cleanup` evaluating exactly its scope; errors propagate. The
    struct never crosses the boundary (all params/returns are `i32`).
    The int-only entry needs its oracle fact (like every int-only
    func); leaf defs need none (uniqueness is the attr triple).
    `cir.cleanup` / `cir.trap` are admitted only here (exact call
    multiset + no-EH pins); everywhere else they reject loudly.
    Misshapen uses (missing/extra calls, non-trivial dtor bodies,
    wrapping leaf arithmetic, bare pointers without the triple,
    non-zero ctor init) are rejected with dedicated messages.
15. `new` / `delete` (M2c): exact shape only —
    `_Z11box_throughi` (one by-value `i32`, `i32` return: `new Box{x}`
    (4-byte `!u64i` size const + `cir.call @_Znwm` + bitcast + field
    store) + read (`cir.get_member` `x`) + at most one null-guarded
    `cleanup`-scoped sized `cir.call @_ZdlPvm` (M1d: the 1-`new` /
    0-`delete` leak spelling validates to the same body; more
    `delete`s than `new`s is double-`delete`)).
    Semantics: the box is a single `i32` value plus an affine `freed`
    token threaded functionally (`boxNew` never fails, `boxGet` reads
    the value, `boxFree` consumes the token; double-`delete` /
    use-after-`delete` are `AssertFail`); the entry is total
    (`boxThrough` = identity). The box never crosses the boundary
    (param/return are `i32`). The int-only entry needs its oracle
    fact (like every int-only func). The null guard (`cir.cmp ne` vs
    `#cir.ptr<null>` + `cir.if`) is dead (`_Znwm` returns `nonnull`)
    and erased, as is the `cleanup` scope; the gate pins the guard,
    the size const, and the call multiset instead. `cir.cleanup` is
    admitted here (exact 1 + 1 multiset + guard + no-EH pins) and in
    M2b; `cir.trap` only in M2b; everywhere else both reject loudly.
    Misshapen uses (missing `new`, unguarded `delete`, double-
    `delete`, wrong size const) are rejected with dedicated messages.
16. Overloads + namespaces (N4a): mangling-scheme match, not an
    admit-list — the gate pins arity/types and is name-agnostic
    (`isAdd3Shape` / `isOverloadCallerShape` never inspect the
    spelling):
    `_Z3addii` 2-`i32` leaf (body-identical to `add`: two `i32`,
    `cir.add nsw`, `i32` return; renamed-leaf proofs reuse
    `evalFuncFuel_addAt` / `memEvalFuncFuel_addAt`),
    `_Z3addiii` 3-`i32` leaf (three `i32`, two threaded `nsw` adds
    via an explicit `let_` temp, `i32` return),
    `_Z7use_addii` entry (two `i32`, exactly one call site to the
    2-`i32` overload, `i32` return),
    `_ZN2ns3addEii` namespaced leaf (body-identical to `add` under
    the nested-name scheme) and `_Z10use_ns_addii` entry (two
    `i32`, exactly one call site to the namespaced leaf, `i32`
    return).
    Semantics: `add3` threads two `checkedAddI32` binds (ok/err
    lemmas `add3Fwd_ok/err`); entries dispatch to their leaf at the
    same fuel via `evalProgFunc` (`useAddFwd_is_call` /
    `useNsAddFwd_is_call`); errors propagate. Int-only leaves and
    entries need explicit oracle facts (pure, so the `unknown`
    verdict is unchecked — but the wiring entry is still required).
    Misshapen uses (calls to unknown mangled callees, wrong-arity
    calls into known leaves, double calls, local arithmetic beside
    the call) are rejected with dedicated messages
    (`callsOverloadWrongShape`).
17. Move + RAII (N4b): exact shapes only —
    `_Z8move_intii` (trivial move: `std::move` on `int` erases to a
    copy, body-identical to `add`; the source stays live),
    `_ZN3AccC2EOS_` move-ctor leaf (two single-reference params,
    `cxx_ctor<…, move>` marker, `get_member` + `cir.const 0`
    source-zeroing store, void return; destination takes the source
    word, destination storage never read),
    `_Z8move_accii` entry (two `i32`, nested `cleanup` scopes closed
    by `cir.trap`, exact call multiset 1 default ctor + 1 move ctor
    + 2 `add` + 1 `get` + 2 dtors; the move-ctor `o.s = 0` store is
    threaded as an `assign`, so post-move reads see the zeroed word
    and no textual no-read pin is needed),
    `_Z11scope_earlyii` entry (two `i32`, `cleanup`/`trap` scope,
    exact call multiset 1 ctor + 2 `add` + 2 `get` + 1 dtor, one
    `cir.cmp eq` + `cir.if` early return; both scope-exit dtors are
    no-ops so both returns are direct).
    Semantics: `accMoveCtor` is the source word; `moveAcc` threads
    ctor-init + two checked adds with the zeroing `assign`;
    `scopeEarly` takes the early `get` on `a == b` else the second
    checked add + `get`; errors propagate. `ueq` is
    width-polymorphic bit equality (`cir.cmp eq` is signedness-blind;
    mixed widths are still `AssertFail`). The int-only entries need
    explicit oracle facts; the move-ctor leaf validates under a
    synthetic fact (single-reference params). Misshapen uses (wrong
    call multisets, `cir.cmp` other than `eq`, `if` outside the
    exact early-return shape, move-assign `aSEOS_`, copy
    ctor/assign) are rejected with dedicated messages.
18. Templates, monomorphized (N4c): no generic reasoning — each
    instantiation is its own shape, mirroring the `Vec32`/`Vec64`
    precedent:
    `_Z4taddIiET_S0_S0_` (32-bit `tadd` monomorph: two `i32`,
    `cir.add nsw`, `i32` return; body-identical to `add`, so zero
    gate change — the gate is name-agnostic),
    `_Z4taddIlET_S0_S0_` (64-bit monomorph: two `i64`, `cir.add nsw`,
    `i64` return; body-identical to `add64`),
    `_Z10use_tadd32ii` entry (two `i32`, exactly one call site to the
    32-bit monomorph, `i32` return),
    `_Z10use_tadd64ll` entry (two `i64`, exactly one call site to the
    64-bit monomorph, `i64` return).
    Explicit instantiation definitions keep the monomorphs as (weak)
    symbols; implicit-only instantiation inlines away at `-O1` and the
    native diff driver could not call the leaves directly. The
    `weak_odr` linkage parses like `linkonce_odr` (linkage never
    gates). Int-only leaves and entries need explicit oracle facts.
    Misshapen uses (wrong-arity calls into known monomorphs, double
    calls, local arithmetic beside the call, 64-bit monomorph called
    at 32-bit width) are rejected with dedicated messages
    (`callsTemplateWrongShape`).
19. `std::array<int, 4>` reads (N4d-i): each monomorph is its own
    shape (the N4c precedent); the depth-2 call chain
    (`array_sum` → `operator[]` → `_S_ref`) functionalizes with one
    fused edge (the M2b leaf-fusion precedent):
    `_ZNSt14__array_traitsIiLm4EE6_S_refERA4_Kim` unchecked-index
    leaf (single `const&` to the raw 4-word `i32` array with the
    single-reference triple, `u64` index, pointer-to-`i32` return,
    one `cir.get_element`),
    `_ZNKSt5arrayIiLm4EEixEm` entry (single `const&` to the array
    object with the single-reference triple, `u64` index,
    pointer-to-`i32` return, one `_M_elems` `cir.get_member` +
    exactly one call site to the `_S_ref` leaf; the projection +
    call fuse into the `idxi` read),
    `_Z9array_sumRKSt5arrayIiLm4EE` entry (single `const&` with the
    single-reference triple, `i32` return, exactly four call sites
    to `operator[]` at const `u64` indices 0–3 functionalized as
    `let_`-bound words, three threaded `nsw` adds).
    Semantics: `arrayRef`/`arrayAt` read the word at a live `u64`
    index (`OOB` off the end — unchecked indexing is UB, so the
    model reports it); `arraySum` threads three `checkedAddI32`
    (ok needs all three certs, each-site error propagates).
    `idxi` is the `i32`-flavored bounded index (`cir.get_element`
    with a `u64` index over an `arr32` word list, mirroring `idx`).
    All three validate under synthetic facts (single-reference
    params). Misshapen uses (double calls into `_S_ref`, extra
    indexing ops beside the call, wrong-arity calls into
    `operator[]`, wrong site counts into the entry, bare array
    pointers without the triple) are rejected with dedicated
    messages (`callsArrayWrongShape`, or `alias-reject`).
    Deferred with pins (`tests/lean/GoldenArray.lean`): `string_view`
    (iterators return raw pointers), `vector` (operator-`new` +
    60-def allocator bloat). (`optional` graduated to item 20;
    only the `value` throw path stays deferred. `span` index-sum
    graduated to item 21 — `-std=c++20` scoped to `span_*` in
    `tools/emit-cir.sh`; only range-for stays out.)
20. `std::optional<int32_t>` guarded deref (N4d-ii): the depth-3
    call chain (`opt_deref` → `operator*` → impl `_M_get` →
    payload `_M_get`) functionalizes with fused edges (the N4d-i
    fusion precedent):
    `_ZNKSt19_Optional_base_implIiSt14_Optional_baseIiLb1ELb1EEE13_M_is_engagedEv`
    engaged-bit leaf (single `const&` to the base-impl object with
    the single-reference triple, `bool` return, the `derived [0]` +
    `get_member [0]` (`_M_payload`) + `base [0]` + `get_member [1]`
    (`_M_engaged`) projection chain),
    `_ZNKSt22_Optional_payload_baseIiE6_M_getEv` leaf (single
    `const&` to the payload-base object with the single-reference
    triple, pointer-to-`i32` return, the `get_member [0]`
    (`_M_payload`) + `get_member [1]` (`_M_value`) projection pair),
    `_ZNKSt8optionalIiE9has_valueEv` entry (single `const&` to the
    optional object with the single-reference triple, `bool`
    return, exactly one call site to the `_M_is_engaged` leaf; the
    `base_class_addr [0]` projection + call fuse into the `optHas`
    read),
    `_ZNKSt19_Optional_base_implIiSt14_Optional_baseIiLb1ELb1EEE6_M_getEv`
    entry (single `const&` to the base-impl object with the
    single-reference triple, pointer-to-`i32` return, exactly two
    call sites — the live payload-`_M_get` call plus the
    `_M_is_engaged` call in the dead assert arm; the dead
    disabled-`__glibcxx_assert` skeleton — single `cir.ternary`
    over a `false` const, one-sided `cir.if`, `cir.unreachable` in
    a do-while-false scope — is dropped downstream and pinned by
    the gate, so a live-assert variant rejects loudly),
    `_ZNKRSt8optionalIiEdeEv` leaf (single `const&` to the optional
    object with the single-reference triple, pointer-to-`i32`
    return, exactly one call site to impl `_M_get`; two call edges
    + the caller-side load fuse into the `optGet` read),
    `_Z9opt_derefRKSt8optionalIiE` entry (single `const&` with the
    single-reference triple, `i32` return, exactly two call sites
    — `has_value` for the guard, `operator*` for the word — the
    one-sided `cir.if` with the deref inside, the live `-1`
    sentinel const plus the stray dead `1` const, dropped
    downstream).
    Semantics: `optHas` reads the engaged bit; `optGet` reads the
    payload word on engaged and reports `AssertFail` on
    disengaged (the `unreachable` assert made loud — the payload
    word of a disengaged optional is unobservable when guarded);
    `optDeref` returns the word on engaged and the `-1` sentinel
    on disengaged. `optVal : Option (BitVec 32)` is the value
    model; memory binds the 2-word `[payload, engaged-as-1/0]`
    block at entry (reads only). `base`/`derived_class_addr` at
    `[0]` erase. All six validate under synthetic facts
    (single-reference params). Misshapen uses (double calls into
    payload `_M_get`, live-assert impl variants, wrong-arity calls
    into `has_value`, bare optional pointers without the triple)
    are rejected with dedicated messages
    (`callsOptWrongShape`, or `alias-reject`).
    Still deferred: `optional::value` (throw path lowers to
    `cir.trap`).
21. `std::span<const int32_t>` index-sum (N4d-iii): the depth-2
    call chain (`span_sum` → `size` → `_M_extent` →
    the `_M_extent_value` load; `span_sum` → `operator[]` → the live
    `size` call in the dead assert arm) functionalizes with fused
    edges (the N4d-ii fusion precedent), captured with `-std=c++20`
    scoped to `span_*` in `tools/emit-cir.sh`:
    `_ZNKSt8__detail16__extent_storageILm18446744073709551615EE9_M_extentEv`
    extent leaf (single `const&` to the extent-storage object with
    the single-reference triple, `u64` return, the single
    `get_member [0]` (`_M_extent_value`) projection with the value
    load, no calls, no control flow),
    `_ZNKSt4spanIKiLm18446744073709551615EE4sizeEv` entry (single
    `const&` to the span object with the single-reference triple,
    `u64` return, exactly one call site to the `_M_extent` leaf;
    the `get_member [1]` (`_M_extent`) projection + call fuse into
    the `spanLen` read),
    `_ZNKSt4spanIKiLm18446744073709551615EEixEm` leaf (the span
    `const&` with the single-reference triple plus the `u64` index,
    pointer-to-`i32` return, exactly one call site — the live
    `size()` call in the dead assert arm — with the dead
    disabled-assert skeleton pinned exactly: single `cir.ternary`
    over three `#false` consts, one `cir.cmp lt`, one `cir.not`,
    one-sided `cir.if`, `cir.unreachable`, `cir.do`/`cir.condition`;
    a variant with the assert enabled, or without it, rejects
    loudly; the live tail — `get_member [0]` (`_M_ptr`) +
    `ptr_stride` + both loads — fuses into the `spanAt` read),
    `_Z8span_sumSt4spanIKiLm18446744073709551615EE` entry (the span
    **by value** — no pointer, no aliasing question on the object
    itself — `i32` return, exactly two call sites: `size` in `cond`,
    `operator[]` in `body`; the single `cir.for` with the `lt`
    comparison, the `u64` increment, and the one `nsw` accumulation
    add; three `cir.const` — the two live `0` inits plus one stray
    dead `i32` `0`, the clang init quirk, dropped downstream).
    Semantics: `spanVal : List (BitVec 32)` is the reified viewed
    words (`sharedBorrow` snapshot, the S1 `sum_array` precedent);
    `spanLen` reads the length, `spanAt` the word at a live `u64`
    index (`OOB` off the end — unchecked indexing is UB, so the
    model reports it); `spanSum` is the checked-add fold from `0`
    over the words (loud err-propagation); memory binds the
    `[len-as-u64] ++ words` block (word0 extent, words 1+i
    elements). The entry validates under ONE explicit oracle fact
    (by value, so no synthetic-fact triple — the M2b int-only-entry
    precedent). Misshapen uses (double calls into `size`,
    live-assert `operator[]` variants, wrong-arity calls into
    `size`, bare span pointers without the triple) are rejected
    with dedicated messages (`callsSpanWrongShape`, or
    `alias-reject`).
    Containment result: index-based `size()`/`operator[]` is IN;
    the range-for form is OUT (it lowers to `begin`/`end`
    iterator calls plus pointer-chasing, outside the admitted call
    shapes — pinned in `tests/lean/GoldenSpan.lean`).
    Still deferred: `string_view` range-for (same iterator reason),
    `vector`.

## Admitted CIR ops (raw CIRGen shape)

`cir.func`, `cir.alloca`/`load`/`store` (functionalizable shape),
`cir.cast` (int/bool), `cir.binop`/`cmp`/`unary`, `cir.cond_br`
(`cir.br` from `goto` rejected), `cir.return`, `cir.call`
(`@malloc`/`@free` in the vec/vec2/vec64/vecRealloc shapes only,
`@realloc` in the vecRealloc shape only; `@add`/`@sum_array` in the exact
S1 caller shapes only; `@_ZNK5Point3sumEv` in the exact M2a entry shape
only; `@_ZN3AccC2Ev` / `@_ZN3Acc3addEi` / `@_ZNK3Acc3getEv` /
`@_ZN3AccD2Ev` in the exact M2b entry shape only (1 + 2 + 1 + 1 sites);
`@_Znwm` / `@_ZdlPvm` in the exact M2c entry shape only (1 + at most 1
sites: leak allowed, double-`delete` rejected);
`@_Z3addii` in the exact N4a `use_add` entry shape only (1 site);
`@_ZN2ns3addEii` in the exact N4a `use_ns_add` entry shape only (1 site);
`@_ZN3AccC2EOS_` in the exact N4b `move_acc` entry shape only (1 site);
`@_Z4taddIiET_S0_S0_` in the exact N4c `use_tadd32` entry shape only
(1 site); `@_Z4taddIlET_S0_S0_` in the exact N4c `use_tadd64` entry
shape only (1 site);
`@_ZNSt14__array_traitsIiLm4EE6_S_refERA4_Kim` in the exact N4d-i
`array_at` entry shape only (1 site);
`@_ZNKSt5arrayIiLm4EEixEm` in the exact N4d-i `array_sum` entry shape
only (4 sites);
`@_ZNKSt19_Optional_base_implIiSt14_Optional_baseIiLb1ELb1EEE13_M_is_engagedEv`
in the exact N4d-ii `opt_has_value` entry shape only (1 site) and in
the dead assert arm of the exact N4d-ii `opt_impl_get` shape;
`@_ZNKSt22_Optional_payload_baseIiE6_M_getEv` in the exact N4d-ii
`opt_impl_get` entry shape only (1 site);
`@_ZNKSt19_Optional_base_implIiSt14_Optional_baseIiLb1ELb1EEE6_M_getEv`
in the exact N4d-ii `opt_deref_op` leaf shape only (1 site);
`@_ZNKSt8optionalIiE9has_valueEv` / `@_ZNKRSt8optionalIiEdeEv` in the
exact N4d-ii `opt_deref` entry shape only (1 + 1 sites)),
`cir.const`, `cir.get_member` (S2 `translate`
shape only: `Point` field reads with `nsw` adds; M2a method-leaf shape
only: single-`this` field reads with one `nsw` add; M2b `Acc` leaf
shapes only: `cxx_ctor` const-`0` init / `add` one-`nsw`-add /
`get` identity read; M2c `box_through` entry shape only: `Box` field
`x` write + read; N4d-i `array_at` entry shape only: one `_M_elems`
projection beside the single `_S_ref` call; N4d-ii `opt_has` leaf
shape only: the `derived [0]` + `_M_payload [0]` + `base [0]` +
`_M_engaged [1]` chain, `opt_get` leaf shape only: the
`_M_payload [0]` + `_M_value [1]` pair, `opt_impl_get` entry shape
only: one live `_M_payload [0]` beside the payload call; all other
struct uses rejected), `cir.break`/`cir.continue` (S3a `skip_sum` shape
only), `cir.switch`/`cir.case` (S3a `cls` shape only: equality cases
on pinned consts + `default`, all other switches rejected),
`cir.mul` (plain unsigned, S3a `nested_sum` shape only),
`get_element` (bounded: the N4d-i `_S_ref` leaf shape only) /
`ptr_stride` (bounded),
`cir.if`/`ternary`/`while`/`for` + `cir.condition`/`cir.inc`
(`cir.if` carries the M2c null guard (`cir.cmp ne` vs
`#cir.ptr<null>`), the N4b early return (`cir.cmp eq` on `i32`
in the exact `scope_early` shape only), the N4d-ii guarded deref
(one-sided with the deref inside, exact `opt_deref` shape only),
and the dead one-sided assert (exact `opt_impl_get` shape only);
`cir.ternary` + `cir.unreachable` + `cir.do`/`cir.condition` in the
exact dead-assert skeleton of `opt_impl_get` only),
`cir.scope`/`cir.yield`, `cir.const #cir.int<N>`
(`#cir.int<4> : !u64i` pinned in the M2c shape; the `-1` sentinel +
stray dead `1` pinned in the exact `opt_deref` shape (2 consts);
three `#false` consts with no `#cir.int` pinned in the exact
`opt_impl_get` shape).
`cir.cleanup.scope` / `cleanup normal` + `cir.trap` in the exact M2b
`acc_two` entry shape only (single `cleanup` scope, exact 1 + 2 + 1 + 1
call multiset, no `cir.try` / `personality` / `cleanup eh` / heap)
and in the exact N4b `move_acc` (nested scopes, exact
1 + 1 + 2 + 1 + 2 call multiset) and `scope_early` (exact
1 + 2 + 2 + 1 call multiset + `cir.cmp eq`/`cir.if`) entry shapes;
`cir.cleanup.scope` / `cleanup normal` (no `cir.trap`) in the exact M2c
`box_through` entry shape only (null-guarded, exact 1 + 1 call
multiset, 4-byte size const, no `cir.try` / `personality` /
`cleanup eh` / C heap).
`cir.get_global @malloc/@free` plumbing allowed in vec/vec2/vec64/vecRealloc
shapes only (`@realloc` in vecRealloc only).
`cir.cast bitcast` (`void` ↔ `Box`) in the M2c shape only.
64-bit spellings (`!s64i`/`!u64i` + long forms) in the S3b `add64` /
`addu64` shapes only (plus the M2c 4-byte `!u64i` size const); 8/16-bit spellings always rejected (promotion).

## Rejected (loud, with dedicated messages)

`cir.try`/cleanup/EH (except the exact M2b `acc_two` entry scope and
the exact M2c `box_through` entry scope),
vtables, atomics, `volatile`, float,
inline asm, `void*`/int-ptr casts, escaping address-of, unbounded
pointer arithmetic, non-admitted heap uses, `setjmp`/`longjmp`,
globals, function pointers, VLAs, variadics, non-lowerable
`cir.switch`, `goto` (`cir.br`, matched line-aware so `cir.break`
never trips it), bitfields, signed wrapping arithmetic without `nsw`
(per-line check, `i32` + `i64`).
Aliasing rejections are per-cause (N2b), not catch-all: writer+reader
(two or more live pointer params outside `choose`, `alias-reject`),
escaping-borrow (pointer return with no pointer inputs,
`escape-reject`), borrow-after-free (`free`/`delete` plus a pointer
return, `escape-reject`); missing `__restrict__`/triple evidence and
inconclusive oracle verdicts keep their `alias-reject` messages, and
the ambiguous-inputs escape keeps the borrow-return `escape-reject`.
Coverage: `tests/lean/GoldenPhase4.lean` (19) + `GoldenPhase6.lean` (18) + `GoldenPhase7.lean` (6)
+ `GoldenCalls.lean` (7) + `GoldenStruct.lean` (5)
+ `GoldenFlow.lean` (10) + `GoldenWidth.lean` (5) + `GoldenVec2.lean` (6)
+ `GoldenVec64.lean` (6) + `GoldenVecRealloc.lean` (7)
+ `GoldenFreeDiscipline.lean` (13) + `GoldenM2Setup.lean` (5)
+ `GoldenMethod.lean` (8) + `GoldenAcc.lean` (12) + `GoldenBox.lean` (9)
+ `GoldenReadOnly.lean` (5) + `GoldenRejectCatalog.lean` (5).
