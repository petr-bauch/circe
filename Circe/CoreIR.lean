/-!
Circe.CoreIR — verified core IR for the Ownable-C subset.

`CoreIR` is the trust boundary output: unverified parser text can never
reach `Emit` without passing `validate : RawIR → Option Func`.
Pointers do not appear as values; they become ownership roles
(`BorrowRole`), per docs/SUBSET.md and docs/PIPELINE.md.
-/

/-- C types admitted (see docs/SUBSET.md). Widths are in bits. -/
inductive CType : Type
  | void
  | bool
  | i (w : Nat)
  | u (w : Nat)
  | array (t : CType) (n : Nat)
  | struct (name : String) (fields : List CType)
  | vecBlock

/-- Ownership role of a function parameter or return. `mutBorrow` is a
    `T *__restrict` param unique for its region; `sharedBorrow` is a
    `const T *` with a length param (pure copy semantics). -/
inductive BorrowRole : Type
  | owned
  | mutBorrow (region : Nat)
  | sharedBorrow
  deriving DecidableEq, Repr

/-- A function parameter: name, type, and ownership role. -/
structure Param : Type where
  name : String
  ty : CType
  role : BorrowRole

/-- Literals of the Phase 3–4 fragment. Integer width is checked against the
    context `CType` by `validate`; `Eval` interprets `i32` as `Value.i32`,
    `u32` as `Value.u32`, `i64` as `Value.i64`, `u64` as `Value.u64`,
    and `b` as `Value.b`. -/
inductive CLit : Type
  | i32 : BitVec 32 → CLit
  | u32 : BitVec 32 → CLit
  | i64 : BitVec 64 → CLit
  | u64 : BitVec 64 → CLit
  | b : Bool → CLit
  deriving DecidableEq, Repr

/-- C expressions for the admitted fragment. `add` is signed `nsw`-checked
    addition (`cir.add nsw`, width-polymorphic over the `Value` tags:
    `i32` via `checkedAddI32`, `i64` via `checkedAddI64` — S3b);
    `uadd` is wrapping unsigned addition (plain `cir.add`, over
    `u32`/`u64`); `usub` is wrapping unsigned subtraction (plain
    `cir.sub` on unsigned, over `u32`/`u64` — N4d-iv-b1: `_M_check_len`
    length arithmetic, iterator `miEl`, `back`); `s64diff` is the fused
    `cir.ptr_diff` over `s32` (bit-exact `u64` subtraction delivered as
    `i64` — N4d-iv-b1: iterator `mi`, whose `s64` result the caller
    casts back to `u64`); `tif c t e` is the pure ternary
    (`cir.ternary`: `c` must evaluate to a `b`, otherwise `AssertFail`
    — N4d-iv-b1: `_M_check_len` length pick); `umul` is wrapping unsigned multiplication (plain
    `cir.mul` on unsigned: C unsigned arithmetic wraps, never fails);
    `ult` is unsigned comparison (`cir.cmp lt` on unsigned);
    `ueq` is width-polymorphic bit equality (`cir.cmp eq` compares
    bits regardless of signedness, so `u32`/`u64`/`i32`/`i64` pairs
    are all defined; mixed widths are `AssertFail`);
    `une` is width-polymorphic bit inequality (the `ueq` twin:
    `cir.cmp ne` — N4d-iv-b2 fuses the emplace raw-pointer guard
    to `len ≠ cap` over `u64` words);
    `idx a i` is bounded indexing (`cir.ptr_stride` + `cir.load`).
    `idxi a i` is `i32`-flavored bounded indexing over the same
    `arr32` word list (`cir.get_element` with a `u64` index, as in
    `std::array<int32_t, N>` reads — N4d; `OOB` off the end, mirroring
    `idx`).
    `optHas o` reads the engaged bit of `std::optional<int32_t>`
    `o` (`_M_is_engaged` fused: `o` must be an `optVal`); `optGet o`
    reads the payload word (`_M_get` fused: engaged `optVal` delivers
    the word, disengaged is `AssertFail` — the `cir.unreachable`
    assert made loud).
    `spanLen s` reads the extent of `std::span<const int32_t>` `s`
    (`size` / `_M_extent` fused: `s` must be a `spanVal`, delivered
    as a `u64` word); `spanAt s ie` is bounded indexing over the
    reified words (`operator[]` fused: `ie` must be a `u64`, `OOB`
    off the end, mirroring `idx`).
    `stdVecLen s` reads the length of `std::vector<int32_t>` `s`
    (`size` fused: the `_M_finish` / `_M_start` loads + `ptr_diff` +
    `cast` fuse into the read — `s` must be a `stdVecVal`, delivered
    as a `u64` word); `stdVecAt s ie` is bounded indexing over the
    reified words (`operator[]` fused: `ie` must be a `u64`, `OOB`
    off the end, mirroring `spanAt`).
    Owned-triple operations (N4d-iv-b1: `std::vector<int32_t>` growth
    leaves over `stdVecOwned` — the uniquely-owned heap triple
    `(buf, len, cap)` with `buf` a live-or-consumed `Vec32` block):
    `vgrowLen s` / `vgrowCap s` project the length / capacity as a
    `u64` word (`s` must be a `stdVecOwned`); `vgrowAt s ie` reads
    the word at `u64` offset `ie` (`OOB` at or past the length);
    `vgrowNew ce` allocates a fresh zeroed `cap`-word buffer with
    length `0` (`ce` must be a `u64`; `_M_allocate` fused — the
    `n == 0` null branch coincides with the empty triple under the
    null-iff-`cap == 0` convention, so both branches build the same
    value).
    Composer-only pure operations (N4d-iv-b2: `_M_realloc_insert` /
    `emplace_back` growth composition over the frozen b1 leaves —
    these never appear in leaf bodies, only in composer `Func`s):
    `vgrowSetLen s e` rebuilds the owned triple `s` with length `e`
    (same buffer and capacity; `s` must be a `stdVecOwned`, `e` a
    `u64` — the `_M_start` / `_M_finish` / `_M_end_of_storage`
    header stores fused, the pointer computations dropped since the
    buffer identity and capacity already thread through the fresh
    triple); `u64ofI64 e` reinterprets an `i64` word as `u64`
    (same 64 bits retagged; `e` must be an `i64` — the
    `cir.cast integral s64 -> u64` on the `mi` difference fused).
    `fget o f` is struct field projection (`cir.get_member` + `cir.load`
    fused: `o` must be a `structVal`, `f` one of its fields); `pmk x y`
    builds the S2 `Point` value from two `i32` field exprs (field-wise
    update functionalized: `q.x = …; q.y = …; return q`).
    `boxNew e` is `new Box{…}` (`cir.call @_Znwm` + bitcast + field
    store fused: `e` must be an `i32`); `boxGet b` is `p->x`
    (`cir.get_member` + `cir.load` fused: `b` must be a `boxVal`;
    use-after-`delete` is `AssertFail`).
    `viewLen s` reads the length of `std::string_view` `s`
    (`begin`/`end` fused: `s` must be a `viewVal`, delivered as a
    `u64` word); `viewAt s ie` is bounded indexing over the reified
    bytes (`ie` must be a `u64`, `OOB` off the end, mirroring
    `spanAt` — the `s8i` load + `s8i -> s32i` sext fuse into the
    read, delivered as a sign-extended `i32`).
    Each constructor requires per-op `Eval`/`Emit` lemmas before admission
    (see docs/PIPELINE.md). -/
inductive CExpr : Type
  | lit : CLit → CExpr
  | var : String → CExpr
  | add : CExpr → CExpr → CExpr
  | uadd : CExpr → CExpr → CExpr
  | usub : CExpr → CExpr → CExpr
  | s64diff : CExpr → CExpr → CExpr
  | tif : CExpr → CExpr → CExpr → CExpr
  | umul : CExpr → CExpr → CExpr
  | neg : CExpr → CExpr
  | sdiv : CExpr → CExpr → CExpr
  | ult : CExpr → CExpr → CExpr
  | ueq : CExpr → CExpr → CExpr
  | une : CExpr → CExpr → CExpr
  | idx : String → CExpr → CExpr
  | optHas : String → CExpr
  | optGet : String → CExpr
  | spanLen : String → CExpr
  | spanAt : String → CExpr → CExpr
  | viewLen : String → CExpr
  | viewAt : String → CExpr → CExpr
  | stdVecLen : String → CExpr
  | stdVecAt : String → CExpr → CExpr
  | vgrowLen : String → CExpr
  | vgrowCap : String → CExpr
  | vgrowAt : String → CExpr → CExpr
  | vgrowNew : CExpr → CExpr
  | vgrowSetLen : String → CExpr → CExpr
  | u64ofI64 : CExpr → CExpr
  | idxi : String → CExpr → CExpr
  | vnew : CExpr → CExpr
  | vget : String → CExpr → CExpr
  | boxNew : CExpr → CExpr
  | boxGet : String → CExpr
  | fget : String → String → CExpr
  | pmk : CExpr → CExpr → CExpr
  deriving DecidableEq, Repr

/-- Minimal statement language. `let_`/`assign` bind pure expressions and
    `return_` returns one; `if_` branches on a `Value.b` condition; `while_`
    is fuel-bounded (see `EVAL_FUEL`: loops must terminate within
    `EVAL_FUEL` iterations; exhaustion reports `AssertFail`).
    `break_`/`continue_` (S3a) are loop-scoped: `break_` exits the
    innermost `while_`, `continue_` starts its next iteration; outside a
    loop they are `AssertFail` (and `validate` admits them only in the
    exact `skip_sum` shape, so this is incompleteness, never unsoundness).
    `callRet dst f args` binds `dst` to the return value of the program
    function `f` applied to the values of `args` (S1: DAG calls into
    call-free leaves, evaluated by `evalProgStmt` in `Circe.Eval`;
    `call` stays a legacy `fellThrough` stub, never produced by
    `validate`). `callProg dst f args` is the depth-n twin of
    `callRet` (N4d-iv-b2: composer calls composer — emplace calls
    `_M_realloc_insert`, push_back calls emplace, entry calls
    push_back): the callee runs under the full program evaluator
    (`evalProgFunc` / `memEvalProgFunc`, same fuel), so arbitrarily
    deep `Prog` call DAGs evaluate; leaf calls stay `callRet`.
    Heap block statements: `vset`/`vfree` thread `Vec32` /
    `Vec64` values with an affine token; `vrealloc vec m` (M1c) resizes
    the named block to `m` words via `vecRealloc` (prefix preserved,
    growth zero-filled, never fails). `boxFree box` (M2c) consumes the
    named box via `boxFree` (double-`delete` is `AssertFail`).
    `cleanup body` (M2b) sequences a
    destructor-guarded scope: the body runs, then the `cleanup normal`
    region (a trivial-dtor call, a no-op at validation, so `cleanup`
    evaluates exactly its body; the trailing `cir.trap` marks the
    unreachable exceptional path and has no model).
    Owned-triple statements (N4d-iv-b1): `vgrowSet t ie ve` stores
    the `i32` word `ve` at `u64` offset `ie` of the `stdVecOwned`
    triple `t` (`construct` fused: use-after-free is `AssertFail`,
    offset at or past the capacity is `OOB` — the slot must be live
    storage, mirroring `vset`); `vgrowFree t` consumes the triple's
    buffer (`_M_deallocate` / dtor fused: double-`free` is
    `AssertFail`, mirroring `vfree`); `fail` is the loud abort
    (noreturn-throw call sites fused: `_M_check_len`'s
    `length_error`, `new_allocator::allocate`'s `bad_alloc` /
    `bad_array_new_length` — hitting it is `AssertFail`, never a
    silent model). -/
inductive CStmt : Type
  | skip
  | seq (a b : CStmt)
  | cleanup (body : CStmt)
  | let_ (name : String) (ty : CType) (val : CExpr)
  | assign (name : String) (val : CExpr)
  | vset (vec : String) (idx val : CExpr)
  | vrealloc (vec : String) (newSize : CExpr)
  | vfree (vec : String)
  | boxFree (box : String)
  | vgrowSet (t : String) (idx val : CExpr)
  | vgrowFree (t : String)
  | fail
  | if_ (cond : CExpr) (then_ else_ : CStmt)
  | while_ (cond : CExpr) (body : CStmt)
  | break_
  | continue_
  | call (func : String) (args : List String)
  | callRet (dst func : String) (args : List String)
  | callProg (dst func : String) (args : List String)
  | return_ (val : CExpr)

/-- A validated function: name, params, return type, and body. -/
structure Func : Type where
  name : String
  args : List Param
  ret : CType
  body : CStmt
