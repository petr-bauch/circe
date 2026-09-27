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
    `u32`/`u64`); `umul` is wrapping unsigned multiplication (plain
    `cir.mul` on unsigned: C unsigned arithmetic wraps, never fails);
    `ult` is unsigned comparison (`cir.cmp lt` on unsigned);
    `ueq` is unsigned equality (`cir.cmp eq` on unsigned);
    `idx a i` is bounded indexing (`cir.ptr_stride` + `cir.load`).
    `fget o f` is struct field projection (`cir.get_member` + `cir.load`
    fused: `o` must be a `structVal`, `f` one of its fields); `pmk x y`
    builds the S2 `Point` value from two `i32` field exprs (field-wise
    update functionalized: `q.x = …; q.y = …; return q`).
    Each constructor requires per-op `Eval`/`Emit` lemmas before admission
    (see docs/PIPELINE.md). -/
inductive CExpr : Type
  | lit : CLit → CExpr
  | var : String → CExpr
  | add : CExpr → CExpr → CExpr
  | uadd : CExpr → CExpr → CExpr
  | umul : CExpr → CExpr → CExpr
  | ult : CExpr → CExpr → CExpr
  | ueq : CExpr → CExpr → CExpr
  | idx : String → CExpr → CExpr
  | vnew : CExpr → CExpr
  | vget : String → CExpr → CExpr
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
    `validate`). -/
inductive CStmt : Type
  | skip
  | seq (a b : CStmt)
  | let_ (name : String) (ty : CType) (val : CExpr)
  | assign (name : String) (val : CExpr)
  | vset (vec : String) (idx val : CExpr)
  | vfree (vec : String)
  | if_ (cond : CExpr) (then_ else_ : CStmt)
  | while_ (cond : CExpr) (body : CStmt)
  | break_
  | continue_
  | call (func : String) (args : List String)
  | callRet (dst func : String) (args : List String)
  | return_ (val : CExpr)

/-- A validated function: name, params, return type, and body. -/
structure Func : Type where
  name : String
  args : List Param
  ret : CType
  body : CStmt
