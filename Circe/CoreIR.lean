/-
Circe.CoreIR — verified core IR for the Ownable-C subset (v0.1).

`CoreIR` is the trust boundary output: unverified parser text can never
reach `Emit` without passing `validate : RawIR → Option Func`.
Pointers do not appear as values; they become ownership roles
(`BorrowRole`), per docs/OWNERSHIP.md and PLAN.md §6.
-/

/-- C types admitted in v0.1 (see docs/CIR_SUBSET.md). Widths are in bits. -/
inductive CType : Type
  | void
  | bool
  | i (w : Nat)
  | u (w : Nat)
  | array (t : CType) (n : Nat)
  | struct (name : String) (fields : List CType)

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
    `u32` as `Value.u32`, and `b` as `Value.b`. -/
inductive CLit : Type
  | i32 : BitVec 32 → CLit
  | u32 : BitVec 32 → CLit
  | b : Bool → CLit
  deriving DecidableEq, Repr

/-- C expressions for the admitted fragment. `add` is signed `nsw`-checked
    addition (`cir.add nsw`); `uadd` is wrapping unsigned addition (plain
    `cir.add`); `ult` is unsigned comparison (`cir.cmp lt` on unsigned);
    `idx a i` is bounded indexing (`cir.ptr_stride` + `cir.load`).
    Each constructor requires per-op `Eval`/`Emit` lemmas before admission
    (PLAN.md §6); Phase 4 admits all of the above. -/
inductive CExpr : Type
  | lit : CLit → CExpr
  | var : String → CExpr
  | add : CExpr → CExpr → CExpr
  | uadd : CExpr → CExpr → CExpr
  | ult : CExpr → CExpr → CExpr
  | idx : String → CExpr → CExpr
  deriving DecidableEq, Repr

/-- Minimal statement language. `let_`/`assign` bind pure expressions and
    `return_` returns one; `if_` branches on a `Value.b` condition; `while_`
    is fuel-bounded (see `EVAL_FUEL`: v0.1 loops must terminate within
    `EVAL_FUEL` iterations; exhaustion reports `AssertFail`).
    Phase 3 gave `Eval` semantics to `skip`/`seq`/`let_`/`return_`;
    Phase 4 adds `assign`/`if_`/`while_` with per-op lemmas; `call` stays a
    `fellThrough` stub until function calls land (Phase 5+). -/
inductive CStmt : Type
  | skip
  | seq (a b : CStmt)
  | let_ (name : String) (ty : CType) (val : CExpr)
  | assign (name : String) (val : CExpr)
  | if_ (cond : CExpr) (then_ else_ : CStmt)
  | while_ (cond : CExpr) (body : CStmt)
  | call (func : String) (args : List String)
  | return_ (val : CExpr)

/-- A validated function: name, params, return type, and body. -/
structure Func : Type where
  name : String
  args : List Param
  ret : CType
  body : CStmt
