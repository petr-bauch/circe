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

/-- Literals of the Phase 3 fragment. Integer width is checked against the
    context `CType` by `validate` (Phase 4); `Eval` interprets `i32` as
    `Value.i32` and `b` as `Value.b`. -/
inductive CLit : Type
  | i32 : BitVec 32 → CLit
  | b : Bool → CLit
  deriving DecidableEq, Repr

/-- Minimal C expressions for the admitted fragment (Phase 3: `lit`/`var`/
    `add`; extended op-by-op in Phase 4 with per-op `Eval`/`Emit` lemmas). -/
inductive CExpr : Type
  | lit : CLit → CExpr
  | var : String → CExpr
  | add : CExpr → CExpr → CExpr
  deriving DecidableEq, Repr

/-- Minimal statement language. `let_`/`assign` bind pure expressions and
    `return_` returns one; `if_`/`while_` conditions are pure expressions.
    Phase 3 gives `Eval` semantics to `skip`/`seq`/`let_`/`return_` (the
    `add`/`incr` fragment); `if_`/`while_`/`call`/`assign` arrive in Phase 4
    and are `fellThrough` stubs until then. -/
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
