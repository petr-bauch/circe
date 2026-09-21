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

/-- Minimal statement language for Phase 1. Extended op-by-op in
    Phases 3–4; each new constructor requires per-op `Eval`/`Emit` lemmas
    before admission (PLAN.md §6). -/
inductive CStmt : Type
  | skip
  | seq (a b : CStmt)
  | let_ (name : String) (ty : CType) (val : CStmt)
  | assign (name : String) (val : CStmt)
  | if_ (cond : CStmt) (then_ else_ : CStmt)
  | while_ (cond : CStmt) (body : CStmt)
  | call (func : String) (args : List String)
  | return_ (val : CStmt)

/-- A validated function: name, params, return type, and body. -/
structure Func : Type where
  name : String
  args : List Param
  ret : CType
  body : CStmt
