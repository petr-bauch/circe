/-
Circe.Parser — unverified, trusted text → `RawIR` front end.

Raw CIRGen output (`cir.func`, `cir.alloca/load/store`, …) is parsed here
into `RawIR`. This module is explicitly *unverified*: soundness comes from
`validate` (Circe.Validator), which gates every path from `RawIR` to
`CoreIR`/`Emit`. Thin and version-gated per pinned CIR SHA
(see docs/PINS.md).
-/

/-- Raw parsed CIR text for one function. Phase 1: opaque blob; Phase 4
    grows this into an operation-level AST mirroring the admitted CIR ops
    in docs/CIR_SUBSET.md. -/
structure RawFunc : Type where
  name : String
  text : String
  deriving DecidableEq, Repr

/-- Raw parsed CIR module: the functions found in one `.cir` file. -/
structure RawIR : Type where
  funcs : List RawFunc
  deriving DecidableEq, Repr

/-- Parse stub: splits input into a single anonymous function blob.
    Real MLIR-text parsing lands in Phase 4 alongside golden tests. -/
def parse (name text : String) : RawIR :=
  { funcs := [{ name, text }] }
