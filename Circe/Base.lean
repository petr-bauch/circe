/-
Circe.Base — memory-free value model for the Ownable-C subset (v0.1).

Phase 1 skeleton: `Result` + checked integer ops used by the emitter.
Phase 2 will add overflow-correctness lemmas and struct/array mappings.
No memory model here by design (see docs/OWNERSHIP.md).
-/

/-- Reasons a pure Ownable-C program can fail. UB in the subset maps to
    `Result.err`; out-of-subset/aliasing never reaches Lean (rejected by
    `validate`). -/
inductive Panic : Type
  | Overflow
  | DivZero
  | OOB
  | AssertFail
  | Uninit
  deriving DecidableEq, Repr

/-- Partiality monad for emitted code (`Except` with `Panic` errors). -/
abbrev Result (α : Type) : Type := Except Panic α

/-- Checked signed-32 addition. Phase 1: wraps (two's complement), matching
    CIR `cir.add` without `nsw` checking. Phase 2 tightens this to return
    `.error .Overflow` on signed overflow for `nsw` sites, with a
    correctness lemma against `BitVec`/`Int` specs. -/
def checkedAddI32 (a b : BitVec 32) : Result (BitVec 32) :=
  .ok (a + b)

/-- Checked unsigned-32 addition (wrapping in Phase 1; Phase 2 adds the
    overflow-reporting variant where the C semantics require it). -/
def checkedAddU32 (a b : BitVec 32) : Result (BitVec 32) :=
  .ok (a + b)

/-- Checked signed-32 increment: the `incr` fragment (`*p = *p + 1`). -/
def checkedIncrI32 (a : BitVec 32) : Result (BitVec 32) :=
  checkedAddI32 a 1
