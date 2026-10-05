-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same `Base` op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base
import Circe.Emit.VecGrow
import Circe.Emit.VecCompose

/-- C++ signature: `_ZNSt6vectorIiSaIiEE9push_backEOi(t, x)` forwards to `emplace_back` (the reference result is discarded; the C++ `void` functionalizes as triple threading).
    Base body reference: the delegation itself (cf. emitted `_ZNSt6vectorIiSaIiEE9push_backEOi_fwd`,
    `stdVecPushBackFwd`). -/
def _ZNSt6vectorIiSaIiEE9push_backEOi_spec_fwd (b : Vec32) (len cap : Nat) (x : BitVec 32) : Result Value :=
  stdVecPushBackFwd b len cap x

/-- Edge cases: fast append, slow realloc-insert, `check_len` failure (frozen by evaluating `stdVecPushBackFwd`). -/
def _ZNSt6vectorIiSaIiEE9push_backEOi_spec_edges : List ((Vec32 × Nat × Nat × BitVec 32) × Result Value) :=
  [(((⟨[(0 : BitVec 32)], false⟩, 0, 1, 5)), .ok (.stdVecOwned ⟨[(5 : BitVec 32)], false⟩ 1 1)),
   (((⟨[], false⟩, 0, 0, 5)), .ok (.stdVecOwned ⟨[(5 : BitVec 32)], false⟩ 1 1)),
   (((⟨[], false⟩, stdVecMaxDiff, stdVecMaxDiff, 5)), .error .AssertFail)]

/-- Mirror-agreement entry: the stub mirror agrees with the verified forward on every edge. -/
def _ZNSt6vectorIiSaIiEE9push_backEOi_spec_check : Bool :=
  _ZNSt6vectorIiSaIiEE9push_backEOi_spec_edges.all fun t =>
    match t with
    | ((b, len, cap, x), expected) =>
      (repr (_ZNSt6vectorIiSaIiEE9push_backEOi_spec_fwd b len cap x)).pretty == (repr expected).pretty
