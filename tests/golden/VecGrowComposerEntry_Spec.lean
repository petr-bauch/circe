-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same `Base` op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base
import Circe.Emit.VecGrow
import Circe.Emit.VecCompose

/-- C++ signature: `_Z12vec_push_sumv()` runs the closed push/read/sum script (three `push_back`, three `operator[]`, two adds, destructor).
    Base body reference: the delegation itself (cf. emitted `_Z12vec_push_sumv_fwd`,
    `vecPushSumEntryFwd`). -/
def _Z12vec_push_sumv_spec_fwd : Result Value :=
  vecPushSumEntryFwd

/-- Edge cases: the single closed run `1 + 2 + 3 = 6` (frozen by evaluating `vecPushSumEntryFwd`). -/
def _Z12vec_push_sumv_spec_edges : List (Unit × Result Value) :=
  [((), .ok (.i32 (BitVec.ofNat 32 6)))]

/-- Mirror-agreement entry: the stub mirror agrees with the verified forward on every edge. -/
def _Z12vec_push_sumv_spec_check : Bool :=
  _Z12vec_push_sumv_spec_edges.all fun t =>
    (repr (_Z12vec_push_sumv_spec_fwd)).pretty == (repr t.2).pretty
