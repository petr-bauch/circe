-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base
import Circe.Emit.VecGrow
import Circe.Emit.VecCompose

/-- C++ signature: `_Z15vec_reserve_sumv()` runs the closed reserve/push/read/sum script (`reserve(10)`, two `push_back`, two `operator[]`, one add, destructor).
    Base body reference: the delegation itself (cf. emitted `_Z15vec_reserve_sumv_fwd`,
    `vecReserveSumEntryFwd`). -/
def _Z15vec_reserve_sumv_spec_fwd : Result Value :=
  vecReserveSumEntryFwd

/-- Edge cases: the single closed run `1 + 2 = 3` (frozen by evaluating `vecReserveSumEntryFwd`). -/
def _Z15vec_reserve_sumv_spec_edges : List (Unit × Result Value) :=
  [((), .ok (.i32 (BitVec.ofNat 32 3)))]

/-- Mirror-agreement entry: the stub mirror agrees with the verified forward on every edge.
    TODO (user): strengthen to the gallery equation `vecReserveSumEntry_correct`
    (proved by hand in `Circe.Specs`). -/
def _Z15vec_reserve_sumv_spec_check : Bool :=
  _Z15vec_reserve_sumv_spec_edges.all fun t =>
    (repr (_Z15vec_reserve_sumv_spec_fwd)).pretty == (repr t.2).pretty
