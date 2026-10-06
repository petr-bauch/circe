/-
Circe.Transfer — M3a per-leaf transfer (`oracleNoalias → memEval = Eval`).

`Circe.Mem` stays below `Emit` (no imports upward); this module joins
them for the M3a fragment (call-free C leaves live in `Mem` already —
`memTransfer_add/incr` — while `sum_array` / `vec_alloc` need the
canonical `Func`s + loop envs from `Emit`). Each proof mirrors the
corresponding `emit_correct` argument step for step, with the memory
side threaded alongside (reads cross-checked, writes lockstepped, loops
re-inducted with `Mem`/`Layout` constant or lockstepped).
Aggregator: `sum_array` and correctness live in `Circe.Transfer.Core`, the remaining transfers in the milestone parts it chains into (`VecLeaves` → `VecHeap` → `Flow` → `Slice` → `Acc` → `GrowLeaves` → `GrowReloc` → `GrowRealloc` → `GrowEmplace` → `GrowEntry`).
-/
import Circe.Transfer.Core
import Circe.Transfer.VecLeaves
import Circe.Transfer.VecHeap
import Circe.Transfer.Flow
import Circe.Transfer.Slice
import Circe.Transfer.Acc
import Circe.Transfer.GrowLeaves
import Circe.Transfer.GrowReloc
import Circe.Transfer.GrowRealloc
import Circe.Transfer.GrowEmplace
import Circe.Transfer.GrowEntry
import Circe.Transfer.GrowReserve
