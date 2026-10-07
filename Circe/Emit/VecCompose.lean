/-
Circe.Emit.VecCompose — N4d-iv-b2 `std::vector<int32_t>` growth
composers: `_M_realloc_insert` (this slice), then `emplace_back`,
`push_back`, and the `vec_push_sum` entry. Each composer is a
`Prog`-level `Func` over the frozen b1 leaves (no inlining: every
corpus `cir.call` to a growth leaf is a `callRet` into the leaf's
canonical `Func`, resolved by name in `evalProgStmt`).

Value model: inherited from `Circe.Emit.VecGrow` (`stdVecOwned`
triples, iterators as `u64` offsets). The two composer-only pure
expression forms (`vgrowSetLen`, `u64ofI64` — see `Circe.CoreIR`)
appear only here, never in leaf bodies.
Aggregator: the shared prelude lives in `Circe.Emit.VecCompose.Base`, composers in `Realloc` / `Emplace` / `Entry` / `Reserve`.
-/
import Circe.Emit.VecCompose.Base
import Circe.Emit.VecCompose.Realloc
import Circe.Emit.VecCompose.Emplace
import Circe.Emit.VecCompose.Entry
import Circe.Emit.VecCompose.Reserve
import Circe.Emit.VecCompose.Insert
import Circe.Emit.VecCompose.Erase
