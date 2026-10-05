/-
Circe.Validator — the verified gate `validate : RawIR → Option Func`.

Rejects aliasing/out-of-subset inputs loudly with actionable codes
(`alias-reject`, `escape-reject`, `oob-possible`, `out-of-subset`).
Enforces docs/SUBSET.md rules and the
oracle `noalias` requirement, mapping the admitted corpus shapes to
their canonical `Func`s (the only `Func`s `Emit` handles). Anything else
is rejected with a precise code + message (golden-tested in
`tests/lean/GoldenPhase4.lean`, `GoldenPhase6.lean`, `GoldenPhase7.lean`,
`GoldenCalls.lean`).

Check order (first hit wins — rejection codes are priority-ordered):
1. oracle wiring (fact must name this function);
1b. N4d-iv-b2 composer pin (a text calling `_M_realloc_insert` /
   `emplace_back` / `push_back` is multi-call growth composition,
   deferred to b2 — actionable message before any other gate);
2. forbidden constructs (EH, int↔ptr casts, `void*`, volatile/atomics,
   float, `setjmp`/`longjmp`, globals,
   function pointers, VLAs, variadics, cleanup regions (`cir.cleanup`),
   trap (`cir.trap`), `goto` (`cir.br`),
   bitfields, signed wrapping arithmetic without `nsw` — all `outOfSubset`;
   `switch` is shape-aware (the admitted `cls` lowering passes, all other
   `switch` uses are `outOfSubset`);
   heap (`malloc`/`free`/`realloc`) and calls are shape-aware (see step 5):
   the admitted `vec_alloc` / `vec_copy_sum` / `vec_alloc_u64` /
   `vec_realloc` (M1c) shapes pass (M1d: each with `free <= expected`:
   leak is forgetting a value, sound),
    all other heap/call uses are
   `outOfSubset` with dedicated messages (double-`free`,
   `realloc`-shape, heap-shape, calls);
3. pointer discipline (`aliasReject`: raw pointer without `__restrict__`
   and without the C++ single-reference triple (N2c carve-out: the single
   live array of a recovered reader shape — `recoveredNoalias` —
   recovers noalias from construction instead of attr text; N4d-iv-b1
   carve-out: borrowed erased-offset `int*`/`s8*`/`void*` params inside
   a pinned growth-leaf shape — `isVecGrowErasedParam` — need no
   uniqueness since the value model erases them to `u64` offsets or
   drops them), oracle
   verdict other than `noalias` with live oracle-governed pointer params
   (same N2c carve-out), or writer+reader ambiguity — two or more live
   oracle-governed pointer params outside the `choose` borrow-return
   shape);
5. shape admission (canonical `Func` or a precise code: `escapeReject`
   for non-`choose` pointer returns (borrow-after-free when a heap
   `free`/`delete` is present, escaping-borrow when there are no pointer
   inputs at all), `oobPossible` for unbounded
   `ptr_stride`, `outOfSubset` otherwise, including misshapen struct
   uses outside the S2 `translate` shape, the M2a method shapes, and
   the M2b `Acc` leaf shapes, the M2b entry shape (with its
   `cleanup`/`trap` exemption), the N4d-iv-b1 growth-leaf shapes (with
   the dtor `cleanup`-only exemption — no `trap`), and by-value struct
   params stuck in the deferred `coerce` lowering).
Aggregator: text predicates live in `Circe.Validator.Features`, shapes in `Shapes` / `GrowLeaves`, the gate in `Gate`.
-/
import Circe.Validator.Features
import Circe.Validator.Shapes
import Circe.Validator.GrowLeaves
import Circe.Validator.Gate
