/-
Circe.Emit.SpecStubs — S4 spec-stub rendering (`out/*_Spec.lean`:
signature + body reference + edge list + prop-test entry).

Pure string functions, one per shape; dispatched by `emitSpec` in
`Circe.Emit` exactly like `emitFunc`.
-/

/-! ## S4 spec stubs (`out/*_Spec.lean`)

Unverified scaffolding, not trusted code: each stub re-states the
function signature, names the `Base`-op body reference (the same body
the emitted forward uses — body identity is the transfer argument in
`docs/VERIFYING.md`), lists edge cases, and provides a `Diff`-style
prop-test entry (`_check : Bool`). The user copies the stub into
`Circe.Specs` (or a per-project spec file) and fills the equation;
the `_check` placeholder states whatever equation is already known
(self-agreement where the spec is still TODO, the real equation for
`sum`/`vec`). Out-of-subset input never reaches here: `emitSpec`
dispatches on `matchFrag`, exactly like `emitFunc`. -/

/-- File header shared by all rendered spec stubs. -/
def emitSpecHeader : String :=
  "-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.\n"
  ++ "-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec\n"
  ++ "-- file) and fill the equation. The `_fwd` mirror below is body-identical\n"
  ++ "-- to the emitted forward (same `Base` op); specs proved against it\n"
  ++ "-- transfer verbatim by body identity (see docs/VERIFYING.md).\n"

/-- Spec stub for the `add` shape. -/
def emitAddSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `int32_t {name}(int32_t a, int32_t b)`.\n"
  ++ s!"    Base body reference: `checkedAddI32` (cf. emitted `{name}_fwd`, `emit_correct_add`). -/\n"
  ++ s!"def {name}_spec_fwd (a b : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  checkedAddI32 a b\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, `INT32_MAX`/`INT32_MIN` boundaries, wrap. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32 × BitVec 32) :=\n"
  ++ "  [(0, 0), (1, 2), (0x7FFFFFFF, 0), (0x7FFFFFFF, 1),\n"
  ++ "   (0x80000000, 0), (0x80000000, 0xFFFFFFFF), (0xFFFFFFFF, 0xFFFFFFFF)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with the `Base` body on every edge.\n"
  ++ "    TODO (user): strengthen to the equation, e.g. ok implies `r = a + b`\n"
  ++ "    with the `nsw` certificate (see `incr_correct`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun p =>\n"
  ++ s!"    (repr ({name}_spec_fwd p.1 p.2)).pretty == (repr (checkedAddI32 p.1 p.2)).pretty\n"

/-- Spec stub for the `incr` shape. -/
def emitIncrSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `void {name}(int32_t *p)` (`*p = *p + 1`, functionalized).\n"
  ++ s!"    Base body reference: `checkedIncrI32` (cf. emitted `{name}_fwd`, `emit_correct_incr`). -/\n"
  ++ s!"def {name}_spec_fwd (p : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  checkedIncrI32 p\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, `INT32_MAX` (overflow), `INT32_MIN`, `-1`. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32) :=\n"
  ++ "  [0, 1, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with the `Base` body on every edge.\n"
  ++ "    TODO (user): strengthen to `incr_correct` (successor + certificate). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun p => (repr ({name}_spec_fwd p)).pretty == (repr (checkedIncrI32 p)).pretty\n"

/-- Spec stub for the 64-bit `add64` shape (S3b). -/
def emitAdd64SpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `int64_t {name}(int64_t a, int64_t b)`.\n"
  ++ s!"    Base body reference: `checkedAddI64` (cf. emitted `{name}_fwd`, `emit_correct_add64`). -/\n"
  ++ s!"def {name}_spec_fwd (a b : BitVec 64) : Result (BitVec 64) :=\n"
  ++ "  checkedAddI64 a b\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, `INT64_MAX`/`INT64_MIN` boundaries, wrap. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 64 × BitVec 64) :=\n"
  ++ "  [(0, 0), (1, 2), (0x7FFFFFFFFFFFFFFF, 0), (0x7FFFFFFFFFFFFFFF, 1),\n"
  ++ "   (0x8000000000000000, 0), (0x8000000000000000, 0xFFFFFFFFFFFFFFFF),\n"
  ++ "   (0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with the `Base` body on every edge.\n"
  ++ "    TODO (user): strengthen to the ok/err equation (see `emit_correct_add64_ok`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun p =>\n"
  ++ s!"    (repr ({name}_spec_fwd p.1 p.2)).pretty == (repr (checkedAddI64 p.1 p.2)).pretty\n"

/-- Spec stub for the 64-bit `addu64` shape (S3b, wrapping). -/
def emitAddu64SpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `uint64_t {name}(uint64_t a, uint64_t b)` (wrapping, never fails).\n"
  ++ s!"    Base body reference: `a + b` (cf. emitted `{name}_fwd`, `emit_correct_addu64`). -/\n"
  ++ s!"def {name}_spec_fwd (a b : BitVec 64) : Result (BitVec 64) :=\n"
  ++ "  .ok (a + b)\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, `UINT64_MAX` wrap edges. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 64 × BitVec 64) :=\n"
  ++ "  [(0, 0), (1, 2), (0xFFFFFFFFFFFFFFFF, 0), (0xFFFFFFFFFFFFFFFF, 1),\n"
  ++ "   (0xFFFFFFFFFFFFFFFF, 0xFFFFFFFFFFFFFFFF)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: wrapping equation holds on every edge (this one is\n"
  ++ "    already the spec — unsigned addition never fails). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun p =>\n"
  ++ s!"    (repr ({name}_spec_fwd p.1 p.2)).pretty == (repr ((Except.ok (p.1 + p.2) : Result (BitVec 64)))).pretty\n"

/-- Spec stub for the `neg` shape (N6a: signed-32 negation). -/
def emitNegSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `int32_t {name}(int32_t x)` (negation, `INT_MIN` overflows).\n"
  ++ s!"    Base body reference: `checkedNegI32` (cf. emitted `{name}_fwd`, `emit_correct_neg`). -/\n"
  ++ s!"def {name}_spec_fwd (x : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  checkedNegI32 x\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, `INT32_MAX`, `INT32_MIN` (overflow). -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32) :=\n"
  ++ "  [0, 1, 0x7FFFFFFF, 0x80000000, 0xFFFFFFFF]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with the `Base` body on every edge.\n"
  ++ "    TODO (user): strengthen to the gallery equations `neg_correct_ok` /\n"
  ++ "    `neg_correct_err` (proved by hand in `Circe.Specs`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun p => (repr ({name}_spec_fwd p)).pretty == (repr (checkedNegI32 p)).pretty\n"

/-- Spec stub for the `sdiv` shape (N6a: signed-32 division). -/
def emitSdivSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `int32_t {name}(int32_t a, int32_t b)` (truncating division).\n"
  ++ s!"    Base body reference: `checkedDivI32` (cf. emitted `{name}_fwd`, `emit_correct_sdiv`). -/\n"
  ++ s!"def {name}_spec_fwd (a b : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  checkedDivI32 a b\n"
  ++ "\n"
  ++ s!"/-- Edge cases: exact, truncating, divide-by-zero, `INT_MIN / -1` (overflow). -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32 × BitVec 32) :=\n"
  ++ "  [(6, 3), (7, 3), (1, 0), (0x80000000, 0xFFFFFFFF)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with the `Base` body on every edge.\n"
  ++ "    TODO (user): strengthen to the gallery equations `sdiv_correct_ok` /\n"
  ++ "    `sdiv_correct_zero` / `sdiv_correct_overflow` (proved by hand in `Circe.Specs`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun p =>\n"
  ++ s!"    (repr ({name}_spec_fwd p.1 p.2)).pretty == (repr (checkedDivI32 p.1 p.2)).pretty\n"

/-- Spec stub for the `choose` shape (forward + backward). -/
def emitChooseSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: borrow-return `{name}(bool b, int32_t *x, int32_t *y)`.\n"
  ++ s!"    Base body references: `if b then x else y` / back-propagation pair\n"
  ++ s!"    (cf. emitted `{name}_fwd` / `{name}_back`, `choose_lens_laws`). -/\n"
  ++ s!"def {name}_spec_fwd (b : Bool) (x y : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  .ok (if b then x else y)\n"
  ++ s!"def {name}_spec_back (b : Bool) (x y ret : BitVec 32) : Result (BitVec 32 × BitVec 32) :=\n"
  ++ "  .ok (if b then (ret, y) else (x, ret))\n"
  ++ "\n"
  ++ s!"/-- Edge cases: both selectors, zero / distinct / max inputs. -/\n"
  ++ s!"def {name}_spec_edges : List (Bool × BitVec 32 × BitVec 32) :=\n"
  ++ "  [(true, 0, 0), (true, 1, 2), (false, 1, 2), (false, 0xFFFFFFFF, 0)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: get-put holds on every edge (see `choose_lens_laws`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_back t.1 t.2.1 t.2.2 (if t.1 then t.2.1 else t.2.2))).pretty\n"
  ++ s!"      == (repr ((Except.ok (t.2.1, t.2.2) : Result (BitVec 32 × BitVec 32)))).pretty\n"

/-- Spec stub for the `sum_array` shape. -/
def emitSumSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `uint32_t {name}(uint32_t *a, uint32_t n)` (length-paired, wrapping).\n"
  ++ s!"    Base body reference: `prefixSumU32` (cf. emitted `{name}_fwd`, `emit_correct_sum`). -/\n"
  ++ s!"def {name}_spec_fwd " ++ "{n : Nat} (a : BoundedList (BitVec 32) n) : Result (BitVec 32) :=\n"
  ++ "  .ok (prefixSumU32 a.val a.val.length)\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty / singleton / max-fuel (length = bound). -/\n"
  ++ s!"def {name}_spec_edges : List (List (BitVec 32)) :=\n"
  ++ "  [[], [0], [1], [1, 2, 3], [0xFFFFFFFF, 1]]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the `List.sum` equation holds on every edge\n"
  ++ "    (this one is already the spec — see `sum_correct`; copy into\n"
  ++ "    `Circe.Specs` to build on it). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun l =>\n"
  ++ "    (repr (prefixSumU32 l l.length)).pretty == (repr ((l.take l.length).sum)).pretty\n"

/-- Spec stub for the `vec_alloc` shape. -/
def emitVecSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `uint32_t {name}(uint32_t n)` (allocate, fill with indices, sum, free).\n"
  ++ s!"    Base body reference: `vecFillSumU32` (cf. emitted `{name}_fwd`, `emit_correct_vec`). -/\n"
  ++ s!"def {name}_spec_fwd (n : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  vecFillSumU32 n.toNat\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty / singleton / small / page-ish. -/\n"
  ++ s!"def {name}_spec_edges : List Nat :=\n"
  ++ "  [0, 1, 2, 10, 256]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the index-sum equation holds on every edge\n"
  ++ "    (this one is already the spec — see `vec_correct`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun n =>\n"
  ++ "    (repr (vecFillSumU32 n)).pretty\n"
  ++ "      == (repr ((Except.ok (((List.range n).map (BitVec.ofNat 32)).sum) : Result (BitVec 32)))).pretty\n"

/-- Spec stub for the `vec_copy_sum` shape (M1a: two live blocks). -/
def emitVec2SpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `uint32_t {name}(uint32_t n)` (allocate two, fill `a` with indices, copy `a` into `b`, sum `b`, free both).\n"
  ++ s!"    Base body reference: `vecFillSumU32` — the copy is value-invisible (cf. emitted `{name}_fwd`, `emit_correct_vec2`, `vec2Fwd_eq_vecFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (n : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  vecFillSumU32 n.toNat\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty / singleton / small / page-ish. -/\n"
  ++ s!"def {name}_spec_edges : List Nat :=\n"
  ++ "  [0, 1, 2, 10, 256]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the index-sum equation holds on every edge\n"
  ++ "    (this one is already the spec — see `vec_correct`; the copy adds\n"
  ++ "    no observable behavior). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun n =>\n"
  ++ "    (repr (vecFillSumU32 n)).pretty\n"
  ++ "      == (repr ((Except.ok (((List.range n).map (BitVec.ofNat 32)).sum) : Result (BitVec 32)))).pretty\n"

/-- Spec stub for the `vec_alloc_u64` shape (M1b: `u64` mirror). -/
def emitVec64SpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `uint64_t {name}(uint64_t n)` (allocate, fill with indices, sum, free).\n"
  ++ s!"    Base body reference: `vecFillSumU64` (cf. emitted `{name}_fwd`, `emit_correct_vec64`). -/\n"
  ++ s!"def {name}_spec_fwd (n : BitVec 64) : Result (BitVec 64) :=\n"
  ++ "  vecFillSumU64 n.toNat\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty / singleton / small / page-ish. -/\n"
  ++ s!"def {name}_spec_edges : List Nat :=\n"
  ++ "  [0, 1, 2, 10, 256]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the index-sum equation holds on every edge\n"
  ++ "    (this one is already the spec — see `vec64_correct`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun n =>\n"
  ++ "    (repr (vecFillSumU64 n)).pretty\n"
  ++ "      == (repr ((Except.ok (((List.range n).map (BitVec.ofNat 64)).sum) : Result (BitVec 64)))).pretty\n"

/-- Spec stub for the `vec_realloc` shape (M1c: grown block). -/
def emitVecReallocSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `uint32_t {name}(uint32_t n)` (allocate, fill `[0,n)`, `realloc` to `2*n`, fill `[n,2*n)`, sum, free).\n"
  ++ s!"    Base body reference: `vecReallocFillSumU32` (cf. emitted `{name}_fwd`, `emit_correct_vecRealloc`). -/\n"
  ++ s!"def {name}_spec_fwd (n : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  vecReallocFillSumU32 n.toNat\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty / singleton / small / page-ish (sums run over `2*n`). -/\n"
  ++ s!"def {name}_spec_edges : List Nat :=\n"
  ++ "  [0, 1, 2, 10, 256]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the grown index-sum equation holds on every edge\n"
  ++ "    (this one is already the spec — see `vecRealloc_correct`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun n =>\n"
  ++ "    (repr (vecReallocFillSumU32 n)).pretty\n"
  ++ "      == (repr ((Except.ok (((List.range (n + n)).map (BitVec.ofNat 32)).sum) : Result (BitVec 32)))).pretty\n"

/-- Spec stub for the `add_caller` shape (S1 DAG calls). -/
def emitAddCallerSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `{name}(x, y, z)` = two DAG calls into `add_fwd`.\n"
  ++ s!"    Base body reference: two sequenced `checkedAddI32` binds, leaf bodies\n"
  ++ s!"    inlined (cf. emitted `{name}_fwd`, `addCallerFwd_as_calls`). -/\n"
  ++ s!"def {name}_spec_fwd (x y z : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  do let t ← checkedAddI32 x y\n"
  ++ "     checkedAddI32 t z\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, first-add overflow, second-add overflow. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32 × BitVec 32 × BitVec 32) :=\n"
  ++ "  [(0, 0, 0), (1, 2, 3), (0x7FFFFFFF, 1, 0), (0x7FFFFFFF, 0, 1), (1, 0x7FFFFFFF, 1)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the two-call bind structure holds on every edge\n"
  ++ "    (cf. `addCallerFwd_as_calls`). TODO (user): fill the ok/err equation. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1 t.2.1 t.2.2)).pretty\n"
  ++ s!"      == (repr ((checkedAddI32 t.1 t.2.1).bind fun u => checkedAddI32 u t.2.2)).pretty\n"

/-- Spec stub for the `add3` shape (N4a 3-`i32` overload leaf). -/
def emitAdd3SpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(x, y, z)` = two threaded `nsw` adds.\n"
  ++ s!"    Base body reference: two sequenced `checkedAddI32` binds\n"
  ++ s!"    (cf. emitted `{name}_fwd`, `add3Fwd_ok/err`). -/\n"
  ++ s!"def {name}_spec_fwd (x y z : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  do let t ← checkedAddI32 x y\n"
  ++ "     checkedAddI32 t z\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, first-add overflow, second-add overflow. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32 × BitVec 32 × BitVec 32) :=\n"
  ++ "  [(0, 0, 0), (1, 2, 3), (0x7FFFFFFF, 1, 0), (0x7FFFFFFF, 0, 1), (1, 0x7FFFFFFF, 1)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the two-add bind structure holds on every edge\n"
  ++ "    (cf. `add3Fwd_ok/err`). TODO (user): fill the ok/err equation. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1 t.2.1 t.2.2)).pretty\n"
  ++ s!"      == (repr ((checkedAddI32 t.1 t.2.1).bind fun u => checkedAddI32 u t.2.2)).pretty\n"

/-- Spec stub for the `use_add` shape (N4a overload entry). -/
def emitUseAddSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(x, y)` delegates to the `_Z3addii` overload.\n"
  ++ s!"    Base body reference: `checkedAddI32` (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `useAddFwd_is_call`). -/\n"
  ++ s!"def {name}_spec_fwd (x y : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  checkedAddI32 x y\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, overflow. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32 × BitVec 32) :=\n"
  ++ "  [(0, 0), (1, 2), (0x7FFFFFFF, 1), (1, 0x7FFFFFFF), (0x7FFFFFFF, 0x7FFFFFFF)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with `checkedAddI32` on every edge.\n"
  ++ "    TODO (user): strengthen to the delegation equation\n"
  ++ "    (`useAddFwd_is_call`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1 t.2)).pretty\n"
  ++ s!"      == (repr (checkedAddI32 t.1 t.2)).pretty\n"

/-- Spec stub for the `use_ns_add` shape (N4a namespace entry). -/
def emitUseNsAddSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(x, y)` delegates to the `_ZN2ns3addEii` leaf.\n"
  ++ s!"    Base body reference: `checkedAddI32` (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `useNsAddFwd_is_call`). -/\n"
  ++ s!"def {name}_spec_fwd (x y : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  checkedAddI32 x y\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, overflow. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32 × BitVec 32) :=\n"
  ++ "  [(0, 0), (1, 2), (0x7FFFFFFF, 1), (1, 0x7FFFFFFF), (0x7FFFFFFF, 0x7FFFFFFF)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with `checkedAddI32` on every edge.\n"
  ++ "    TODO (user): strengthen to the delegation equation\n"
  ++ "    (`useNsAddFwd_is_call`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1 t.2)).pretty\n"
  ++ s!"      == (repr (checkedAddI32 t.1 t.2)).pretty\n"

/-- Spec stub for the `use_tadd32` shape (N4c 32-bit instantiation entry). -/
def emitUseTadd32SpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(x, y)` delegates to the `_Z4taddIiET_S0_S0_` instantiation.\n"
  ++ s!"    Base body reference: `checkedAddI32` (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `useTadd32Fwd_is_call`). -/\n"
  ++ s!"def {name}_spec_fwd (x y : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  checkedAddI32 x y\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, overflow. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32 × BitVec 32) :=\n"
  ++ "  [(0, 0), (1, 2), (0x7FFFFFFF, 1), (1, 0x7FFFFFFF), (0x7FFFFFFF, 0x7FFFFFFF)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with `checkedAddI32` on every edge.\n"
  ++ "    TODO (user): strengthen to the delegation equation\n"
  ++ "    (`useTadd32Fwd_is_call`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1 t.2)).pretty\n"
  ++ s!"      == (repr (checkedAddI32 t.1 t.2)).pretty\n"

/-- Spec stub for the `use_tadd64` shape (N4c 64-bit instantiation entry). -/
def emitUseTadd64SpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(x, y)` delegates to the `_Z4taddIlET_S0_S0_` instantiation.\n"
  ++ s!"    Base body reference: `checkedAddI64` (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `useTadd64Fwd_is_call`). -/\n"
  ++ s!"def {name}_spec_fwd (x y : BitVec 64) : Result (BitVec 64) :=\n"
  ++ "  checkedAddI64 x y\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, overflow. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 64 × BitVec 64) :=\n"
  ++ "  [(0, 0), (1, 2), (0x7FFFFFFFFFFFFFFF, 1), (1, 0x7FFFFFFFFFFFFFFF), (0x7FFFFFFFFFFFFFFF, 0x7FFFFFFFFFFFFFFF)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with `checkedAddI64` on every edge.\n"
  ++ "    TODO (user): strengthen to the delegation equation\n"
  ++ "    (`useTadd64Fwd_is_call`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1 t.2)).pretty\n"
  ++ s!"      == (repr (checkedAddI64 t.1 t.2)).pretty\n"

/-- Spec stub for the `_S_ref` shape (N4d-i unchecked-index leaf). The
    mirror is the tag-erased `arrayRefFwd`; with no deeper `Base` op
    to compare against, edges carry ground truth (hits at every
    index, `OOB` off the end). -/
def emitArrayRefSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(t, n)` reads the word at `u64` index `n`.\n"
  ++ s!"    Base body reference: the index read itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `arrayRefFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (t : List (BitVec 32)) (n : BitVec 64) : Result (BitVec 32) :=\n"
  ++ "  match t[n.toNat]? with\n"
  ++ "  | some x => .ok x\n"
  ++ "  | none => .error .OOB\n"
  ++ "\n"
  ++ s!"/-- Edge cases: hits at every index, `OOB` off the end. -/\n"
  ++ s!"def {name}_spec_edges : List (List (BitVec 32) × BitVec 64 × Result (BitVec 32)) :=\n"
  ++ "  [([10, 20, 30, 40], 0, .ok 10), ([10, 20, 30, 40], 3, .ok 40),\n"
  ++ "   ([10, 20, 30, 40], 4, .error .OOB)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1 t.2.1)).pretty == (repr t.2.2).pretty\n"

/-- Spec stub for the `operator[]` shape (N4d-i single-delegation
    entry). Same mirror as `_S_ref` (the call edge is fused, cf.
    `arrayAtFwd_is_call`); edges carry ground truth likewise. -/
def emitArrayAtSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(a, n)` delegates to the `_S_ref` unchecked-index body.\n"
  ++ s!"    Base body reference: the index read itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `arrayAtFwd_is_call`). -/\n"
  ++ s!"def {name}_spec_fwd (a : List (BitVec 32)) (n : BitVec 64) : Result (BitVec 32) :=\n"
  ++ "  match a[n.toNat]? with\n"
  ++ "  | some x => .ok x\n"
  ++ "  | none => .error .OOB\n"
  ++ "\n"
  ++ s!"/-- Edge cases: hits at every index, `OOB` off the end. -/\n"
  ++ s!"def {name}_spec_edges : List (List (BitVec 32) × BitVec 64 × Result (BitVec 32)) :=\n"
  ++ "  [([10, 20, 30, 40], 1, .ok 20), ([10, 20, 30, 40], 2, .ok 30),\n"
  ++ "   ([10, 20, 30, 40], 7, .error .OOB)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1 t.2.1)).pretty == (repr t.2.2).pretty\n"

/-- Spec stub for the `array_sum` shape (N4d-i 4-call entry). The
    mirror threads the three `nsw` adds (the tag-erased `arraySumFwd`);
    edges carry ground truth (zero, unit, overflow at each site). -/
def emitArraySumSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(a)` reads all four words through `operator[]`.\n"
  ++ s!"    Base body reference: three threaded `checkedAddI32` (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `arraySumFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (a b c d : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  do let t ← checkedAddI32 a b\n"
  ++ "     let u ← checkedAddI32 t c\n"
  ++ "     checkedAddI32 u d\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, overflow at each add site. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32 × BitVec 32 × BitVec 32 × BitVec 32 × Result (BitVec 32)) :=\n"
  ++ "  [(0, 0, 0, 0, .ok 0), (1, 2, 3, 4, .ok 10),\n"
  ++ "   (0x7FFFFFFF, 1, 0, 0, .error .Overflow), (1, 0x7FFFFFFF, 1, 0, .error .Overflow),\n"
  ++ "   (1, 1, 1, 0x7FFFFFFF, .error .Overflow)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1 t.2.1 t.2.2.1 t.2.2.2.1)).pretty == (repr t.2.2.2.2).pretty\n"

/-- Spec stub for the `_M_is_engaged` shape (N4d-ii engaged-bit
    leaf). The mirror is the tag-erased `optHasFwd`; with no deeper
    `Base` op to compare against, edges carry ground truth (engaged
    words report `true`, disengaged reports `false`). -/
def emitOptHasSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(o)` reads the `_M_engaged` bit.\n"
  ++ s!"    Base body reference: the engaged-bit read itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `optHasFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (o : Option (BitVec 32)) : Bool :=\n"
  ++ "  o.isSome\n"
  ++ "\n"
  ++ s!"/-- Edge cases: engaged words, zero payload, disengaged. -/\n"
  ++ s!"def {name}_spec_edges : List (Option (BitVec 32) × Bool) :=\n"
  ++ "  [(some 7, true), (some 0, true), (none, false)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1)).pretty == (repr t.2).pretty\n"

/-- Spec stub for the `has_value` shape (N4d-ii single-delegation
    entry). Same mirror as `_M_is_engaged` (the call edge is fused,
    cf. `optHasValueFwd_is_call`); edges carry ground truth
    likewise. -/
def emitOptHasValueSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(o)` delegates to the `_M_is_engaged` bit body.\n"
  ++ s!"    Base body reference: the engaged-bit read itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `optHasValueFwd_is_call`). -/\n"
  ++ s!"def {name}_spec_fwd (o : Option (BitVec 32)) : Bool :=\n"
  ++ "  o.isSome\n"
  ++ "\n"
  ++ s!"/-- Edge cases: engaged words, zero payload, disengaged. -/\n"
  ++ s!"def {name}_spec_edges : List (Option (BitVec 32) × Bool) :=\n"
  ++ "  [(some 7, true), (some 0, true), (none, false)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1)).pretty == (repr t.2).pretty\n"

/-- Spec stub for the payload `_M_get` shape (N4d-ii word leaf). The
    mirror is the tag-erased `optGetFwd`; edges carry ground truth
    (payload words, disengaged `AssertFail`). -/
def emitOptGetSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(o)` reads the `_M_value` word.\n"
  ++ s!"    Base body reference: the payload-word read itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `optGetFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (o : Option (BitVec 32)) : Result (BitVec 32) :=\n"
  ++ "  match o with\n"
  ++ "  | some x => .ok x\n"
  ++ "  | none => .error .AssertFail\n"
  ++ "\n"
  ++ s!"/-- Edge cases: payload words, zero payload, disengaged. -/\n"
  ++ s!"def {name}_spec_edges : List (Option (BitVec 32) × Result (BitVec 32)) :=\n"
  ++ "  [(some 7, .ok 7), (some 0, .ok 0), (none, .error .AssertFail)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1)).pretty == (repr t.2).pretty\n"

/-- Spec stub for the impl `_M_get` shape (N4d-ii delegation entry).
    Same mirror as payload `_M_get` (the dead assert scope is
    dropped); edges carry ground truth likewise. -/
def emitOptImplGetSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(o)` delegates to the payload `_M_get` word body.\n"
  ++ s!"    Base body reference: the payload-word read itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `optGetFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (o : Option (BitVec 32)) : Result (BitVec 32) :=\n"
  ++ "  match o with\n"
  ++ "  | some x => .ok x\n"
  ++ "  | none => .error .AssertFail\n"
  ++ "\n"
  ++ s!"/-- Edge cases: payload words, zero payload, disengaged. -/\n"
  ++ s!"def {name}_spec_edges : List (Option (BitVec 32) × Result (BitVec 32)) :=\n"
  ++ "  [(some 7, .ok 7), (some 0, .ok 0), (none, .error .AssertFail)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1)).pretty == (repr t.2).pretty\n"

/-- Spec stub for the `operator*` shape (N4d-ii fused leaf). Same
    mirror as payload `_M_get` (two call edges fused, cf.
    `optDerefOpFwd_is_call`); edges carry ground truth likewise. -/
def emitOptDerefOpSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(o)` is the fused `operator*` word read.\n"
  ++ s!"    Base body reference: the payload-word read itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `optDerefOpFwd_is_call`). -/\n"
  ++ s!"def {name}_spec_fwd (o : Option (BitVec 32)) : Result (BitVec 32) :=\n"
  ++ "  match o with\n"
  ++ "  | some x => .ok x\n"
  ++ "  | none => .error .AssertFail\n"
  ++ "\n"
  ++ s!"/-- Edge cases: payload words, zero payload, disengaged. -/\n"
  ++ s!"def {name}_spec_edges : List (Option (BitVec 32) × Result (BitVec 32)) :=\n"
  ++ "  [(some 7, .ok 7), (some 0, .ok 0), (none, .error .AssertFail)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1)).pretty == (repr t.2).pretty\n"

/-- Spec stub for the `opt_deref` shape (N4d-ii guarded entry). The
    mirror is the tag-erased `optDerefFwd`; edges carry ground truth
    (payload words, the `-1` sentinel on disengaged). -/
def emitOptDerefSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(o)` dereferences when engaged, `-1` sentinel otherwise.\n"
  ++ s!"    Base body reference: the guarded deref itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `optDerefFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (o : Option (BitVec 32)) : Result (BitVec 32) :=\n"
  ++ "  match o with\n"
  ++ "  | some x => .ok x\n"
  ++ "  | none => .ok (-1)\n"
  ++ "\n"
  ++ s!"/-- Edge cases: payload words, zero payload, disengaged sentinel. -/\n"
  ++ s!"def {name}_spec_edges : List (Option (BitVec 32) × Result (BitVec 32)) :=\n"
  ++ "  [(some 7, .ok 7), (some 0, .ok 0), (none, .ok (-1))]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1)).pretty == (repr t.2).pretty\n"

/-- Spec stub for the `_M_extent` shape (N4d-iii extent leaf). The
    mirror is the tag-erased `spanExtentFwd`; edges carry ground
    truth (empty, singleton, longer views). -/
def emitSpanExtentSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(e)` reads the `_M_extent_value` word.\n"
  ++ s!"    Base body reference: the reified length itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `spanExtentFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (l : List (BitVec 32)) : BitVec 64 :=\n"
  ++ "  BitVec.ofNat 64 l.length\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty, singleton, longer views. -/\n"
  ++ s!"def {name}_spec_edges : List (List (BitVec 32) × BitVec 64) :=\n"
  ++ "  [([], 0), ([7], 1), ([1, 2, 3], 3)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1)).pretty == (repr t.2).pretty\n"

/-- Spec stub for the `size` shape (N4d-iii single-delegation
    entry). Same mirror as `_M_extent` (the call edge is fused,
    cf. `spanSizeFwd_is_call`); edges carry ground truth
    likewise. -/
def emitSpanSizeSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(s)` delegates to the `_M_extent` length body.\n"
  ++ s!"    Base body reference: the reified length itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `spanSizeFwd_is_call`). -/\n"
  ++ s!"def {name}_spec_fwd (l : List (BitVec 32)) : BitVec 64 :=\n"
  ++ "  BitVec.ofNat 64 l.length\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty, singleton, longer views. -/\n"
  ++ s!"def {name}_spec_edges : List (List (BitVec 32) × BitVec 64) :=\n"
  ++ "  [([], 0), ([7], 1), ([1, 2, 3], 3)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1)).pretty == (repr t.2).pretty\n"

/-- Spec stub for the `operator[]` shape (N4d-iii fused leaf). The
    mirror is the tag-erased `spanIndexFwd`; edges carry ground
    truth (hits, `OOB` past the end). -/
def emitSpanIndexSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(s, n)` reads the word at index `n`.\n"
  ++ s!"    Base body reference: the bounded read itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `spanIndexFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (l : List (BitVec 32)) (n : BitVec 64) : Result (BitVec 32) :=\n"
  ++ "  match l[n.toNat]? with\n"
  ++ "  | some x => .ok x\n"
  ++ "  | none => .error .OOB\n"
  ++ "\n"
  ++ s!"/-- Edge cases: first/last hits, `OOB` past the end. -/\n"
  ++ s!"def {name}_spec_edges : List ((List (BitVec 32) × BitVec 64) × Result (BitVec 32)) :=\n"
  ++ "  [(([1, 2, 3], 0), .ok 1), (([1, 2, 3], 2), .ok 3), (([1, 2, 3], 3), .error .OOB)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1.1 t.1.2)).pretty == (repr t.2).pretty\n"

/-- Spec stub for the `span_sum` shape (N4d-iii index-loop entry).
    The mirror is the tag-erased `spanSumFwd`; edges carry ground
    truth (empty sum, small sums, `nsw` overflow). -/
def emitSpanSumSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(s)` sums the viewed words.\n"
  ++ s!"    Base body reference: the checked-add fold itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `spanSumFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (l : List (BitVec 32)) : Result (BitVec 32) :=\n"
  ++ "  go l 0\n"
  ++ "where go : List (BitVec 32) → BitVec 32 → Result (BitVec 32)\n"
  ++ "  | [], acc => .ok acc\n"
  ++ "  | x :: xs, acc => do\n"
  ++ "      let a ← checkedAddI32 acc x\n"
  ++ "      go xs a\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty sum, small sums, `nsw` overflow. -/\n"
  ++ s!"def {name}_spec_edges : List (List (BitVec 32) × Result (BitVec 32)) :=\n"
  ++ "  [([], .ok 0), ([1, 2, 3], .ok 6), ([0x7FFFFFFF, 1], .error .Overflow)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1)).pretty == (repr t.2).pretty\n"

/-- Spec stub for the vector `size` shape (N4d-iv-a projection
    leaf). The mirror is the tag-erased `stdVecSizeFwd`; edges carry
    ground truth (empty, singleton, longer vectors). -/
def emitStdVecSizeSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(s)` reads the vector length.\n"
  ++ s!"    Base body reference: the reified length itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecSizeFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (l : List (BitVec 32)) : BitVec 64 :=\n"
  ++ "  BitVec.ofNat 64 l.length\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty, singleton, longer vectors. -/\n"
  ++ s!"def {name}_spec_edges : List (List (BitVec 32) × BitVec 64) :=\n"
  ++ "  [([], 0), ([7], 1), ([1, 2, 3], 3)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1)).pretty == (repr t.2).pretty\n"

/-- Spec stub for the vector `operator[]` shape (N4d-iv-a fused
    leaf). The mirror is the tag-erased `stdVecIndexFwd`; edges
    carry ground truth (hits, `OOB` past the end). -/
def emitStdVecIndexSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(s, n)` reads the word at index `n`.\n"
  ++ s!"    Base body reference: the bounded read itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecIndexFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (l : List (BitVec 32)) (n : BitVec 64) : Result (BitVec 32) :=\n"
  ++ "  match l[n.toNat]? with\n"
  ++ "  | some x => .ok x\n"
  ++ "  | none => .error .OOB\n"
  ++ "\n"
  ++ s!"/-- Edge cases: first/last hits, `OOB` past the end. -/\n"
  ++ s!"def {name}_spec_edges : List ((List (BitVec 32) × BitVec 64) × Result (BitVec 32)) :=\n"
  ++ "  [(([1, 2, 3], 0), .ok 1), (([1, 2, 3], 2), .ok 3), (([1, 2, 3], 3), .error .OOB)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1.1 t.1.2)).pretty == (repr t.2).pretty\n"

/-- Spec stub for the `vec_read_sum` shape (N4d-iv-a index-loop
    entry). The mirror is the tag-erased `stdVecReadSumFwd`; edges
    carry ground truth (empty sum, small sums, `nsw` overflow). -/
def emitStdVecReadSumSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(s)` sums the element words.\n"
  ++ s!"    Base body reference: the checked-add fold itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecReadSumFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (l : List (BitVec 32)) : Result (BitVec 32) :=\n"
  ++ "  go l 0\n"
  ++ "where go : List (BitVec 32) → BitVec 32 → Result (BitVec 32)\n"
  ++ "  | [], acc => .ok acc\n"
  ++ "  | x :: xs, acc => do\n"
  ++ "      let a ← checkedAddI32 acc x\n"
  ++ "      go xs a\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty sum, small sums, `nsw` overflow. -/\n"
  ++ s!"def {name}_spec_edges : List (List (BitVec 32) × Result (BitVec 32)) :=\n"
  ++ "  [([], .ok 0), ([1, 2, 3], .ok 6), ([0x7FFFFFFF, 1], .error .Overflow)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1)).pretty == (repr t.2).pretty\n"

/-- Spec stub for the default-ctor chain (N4d-iv-b1 empty triple).
    The mirror is the tag-erased `stdVecEmptyCtorFwd`. -/
def emitStdVecEmptyCtorSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}()` builds the empty vector.\n"
  ++ s!"    Base body reference: the empty triple itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecEmptyCtorFwd`). -/\n"
  ++ s!"def {name}_spec_fwd : Vec32 × Nat × Nat :=\n"
  ++ "  (⟨[], false⟩, 0, 0)\n"
  ++ "\n"
  ++ s!"/-- Edge cases: the single empty triple. -/\n"
  ++ s!"def {name}_spec_edges : List (Unit × (Vec32 × Nat × Nat)) :=\n"
  ++ "  [((), (⟨[], false⟩, 0, 0))]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd)).pretty == (repr t.2).pretty\n"

/-- Spec stub for the empty-effect leaves (N4d-iv-b1 void as
    `i32 0`). The mirror is the tag-erased `stdVecUnitFwd`. -/
def emitStdVecUnitSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}()` has no observable effect.\n"
  ++ s!"    Base body reference: void as `i32 0` (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecUnitFwd`). -/\n"
  ++ s!"def {name}_spec_fwd : BitVec 32 :=\n"
  ++ "  BitVec.ofNat 32 0\n"
  ++ "\n"
  ++ s!"/-- Edge cases: the single void value. -/\n"
  ++ s!"def {name}_spec_edges : List (Unit × BitVec 32) :=\n"
  ++ "  [((), BitVec.ofNat 32 0)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd)).pretty == (repr t.2).pretty\n"

/-- Spec stub for the destructor (N4d-iv-b1 guarded consume). The
    mirror is the tag-erased `stdVecDtorFwd`; edges carry ground
    truth (empty, live consume, use-after-free). -/
def emitStdVecDtorSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(t)` consumes the triple.\n"
  ++ s!"    Base body reference: the `0 < cap`-guarded consume itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecDtorFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (b : Vec32) (len cap : Nat) : Result (Vec32 × Nat × Nat) :=\n"
  ++ "  if 0 < cap then\n"
  ++ "    match vecFree b with\n"
  ++ "    | .error e => .error e\n"
  ++ "    | .ok b' => .ok (b', len, cap)\n"
  ++ "  else .ok (b, len, cap)\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty, live consume, use-after-free. -/\n"
  ++ s!"def {name}_spec_edges : List ((Vec32 × Nat × Nat) × Result (Vec32 × Nat × Nat)) :=\n"
  ++ "  [(((⟨[], false⟩, 0, 0)), .ok (⟨[], false⟩, 0, 0)),\n"
  ++ "   (((⟨[7], false⟩, 1, 1)), .ok (⟨[7], true⟩, 1, 1)),\n"
  ++ "   (((⟨[7], true⟩, 1, 1)), .error .AssertFail)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1.1 t.1.2.1 t.1.2.2)).pretty == (repr t.2).pretty\n"

/-- Spec stub for the destroy range (N4d-iv-b1 trivial-`int`
    no-op). The mirror is the tag-erased `stdVecDestroyNoopFwd`. -/
def emitStdVecDestroyNoopSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(a, b)` destroys nothing.\n"
  ++ s!"    Base body reference: void as `i32 0` (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecDestroyNoopFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (_a _b : BitVec 64) : BitVec 32 :=\n"
  ++ "  BitVec.ofNat 32 0\n"
  ++ "\n"
  ++ s!"/-- Edge cases: the single void value. -/\n"
  ++ s!"def {name}_spec_edges : List ((BitVec 64 × BitVec 64) × BitVec 32) :=\n"
  ++ "  [((0, 0), BitVec.ofNat 32 0)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1.1 t.1.2)).pretty == (repr t.2).pretty\n"

/-- Spec stub for element destroy (N4d-iv-b1 `int` no-op). The
    mirror is the tag-erased `stdVecDestroyPtrFwd`. -/
def emitStdVecDestroyPtrSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(p)` destroys nothing.\n"
  ++ s!"    Base body reference: void as `i32 0` (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecDestroyPtrFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (_p : BitVec 64) : BitVec 32 :=\n"
  ++ "  BitVec.ofNat 32 0\n"
  ++ "\n"
  ++ s!"/-- Edge cases: the single void value. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 64 × BitVec 32) :=\n"
  ++ "  [(0, BitVec.ofNat 32 0)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1)).pretty == (repr t.2).pretty\n"

/-- Spec stub for the allocator projection (N4d-iv-b1 erased
    allocator). The mirror is the tag-erased `stdVecGetTpFwd`. -/
def emitStdVecGetTpSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(t)` projects the allocator.\n"
  ++ s!"    Base body reference: the erased allocator `i32 0` (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecGetTpFwd`). -/\n"
  ++ s!"def {name}_spec_fwd : BitVec 32 :=\n"
  ++ "  BitVec.ofNat 32 0\n"
  ++ "\n"
  ++ s!"/-- Edge cases: the single erased allocator. -/\n"
  ++ s!"def {name}_spec_edges : List (Unit × BitVec 32) :=\n"
  ++ "  [((), BitVec.ofNat 32 0)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd)).pretty == (repr t.2).pretty\n"

/-- Spec stub for the max-size chain (N4d-iv-b1 `diffmax` const).
    The mirror is the tag-erased `stdVecDiffMaxFwd`. -/
def emitStdVecDiffMaxSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}()` returns the max size.\n"
  ++ s!"    Base body reference: the `diffmax` const itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecDiffMaxFwd`). -/\n"
  ++ s!"def {name}_spec_fwd : BitVec 64 :=\n"
  ++ "  BitVec.ofNat 64 2305843009213693951\n"
  ++ "\n"
  ++ s!"/-- Edge cases: the single const. -/\n"
  ++ s!"def {name}_spec_edges : List (Unit × BitVec 64) :=\n"
  ++ "  [((), BitVec.ofNat 64 2305843009213693951)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd)).pretty == (repr t.2).pretty\n"

/-- Spec stub for `std::max` (N4d-iv-b1 early-return-`if`). The
    mirror is the tag-erased `stdVecMaxFwd`; edges carry ground
    truth (either side wins). -/
def emitStdVecMaxSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(a, b)` returns the larger word.\n"
  ++ s!"    Base body reference: the early-return-`if` itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecMaxFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (a b : BitVec 64) : BitVec 64 :=\n"
  ++ "  if a.ult b then b else a\n"
  ++ "\n"
  ++ s!"/-- Edge cases: either side wins. -/\n"
  ++ s!"def {name}_spec_edges : List ((BitVec 64 × BitVec 64) × BitVec 64) :=\n"
  ++ "  [((3, 5), 5), ((5, 3), 5), ((4, 4), 4)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1.1 t.1.2)).pretty == (repr t.2).pretty\n"

/-- Spec stub for `std::min` (N4d-iv-b1 early-return-`if`). The
    mirror is the tag-erased `stdVecMinFwd`; edges carry ground
    truth (either side wins). -/
def emitStdVecMinSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(a, b)` returns the smaller word.\n"
  ++ s!"    Base body reference: the early-return-`if` itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecMinFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (a b : BitVec 64) : BitVec 64 :=\n"
  ++ "  if b.ult a then b else a\n"
  ++ "\n"
  ++ s!"/-- Edge cases: either side wins. -/\n"
  ++ s!"def {name}_spec_edges : List ((BitVec 64 × BitVec 64) × BitVec 64) :=\n"
  ++ "  [((3, 5), 3), ((5, 3), 3), ((4, 4), 4)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1.1 t.1.2)).pretty == (repr t.2).pretty\n"

/-- Spec stub for `_M_check_len` (N4d-iv-b1 checked length). The
    mirror is the tag-erased `stdVecCheckLenFwd`; edges carry ground
    truth (exact, clamp, loud over-max). -/
def emitStdVecCheckLenSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(t, n)` checks the grown length.\n"
  ++ s!"    Base body reference: the checked length with `maxDiff` clamp itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecCheckLenFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (len : Nat) (n : BitVec 64) : Result (BitVec 64) :=\n"
  ++ "  if (BitVec.ofNat 64 2305843009213693951 - BitVec.ofNat 64 len).ult n then\n"
  ++ "    .error .AssertFail\n"
  ++ "  else if (BitVec.ofNat 64 len +\n"
  ++ "      (if (BitVec.ofNat 64 len).ult n then n\n"
  ++ "        else BitVec.ofNat 64 len)).ult (BitVec.ofNat 64 len) then\n"
  ++ "    .ok (BitVec.ofNat 64 2305843009213693951)\n"
  ++ "  else if (BitVec.ofNat 64 2305843009213693951).ult (BitVec.ofNat 64 len +\n"
  ++ "      (if (BitVec.ofNat 64 len).ult n then n\n"
  ++ "        else BitVec.ofNat 64 len)) then\n"
  ++ "    .ok (BitVec.ofNat 64 2305843009213693951)\n"
  ++ "  else\n"
  ++ "    .ok (BitVec.ofNat 64 len +\n"
  ++ "      (if (BitVec.ofNat 64 len).ult n then n\n"
  ++ "        else BitVec.ofNat 64 len))\n"
  ++ "\n"
  ++ s!"/-- Edge cases: exact, clamp, loud over-max. -/\n"
  ++ s!"def {name}_spec_edges : List ((Nat × BitVec 64) × Result (BitVec 64)) :=\n"
  ++ "  [((0, 0), .ok 0),\n"
  ++ "   ((0, BitVec.ofNat 64 2305843009213693951), .ok (BitVec.ofNat 64 2305843009213693951)),\n"
  ++ "   ((0, BitVec.ofNat 64 2305843009213693952), .error .AssertFail)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1.1 t.1.2)).pretty == (repr t.2).pretty\n"

/-- Spec stub for `begin` (N4d-iv-b1 `0` offset). The mirror is the
    tag-erased `stdVecBeginFwd`. -/
def emitStdVecBeginSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(t)` returns the first offset.\n"
  ++ s!"    Base body reference: the `0` offset itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecBeginFwd`). -/\n"
  ++ s!"def {name}_spec_fwd : BitVec 64 :=\n"
  ++ "  BitVec.ofNat 64 0\n"
  ++ "\n"
  ++ s!"/-- Edge cases: the single offset. -/\n"
  ++ s!"def {name}_spec_edges : List (Unit × BitVec 64) :=\n"
  ++ "  [((), BitVec.ofNat 64 0)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd)).pretty == (repr t.2).pretty\n"

/-- Spec stub for `end` (N4d-iv-b1 `len` offset). The mirror is the
    tag-erased `stdVecEndFwd`; edges carry ground truth (empty,
    longer). -/
def emitStdVecEndSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(t)` returns the past-the-end offset.\n"
  ++ s!"    Base body reference: the `len` offset itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecEndFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (len : Nat) : BitVec 64 :=\n"
  ++ "  BitVec.ofNat 64 len\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty, longer. -/\n"
  ++ s!"def {name}_spec_edges : List (Nat × BitVec 64) :=\n"
  ++ "  [(0, BitVec.ofNat 64 0), (3, BitVec.ofNat 64 3)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1)).pretty == (repr t.2).pretty\n"

/-- Spec stub for `back` (N4d-iv-b1 `len - 1` offset). The mirror is
    the tag-erased `stdVecBackFwd`; edges carry ground truth
    (singleton, longer). -/
def emitStdVecBackSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(t)` returns the last offset.\n"
  ++ s!"    Base body reference: the `len - 1` offset itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecBackFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (len : Nat) : BitVec 64 :=\n"
  ++ "  BitVec.ofNat 64 len - 1\n"
  ++ "\n"
  ++ s!"/-- Edge cases: singleton, longer. -/\n"
  ++ s!"def {name}_spec_edges : List (Nat × BitVec 64) :=\n"
  ++ "  [(1, BitVec.ofNat 64 0), (3, BitVec.ofNat 64 2)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1)).pretty == (repr t.2).pretty\n"

/-- Spec stub for the iterator identities (N4d-iv-b1 erased
    offsets). The mirror is the tag-erased `stdVecIterIdFwd`; edges
    carry ground truth (zero, nonzero). -/
def emitStdVecIterIdSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(p)` returns the offset itself.\n"
  ++ s!"    Base body reference: the identity itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecIterIdFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (x : BitVec 64) : BitVec 64 :=\n"
  ++ "  x\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, nonzero. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 64 × BitVec 64) :=\n"
  ++ "  [(0, 0), (9, 9)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1)).pretty == (repr t.2).pretty\n"

/-- Spec stub for `miEl` (N4d-iv-b1 wrapping `usub`). The mirror is
    the tag-erased `stdVecMinusElFwd`; edges carry ground truth
    (exact, wrap). -/
def emitStdVecMinusElSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(it, n)` steps the offset back.\n"
  ++ s!"    Base body reference: wrapping `usub` itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecMinusElFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (it n : BitVec 64) : BitVec 64 :=\n"
  ++ "  it - n\n"
  ++ "\n"
  ++ s!"/-- Edge cases: exact, wrap. -/\n"
  ++ s!"def {name}_spec_edges : List ((BitVec 64 × BitVec 64) × BitVec 64) :=\n"
  ++ "  [((10, 3), 7), ((3, 10), 18446744073709551609)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1.1 t.1.2)).pretty == (repr t.2).pretty\n"

/-- Spec stub for `mi` (N4d-iv-b1 bit-exact `s64diff`, `s64` erased
    to the 64-bit word). The mirror is the tag-erased
    `stdVecMinusFwd`; edges carry ground truth (exact, wrap). -/
def emitStdVecMinusSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(a, b)` differences the offsets.\n"
  ++ s!"    Base body reference: bit-exact `s64diff` itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecMinusFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (a b : BitVec 64) : BitVec 64 :=\n"
  ++ "  a - b\n"
  ++ "\n"
  ++ s!"/-- Edge cases: exact, wrap. -/\n"
  ++ s!"def {name}_spec_edges : List ((BitVec 64 × BitVec 64) × BitVec 64) :=\n"
  ++ "  [((10, 3), 7), ((3, 10), 18446744073709551609)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1.1 t.1.2)).pretty == (repr t.2).pretty\n"

/-- Spec stub for allocate (N4d-iv-b1 fresh storage). The mirror is
    the tag-erased `stdVecAllocFwd`; edges carry ground truth
    (empty, fresh, loud over-max). -/
def emitStdVecAllocSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(n)` allocates `n` words.\n"
  ++ s!"    Base body reference: fresh storage itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecAllocFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (n : BitVec 64) : Result (Vec32 × Nat × Nat) :=\n"
  ++ "  if (BitVec.ofNat 64 0).ult n then\n"
  ++ "    if (BitVec.ofNat 64 2305843009213693951).ult n then .error .AssertFail\n"
  ++ "    else .ok (⟨List.replicate n.toNat 0, false⟩, 0, n.toNat)\n"
  ++ "  else .ok (⟨[], false⟩, 0, 0)\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty, fresh, loud over-max. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 64 × Result (Vec32 × Nat × Nat)) :=\n"
  ++ "  [(0, .ok (⟨[], false⟩, 0, 0)),\n"
  ++ "   (1, .ok (⟨[0], false⟩, 0, 1)),\n"
  ++ "   (BitVec.ofNat 64 2305843009213693952, .error .AssertFail)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1)).pretty == (repr t.2).pretty\n"

/-- Spec stub for deallocate (N4d-iv-b1 unconditional consume). The
    mirror is the tag-erased `stdVecDeallocFwd`; edges carry ground
    truth (live consume, double-free). -/
def emitStdVecDeallocSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(t)` consumes the triple.\n"
  ++ s!"    Base body reference: the unconditional consume itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecDeallocFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (b : Vec32) (len cap : Nat) : Result (Vec32 × Nat × Nat) :=\n"
  ++ "  match vecFree b with\n"
  ++ "  | .error e => .error e\n"
  ++ "  | .ok b' => .ok (b', len, cap)\n"
  ++ "\n"
  ++ s!"/-- Edge cases: live consume, double-free. -/\n"
  ++ s!"def {name}_spec_edges : List ((Vec32 × Nat × Nat) × Result (Vec32 × Nat × Nat)) :=\n"
  ++ "  [(((⟨[1, 2], false⟩, 2, 2)), .ok (⟨[1, 2], true⟩, 2, 2)),\n"
  ++ "   (((⟨[1], true⟩, 1, 1)), .error .AssertFail)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1.1 t.1.2.1 t.1.2.2)).pretty == (repr t.2).pretty\n"

/-- Spec stub for `_M_deallocate` (N4d-iv-b1 guarded consume). The
    mirror is the tag-erased `stdVecDeallocGuardFwd`; edges carry
    ground truth (null kept, live consume). -/
def emitStdVecDeallocGuardSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(t, n)` consumes the triple unless `n == 0`.\n"
  ++ s!"    Base body reference: the `n == 0` test around the consume itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecDeallocGuardFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (b : Vec32) (len cap : Nat) (n : BitVec 64) : Result (Vec32 × Nat × Nat) :=\n"
  ++ "  if (BitVec.ofNat 64 0).ult n then\n"
  ++ "    match vecFree b with\n"
  ++ "    | .error e => .error e\n"
  ++ "    | .ok b' => .ok (b', len, cap)\n"
  ++ "  else .ok (b, len, cap)\n"
  ++ "\n"
  ++ s!"/-- Edge cases: null kept, live consume. -/\n"
  ++ s!"def {name}_spec_edges : List (((Vec32 × Nat × Nat) × BitVec 64) × Result (Vec32 × Nat × Nat)) :=\n"
  ++ "  [((((⟨[1], false⟩, 1, 1), 0)), .ok (⟨[1], false⟩, 1, 1)),\n"
  ++ "   ((((⟨[1], false⟩, 1, 1), 5)), .ok (⟨[1], true⟩, 1, 1))]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1.1.1 t.1.1.2.1 t.1.1.2.2 t.1.2)).pretty == (repr t.2).pretty\n"

/-- Spec stub for `construct` (N4d-iv-b1 placement store). The
    mirror is the tag-erased `stdVecConstructFwd`; edges carry ground
    truth (store, `OOB` past the storage words). -/
def emitStdVecConstructSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(t, p, v)` stores the word.\n"
  ++ s!"    Base body reference: the placement store itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecConstructFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (b : Vec32) (len cap : Nat) (p : BitVec 64) (x : BitVec 32) : Result (Vec32 × Nat × Nat) :=\n"
  ++ "  match vecSet b p.toNat x with\n"
  ++ "  | .error e => .error e\n"
  ++ "  | .ok b' => .ok (b', len, cap)\n"
  ++ "\n"
  ++ s!"/-- Edge cases: store, `OOB` past the storage words. -/\n"
  ++ s!"def {name}_spec_edges : List ((((Vec32 × Nat × Nat) × BitVec 64) × BitVec 32) × Result (Vec32 × Nat × Nat)) :=\n"
  ++ "  [(((((⟨[1, 2], false⟩, 2, 2), 0), 9)), .ok (⟨[9, 2], false⟩, 2, 2)),\n"
  ++ "   (((((⟨[1], false⟩, 1, 1), 5), 9)), .error .OOB)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1.1.1.1 t.1.1.1.2.1 t.1.1.1.2.2 t.1.1.2 t.1.2)).pretty == (repr t.2).pretty\n"

/-- Spec stub for relocate (N4d-iv-b1 bulk copy). The mirror is the
    tag-erased `stdVecRelocFwd`; edges carry ground truth (empty
    trip, copy, consumed source). -/
def emitStdVecRelocSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(src, dst, first, last, result)` copies the range.\n"
  ++ s!"    Base body reference: the copy loop itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecRelocFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (bS : Vec32) (lenS : Nat) (_capS : Nat) (bD : Vec32) (lenD capD : Nat) (first last result : BitVec 64) : Result (Vec32 × Nat × Nat) :=\n"
  ++ "  match stdVecBlitFold bS.val lenS bS.freed bD result.toNat first.toNat (last.toNat - first.toNat) with\n"
  ++ "  | .error e => .error e\n"
  ++ "  | .ok bD' => .ok (bD', lenD, capD)\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty trip, copy, consumed source. -/\n"
  ++ s!"def {name}_spec_edges : List (((Vec32 × Nat × Nat × Vec32 × Nat × Nat × BitVec 64 × BitVec 64 × BitVec 64)) × Result (Vec32 × Nat × Nat)) :=\n"
  ++ "  [(((⟨[], false⟩, 0, 0, ⟨[9], false⟩, 1, 1, 0, 0, 0)), .ok (⟨[9], false⟩, 1, 1)),\n"
  ++ "   (((⟨[5, 6], false⟩, 2, 2, ⟨[0, 0, 0], false⟩, 0, 3, 0, 2, 1)), .ok (⟨[0, 5, 6], false⟩, 0, 3)),\n"
  ++ "   (((⟨[5], true⟩, 1, 1, ⟨[0], false⟩, 0, 1, 0, 1, 0)), .error .AssertFail)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1.1 t.1.2.1 t.1.2.2.1 t.1.2.2.2.1 t.1.2.2.2.2.1 t.1.2.2.2.2.2.1 t.1.2.2.2.2.2.2.1 t.1.2.2.2.2.2.2.2.1 t.1.2.2.2.2.2.2.2.2)).pretty == (repr t.2).pretty\n"

/-- Spec stub for the `_M_realloc_insert` growth composition (N4d-iv-b2:
    the bind chain over the frozen b1 leaf forwards; mismatch shapes
    fail loudly through the `vecGrow*` projectors, cf.
    `stdVecGrowReallocFwd`). -/
def emitStdVecGrowReallocSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\nimport Circe.Emit.VecGrow\nimport Circe.Emit.VecCompose\n\n"
  ++ s!"/-- C++ signature: `{name}(t, pos, x)` reallocating insert (growth\n"
  ++ s!"    composition: `check_len` → `begin` → `mi` → `allocate` →\n"
  ++ s!"    `construct`-at-`k` → two `_S_relocate`s → the cap-counted\n"
  ++ s!"    `_M_deallocate` guard).\n"
  ++ s!"    Base body reference: the bind chain itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecGrowReallocFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (b : Vec32) (len cap : Nat) (pos : BitVec 64) (x : BitVec 32) : Result Value :=\n"
  ++ "  (stdVecCheckLenFwd len (BitVec.ofNat 64 1)).bind fun ckv =>\n"
  ++ "  (vecGrowU64 ckv).bind fun newlen =>\n"
  ++ "  (stdVecBeginFwd).bind fun bgv =>\n"
  ++ "  (vecGrowU64 bgv).bind fun bpos =>\n"
  ++ "  (stdVecMinusFwd pos bpos).bind fun miv =>\n"
  ++ "  (vecGrowI64 miv).bind fun kd =>\n"
  ++ "  (stdVecAllocFwd newlen).bind fun alv =>\n"
  ++ "  (vecGrowOwned alv).bind fun (bNew, lenA, capA) =>\n"
  ++ "  (stdVecConstructFwd bNew lenA capA kd x).bind fun conv =>\n"
  ++ "  (vecGrowOwned conv).bind fun (bC, lenC, capC) =>\n"
  ++ "  (stdVecRelocFwd b len cap bC lenC capC (BitVec.ofNat 64 0) kd\n"
  ++ "    (BitVec.ofNat 64 0)).bind fun r1v =>\n"
  ++ "  (vecGrowOwned r1v).bind fun (bR1, lenR1, capR1) =>\n"
  ++ "  (stdVecRelocFwd b len cap bR1 lenR1 capR1 kd (BitVec.ofNat 64 len)\n"
  ++ "    (kd + BitVec.ofNat 64 1)).bind fun r2v =>\n"
  ++ "  (vecGrowOwned r2v).bind fun (bR2, _, capR2) =>\n"
  ++ "  (stdVecDeallocGuardFwd b len cap (BitVec.ofNat 64 cap)).bind fun _ =>\n"
  ++ "  .ok (.stdVecOwned bR2\n"
  ++ "    ((BitVec.ofNat 64 len + BitVec.ofNat 64 1).toNat) capR2)\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty insert ok, `check_len` failure (frozen by evaluating `stdVecGrowReallocFwd`). -/\n"
  ++ s!"def {name}_spec_edges : List ((Vec32 × Nat × Nat × BitVec 64 × BitVec 32) × Result Value) :=\n"
  ++ "  [(((⟨[], false⟩, 0, 0, 0, 5)), .ok (.stdVecOwned ⟨[(5 : BitVec 32)], false⟩ 1 1)),\n"
  ++ "   (((⟨[], false⟩, stdVecMaxDiff, 0, 0, 5)), .error .AssertFail)]\n"
  ++ "\n"
  ++ s!"/-- Mirror-agreement entry: the stub mirror agrees with the verified forward on every edge.\n"
  ++ "    TODO (user): strengthen to the gallery equations `stdVecGrowRealloc_correct_ok` /\n"
  ++ "    `stdVecGrowRealloc_correct_err_checklen` (proved by hand in `Circe.Specs`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    match t with\n"
  ++ s!"    | ((b, len, cap, pos, x), expected) =>\n"
  ++ s!"      (repr ({name}_spec_fwd b len cap pos x)).pretty == (repr expected).pretty\n"

/-- Spec stub for the `emplace_back` composer (N4d-iv-b2: capacity
    dispatch — slow arm is the realloc bind chain at `pos = len`,
    fast arm is the construct forward at `len`; edge values frozen
    by evaluating `stdVecEmplaceBackFwd`). -/
def emitStdVecEmplaceBackSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\nimport Circe.Emit.VecGrow\nimport Circe.Emit.VecCompose\n\n"
  ++ s!"/-- C++ signature: `{name}(t, x)` appends `x` (fast construct when\n"
  ++ s!"    `len ≠ cap`, slow realloc-insert at `pos = len` otherwise).\n"
  ++ s!"    Base body reference: the dispatch itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecEmplaceBackFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (b : Vec32) (len cap : Nat) (x : BitVec 32) : Result Value :=\n"
  ++ "  if len == cap then\n"
  ++ "    (stdVecCheckLenFwd len (BitVec.ofNat 64 1)).bind fun ckv =>\n"
  ++ "    (vecGrowU64 ckv).bind fun newlen =>\n"
  ++ "    (stdVecBeginFwd).bind fun bgv =>\n"
  ++ "    (vecGrowU64 bgv).bind fun bpos =>\n"
  ++ "    (stdVecMinusFwd (BitVec.ofNat 64 len) bpos).bind fun miv =>\n"
  ++ "    (vecGrowI64 miv).bind fun kd =>\n"
  ++ "    (stdVecAllocFwd newlen).bind fun alv =>\n"
  ++ "    (vecGrowOwned alv).bind fun (bNew, lenA, capA) =>\n"
  ++ "    (stdVecConstructFwd bNew lenA capA kd x).bind fun conv =>\n"
  ++ "    (vecGrowOwned conv).bind fun (bC, lenC, capC) =>\n"
  ++ "    (stdVecRelocFwd b len cap bC lenC capC (BitVec.ofNat 64 0) kd\n"
  ++ "      (BitVec.ofNat 64 0)).bind fun r1v =>\n"
  ++ "    (vecGrowOwned r1v).bind fun (bR1, lenR1, capR1) =>\n"
  ++ "    (stdVecRelocFwd b len cap bR1 lenR1 capR1 kd (BitVec.ofNat 64 len)\n"
  ++ "      (kd + BitVec.ofNat 64 1)).bind fun r2v =>\n"
  ++ "    (vecGrowOwned r2v).bind fun (bR2, _, capR2) =>\n"
  ++ "    (stdVecDeallocGuardFwd b len cap (BitVec.ofNat 64 cap)).bind fun _ =>\n"
  ++ "    .ok (.stdVecOwned bR2\n"
  ++ "      ((BitVec.ofNat 64 len + BitVec.ofNat 64 1).toNat) capR2)\n"
  ++ "  else (stdVecConstructFwd b len cap (BitVec.ofNat 64 len) x).bind fun conv =>\n"
  ++ "    (vecGrowOwned conv).bind fun (b', _, _) =>\n"
  ++ "    .ok (.stdVecOwned b' (len + 1) cap)\n"
  ++ "\n"
  ++ s!"/-- Edge cases: fast append, slow realloc-insert, `check_len` failure (frozen by evaluating `stdVecEmplaceBackFwd`). -/\n"
  ++ s!"def {name}_spec_edges : List ((Vec32 × Nat × Nat × BitVec 32) × Result Value) :=\n"
  ++ "  [(((⟨[(0 : BitVec 32)], false⟩, 0, 1, 5)), .ok (.stdVecOwned ⟨[(5 : BitVec 32)], false⟩ 1 1)),\n"
  ++ "   (((⟨[], false⟩, 0, 0, 5)), .ok (.stdVecOwned ⟨[(5 : BitVec 32)], false⟩ 1 1)),\n"
  ++ "   (((⟨[], false⟩, stdVecMaxDiff, stdVecMaxDiff, 5)), .error .AssertFail)]\n"
  ++ "\n"
  ++ s!"/-- Mirror-agreement entry: the stub mirror agrees with the verified forward on every edge.\n"
  ++ "    TODO (user): strengthen to the gallery equations `stdVecEmplaceBack_correct_fast` /\n"
  ++ "    `stdVecEmplaceBack_correct_ok_fast` / `stdVecEmplaceBack_correct_slow` /\n"
  ++ "    `stdVecEmplaceBack_correct_ok_slow` / `stdVecEmplaceBack_correct_err_checklen` /\n"
  ++ "    `stdVecEmplaceBack_correct_err_construct` (proved by hand in `Circe.Specs`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    match t with\n"
  ++ s!"    | ((b, len, cap, x), expected) =>\n"
  ++ s!"      (repr ({name}_spec_fwd b len cap x)).pretty == (repr expected).pretty\n"

/-- Spec stub for the `push_back` forwarder: the mirror delegates to
    the verified `stdVecPushBackFwd` (same `Base` op as the emitted
    forward, so the proved `stdVecPushBack_correct_*` specs transfer
    verbatim by body identity). -/
def emitStdVecPushBackSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\nimport Circe.Emit.VecGrow\nimport Circe.Emit.VecCompose\n\n"
  ++ s!"/-- C++ signature: `{name}(t, x)` forwards to `emplace_back` (the reference result is discarded; the C++ `void` functionalizes as triple threading).\n"
  ++ s!"    Base body reference: the delegation itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `stdVecPushBackFwd`). -/\n"
  ++ s!"def {name}_spec_fwd (b : Vec32) (len cap : Nat) (x : BitVec 32) : Result Value :=\n"
  ++ "  stdVecPushBackFwd b len cap x\n"
  ++ "\n"
  ++ s!"/-- Edge cases: fast append, slow realloc-insert, `check_len` failure (frozen by evaluating `stdVecPushBackFwd`). -/\n"
  ++ s!"def {name}_spec_edges : List ((Vec32 × Nat × Nat × BitVec 32) × Result Value) :=\n"
  ++ "  [(((⟨[(0 : BitVec 32)], false⟩, 0, 1, 5)), .ok (.stdVecOwned ⟨[(5 : BitVec 32)], false⟩ 1 1)),\n"
  ++ "   (((⟨[], false⟩, 0, 0, 5)), .ok (.stdVecOwned ⟨[(5 : BitVec 32)], false⟩ 1 1)),\n"
  ++ "   (((⟨[], false⟩, stdVecMaxDiff, stdVecMaxDiff, 5)), .error .AssertFail)]\n"
  ++ "\n"
  ++ s!"/-- Mirror-agreement entry: the stub mirror agrees with the verified forward on every edge.\n"
  ++ "    TODO (user): strengthen to the gallery equations `stdVecPushBack_correct_slow` /\n"
  ++ "    `stdVecPushBack_correct_ok_slow` / `stdVecPushBack_correct_fast` /\n"
  ++ "    `stdVecPushBack_correct_ok_fast` / `stdVecPushBack_correct_err_checklen` /\n"
  ++ "    `stdVecPushBack_correct_err_construct` (proved by hand in `Circe.Specs`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    match t with\n"
  ++ s!"    | ((b, len, cap, x), expected) =>\n"
  ++ s!"      (repr ({name}_spec_fwd b len cap x)).pretty == (repr expected).pretty\n"

/-- Spec stub for the closed `vec_push_sum` entry: the mirror delegates
    to the verified `vecPushSumEntryFwd` (same forward as the emitted
    entry, so the proved `vecPushSumEntry_correct` spec transfers
    verbatim by body identity). -/
def emitVecPushSumEntrySpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\nimport Circe.Emit.VecGrow\nimport Circe.Emit.VecCompose\n\n"
  ++ s!"/-- C++ signature: `{name}()` runs the closed push/read/sum script (three `push_back`, three `operator[]`, two adds, destructor).\n"
  ++ s!"    Base body reference: the delegation itself (cf. emitted `{name}_fwd`,\n"
  ++ s!"    `vecPushSumEntryFwd`). -/\n"
  ++ s!"def {name}_spec_fwd : Result Value :=\n"
  ++ "  vecPushSumEntryFwd\n"
  ++ "\n"
  ++ s!"/-- Edge cases: the single closed run `1 + 2 + 3 = 6` (frozen by evaluating `vecPushSumEntryFwd`). -/\n"
  ++ s!"def {name}_spec_edges : List (Unit × Result Value) :=\n"
  ++ "  [((), .ok (.i32 (BitVec.ofNat 32 6)))]\n"
  ++ "\n"
  ++ s!"/-- Mirror-agreement entry: the stub mirror agrees with the verified forward on every edge.\n"
  ++ "    TODO (user): strengthen to the gallery equation `vecPushSumEntry_correct`\n"
  ++ "    (proved by hand in `Circe.Specs`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd)).pretty == (repr t.2).pretty\n"

/-- Spec stub for the `sum_caller` shape (S1 delegation). -/
def emitSumCallerSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `{name}(a, n)` delegates to `sum_array_fwd`.\n"
  ++ s!"    Base body reference: `prefixSumU32` (cf. emitted `{name}_fwd`, `sumCallerFwd_is_call`). -/\n"
  ++ s!"def {name}_spec_fwd " ++ "{n : Nat} (a : BoundedList (BitVec 32) n) : Result (BitVec 32) :=\n"
  ++ "  .ok (prefixSumU32 a.val a.val.length)\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty / singleton / max-fuel (length = bound). -/\n"
  ++ s!"def {name}_spec_edges : List (List (BitVec 32)) :=\n"
  ++ "  [[], [0], [1], [1, 2, 3], [0xFFFFFFFF, 1]]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the `List.sum` equation holds on every edge\n"
  ++ "    (cf. `sumCallerFwd_is_call`, `sum_correct`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun l =>\n"
  ++ "    (repr (prefixSumU32 l l.length)).pretty == (repr ((l.take l.length).sum)).pretty\n"

/-- Spec stub for the `translate` shape (S2 struct-by-value). -/
def emitTranslateSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `struct Point {name}(struct Point p, int32_t dx, int32_t dy)`.\n"
  ++ s!"    Base body reference: `pointTranslate` (cf. emitted `{name}_fwd`, `evalFuncFuel_translate`). -/\n"
  ++ s!"def {name}_spec_fwd (p : Point) (dx dy : BitVec 32) : Result Point :=\n"
  ++ "  pointTranslate p dx dy\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, x-overflow, y-overflow. -/\n"
  ++ s!"def {name}_spec_edges : List (Point × BitVec 32 × BitVec 32) :=\n"
  ++ "  [((⟨0, 0⟩ : Point), 0, 0), ((⟨1, 2⟩ : Point), 3, 4),\n"
  ++ "   ((⟨0x7FFFFFFF, 0⟩ : Point), 1, 0), ((⟨0, 0x7FFFFFFF⟩ : Point), 0, 1)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with `pointTranslate` on every edge.\n"
  ++ "    TODO (user): strengthen to the ok/err bridges (`translateFwd_ok_bridge`,\n"
  ++ "    `translateFwd_err_x/y` — all three fire in `cir_simp`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1 t.2.1 t.2.2)).pretty\n"
  ++ s!"      == (repr (pointTranslate t.1 t.2.1 t.2.2)).pretty\n"

/-- Spec stub for the `methodSum` shape (M2a method leaf). -/
def emitMethodSumSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `int32_t Point::sum() const` (`{name}`).\n"
  ++ s!"    Base body reference: `pointSum` (cf. emitted `{name}_fwd`, `evalFuncFuel_methodSum`). -/\n"
  ++ s!"def {name}_spec_fwd (p : Point) : Result (BitVec 32) :=\n"
  ++ "  pointSum p\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, x-overflow, y-overflow. -/\n"
  ++ s!"def {name}_spec_edges : List Point :=\n"
  ++ "  [(⟨0, 0⟩ : Point), (⟨1, 2⟩ : Point),\n"
  ++ "   (⟨0x7FFFFFFF, 0⟩ : Point), (⟨0, 0x7FFFFFFF⟩ : Point)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with `pointSum` on every edge.\n"
  ++ "    TODO (user): strengthen to the ok/err bridges (`methodSumFwd_ok/err`,\n"
  ++ "    `pointSum_ok/err` — all four fire in `cir_simp`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun p =>\n"
  ++ s!"    (repr ({name}_spec_fwd p)).pretty\n"
  ++ s!"      == (repr (pointSum p)).pretty\n"

/-- Spec stub for the `pointSumRef` shape (M2a entry). -/
def emitPointSumRefSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `int32_t {name}(const Point &p)` (delegates to `Point::sum`).\n"
  ++ s!"    Base body reference: `pointSum` (cf. emitted `{name}_fwd`, `evalProgFunc_pointSumRef`). -/\n"
  ++ s!"def {name}_spec_fwd (p : Point) : Result (BitVec 32) :=\n"
  ++ "  pointSum p\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, x-overflow, y-overflow. -/\n"
  ++ s!"def {name}_spec_edges : List Point :=\n"
  ++ "  [(⟨0, 0⟩ : Point), (⟨1, 2⟩ : Point),\n"
  ++ "   (⟨0x7FFFFFFF, 0⟩ : Point), (⟨0, 0x7FFFFFFF⟩ : Point)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with `pointSum` on every edge.\n"
  ++ "    TODO (user): strengthen to the call-delegation equation\n"
  ++ "    (`pointSumRefFwd_is_call`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun p =>\n"
  ++ s!"    (repr ({name}_spec_fwd p)).pretty\n"
  ++ s!"      == (repr (pointSum p)).pretty\n"

/-- Spec stub for the `accCtor` shape (M2b ctor leaf). -/
def emitAccCtorSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `Acc::Acc()` (`{name}`: field-init `s = 0`).\n"
  ++ s!"    Base body reference: `accCtor` (cf. emitted `{name}_fwd`, `evalFuncFuel_accCtor`). -/\n"
  ++ s!"def {name}_spec_fwd : Result (BitVec 32) :=\n"
  ++ "  .ok accCtor\n"
  ++ "\n"
  ++ s!"/-- Edge cases: the ctor is total (one trivial edge). -/\n"
  ++ s!"def {name}_spec_edges : List Unit :=\n"
  ++ "  [()]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with `accCtor` on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun _ =>\n"
  ++ s!"    (repr ({name}_spec_fwd)).pretty\n"
  ++ s!"      == (repr ((.ok accCtor : Result (BitVec 32)))).pretty\n"

/-- Spec stub for the `accAdd` shape (M2b method leaf). -/
def emitAccAddSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `void Acc::add(int32_t v)` (`{name}`: checked `s += v`).\n"
  ++ s!"    Base body reference: `accAdd` (cf. emitted `{name}_fwd`, `evalFuncFuel_accAdd`). -/\n"
  ++ s!"def {name}_spec_fwd (s v : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  accAdd s v\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, overflow. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32 × BitVec 32) :=\n"
  ++ "  [(0, 0), (1, 2), (0x7FFFFFFF, 0), (0x7FFFFFFF, 1)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with `accAdd` on every edge.\n"
  ++ "    TODO (user): strengthen to the ok/err bridges (`accAddFwd_ok/err`\n"
  ++ "    — both fire in `cir_simp`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1 t.2)).pretty\n"
  ++ s!"      == (repr (accAdd t.1 t.2)).pretty\n"

/-- Spec stub for the `accGet` shape (M2b getter leaf). -/
def emitAccGetSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `int32_t Acc::get() const` (`{name}`: identity).\n"
  ++ s!"    Base body reference: `accGet` (cf. emitted `{name}_fwd`, `evalFuncFuel_accGet`). -/\n"
  ++ s!"def {name}_spec_fwd (s : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  accGet s\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, extrema. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32) :=\n"
  ++ "  [0, 1, 0x7FFFFFFF, 0x80000000]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with `accGet` on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun s =>\n"
  ++ s!"    (repr ({name}_spec_fwd s)).pretty\n"
  ++ s!"      == (repr (accGet s)).pretty\n"

/-- Spec stub for the `accDtor` shape (M2b trivial-dtor leaf). -/
def emitAccDtorSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `Acc::~Acc()` (`{name}`: no-op identity).\n"
  ++ s!"    Base body reference: `accDtor` (cf. emitted `{name}_fwd`, `evalFuncFuel_accDtor`). -/\n"
  ++ s!"def {name}_spec_fwd (t : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  accDtor t\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, extrema. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32) :=\n"
  ++ "  [0, 1, 0x7FFFFFFF, 0x80000000]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with `accDtor` on every edge. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t)).pretty\n"
  ++ s!"      == (repr (accDtor t)).pretty\n"

/-- Spec stub for the `accTwo` shape (M2b entry). -/
def emitAccTwoSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `int32_t {name}(int32_t a, int32_t b)` (ctor + two `add` + `get`, dtor no-op).\n"
  ++ s!"    Base body reference: `accTwo` (cf. emitted `{name}_fwd`, `evalProgFunc_accTwo`). -/\n"
  ++ s!"def {name}_spec_fwd (a b : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  accTwo a b\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, first-add overflow, second-add overflow. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32 × BitVec 32) :=\n"
  ++ "  [(0, 0), (1, 2), (0x7FFFFFFF, 0), (0x7FFFFFFF, 1), (1, 0x7FFFFFFF)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with `accTwo` on every edge.\n"
  ++ "    TODO (user): strengthen to the ok/err bridges (`accTwo_ok/err_a/err_b`,\n"
  ++ "    `accTwoFwd_is_accTwo` — all four fire in `cir_simp`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1 t.2)).pretty\n"
  ++ s!"      == (repr (accTwo t.1 t.2)).pretty\n"

/-- Spec stub for the move-ctor leaf (N4b `_ZN3AccC2EOS_`). -/
def emitAccMoveCtorSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `{name}(dst, src)` move ctor (dst takes src word; `o.s = 0` is entry-level).\n"
  ++ s!"    Base body reference: `accMoveCtor` (cf. emitted `{name}_fwd`, `accMoveCtorFwd_is_ok`). -/\n"
  ++ s!"def {name}_spec_fwd (d s : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  accMoveCtor d s\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, max word (move never fails). -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32 × BitVec 32) :=\n"
  ++ "  [(0, 0), (0, 1), (1, 0x7FFFFFFF), (0xFFFFFFFF, 0xFFFFFFFF)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with `accMoveCtor` on every edge.\n"
  ++ "    TODO (user): strengthen to `accMoveCtorFwd_is_ok`. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1 t.2)).pretty\n"
  ++ s!"      == (repr (accMoveCtor t.1 t.2)).pretty\n"

/-- Spec stub for the `move_acc` entry (N4b). -/
def emitMoveAccSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `int32_t {name}(int32_t a, int32_t b)` (move + two `add` + `get`, dtors no-op).\n"
  ++ s!"    Base body reference: `moveAcc` (cf. emitted `{name}_fwd`, `evalProgFunc_moveAcc`). -/\n"
  ++ s!"def {name}_spec_fwd (a b : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  moveAcc a b\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, first-add overflow, second-add overflow. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32 × BitVec 32) :=\n"
  ++ "  [(0, 0), (1, 2), (0x7FFFFFFF, 0), (0x7FFFFFFF, 1), (1, 0x7FFFFFFF)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with `moveAcc` on every edge.\n"
  ++ "    TODO (user): strengthen to the ok/err bridges (`moveAcc_ok/err_a/err_b`,\n"
  ++ "    `moveAccFwd_is_moveAcc` — all four fire in `cir_simp`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1 t.2)).pretty\n"
  ++ s!"      == (repr (moveAcc t.1 t.2)).pretty\n"

/-- Spec stub for the `scope_early` entry (N4b). -/
def emitScopeEarlySpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `int32_t {name}(int32_t a, int32_t b)` (early `get` on `a == b`, else `add` + `get`, dtors no-op).\n"
  ++ s!"    Base body reference: `scopeEarly` (cf. emitted `{name}_fwd`, `evalProgFunc_scopeEarly`). -/\n"
  ++ s!"def {name}_spec_fwd (a b : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  scopeEarly a b\n"
  ++ "\n"
  ++ s!"/-- Edge cases: equal args (early path), zero, unit, first-add overflow, second-add overflow. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32 × BitVec 32) :=\n"
  ++ "  [(0, 0), (1, 1), (1, 2), (0x7FFFFFFF, 0), (0x7FFFFFFF, 1), (1, 0x7FFFFFFF)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with `scopeEarly` on every edge.\n"
  ++ "    TODO (user): strengthen to the ok/err bridges (`scopeEarly_ok_eq/ok_ne/err_a/err_b`,\n"
  ++ "    `scopeEarlyFwd_is_scopeEarly` — all five fire in `cir_simp`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1 t.2)).pretty\n"
  ++ s!"      == (repr (scopeEarly t.1 t.2)).pretty\n"

/-- Spec stub for the `boxThrough` shape (M2c entry). -/
def emitBoxThroughSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C++ signature: `int32_t {name}(int32_t x)` (`new` → read → `delete` passthrough).\n"
  ++ s!"    Base body reference: `boxThrough` (cf. emitted `{name}_fwd`, `evalFuncFuel_boxThrough`). -/\n"
  ++ s!"def {name}_spec_fwd (x : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  boxThrough x\n"
  ++ "\n"
  ++ s!"/-- Edge cases: zero, unit, extrema (the passthrough is total). -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32) :=\n"
  ++ "  [0, 1, 0x7FFFFFFF, 0x80000000]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with `boxThrough` on every edge.\n"
  ++ "    TODO (user): strengthen to the identity equation (`boxThrough_ok`\n"
  ++ "    — fires in `cir_simp`). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun x =>\n"
  ++ s!"    (repr ({name}_spec_fwd x)).pretty\n"
  ++ s!"      == (repr (boxThrough x)).pretty\n"

/-- Spec stub for the `nested_sum` shape (S3a). -/
def emitNestedSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `uint32_t {name}(uint32_t n, uint32_t m)` (nested bounded loops, wrapping).\n"
  ++ s!"    Base body reference: `nestedSumU32` (cf. emitted `{name}_fwd`, `emit_correct_nested`). -/\n"
  ++ s!"def {name}_spec_fwd (n m : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  .ok (nestedSumU32 n.toNat m.toNat)\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty outer / empty inner / unit / small square. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32 × BitVec 32) :=\n"
  ++ "  [(0, 0), (0, 5), (5, 0), (1, 1), (3, 4), (10, 10)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with `nestedSumU32` on every edge.\n"
  ++ "    TODO (user): strengthen to the double-fold equation. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun p =>\n"
  ++ s!"    (repr ({name}_spec_fwd p.1 p.2)).pretty\n"
  ++ s!"      == (repr ((Except.ok (nestedSumU32 p.1.toNat p.2.toNat) : Result (BitVec 32)))).pretty\n"

/-- Spec stub for the `skip_sum` shape (S3a break/continue). -/
def emitSkipSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `uint32_t {name}(uint32_t n)` (`continue` at 2, `break` at 8).\n"
  ++ s!"    Base body reference: `skipSumU32` (cf. emitted `{name}_fwd`, `emit_correct_skip`). -/\n"
  ++ s!"def {name}_spec_fwd (n : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  .ok (skipSumU32 n.toNat)\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty / singleton / the skipped 2 / the break cap 8–9 / above cap. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32) :=\n"
  ++ "  [0, 1, 2, 3, 8, 9, 100]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with `skipSumU32` on every edge.\n"
  ++ "    TODO (user): strengthen to the capped-range equation. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun n =>\n"
  ++ s!"    (repr ({name}_spec_fwd n)).pretty\n"
  ++ s!"      == (repr ((Except.ok (skipSumU32 n.toNat) : Result (BitVec 32)))).pretty\n"

/-- Spec stub for the `find_eq` shape (S3a early return). -/
def emitFindEqSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `uint32_t {name}(uint32_t *a, uint32_t n, uint32_t k)`\n"
  ++ "    (first match, else length, else `OOB`).\n"
  ++ s!"    Base body reference: `findEqOut` (cf. emitted `{name}_fwd`, `emit_correct_find`). -/\n"
  ++ s!"def {name}_spec_fwd (a : List (BitVec 32)) (n k : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  findEqOut a n.toNat k\n"
  ++ "\n"
  ++ s!"/-- Edge cases: empty / singleton hit / hit / miss / over-long length. -/\n"
  ++ s!"def {name}_spec_edges : List (List (BitVec 32) × BitVec 32 × BitVec 32) :=\n"
  ++ "  [([], 0, 0), ([1], 1, 1), ([1, 2, 3], 3, 2), ([1, 2, 3], 3, 9), ([1, 2, 3], 9, 2)]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the mirror agrees with `findEqOut` on every edge.\n"
  ++ "    TODO (user): strengthen to the hit/miss/`OOB` equation. -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun t =>\n"
  ++ s!"    (repr ({name}_spec_fwd t.1 t.2.1 t.2.2)).pretty\n"
  ++ s!"      == (repr (findEqOut t.1 t.2.1.toNat t.2.2)).pretty\n"

/-- Spec stub for the `cls` shape (S3a switch-as-if-chain). -/
def emitClsSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `uint32_t {name}(uint32_t x)` (`switch` on 0/1 + default).\n"
  ++ s!"    Base body reference: the if-chain (cf. emitted `{name}_fwd`, `emit_correct_cls`). -/\n"
  ++ s!"def {name}_spec_fwd (x : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  if x == 0 then .ok 10\n"
  ++ "  else if x == 1 then .ok 20\n"
  ++ "  else .ok 30\n"
  ++ "\n"
  ++ s!"/-- Edge cases: both cases, default, max. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32) :=\n"
  ++ "  [0, 1, 2, 0xFFFFFFFF]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the class equation holds on every edge (this one is\n"
  ++ "    already the spec — the if-chain is the whole body). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun x =>\n"
  ++ s!"    (repr ({name}_spec_fwd x)).pretty\n"
  ++ "      == (repr (((if x == (0 : BitVec 32) then (Except.ok (10 : BitVec 32)) else if x == (1 : BitVec 32) then (Except.ok (20 : BitVec 32)) else (Except.ok (30 : BitVec 32))) : Result (BitVec 32)))).pretty\n"

/-- Spec stub for the `cls_fall` shape (N6b-i switch with fallthrough). -/
def emitClsFallSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `uint32_t {name}(uint32_t x)` (`switch` on 0/1 + default, empty `case 0` falls through to `case 1`).\n"
  ++ s!"    Base body reference: the if-chain (cf. emitted `{name}_fwd`, `emit_correct_clsFall`). -/\n"
  ++ s!"def {name}_spec_fwd (x : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  if x == 0 then .ok 10\n"
  ++ "  else if x == 1 then .ok 10\n"
  ++ "  else .ok 30\n"
  ++ "\n"
  ++ s!"/-- Edge cases: both cases (fallthrough shares the arm), default, max. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32) :=\n"
  ++ "  [0, 1, 2, 0xFFFFFFFF]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the class equation holds on every edge (this one is\n"
  ++ "    already the spec — the if-chain is the whole body). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun x =>\n"
  ++ s!"    (repr ({name}_spec_fwd x)).pretty\n"
  ++ "      == (repr (((if x == (0 : BitVec 32) then (Except.ok (10 : BitVec 32)) else if x == (1 : BitVec 32) then (Except.ok (10 : BitVec 32)) else (Except.ok (30 : BitVec 32))) : Result (BitVec 32)))).pretty\n"

/-- Spec stub for the `cls_break` shape (N6b-ii break-switch). -/
def emitClsBreakSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `uint32_t {name}(uint32_t x)` (`switch` on 0/1, no `default`: guarded stores + `break`, `99` initializer).\n"
  ++ s!"    Base body reference: the guarded assigns (cf. emitted `{name}_fwd`, `emit_correct_clsBreak`). -/\n"
  ++ s!"def {name}_spec_fwd (x : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  .ok (if x == 0 then 10 else if x == 1 then 20 else 99)\n"
  ++ "\n"
  ++ s!"/-- Edge cases: both cases, initializer path, max. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32) :=\n"
  ++ "  [0, 1, 2, 0xFFFFFFFF]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the class equation holds on every edge (this one is\n"
  ++ "    already the spec — the guarded assigns are the whole body). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun x =>\n"
  ++ s!"    (repr ({name}_spec_fwd x)).pretty\n"
  ++ "      == (repr (((Except.ok (if x == (0 : BitVec 32) then (10 : BitVec 32) else if x == (1 : BitVec 32) then (20 : BitVec 32) else (99 : BitVec 32))) : Result (BitVec 32)))).pretty\n"

/-- Spec stub for the `cls_dense` shape (N6b-i eight-case switch). -/
def emitClsDenseSpecText (name : String) : String :=
  emitSpecHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- C signature: `uint32_t {name}(uint32_t x)` (`switch` on 0..7 + default).\n"
  ++ s!"    Base body reference: the if-chain (cf. emitted `{name}_fwd`, `emit_correct_clsDense`). -/\n"
  ++ s!"def {name}_spec_fwd (x : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  if x == 0 then .ok 0\n"
  ++ "  else if x == 1 then .ok 10\n"
  ++ "  else if x == 2 then .ok 20\n"
  ++ "  else if x == 3 then .ok 30\n"
  ++ "  else if x == 4 then .ok 40\n"
  ++ "  else if x == 5 then .ok 50\n"
  ++ "  else if x == 6 then .ok 60\n"
  ++ "  else if x == 7 then .ok 70\n"
  ++ "  else .ok 80\n"
  ++ "\n"
  ++ s!"/-- Edge cases: every case, default, max. -/\n"
  ++ s!"def {name}_spec_edges : List (BitVec 32) :=\n"
  ++ "  [0, 1, 2, 3, 4, 5, 6, 7, 8, 0xFFFFFFFF]\n"
  ++ "\n"
  ++ s!"/-- Prop-test entry: the class equation holds on every edge (this one is\n"
  ++ "    already the spec — the if-chain is the whole body). -/\n"
  ++ s!"def {name}_spec_check : Bool :=\n"
  ++ s!"  {name}_spec_edges.all fun x =>\n"
  ++ s!"    (repr ({name}_spec_fwd x)).pretty\n"
  ++ "      == (repr (((if x == (0 : BitVec 32) then (Except.ok (0 : BitVec 32)) else if x == (1 : BitVec 32) then (Except.ok (10 : BitVec 32)) else if x == (2 : BitVec 32) then (Except.ok (20 : BitVec 32)) else if x == (3 : BitVec 32) then (Except.ok (30 : BitVec 32)) else if x == (4 : BitVec 32) then (Except.ok (40 : BitVec 32)) else if x == (5 : BitVec 32) then (Except.ok (50 : BitVec 32)) else if x == (6 : BitVec 32) then (Except.ok (60 : BitVec 32)) else if x == (7 : BitVec 32) then (Except.ok (70 : BitVec 32)) else (Except.ok (80 : BitVec 32))) : Result (BitVec 32)))).pretty\n"
