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
