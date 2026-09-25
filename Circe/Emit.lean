/-
Circe.Emit — verified emitter `CoreIR → Lean` (forward + backward defs).

Phase 3: real emitter for the `add`/`incr` fragment.
- `matchFrag` recognizes the two admitted `Func` shapes (by-value `add`;
  single-`mutBorrow` `incr` returning `p + 1`).
- `addFwd`/`incrFwd` are the verified forward functions (Value level);
  `emit_correct_add`/`emit_correct_incr` prove they agree with `evalFunc`
  on the canonical `addFunc`/`incrFunc`, with error-preservation
  corollaries.
- `emitFunc` renders an accepted `Func` to `EmittedFunc` file text
  (`out/Add.lean`, `out/Incr.lean` via `tools/GenOut.lean`); anything else
  is rejected with `EmitError.notFragment` (loudly — never silently
  modeled).

Trust note: the *rendering* (Value-tag erasure to `BitVec` text) is
trusted, like the parser; what is verified is that the rendered
definitions have exactly the semantics of `evalFunc` on the fragment.
`tools/check-phase3.sh` regenerates the outputs and `diff`s them against
the checked-in goldens (`tests/golden/*.lean`, also spot-checked by the
`native_decide` examples below on clean builds), and `lake env lean`
typechecks the rendered files.
Borrow-returns (`choose`-shape) arrive in Phase 4.
-/
import Circe.Base
import Circe.CoreIR
import Circe.Eval

/-! ## Fragment shapes -/

/-- The Phase 3 admitted fragment. -/
inductive FragKind : Type
  | add
  | incr
  deriving DecidableEq, Repr

/-- Recognize the two admitted `Func` shapes. Anything else is `none`
    (and `emitFunc` rejects it loudly). -/
def matchFrag : Func → Option FragKind
  | ⟨_, [⟨"a", .i 32, .owned⟩, ⟨"b", .i 32, .owned⟩], _,
      .return_ (.add (.var "a") (.var "b"))⟩ => some .add
  | ⟨_, [⟨"p", .i 32, .mutBorrow 0⟩], _,
      .return_ (.add (.var "p") (.lit (.i32 one)))⟩ =>
    if one == 1 then some .incr else none
  | _ => none

/-- Canonical CoreIR for `tests/c/add.c`
    (`int32_t add(int32_t a, int32_t b) { return a + b; }`).
    Stands in for validated CoreIR until the parser lands in Phase 4. -/
def addFunc : Func :=
  ⟨"add", [{ name := "a", ty := .i 32, role := .owned },
           { name := "b", ty := .i 32, role := .owned }],
   .i 32, .return_ (.add (.var "a") (.var "b"))⟩

/-- Canonical CoreIR for `tests/c/incr_ptr.c`
    (`void incr(int32_t *__restrict p) { *p = *p + 1; }`, functionalized:
    value in, updated value out). -/
def incrFunc : Func :=
  ⟨"incr", [{ name := "p", ty := .i 32, role := .mutBorrow 0 }],
   .i 32, .return_ (.add (.var "p") (.lit (.i32 1)))⟩

theorem matchFrag_add : matchFrag addFunc = some .add := rfl

theorem matchFrag_incr : matchFrag incrFunc = some .incr := rfl

/-! ## Verified forward functions (Value level) -/

/-- Verified forward function for `add` (cf. rendered `add_fwd`). -/
def addFwd (a b : BitVec 32) : Result Value := .i32 <$> checkedAddI32 a b

/-- Verified forward function for `incr` (cf. rendered `incr_fwd`). -/
def incrFwd (p : BitVec 32) : Result Value := .i32 <$> checkedIncrI32 p

/-- `(<$>)` on `Result` computes on both constructors (for the corollaries).
    Proved by `rfl` (needs default transparency to see through the
    `Functor` instance, so later proofs use `exact`, not `simp`). -/
theorem i32_map_error (e : Panic) :
    Value.i32 <$> (Except.error e : Result (BitVec 32)) = .error e := rfl

theorem i32_map_ok (r : BitVec 32) :
    Value.i32 <$> (Except.ok r : Result (BitVec 32)) = .ok (.i32 r) := rfl

/-! ## `emit_correct` for the fragment -/

/-- Env facts for the `add` shape (closed name (dis)equalities). -/
theorem envLookup_add_a (a b : BitVec 32) :
    envLookup [("a", .i32 a), ("b", .i32 b)] "a" = some (.i32 a) := by
  simp [envLookup]

theorem envLookup_add_b (a b : BitVec 32) :
    envLookup [("a", .i32 a), ("b", .i32 b)] "b" = some (.i32 b) := by
  simp [envLookup, show ("b" : String) ≠ "a" by decide]

/-- Env fact for the `incr` shape. -/
theorem envLookup_incr_p (p : BitVec 32) :
    envLookup [("p", .i32 p)] "p" = some (.i32 p) := by
  simp [envLookup]

/-- Emitter correctness, `add`: evaluating the CoreIR function agrees with
    the forward function on all inputs (ok and error paths). -/
theorem emit_correct_add (a b : BitVec 32) :
    evalFunc addFunc [.i32 a, .i32 b] = addFwd a b := by
  have ha := envLookup_add_a a b
  have hb := envLookup_add_b a b
  simp only [evalFunc, addFunc, bindArgs, evalStmt, evalExpr, addFwd, ha, hb]
  cases checkedAddI32 a b <;> rfl

/-- Emitter correctness, `incr`. -/
theorem emit_correct_incr (p : BitVec 32) :
    evalFunc incrFunc [.i32 p] = incrFwd p := by
  have hp := envLookup_incr_p p
  simp only [evalFunc, incrFunc, bindArgs, evalStmt, evalExpr, litVal, incrFwd,
    checkedIncrI32, hp]
  cases checkedAddI32 p 1 <;> rfl

/-- Corollary: `add` errors are preserved exactly. -/
theorem emit_correct_add_err (a b : BitVec 32) (e : Panic)
    (h : checkedAddI32 a b = .error e) :
    evalFunc addFunc [.i32 a, .i32 b] = .error e := by
  rw [emit_correct_add]
  unfold addFwd
  rw [h]
  exact i32_map_error e

/-- Corollary: `add` successes deliver the wrapped sum as a value. -/
theorem emit_correct_add_ok (a b r : BitVec 32)
    (h : checkedAddI32 a b = .ok r) :
    evalFunc addFunc [.i32 a, .i32 b] = .ok (.i32 r) := by
  rw [emit_correct_add]
  unfold addFwd
  rw [h]
  exact i32_map_ok r

/-- Corollary: `incr` errors are preserved exactly. -/
theorem emit_correct_incr_err (p : BitVec 32) (e : Panic)
    (h : checkedIncrI32 p = .error e) :
    evalFunc incrFunc [.i32 p] = .error e := by
  rw [emit_correct_incr]
  unfold incrFwd
  rw [h]
  exact i32_map_error e

/-- Corollary: `incr` successes deliver the incremented value. -/
theorem emit_correct_incr_ok (p r : BitVec 32)
    (h : checkedIncrI32 p = .ok r) :
    evalFunc incrFunc [.i32 p] = .ok (.i32 r) := by
  rw [emit_correct_incr]
  unfold incrFwd
  rw [h]
  exact i32_map_ok r

/-! ## Rendering to Lean file text -/

/-- Emission failures: only "not in the admitted fragment" exists in
    Phase 3 (oracle/aliasing rejections arrive with `validate` in Phase 4). -/
inductive EmitError : Type
  | notFragment : String → EmitError
  deriving DecidableEq, Repr

/-- Emitted Lean code for one function: forward definition file text, plus
    an optional backward definition for borrow-returns (`choose`-shape,
    Phase 4). -/
structure EmittedFunc : Type where
  forward : String
  backward : Option String
  deriving DecidableEq, Repr

/-- File header shared by all rendered outputs. -/
def emitHeader : String :=
  "-- Generated by the Circe emitter (Phase 3) from validated CoreIR. Do not edit.\n"
  ++ "-- Emitter correctness (`Circe.Emit.emit_correct_add` / `emit_correct_incr`):\n"
  ++ "-- this file is the tag-erased rendering of the verified forward function\n"
  ++ "-- (`Value.i32` tags dropped; pretty-printing is trusted, semantics verified).\n"
  ++ "-- Checked by `lake env lean`; see `tools/check-phase3.sh`.\n"

/-- Render the `add` forward definition (`add_fwd`). -/
def emitAddText (name : String) : String :=
  emitHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- Pure translation of `{name}`: values in, value out (no memory). -/\n"
  ++ s!"def {name}_fwd (a b : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  checkedAddI32 a b\n"

/-- Render the `incr` forward definition (`incr_fwd`), with the
    caller-side rewrite in the doc comment. -/
def emitIncrText (name : String) : String :=
  emitHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- Pure translation of `{name}` (`*p = *p + 1`, functionalized).\n"
  ++ s!"    Caller rewrite: `incr(&y)` becomes `y ← {name}_fwd y`. -/\n"
  ++ s!"def {name}_fwd (p : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  checkedIncrI32 p\n"

/-- The emitter: accepted fragment renders to file text; everything else
    is rejected loudly (never silently modeled). -/
def emitFunc (f : Func) : Except EmitError EmittedFunc :=
  match matchFrag f with
  | some .add => .ok ⟨emitAddText f.name, none⟩
  | some .incr => .ok ⟨emitIncrText f.name, none⟩
  | none => .error (.notFragment s!"not in the Phase 3 fragment: {f.name}")

/-- Rejection is loud and names the function. -/
theorem emitFunc_rejects (f : Func) (h : matchFrag f = none) :
    ∃ msg, emitFunc f = .error (.notFragment msg) := by
  simp [emitFunc, h]

/-! ## Golden linkage (machine-checked) -/

/-- Project an emission to its forward text (`""` on rejection, so a
    rejection also fails the golden examples below). Top-level def so
    `native_decide` can compile it. -/
def emitForwardText : Except EmitError EmittedFunc → String
  | .ok e => e.forward
  | .error _ => ""

/-- The emitter output for `addFunc` is byte-identical to the checked-in
    golden. Verified on (re)elaboration (clean and CI builds); incremental
    local drift is caught by the `diff` in `tools/check-phase3.sh`, since
    `lake` does not track `include_str` dependencies. -/
example : emitForwardText (emitFunc addFunc) =
    include_str "../tests/golden/Add.lean" := by native_decide

/-- The emitter output for `incrFunc` is byte-identical to the checked-in
    golden. -/
example : emitForwardText (emitFunc incrFunc) =
    include_str "../tests/golden/Incr.lean" := by native_decide
