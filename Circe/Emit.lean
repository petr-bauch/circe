/-
Circe.Emit — verified emitter `CoreIR → Lean` (forward + backward defs).

Phase 4: emitter for the `add`/`incr`/`choose`/`sum` fragment.
- `matchFrag` recognizes the four admitted `Func` shapes (by-value `add`;
  single-`mutBorrow` `incr`; single-region borrow-return `choose`;
  bounded-loop `sum`). See the `matchFrag` contract note: everything
  semantically relevant is pinned.
- `addFwd`/`incrFwd`/`chooseFwd`(+`chooseBack`)`/`sumFwd` are the verified
  forward (and backward) functions (Value level); `emit_correct_*` prove
  they agree with `evalFunc` on the canonical `*Func`s, with
  error-preservation corollaries and `choose` lens laws.
- `emitFunc` renders an accepted `Func` to `EmittedFunc` file text
  (`out/*.lean` via `tools/GenOut.lean`); anything else is rejected with
  `EmitError.notFragment` (loudly — never silently modeled).

Trust note: the *rendering* (Value-tag erasure to `BitVec` text) is
trusted, like the parser; what is verified is that the rendered
definitions have exactly the semantics of `evalFunc` on the fragment.
`tools/check-phase4.sh` regenerates the outputs and `diff`s them against
the checked-in goldens (`tests/golden/*.lean`, also spot-checked by the
`native_decide` examples below on clean builds), and `lake env lean`
typechecks the rendered files.
-/
import Circe.Base
import Circe.CoreIR
import Circe.Eval

/-! ## Fragment shapes -/

/-- The Phase 4 admitted fragment (`add`/`incr` from Phase 3, plus
    borrow-return `choose` and bounded-loop `sum`), extended in Phase 7
    with uniquely-owned heap `vec`. -/
inductive FragKind : Type
  | add
  | incr
  | choose
  | sum
  | vec
  deriving DecidableEq, Repr

/-- Recognize the admitted `Func` shapes. Anything else is `none`
    (and `emitFunc` rejects it loudly).

    Contract: everything semantically relevant is pinned (param names,
    types relevant to evaluation, borrow-region equality for `choose`,
    exact bodies including the `1`/`0` literals). Ignored fields (function
    name, return type, `let_` annotations, static array bounds, borrow
    region numbers up to single-region equality) are semantically inert:
    `Eval` never inspects them. The pipeline only feeds validator-produced
    canonical `Func`s; per-shape generalized `emit_correct` proofs are
    future work. -/
def matchFrag : Func → Option FragKind
  | ⟨_, [⟨"a", .i 32, .owned⟩, ⟨"b", .i 32, .owned⟩], _,
      .return_ (.add (.var "a") (.var "b"))⟩ => some .add
  | ⟨_, [⟨"p", .i 32, .mutBorrow _⟩], _,
      .return_ (.add (.var "p") (.lit (.i32 one)))⟩ =>
    if one == 1 then some .incr else none
  | ⟨_, [⟨"b", .bool, .owned⟩, ⟨"x", .i 32, .mutBorrow r1⟩,
         ⟨"y", .i 32, .mutBorrow r2⟩], _,
      .if_ (.var "b") (.return_ (.var "x")) (.return_ (.var "y"))⟩ =>
    if r1 == r2 then some .choose else none
  | ⟨_, [⟨"a", .array (.u 32) _, .sharedBorrow⟩,
         ⟨"n", .u 32, .owned⟩], _,
      .seq (.let_ "s" _ (.lit (.u32 s0)))
      (.seq (.let_ "i" _ (.lit (.u32 i0)))
      (.seq (.while_ (.ult (.var "i") (.var "n"))
              (.seq (.assign "s" (.uadd (.var "s") (.idx "a" (.var "i"))))
                    (.assign "i" (.uadd (.var "i") (.lit (.u32 one))))))
            (.return_ (.var "s"))))⟩ =>
    if s0 == 0 && i0 == 0 && one == 1 then some .sum else none
  | ⟨_, [⟨"n", .u 32, .owned⟩], _,
      .seq (.let_ "v" _ (.vnew (.var "n")))
      (.seq (.let_ "i" _ (.lit (.u32 i0)))
      (.seq (.let_ "s" _ (.lit (.u32 s0)))
      (.seq (.let_ "j" _ (.lit (.u32 j0)))
      (.seq (.while_ (.ult (.var "i") (.var "n"))
              (.seq (.vset "v" (.var "i") (.var "i"))
                    (.assign "i" (.uadd (.var "i") (.lit (.u32 one1))))))
      (.seq (.while_ (.ult (.var "j") (.var "n"))
              (.seq (.assign "s" (.uadd (.var "s") (.vget "v" (.var "j"))))
                    (.assign "j" (.uadd (.var "j") (.lit (.u32 one2))))))
      (.seq (.vfree "v")
            (.return_ (.var "s"))))))))⟩ =>
    if i0 == 0 && s0 == 0 && j0 == 0 && one1 == 1 && one2 == 1 then
      some .vec
    else none
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
  simp only [evalFunc, evalFuncFuel, addFunc, bindArgs, evalStmtFuel,
    evalStmtWith, EVAL_FUEL, evalExpr, addFwd, ha, hb]
  cases checkedAddI32 a b <;> rfl

/-- Emitter correctness, `incr`. -/
theorem emit_correct_incr (p : BitVec 32) :
    evalFunc incrFunc [.i32 p] = incrFwd p := by
  have hp := envLookup_incr_p p
  simp only [evalFunc, evalFuncFuel, incrFunc, bindArgs, evalStmtFuel,
    evalStmtWith, EVAL_FUEL, evalExpr, litVal, incrFwd, checkedIncrI32, hp]
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

/-! ## `choose`: borrow-return (forward + backward) -/

/-- Canonical CoreIR for `tests/c/choose_ptr.c`
    (`int32_t *choose(bool b, int32_t *__restrict x, int32_t *__restrict y)`).
    Single-region (both borrows share region 0, per `docs/OWNERSHIP.md` rule 6);
    the returned borrow is functionalized to the selected *value*, and writes
    through it are propagated by `chooseBack` (Aeneas §4.3). -/
def chooseFunc : Func :=
  ⟨"choose",
   [{ name := "b", ty := .bool, role := .owned },
    { name := "x", ty := .i 32, role := .mutBorrow 0 },
    { name := "y", ty := .i 32, role := .mutBorrow 0 }],
   .i 32,
   .if_ (.var "b") (.return_ (.var "x")) (.return_ (.var "y"))⟩

/-- Verified forward function for `choose` (cf. rendered `choose_fwd`):
    pure selection, never fails. -/
def chooseFwd (b : Bool) (x y : BitVec 32) : Result Value :=
  .ok (.i32 (if b then x else y))

/-- Verified backward function for `choose` (cf. rendered `choose_back`):
    the updated return value flows back to the selected input; the other
    input is unchanged. -/
def chooseBack (b : Bool) (x y ret : BitVec 32) : Result (Value × Value) :=
  .ok (if b then (.i32 ret, .i32 y) else (.i32 x, .i32 ret))

/-- Env facts for the `choose` shape. -/
theorem envLookup_choose_b (b : Bool) (x y : BitVec 32) :
    envLookup [("b", .b b), ("x", .i32 x), ("y", .i32 y)] "b" =
      some (.b b) := by
  simp [envLookup]

theorem envLookup_choose_x (b : Bool) (x y : BitVec 32) :
    envLookup [("b", .b b), ("x", .i32 x), ("y", .i32 y)] "x" =
      some (.i32 x) := by
  simp [envLookup, show ("x" : String) ≠ "b" by decide]

theorem envLookup_choose_y (b : Bool) (x y : BitVec 32) :
    envLookup [("b", .b b), ("x", .i32 x), ("y", .i32 y)] "y" =
      some (.i32 y) := by
  simp [envLookup, show ("y" : String) ≠ "b" by decide,
    show ("y" : String) ≠ "x" by decide]

/-- Emitter correctness, `choose`: evaluating the CoreIR function agrees with
    the forward function on all inputs. -/
theorem emit_correct_choose (b : Bool) (x y : BitVec 32) :
    evalFunc chooseFunc [.b b, .i32 x, .i32 y] = chooseFwd b x y := by
  have hb := envLookup_choose_b b x y
  have hx := envLookup_choose_x b x y
  have hy := envLookup_choose_y b x y
  cases b <;>
    simp [evalFunc, evalFuncFuel, chooseFunc, bindArgs, evalStmtFuel,
      evalStmtWith, EVAL_FUEL, evalExpr, chooseFwd, hb, hx, hy]

/-- Lens law (get-put): propagating the selected value back unchanged is the
    identity on the inputs. -/
theorem choose_back_get_put (b : Bool) (x y : BitVec 32) :
    chooseBack b x y (if b then x else y) = .ok (.i32 x, .i32 y) := by
  cases b <;> rfl

/-- Lens law (put-get): selecting after a backward update yields the update. -/
theorem choose_back_put_get (b : Bool) (x y r : BitVec 32) :
    (match chooseBack b x y r with
    | .ok (.i32 x', .i32 y') => chooseFwd b x' y'
    | _ => .error .AssertFail) = .ok (.i32 r) := by
  cases b <;> rfl

theorem matchFrag_choose : matchFrag chooseFunc = some .choose := rfl

/-! ## `sum_array`: bounded loop over a length-paired array -/

/-! ### Small-number word lemmas (loop indices live below 2^32) -/

theorem ofNat32_zero : BitVec.ofNat 32 0 = 0 := rfl

theorem ofNat32_toNat (k : Nat) (h : k < 2 ^ 32) :
    (BitVec.ofNat 32 k).toNat = k := by
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt h

/-- Incrementing a small word stays in `ofNat` form (no wrap).
    Stated with `ofNat 32 1` (not `1`): simp normalizes `1` to `1#32`. -/
theorem ofNat32_add_one (k : Nat) :
    BitVec.ofNat 32 k + BitVec.ofNat 32 1 = BitVec.ofNat 32 (k + 1) :=
  (BitVec.ofNat_add (n := 32) k 1).symm

/-- Unsigned comparison of a small word against any word. -/
theorem ofNat32_ult (k : Nat) (n : BitVec 32) (h : k < 2 ^ 32) :
    (BitVec.ofNat 32 k).ult n = decide (k < n.toNat) := by
  rw [BitVec.ult_eq_decide, ofNat32_toNat k h]

/-- Splitting a drop at a valid index exposes head and tail. -/
theorem drop_cons_getElem (l : List (BitVec 32)) (k : Nat)
    (h : k < l.length) :
    l.drop k = l[k] :: l.drop (k + 1) := by
  induction l generalizing k with
  | nil => simp at h
  | cons x xs ih =>
    cases k with
    | zero => simp
    | succ k =>
      have hk : k < xs.length := by
        simp only [List.length_cons] at h
        omega
      simp only [List.drop_succ_cons, List.getElem_cons_succ]
      exact ih k hk

/-! ### Canonical CoreIR + verified forward function -/

/-- Loop body: `s = s + a[i]; i = i + 1` (wrapping `u32`, plain `cir.add`;
    `cir.for` step region). The `1` is written `1#32` (`ofNat`-headed):
    simp's simprocs normalize `1` to `1#32`, so rewrite rules must use the
    normal form to match. -/
def sumBody : CStmt :=
  .seq (.assign "s" (.uadd (.var "s") (.idx "a" (.var "i"))))
       (.assign "i" (.uadd (.var "i") (.lit (.u32 1#32))))

/-- Loop: `while (i < n) { ... }` (`cir.for` cond region). -/
def sumWhile : CStmt :=
  .while_ (.ult (.var "i") (.var "n")) sumBody

/-- Canonical CoreIR for `tests/c/sum_array.c`. `a` is a `sharedBorrow`
    (pure list value, copy semantics); `n` is the 32-bit length (v0.1
    restriction: C `size_t` lengths must fit 32 bits — `validate` narrows
    them, runtime excess is `OOB`). The static array bound (4096) equals
    `EVAL_FUEL`: capacity and fuel coincide by construction. -/
def sumFunc : Func :=
  ⟨"sum_array",
   [{ name := "a", ty := .array (.u 32) 4096, role := .sharedBorrow },
    { name := "n", ty := .u 32, role := .owned }],
   .u 32,
   .seq (.let_ "s" (.u 32) (.lit (.u32 0)))
   (.seq (.let_ "i" (.u 32) (.lit (.u32 0)))
   (.seq sumWhile
         (.return_ (.var "s"))))⟩

/-- Value-level forward function for `sum_array` (cf. rendered `sum_fwd`):
    wrapping prefix sum of the first `n` elements; `OOB` when `n` exceeds
    the array (C would read out of bounds there — UB made loud). -/
def sumFwd (l : List (BitVec 32)) (n : BitVec 32) : Result Value :=
  if n.toNat ≤ l.length then .ok (.u32 (prefixSumU32 l n.toNat))
  else .error .OOB

/-- OOB corollary helper: `sumFwd` reports `OOB` exactly off-range. -/
theorem sumFwd_oob (l : List (BitVec 32)) (n : BitVec 32)
    (h : ¬ n.toNat ≤ l.length) : sumFwd l n = .error .OOB := by
  simp [sumFwd, h]

theorem sumFwd_ok (l : List (BitVec 32)) (n : BitVec 32)
    (h : n.toNat ≤ l.length) :
    sumFwd l n = .ok (.u32 (prefixSumU32 l n.toNat)) := by
  simp [sumFwd, h]

theorem matchFrag_sum : matchFrag sumFunc = some .sum := rfl

/-! ### Loop invariant -/

/-- Loop environments: index `k` and accumulator, array and bound fixed. -/
def mkSumEnv (l : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) : Env :=
  [("i", .u32 (BitVec.ofNat 32 k)), ("s", .u32 acc),
   ("a", .arr32 l), ("n", .u32 nv)]

theorem mkSumEnv_i (l : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) :
    envLookup (mkSumEnv l nv k acc) "i" =
      some (.u32 (BitVec.ofNat 32 k)) := by
  simp [mkSumEnv, envLookup]

theorem mkSumEnv_s (l : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) :
    envLookup (mkSumEnv l nv k acc) "s" = some (.u32 acc) := by
  simp [mkSumEnv, envLookup, show ("s" : String) ≠ "i" by decide]

theorem mkSumEnv_a (l : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) :
    envLookup (mkSumEnv l nv k acc) "a" = some (.arr32 l) := by
  simp [mkSumEnv, envLookup, show ("a" : String) ≠ "i" by decide,
    show ("a" : String) ≠ "s" by decide]

theorem mkSumEnv_n (l : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) :
    envLookup (mkSumEnv l nv k acc) "n" = some (.u32 nv) := by
  simp [mkSumEnv, envLookup, show ("n" : String) ≠ "i" by decide,
    show ("n" : String) ≠ "s" by decide,
    show ("n" : String) ≠ "a" by decide]

/-- Updating `s` in a loop env stays a loop env. -/
theorem sumEnv_update_s (l : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc v : BitVec 32) :
    envUpdate (mkSumEnv l nv k acc) "s" (.u32 v) =
      some (mkSumEnv l nv k v) := by
  simp [mkSumEnv, envUpdate, show ("s" : String) ≠ "i" by decide]

/-- Updating `i` in a loop env stays a loop env. -/
theorem sumEnv_update_i (l : List (BitVec 32)) (nv : BitVec 32) (k k' : Nat)
    (acc : BitVec 32) :
    envUpdate (mkSumEnv l nv k acc) "i" (.u32 (BitVec.ofNat 32 k')) =
      some (mkSumEnv l nv k' acc) := by
  simp [mkSumEnv, envUpdate]

/-- The loop condition reads the index against the bound. -/
theorem sumCond_eval (l : List (BitVec 32)) (nv : BitVec 32) (k : Nat)
    (acc : BitVec 32) (h : k < 2 ^ 32) :
    evalExpr (.ult (.var "i") (.var "n")) (mkSumEnv l nv k acc) =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkSumEnv_i l nv k acc
  have hn := mkSumEnv_n l nv k acc
  simp [evalExpr, hi, hn, ofNat32_ult k nv h]

/-- One body step advances index and accumulator (any fuel: loop-free). -/
theorem sumBody_eval (F : Nat) (l : List (BitVec 32)) (nv : BitVec 32)
    (k : Nat) (acc : BitVec 32)
    (hklen : k < l.length) (hk32 : k < 2 ^ 32) :
    evalStmtFuel F sumBody (mkSumEnv l nv k acc) =
      .ok (mkSumEnv l nv (k + 1) (acc + l[k]), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hget : l[k]? = some l[k] := List.getElem?_eq_getElem hklen
  have hs : evalExpr (.uadd (.var "s") (.idx "a" (.var "i")))
        (mkSumEnv l nv k acc) = .ok (.u32 (acc + l[k])) := by
    have h1 := mkSumEnv_s l nv k acc
    have ha := mkSumEnv_a l nv k acc
    have hii := mkSumEnv_i l nv k acc
    simp only [evalExpr, h1, ha, hii, hkk, hget]
  have hi2 : evalExpr (.uadd (.var "i") (.lit (.u32 1#32)))
        (mkSumEnv l nv k (acc + l[k])) =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkSumEnv_i l nv k (acc + l[k])
    simp only [evalExpr, litVal, h1, ofNat32_add_one]
  have up1 := sumEnv_update_s l nv k acc (acc + l[k])
  have up2 := sumEnv_update_i l nv k (k + 1) (acc + l[k])
  cases F <;>
    simp [sumBody, evalStmtFuel, evalStmtZero, evalStmtWith, hs, hi2, up1, up2]

/-- The OOB step: at `k = length` the index read fails loudly
    (independent of the bound `n`). -/
theorem sumBody_oob (F : Nat) (l : List (BitVec 32)) (nv : BitVec 32)
    (acc : BitVec 32) (h32 : l.length < 2 ^ 32) :
    evalStmtFuel F sumBody
        (mkSumEnv l nv l.length acc) = .error .OOB := by
  have hkk : (BitVec.ofNat 32 l.length).toNat = l.length :=
    ofNat32_toNat _ h32
  have hget : l[l.length]? = none :=
    List.getElem?_eq_none (Nat.le_refl _)
  have ha := mkSumEnv_a l nv l.length acc
  have hii := mkSumEnv_i l nv l.length acc
  have hs : evalExpr (.uadd (.var "s") (.idx "a" (.var "i")))
        (mkSumEnv l nv l.length acc) = .error .OOB := by
    have h1 := mkSumEnv_s l nv l.length acc
    simp only [evalExpr, h1, ha, hii, hkk, hget]
  cases F <;>
    simp [sumBody, evalStmtFuel, evalStmtZero, evalStmtWith, hs]

/-- Loop correctness, in-range: the loop folds the remaining suffix. -/
theorem sumWhile_correct (l : List (BitVec 32)) (nv : BitVec 32)
    (F k : Nat) (acc : BitVec 32)
    (hk : k ≤ nv.toNat)
    (hlen : nv.toNat ≤ l.length)
    (h32 : nv.toNat < 2 ^ 32)
    (hF : nv.toNat - k ≤ F) :
    evalStmtFuel F sumWhile (mkSumEnv l nv k acc) =
      .ok (mkSumEnv l nv nv.toNat
        (acc + prefixSumU32 (l.drop k) (nv.toNat - k)), .fellThrough) := by
  induction F generalizing k acc with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : evalExpr (.ult (.var "i") (.var "n"))
        (mkSumEnv l nv nv.toNat acc) = .ok (.b false) := by
      simpa using (sumCond_eval l nv nv.toNat acc h32)
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    have hpre : prefixSumU32 (l.drop nv.toNat) 0 = 0 := prefixSumU32_zero _
    simp [sumWhile, evalStmtFuel, evalStmtZero, evalStmtZeroHandler, evalStmtWith,
      hcond, hsub, hpre]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hklen : k < l.length := by omega
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkSumEnv l nv k acc) = .ok (.b true) := by
        simpa [hlt] using (sumCond_eval l nv k acc hk32)
      have hbody := sumBody_eval F l nv k acc hklen hk32
      have hstep : evalStmtFuel (F + 1) sumWhile (mkSumEnv l nv k acc)
          = evalStmtFuel F sumWhile (mkSumEnv l nv (k + 1) (acc + l[k])) := by
        simp [sumWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith, hcond,
          hbody]
      rw [hstep]
      have hrec := ih (k + 1) (acc + l[k]) (by omega) (by omega)
      rw [hrec]
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      have hdrop : l.drop k = l[k] :: l.drop (k + 1) :=
        drop_cons_getElem l k hklen
      have hacc : (acc + l[k]) +
            prefixSumU32 (l.drop (k + 1)) (nv.toNat - (k + 1))
          = acc + prefixSumU32 (l.drop k) (nv.toNat - k) := by
        rw [hkk1, hdrop, prefixSumU32_cons]
        exact BitVec.add_assoc _ _ _
      rw [hacc]
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkSumEnv l nv nv.toNat acc) = .ok (.b false) := by
        simpa using (sumCond_eval l nv nv.toNat acc h32)
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      have hpre : prefixSumU32 (l.drop nv.toNat) 0 = 0 := prefixSumU32_zero _
      simp [sumWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith, hcond,
        hsub, hpre]

/-- Loop correctness, out-of-range: the loop reports `OOB` at the end.
    Note the bound is on the *length* (`hlen32`): `n` itself may exceed
    32 bits here (that is the OOB case); indices never pass `length`. -/
theorem sumWhile_oob (l : List (BitVec 32)) (nv : BitVec 32)
    (F k : Nat) (acc : BitVec 32)
    (hk : k ≤ l.length)
    (hlt : l.length < nv.toNat)
    (hlen32 : l.length < 2 ^ 32)
    (hF : l.length - k + 1 ≤ F) :
    evalStmtFuel F sumWhile (mkSumEnv l nv k acc) = .error .OOB := by
  induction F generalizing k acc with
  | zero => omega
  | succ F ih =>
    by_cases hlt2 : k < l.length
    · have hk32 : k < 2 ^ 32 := by omega
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkSumEnv l nv k acc) = .ok (.b true) := by
        have hkn : k < nv.toNat := by omega
        simpa [hkn] using (sumCond_eval l nv k acc hk32)
      have hbody := sumBody_eval F l nv k acc hlt2 hk32
      have hstep : evalStmtFuel (F + 1) sumWhile (mkSumEnv l nv k acc)
          = evalStmtFuel F sumWhile (mkSumEnv l nv (k + 1) (acc + l[k])) := by
        simp [sumWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith, hcond,
          hbody]
      rw [hstep]
      exact ih (k + 1) (acc + l[k]) (by omega) (by omega)
    · have hkk : k = l.length := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkSumEnv l nv l.length acc) = .ok (.b true) := by
        simpa [hlt] using
          (sumCond_eval l nv l.length acc hlen32)
      have hbody := sumBody_oob F l nv acc hlen32
      simp [sumWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith, hcond,
        hbody]

/-! ### Whole-function correctness (fuel-generalized, then instantiated) -/

/-- `emit_correct` for `sum`, at any fuel covering `n`. -/
theorem evalFuncFuel_sum (F : Nat) (l : List (BitVec 32)) (nv : BitVec 32)
    (hle : nv.toNat ≤ l.length) (h32 : nv.toNat < 2 ^ 32)
    (hF : nv.toNat ≤ F) :
    evalFuncFuel F sumFunc [.arr32 l, .u32 nv] = sumFwd l nv := by
  -- Stated with `ofNat`-headed zeros (simp's simprocs normalize `0` to
  -- `0#32`, so `OfNat`-headed forms would not match after normalization).
  have henv : [("i", .u32 (BitVec.ofNat 32 0)),
        ("s", .u32 (BitVec.ofNat 32 0)),
        ("a", .arr32 l), ("n", .u32 nv)]
      = mkSumEnv l nv 0 (BitVec.ofNat 32 0) := rfl
  have hret := mkSumEnv_s l nv nv.toNat (prefixSumU32 l nv.toNat)
  -- The loop `have`s match simp's *unfolded* handler forms (the fuel
  -- equations necessarily unfold the loop while evaluating the lets, so a
  -- folded `evalStmtFuel` statement could never match). Handlers are named
  -- definitions (`evalStmtZeroHandler` / `evalStmtSuccHandler`), so the
  -- rules match syntactically; each is proved from the corresponding loop
  -- theorem by definitional unfolding (`exact` checks up to defeq).
  cases F with
  | zero =>
    -- Inside the zero branch `hF` forces `nv.toNat = 0`.
    have hloopH0 : evalStmtWith evalStmtZeroHandler
          sumWhile (mkSumEnv l nv 0 (BitVec.ofNat 32 0))
        = .ok (mkSumEnv l nv nv.toNat
            (BitVec.ofNat 32 0 + prefixSumU32 (l.drop 0) (nv.toNat - 0)),
            .fellThrough) :=
      sumWhile_correct l nv 0 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hle h32
        (by omega)
    simp [evalFuncFuel, sumFunc, bindArgs, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, litVal, envExtend, sumFwd, henv, hloopH0, hret,
      hle]
  | succ F =>
    have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          sumWhile (mkSumEnv l nv 0 (BitVec.ofNat 32 0))
        = .ok (mkSumEnv l nv nv.toNat
            (BitVec.ofNat 32 0 + prefixSumU32 (l.drop 0) (nv.toNat - 0)),
            .fellThrough) :=
      sumWhile_correct l nv (F + 1) 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hle
        h32 (by simpa using hF)
    simp [evalFuncFuel, sumFunc, bindArgs, evalStmtFuel, evalStmtWith,
      evalExpr, litVal, envExtend, sumFwd, henv, hloopS, hret, hle]

/-- `emit_correct` for `sum` at the default fuel. -/
theorem emit_correct_sum (l : List (BitVec 32)) (nv : BitVec 32)
    (hle : nv.toNat ≤ l.length) (hfuel : nv.toNat ≤ EVAL_FUEL) :
    evalFunc sumFunc [.arr32 l, .u32 nv] = sumFwd l nv := by
  have h32eq : (2 : Nat) ^ 32 = 4294967296 := rfl
  have h32 : nv.toNat < 2 ^ 32 := by
    rw [h32eq]
    have hle4096 : nv.toNat ≤ 4096 := by simpa [EVAL_FUEL] using hfuel
    omega
  exact evalFuncFuel_sum EVAL_FUEL l nv hle h32 hfuel

/-- OOB corollary: over-long lengths fail loudly on both sides. -/
theorem evalFuncFuel_sum_oob (F : Nat) (l : List (BitVec 32))
    (nv : BitVec 32)
    (hlt : l.length < nv.toNat) (hlen32 : l.length < 2 ^ 32)
    (hF : l.length + 1 ≤ F) :
    evalFuncFuel F sumFunc [.arr32 l, .u32 nv] = .error .OOB := by
  -- `ofNat`-headed zeros (see `evalFuncFuel_sum`).
  have henv : [("i", .u32 (BitVec.ofNat 32 0)),
        ("s", .u32 (BitVec.ofNat 32 0)),
        ("a", .arr32 l), ("n", .u32 nv)]
      = mkSumEnv l nv 0 (BitVec.ofNat 32 0) := rfl
  cases F with
  | zero =>
    have hloopH0 : evalStmtWith evalStmtZeroHandler
          sumWhile (mkSumEnv l nv 0 (BitVec.ofNat 32 0)) = .error .OOB :=
      sumWhile_oob l nv 0 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hlt hlen32
        (by omega)
    simp [evalFuncFuel, sumFunc, bindArgs, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, litVal, envExtend, henv, hloopH0]
  | succ F =>
    have hloopS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          sumWhile (mkSumEnv l nv 0 (BitVec.ofNat 32 0)) = .error .OOB :=
      sumWhile_oob l nv (F + 1) 0 (BitVec.ofNat 32 0) (Nat.zero_le _) hlt
        hlen32 (by simpa using hF)
    simp [evalFuncFuel, sumFunc, bindArgs, evalStmtFuel, evalStmtWith,
      evalExpr, litVal, envExtend, henv, hloopS]

/-- OOB corollary at the default fuel. -/
theorem emit_correct_sum_oob (l : List (BitVec 32)) (nv : BitVec 32)
    (hlt : l.length < nv.toNat) (hfuel : l.length + 1 ≤ EVAL_FUEL) :
    evalFunc sumFunc [.arr32 l, .u32 nv] = .error .OOB := by
  have h32eq : (2 : Nat) ^ 32 = 4294967296 := rfl
  have hlen32 : l.length < 2 ^ 32 := by
    rw [h32eq]
    have hle4096 : l.length + 1 ≤ 4096 := by simpa [EVAL_FUEL] using hfuel
    omega
  exact evalFuncFuel_sum_oob EVAL_FUEL l nv hlt hlen32 hfuel

/-! ## `vec_alloc`: uniquely-owned heap block (Phase 7, u32-only) -/

/-- Fill body: `v[i] = i; i = i + 1` (the value written is the index).
    The `1` is `1#32` (`ofNat`-headed, cf. `sumBody`). -/
def vecFillBody : CStmt :=
  .seq (.vset "v" (.var "i") (.var "i"))
       (.assign "i" (.uadd (.var "i") (.lit (.u32 1#32))))

/-- Fill loop: `while (i < n) { ... }`. -/
def vecFillWhile : CStmt :=
  .while_ (.ult (.var "i") (.var "n")) vecFillBody

/-- Sum body: `s = s + v[j]; j = j + 1`. -/
def vecSumBody : CStmt :=
  .seq (.assign "s" (.uadd (.var "s") (.vget "v" (.var "j"))))
       (.assign "j" (.uadd (.var "j") (.lit (.u32 1#32))))

/-- Sum loop: `while (j < n) { ... }`. -/
def vecSumWhile : CStmt :=
  .while_ (.ult (.var "j") (.var "n")) vecSumBody

/-- Canonical CoreIR for `tests/c/vec_alloc.c`: allocate a zeroed `u32`
    block of `n` words (`malloc`), fill it with indices, sum it, `free`
    it, return the sum. `n` is the length (`u32`: C `size_t` must fit
    32 bits, like `sum_array`); the block lives in `v` as a `vecVal`. -/
def vecFunc : Func :=
  ⟨"vec_alloc",
   [{ name := "n", ty := .u 32, role := .owned }],
   .u 32,
   .seq (.let_ "v" .vecBlock (.vnew (.var "n")))
   (.seq (.let_ "i" (.u 32) (.lit (.u32 0)))
   (.seq (.let_ "s" (.u 32) (.lit (.u32 0)))
   (.seq (.let_ "j" (.u 32) (.lit (.u32 0)))
   (.seq vecFillWhile
   (.seq vecSumWhile
   (.seq (.vfree "v")
         (.return_ (.var "s"))))))))⟩

theorem matchFrag_vec : matchFrag vecFunc = some .vec := rfl

/-- Value-level forward function for `vec_alloc` (cf. rendered
    `vec_alloc_fwd`): the pure heap program from `Circe.Base`. -/
def vecFwd (n : BitVec 32) : Result Value :=
  .u32 <$> vecFillSumU32 n.toNat

/-- `(<$>)` on `Result` computes on both constructors (for the corollaries;
    cf. `i32_map_error`/`i32_map_ok`). -/
theorem u32_map_error (e : Panic) :
    Value.u32 <$> (Except.error e : Result (BitVec 32)) = .error e := rfl

theorem u32_map_ok (r : BitVec 32) :
    Value.u32 <$> (Except.ok r : Result (BitVec 32)) = .ok (.u32 r) := rfl

/-! ### Heap loop environments -/

/-- Heap environments: block plus bound, both indices, accumulator.
    All four lets are bound before the fill loop, so one shape threads
    through both loops (`s`/`j` sit unused during fill). -/
def mkVecEnv (blk : Vec32) (nv iv sv jv : BitVec 32) : Env :=
  [("j", .u32 jv), ("s", .u32 sv), ("i", .u32 iv),
   ("v", .vecVal blk), ("n", .u32 nv)]

theorem mkVecEnv_j (blk : Vec32) (nv iv sv jv : BitVec 32) :
    envLookup (mkVecEnv blk nv iv sv jv) "j" = some (.u32 jv) := by
  simp [mkVecEnv, envLookup]

theorem mkVecEnv_s (blk : Vec32) (nv iv sv jv : BitVec 32) :
    envLookup (mkVecEnv blk nv iv sv jv) "s" = some (.u32 sv) := by
  simp [mkVecEnv, envLookup, show ("s" : String) ≠ "j" by decide]

theorem mkVecEnv_i (blk : Vec32) (nv iv sv jv : BitVec 32) :
    envLookup (mkVecEnv blk nv iv sv jv) "i" = some (.u32 iv) := by
  simp [mkVecEnv, envLookup, show ("i" : String) ≠ "j" by decide,
    show ("i" : String) ≠ "s" by decide]

theorem mkVecEnv_v (blk : Vec32) (nv iv sv jv : BitVec 32) :
    envLookup (mkVecEnv blk nv iv sv jv) "v" = some (.vecVal blk) := by
  simp [mkVecEnv, envLookup, show ("v" : String) ≠ "j" by decide,
    show ("v" : String) ≠ "s" by decide,
    show ("v" : String) ≠ "i" by decide]

theorem mkVecEnv_n (blk : Vec32) (nv iv sv jv : BitVec 32) :
    envLookup (mkVecEnv blk nv iv sv jv) "n" = some (.u32 nv) := by
  simp [mkVecEnv, envLookup, show ("n" : String) ≠ "j" by decide,
    show ("n" : String) ≠ "s" by decide,
    show ("n" : String) ≠ "i" by decide,
    show ("n" : String) ≠ "v" by decide]

/-- Updating `v` in a heap env stays a heap env. -/
theorem vecEnv_update_v (blk : Vec32) (nv iv sv jv : BitVec 32)
    (blk' : Vec32) :
    envUpdate (mkVecEnv blk nv iv sv jv) "v" (.vecVal blk') =
      some (mkVecEnv blk' nv iv sv jv) := by
  simp [mkVecEnv, envUpdate, show ("v" : String) ≠ "j" by decide,
    show ("v" : String) ≠ "s" by decide,
    show ("v" : String) ≠ "i" by decide]

/-- Updating `i` in a heap env stays a heap env. -/
theorem vecEnv_update_i (blk : Vec32) (nv iv iv' sv jv : BitVec 32) :
    envUpdate (mkVecEnv blk nv iv sv jv) "i" (.u32 iv') =
      some (mkVecEnv blk nv iv' sv jv) := by
  simp [mkVecEnv, envUpdate, show ("i" : String) ≠ "j" by decide,
    show ("i" : String) ≠ "s" by decide]

/-- Updating `s` in a heap env stays a heap env. -/
theorem vecEnv_update_s (blk : Vec32) (nv iv sv sv' jv : BitVec 32) :
    envUpdate (mkVecEnv blk nv iv sv jv) "s" (.u32 sv') =
      some (mkVecEnv blk nv iv sv' jv) := by
  simp [mkVecEnv, envUpdate, show ("s" : String) ≠ "j" by decide]

/-- Updating `j` in a heap env stays a heap env. -/
theorem vecEnv_update_j (blk : Vec32) (nv iv sv jv jv' : BitVec 32) :
    envUpdate (mkVecEnv blk nv iv sv jv) "j" (.u32 jv') =
      some (mkVecEnv blk nv iv sv jv') := by
  simp [mkVecEnv, envUpdate]

/-- The fill-loop condition reads the index against the bound. -/
theorem vecFillCond_eval (blk : Vec32) (nv : BitVec 32) (k : Nat)
    (sv jv : BitVec 32) (h : k < 2 ^ 32) :
    evalExpr (.ult (.var "i") (.var "n"))
        (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) =
      .ok (.b (decide (k < nv.toNat))) := by
  have hi := mkVecEnv_i blk nv (BitVec.ofNat 32 k) sv jv
  have hn := mkVecEnv_n blk nv (BitVec.ofNat 32 k) sv jv
  simp [evalExpr, hi, hn, ofNat32_ult k nv h]

/-- The sum-loop condition reads the index against the bound. -/
theorem vecSumCond_eval (blk : Vec32) (nv iv sv : BitVec 32) (k : Nat)
    (h : k < 2 ^ 32) :
    evalExpr (.ult (.var "j") (.var "n"))
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) =
      .ok (.b (decide (k < nv.toNat))) := by
  have hj := mkVecEnv_j blk nv iv sv (BitVec.ofNat 32 k)
  have hn := mkVecEnv_n blk nv iv sv (BitVec.ofNat 32 k)
  simp [evalExpr, hj, hn, ofNat32_ult k nv h]

/-- One fill step stores the index and advances (any fuel: loop-free). -/
theorem vecFillBody_eval (F : Nat) (blk : Vec32) (nv : BitVec 32)
    (k : Nat) (sv jv : BitVec 32) (blkMid : Vec32)
    (_hklen : k < blk.val.length) (hk32 : k < 2 ^ 32)
    (_hlive : blk.freed = false)
    (hset : vecSet blk k (BitVec.ofNat 32 k) = .ok blkMid) :
    evalStmtFuel F vecFillBody
        (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) =
      .ok (mkVecEnv blkMid nv (BitVec.ofNat 32 (k + 1)) sv jv,
        .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hi : evalExpr (.var "i")
        (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) =
        .ok (.u32 (BitVec.ofNat 32 k)) :=
    evalExpr_var_hit _ _ _
      (mkVecEnv_i blk nv (BitVec.ofNat 32 k) sv jv)
  have harr := mkVecEnv_v blk nv (BitVec.ofNat 32 k) sv jv
  have hset' : vecSet blk (BitVec.ofNat 32 k).toNat (BitVec.ofNat 32 k) =
      .ok blkMid := by rw [hkk]; exact hset
  have up1 := vecEnv_update_v blk nv (BitVec.ofNat 32 k) sv jv blkMid
  have hi2 : evalExpr (.uadd (.var "i") (.lit (.u32 1#32)))
        (mkVecEnv blkMid nv (BitVec.ofNat 32 k) sv jv) =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVecEnv_i blkMid nv (BitVec.ofNat 32 k) sv jv
    simp only [evalExpr, litVal, h1, ofNat32_add_one]
  have up2 := vecEnv_update_i blkMid nv (BitVec.ofNat 32 k)
    (BitVec.ofNat 32 (k + 1)) sv jv
  -- Feed primitive facts (never intermediate `evalStmtFuel` facts: after
  -- unfolding, only syntactically-matching rules fire). `simp only`
  -- (unlike full `simp`) leaves `(ofNat 32 k).toNat` alone, so `hset'`
  -- fires as-is.
  cases F <;>
    simp only [vecFillBody, evalStmtFuel, evalStmtZero, evalStmtWith, hi, harr,
      hset', up1, hi2, up2]

/-- One sum step accumulates the block element and advances (any fuel). -/
theorem vecSumBody_eval (F : Nat) (blk : Vec32) (nv iv sv : BitVec 32)
    (k : Nat) (hk32 : k < 2 ^ 32)
    (hget : vecGet blk k = .ok (BitVec.ofNat 32 k)) :
    evalStmtFuel F vecSumBody
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) =
      .ok (mkVecEnv blk nv iv (sv + BitVec.ofNat 32 k)
        (BitVec.ofNat 32 (k + 1)), .fellThrough) := by
  have hkk : (BitVec.ofNat 32 k).toNat = k := ofNat32_toNat k hk32
  have hj := mkVecEnv_j blk nv iv sv (BitVec.ofNat 32 k)
  have hs0 := mkVecEnv_s blk nv iv sv (BitVec.ofNat 32 k)
  have harr := mkVecEnv_v blk nv iv sv (BitVec.ofNat 32 k)
  have hget' : vecGet blk (BitVec.ofNat 32 k).toNat =
      .ok (BitVec.ofNat 32 k) := by rw [hkk]; exact hget
  have hg : evalExpr (.vget "v" (.var "j"))
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) =
        .ok (.u32 (BitVec.ofNat 32 k)) := by
    simp only [evalExpr, hj, harr, hget']
  have hs : evalExpr (.uadd (.var "s") (.vget "v" (.var "j")))
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) =
        .ok (.u32 (sv + BitVec.ofNat 32 k)) := by
    simp only [evalExpr, hs0, hj, harr, hget']
  have hj2 : evalExpr (.uadd (.var "j") (.lit (.u32 1#32)))
        (mkVecEnv blk nv iv (sv + BitVec.ofNat 32 k) (BitVec.ofNat 32 k)) =
        .ok (.u32 (BitVec.ofNat 32 (k + 1))) := by
    have h1 := mkVecEnv_j blk nv iv (sv + BitVec.ofNat 32 k)
      (BitVec.ofNat 32 k)
    simp only [evalExpr, litVal, h1, ofNat32_add_one]
  have up1 := vecEnv_update_s blk nv iv sv (sv + BitVec.ofNat 32 k)
    (BitVec.ofNat 32 k)
  have up2 := vecEnv_update_j blk nv iv (sv + BitVec.ofNat 32 k)
    (BitVec.ofNat 32 k) (BitVec.ofNat 32 (k + 1))
  -- Feed primitive facts (never intermediate `evalStmtFuel` facts: after
  -- unfolding, only syntactically-matching rules fire). `hs`/`hg` are
  -- `evalExpr`-headed (no `evalExpr` unfolding in the set), so they fire
  -- as-is; `hj`/`harr`/`hget'` discharge the inner `vget` matches.
  cases F <;>
    simp only [vecSumBody, evalStmtFuel, evalStmtZero, evalStmtWith, hs, hj2,
      up1, up2]

/-! ### Heap loop correctness (fuel-generalized) -/

/-- Fill-loop correctness: the eval loop runs the `Base` fill to completion.
    The `Base` program (`hfill`) is both spec and witness: induction follows
    its unfolding, like `sumWhile_correct`. -/
theorem vecFillWhile_correct (blk : Vec32) (nv : BitVec 32)
    (F k : Nat) (sv jv : BitVec 32) (blkOut : Vec32)
    (hk : k ≤ nv.toNat)
    (hlen : blk.val.length = nv.toNat)
    (hlive : blk.freed = false)
    (hn32 : nv.toNat < 2 ^ 32)
    (hfill : vecFillLoopAux blk k (nv.toNat - k) = .ok blkOut)
    (hF : nv.toNat - k ≤ F) :
    evalStmtFuel F vecFillWhile
        (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) =
      .ok (mkVecEnv blkOut nv (BitVec.ofNat 32 nv.toNat) sv jv,
        .fellThrough) := by
  induction F generalizing k blk blkOut with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    -- `subst` creates `ofNat 32 nv.toNat`; `simp only` (unlike full `simp`)
    -- leaves it alone, so the cond fact stays in `ofNat` form and `rw`
    -- fires syntactically (cf. probe6).
    have hcond : evalExpr (.ult (.var "i") (.var "n"))
        (mkVecEnv blk nv (BitVec.ofNat 32 nv.toNat) sv jv) =
        .ok (.b false) := by
      have hc := vecFillCond_eval blk nv nv.toNat sv jv hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hfill
    simp only [vecFillLoopAux] at hfill
    cases hfill
    simp only [vecFillWhile, evalStmtFuel, evalStmtZero, evalStmtZeroHandler,
      evalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hklen : k < blk.val.length := by omega
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv) =
          .ok (.b true) := by
        simpa [hlt] using (vecFillCond_eval blk nv k sv jv hk32)
      have hset : vecSet blk k (BitVec.ofNat 32 k) =
          .ok ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ :=
        vecSet_ok blk k _ hlive hklen
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hfill
      simp only [vecFillLoopAux, hset] at hfill
      -- hfill : Aux ⟨set ..⟩ (k+1) (n-(k+1)) = ok blkOut
      have hbody := vecFillBody_eval F blk nv k sv jv
        ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩
        hklen hk32 hlive hset
      have hstep : evalStmtFuel (F + 1) vecFillWhile
            (mkVecEnv blk nv (BitVec.ofNat 32 k) sv jv)
          = evalStmtFuel F vecFillWhile
            (mkVecEnv ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ nv
              (BitVec.ofNat 32 (k + 1)) sv jv) := by
        simp [vecFillWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond, hbody]
      rw [hstep]
      have hlenMid : (⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).val.length
          = nv.toNat := by
        show (blk.val.set k (BitVec.ofNat 32 k)).length = nv.toNat
        rw [List.length_set]
        omega
      have hliveMid : (⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).freed
          = false := rfl
      exact ih ⟨blk.val.set k (BitVec.ofNat 32 k), false⟩ (k + 1) blkOut
        (by omega) hlenMid hliveMid hfill (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "i") (.var "n"))
          (mkVecEnv blk nv (BitVec.ofNat 32 nv.toNat) sv jv) =
          .ok (.b false) := by
        have hc := vecFillCond_eval blk nv nv.toNat sv jv hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hfill
      simp only [vecFillLoopAux] at hfill
      cases hfill
      simp only [vecFillWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith]
      rw [hcond]

/-- Sum-loop correctness: the eval loop runs the `Base` sum to completion. -/
theorem vecSumWhile_correct (blk : Vec32) (nv : BitVec 32)
    (F k : Nat) (iv sv : BitVec 32) (sout : BitVec 32)
    (hk : k ≤ nv.toNat)
    (hget : ∀ j, k ≤ j → j < nv.toNat →
      vecGet blk j = .ok (BitVec.ofNat 32 j))
    (hn32 : nv.toNat < 2 ^ 32)
    (hsum : vecSumLoopAux blk k (nv.toNat - k) sv = .ok sout)
    (hF : nv.toNat - k ≤ F) :
    evalStmtFuel F vecSumWhile
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) =
      .ok (mkVecEnv blk nv iv sout (BitVec.ofNat 32 nv.toNat),
        .fellThrough) := by
  induction F generalizing k sv sout with
  | zero =>
    have hkk : k = nv.toNat := by omega
    subst hkk
    have hcond : evalExpr (.ult (.var "j") (.var "n"))
        (mkVecEnv blk nv iv sv (BitVec.ofNat 32 nv.toNat)) =
        .ok (.b false) := by
      have hc := vecSumCond_eval blk nv iv sv nv.toNat hn32
      rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
      exact hc
    have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
    rw [hsub] at hsum
    simp only [vecSumLoopAux] at hsum
    cases hsum
    simp only [vecSumWhile, evalStmtFuel, evalStmtZero, evalStmtZeroHandler,
      evalStmtWith]
    rw [hcond]
  | succ F ih =>
    by_cases hlt : k < nv.toNat
    · have hk32 : k < 2 ^ 32 := by omega
      have hcond : evalExpr (.ult (.var "j") (.var "n"))
          (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k)) =
          .ok (.b true) := by
        simpa [hlt] using (vecSumCond_eval blk nv iv sv k hk32)
      have hgetk : vecGet blk k = .ok (BitVec.ofNat 32 k) :=
        hget k (Nat.le_refl _) hlt
      have hbody := vecSumBody_eval F blk nv iv sv k hk32 hgetk
      have hstep : evalStmtFuel (F + 1) vecSumWhile
            (mkVecEnv blk nv iv sv (BitVec.ofNat 32 k))
          = evalStmtFuel F vecSumWhile
            (mkVecEnv blk nv iv (sv + BitVec.ofNat 32 k)
              (BitVec.ofNat 32 (k + 1))) := by
        simp [vecSumWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond, hbody]
      rw [hstep]
      have hkk1 : nv.toNat - k = (nv.toNat - (k + 1)) + 1 := by omega
      rw [hkk1] at hsum
      simp only [vecSumLoopAux, hgetk] at hsum
      exact ih (k + 1) (sv + BitVec.ofNat 32 k) sout (by omega)
        (by intro j hjlo hjhi; exact hget j (by omega) hjhi) hsum (by omega)
    · have hkk : k = nv.toNat := by omega
      subst hkk
      have hcond : evalExpr (.ult (.var "j") (.var "n"))
          (mkVecEnv blk nv iv sv (BitVec.ofNat 32 nv.toNat)) =
          .ok (.b false) := by
        have hc := vecSumCond_eval blk nv iv sv nv.toNat hn32
        rw [show decide (nv.toNat < nv.toNat) = false from by simp] at hc
        exact hc
      have hsub : nv.toNat - nv.toNat = 0 := Nat.sub_self _
      rw [hsub] at hsum
      simp only [vecSumLoopAux] at hsum
      cases hsum
      simp only [vecSumWhile, evalStmtFuel, evalStmtSuccHandler, evalStmtWith]
      rw [hcond]

/-! ### Whole-function correctness (fuel-generalized, then instantiated) -/

/-- `emit_correct` for `vec_alloc`, at any fuel covering `n`. -/
theorem evalFuncFuel_vec (F : Nat) (nv : BitVec 32)
    (hn : nv.toNat ≤ F) (hn32 : nv.toNat < 2 ^ 32) :
    evalFuncFuel F vecFunc [.u32 nv] =
      .ok (.u32 (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
        nv.toNat)) := by
  have hfresh : (⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ : Vec32).val.length =
      0 + nv.toNat := by simp
  obtain ⟨blkOut, hfill0⟩ := vecFillLoopAux_fresh_ok
    (List.replicate nv.toNat (BitVec.ofNat 32 0)) 0 nv.toNat (by simp)
  have hliveOut : blkOut.freed = false :=
    vecFillLoopAux_live _ _ _ _ rfl hfill0
  have hgetOut : ∀ j, 0 ≤ j → j < nv.toNat →
      vecGet blkOut j = .ok (BitVec.ofNat 32 j) := by
    intro j hjlo hjhi
    have hjhi' : j < 0 + nv.toNat := by omega
    exact vecFillLoopAux_get _ 0 nv.toNat _ rfl hfresh hfill0 j hjlo hjhi'
  have hsum0 := vecSumLoopAux_correct blkOut 0 nv.toNat 0 (by
    intro j hjlo hjhi
    exact hgetOut j hjlo (by omega))
  have hrange : List.range' 0 nv.toNat = List.range nv.toNat := by
    simp [List.range_eq_range']
  rw [hrange] at hsum0
  have h0 : (0 : BitVec 32) + prefixSumU32 ((List.range nv.toNat).map
      (BitVec.ofNat 32)) nv.toNat
      = prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat :=
    BitVec.zero_add _
  rw [h0] at hsum0
  have hfree0 : vecFree blkOut = .ok ⟨blkOut.val, true⟩ :=
    vecFree_ok blkOut hliveOut
  -- The four lets build the heap env (stated `ofNat`-headed: simp's
  -- simprocs normalize `0` to `0#32`).
  have henv : [("j", .u32 (BitVec.ofNat 32 0)),
        ("s", .u32 (BitVec.ofNat 32 0)),
        ("i", .u32 (BitVec.ofNat 32 0)),
        ("v", .vecVal ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩),
        ("n", .u32 nv)]
      = mkVecEnv ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
        (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) := rfl
  have hn0 : envLookup [("n", .u32 nv)] "n" = some (.u32 nv) := rfl
  -- Loop haves match simp's unfolded handler forms (cf. `evalFuncFuel_sum`).
  cases F with
  | zero =>
    have hF0 : nv.toNat - 0 ≤ 0 := by omega
    have hloopF0 : evalStmtWith evalStmtZeroHandler
          vecFillWhile
          (mkVecEnv ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
        = .ok (mkVecEnv blkOut nv (BitVec.ofNat 32 nv.toNat)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0), .fellThrough) :=
      vecFillWhile_correct _ _ 0 0 _ _ blkOut (Nat.zero_le _)
        (by simp) rfl hn32 hfill0 hF0
    have hloopS0 : evalStmtWith evalStmtZeroHandler
          vecSumWhile
          (mkVecEnv blkOut nv nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
        = .ok (mkVecEnv blkOut nv nv
            (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
              nv.toNat)
            (BitVec.ofNat 32 nv.toNat), .fellThrough) :=
      vecSumWhile_correct blkOut nv 0 0 nv _ _ (Nat.zero_le _)
        (by intro j hjlo hjhi; exact hgetOut j hjlo hjhi) hn32 hsum0 hF0
    have huv := vecEnv_update_v blkOut nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      nv ⟨blkOut.val, true⟩
    have harv := mkVecEnv_v blkOut nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      nv
    have hars := mkVecEnv_s ⟨blkOut.val, true⟩ nv
      nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      nv
    simp [evalFuncFuel, vecFunc, bindArgs, evalStmtFuel, evalStmtZero,
      evalStmtWith, evalExpr, litVal, envExtend, hn0, vecNew, henv,
      hloopF0, hloopS0, hfree0, huv, harv, hars]
  | succ F =>
    have hFS : nv.toNat - 0 ≤ F + 1 := by omega
    have hloopFS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          vecFillWhile
          (mkVecEnv ⟨List.replicate nv.toNat (BitVec.ofNat 32 0), false⟩ nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
        = .ok (mkVecEnv blkOut nv (BitVec.ofNat 32 nv.toNat)
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0), .fellThrough) :=
      vecFillWhile_correct _ _ (F + 1) 0 _ _ blkOut (Nat.zero_le _)
        (by simp) rfl hn32 hfill0 hFS
    have hloopSS : evalStmtWith (evalStmtSuccHandler (evalStmtFuel F))
          vecSumWhile
          (mkVecEnv blkOut nv nv
            (BitVec.ofNat 32 0) (BitVec.ofNat 32 0))
        = .ok (mkVecEnv blkOut nv nv
            (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32))
              nv.toNat)
            (BitVec.ofNat 32 nv.toNat), .fellThrough) :=
      vecSumWhile_correct blkOut nv (F + 1) 0 nv _ _ (Nat.zero_le _)
        (by intro j hjlo hjhi; exact hgetOut j hjlo hjhi) hn32 hsum0 hFS
    have huv := vecEnv_update_v blkOut nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      nv ⟨blkOut.val, true⟩
    have harv := mkVecEnv_v blkOut nv nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      nv
    have hars := mkVecEnv_s ⟨blkOut.val, true⟩ nv
      nv
      (prefixSumU32 ((List.range nv.toNat).map (BitVec.ofNat 32)) nv.toNat)
      nv
    simp [evalFuncFuel, vecFunc, bindArgs, evalStmtFuel, evalStmtWith,
      evalExpr, litVal, envExtend, hn0, vecNew, henv, hloopFS,
      hloopSS, hfree0, huv, harv, hars]

/-- `emit_correct` for `vec_alloc` at the default fuel. -/
theorem emit_correct_vec (nv : BitVec 32)
    (hfuel : nv.toNat ≤ EVAL_FUEL) :
    evalFunc vecFunc [.u32 nv] = vecFwd nv := by
  have h32eq : (2 : Nat) ^ 32 = 4294967296 := rfl
  have h32 : nv.toNat < 2 ^ 32 := by
    rw [h32eq]
    have hle4096 : nv.toNat ≤ 4096 := by simpa [EVAL_FUEL] using hfuel
    omega
  have h := evalFuncFuel_vec EVAL_FUEL nv hfuel h32
  have hc := vecFillSumU32_correct nv.toNat
  simp only [evalFunc, vecFwd, h, hc, u32_map_ok]

/-- Corollary: `vec_alloc` delivers the `range` prefix sum on success. -/
theorem emit_correct_vec_ok (nv : BitVec 32) (r : BitVec 32)
    (hfuel : nv.toNat ≤ EVAL_FUEL)
    (h : vecFillSumU32 nv.toNat = .ok r) :
    evalFunc vecFunc [.u32 nv] = .ok (.u32 r) := by
  rw [emit_correct_vec nv hfuel]
  unfold vecFwd
  rw [h]
  exact u32_map_ok r

/-! ## Rendering to Lean file text -/

/-- Emission failures: only "not in the admitted fragment" exists
    (oracle/aliasing rejections live in `validate`, Phase 4). -/
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
  "-- Generated by the Circe emitter (Phase 4) from validated CoreIR. Do not edit.\n"
  ++ "-- Emitter correctness (`Circe.Emit.emit_correct_add/incr/choose/sum`):\n"
  ++ "-- this file is the tag-erased rendering of the verified forward function\n"
  ++ "-- (value tags dropped; pretty-printing is trusted, semantics verified).\n"
  ++ "-- Checked by `lake env lean`; see `tools/check-phase4.sh`.\n"

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

/-- Render the `choose` forward definition (`choose_fwd`). -/
def emitChooseFwdText (name : String) : String :=
  emitHeader
  ++ "\nimport Circe.Base\n\n"
  ++ s!"/-- Pure translation of `{name}` (borrow-return): forward selection. -/\n"
  ++ s!"def {name}_fwd (b : Bool) (x y : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  .ok (if b then x else y)\n"

/-- Render the `choose` backward definition (`choose_back`): file-local,
    concatenated after the forward text (no import of its own). -/
def emitChooseBackText (name : String) : String :=
  s!"/-- Backward propagation for `{name}`: the updated return value flows back to the selected input; the other input is unchanged. -/\n"
  ++ s!"def {name}_back (b : Bool) (x y ret : BitVec 32) : Result (BitVec 32 × BitVec 32) :=\n"
  ++ "  .ok (if b then (ret, y) else (x, ret))\n"

/-- Render the `sum_array` forward definition (`sum_fwd`): the length
    hypothesis travels in the type (`BoundedList`), so the loop bound is
    structural and the body is the verified `prefixSumU32` fold. -/
def emitSumText (name : String) : String :=
  emitHeader
  ++ "\nimport Circe.Base\n\n"
  ++ "/-- Pure translation of `" ++ name ++ "` (bounded `u32` accumulation, wrapping). -/\n"
  ++ "def " ++ name ++ "_fwd {n : Nat} (a : BoundedList (BitVec 32) n) : Result (BitVec 32) :=\n"
  ++ "  .ok (prefixSumU32 a.val a.val.length)\n"

/-- Render the `vec_alloc` forward definition (`vec_alloc_fwd`): the
    length comes in as a word, so the body is the verified
    `vecFillSumU32` fold over `n.toNat`. -/
def emitVecText (name : String) : String :=
  emitHeader
  ++ "\nimport Circe.Base\n\n"
  ++ "/-- Pure translation of `" ++ name ++ "` (uniquely-owned `u32` heap block: allocate, fill with indices, sum, free). -/\n"
  ++ "def " ++ name ++ "_fwd (n : BitVec 32) : Result (BitVec 32) :=\n"
  ++ "  vecFillSumU32 n.toNat\n"

/-- The emitter: accepted fragment renders to file text; everything else
    is rejected loudly (never silently modeled). -/
def emitFunc (f : Func) : Except EmitError EmittedFunc :=
  match matchFrag f with
  | some .add => .ok ⟨emitAddText f.name, none⟩
  | some .incr => .ok ⟨emitIncrText f.name, none⟩
  | some .choose =>
    .ok ⟨emitChooseFwdText f.name, some (emitChooseBackText f.name)⟩
  | some .sum => .ok ⟨emitSumText f.name, none⟩
  | some .vec => .ok ⟨emitVecText f.name, none⟩
  | none => .error (.notFragment s!"not in the admitted fragment: {f.name}")

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

/-- File bytes for one emission: forward text plus the backward definition
    (if any). Top-level def so `native_decide` can compile it. -/
def emitFileText : Except EmitError EmittedFunc → String
  | .ok e =>
    match e.backward with
    | none => e.forward
    | some b => e.forward ++ "\n" ++ b
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

/-- The emitter output for `chooseFunc` (forward + backward) is
    byte-identical to the checked-in golden. -/
example : emitFileText (emitFunc chooseFunc) =
    include_str "../tests/golden/Choose.lean" := by native_decide

/-- The emitter output for `sumFunc` is byte-identical to the checked-in
    golden. -/
example : emitFileText (emitFunc sumFunc) =
    include_str "../tests/golden/SumArray.lean" := by native_decide

/-- The emitter output for `vecFunc` is byte-identical to the checked-in
    golden. -/
example : emitFileText (emitFunc vecFunc) =
    include_str "../tests/golden/VecAlloc.lean" := by native_decide
