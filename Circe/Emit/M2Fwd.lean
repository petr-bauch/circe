/-
Circe.Emit.M2Fwd — M2 C++-lite program translations (value level).

Canonical home of the struct/method/accumulator/box definitions the M2
goldens render: `Point` + `pointTranslate`/`pointSum`, the `Acc` leaves +
`accTwo`/`moveAcc`/`scopeEarly` entries, and the `boxThrough` entry, with
their dedicated ok/err lemmas. Names are unchanged from their former
`Circe.Base` home; only the address moved (Base keeps the evaluator
vocabulary: the `Box32` type + `boxNew`/`boxGet`/`boxFree` ops, which
`Eval` calls directly, and the value/checked-op primitives). Proofs of
the emitted entries stay in their fragment modules and import this module.
-/
import Circe.Base

/-! ## Struct + methods (`translate`, `point_sum`) -/

/-! ## Struct mapping: `struct_by_value` corpus -/

/-- `struct Point { int32_t x, y; }` as a pure Lean structure. -/
structure Point where
  x : BitVec 32
  y : BitVec 32
  deriving DecidableEq, Repr

/-- `translate`: field-wise checked addition (pure equation, no memory). -/
def pointTranslate (p : Point) (dx dy : BitVec 32) : Result Point :=
  match checkedAddI32 p.x dx, checkedAddI32 p.y dy with
  | .ok x', .ok y' => .ok ⟨x', y'⟩
  | .error e, _ => .error e
  | _, .error e => .error e

/-- `translate` succeeds exactly when both field adds succeed. -/
theorem pointTranslate_ok (p : Point) (dx dy x' y' : BitVec 32)
    (hx : checkedAddI32 p.x dx = .ok x')
    (hy : checkedAddI32 p.y dy = .ok y') :
    pointTranslate p dx dy = .ok ⟨x', y'⟩ := by
  simp [pointTranslate, hx, hy]

/-- A failing `x` add propagates (and determines the error). -/
theorem pointTranslate_err_x (p : Point) (dx dy : BitVec 32) (e : Panic)
    (hx : checkedAddI32 p.x dx = .error e) :
    pointTranslate p dx dy = .error e := by
  simp [pointTranslate, hx]

/-- A failing `y` add propagates once `x` succeeds. -/
theorem pointTranslate_err_y (p : Point) (dx dy : BitVec 32)
    (x' : BitVec 32) (e : Panic)
    (hx : checkedAddI32 p.x dx = .ok x')
    (hy : checkedAddI32 p.y dy = .error e) :
    pointTranslate p dx dy = .error e := by
  simp [pointTranslate, hx, hy]

/-- M2a `sum() const`: field-wise checked addition folded to one word
    (pure equation, no memory; `this` binds the `Point` value). -/
def pointSum (p : Point) : Result (BitVec 32) :=
  checkedAddI32 p.x p.y

/-- `pointSum` succeeds exactly when the field add succeeds. -/
theorem pointSum_ok (p : Point) (s : BitVec 32)
    (h : checkedAddI32 p.x p.y = .ok s) :
    pointSum p = .ok s := by
  simp [pointSum, h]

/-- A failing field add propagates. -/
theorem pointSum_err (p : Point) (e : Panic)
    (h : checkedAddI32 p.x p.y = .error e) :
    pointSum p = .error e := by
  simp [pointSum, h]

/-! ## Accumulator leaves + entries (`acc_two`, `move_acc`, `scope_early`) -/

/-- M2b `Acc` value model: the struct never crosses the boundary (the
    entry is int-only), so the accumulator state is a single `i32` word
    threaded functionally (mutating methods functionalized, as in
    `incr`). `accCtor` is the field-init (`s = 0`), `accAdd` the checked
    `s += v`, `accGet` / `accDtor` the identity (const getter / trivial
    dtor are no-ops). -/
def accCtor : BitVec 32 := 0

def accAdd (s v : BitVec 32) : Result (BitVec 32) :=
  checkedAddI32 s v

def accGet (s : BitVec 32) : Result (BitVec 32) :=
  .ok s

def accDtor (s : BitVec 32) : Result (BitVec 32) :=
  .ok s

/-- M2b `acc_two`: ctor-init `0`, two checked adds, get (identity). -/
def accTwo (a b : BitVec 32) : Result (BitVec 32) :=
  match checkedAddI32 0 a with
  | .error e => .error e
  | .ok s1 => checkedAddI32 s1 b

/-- `accTwo` succeeds exactly when both adds succeed. -/
theorem accTwo_ok (a b s1 s2 : BitVec 32)
    (h1 : checkedAddI32 0 a = .ok s1)
    (h2 : checkedAddI32 s1 b = .ok s2) :
    accTwo a b = .ok s2 := by
  simp only [accTwo, h1, h2]

/-- A failing first add propagates (and determines the error). -/
theorem accTwo_err_a (a b : BitVec 32) (e : Panic)
    (h1 : checkedAddI32 0 a = .error e) :
    accTwo a b = .error e := by
  simp only [accTwo, h1]

/-- A failing second add propagates once the first succeeds. -/
theorem accTwo_err_b (a b s1 : BitVec 32) (e : Panic)
    (h1 : checkedAddI32 0 a = .ok s1)
    (h2 : checkedAddI32 s1 b = .error e) :
    accTwo a b = .error e := by
  simp only [accTwo, h1, h2]

/-- N4b move ctor (`_ZN3AccC2EOS_`): the destination takes the source
    word (`s(o.s)` member-init); the destination's old storage is never
    read, so the `d` arg is ignored. (The source-zeroing store
    `o.s = 0` is entry-level: `moveAccFunc` threads it as an `assign`,
    where the C++ sequence point lives.) -/
def accMoveCtor (_d s : BitVec 32) : Result (BitVec 32) :=
  .ok s

/-- N4b `move_acc`: `src` ctor-init `0`, `src += a`, move (`dst` takes
    `src`, `src` zeroed), `dst += b`, get (identity). Computationally
    the `accTwo` delegation chain; the move itself is value-preserving. -/
def moveAcc (a b : BitVec 32) : Result (BitVec 32) :=
  match checkedAddI32 0 a with
  | .error e => .error e
  | .ok s1 => checkedAddI32 s1 b

/-- `moveAcc` succeeds exactly when both adds succeed. -/
theorem moveAcc_ok (a b s1 s2 : BitVec 32)
    (h1 : checkedAddI32 0 a = .ok s1)
    (h2 : checkedAddI32 s1 b = .ok s2) :
    moveAcc a b = .ok s2 := by
  simp only [moveAcc, h1, h2]

/-- A failing first add propagates (and determines the error). -/
theorem moveAcc_err_a (a b : BitVec 32) (e : Panic)
    (h1 : checkedAddI32 0 a = .error e) :
    moveAcc a b = .error e := by
  simp only [moveAcc, h1]

/-- A failing second add propagates once the first succeeds. -/
theorem moveAcc_err_b (a b s1 : BitVec 32) (e : Panic)
    (h1 : checkedAddI32 0 a = .ok s1)
    (h2 : checkedAddI32 s1 b = .error e) :
    moveAcc a b = .error e := by
  simp only [moveAcc, h1, h2]

/-- N4b `scope_early`: `src` ctor-init `0`, `src += a`, early `get` when
    `a == b`, else `src += b` + `get` (identity). The scope-exit dtor is
    a no-op on every path, so both returns are direct. -/
def scopeEarly (a b : BitVec 32) : Result (BitVec 32) :=
  match checkedAddI32 0 a with
  | .error e => .error e
  | .ok s1 => if a == b then .ok s1 else checkedAddI32 s1 b

/-- `scopeEarly` takes the early path exactly when the first add
    succeeds and the args are equal. -/
theorem scopeEarly_ok_eq (a b s1 : BitVec 32)
    (h1 : checkedAddI32 0 a = .ok s1)
    (heq : a == b) :
    scopeEarly a b = .ok s1 := by
  unfold scopeEarly
  rw [h1]
  simp [heq]

/-- `scopeEarly` takes the fallthrough path on unequal args. -/
theorem scopeEarly_ok_ne (a b s1 s2 : BitVec 32)
    (h1 : checkedAddI32 0 a = .ok s1)
    (hne : (a == b) = false)
    (h2 : checkedAddI32 s1 b = .ok s2) :
    scopeEarly a b = .ok s2 := by
  unfold scopeEarly
  rw [h1]
  simp [hne, h2]

/-- A failing first add propagates (and determines the error). -/
theorem scopeEarly_err_a (a b : BitVec 32) (e : Panic)
    (h1 : checkedAddI32 0 a = .error e) :
    scopeEarly a b = .error e := by
  unfold scopeEarly
  rw [h1]

/-- A failing second add propagates on the fallthrough path. -/
theorem scopeEarly_err_b (a b s1 : BitVec 32) (e : Panic)
    (h1 : checkedAddI32 0 a = .ok s1)
    (hne : (a == b) = false)
    (h2 : checkedAddI32 s1 b = .error e) :
    scopeEarly a b = .error e := by
  unfold scopeEarly
  rw [h1]
  simp [hne, h2]

/-! ## Box passthrough (`box_through`) -/

/-- M2c `box_through`: `new` → read → `delete` passthrough (total). -/
def boxThrough (x : BitVec 32) : Result (BitVec 32) :=
  match boxNew x with
  | .error e => .error e
  | .ok b0 =>
    match boxGet b0 with
    | .error e => .error e
    | .ok r =>
      match boxFree b0 with
      | .error e => .error e
      | .ok _ => .ok r

/-- `box_through` is the identity (all three ops succeed on the fresh
    live box). -/
theorem boxThrough_ok (x : BitVec 32) :
    boxThrough x = .ok x := by
  simp [boxThrough, boxNew, boxGet, boxFree]
