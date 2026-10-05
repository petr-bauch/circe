/-
Circe.Base — memory-free value model for the Ownable-C subset (v0.1).

Phase 2: `Result` + checked integer ops with overflow-correctness lemmas,
plus struct/array mappings. No memory model by design
(see docs/OWNERSHIP.md).
-/

/-- Reasons a pure Ownable-C program can fail. UB in the subset maps to
    `Result.err`; out-of-subset/aliasing never reaches Lean (rejected by
    `validate`). -/
inductive Panic : Type
  | Overflow
  | DivZero
  | OOB
  | AssertFail
  | Uninit
  deriving DecidableEq, Repr

/-- Partiality monad for emitted code (`Except` with `Panic` errors). -/
abbrev Result (α : Type) : Type := Except Panic α

/-! ## Bounds -/

/-- Minimum `Int` value of C `int32_t`. -/
def int32Min : Int := -(2 ^ 31)

/-- Maximum `Int` value of C `int32_t`. -/
def int32Max : Int := 2 ^ 31 - 1

/-- Modulus of C `uint32_t`. -/
def u32Mod : Nat := 2 ^ 32

/-- Decidable range check for signed-32 (`nsw` sites). -/
def inInt32Range (z : Int) : Bool :=
  decide (int32Min ≤ z ∧ z ≤ int32Max)

/-- Propositional version of `inInt32Range` (for specs). -/
theorem inInt32Range_iff (z : Int) :
    inInt32Range z = true ↔ int32Min ≤ z ∧ z ≤ int32Max := by
  simp [inInt32Range]

/-! ## Checked signed-32 ops (`nsw` semantics) -/

/-- Checked signed-32 addition: `cir.add nsw` on `!cir.int<s,32>`.
    Returns `.error .Overflow` on signed overflow instead of wrapping. -/
def checkedAddI32 (a b : BitVec 32) : Result (BitVec 32) :=
  if inInt32Range (a.toInt + b.toInt) then .ok (a + b)
  else .error .Overflow

/-- Wrapping signed-32 addition (non-`nsw` sites; wraps, never fails). -/
def wrapAddI32 (a b : BitVec 32) : BitVec 32 := a + b

/-- `checkedAddI32` succeeds exactly on the `nsw` range condition. -/
theorem checkedAddI32_ok (a b : BitVec 32)
    (h : inInt32Range (a.toInt + b.toInt) = true) :
    checkedAddI32 a b = .ok (a + b) := by
  simp [checkedAddI32, h]

/-- `checkedAddI32` reports overflow exactly off the range. -/
theorem checkedAddI32_err (a b : BitVec 32)
    (h : inInt32Range (a.toInt + b.toInt) = false) :
    checkedAddI32 a b = .error .Overflow := by
  simp [checkedAddI32, h]

/-- Success implies the mathematical sum is in range. -/
theorem checkedAddI32_ok_implies_range (a b r : BitVec 32)
    (h : checkedAddI32 a b = .ok r) :
    int32Min ≤ a.toInt + b.toInt ∧ a.toInt + b.toInt ≤ int32Max := by
  unfold checkedAddI32 at h
  split at h
  · next hc => exact (inInt32Range_iff _).mp hc
  · next => simp at h

/-- Overflow implies the mathematical sum is out of range. -/
theorem checkedAddI32_err_implies_outside (a b : BitVec 32)
    (h : checkedAddI32 a b = .error .Overflow) :
    ¬ (int32Min ≤ a.toInt + b.toInt ∧ a.toInt + b.toInt ≤ int32Max) := by
  unfold checkedAddI32 at h
  split at h
  · next => simp at h
  · next hc => exact fun hp => absurd ((inInt32Range_iff _).mpr hp) (by simp [hc])

/-- On success the delivered value is the wrap sum. -/
theorem checkedAddI32_ok_value (a b r : BitVec 32)
    (h : checkedAddI32 a b = .ok r) : r = a + b := by
  unfold checkedAddI32 at h
  split at h
  · next => simp at h; exact h.symm
  · next => simp at h

/-- Checked addition commutes (both the range check and the sum do). -/
theorem checkedAddI32_comm (a b : BitVec 32) :
    checkedAddI32 a b = checkedAddI32 b a := by
  unfold checkedAddI32
  have hsum : a.toInt + b.toInt = b.toInt + a.toInt := Int.add_comm _ _
  have hadd : a + b = b + a := BitVec.add_comm _ _
  rw [hsum, hadd]

/-- Checked signed-32 negation: fails only on `INT_MIN`. -/
def checkedNegI32 (a : BitVec 32) : Result (BitVec 32) :=
  if inInt32Range (-a.toInt) then .ok (-a) else .error .Overflow

theorem checkedNegI32_ok (a : BitVec 32)
    (h : inInt32Range (-a.toInt) = true) :
    checkedNegI32 a = .ok (-a) := by
  simp [checkedNegI32, h]

theorem checkedNegI32_err (a : BitVec 32)
    (h : inInt32Range (-a.toInt) = false) :
    checkedNegI32 a = .error .Overflow := by
  simp [checkedNegI32, h]

/-- Checked signed-32 division: `DivZero` plus the `INT_MIN / -1` overflow. -/
def checkedDivI32 (a b : BitVec 32) : Result (BitVec 32) :=
  if b.toInt == 0 then .error .DivZero
  else if inInt32Range (a.toInt / b.toInt) then .ok (a / b)
  else .error .Overflow

theorem checkedDivI32_zero (a b : BitVec 32) (h : b.toInt = 0) :
    checkedDivI32 a b = .error .DivZero := by
  simp [checkedDivI32, h]

/-- Checked signed-32 increment: the `incr` fragment (`*p = *p + 1`). -/
def checkedIncrI32 (a : BitVec 32) : Result (BitVec 32) :=
  checkedAddI32 a 1

/-- `checkedIncrI32` is addition of one (so `incr` inherits all add lemmas). -/
theorem checkedIncrI32_eq_add_one (a : BitVec 32) :
    checkedIncrI32 a = checkedAddI32 a 1 := rfl

theorem checkedIncrI32_ok (a : BitVec 32)
    (h : inInt32Range (a.toInt + 1) = true) :
    checkedIncrI32 a = .ok (a + 1) := by
  simp [checkedIncrI32, checkedAddI32, h]

/-! ## Checked signed-64 ops (S3b: 64-bit loop-free widths) -/

/-- Minimum `Int` value of C `int64_t`. -/
def int64Min : Int := -(2 ^ 63)

/-- Maximum `Int` value of C `int64_t`. -/
def int64Max : Int := 2 ^ 63 - 1

/-- Decidable range check for signed-64 (`nsw` sites on `!s64i`). -/
def inInt64Range (z : Int) : Bool :=
  decide (int64Min ≤ z ∧ z ≤ int64Max)

/-- Propositional version of `inInt64Range` (for specs). -/
theorem inInt64Range_iff (z : Int) :
    inInt64Range z = true ↔ int64Min ≤ z ∧ z ≤ int64Max := by
  simp [inInt64Range]

/-- Checked signed-64 addition: `cir.add nsw` on `!cir.int<s,64>`.
    Returns `.error .Overflow` on signed overflow instead of wrapping. -/
def checkedAddI64 (a b : BitVec 64) : Result (BitVec 64) :=
  if inInt64Range (a.toInt + b.toInt) then .ok (a + b)
  else .error .Overflow

/-- `checkedAddI64` succeeds exactly on the `nsw` range condition. -/
theorem checkedAddI64_ok (a b : BitVec 64)
    (h : inInt64Range (a.toInt + b.toInt) = true) :
    checkedAddI64 a b = .ok (a + b) := by
  simp [checkedAddI64, h]

/-- `checkedAddI64` reports overflow exactly off the range. -/
theorem checkedAddI64_err (a b : BitVec 64)
    (h : inInt64Range (a.toInt + b.toInt) = false) :
    checkedAddI64 a b = .error .Overflow := by
  simp [checkedAddI64, h]

/-- Success implies the mathematical sum is in range. -/
theorem checkedAddI64_ok_implies_range (a b r : BitVec 64)
    (h : checkedAddI64 a b = .ok r) :
    int64Min ≤ a.toInt + b.toInt ∧ a.toInt + b.toInt ≤ int64Max := by
  unfold checkedAddI64 at h
  split at h
  · next hc => exact (inInt64Range_iff _).mp hc
  · next => simp at h

/-- Overflow implies the mathematical sum is out of range. -/
theorem checkedAddI64_err_implies_outside (a b : BitVec 64)
    (h : checkedAddI64 a b = .error .Overflow) :
    ¬ (int64Min ≤ a.toInt + b.toInt ∧ a.toInt + b.toInt ≤ int64Max) := by
  unfold checkedAddI64 at h
  split at h
  · next => simp at h
  · next hc => exact fun hp => absurd ((inInt64Range_iff _).mpr hp) (by simp [hc])

/-- On success the delivered value is the wrap sum. -/
theorem checkedAddI64_ok_value (a b r : BitVec 64)
    (h : checkedAddI64 a b = .ok r) : r = a + b := by
  unfold checkedAddI64 at h
  split at h
  · next => simp at h; exact h.symm
  · next => simp at h

/-- Checked addition commutes (both the range check and the sum do). -/
theorem checkedAddI64_comm (a b : BitVec 64) :
    checkedAddI64 a b = checkedAddI64 b a := by
  unfold checkedAddI64
  have hsum : a.toInt + b.toInt = b.toInt + a.toInt := Int.add_comm _ _
  have hadd : a + b = b + a := BitVec.add_comm _ _
  rw [hsum, hadd]

/-! ## Unsigned-32 ops -/

/-- Wrapping unsigned-32 addition (C unsigned arithmetic wraps; never fails). -/
def checkedAddU32 (a b : BitVec 32) : Result (BitVec 32) :=
  .ok (a + b)

/-- Unsigned addition always succeeds (wraps). -/
theorem checkedAddU32_ok (a b : BitVec 32) :
    ∃ r, checkedAddU32 a b = .ok r := by
  exact ⟨a + b, rfl⟩

/-- Strict unsigned addition reporting carry as `Overflow`
    (for bounds-checked indexing arithmetic). -/
def checkedAddU32Strict (a b : BitVec 32) : Result (BitVec 32) :=
  if a.toNat + b.toNat < u32Mod then .ok (a + b) else .error .Overflow

theorem checkedAddU32Strict_ok (a b : BitVec 32)
    (h : a.toNat + b.toNat < u32Mod) :
    checkedAddU32Strict a b = .ok (a + b) := by
  simp [checkedAddU32Strict, h]

theorem checkedAddU32Strict_err (a b : BitVec 32)
    (h : ¬ a.toNat + b.toNat < u32Mod) :
    checkedAddU32Strict a b = .error .Overflow := by
  simp [checkedAddU32Strict, h]

/-! ## Array mapping: length-paired lists -/

/-- An array with its C length parameter made explicit
    (`sum_array`: `a.length = n`). -/
abbrev BoundedList (α : Type) (n : Nat) : Type :=
  { l : List α // l.length = n }

/-- Bounds-checked index: `p[i]` with `0 ≤ i < n`, else `OOB`. -/
def bget {α : Type} {n : Nat} (a : BoundedList α n) (i : Nat) : Result α :=
  if h : i < a.val.length then .ok a.val[i] else .error .OOB

/-- In-bounds indexing succeeds. -/
theorem bget_ok {α : Type} {n : Nat} (a : BoundedList α n) (i : Nat)
    (h : i < a.val.length) : ∃ x, bget a i = .ok x := by
  exact ⟨a.val[i], by simp [bget, h]⟩

/-- Out-of-bounds indexing reports `OOB`. -/
theorem bget_oob {α : Type} {n : Nat} (a : BoundedList α n) (i : Nat)
    (h : ¬ i < a.val.length) : bget a i = .error .OOB := by
  simp [bget, h]

/-- The length invariant travels with the value. -/
theorem bget_length {α : Type} {n : Nat} (a : BoundedList α n) :
    a.val.length = n := a.property

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

/-! ## M2c: uniquely-owned heap box `Box32` (`new` / `delete`) -/

/-- A uniquely-owned single-`i32` heap box (`new Box{x}` / `delete`
    functionalized, Vec32 precedent at one word). `val` is the field
    value; `freed` is the affine token: `boxFree` sets it, and every use
    checks it (`AssertFail` on use-after-delete / double-`delete` —
    incompleteness, never unsoundness). Allocation is unbounded
    (`boxNew` never fails, like `_Znwm` / `vecNew`); the null-guarded
    `cir.if` in the corpus is dead (the pointer is `nonnull`) and erased
    at validation. -/
structure Box32 where
  val : BitVec 32
  freed : Bool
  deriving DecidableEq, Repr

/-- `new Box{x}`: fresh live box holding `x`. Never fails (unbounded
    allocation; `_Znwm` carries `nonnull + noundef`). -/
def boxNew (x : BitVec 32) : Result Box32 :=
  .ok ⟨x, false⟩

/-- `p->x`: token then value. -/
def boxGet (b : Box32) : Result (BitVec 32) :=
  if b.freed then .error .AssertFail
  else .ok b.val

/-- `delete p`: consumes the token (double-`delete` is `AssertFail`). -/
def boxFree (b : Box32) : Result Box32 :=
  if b.freed then .error .AssertFail
  else .ok ⟨b.val, true⟩

/-- Allocation delivers a live box holding the init value. -/
theorem boxNew_ok (x : BitVec 32) :
    boxNew x = .ok ⟨x, false⟩ := rfl

/-- Allocation keeps the box live. -/
theorem boxNew_live (x : BitVec 32) (b : Box32)
    (h : boxNew x = .ok b) : b.freed = false := by
  rw [boxNew_ok] at h
  cases h
  rfl

/-- Read on a live box succeeds. -/
theorem boxGet_ok (b : Box32)
    (hlive : b.freed = false) :
    boxGet b = .ok b.val := by
  simp [boxGet, hlive]

/-- Read on a freed box is rejected (use-after-`delete`). -/
theorem boxGet_freed (b : Box32)
    (h : b.freed = true) : boxGet b = .error .AssertFail := by
  simp [boxGet, h]

/-- Freeing a live box sets the token, keeping the value. -/
theorem boxFree_ok (b : Box32)
    (hlive : b.freed = false) :
    boxFree b = .ok ⟨b.val, true⟩ := by
  simp [boxFree, hlive]

/-- Double-`delete` is rejected. -/
theorem boxFree_double (b : Box32)
    (h : b.freed = true) : boxFree b = .error .AssertFail := by
  simp [boxFree, h]

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

/-! ## S3a control-flow folds: `nested_sum` / `skip_sum` value models -/

/-- One row of `nested_sum`: `Σ_{j<m} i*j` as a wrapping `u32` sum of
    `ofNat` products (rendered `nested_sum_fwd` references this). -/
def rowU32 (i m : Nat) : BitVec 32 :=
  ((List.range m).map (fun j => BitVec.ofNat 32 (i * j))).sum

/-- `nested_sum`: `Σ_{i<n} rowU32 i m` (rendered forward reference). -/
def nestedSumU32 (n m : Nat) : BitVec 32 :=
  ((List.range n).map (fun i => rowU32 i m)).sum

/-- `skip_sum`: `Σ` of `i ∈ [0, min n 8)`, skipping `2` (rendered
    forward reference; `break` at `8` caps the range, `continue`
    filters `2`). -/
def skipSumU32 (n : Nat) : BitVec 32 :=
  (((List.range (min n 8)).filter (fun i => i != 2)).map
    (fun i => BitVec.ofNat 32 i)).sum

/-! ## `find_eq` value model: first match, length-narrowed -/

/-- First match of `k` in `l[j]?` over `j ∈ [0, min n len)` (rendered
    forward reference). The search never passes `min n len`, so an
    early hit returns even when `n` exceeds the length (the OOB read
    never happens); running past the length with no hit is `OOB`. -/
def findIdxU32 (l : List (BitVec 32)) (n : Nat) (k : BitVec 32) :
    Option Nat :=
  ((List.range (min n l.length)).find?
    (fun j => decide (l[j]? = some k)))

/-- `find_eq` outcome on values: the first match, else the length when
    exact, else `OOB` (C would read out of bounds there — UB made
    loud). The length test is `decide`-headed so proofs rewrite it
    with a boolean equation. -/
def findEqOut (l : List (BitVec 32)) (n : Nat) (k : BitVec 32) :
    Result (BitVec 32) :=
  match findIdxU32 l n k with
  | some j => .ok (BitVec.ofNat 32 j)
  | none =>
    if decide (n ≤ l.length) then .ok (BitVec.ofNat 32 n)
    else .error .OOB

/-! ## Uniquely-owned heap: `Vec32` (Phase 7, u32-only) -/

/-- A uniquely-owned `u32` heap block (`malloc`/`free` functionalized).
    Capacity is `val.length` (fixed at creation, zero-initialized);
    `freed` is the affine token: `vecFree` sets it, and every use checks
    it (`AssertFail` on use-after-free / double-free — incompleteness,
    never unsoundness). Allocation is unbounded (`vecNew` never fails);
    bounds are enforced per-access (`OOB`). -/
structure Vec32 where
  val : List (BitVec 32)
  freed : Bool
  deriving DecidableEq, Repr

/-- `malloc(n * sizeof(uint32_t))`: fresh zeroed block, live token.
    Never fails (unbounded allocation; see the module note). -/
def vecNew (n : Nat) : Result Vec32 :=
  .ok ⟨List.replicate n 0, false⟩

/-- `v[i] = x`: token then bounds, else the updated block. -/
def vecSet (v : Vec32) (i : Nat) (x : BitVec 32) : Result Vec32 :=
  if v.freed then .error .AssertFail
  else if _ : i < v.val.length then .ok ⟨v.val.set i x, false⟩
  else .error .OOB

/-- `v[i]`: token then bounds, else the element. -/
def vecGet (v : Vec32) (i : Nat) : Result (BitVec 32) :=
  if v.freed then .error .AssertFail
  else
    match v.val[i]? with
    | some x => .ok x
    | none => .error .OOB

/-- `free(v)`: consumes the token (double-free is `AssertFail`). -/
def vecFree (v : Vec32) : Result Vec32 :=
  if v.freed then .error .AssertFail
  else .ok ⟨v.val, true⟩

/-- Allocation delivers a zeroed live block of the requested length. -/
theorem vecNew_ok (n : Nat) :
    vecNew n = .ok ⟨List.replicate n 0, false⟩ := rfl

theorem vecNew_length (n : Nat) (v : Vec32)
    (h : vecNew n = .ok v) : v.val.length = n := by
  rw [vecNew_ok] at h
  cases h
  simp

theorem vecNew_live (n : Nat) (v : Vec32)
    (h : vecNew n = .ok v) : v.freed = false := by
  rw [vecNew_ok] at h
  cases h
  rfl

/-- In-bounds set on a live block succeeds. -/
theorem vecSet_ok (v : Vec32) (i : Nat) (x : BitVec 32)
    (hlive : v.freed = false) (hb : i < v.val.length) :
    vecSet v i x = .ok ⟨v.val.set i x, false⟩ := by
  simp [vecSet, hlive, hb]

/-- Set on a freed block is rejected, never silently modeled. -/
theorem vecSet_freed (v : Vec32) (i : Nat) (x : BitVec 32)
    (h : v.freed = true) : vecSet v i x = .error .AssertFail := by
  simp [vecSet, h]

/-- Out-of-bounds set on a live block reports `OOB`. -/
theorem vecSet_oob (v : Vec32) (i : Nat) (x : BitVec 32)
    (hlive : v.freed = false) (hb : ¬ i < v.val.length) :
    vecSet v i x = .error .OOB := by
  simp [vecSet, hlive, hb]

/-- Set preserves the capacity. -/
theorem vecSet_length (v : Vec32) (i : Nat) (x : BitVec 32) (w : Vec32)
    (h : vecSet v i x = .ok w) : w.val.length = v.val.length := by
  unfold vecSet at h
  split at h
  · next => simp at h
  · next =>
    split at h
    · next => cases h; simp
    · next => simp at h

/-- Set keeps the block live. -/
theorem vecSet_live (v : Vec32) (i : Nat) (x : BitVec 32) (w : Vec32)
    (h : vecSet v i x = .ok w) : w.freed = false := by
  unfold vecSet at h
  split at h
  · next => simp at h
  · next =>
    split at h
    · next => cases h; rfl
    · next => simp at h

/-- In-bounds get on a live block succeeds. -/
theorem vecGet_ok (v : Vec32) (i : Nat) (x : BitVec 32)
    (hlive : v.freed = false) (hget : v.val[i]? = some x) :
    vecGet v i = .ok x := by
  simp [vecGet, hlive, hget]

/-- Get on a freed block is rejected. -/
theorem vecGet_freed (v : Vec32) (i : Nat)
    (h : v.freed = true) : vecGet v i = .error .AssertFail := by
  simp [vecGet, h]

/-- Out-of-bounds get on a live block reports `OOB`. -/
theorem vecGet_oob (v : Vec32) (i : Nat)
    (hlive : v.freed = false) (hget : v.val[i]? = none) :
    vecGet v i = .error .OOB := by
  simp [vecGet, hlive, hget]

/-- Freeing a live block sets the token, keeping the contents. -/
theorem vecFree_ok (v : Vec32)
    (hlive : v.freed = false) :
    vecFree v = .ok ⟨v.val, true⟩ := by
  simp [vecFree, hlive]

/-- Double-free is rejected. -/
theorem vecFree_double (v : Vec32)
    (h : v.freed = true) : vecFree v = .error .AssertFail := by
  simp [vecFree, h]

/-- `List.set` then `get?` at the same in-bounds index reads back. -/
theorem getElem?_set_self (l : List (BitVec 32)) (i : Nat)
    (x : BitVec 32) (h : i < l.length) :
    (l.set i x)[i]? = some x := by
  induction l generalizing i with
  | nil => simp at h
  | cons y ys ih =>
    cases i with
    | zero => simp [List.set]
    | succ i => simp [List.set]; exact ih i (by simpa using h)

/-- Get-after-set on a live block reads the written value. -/
theorem vecGet_set_same (v : Vec32) (i : Nat) (x : BitVec 32) (w : Vec32)
    (hlive : v.freed = false) (hb : i < v.val.length)
    (hset : vecSet v i x = .ok w) :
    vecGet w i = .ok x := by
  have hlen : w.val.length = v.val.length := vecSet_length v i x w hset
  have hset' : w.val = v.val.set i x := by
    rw [vecSet_ok v i x hlive hb] at hset
    cases hset
    rfl
  rw [vecGet_ok w i x (vecSet_live v i x w hset)]
  rw [hset']
  exact getElem?_set_self v.val i x hb

/-- Fill loop: write indices `[k, n)` into a live capacity-`n` block. -/
def vecFillLoopAux (v : Vec32) (k r : Nat) : Result Vec32 :=
  match r with
  | 0 => .ok v
  | r + 1 =>
    match vecSet v k (BitVec.ofNat 32 k) with
    | .error e => .error e
    | .ok v' => vecFillLoopAux v' (k + 1) r

/-- Fill from `0` to `n`. -/
def vecFillLoop (v : Vec32) (n : Nat) : Result Vec32 :=
  vecFillLoopAux v 0 n

/-- Sum loop: accumulate `v[k .. k+r)` into `acc` (wrapping `u32`). -/
def vecSumLoopAux (v : Vec32) (k r : Nat) (acc : BitVec 32) :
    Result (BitVec 32) :=
  match r with
  | 0 => .ok acc
  | r + 1 =>
    match vecGet v k with
    | .error e => .error e
    | .ok x => vecSumLoopAux v (k + 1) r (acc + x)

/-- Sum the whole `n`-prefix from `0`. -/
def vecSumLoop (v : Vec32) (n : Nat) : Result (BitVec 32) :=
  vecSumLoopAux v 0 n 0

/-- Whole heap program, purely: allocate, fill with indices, sum, free.
    `free` is value-invisible (contents kept, token set); leak is forgetting
    a value, sound here (M1d: `validate` admits `free <= expected`, gating
    only double-`free`). -/
def vecFillSumU32 (n : Nat) : Result (BitVec 32) :=
  match vecNew n with
  | .error e => .error e
  | .ok v0 =>
    match vecFillLoop v0 n with
    | .error e => .error e
    | .ok v1 =>
      match vecSumLoop v1 n with
      | .error e => .error e
      | .ok s =>
        match vecFree v1 with
        | .error e => .error e
        | .ok _ => .ok s

/-- Fill preserves capacity. -/
theorem vecFillLoopAux_length (v : Vec32) (k r : Nat) (w : Vec32)
    (h : vecFillLoopAux v k r = .ok w) :
    w.val.length = v.val.length := by
  induction r generalizing v k w with
  | zero => simp [vecFillLoopAux] at h; cases h; rfl
  | succ r ih =>
    unfold vecFillLoopAux at h
    match hs : vecSet v k (BitVec.ofNat 32 k) with
    | .error e => simp [hs] at h
    | .ok v' =>
      simp [hs] at h
      have hlen := vecSet_length v k (BitVec.ofNat 32 k) v' hs
      have ihr := ih v' (k + 1) w h
      omega

/-- Fill keeps the block live (every step succeeds on a live block, so the
    token can only come from the input). -/
theorem vecFillLoopAux_live (v : Vec32) (k r : Nat) (w : Vec32)
    (hlive : v.freed = false)
    (h : vecFillLoopAux v k r = .ok w) :
    w.freed = false := by
  induction r generalizing v k w with
  | zero => simp [vecFillLoopAux] at h; cases h; exact hlive
  | succ r ih =>
    unfold vecFillLoopAux at h
    match hs : vecSet v k (BitVec.ofNat 32 k) with
    | .error e => simp [hs] at h
    | .ok v' =>
      simp [hs] at h
      exact ih v' (k + 1) w (vecSet_live v k (BitVec.ofNat 32 k) v' hs) h

/-- `List.set` at `i` leaves every other position's `get?` alone. -/
theorem getElem?_set_ne (l : List (BitVec 32)) (i j : Nat)
    (x : BitVec 32) (h : j ≠ i) :
    (l.set i x)[j]? = l[j]? := by
  induction l generalizing i j with
  | nil => rfl
  | cons y ys ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl h
      | succ j => rfl
    | succ i =>
      cases j with
      | zero => rfl
      | succ j => simp [List.set]; exact ih i j (by omega)

/-- Get-after-set at a different position reads the old value. -/
theorem vecSet_get_other (v : Vec32) (i j : Nat) (x y : BitVec 32)
    (w : Vec32) (hne : j ≠ i)
    (hset : vecSet v i x = .ok w) (hget : vecGet v j = .ok y) :
    vecGet w j = .ok y := by
  have hlive : v.freed = false := by
    unfold vecSet at hset
    split at hset
    · next h => simp at hset
    · next h =>
      cases hv : v.freed
      · rfl
      · simp_all
  have hb : i < v.val.length := by
    rcases Nat.lt_or_ge i v.val.length with hb | hge
    · exact hb
    · have herr := vecSet_oob v i x hlive (by omega)
      rw [herr] at hset
      simp at hset
  have hsetw : w = ⟨v.val.set i x, false⟩ := by
    rw [vecSet_ok v i x hlive hb] at hset
    cases hset
    rfl
  have hget' : v.val[j]? = some y := by
    match hm : v.val[j]? with
    | some z =>
      have h2 : vecGet v j = .ok z := vecGet_ok v j z hlive hm
      have hzy : z = y := by
        rw [h2] at hget
        simpa using hget
      exact congrArg some hzy
    | none =>
      have h2 : vecGet v j = .error .OOB := vecGet_oob v j hlive hm
      rw [h2] at hget
      simp at hget
  subst hsetw
  show vecGet ⟨v.val.set i x, false⟩ j = .ok y
  rw [vecGet_ok _ _ _ rfl (by
    show (v.val.set i x)[j]? = some y
    rw [getElem?_set_ne _ _ _ _ hne]
    exact hget')]

/-- Filling `[k, k+r)` preserves reads below `k`. -/
theorem vecFillLoopAux_preserve (v : Vec32) (k r j : Nat) (y : BitVec 32)
    (w : Vec32) (hlt : j < k) (hget : vecGet v j = .ok y)
    (h : vecFillLoopAux v k r = .ok w) :
    vecGet w j = .ok y := by
  induction r generalizing v k w with
  | zero => simp [vecFillLoopAux] at h; cases h; exact hget
  | succ r ih =>
    unfold vecFillLoopAux at h
    match hs : vecSet v k (BitVec.ofNat 32 k) with
    | .error e => simp [hs] at h
    | .ok v' =>
      simp [hs] at h
      have hne : j ≠ k := by omega
      exact ih v' (k + 1) w (by omega)
        (vecSet_get_other v k j _ y v' hne hs hget) h

/-- A filled block reads back the index at every filled position. -/
theorem vecFillLoopAux_get (v : Vec32) (k r : Nat) (w : Vec32)
    (hlive : v.freed = false) (hlen : v.val.length = k + r)
    (h : vecFillLoopAux v k r = .ok w) (j : Nat)
    (hjlo : k ≤ j) (hjhi : j < k + r) :
    vecGet w j = .ok (BitVec.ofNat 32 j) := by
  induction r generalizing v k w j with
  | zero => omega
  | succ r ih =>
    unfold vecFillLoopAux at h
    have hk : k < v.val.length := by omega
    have hs : vecSet v k (BitVec.ofNat 32 k) =
        .ok ⟨v.val.set k (BitVec.ofNat 32 k), false⟩ :=
      vecSet_ok v k _ hlive hk
    rw [hs] at h
    simp only at h
    by_cases hjk : j = k
    · subst j
      have hhere : vecGet ⟨v.val.set k (BitVec.ofNat 32 k), false⟩ k =
          .ok (BitVec.ofNat 32 k) := by
        rw [vecGet_ok _ _ _ rfl]
        exact getElem?_set_self v.val k _ hk
      have hlen' : (⟨v.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).val.length
          = (k + 1) + r := by
        show (v.val.set k (BitVec.ofNat 32 k)).length = (k + 1) + r
        rw [List.length_set]
        omega
      have := vecFillLoopAux_preserve _ (k + 1) r k _ w (by omega) hhere h
      simpa using this
    · have hlen' : (⟨v.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).val.length
          = (k + 1) + r := by
        show (v.val.set k (BitVec.ofNat 32 k)).length = (k + 1) + r
        rw [List.length_set]
        omega
      exact ih _ _ _ (by rfl) hlen' h j (by omega) (by omega)

/-! ### M1a: block copy (`vec_copy_sum`, two live blocks) -/

/-- Copy loop: write `src[k .. k+r)` into `dst` (M1a). Reads through
    `vecGet`, writes through `vecSet`: either side's token/bounds
    failure is loud. Both spec and unfolding witness for
    `vecCopyWhile_correct` (cf. `vecFillLoopAux`). -/
def vecCopyLoopAux (src dst : Vec32) (k r : Nat) : Result Vec32 :=
  match r with
  | 0 => .ok dst
  | r + 1 =>
    match vecGet src k with
    | .error e => .error e
    | .ok x =>
      match vecSet dst k x with
      | .error e => .error e
      | .ok dst' => vecCopyLoopAux src dst' (k + 1) r

/-- Copy preserves the capacity. -/
theorem vecCopyLoopAux_length (src dst : Vec32) (k r : Nat) (w : Vec32)
    (h : vecCopyLoopAux src dst k r = .ok w) :
    w.val.length = dst.val.length := by
  -- NOTE: `induction ... generalizing` orders the `ih` binders by
  -- theorem declaration order (`dst k w` here), *not* by listed order
  -- (probed). The `vecFill*` proofs never noticed: `(v k w)` is
  -- type-palindromic. Calls below use declaration order.
  induction r generalizing k dst w with
  | zero =>
    simp [vecCopyLoopAux] at h; cases h; rfl
  | succ r ih =>
    unfold vecCopyLoopAux at h
    match hg : vecGet src k with
    | .error e => simp [hg] at h
    | .ok x =>
      match hs : vecSet dst k x with
      | .error e => simp [hg, hs] at h
      | .ok dst' =>
        simp [hg, hs] at h
        have hlen := vecSet_length dst k x dst' hs
        have ihr := ih dst' (k + 1) w h
        omega

/-- Copy keeps the destination live (every step succeeds on a live
    destination, so the token can only come from the input). -/
theorem vecCopyLoopAux_live (src dst : Vec32) (k r : Nat) (w : Vec32)
    (hlive : dst.freed = false)
    (h : vecCopyLoopAux src dst k r = .ok w) :
    w.freed = false := by
  induction r generalizing k dst w with
  | zero =>
    simp [vecCopyLoopAux] at h; cases h; exact hlive
  | succ r ih =>
    unfold vecCopyLoopAux at h
    match hg : vecGet src k with
    | .error e => simp [hg] at h
    | .ok x =>
      match hs : vecSet dst k x with
      | .error e => simp [hg, hs] at h
      | .ok dst' =>
        simp [hg, hs] at h
        exact ih dst' (k + 1) w (vecSet_live dst k x dst' hs) h

/-- Copying `[k, k+r)` preserves reads below `k`
    (cf. `vecFillLoopAux_preserve`). -/
theorem vecCopyLoopAux_preserve (src dst : Vec32) (k r j : Nat)
    (y : BitVec 32) (w : Vec32) (hlt : j < k)
    (hget : vecGet dst j = .ok y)
    (h : vecCopyLoopAux src dst k r = .ok w) :
    vecGet w j = .ok y := by
  induction r generalizing k dst w with
  | zero =>
    simp [vecCopyLoopAux] at h; cases h; exact hget
  | succ r ih =>
    unfold vecCopyLoopAux at h
    match hg : vecGet src k with
    | .error e => simp [hg] at h
    | .ok x =>
      match hs : vecSet dst k x with
      | .error e => simp [hg, hs] at h
      | .ok dst' =>
        simp [hg, hs] at h
        have hne : j ≠ k := by omega
        exact ih dst' (k + 1) w (by omega)
          (vecSet_get_other dst k j x y dst' hne hs hget) h

/-- A copied range reads back `src`'s values: positions below `k` are
    preserved, positions in `[k, k+r)` take what `src` holds there.
    With `src` holding indices, the copy holds indices. -/
theorem vecCopyLoopAux_all (src dst : Vec32) (k r : Nat) (w : Vec32)
    (hliveD : dst.freed = false) (hlenD : dst.val.length = src.val.length)
    (hbound : k + r ≤ src.val.length)
    (hpre : ∀ t, t < k → vecGet dst t = .ok (BitVec.ofNat 32 t))
    (hsrc : ∀ t, t < k + r → vecGet src t = .ok (BitVec.ofNat 32 t))
    (h : vecCopyLoopAux src dst k r = .ok w) (j : Nat)
    (hjhi : j < k + r) :
    vecGet w j = .ok (BitVec.ofNat 32 j) := by
  induction r generalizing k dst w with
  | zero =>
    simp [vecCopyLoopAux] at h; cases h
    exact hpre j (by omega)
  | succ r ih =>
    unfold vecCopyLoopAux at h
    have hgetk : vecGet src k = .ok (BitVec.ofNat 32 k) :=
      hsrc k (by omega)
    simp only [hgetk] at h
    have hklen : k < dst.val.length := by omega
    have hs : vecSet dst k (BitVec.ofNat 32 k) =
        .ok ⟨dst.val.set k (BitVec.ofNat 32 k), false⟩ :=
      vecSet_ok dst k _ hliveD hklen
    rw [hs] at h
    simp only at h
    by_cases hjk : j = k
    · subst j
      have hhere : vecGet ⟨dst.val.set k (BitVec.ofNat 32 k), false⟩ k =
          .ok (BitVec.ofNat 32 k) := by
        rw [vecGet_ok _ _ _ rfl]
        exact getElem?_set_self dst.val k _ hklen
      have := vecCopyLoopAux_preserve src
        ⟨dst.val.set k (BitVec.ofNat 32 k), false⟩ (k + 1) r k _ w
        (by omega) hhere h
      simpa using this
    · have hlen' : (⟨dst.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).val.length
        = src.val.length := by
        show (dst.val.set k (BitVec.ofNat 32 k)).length = src.val.length
        rw [List.length_set]
        omega
      have hlive' : (⟨dst.val.set k (BitVec.ofNat 32 k), false⟩ : Vec32).freed
          = false := rfl
      have hpre' : ∀ t, t < k + 1 →
          vecGet ⟨dst.val.set k (BitVec.ofNat 32 k), false⟩ t =
            .ok (BitVec.ofNat 32 t) := by
        intro t ht
        by_cases htk : t = k
        · subst t
          rw [vecGet_ok _ _ _ rfl]
          exact getElem?_set_self dst.val k _ hklen
        · exact vecSet_get_other dst k t _ _ _ (by omega) hs
            (hpre t (by omega))
      exact ih _ (k + 1) w hlive' hlen' (by omega) hpre'
        (fun t ht => hsrc t (by omega)) h (by omega)

/-- Copy on live equal-length blocks with indexed `src` always succeeds. -/
theorem vecCopyLoopAux_fresh_ok (src dst : Vec32) (k r : Nat)
    (_hliveS : src.freed = false) (hliveD : dst.freed = false)
    (hlen : dst.val.length = src.val.length)
    (hbound : k + r ≤ src.val.length)
    (hsrc : ∀ t, t < k + r → vecGet src t = .ok (BitVec.ofNat 32 t)) :
    ∃ w, vecCopyLoopAux src dst k r = .ok w := by
  induction r generalizing k dst with
  | zero => exact ⟨dst, rfl⟩
  | succ r ih =>
    have hgetk : vecGet src k = .ok (BitVec.ofNat 32 k) :=
      hsrc k (by omega)
    have hklen : k < dst.val.length := by omega
    have hs : vecSet dst k (BitVec.ofNat 32 k) =
        .ok ⟨dst.val.set k (BitVec.ofNat 32 k), false⟩ :=
      vecSet_ok dst k _ hliveD hklen
    unfold vecCopyLoopAux
    simp only [hgetk, hs]
    have hlen' : (dst.val.set k (BitVec.ofNat 32 k)).length
        = src.val.length := by
      rw [List.length_set]
      omega
    exact ih ⟨dst.val.set k (BitVec.ofNat 32 k), false⟩ (k + 1)
      (vecSet_live dst k _ _ hs) hlen' (by omega)
      (fun t ht => hsrc t (by omega))

/-- Fill on a live capacity-`(k+r)` block always succeeds. -/
theorem vecFillLoopAux_fresh_ok (l : List (BitVec 32)) (k r : Nat)
    (h : l.length = k + r) :
    ∃ w, vecFillLoopAux ⟨l, false⟩ k r = .ok w := by
  induction r generalizing l k with
  | zero => exact ⟨⟨l, false⟩, rfl⟩
  | succ r ih =>
    have hk : k < (⟨l, false⟩ : Vec32).val.length := by
      show k < l.length
      omega
    have hs : vecSet ⟨l, false⟩ k (BitVec.ofNat 32 k) =
        .ok ⟨l.set k (BitVec.ofNat 32 k), false⟩ :=
      vecSet_ok _ _ _ rfl hk
    unfold vecFillLoopAux
    rw [hs]
    simp only
    have hlen : (l.set k (BitVec.ofNat 32 k)).length = (k + 1) + r := by
      rw [List.length_set]
      omega
    exact ih _ _ hlen

/-- Wrapping prefix sum of the first `k` elements (`sum_array` accumulates
    `uint32_t`, so addition wraps mod 2^32 and never fails). -/
def prefixSumU32 : List (BitVec 32) → Nat → BitVec 32
  | [], _ => 0
  | _, 0 => 0
  | x :: xs, k + 1 => x + prefixSumU32 xs k

theorem prefixSumU32_nil (k : Nat) : prefixSumU32 [] k = 0 := by
  cases k <;> rfl

theorem prefixSumU32_zero (l : List (BitVec 32)) : prefixSumU32 l 0 = 0 := by
  cases l <;> rfl

theorem prefixSumU32_cons (x : BitVec 32) (xs : List (BitVec 32)) (k : Nat) :
    prefixSumU32 (x :: xs) (k + 1) = x + prefixSumU32 xs k := rfl

/-- Bridge to the spec world: a prefix sum is the `List.sum` of the taken
    prefix (Phase 5 functional specs build on this). -/
theorem prefixSumU32_take_sum (l : List (BitVec 32)) (k : Nat) :
    prefixSumU32 l k = (l.take k).sum := by
  induction l generalizing k with
  | nil => cases k <;> rfl
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k => simp [prefixSumU32, List.sum_cons, ih]

/-- Full-length prefix sum is the whole-list sum. -/
theorem prefixSumU32_full (l : List (BitVec 32)) :
    prefixSumU32 l l.length = l.sum := by
  have h := prefixSumU32_take_sum l l.length
  rwa [List.take_length] at h

/-! ## Heap program bridges (need `prefixSumU32`, so they live last) -/

/-- Sum loop over filled positions folds the `range'` prefix. -/
theorem vecSumLoopAux_correct (v : Vec32) (k r : Nat) (acc : BitVec 32)
    (hget : ∀ j, k ≤ j → j < k + r → vecGet v j = .ok (BitVec.ofNat 32 j)) :
    vecSumLoopAux v k r acc =
      .ok (acc + prefixSumU32 ((List.range' k r).map (BitVec.ofNat 32)) r) := by
  induction r generalizing k acc with
  | zero =>
    simp [vecSumLoopAux, prefixSumU32_zero, BitVec.add_zero]
  | succ r ih =>
    have hk : k < k + (r + 1) := by omega
    have hgetk : vecGet v k = .ok (BitVec.ofNat 32 k) :=
      hget k (Nat.le_refl _) hk
    unfold vecSumLoopAux
    rw [hgetk]
    simp only
    rw [ih (k + 1) (acc + BitVec.ofNat 32 k) (by
      intro j hjlo hjhi
      exact hget j (by omega) (by omega))]
    congr 1
    rw [List.range'_succ, List.map_cons, prefixSumU32_cons]
    exact BitVec.add_assoc acc _ _

/-- Whole-program bridge: allocate/fill/sum/free equals the `range` prefix
    sum (the spec world; `free` is value-invisible). -/
theorem vecFillSumU32_correct (n : Nat) :
    vecFillSumU32 n =
      .ok (prefixSumU32 ((List.range n).map (BitVec.ofNat 32)) n) := by
  have hfill := vecFillLoopAux_fresh_ok (List.replicate n 0) 0 n (by simp)
  obtain ⟨w, hw⟩ := hfill
  have hlive : w.freed = false :=
    vecFillLoopAux_live _ _ _ _ rfl hw
  have hlenFresh : (⟨List.replicate n 0, false⟩ : Vec32).val.length = 0 + n := by
    simp
  have hget : ∀ j, 0 ≤ j → j < 0 + n →
      vecGet w j = .ok (BitVec.ofNat 32 j) :=
    fun j hjlo hjhi => vecFillLoopAux_get _ 0 n _ rfl hlenFresh
      hw j hjlo hjhi
  have hsum := vecSumLoopAux_correct w 0 n 0 (by
    intro j hjlo hjhi
    exact hget j hjlo hjhi)
  have hfree : vecFree w = .ok ⟨w.val, true⟩ := vecFree_ok w hlive
  have hrange : List.range' 0 n = List.range n := by
    simp [List.range_eq_range']
  simp only [vecFillSumU32, vecNew_ok, vecFillLoop, hw] at *
  simp only [vecSumLoop] at hsum ⊢
  rw [hsum]
  simp only
  rw [hfree]
  simp only
  congr 1
  rw [hrange]
  simp [BitVec.zero_add]

/-! ## M1b: uniquely-owned heap mirror `Vec64` (u64-only) -/

/-- A uniquely-owned `u64` heap block (`malloc`/`free` functionalized).
    Monomorphized mirror of `Vec32` (M1b): no `Vec α` polymorphism
    (width unification stays deferred, see docs/DELIVERED.md S3b).
    Capacity is `val.length` (fixed at creation, zero-initialized);
    `freed` is the affine token: `vecFree64` sets it, and every use checks
    it (`AssertFail` on use-after-free / double-free — incompleteness,
    never unsoundness). Allocation is unbounded (`vecNew64` never fails);
    bounds are enforced per-access (`OOB`). -/
structure Vec64 where
  val : List (BitVec 64)
  freed : Bool
  deriving DecidableEq, Repr

/-- `malloc(n * sizeof(uint64_t))`: fresh zeroed block, live token.
    Never fails (unbounded allocation; see the module note). -/
def vecNew64 (n : Nat) : Result Vec64 :=
  .ok ⟨List.replicate n 0, false⟩

/-- `v[i] = x`: token then bounds, else the updated block. -/
def vecSet64 (v : Vec64) (i : Nat) (x : BitVec 64) : Result Vec64 :=
  if v.freed then .error .AssertFail
  else if _ : i < v.val.length then .ok ⟨v.val.set i x, false⟩
  else .error .OOB

/-- `v[i]`: token then bounds, else the element. -/
def vecGet64 (v : Vec64) (i : Nat) : Result (BitVec 64) :=
  if v.freed then .error .AssertFail
  else
    match v.val[i]? with
    | some x => .ok x
    | none => .error .OOB

/-- `free(v)`: consumes the token (double-free is `AssertFail`). -/
def vecFree64 (v : Vec64) : Result Vec64 :=
  if v.freed then .error .AssertFail
  else .ok ⟨v.val, true⟩

/-- Allocation delivers a zeroed live block of the requested length. -/
theorem vecNew64_ok (n : Nat) :
    vecNew64 n = .ok ⟨List.replicate n 0, false⟩ := rfl

theorem vecNew64_length (n : Nat) (v : Vec64)
    (h : vecNew64 n = .ok v) : v.val.length = n := by
  rw [vecNew64_ok] at h
  cases h
  simp

theorem vecNew64_live (n : Nat) (v : Vec64)
    (h : vecNew64 n = .ok v) : v.freed = false := by
  rw [vecNew64_ok] at h
  cases h
  rfl

/-- In-bounds set on a live block succeeds. -/
theorem vecSet64_ok (v : Vec64) (i : Nat) (x : BitVec 64)
    (hlive : v.freed = false) (hb : i < v.val.length) :
    vecSet64 v i x = .ok ⟨v.val.set i x, false⟩ := by
  simp [vecSet64, hlive, hb]

/-- Set on a freed block is rejected, never silently modeled. -/
theorem vecSet64_freed (v : Vec64) (i : Nat) (x : BitVec 64)
    (h : v.freed = true) : vecSet64 v i x = .error .AssertFail := by
  simp [vecSet64, h]

/-- Out-of-bounds set on a live block reports `OOB`. -/
theorem vecSet64_oob (v : Vec64) (i : Nat) (x : BitVec 64)
    (hlive : v.freed = false) (hb : ¬ i < v.val.length) :
    vecSet64 v i x = .error .OOB := by
  simp [vecSet64, hlive, hb]

/-- Set preserves the capacity. -/
theorem vecSet64_length (v : Vec64) (i : Nat) (x : BitVec 64) (w : Vec64)
    (h : vecSet64 v i x = .ok w) : w.val.length = v.val.length := by
  unfold vecSet64 at h
  split at h
  · next => simp at h
  · next =>
    split at h
    · next => cases h; simp
    · next => simp at h

/-- Set keeps the block live. -/
theorem vecSet64_live (v : Vec64) (i : Nat) (x : BitVec 64) (w : Vec64)
    (h : vecSet64 v i x = .ok w) : w.freed = false := by
  unfold vecSet64 at h
  split at h
  · next => simp at h
  · next =>
    split at h
    · next => cases h; rfl
    · next => simp at h

/-- In-bounds get on a live block succeeds. -/
theorem vecGet64_ok (v : Vec64) (i : Nat) (x : BitVec 64)
    (hlive : v.freed = false) (hget : v.val[i]? = some x) :
    vecGet64 v i = .ok x := by
  simp [vecGet64, hlive, hget]

/-- Get on a freed block is rejected. -/
theorem vecGet64_freed (v : Vec64) (i : Nat)
    (h : v.freed = true) : vecGet64 v i = .error .AssertFail := by
  simp [vecGet64, h]

/-- Out-of-bounds get on a live block reports `OOB`. -/
theorem vecGet64_oob (v : Vec64) (i : Nat)
    (hlive : v.freed = false) (hget : v.val[i]? = none) :
    vecGet64 v i = .error .OOB := by
  simp [vecGet64, hlive, hget]

/-- Freeing a live block sets the token, keeping the contents. -/
theorem vecFree64_ok (v : Vec64)
    (hlive : v.freed = false) :
    vecFree64 v = .ok ⟨v.val, true⟩ := by
  simp [vecFree64, hlive]

/-- Double-free is rejected. -/
theorem vecFree64_double (v : Vec64)
    (h : v.freed = true) : vecFree64 v = .error .AssertFail := by
  simp [vecFree64, h]

/-- `List.set` then `get?` at the same in-bounds index reads back. -/
theorem getElem?_set_self64 (l : List (BitVec 64)) (i : Nat)
    (x : BitVec 64) (h : i < l.length) :
    (l.set i x)[i]? = some x := by
  induction l generalizing i with
  | nil => simp at h
  | cons y ys ih =>
    cases i with
    | zero => simp [List.set]
    | succ i => simp [List.set]; exact ih i (by simpa using h)

/-- Get-after-set on a live block reads the written value. -/
theorem vecGet64_set_same (v : Vec64) (i : Nat) (x : BitVec 64) (w : Vec64)
    (hlive : v.freed = false) (hb : i < v.val.length)
    (hset : vecSet64 v i x = .ok w) :
    vecGet64 w i = .ok x := by
  have hlen : w.val.length = v.val.length := vecSet64_length v i x w hset
  have hset' : w.val = v.val.set i x := by
    rw [vecSet64_ok v i x hlive hb] at hset
    cases hset
    rfl
  rw [vecGet64_ok w i x (vecSet64_live v i x w hset)]
  rw [hset']
  exact getElem?_set_self64 v.val i x hb

/-- Fill loop: write indices `[k, n)` into a live capacity-`n` block. -/
def vecFillLoopAux64 (v : Vec64) (k r : Nat) : Result Vec64 :=
  match r with
  | 0 => .ok v
  | r + 1 =>
    match vecSet64 v k (BitVec.ofNat 64 k) with
    | .error e => .error e
    | .ok v' => vecFillLoopAux64 v' (k + 1) r

/-- Fill from `0` to `n`. -/
def vecFillLoop64 (v : Vec64) (n : Nat) : Result Vec64 :=
  vecFillLoopAux64 v 0 n

/-- Sum loop: accumulate `v[k .. k+r)` into `acc` (wrapping `u64`). -/
def vecSumLoopAux64 (v : Vec64) (k r : Nat) (acc : BitVec 64) :
    Result (BitVec 64) :=
  match r with
  | 0 => .ok acc
  | r + 1 =>
    match vecGet64 v k with
    | .error e => .error e
    | .ok x => vecSumLoopAux64 v (k + 1) r (acc + x)

/-- Sum the whole `n`-prefix from `0`. -/
def vecSumLoop64 (v : Vec64) (n : Nat) : Result (BitVec 64) :=
  vecSumLoopAux64 v 0 n 0

/-- Whole heap program, purely: allocate, fill with indices, sum, free.
    `free` is value-invisible (contents kept, token set); leak is forgetting
    a value, sound here (M1d: `validate` admits `free <= expected`, gating
    only double-`free`). -/
def vecFillSumU64 (n : Nat) : Result (BitVec 64) :=
  match vecNew64 n with
  | .error e => .error e
  | .ok v0 =>
    match vecFillLoop64 v0 n with
    | .error e => .error e
    | .ok v1 =>
      match vecSumLoop64 v1 n with
      | .error e => .error e
      | .ok s =>
        match vecFree64 v1 with
        | .error e => .error e
        | .ok _ => .ok s

/-- Fill preserves capacity. -/
theorem vecFillLoopAux64_length (v : Vec64) (k r : Nat) (w : Vec64)
    (h : vecFillLoopAux64 v k r = .ok w) :
    w.val.length = v.val.length := by
  induction r generalizing v k w with
  | zero => simp [vecFillLoopAux64] at h; cases h; rfl
  | succ r ih =>
    unfold vecFillLoopAux64 at h
    match hs : vecSet64 v k (BitVec.ofNat 64 k) with
    | .error e => simp [hs] at h
    | .ok v' =>
      simp [hs] at h
      have hlen := vecSet64_length v k (BitVec.ofNat 64 k) v' hs
      have ihr := ih v' (k + 1) w h
      omega

/-- Fill keeps the block live (every step succeeds on a live block, so the
    token can only come from the input). -/
theorem vecFillLoopAux64_live (v : Vec64) (k r : Nat) (w : Vec64)
    (hlive : v.freed = false)
    (h : vecFillLoopAux64 v k r = .ok w) :
    w.freed = false := by
  induction r generalizing v k w with
  | zero => simp [vecFillLoopAux64] at h; cases h; exact hlive
  | succ r ih =>
    unfold vecFillLoopAux64 at h
    match hs : vecSet64 v k (BitVec.ofNat 64 k) with
    | .error e => simp [hs] at h
    | .ok v' =>
      simp [hs] at h
      exact ih v' (k + 1) w (vecSet64_live v k (BitVec.ofNat 64 k) v' hs) h

/-- `List.set` at `i` leaves every other position's `get?` alone. -/
theorem getElem?_set_ne64 (l : List (BitVec 64)) (i j : Nat)
    (x : BitVec 64) (h : j ≠ i) :
    (l.set i x)[j]? = l[j]? := by
  induction l generalizing i j with
  | nil => rfl
  | cons y ys ih =>
    cases i with
    | zero =>
      cases j with
      | zero => exact absurd rfl h
      | succ j => rfl
    | succ i =>
      cases j with
      | zero => rfl
      | succ j => simp [List.set]; exact ih i j (by omega)

/-- Get-after-set at a different position reads the old value. -/
theorem vecSet64_get_other (v : Vec64) (i j : Nat) (x y : BitVec 64)
    (w : Vec64) (hne : j ≠ i)
    (hset : vecSet64 v i x = .ok w) (hget : vecGet64 v j = .ok y) :
    vecGet64 w j = .ok y := by
  have hlive : v.freed = false := by
    unfold vecSet64 at hset
    split at hset
    · next h => simp at hset
    · next h =>
      cases hv : v.freed
      · rfl
      · simp_all
  have hb : i < v.val.length := by
    rcases Nat.lt_or_ge i v.val.length with hb | hge
    · exact hb
    · have herr := vecSet64_oob v i x hlive (by omega)
      rw [herr] at hset
      simp at hset
  have hsetw : w = ⟨v.val.set i x, false⟩ := by
    rw [vecSet64_ok v i x hlive hb] at hset
    cases hset
    rfl
  have hget' : v.val[j]? = some y := by
    match hm : v.val[j]? with
    | some z =>
      have h2 : vecGet64 v j = .ok z := vecGet64_ok v j z hlive hm
      have hzy : z = y := by
        rw [h2] at hget
        simpa using hget
      exact congrArg some hzy
    | none =>
      have h2 : vecGet64 v j = .error .OOB := vecGet64_oob v j hlive hm
      rw [h2] at hget
      simp at hget
  subst hsetw
  show vecGet64 ⟨v.val.set i x, false⟩ j = .ok y
  rw [vecGet64_ok _ _ _ rfl (by
    show (v.val.set i x)[j]? = some y
    rw [getElem?_set_ne64 _ _ _ _ hne]
    exact hget')]

/-- Filling `[k, k+r)` preserves reads below `k`. -/
theorem vecFillLoopAux64_preserve (v : Vec64) (k r j : Nat) (y : BitVec 64)
    (w : Vec64) (hlt : j < k) (hget : vecGet64 v j = .ok y)
    (h : vecFillLoopAux64 v k r = .ok w) :
    vecGet64 w j = .ok y := by
  induction r generalizing v k w with
  | zero => simp [vecFillLoopAux64] at h; cases h; exact hget
  | succ r ih =>
    unfold vecFillLoopAux64 at h
    match hs : vecSet64 v k (BitVec.ofNat 64 k) with
    | .error e => simp [hs] at h
    | .ok v' =>
      simp [hs] at h
      have hne : j ≠ k := by omega
      exact ih v' (k + 1) w (by omega)
        (vecSet64_get_other v k j _ y v' hne hs hget) h

/-- A filled block reads back the index at every filled position. -/
theorem vecFillLoopAux64_get (v : Vec64) (k r : Nat) (w : Vec64)
    (hlive : v.freed = false) (hlen : v.val.length = k + r)
    (h : vecFillLoopAux64 v k r = .ok w) (j : Nat)
    (hjlo : k ≤ j) (hjhi : j < k + r) :
    vecGet64 w j = .ok (BitVec.ofNat 64 j) := by
  induction r generalizing v k w j with
  | zero => omega
  | succ r ih =>
    unfold vecFillLoopAux64 at h
    have hk : k < v.val.length := by omega
    have hs : vecSet64 v k (BitVec.ofNat 64 k) =
        .ok ⟨v.val.set k (BitVec.ofNat 64 k), false⟩ :=
      vecSet64_ok v k _ hlive hk
    rw [hs] at h
    simp only at h
    by_cases hjk : j = k
    · subst j
      have hhere : vecGet64 ⟨v.val.set k (BitVec.ofNat 64 k), false⟩ k =
          .ok (BitVec.ofNat 64 k) := by
        rw [vecGet64_ok _ _ _ rfl]
        exact getElem?_set_self64 v.val k _ hk
      have hlen' : (⟨v.val.set k (BitVec.ofNat 64 k), false⟩ : Vec64).val.length
          = (k + 1) + r := by
        show (v.val.set k (BitVec.ofNat 64 k)).length = (k + 1) + r
        rw [List.length_set]
        omega
      have := vecFillLoopAux64_preserve _ (k + 1) r k _ w (by omega) hhere h
      simpa using this
    · have hlen' : (⟨v.val.set k (BitVec.ofNat 64 k), false⟩ : Vec64).val.length
          = (k + 1) + r := by
        show (v.val.set k (BitVec.ofNat 64 k)).length = (k + 1) + r
        rw [List.length_set]
        omega
      exact ih _ _ _ (by rfl) hlen' h j (by omega) (by omega)

/-- Fill on a live capacity-`(k+r)` block always succeeds. -/
theorem vecFillLoopAux64_fresh_ok (l : List (BitVec 64)) (k r : Nat)
    (h : l.length = k + r) :
    ∃ w, vecFillLoopAux64 ⟨l, false⟩ k r = .ok w := by
  induction r generalizing l k with
  | zero => exact ⟨⟨l, false⟩, rfl⟩
  | succ r ih =>
    have hk : k < (⟨l, false⟩ : Vec64).val.length := by
      show k < l.length
      omega
    have hs : vecSet64 ⟨l, false⟩ k (BitVec.ofNat 64 k) =
        .ok ⟨l.set k (BitVec.ofNat 64 k), false⟩ :=
      vecSet64_ok _ _ _ rfl hk
    unfold vecFillLoopAux64
    rw [hs]
    simp only
    have hlen : (l.set k (BitVec.ofNat 64 k)).length = (k + 1) + r := by
      rw [List.length_set]
      omega
    exact ih _ _ hlen

/-- Wrapping prefix sum of the first `k` elements (wrapping `u64`,
    so addition wraps mod 2^64 and never fails). -/
def prefixSumU64 : List (BitVec 64) → Nat → BitVec 64
  | [], _ => 0
  | _, 0 => 0
  | x :: xs, k + 1 => x + prefixSumU64 xs k

theorem prefixSumU64_nil (k : Nat) : prefixSumU64 [] k = 0 := by
  cases k <;> rfl

theorem prefixSumU64_zero (l : List (BitVec 64)) : prefixSumU64 l 0 = 0 := by
  cases l <;> rfl

theorem prefixSumU64_cons (x : BitVec 64) (xs : List (BitVec 64)) (k : Nat) :
    prefixSumU64 (x :: xs) (k + 1) = x + prefixSumU64 xs k := rfl

/-- Bridge to the spec world: a prefix sum is the `List.sum` of the taken
    prefix (Phase 5 functional specs build on this). -/
theorem prefixSumU64_take_sum (l : List (BitVec 64)) (k : Nat) :
    prefixSumU64 l k = (l.take k).sum := by
  induction l generalizing k with
  | nil => cases k <;> rfl
  | cons x xs ih =>
    cases k with
    | zero => rfl
    | succ k => simp [prefixSumU64, List.sum_cons, ih]

/-- Full-length prefix sum is the whole-list sum. -/
theorem prefixSumU64_full (l : List (BitVec 64)) :
    prefixSumU64 l l.length = l.sum := by
  have h := prefixSumU64_take_sum l l.length
  rwa [List.take_length] at h

/-! ## Heap program bridges (need `prefixSumU64`, so they live last) -/

/-- Sum loop over filled positions folds the `range'` prefix. -/
theorem vecSumLoopAux64_correct (v : Vec64) (k r : Nat) (acc : BitVec 64)
    (hget : ∀ j, k ≤ j → j < k + r → vecGet64 v j = .ok (BitVec.ofNat 64 j)) :
    vecSumLoopAux64 v k r acc =
      .ok (acc + prefixSumU64 ((List.range' k r).map (BitVec.ofNat 64)) r) := by
  induction r generalizing k acc with
  | zero =>
    simp [vecSumLoopAux64, prefixSumU64_zero, BitVec.add_zero]
  | succ r ih =>
    have hk : k < k + (r + 1) := by omega
    have hgetk : vecGet64 v k = .ok (BitVec.ofNat 64 k) :=
      hget k (Nat.le_refl _) hk
    unfold vecSumLoopAux64
    rw [hgetk]
    simp only
    rw [ih (k + 1) (acc + BitVec.ofNat 64 k) (by
      intro j hjlo hjhi
      exact hget j (by omega) (by omega))]
    congr 1
    rw [List.range'_succ, List.map_cons, prefixSumU64_cons]
    exact BitVec.add_assoc acc _ _

/-- Whole-program bridge: allocate/fill/sum/free equals the `range` prefix
    sum (the spec world; `free` is value-invisible). -/
theorem vecFillSumU64_correct (n : Nat) :
    vecFillSumU64 n =
      .ok (prefixSumU64 ((List.range n).map (BitVec.ofNat 64)) n) := by
  have hfill := vecFillLoopAux64_fresh_ok (List.replicate n 0) 0 n (by simp)
  obtain ⟨w, hw⟩ := hfill
  have hlive : w.freed = false :=
    vecFillLoopAux64_live _ _ _ _ rfl hw
  have hlenFresh : (⟨List.replicate n 0, false⟩ : Vec64).val.length = 0 + n := by
    simp
  have hget : ∀ j, 0 ≤ j → j < 0 + n →
      vecGet64 w j = .ok (BitVec.ofNat 64 j) :=
    fun j hjlo hjhi => vecFillLoopAux64_get _ 0 n _ rfl hlenFresh
      hw j hjlo hjhi
  have hsum := vecSumLoopAux64_correct w 0 n 0 (by
    intro j hjlo hjhi
    exact hget j hjlo hjhi)
  have hfree : vecFree64 w = .ok ⟨w.val, true⟩ := vecFree64_ok w hlive
  have hrange : List.range' 0 n = List.range n := by
    simp [List.range_eq_range']
  simp only [vecFillSumU64, vecNew64_ok, vecFillLoop64, hw] at *
  simp only [vecSumLoop64] at hsum ⊢
  rw [hsum]
  simp only
  rw [hfree]
  simp only
  congr 1
  rw [hrange]
  simp [BitVec.zero_add]

/-! ## M1c: `realloc` (`vec_realloc`, grow a uniquely-owned `u32` block) -/

/-- `realloc(v, m * sizeof(uint32_t))`: resize to `m` words, preserving the
    `min(old, new)` prefix and zero-filling growth (the extension is
    explicitly initialized before any read in the admitted shape, so the
    zero-fill is unobservable there — like `malloc` zero-init in
    `vec_alloc`). Never fails (unbounded allocation, like `vecNew`);
    use-after-`free` is `AssertFail`. The `realloc(p, 0)` (= `free`) and
    `realloc(NULL, n)` (= `malloc`) spellings are rejected by `validate`
    (dedicated heap-shape message), never modeled here. -/
def vecRealloc (v : Vec32) (m : Nat) : Result Vec32 :=
  if v.freed then .error .AssertFail
  else .ok ⟨v.val.take m ++ List.replicate (m - v.val.length) 0, false⟩

/-- Realloc on a freed block is rejected, never silently modeled. -/
theorem vecRealloc_freed (v : Vec32) (m : Nat)
    (h : v.freed = true) : vecRealloc v m = .error .AssertFail := by
  simp [vecRealloc, h]

/-- Realloc on a live block succeeds with the resized contents. -/
theorem vecRealloc_ok (v : Vec32) (m : Nat)
    (hlive : v.freed = false) :
    vecRealloc v m =
      .ok ⟨v.val.take m ++ List.replicate (m - v.val.length) 0, false⟩ := by
  simp [vecRealloc, hlive]

/-- Resizing delivers exactly the requested capacity. -/
theorem vecRealloc_length (v : Vec32) (m : Nat) (w : Vec32)
    (h : vecRealloc v m = .ok w) : w.val.length = m := by
  unfold vecRealloc at h
  split at h
  · next => simp at h
  · next =>
    cases h
    simp only [List.length_take, List.length_append, List.length_replicate]
    omega

/-- Resizing keeps the block live. -/
theorem vecRealloc_live (v : Vec32) (m : Nat) (w : Vec32)
    (h : vecRealloc v m = .ok w) : w.freed = false := by
  unfold vecRealloc at h
  split at h
  · next => simp at h
  · next => cases h; rfl

/-- List-level: resizing preserves reads below both lengths. -/
theorem take_append_replicate_get_preserve (l : List (BitVec 32))
    (m j : Nat) (hjlen : j < l.length) (hjm : j < m) :
    (l.take m ++ List.replicate (m - l.length) 0)[j]? = l[j]? := by
  induction l generalizing m j with
  | nil => simp at hjlen
  | cons y ys ih =>
    cases m with
    | zero => simp at hjm
    | succ m =>
      cases j with
      | zero => simp [List.take]
      | succ j =>
        simp only [List.take_succ_cons, List.length_cons, List.cons_append,
          List.getElem?_cons_succ, Nat.succ_sub_succ]
        exact ih m j (by simpa using hjlen) (by omega)

/-- List-level: growth reads back zero past the old length. -/
theorem take_append_replicate_get_zero (l : List (BitVec 32))
    (m j : Nat) (hjge : l.length ≤ j) (hjm : j < m) :
    (l.take m ++ List.replicate (m - l.length) 0)[j]? = some 0 := by
  induction l generalizing m j with
  | nil =>
    rw [List.take_nil]
    simp only [List.length, Nat.sub_zero, List.nil_append]
    rw [List.getElem?_replicate]
    simp [hjm]
  | cons y ys ih =>
    cases m with
    | zero => simp at hjm
    | succ m =>
      cases j with
      | zero => simp at hjge
      | succ j =>
        simp only [List.take_succ_cons, List.length_cons, List.cons_append,
          List.getElem?_cons_succ, Nat.succ_sub_succ]
        exact ih m j (by simpa using hjge) (by omega)

/-- Resizing preserves every element below both lengths. -/
theorem vecRealloc_preserve (v : Vec32) (m j : Nat) (y : BitVec 32)
    (w : Vec32) (hlt : j < m) (hget : vecGet v j = .ok y)
    (h : vecRealloc v m = .ok w) : vecGet w j = .ok y := by
  have hlive : v.freed = false := by
    cases hv : v.freed
    · rfl
    · unfold vecRealloc at h
      simp [hv] at h
  have hjlen : j < v.val.length := by
    rcases Nat.lt_or_ge j v.val.length with hj | hge
    · exact hj
    · have hnone : v.val[j]? = none := List.getElem?_eq_none hge
      have h2 : vecGet v j = .error .OOB := vecGet_oob v j hlive hnone
      rw [h2] at hget
      simp at hget
  have hget' : v.val[j]? = some y := by
    match hm : v.val[j]? with
    | some z =>
      have h2 : vecGet v j = .ok z := vecGet_ok v j z hlive hm
      have hzy : z = y := by
        rw [h2] at hget
        simpa using hget
      exact congrArg some hzy
    | none =>
      have h2 : vecGet v j = .error .OOB := vecGet_oob v j hlive hm
      rw [h2] at hget
      simp at hget
  have hw : w = ⟨v.val.take m ++ List.replicate (m - v.val.length) 0, false⟩ := by
    rw [vecRealloc_ok v m hlive] at h
    cases h
    rfl
  subst hw
  rw [vecGet_ok _ _ _ rfl (by
    show (v.val.take m ++ List.replicate (m - v.val.length) 0)[j]? = some y
    rw [take_append_replicate_get_preserve _ _ _ hjlen hlt]
    exact hget')]

/-- Growth reads back zero past the old length. -/
theorem vecRealloc_get_zero (v : Vec32) (m j : Nat) (w : Vec32)
    (hle : v.val.length ≤ j) (hlt : j < m)
    (h : vecRealloc v m = .ok w) : vecGet w j = .ok 0 := by
  have hlive : v.freed = false := by
    cases hv : v.freed
    · rfl
    · unfold vecRealloc at h
      simp [hv] at h
  have hw : w = ⟨v.val.take m ++ List.replicate (m - v.val.length) 0, false⟩ := by
    rw [vecRealloc_ok v m hlive] at h
    cases h
    rfl
  subst hw
  rw [vecGet_ok _ _ _ rfl (by
    show (v.val.take m ++ List.replicate (m - v.val.length) 0)[j]? = some 0
    exact take_append_replicate_get_zero _ _ _ hle hlt)]

/-- Fill on a live capacity-`(k+r)` block always succeeds (generalizes
    `vecFillLoopAux_fresh_ok` beyond fresh blocks; M1c extension fills run
    on `realloc` outputs). -/
theorem vecFillLoopAux_live_ok (v : Vec32) (k r : Nat)
    (hlive : v.freed = false) (hlen : v.val.length = k + r) :
    ∃ w, vecFillLoopAux v k r = .ok w := by
  induction r generalizing v k with
  | zero => exact ⟨v, rfl⟩
  | succ r ih =>
    have hk : k < v.val.length := by omega
    have hs : vecSet v k (BitVec.ofNat 32 k) =
        .ok ⟨v.val.set k (BitVec.ofNat 32 k), false⟩ :=
      vecSet_ok v k _ hlive hk
    unfold vecFillLoopAux
    rw [hs]
    simp only
    have hlen' : (v.val.set k (BitVec.ofNat 32 k)).length = (k + 1) + r := by
      rw [List.length_set]
      omega
    exact ih _ _ (vecSet_live v k _ _ hs) hlen'

/-- Whole heap program, purely: allocate `n`, fill `[0, n)` with indices,
    `realloc` to `n + n` (prefix preserved), fill the extension `[n, n+n)`
    with indices, sum `[0, n+n)`, free. `free` is value-invisible
    (contents kept, token set); leak is forgetting a value, sound here
    (M1d: `validate` admits `free <= expected`, gating only double-`free`). -/
def vecReallocFillSumU32 (n : Nat) : Result (BitVec 32) :=
  match vecNew n with
  | .error e => .error e
  | .ok v0 =>
    match vecFillLoop v0 n with
    | .error e => .error e
    | .ok v1 =>
      match vecRealloc v1 (n + n) with
      | .error e => .error e
      | .ok v2 =>
        match vecFillLoopAux v2 n n with
        | .error e => .error e
        | .ok v3 =>
          match vecSumLoop v3 (n + n) with
          | .error e => .error e
          | .ok s =>
            match vecFree v3 with
            | .error e => .error e
            | .ok _ => .ok s

/-- Bulk word copy (`memmove` fused, N4d-iv-b1 `__relocate_a_1`): copy
    `n` words from `src` at `soff` to `dst` at `doff`. Reads go
    through the `vgrowAt` discipline (`freeS` is the source token:
    consumed source is `AssertFail`; `soff` at or past `lenS` is `OOB`,
    as is a short source list); writes go through `vecSet` (consumed
    or short destination propagates its error). Read-then-write per
    step, so overlapping ranges copy correctly. -/
def stdVecBlitFold (src : List (BitVec 32)) (lenS : Nat) (freeS : Bool)
    (dst : Vec32) (doff soff n : Nat) : Result Vec32 :=
  match n with
  | 0 => .ok dst
  | k + 1 =>
    if freeS then .error .AssertFail
    else if soff < lenS then
      match src[soff]? with
      | none => .error .OOB
      | some x =>
        match vecSet dst doff x with
        | .error e => .error e
        | .ok dst' =>
          stdVecBlitFold src lenS freeS dst' (doff + 1) (soff + 1) k
    else .error .OOB

/-- Whole-program bridge: allocate/fill/realloc/fill-extension/sum/free
    equals the `range (n + n)` prefix sum (the spec world). -/
theorem vecReallocFillSumU32_correct (n : Nat) :
    vecReallocFillSumU32 n =
      .ok (prefixSumU32 ((List.range (n + n)).map (BitVec.ofNat 32)) (n + n)) := by
  have hfill := vecFillLoopAux_fresh_ok (List.replicate n 0) 0 n (by simp)
  obtain ⟨w1, hw1⟩ := hfill
  have hlive1 : w1.freed = false :=
    vecFillLoopAux_live _ _ _ _ rfl hw1
  have hlenFresh : (⟨List.replicate n 0, false⟩ : Vec32).val.length = 0 + n := by
    simp
  have hget1 : ∀ j, 0 ≤ j → j < 0 + n →
      vecGet w1 j = .ok (BitVec.ofNat 32 j) :=
    fun j hjlo hjhi => vecFillLoopAux_get _ 0 n _ rfl hlenFresh
      hw1 j hjlo hjhi
  have hlen1 : w1.val.length = n := by
    have h := vecFillLoopAux_length _ _ _ _ hw1
    simp at h
    exact h
  obtain ⟨w2, hw2⟩ : ∃ w, vecRealloc w1 (n + n) = .ok w :=
    ⟨_, vecRealloc_ok w1 (n + n) hlive1⟩
  have hlive2 : w2.freed = false := vecRealloc_live w1 (n + n) w2 hw2
  have hlen2 : w2.val.length = n + n := vecRealloc_length w1 (n + n) w2 hw2
  have hget2 : ∀ j, j < n → vecGet w2 j = .ok (BitVec.ofNat 32 j) := by
    intro j hj
    exact vecRealloc_preserve w1 (n + n) j _ w2 (by omega)
      (hget1 j (Nat.zero_le _) (by omega)) hw2
  obtain ⟨w3, hw3⟩ := vecFillLoopAux_live_ok w2 n n hlive2 hlen2
  have hlive3 : w3.freed = false :=
    vecFillLoopAux_live _ _ _ _ hlive2 hw3
  have hget3 : ∀ j, 0 ≤ j → j < n + n →
      vecGet w3 j = .ok (BitVec.ofNat 32 j) := by
    intro j hjlo hjhi
    rcases Nat.lt_or_ge j n with hj | hj
    · have hhere := hget2 j hj
      exact vecFillLoopAux_preserve _ n n j _ w3 hj hhere hw3
    · exact vecFillLoopAux_get _ n n _ hlive2 hlen2
        hw3 j hj hjhi
  have hsum := vecSumLoopAux_correct w3 0 (n + n) 0 (by
    intro j hjlo hjhi
    exact hget3 j hjlo (by omega))
  have hrange : List.range' 0 (n + n) = List.range (n + n) := by
    simp [List.range_eq_range']
  rw [hrange] at hsum
  have h0 : (0 : BitVec 32) + prefixSumU32 ((List.range (n + n)).map
      (BitVec.ofNat 32)) (n + n)
      = prefixSumU32 ((List.range (n + n)).map (BitVec.ofNat 32)) (n + n) :=
    BitVec.zero_add _
  rw [h0] at hsum
  have hfree : vecFree w3 = .ok ⟨w3.val, true⟩ := vecFree_ok w3 hlive3
  simp only [vecReallocFillSumU32, vecNew_ok, vecFillLoop, hw1, hw2, hw3] at *
  simp only [vecSumLoop] at hsum ⊢
  rw [hsum]
  simp only
  rw [hfree]
