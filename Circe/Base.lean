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
