/-
Circe.Emit.SumFwd — summation translations (value level).

Canonical home of the wrapping prefix-sum definitions the sum goldens
render and the `DiffSum` fuzzers execute: `prefixSumU32` (with its
take-sum bridge lemmas) and the `u64` mirror `prefixSumU64`. Names are
unchanged from their former `Circe.Base` home; only the address moved.
Proofs of the emitted entries (`emit_correct_sum`, `memTransfer_sum`,
user specs in `Circe.Specs`, and the heap whole-program bridges in
`Circe.Emit.VecFwd`) stay in their modules and import this module.
-/
import Circe.Base

/-! ## Wrapping prefix sum (, u32) -/

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
/-! ## Wrapping prefix sum (u64 mirror) -/

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
