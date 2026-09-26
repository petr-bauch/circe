/-
Circe.Specs — Phase 5 functional-correctness specs (user workflow).

Pattern (à la Aeneas): pure equations over emitted code — no memory
model, no separation logic, no framing lemmas. Each section states the
spec against `Circe.Base` operations, which are *literally the bodies*
of the emitted definitions in `out/*.lean`:

- `out/Incr.lean`:      `incr_fwd p := checkedIncrI32 p`
- `out/Choose.lean`:    `choose_fwd b x y := .ok (if b then x else y)`
- `out/Choose.lean`:    `choose_back b x y ret := .ok (if b then (ret, y) else (x, ret))`
- `out/SumArray.lean`:  `sum_array_fwd a := .ok (prefixSumU32 a.val a.val.length)`

Body identity is machine-checked: `tests/golden/*.lean` pin the bytes
(`native_decide` linkage in `Circe.Emit`, `diff` in
`tools/check-phase4.sh`), so every theorem below transfers verbatim to
the emitted files. The required three (§8 DoD item 2) are `incr_correct`,
`choose_lens_laws`, and `sum_correct`; surrounding lemmas package the
ok/err sides. `cir_simp` (`Circe.Tactics`) is used throughout.
-/
import Circe.Base
import Circe.Emit
import Circe.Tactics

/-! ## `incr`: mathematical successor spec -/

/-- Success delivers the wrapped successor and certifies no overflow. -/
theorem incr_spec_ok (p r : BitVec 32)
    (h : checkedIncrI32 p = .ok r) :
    r = p + 1 ∧ inInt32Range (p.toInt + 1) = true := by
  simp only [checkedIncrI32, checkedAddI32] at h
  split at h
  · next hc => simp at h; exact ⟨h.symm, hc⟩
  · next => simp at h

/-- Overflow reports exactly the out-of-range case. -/
theorem incr_spec_err (p : BitVec 32)
    (h : checkedIncrI32 p = .error .Overflow) :
    inInt32Range (p.toInt + 1) = false := by
  simp only [checkedIncrI32, checkedAddI32] at h
  split at h
  · next => simp at h
  -- `h` mentions `(1 : BitVec 32).toInt`; simprocs evaluate it to `1`.
  · next hc => simpa using hc

/-- Functional correctness for `incr` (DoD theorem 1 of 3): on success the
    result is the mathematical successor (`r = p + 1` with the `nsw` range
    certificate); on overflow the input was genuinely out of range.
    Applies verbatim to `out/Incr.lean:incr_fwd` (body-identical). -/
theorem incr_correct (p : BitVec 32) :
    (∀ r, checkedIncrI32 p = .ok r →
      r = p + 1 ∧ inInt32Range (p.toInt + 1) = true) ∧
    (checkedIncrI32 p = .error .Overflow →
      inInt32Range (p.toInt + 1) = false) :=
  ⟨fun r h => incr_spec_ok p r h, fun h => incr_spec_err p h⟩

/-! ## `choose`: lens laws over plain bitvectors -/

/-- BitVec mirror of the emitted `choose_fwd` body (tags stripped).
    `out/Choose.lean` defines exactly `.ok (if b then x else y)`. -/
def chooseFwdBV (b : Bool) (x y : BitVec 32) : BitVec 32 :=
  if b then x else y

/-- BitVec mirror of the emitted `choose_back` body (tags stripped).
    `out/Choose.lean` defines exactly `.ok (if b then (ret, y) else (x, ret))`. -/
def chooseBackBV (b : Bool) (x y ret : BitVec 32) : BitVec 32 × BitVec 32 :=
  if b then (ret, y) else (x, ret)

/-- The mirror agrees with the verified forward function up to tags. -/
theorem chooseFwdBV_agrees (b : Bool) (x y : BitVec 32) :
    chooseFwd b x y = .ok (.i32 (chooseFwdBV b x y)) := rfl

/-- The mirror agrees with the verified backward function up to tags. -/
theorem chooseBackBV_agrees (b : Bool) (x y ret : BitVec 32) :
    chooseBack b x y ret =
      .ok ((.i32 (chooseBackBV b x y ret).1, .i32 (chooseBackBV b x y ret).2)) := by
  cases b <;> rfl

/-- Lens laws for `choose` (DoD theorem 2 of 3): get-put (writing back the
    selected value is the identity) and put-get (selecting after an update
    yields the update). Pure bitvector equations — the user never sees
    loans, regions, or tags. -/
theorem choose_lens_laws (b : Bool) (x y r : BitVec 32) :
    chooseBackBV b x y (chooseFwdBV b x y) = (x, y) ∧
    chooseFwdBV b (chooseBackBV b x y r).1 (chooseBackBV b x y r).2 = r := by
  cases b <;> exact ⟨rfl, rfl⟩

/-! ## `sum_array`: prefix sum is `List.sum` of the taken prefix -/

/-- Functional correctness for `sum_array` (DoD theorem 3 of 3): in-range
    lengths deliver the `List.sum` of the taken prefix (wrapping `u32`
    arithmetic is exactly `BitVec` addition, so no overflow side condition).
    Applies verbatim to `out/SumArray.lean:sum_array_fwd` via
    `prefixSumU32_full` below. -/
theorem sum_correct (l : List (BitVec 32)) (n : BitVec 32)
    (h : n.toNat ≤ l.length) :
    sumFwd l n = .ok (.u32 ((l.take n.toNat).sum)) := by
  rw [sumFwd_ok l n h, prefixSumU32_take_sum]

/-- Full-length corollary: summing the whole array is `List.sum`. This is
    exactly the emitted `sum_array_fwd` body on a `BoundedList`. -/
theorem sum_correct_full {n : Nat} (a : BoundedList (BitVec 32) n) :
    prefixSumU32 a.val a.val.length = a.val.sum := by
  cir_simp

/-- The empty array sums to zero (closed by `cir_simp` alone). -/
theorem sum_empty : prefixSumU32 [] 0 = (0 : BitVec 32) := by
  cir_simp

/-- Over-long lengths stay loud: the spec-level `OOB` agrees with `sumFwd`. -/
theorem sum_correct_oob (l : List (BitVec 32)) (n : BitVec 32)
    (h : ¬ n.toNat ≤ l.length) :
    sumFwd l n = .error .OOB :=
  sumFwd_oob l n h
