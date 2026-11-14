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
- `out/VecAlloc.lean`:  `vec_alloc_fwd n := vecFillSumU32 n.toNat`

Body identity is machine-checked: `tests/golden/*.lean` pin the bytes
(`native_decide` linkage in `Circe.Emit`, `diff` in
`tools/check.sh`), so every theorem below transfers verbatim to
the emitted files. The required three (§8 DoD item 2) are `incr_correct`,
`choose_lens_laws`, and `sum_correct`; Phase 7 adds the heap spec
`vec_correct` (+ `vec_empty`); surrounding lemmas package the
ok/err sides. `cir_simp` (`Circe.Tactics`) is used throughout.
-/
import Circe.Base
import Circe.Emit
import Circe.Emit.VecCopyIf
import Circe.Emit.VecMismatch
import Circe.Emit.VecIntersect
import Circe.Emit.VecUnion
import Circe.Emit.VecDifference
import Circe.Emit.VecPartialSum
import Circe.Emit.VecUnique
import Circe.Emit.VecUniqueCopy
import Circe.Emit.VecReverseCopy
import Circe.Emit.VecPartitionCopy
import Circe.Tactics
import Circe.Lemmas.TwoCursor

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

/-! ## `sum_two`: pairwise sum is the sum of the two prefix sums -/

/-- Functional correctness for `sum_two` (two-reader admission): an
    in-range length delivers the pairwise wrapping sum, which is the
    sum of the two prefix sums (so `List.sum` lemmas apply via
    `prefixSumU32_take_sum`). Applies verbatim to
    `out/SumTwo.lean:sum_two_fwd`. -/
theorem sum_two_correct (l₁ l₂ : List (BitVec 32)) (n : BitVec 32)
    (h₁ : n.toNat ≤ l₁.length) (h₂ : n.toNat ≤ l₂.length) :
    sumTwoFwd l₁ l₂ n =
      .ok (.u32 (prefixSumU32 l₁ n.toNat + prefixSumU32 l₂ n.toNat)) := by
  rw [sumTwoFwd_ok l₁ l₂ n ⟨h₁, h₂⟩, pairSum_distrib l₁ l₂ n.toNat h₁ h₂]

/-- Aliased readers (`a == b`) read identically through either pin —
    the value-soundness claim the N2a discipline rests on, at the
    spec level. -/
theorem sum_two_aliased (l : List (BitVec 32)) (n : BitVec 32)
    (h : n.toNat ≤ l.length) :
    sumTwoFwd l l n =
      .ok (.u32 (prefixSumU32 l n.toNat + prefixSumU32 l n.toNat)) :=
  sum_two_correct l l n h h

/-- Over-long lengths stay loud past either array. -/
theorem sum_two_correct_oob (l₁ l₂ : List (BitVec 32)) (n : BitVec 32)
    (h : ¬ (n.toNat ≤ l₁.length ∧ n.toNat ≤ l₂.length)) :
    sumTwoFwd l₁ l₂ n = .error .OOB :=
  sumTwoFwd_oob l₁ l₂ n h

/-! ## `vec_alloc`: index-sum is `List.sum` of the filled range -/

/-- Functional correctness for `vec_alloc` (Phase 7 heap spec): the pure
    heap program delivers the `List.sum` of indices `[0, n)` (wrapping
    `u32` arithmetic is exactly `BitVec` addition). Applies verbatim to
    `out/VecAlloc.lean:vec_alloc_fwd` (body-identical:
    `vecFillSumU32 n.toNat`). S4: stated via the grown `cir_simp` set
    (`vecFillSumU32_correct` + `prefixSumU32_take_sum` fire
    automatically; only the take-length fact is manual). -/
theorem vec_correct (n : Nat) :
    vecFillSumU32 n = .ok (((List.range n).map (BitVec.ofNat 32)).sum) := by
  have hlen : ((List.range n).map (BitVec.ofNat 32)).length = n := by simp
  have htake : ((List.range n).map (BitVec.ofNat 32)).take n =
      (List.range n).map (BitVec.ofNat 32) := by
    have h2 := List.take_length (l := (List.range n).map (BitVec.ofNat 32))
    rwa [hlen] at h2
  cir_simp
  rw [htake]

/-- The empty heap program sums to zero. -/
theorem vec_empty : vecFillSumU32 0 = .ok 0 := by
  rw [vec_correct]
  simp

/-! ## `vec_realloc`: grown index-sum is `List.sum` of the doubled range (M1c) -/

/-- Functional correctness for `vec_realloc` (M1c heap spec): the pure
    grown-heap program delivers the `List.sum` of indices `[0, n + n)`
    (wrapping `u32` arithmetic is exactly `BitVec` addition). Applies
    verbatim to `out/VecRealloc.lean:vec_realloc_fwd` (body-identical:
    `vecReallocFillSumU32 n.toNat`). S4: stated via the grown `cir_simp`
    set (`vecReallocFillSumU32_correct` + `prefixSumU32_take_sum` fire
    automatically; only the take-length fact is manual). -/
theorem vecRealloc_correct (n : Nat) :
    vecReallocFillSumU32 n =
      .ok (((List.range (n + n)).map (BitVec.ofNat 32)).sum) := by
  have hlen : ((List.range (n + n)).map (BitVec.ofNat 32)).length = n + n := by
    simp
  have htake : ((List.range (n + n)).map (BitVec.ofNat 32)).take (n + n) =
      (List.range (n + n)).map (BitVec.ofNat 32) := by
    have h2 := List.take_length
      (l := (List.range (n + n)).map (BitVec.ofNat 32))
    rwa [hlen] at h2
  cir_simp
  rw [htake]

/-- The empty grown-heap program sums to zero. -/
theorem vecRealloc_empty : vecReallocFillSumU32 0 = .ok 0 := by
  cir_simp

/-! ## `vec_alloc_u64`: index-sum is `List.sum` of the filled range (M1b) -/

/-- Functional correctness for `vec_alloc_u64` (M1b heap spec): the pure
    `u64` heap program delivers the `List.sum` of indices `[0, n)`
    (wrapping `u64` arithmetic is exactly `BitVec` addition). Applies
    verbatim to `out/VecAllocU64.lean:vec_alloc_u64_fwd` (body-identical:
    `vecFillSumU64 n.toNat`). -/
theorem vec64_correct (n : Nat) :
    vecFillSumU64 n = .ok (((List.range n).map (BitVec.ofNat 64)).sum) := by
  have hlen : ((List.range n).map (BitVec.ofNat 64)).length = n := by simp
  have htake : ((List.range n).map (BitVec.ofNat 64)).take n =
      (List.range n).map (BitVec.ofNat 64) := by
    have h2 := List.take_length (l := (List.range n).map (BitVec.ofNat 64))
    rwa [hlen] at h2
  cir_simp
  rw [htake]

/-- The empty `u64` heap program sums to zero. -/
theorem vec64_empty : vecFillSumU64 0 = .ok 0 := by
  cir_simp

/-! ## `add_caller` / `sum_caller`: calls compose (S1, N3a) -/

/-- `add_caller` threads two checked adds: success delivers the
    sequential sum (`cir_simp` closes the `(<$>)` residue via the set's
    map lemmas). Template instance: sequential threading (see
    VERIFYING.md Contracts). -/
theorem addCaller_correct_ok (x y z t r : BitVec 32)
    (h1 : checkedAddI32 x y = .ok t) (h2 : checkedAddI32 t z = .ok r) :
    addCallerFwd x y z = .ok (.i32 r) := by
  simp only [addCallerFwd, h1, h2] <;> cir_simp

/-- First-add failure propagates (and determines the error).
    Template instance: sequential threading, err leg (see
    VERIFYING.md Contracts). -/
theorem addCaller_correct_err (x y z : BitVec 32) (e : Panic)
    (h : checkedAddI32 x y = .error e) :
    addCallerFwd x y z = .error e := by
  simp only [addCallerFwd, h] <;> cir_simp

/-- `sum_caller` delegates: in-range lengths deliver the taken-prefix
    sum (`cir_simp` discharges the delegation rewrite — the spec —
    leaving exactly `sum_correct`). Template instance: delegation
    (see VERIFYING.md Contracts). -/
theorem sumCaller_correct (l : List (BitVec 32)) (n : BitVec 32)
    (h : n.toNat ≤ l.length) :
    sumCallerFwd l n = .ok (.u32 ((l.take n.toNat).sum)) := by
  cir_simp
  exact sum_correct l n h

/-! ## `translate`: the point moves (S2, N3a) -/

/-- Functional correctness for `translate`, packaged `incr`-style: the
    ok/err bridges (`translateFwd_ok_bridge`, `translateFwd_err_x`) are
    already the complete properties, so the spec conjoins them
    (conditional bridges apply by `exact` — they provably do not fire
    under `simp`; cf. `accAddFwd_ok` usage in `Circe.Emit.Acc`).
    Template instance: conjunction (see VERIFYING.md Contracts). -/
theorem translate_correct (px py dx dy : BitVec 32) :
    (∀ x' y', checkedAddI32 px dx = .ok x' →
      checkedAddI32 py dy = .ok y' →
      translateFwd px py dx dy =
        .ok (.structVal "Point" [("x", x'), ("y", y')])) ∧
    (∀ e, checkedAddI32 px dx = .error e →
      translateFwd px py dx dy = .error e) :=
  ⟨fun x' y' hx hy => translateFwd_ok_bridge _ _ _ _ x' y' hx hy,
   fun e h => translateFwd_err_x _ _ _ _ e h⟩

/-! ## `nested_sum` / `skip_sum`: loop folds deliver the models (S3a, N3a) -/

/-- `nested_sum` delivers the row-sum total (value model). -/
theorem nested_correct (n m : BitVec 32) :
    nestedFwd n m = .ok (.u32 (nestedSumU32 n.toNat m.toNat)) := by
  cir_simp

/-- The empty outer range sums to zero. -/
theorem nested_empty (m : Nat) : nestedSumU32 0 m = 0 := by
  cir_simp

/-- Evaluated double sum (`0 + (0 + 1 + 2) = 3`): pins the `i * j`
    row semantics beyond the equation form. -/
theorem nested_two_three : nestedSumU32 2 3 = BitVec.ofNat 32 3 := by
  cir_simp <;> decide

/-- `skip_sum` caps at `8`: longer bounds change nothing. -/
theorem skip_cap (n : Nat) : skipSumU32 (8 + n) = skipSumU32 8 := by
  have h : min (8 + n) 8 = 8 := Nat.min_eq_right (Nat.le_add_right 8 n)
  cir_simp <;> simp [skipSumU32, h]

/-- Evaluated edge (`[0, 1, 2]` minus `2` sums to `1`). -/
theorem skip_three : skipSumU32 3 = 1 := by
  cir_simp <;> decide

/-! ## `find_eq`: hit, miss, and OOB (S3a, N3a) -/

/-- Hit: the first match index is delivered (kernel computation;
    `decide` is unavailable here — `Panic` has no `DecidableEq` — so
    `rfl` evaluates the unfolded model). -/
theorem findEq_hit : findEqOut [7, 8, 9] 3 8 = .ok (BitVec.ofNat 32 1) := by
  cir_simp <;> rfl

/-- Miss: no match returns the bound. -/
theorem findEq_miss : findEqOut [7, 8, 9] 3 5 = .ok (BitVec.ofNat 32 3) := by
  cir_simp <;> rfl

/-- Over-long bound with no hit stays loud. -/
theorem findEq_oob : findEqOut [7] 2 5 = .error .OOB := by
  cir_simp <;> rfl

/-! ## `cls`: the dispatch table (S3a, N3a) -/

/-- `cls` dispatches exhaustively: every input hits exactly one arm and
    always succeeds (no silent default, no error case). -/
theorem cls_correct (x : BitVec 32) :
    clsFwd x =
      .ok (.u32 (if x == 0 then 10 else if x == 1 then 20 else 30)) := by
  by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;> cir_simp <;> simp_all

/-! ## `cls_fall` / `cls_dense`: fallthrough + dense switches (N6b-i, N3a) -/

/-- `cls_fall` dispatches exhaustively: `0` falls through to the `1`
    arm, so both answer `10`. -/
theorem clsFall_correct (x : BitVec 32) :
    clsFallFwd x =
      .ok (.u32 (if x == 0 then 10 else if x == 1 then 10 else 30)) := by
  by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;> cir_simp <;> simp_all

/-- `cls_dense` dispatches exhaustively over all eight cases. -/
theorem clsDense_correct (x : BitVec 32) :
    clsDenseFwd x =
      .ok (.u32 (if x == 0 then 0 else if x == 1 then 10 else if x == 2 then 20
        else if x == 3 then 30 else if x == 4 then 40 else if x == 5 then 50
        else if x == 6 then 60 else if x == 7 then 70 else 80)) := by
  by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;> by_cases h2 : x = 2 <;>
    by_cases h3 : x = 3 <;> by_cases h4 : x = 4 <;> by_cases h5 : x = 5 <;>
    by_cases h6 : x = 6 <;> by_cases h7 : x = 7 <;> cir_simp <;> simp_all

/-! ## `cls_break`: guarded stores over the initializer (N6b-ii, N3a) -/

/-- `cls_break` dispatches exhaustively: both cases store their const,
    unmatched scrutinees keep the `99` initializer. -/
theorem clsBreak_correct (x : BitVec 32) :
    clsBreakFwd x =
      .ok (.u32 (if x == 0 then 10 else if x == 1 then 20 else 99)) := by
  by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;> cir_simp <;> simp_all

/-! ## `cls_add`: compute cases over the operand (N6b-iii, N3a) -/

/-- `cls_add` dispatches exhaustively: the compute cases answer
    `y + 1` / `y + 2` (wrapping), `default` answers `y`. -/
theorem clsAdd_correct (x y : BitVec 32) :
    clsAddFwd x y =
      .ok (.u32 (if x == 0 then y + 1 else if x == 1 then y + 2 else y)) := by
  by_cases h0 : x = 0 <;> by_cases h1 : x = 1 <;> cir_simp <;> simp_all

/-! ## `add64` / `addu64`: 64-bit addition (S3b, N3a) -/

/-- `add64` success delivers the mathematical sum with the `nsw`
    certificate, mirroring `incr_correct`. -/
theorem add64_correct_ok (a b r : BitVec 64)
    (h : checkedAddI64 a b = .ok r) :
    add64Fwd a b = .ok (.i64 r) := by
  simp only [add64Fwd, h] <;> cir_simp

/-- `add64` overflow reports exactly the out-of-range case. -/
theorem add64_correct_err (a b : BitVec 64) (e : Panic)
    (h : checkedAddI64 a b = .error e) :
    add64Fwd a b = .error e := by
  simp only [add64Fwd, h] <;> cir_simp

/-- `addu64` wraps unconditionally (unsigned arithmetic: no UB). -/
theorem addu64_correct (a b : BitVec 64) :
    addu64Fwd a b = .ok (.u64 (a + b)) := by
  cir_simp

/-! ## `neg` / `sdiv`: signed negation + division (N6a) -/

/-- `neg` success delivers the mathematical negation (`INT_MIN` fails). -/
theorem neg_correct_ok (x r : BitVec 32)
    (h : checkedNegI32 x = .ok r) :
    negFwd x = .ok (.i32 r) := by
  simp only [negFwd, h] <;> cir_simp

/-- `neg` overflow reports exactly the `INT_MIN` case. -/
theorem neg_correct_err (x : BitVec 32) (e : Panic)
    (h : checkedNegI32 x = .error e) :
    negFwd x = .error e := by
  simp only [negFwd, h] <;> cir_simp

/-- `sdiv` success delivers the truncating quotient. -/
theorem sdiv_correct_ok (a b r : BitVec 32)
    (h : checkedDivI32 a b = .ok r) :
    sdivFwd a b = .ok (.i32 r) := by
  simp only [sdivFwd, h] <;> cir_simp

/-- Division by zero reports `DivZero`. -/
theorem sdiv_correct_zero (a b : BitVec 32)
    (h : checkedDivI32 a b = .error .DivZero) :
    sdivFwd a b = .error .DivZero := by
  simp only [sdivFwd, h] <;> cir_simp

/-- `INT_MIN / -1` reports `Overflow`. -/
theorem sdiv_correct_overflow (a b : BitVec 32)
    (h : checkedDivI32 a b = .error .Overflow) :
    sdivFwd a b = .error .Overflow := by
  simp only [sdivFwd, h] <;> cir_simp

/-! ## `xor_u32` / `and_u32` / `or_u32` / `shl_u32` / `shr_u32`:
    total `u32` bitwise + checked shifts (K1) -/

/-- `xor_u32` delivers the bitwise xor (total — no UB in C). -/
theorem xorU32_correct (a b : BitVec 32) :
    xorU32Fwd a b = .ok (.u32 (a ^^^ b)) := rfl

/-- `and_u32` delivers the bitwise and (total). -/
theorem andU32_correct (a b : BitVec 32) :
    andU32Fwd a b = .ok (.u32 (a &&& b)) := rfl

/-- `or_u32` delivers the bitwise or (total). -/
theorem orU32_correct (a b : BitVec 32) :
    orU32Fwd a b = .ok (.u32 (a ||| b)) := rfl

/-- `shl_u32` success delivers the shifted word. -/
theorem shlU32_correct_ok (a b r : BitVec 32)
    (h : checkedShiftU32 a b (· <<< ·) = .ok r) :
    shlU32Fwd a b = .ok (.u32 r) := by
  unfold shlU32Fwd
  rw [h]
  rfl

/-- `shl_u32` failure is exactly the `OOB` amount case. -/
theorem shlU32_correct_err (a b : BitVec 32) (e : Panic)
    (h : checkedShiftU32 a b (· <<< ·) = .error e) :
    shlU32Fwd a b = .error e := by
  unfold shlU32Fwd
  rw [h]
  rfl

/-- `shr_u32` success delivers the shifted word. -/
theorem shrU32_correct_ok (a b r : BitVec 32)
    (h : checkedShiftU32 a b (· >>> ·) = .ok r) :
    shrU32Fwd a b = .ok (.u32 r) := by
  unfold shrU32Fwd
  rw [h]
  rfl

/-- `shr_u32` failure is exactly the `OOB` amount case. -/
theorem shrU32_correct_err (a b : BitVec 32) (e : Panic)
    (h : checkedShiftU32 a b (· >>> ·) = .error e) :
    shrU32Fwd a b = .error e := by
  unfold shrU32Fwd
  rw [h]
  rfl

/-! ## `sum_norestrict`: same body, same theorem (N2c, N3a) -/

/-- `sum_norestrict` shares the `sum_array` body exactly (N2c recovers
    admission, never semantics): full-length sum is `List.sum`, via the
    same `cir_simp` close as `sum_correct_full`. -/
theorem sumNorestrict_correct_full {n : Nat} (a : BoundedList (BitVec 32) n) :
    prefixSumU32 a.val a.val.length = a.val.sum := by
  cir_simp

/-! ## `method_sum` / `point_sum_ref`: POD const-method (M2a, N3a) -/

/-- `method_sum` delivers the checked field sum, mirroring
    `add64_correct_ok` (`simp only` exposes the `(<$>)` residue for
    `cir_simp`). -/
theorem methodSum_correct_ok (px py s : BitVec 32)
    (h : checkedAddI32 px py = .ok s) :
    methodSumFwd px py = .ok (.i32 s) := by
  simp only [methodSumFwd, h] <;> cir_simp

/-- Field-add failure propagates out of the method leaf. -/
theorem methodSum_correct_err (px py : BitVec 32) (e : Panic)
    (h : checkedAddI32 px py = .error e) :
    methodSumFwd px py = .error e := by
  simp only [methodSumFwd, h] <;> cir_simp

/-- `point_sum_ref` delegates: the entry is the method leaf (via
    `pointSumRefFwd_is_call`; the delegation rewrite is the spec, as in
    `sumCaller_correct`). -/
theorem pointSumRef_correct (px py : BitVec 32) :
    pointSumRefFwd px py = methodSumFwd px py := by
  cir_simp

/-! ## `Acc`: ctor, add, get, dtor, and the two-add sequence (M2b, N3a) -/

/-- The ctor leaf delivers the field-init (`0`). -/
theorem accCtor_correct : accCtorFwd = .ok (.i32 0) := by
  cir_simp

/-- `add` threads one checked add, mirroring `add64_correct_ok`. -/
theorem accAdd_correct_ok (s v r : BitVec 32)
    (h : checkedAddI32 s v = .ok r) :
    accAddFwd s v = .ok (.i32 r) := by
  simp only [accAddFwd, h] <;> cir_simp

/-- A failing `add` propagates (and determines the error). -/
theorem accAdd_correct_err (s v : BitVec 32) (e : Panic)
    (h : checkedAddI32 s v = .error e) :
    accAddFwd s v = .error e := by
  simp only [accAddFwd, h] <;> cir_simp

/-- The const getter is the identity. -/
theorem accGet_correct (s : BitVec 32) : accGetFwd s = .ok (.i32 s) := by
  cir_simp

/-- The trivial dtor is a no-op identity. -/
theorem accDtor_correct (t : BitVec 32) : accDtorFwd t = .ok (.i32 t) := by
  cir_simp

/-- `acc_two` sequences ctor-init, two checked adds, and get: success
    delivers the second sum (the per-leaf transfers composed at the
    value model — the only multi-call lifecycle proof). -/
theorem accTwo_correct_ok (a b s1 s2 : BitVec 32)
    (h1 : checkedAddI32 0 a = .ok s1)
    (h2 : checkedAddI32 s1 b = .ok s2) :
    accTwoFwd a b = .ok (.i32 s2) := by
  simp only [accTwoFwd_is_accTwo, accTwo, h1, h2] <;> cir_simp

/-- First-add failure aborts the sequence (and determines the error). -/
theorem accTwo_correct_err (a b : BitVec 32) (e : Panic)
    (h1 : checkedAddI32 0 a = .error e) :
    accTwoFwd a b = .error e := by
  simp only [accTwoFwd_is_accTwo, accTwo, h1] <;> cir_simp

/-! ## `box_through`: the box passes through (M2c, N3a) -/

/-- `box_through` is the identity on the boxed word (via the existing
    `boxThrough_ok`; `new` → read → `delete` corrupts nothing). -/
theorem boxThrough_correct (x : BitVec 32) :
    boxThroughFwd x = .ok (.i32 x) := by
  cir_simp

/-! ## N4a: overloads + namespaces (one property per new shape) -/

/-- The 3-`i32` overload leaf threads both adds, mirroring
    `add64_correct_ok` (`simp only` exposes the `(<$>)` residue for
    `cir_simp`). Template instance: sequential threading (see
    VERIFYING.md Contracts). -/
theorem add3_correct_ok (x y z t r : BitVec 32)
    (h1 : checkedAddI32 x y = .ok t)
    (h2 : checkedAddI32 t z = .ok r) :
    add3Fwd x y z = .ok (.i32 r) := by
  simp only [add3Fwd, h1, h2] <;> cir_simp

/-- First-add failure propagates out of the overload leaf.
    Template instance: sequential threading, err leg (see
    VERIFYING.md Contracts). -/
theorem add3_correct_err (x y z : BitVec 32) (e : Panic)
    (h : checkedAddI32 x y = .error e) :
    add3Fwd x y z = .error e := by
  simp only [add3Fwd, h] <;> cir_simp

/-- `use_add` delegates: the entry is the resolved overload body (via
    `useAddFwd_is_call`; the delegation rewrite is the spec, as in
    `pointSumRef_correct`). -/
theorem useAdd_correct (x y : BitVec 32) :
    useAddFwd x y = addFwd x y := by
  cir_simp

/-- `use_ns_add` delegates: the entry is the namespaced leaf body. -/
theorem useNsAdd_correct (x y : BitVec 32) :
    useNsAddFwd x y = addFwd x y := by
  cir_simp

/-! ## N4c: template instantiations (one property per new shape) -/

/-- `use_tadd32` delegates: the entry is the 32-bit instantiation body
    (via `useTadd32Fwd_is_call`; the delegation rewrite is the spec, as
    in `useAdd_correct`). -/
theorem useTadd32_correct (x y : BitVec 32) :
    useTadd32Fwd x y = addFwd x y := by
  cir_simp

/-- `use_tadd64` delegates: the entry is the 64-bit instantiation body. -/
theorem useTadd64_correct (x y : BitVec 64) :
    useTadd64Fwd x y = add64Fwd x y := by
  cir_simp

/-! ## N4d-i: `std::array<int, 4>` reads (one property per new shape) -/

/-- The `_S_ref` leaf reads the word at a live index. -/
theorem arrayRef_correct_hit (l : List (BitVec 32)) (n : BitVec 64)
    (x : BitVec 32) (h : l[n.toNat]? = some x) :
    arrayRefFwd l n = .ok (.i32 x) := by
  simp [arrayRefFwd, h]

/-- The `_S_ref` leaf reports `OOB` off the end. -/
theorem arrayRef_correct_oob (l : List (BitVec 32)) (n : BitVec 64)
    (h : l[n.toNat]? = none) :
    arrayRefFwd l n = .error .OOB := by
  simp [arrayRefFwd, h]

/-- `operator[]` delegates: the entry is the `_S_ref` body (via
    `arrayAtFwd_is_call`; the delegation rewrite is the spec, as in
    `useAdd_correct`). -/
theorem arrayAt_correct (l : List (BitVec 32)) (n : BitVec 64) :
    arrayAtFwd l n = arrayRefFwd l n :=
  arrayAtFwd_is_call l n

/-- The `array_sum` entry threads all three adds, mirroring
    `add3_correct_ok` (three certs, left-associated). -/
theorem arraySum_correct_ok (a b c d t u r : BitVec 32)
    (h1 : checkedAddI32 a b = .ok t)
    (h2 : checkedAddI32 t c = .ok u)
    (h3 : checkedAddI32 u d = .ok r) :
    arraySumFwd a b c d = .ok (.i32 r) := by
  simp only [arraySumFwd, h1, h2, h3, i32_map_ok]

/-- First-add failure propagates out of the entry. -/
theorem arraySum_correct_err_a (a b c d : BitVec 32) (e : Panic)
    (h : checkedAddI32 a b = .error e) :
    arraySumFwd a b c d = .error e := by
  simp [arraySumFwd, h]

/-- Second-add failure propagates out of the entry. -/
theorem arraySum_correct_err_b (a b c d t : BitVec 32) (e : Panic)
    (h1 : checkedAddI32 a b = .ok t)
    (h : checkedAddI32 t c = .error e) :
    arraySumFwd a b c d = .error e := by
  simp [arraySumFwd, h1, h]

/-- Third-add failure propagates out of the entry. -/
theorem arraySum_correct_err_c (a b c d t u : BitVec 32) (e : Panic)
    (h1 : checkedAddI32 a b = .ok t)
    (h2 : checkedAddI32 t c = .ok u)
    (h : checkedAddI32 u d = .error e) :
    arraySumFwd a b c d = .error e := by
  simp [arraySumFwd, h1, h2, h, i32_map_error]

/-! ## N4d-ii: `std::optional<int32_t>` guarded deref (one property per new shape) -/

/-- The `_M_is_engaged` leaf reports the engaged bit. -/
theorem optHas_correct (v : Option (BitVec 32)) :
    optHasFwd v = .ok (.b v.isSome) :=
  rfl

/-- `has_value` delegates: the entry is the `_M_is_engaged` body (via
    `optHasValueFwd_is_call`; the delegation rewrite is the spec, as
    in `arrayAt_correct`). -/
theorem optHasValue_correct (v : Option (BitVec 32)) :
    optHasValueFwd v = optHasFwd v :=
  optHasValueFwd_is_call v

/-- The payload `_M_get` leaf delivers the word on engaged. -/
theorem optGet_correct_some (x : BitVec 32) :
    optGetFwd (some x) = .ok (.i32 x) :=
  rfl

/-- The payload `_M_get` leaf fails loudly on disengaged (the
    `unreachable` assert made loud). -/
theorem optGet_correct_none :
    optGetFwd none = .error .AssertFail :=
  rfl

/-- `operator*` delegates: the fused leaf is the payload body (via
    `optDerefOpFwd_is_call`). -/
theorem optDerefOp_correct (v : Option (BitVec 32)) :
    optDerefOpFwd v = optGetFwd v :=
  optDerefOpFwd_is_call v

/-- The `opt_deref` entry returns the word on engaged. -/
theorem optDeref_correct_some (x : BitVec 32) :
    optDerefFwd (some x) = .ok (.i32 x) :=
  rfl

/-- The `opt_deref` entry returns the `-1` sentinel on disengaged. -/
theorem optDeref_correct_none :
    optDerefFwd none = .ok (.i32 (-1 : BitVec 32)) :=
  rfl

/-- `value()` delegates: the checked leaf is the payload body (via
    `optValueOpFwd_is_call`). -/
theorem optValueOp_correct (v : Option (BitVec 32)) :
    optValueOpFwd v = optGetFwd v :=
  optValueOpFwd_is_call v

/-- The throw helper always aborts. -/
theorem optThrow_correct :
    optThrowFwd = .error .AssertFail :=
  rfl

/-- The `opt_val_guarded` entry returns the word on engaged. -/
theorem optValue_correct_some (x : BitVec 32) :
    optValueFwd (some x) = .ok (.i32 x) :=
  rfl

/-- The `opt_val_guarded` entry returns the `-1` sentinel on
    disengaged. -/
theorem optValue_correct_none :
    optValueFwd none = .ok (.i32 (-1 : BitVec 32)) :=
  rfl

/-! ## N4d-iii: `std::span<const int32_t>` index-sum (one property per new shape) -/

/-- The `_M_extent` leaf reports the reified length. -/
theorem spanExtent_correct (l : List (BitVec 32)) :
    spanExtentFwd l = .ok (.u64 (BitVec.ofNat 64 l.length)) :=
  rfl

/-- `size` delegates: the entry is the `_M_extent` body (via
    `spanSizeFwd_is_call`; the delegation rewrite is the spec, as
    in `arrayAt_correct`). -/
theorem spanSize_correct (l : List (BitVec 32)) :
    spanSizeFwd l = spanExtentFwd l :=
  spanSizeFwd_is_call l

/-- The `operator[]` leaf delivers the word on a hit. -/
theorem spanIndex_correct_some (l : List (BitVec 32)) (n : BitVec 64)
    (x : BitVec 32) (hget : l[n.toNat]? = some x) :
    spanIndexFwd l n = .ok (.i32 x) := by
  simp [spanIndexFwd, hget]

/-- The `operator[]` leaf fails `OOB` loudly past the end. -/
theorem spanIndex_correct_oob (l : List (BitVec 32)) (n : BitVec 64)
    (hget : l[n.toNat]? = none) :
    spanIndexFwd l n = .error .OOB := by
  simp [spanIndexFwd, hget]

/-- The `span_sum` entry sums the empty view to zero. -/
theorem spanSum_correct_nil :
    spanSumFwd [] = .ok (.i32 (BitVec.ofNat 32 0)) := by
  simp [spanSumFwd, spanFold, i32_map_ok]

/-- The `span_sum` entry threads the head word through the
    checked add (cf. `arraySum_correct_ok`). -/
theorem spanSum_correct_cons (x : BitVec 32) (xs : List (BitVec 32))
    (a : BitVec 32)
    (h : checkedAddI32 (BitVec.ofNat 32 0) x = .ok a) :
    spanSumFwd (x :: xs) = .i32 <$> spanFold xs a := by
  simp [spanSumFwd, spanFold, h]

/-- The `span_sum` entry reports a head-word overflow loudly. -/
theorem spanSum_correct_cons_err (x : BitVec 32) (xs : List (BitVec 32))
    (e : Panic)
    (h : checkedAddI32 (BitVec.ofNat 32 0) x = .error e) :
    spanSumFwd (x :: xs) = .error e := by
  simp [spanSumFwd, spanFold, h, i32_map_error]

/-! ## N7a: `std::string_view` range-for sum (one property per new shape) -/

/-- The `begin` leaf reports the erased `0` offset. -/
theorem viewBegin_correct (l : List (BitVec 8)) :
    viewBeginFwd = .ok (.u64 (BitVec.ofNat 64 0)) :=
  rfl

/-- The `end` leaf reports the reified length. -/
theorem viewEnd_correct (l : List (BitVec 8)) :
    viewEndFwd l = .ok (.u64 (BitVec.ofNat 64 l.length)) :=
  rfl

/-- The `view_sum` entry sums the empty view to zero. -/
theorem viewSum_correct_nil :
    viewSumFwd [] = .ok (.i32 (BitVec.ofNat 32 0)) := by
  simp [viewSumFwd, viewFold, i32_map_ok]

/-- The `view_sum` entry threads the sign-extended head byte
    through the checked add. -/
theorem viewSum_correct_cons (x : BitVec 8) (xs : List (BitVec 8))
    (a : BitVec 32)
    (h : checkedAddI32 (BitVec.ofNat 32 0) (x.signExtend 32) = .ok a) :
    viewSumFwd (x :: xs) = .i32 <$> viewFold xs a := by
  simp [viewSumFwd, viewFold, h]

/-- The `view_sum` entry reports a head-byte overflow loudly. -/
theorem viewSum_correct_cons_err (x : BitVec 8) (xs : List (BitVec 8))
    (e : Panic)
    (h : checkedAddI32 (BitVec.ofNat 32 0) (x.signExtend 32) = .error e) :
    viewSumFwd (x :: xs) = .error e := by
  simp [viewSumFwd, viewFold, h, i32_map_error]

/-! ## N4d-iv-a: `std::vector<int32_t>` reads (one property per new shape) -/

/-- The `size` leaf reports the reified length. -/
theorem stdVecSize_correct (l : List (BitVec 32)) :
    stdVecSizeFwd l = .ok (.u64 (BitVec.ofNat 64 l.length)) :=
  rfl

/-- The `operator[]` leaf delivers the word on a hit. -/
theorem stdVecIndex_correct_some (l : List (BitVec 32)) (n : BitVec 64)
    (x : BitVec 32) (hget : l[n.toNat]? = some x) :
    stdVecIndexFwd l n = .ok (.i32 x) := by
  simp [stdVecIndexFwd, hget]

/-- The `operator[]` leaf fails `OOB` loudly past the end. -/
theorem stdVecIndex_correct_oob (l : List (BitVec 32)) (n : BitVec 64)
    (hget : l[n.toNat]? = none) :
    stdVecIndexFwd l n = .error .OOB := by
  simp [stdVecIndexFwd, hget]

/-- The `vec_read_sum` entry sums the empty vector to zero. -/
theorem stdVecReadSum_correct_nil :
    stdVecReadSumFwd [] = .ok (.i32 (BitVec.ofNat 32 0)) := by
  simp [stdVecReadSumFwd, stdVecFold, i32_map_ok]

/-- The `vec_read_sum` entry threads the head word through the
    checked add (cf. `spanSum_correct_cons`). -/
theorem stdVecReadSum_correct_cons (x : BitVec 32) (xs : List (BitVec 32))
    (a : BitVec 32)
    (h : checkedAddI32 (BitVec.ofNat 32 0) x = .ok a) :
    stdVecReadSumFwd (x :: xs) = .i32 <$> stdVecFold xs a := by
  simp [stdVecReadSumFwd, stdVecFold, h]

/-- The `vec_read_sum` entry reports a head-word overflow loudly. -/
theorem stdVecReadSum_correct_cons_err (x : BitVec 32) (xs : List (BitVec 32))
    (e : Panic)
    (h : checkedAddI32 (BitVec.ofNat 32 0) x = .error e) :
    stdVecReadSumFwd (x :: xs) = .error e := by
  simp [stdVecReadSumFwd, stdVecFold, h, i32_map_error]

/-- The `vec_reverse` entry returns the reversal. -/
theorem vecReverse_correct (l : List (BitVec 32)) :
    vecReverseFwd l = .ok (.stdVecVal l.reverse) :=
  rfl

/-- The `vec_seg_reverse` entry returns the window reversal (under
    caller debt; the forward is loud otherwise). -/
theorem vecSegReverse_correct (l : List (BitVec 32))
    (lo hi : BitVec 64)
    (hlo : lo.toNat ≤ hi.toNat) (hhi : hi.toNat ≤ l.length) :
    vecSegReverseFwd l lo hi =
      .ok (.stdVecVal (segReverseWindow l lo.toNat hi.toNat)) := by
  simp only [vecSegReverseFwd]
  rw [if_pos ⟨hlo, hhi⟩]

/-- The `vec_rotate` entry returns the left rotation (under caller
    debt; the forward is loud otherwise). -/
theorem vecRotate_correct (l : List (BitVec 32)) (k : BitVec 64)
    (hk : k.toNat ≤ l.length) :
    vecRotateFwd l k =
      .ok (.stdVecVal ((l.drop k.toNat) ++ l.take k.toNat)) := by
  simp only [vecRotateFwd]
  rw [if_pos hk]

/-- Move ctor: the destination takes the source word (the `o.s = 0`
    store is entry-level, threaded by `moveAccFunc`'s `assign`). -/
theorem accMoveCtor_correct (d s : BitVec 32) :
    accMoveCtorFwd d s = .ok (.i32 s) := by
  cir_simp

/-- `move_acc` ok path: both threaded adds succeed. The move itself is
    invisible at spec level (value-preserving + zeroing, both
    discharged inside `evalProgFunc_moveAcc`). -/
theorem moveAcc_correct_ok (a b s1 s2 : BitVec 32)
    (h1 : checkedAddI32 0 a = .ok s1)
    (h2 : checkedAddI32 s1 b = .ok s2) :
    moveAccFwd a b = .ok (.i32 s2) := by
  simp only [moveAccFwd_is_moveAcc, moveAcc_ok a b s1 s2 h1 h2] <;> cir_simp

/-- `move_acc` first-add failure propagates. -/
theorem moveAcc_correct_err_a (a b : BitVec 32) (e : Panic)
    (h : checkedAddI32 0 a = .error e) :
    moveAccFwd a b = .error e := by
  simp only [moveAccFwd_is_moveAcc, moveAcc_err_a a b e h] <;> cir_simp

/-- `move_acc` second-add failure propagates once the first succeeds. -/
theorem moveAcc_correct_err_b (a b s1 : BitVec 32) (e : Panic)
    (h1 : checkedAddI32 0 a = .ok s1)
    (h2 : checkedAddI32 s1 b = .error e) :
    moveAccFwd a b = .error e := by
  simp only [moveAccFwd_is_moveAcc, moveAcc_err_b a b s1 e h1 h2] <;> cir_simp

/-- `scope_early` takes the early path when the first add succeeds and
    the args are equal (the scope-exit dtor is a no-op, so the first
    `get` is the answer). -/
theorem scopeEarly_correct_eq (a b s1 : BitVec 32)
    (h1 : checkedAddI32 0 a = .ok s1)
    (heq : a == b) :
    scopeEarlyFwd a b = .ok (.i32 s1) := by
  simp only [scopeEarlyFwd_is_scopeEarly,
    scopeEarly_ok_eq a b s1 h1 heq] <;> cir_simp

/-- `scope_early` takes the fallthrough path on unequal args. -/
theorem scopeEarly_correct_ne (a b s1 s2 : BitVec 32)
    (h1 : checkedAddI32 0 a = .ok s1)
    (hne : (a == b) = false)
    (h2 : checkedAddI32 s1 b = .ok s2) :
    scopeEarlyFwd a b = .ok (.i32 s2) := by
  simp only [scopeEarlyFwd_is_scopeEarly,
    scopeEarly_ok_ne a b s1 s2 h1 hne h2] <;> cir_simp

/-- `scope_early` first-add failure propagates. -/
theorem scopeEarly_correct_err_a (a b : BitVec 32) (e : Panic)
    (h : checkedAddI32 0 a = .error e) :
    scopeEarlyFwd a b = .error e := by
  simp only [scopeEarlyFwd_is_scopeEarly,
    scopeEarly_err_a a b e h] <;> cir_simp

/-- `scope_early` second-add failure propagates on the fallthrough. -/
theorem scopeEarly_correct_err_b (a b s1 : BitVec 32) (e : Panic)
    (h1 : checkedAddI32 0 a = .ok s1)
    (hne : (a == b) = false)
    (h2 : checkedAddI32 s1 b = .error e) :
    scopeEarlyFwd a b = .error e := by
  simp only [scopeEarlyFwd_is_scopeEarly,
    scopeEarly_err_b a b s1 e h1 hne h2] <;> cir_simp

/-! ## N4d-iv-b1: `std::vector<int32_t>` growth leaves (one property per new shape) -/

/-- The default ctor delivers the empty owned triple. -/
theorem stdVecEmptyCtor_correct :
    stdVecEmptyCtorFwd = .ok (.stdVecOwned ⟨[], false⟩ 0 0) :=
  rfl

/-- The unit leaf answers zero (erased-iterator no-ops). -/
theorem stdVecUnit_correct :
    stdVecUnitFwd = .ok (.i32 (BitVec.ofNat 32 0)) :=
  rfl

/-- The dtor on a null triple is a passthrough. -/
theorem stdVecDtor_correct_empty (b : Vec32) (len : Nat) :
    stdVecDtorFwd b len 0 = .ok (.stdVecOwned b len 0) := by
  simp [stdVecDtorFwd]

/-- The dtor on a live triple frees the storage. -/
theorem stdVecDtor_correct_free (b b' : Vec32) (len cap : Nat)
    (hcap : 0 < cap) (hfree : vecFree b = .ok b') :
    stdVecDtorFwd b len cap = .ok (.stdVecOwned b' len cap) := by
  simp [stdVecDtorFwd, hcap, hfree]

/-- Destroying a range is a no-op (trivial element type). -/
theorem stdVecDestroyNoop_correct :
    stdVecDestroyNoopFwd = .ok (.i32 (BitVec.ofNat 32 0)) :=
  rfl

/-- Destroying one element is a no-op. -/
theorem stdVecDestroyPtr_correct :
    stdVecDestroyPtrFwd = .ok (.i32 (BitVec.ofNat 32 0)) :=
  rfl

/-- The allocator projection answers zero (stateless allocator). -/
theorem stdVecGetTp_correct :
    stdVecGetTpFwd = .ok (.i32 (BitVec.ofNat 32 0)) :=
  rfl

/-- `max_size` is the `S64_MAX / 4` difference bound. -/
theorem stdVecDiffMax_correct :
    stdVecDiffMaxFwd = .ok (.u64 stdVecMaxDiffBV) :=
  rfl

/-- `max` takes the right arg when it is larger. -/
theorem stdVecMax_correct_right (a b : BitVec 64)
    (h : a.ult b = true) :
    stdVecMaxFwd a b = .ok (.u64 b) := by
  simp [stdVecMaxFwd, h]

/-- `max` takes the left arg otherwise. -/
theorem stdVecMax_correct_left (a b : BitVec 64)
    (h : a.ult b = false) :
    stdVecMaxFwd a b = .ok (.u64 a) := by
  simp [stdVecMaxFwd, h]

/-- `min` takes the right arg when it is smaller. -/
theorem stdVecMin_correct_right (a b : BitVec 64)
    (h : b.ult a = true) :
    stdVecMinFwd a b = .ok (.u64 b) := by
  simp [stdVecMinFwd, h]

/-- `min` takes the left arg otherwise. -/
theorem stdVecMin_correct_left (a b : BitVec 64)
    (h : b.ult a = false) :
    stdVecMinFwd a b = .ok (.u64 a) := by
  simp [stdVecMinFwd, h]

/-- `check_len` fails loudly past `max_size - size`. -/
theorem stdVecCheckLen_correct_fail (len : Nat) (n : BitVec 64)
    (h : (stdVecMaxDiffBV - BitVec.ofNat 64 len).ult n = true) :
    stdVecCheckLenFwd len n = .error .AssertFail := by
  simp [stdVecCheckLenFwd, h]

/-- `check_len` saturates at `max_size` on wrapping growth. -/
theorem stdVecCheckLen_correct_saturate (len : Nat) (n : BitVec 64)
    (h1 : (stdVecMaxDiffBV - BitVec.ofNat 64 len).ult n = false)
    (h2 : (BitVec.ofNat 64 len +
      (if (BitVec.ofNat 64 len).ult n then n
        else BitVec.ofNat 64 len)).ult (BitVec.ofNat 64 len) =
      true) :
    stdVecCheckLenFwd len n = .ok (.u64 stdVecMaxDiffBV) := by
  simp [stdVecCheckLenFwd, h1, h2]

/-- `check_len` otherwise returns the grown length. -/
theorem stdVecCheckLen_correct_exact (len : Nat) (n : BitVec 64)
    (h1 : (stdVecMaxDiffBV - BitVec.ofNat 64 len).ult n = false)
    (h2 : (BitVec.ofNat 64 len +
      (if (BitVec.ofNat 64 len).ult n then n
        else BitVec.ofNat 64 len)).ult (BitVec.ofNat 64 len) =
      false)
    (h3 : stdVecMaxDiffBV.ult (BitVec.ofNat 64 len +
      (if (BitVec.ofNat 64 len).ult n then n
        else BitVec.ofNat 64 len)) = false) :
    stdVecCheckLenFwd len n = .ok (.u64 (BitVec.ofNat 64 len +
      (if (BitVec.ofNat 64 len).ult n then n
        else BitVec.ofNat 64 len))) := by
  simp [stdVecCheckLenFwd, h1, h2, h3]

/-- `begin` is the zero offset. -/
theorem stdVecBegin_correct :
    stdVecBeginFwd = .ok (.u64 (BitVec.ofNat 64 0)) :=
  rfl

/-- `end` is the reified length. -/
theorem stdVecEnd_correct (len : Nat) :
    stdVecEndFwd len = .ok (.u64 (BitVec.ofNat 64 len)) :=
  rfl

/-- `capacity` is the reified storage end (N7b: the `end` twin over
    the second header word). -/
theorem stdVecGrowCapacity_correct (cap : Nat) :
    stdVecGrowCapacityFwd cap = .ok (.u64 (BitVec.ofNat 64 cap)) :=
  rfl

/-- `back` is one before the length. -/
theorem stdVecBack_correct (len : Nat) :
    stdVecBackFwd len = .ok (.u64 (BitVec.ofNat 64 len - 1)) :=
  rfl

/-- Iterator conversion is the identity. -/
theorem stdVecIterId_correct (x : BitVec 64) :
    stdVecIterIdFwd x = .ok (.u64 x) :=
  rfl

/-- Iterator difference is word subtraction. -/
theorem stdVecMinusEl_correct (it n : BitVec 64) :
    stdVecMinusElFwd it n = .ok (.u64 (it - n)) :=
  rfl

/-- Signed iterator difference is word subtraction. -/
theorem stdVecMinus_correct (a b : BitVec 64) :
    stdVecMinusFwd a b = .ok (.i64 (a - b)) :=
  rfl

/-- `_M_allocate` of zero words keeps the null triple shape. -/
theorem stdVecAlloc_correct_zero (n : BitVec 64)
    (h : (BitVec.ofNat 64 0).ult n = false) :
    stdVecAllocFwd n = .ok (.stdVecOwned
      ⟨List.replicate (BitVec.ofNat 64 0).toNat 0, false⟩ 0
      (BitVec.ofNat 64 0).toNat) := by
  simp [stdVecAllocFwd, h]

/-- `_M_allocate` of `n` words delivers zeroed storage. -/
theorem stdVecAlloc_correct_ok (n : BitVec 64)
    (h1 : (BitVec.ofNat 64 0).ult n = true)
    (h2 : stdVecMaxDiffBV.ult n = false) :
    stdVecAllocFwd n = .ok (.stdVecOwned
      ⟨List.replicate n.toNat 0, false⟩ 0 n.toNat) := by
  simp [stdVecAllocFwd, h1, h2]

/-- `_M_allocate` past `max_size` fails loudly. -/
theorem stdVecAlloc_correct_overmax (n : BitVec 64)
    (h1 : (BitVec.ofNat 64 0).ult n = true)
    (h2 : stdVecMaxDiffBV.ult n = true) :
    stdVecAllocFwd n = .error .AssertFail := by
  simp [stdVecAllocFwd, h1, h2]

/-- `_M_deallocate` consumes the storage. -/
theorem stdVecDealloc_correct_ok (b b' : Vec32) (len cap : Nat)
    (h : vecFree b = .ok b') :
    stdVecDeallocFwd b len cap = .ok (.stdVecOwned b' len cap) := by
  simp [stdVecDeallocFwd, h]

/-- `_M_deallocate` propagates a free failure. -/
theorem stdVecDealloc_correct_err (b : Vec32) (len cap : Nat)
    (e : Panic) (h : vecFree b = .error e) :
    stdVecDeallocFwd b len cap = .error e := by
  simp [stdVecDeallocFwd, h]

/-- The deallocate guard on zero words is a passthrough. -/
theorem stdVecDeallocGuard_correct_zero (b : Vec32) (len cap : Nat)
    (n : BitVec 64)
    (h : (BitVec.ofNat 64 0).ult n = false) :
    stdVecDeallocGuardFwd b len cap n =
      .ok (.stdVecOwned b len cap) := by
  simp [stdVecDeallocGuardFwd, h]

/-- The deallocate guard otherwise frees the storage. -/
theorem stdVecDeallocGuard_correct_free (b b' : Vec32) (len cap : Nat)
    (n : BitVec 64)
    (h1 : (BitVec.ofNat 64 0).ult n = true)
    (h2 : vecFree b = .ok b') :
    stdVecDeallocGuardFwd b len cap n =
      .ok (.stdVecOwned b' len cap) := by
  simp [stdVecDeallocGuardFwd, h1, h2]

/-- `construct` places the word. -/
theorem stdVecConstruct_correct_ok (b b' : Vec32) (len cap : Nat)
    (p : BitVec 64) (x : BitVec 32)
    (h : vecSet b p.toNat x = .ok b') :
    stdVecConstructFwd b len cap p x =
      .ok (.stdVecOwned b' len cap) := by
  simp [stdVecConstructFwd, h]

/-- `construct` past the storage fails loudly. -/
theorem stdVecConstruct_correct_oob (b : Vec32) (len cap : Nat)
    (p : BitVec 64) (x : BitVec 32) (e : Panic)
    (h : vecSet b p.toNat x = .error e) :
    stdVecConstructFwd b len cap p x = .error e := by
  simp [stdVecConstructFwd, h]

/-- Relocating zero words leaves the destination buffer in place. -/
theorem stdVecReloc_correct_nil (bS : Vec32) (lenS capS : Nat)
    (bD : Vec32) (lenD capD : Nat) (first last result : BitVec 64)
    (h : last.toNat - first.toNat = 0) :
    stdVecRelocFwd bS lenS capS bD lenD capD first last result =
      .ok (.stdVecOwned bD lenD capD) := by
  simp [stdVecRelocFwd, h, stdVecBlitFold]

/-! ## N4d-iv-b2 `_M_realloc_insert`: composer spec (Fwd level) -/

/-- `check_len` failure fails the whole reallocation (the first bind;
    cf. `addCaller_correct_err`). -/
theorem stdVecGrowRealloc_correct_err_checklen (b : Vec32) (len cap : Nat)
    (pos : BitVec 64) (x : BitVec 32) (e : Panic)
    (h : stdVecCheckLenFwd len (BitVec.ofNat 64 1) = .error e) :
    stdVecGrowReallocFwd b len cap pos x = .error e := by
  simp only [stdVecGrowReallocFwd, h, vecGrow_bind_err]

/-- All-ok stages deliver the reallocated triple: the second relocate's
    buffer with the bumped length (`addCaller_correct_ok` shape — one
    equation per composer `callRet`, projectors discharging the
    between-call value shapes). Template instance: sequential
    threading, eight callee equations (see VERIFYING.md Contracts). -/
theorem stdVecGrowRealloc_correct_ok (b : Vec32) (len cap : Nat)
    (pos : BitVec 64) (x : BitVec 32)
    (newlen : BitVec 64) (bNew bC bR1 bR2 : Vec32) (v : Value)
    (hck : stdVecCheckLenFwd len (BitVec.ofNat 64 1) = .ok (.u64 newlen))
    (hbg : stdVecBeginFwd = .ok (.u64 (BitVec.ofNat 64 0)))
    (hmi : stdVecMinusFwd pos (BitVec.ofNat 64 0) =
      .ok (.i64 (pos - BitVec.ofNat 64 0)))
    (hal : stdVecAllocFwd newlen = .ok (.stdVecOwned bNew 0 newlen.toNat))
    (hcon : stdVecConstructFwd bNew 0 newlen.toNat
      (pos - BitVec.ofNat 64 0) x = .ok (.stdVecOwned bC 0 newlen.toNat))
    (hr1 : stdVecRelocFwd b len cap bC 0 newlen.toNat
      (BitVec.ofNat 64 0) (pos - BitVec.ofNat 64 0)
      (BitVec.ofNat 64 0) = .ok (.stdVecOwned bR1 0 newlen.toNat))
    (hr2 : stdVecRelocFwd b len cap bR1 0 newlen.toNat
      (pos - BitVec.ofNat 64 0) (BitVec.ofNat 64 len)
      ((pos - BitVec.ofNat 64 0) + BitVec.ofNat 64 1) =
      .ok (.stdVecOwned bR2 0 newlen.toNat))
    (hgd : stdVecDeallocGuardFwd b len cap (BitVec.ofNat 64 cap) = .ok v) :
    stdVecGrowReallocFwd b len cap pos x =
      .ok (.stdVecOwned bR2 ((BitVec.ofNat 64 len + BitVec.ofNat 64 1).toNat)
        newlen.toNat) := by
  simp only [stdVecGrowReallocFwd, hck, hbg, hmi, hal, hcon, hr1, hr2, hgd,
    vecGrow_bind_ok, vecGrowU64, vecGrowI64, vecGrowOwned]

/-! ## N4d-iv-b2 `emplace_back`: composer spec (Fwd level) -/

/-- Slow dispatch: at capacity the forward is the realloc forward at
    `pos = len`. Template instance: delegation (see VERIFYING.md
    Contracts). -/
theorem stdVecEmplaceBack_correct_slow (b : Vec32) (len cap : Nat)
    (x : BitVec 32) (h : len = cap) :
    stdVecEmplaceBackFwd b len cap x =
      stdVecGrowReallocFwd b len cap (BitVec.ofNat 64 len) x := by
  unfold stdVecEmplaceBackFwd; simp [h]

/-- Fast dispatch: below capacity the forward is the construct
    forward at `len` with length `len + 1`. Template instance:
    delegation (see VERIFYING.md Contracts). -/
theorem stdVecEmplaceBack_correct_fast (b : Vec32) (len cap : Nat)
    (x : BitVec 32) (h : len ≠ cap) :
    stdVecEmplaceBackFwd b len cap x =
      ((stdVecConstructFwd b len cap (BitVec.ofNat 64 len) x).bind
        fun conv =>
      (vecGrowOwned conv).bind fun (b', _, _) =>
      .ok (.stdVecOwned b' (len + 1) cap)) := by
  unfold stdVecEmplaceBackFwd; simp [h]

/-- `check_len` failure fails the slow path (and hence the whole
    append at capacity). -/
theorem stdVecEmplaceBack_correct_err_checklen (b : Vec32) (len cap : Nat)
    (x : BitVec 32) (e : Panic)
    (hlc : len = cap)
    (h : stdVecCheckLenFwd len (BitVec.ofNat 64 1) = .error e) :
    stdVecEmplaceBackFwd b len cap x = .error e := by
  rw [stdVecEmplaceBack_correct_slow b len cap x hlc,
    stdVecGrowRealloc_correct_err_checklen b len cap _ x e h]

/-- All-ok slow stages deliver the reallocated triple. -/
theorem stdVecEmplaceBack_correct_ok_slow (b : Vec32) (len cap : Nat)
    (x : BitVec 32)
    (hlc : len = cap)
    (newlen : BitVec 64) (bNew bC bR1 bR2 : Vec32) (v : Value)
    (hck : stdVecCheckLenFwd len (BitVec.ofNat 64 1) = .ok (.u64 newlen))
    (hbg : stdVecBeginFwd = .ok (.u64 (BitVec.ofNat 64 0)))
    (hmi : stdVecMinusFwd (BitVec.ofNat 64 len) (BitVec.ofNat 64 0) =
      .ok (.i64 ((BitVec.ofNat 64 len) - BitVec.ofNat 64 0)))
    (hal : stdVecAllocFwd newlen = .ok (.stdVecOwned bNew 0 newlen.toNat))
    (hcon : stdVecConstructFwd bNew 0 newlen.toNat
      ((BitVec.ofNat 64 len) - BitVec.ofNat 64 0) x =
      .ok (.stdVecOwned bC 0 newlen.toNat))
    (hr1 : stdVecRelocFwd b len cap bC 0 newlen.toNat
      (BitVec.ofNat 64 0) ((BitVec.ofNat 64 len) - BitVec.ofNat 64 0)
      (BitVec.ofNat 64 0) = .ok (.stdVecOwned bR1 0 newlen.toNat))
    (hr2 : stdVecRelocFwd b len cap bR1 0 newlen.toNat
      ((BitVec.ofNat 64 len) - BitVec.ofNat 64 0) (BitVec.ofNat 64 len)
      (((BitVec.ofNat 64 len) - BitVec.ofNat 64 0) + BitVec.ofNat 64 1) =
      .ok (.stdVecOwned bR2 0 newlen.toNat))
    (hgd : stdVecDeallocGuardFwd b len cap (BitVec.ofNat 64 cap) = .ok v) :
    stdVecEmplaceBackFwd b len cap x =
      .ok (.stdVecOwned bR2 ((BitVec.ofNat 64 len + BitVec.ofNat 64 1).toNat)
        newlen.toNat) := by
  rw [stdVecEmplaceBack_correct_slow b len cap x hlc,
    stdVecGrowRealloc_correct_ok b len cap _ x newlen bNew bC bR1 bR2 v
      hck hbg hmi hal hcon hr1 hr2 hgd]

/-- Fast construct failure fails the whole append. -/
theorem stdVecEmplaceBack_correct_err_construct (b : Vec32) (len cap : Nat)
    (x : BitVec 32) (e : Panic)
    (hlc : len ≠ cap)
    (h : stdVecConstructFwd b len cap (BitVec.ofNat 64 len) x =
      .error e) :
    stdVecEmplaceBackFwd b len cap x = .error e := by
  simp only [stdVecEmplaceBack_correct_fast b len cap x hlc, h,
    vecGrow_bind_err]

/-- Fast construct success delivers the bumped triple. -/
theorem stdVecEmplaceBack_correct_ok_fast (b : Vec32) (len cap : Nat)
    (x : BitVec 32) (bC : Vec32)
    (hlc : len ≠ cap)
    (h : stdVecConstructFwd b len cap (BitVec.ofNat 64 len) x =
      .ok (.stdVecOwned bC len cap)) :
    stdVecEmplaceBackFwd b len cap x =
      .ok (.stdVecOwned bC (len + 1) cap) := by
  simp only [stdVecEmplaceBack_correct_fast b len cap x hlc, h,
    vecGrow_bind_ok, vecGrowOwned]

/-! ## N4d-iv-b2 `push_back`: forwarder spec (Fwd level) -/

/-- Slow dispatch: at capacity the forwarder is the realloc forward at
    `pos = len` (via `emplace_back`). -/
theorem stdVecPushBack_correct_slow (b : Vec32) (len cap : Nat)
    (x : BitVec 32) (h : len = cap) :
    stdVecPushBackFwd b len cap x =
      stdVecGrowReallocFwd b len cap (BitVec.ofNat 64 len) x := by
  unfold stdVecPushBackFwd
  exact stdVecEmplaceBack_correct_slow b len cap x h

/-- Fast dispatch: below capacity the forwarder is the construct
    forward at `len` with length `len + 1`. -/
theorem stdVecPushBack_correct_fast (b : Vec32) (len cap : Nat)
    (x : BitVec 32) (h : len ≠ cap) :
    stdVecPushBackFwd b len cap x =
      ((stdVecConstructFwd b len cap (BitVec.ofNat 64 len) x).bind
        fun conv =>
      (vecGrowOwned conv).bind fun (b', _, _) =>
      .ok (.stdVecOwned b' (len + 1) cap)) := by
  unfold stdVecPushBackFwd
  exact stdVecEmplaceBack_correct_fast b len cap x h

/-- `check_len` failure fails the slow path (and hence the whole
    append at capacity). -/
theorem stdVecPushBack_correct_err_checklen (b : Vec32) (len cap : Nat)
    (x : BitVec 32) (e : Panic)
    (hlc : len = cap)
    (h : stdVecCheckLenFwd len (BitVec.ofNat 64 1) = .error e) :
    stdVecPushBackFwd b len cap x = .error e := by
  unfold stdVecPushBackFwd
  exact stdVecEmplaceBack_correct_err_checklen b len cap x e hlc h

/-- All-ok slow stages deliver the reallocated triple. -/
theorem stdVecPushBack_correct_ok_slow (b : Vec32) (len cap : Nat)
    (x : BitVec 32)
    (hlc : len = cap)
    (newlen : BitVec 64) (bNew bC bR1 bR2 : Vec32) (v : Value)
    (hck : stdVecCheckLenFwd len (BitVec.ofNat 64 1) = .ok (.u64 newlen))
    (hbg : stdVecBeginFwd = .ok (.u64 (BitVec.ofNat 64 0)))
    (hmi : stdVecMinusFwd (BitVec.ofNat 64 len) (BitVec.ofNat 64 0) =
      .ok (.i64 ((BitVec.ofNat 64 len) - BitVec.ofNat 64 0)))
    (hal : stdVecAllocFwd newlen = .ok (.stdVecOwned bNew 0 newlen.toNat))
    (hcon : stdVecConstructFwd bNew 0 newlen.toNat
      ((BitVec.ofNat 64 len) - BitVec.ofNat 64 0) x =
      .ok (.stdVecOwned bC 0 newlen.toNat))
    (hr1 : stdVecRelocFwd b len cap bC 0 newlen.toNat
      (BitVec.ofNat 64 0) ((BitVec.ofNat 64 len) - BitVec.ofNat 64 0)
      (BitVec.ofNat 64 0) = .ok (.stdVecOwned bR1 0 newlen.toNat))
    (hr2 : stdVecRelocFwd b len cap bR1 0 newlen.toNat
      ((BitVec.ofNat 64 len) - BitVec.ofNat 64 0) (BitVec.ofNat 64 len)
      (((BitVec.ofNat 64 len) - BitVec.ofNat 64 0) + BitVec.ofNat 64 1) =
      .ok (.stdVecOwned bR2 0 newlen.toNat))
    (hgd : stdVecDeallocGuardFwd b len cap (BitVec.ofNat 64 cap) = .ok v) :
    stdVecPushBackFwd b len cap x =
      .ok (.stdVecOwned bR2 ((BitVec.ofNat 64 len + BitVec.ofNat 64 1).toNat)
        newlen.toNat) := by
  unfold stdVecPushBackFwd
  exact stdVecEmplaceBack_correct_ok_slow b len cap x hlc newlen bNew
    bC bR1 bR2 v hck hbg hmi hal hcon hr1 hr2 hgd

/-- Fast construct failure fails the whole append. -/
theorem stdVecPushBack_correct_err_construct (b : Vec32) (len cap : Nat)
    (x : BitVec 32) (e : Panic)
    (hlc : len ≠ cap)
    (h : stdVecConstructFwd b len cap (BitVec.ofNat 64 len) x =
      .error e) :
    stdVecPushBackFwd b len cap x = .error e := by
  unfold stdVecPushBackFwd
  exact stdVecEmplaceBack_correct_err_construct b len cap x e hlc h

/-- Fast construct success delivers the bumped triple. -/
theorem stdVecPushBack_correct_ok_fast (b : Vec32) (len cap : Nat)
    (x : BitVec 32) (bC : Vec32)
    (hlc : len ≠ cap)
    (h : stdVecConstructFwd b len cap (BitVec.ofNat 64 len) x =
      .ok (.stdVecOwned bC len cap)) :
    stdVecPushBackFwd b len cap x =
      .ok (.stdVecOwned bC (len + 1) cap) := by
  unfold stdVecPushBackFwd
  exact stdVecEmplaceBack_correct_ok_fast b len cap x bC hlc h

/-! ## N7b `reserve`: composer spec (Fwd level) -/

/-- Below `max_size` with sufficient capacity the triple passes
    through untouched. -/
theorem stdVecReserve_correct_passthrough (b : Vec32) (len cap : Nat)
    (n : BitVec 64)
    (hmax : stdVecMaxDiffBV.ult n = false)
    (hcap : (BitVec.ofNat 64 cap).ult n = false) :
    stdVecReserveFwd b len cap n = .ok (.stdVecOwned b len cap) := by
  simp only [stdVecReserveFwd, hmax, hcap, ite_false, reduceCtorEq]

/-- Over `max_size` the `length_error` arm fails loudly. -/
theorem stdVecReserve_correct_throw (b : Vec32) (len cap : Nat)
    (n : BitVec 64)
    (hmax : stdVecMaxDiffBV.ult n = true) :
    stdVecReserveFwd b len cap n = .error .AssertFail := by
  simp only [stdVecReserveFwd, hmax, ite_true, reduceCtorEq]

/-- The reallocation arm threads the owned triple through allocate →
    relocate → deallocate and re-pins the length (leaf-hypothesis style
    like `stdVecGrowRealloc_correct_ok`). Template instance:
    sequential threading (see VERIFYING.md Contracts). -/
theorem stdVecReserve_correct_realloc (b : Vec32) (len cap : Nat)
    (n : BitVec 64) (bNew bR : Vec32) (v : Value)
    (hmax : stdVecMaxDiffBV.ult n = false)
    (hcap : (BitVec.ofNat 64 cap).ult n = true)
    (hal : stdVecAllocFwd n = .ok (.stdVecOwned bNew 0 n.toNat))
    (hrlv : stdVecRelocFwd b len cap bNew 0 n.toNat
      (BitVec.ofNat 64 0) (BitVec.ofNat 64 len)
      (BitVec.ofNat 64 0) = .ok (.stdVecOwned bR 0 n.toNat))
    (hgd : stdVecDeallocGuardFwd b len cap (BitVec.ofNat 64 cap) =
      .ok v) :
    stdVecReserveFwd b len cap n =
      .ok (.stdVecOwned bR ((BitVec.ofNat 64 len).toNat) n.toNat) := by
  simp only [stdVecReserveFwd, hmax, hcap, ite_false, ite_true, reduceCtorEq, hal,
    hrlv, hgd, vecGrow_bind_ok, vecGrowOwned]

/-! ## N3c gallery: worked properties beyond the admitted-shape specs -/

/-- The index fill is sorted: `vec` writes `k` at slot `k`, so the
    filled values ascend (`ofNat` is monotone below `2 ^ 32`; the
    cross-append case is the whole proof). -/
theorem fillSorted_u32 (m : Nat) (hm : m ≤ 2 ^ 32) :
    List.Pairwise (· ≤ ·) ((List.range m).map (BitVec.ofNat 32)) := by
  rw [List.pairwise_map]
  revert hm
  induction m with
  | zero => intro _; simp
  | succ k ih =>
    intro hm
    rw [List.range_succ, List.pairwise_append]
    refine ⟨ih (by omega), List.pairwise_singleton _ _, ?_⟩
    intro a ha b hb
    have hbk : b = k := List.mem_singleton.mp hb
    rw [hbk]
    have hak : a < k := List.mem_range.mp ha
    rw [BitVec.ofNat_le_ofNat,
      Nat.mod_eq_of_lt (show a < 2 ^ 32 by omega),
      Nat.mod_eq_of_lt (show k < 2 ^ 32 by omega)]
    omega

/-- `find_eq` returns the *first* match: every index below the hit
    holds a different value (core's `find?_range_eq_some` is the
    minimality fact; the `decide` bridge turns `(!·) = true` into
    `≠`). -/
theorem findEq_first_match (l : List (BitVec 32)) (n : Nat) (k : BitVec 32)
    (j : Nat) (h : findIdxU32 l n k = some j) (i : Nat) (hij : i < j) :
    l[i]? ≠ some k := by
  rw [findIdxU32, List.find?_range_eq_some] at h
  have hneg : decide (l[i]? = some k) = false := by
    simpa using h.2.2 i hij
  exact of_decide_eq_false hneg

/-- `realloc` preserves the prefix at spec level: the grown program
    sums `range (n + n)`, whose length-`n` prefix is exactly the
    ungrown program's domain (the extension fills `[n, n + n)` without
    touching it; cf. `vecReallocFillSumU32_correct`). -/
theorem reallocPrefix_spec (n : Nat) :
    ((List.range (n + n)).take n) = List.range n := by
  simp

/-! ## N4d-iv-b2 entry-scoped `operator[]` leaf: spec (Fwd level) -/

/-- In-bounds index reads deliver the buffer word. -/
theorem stdVecGrowIndex_correct_hit (b : Vec32) (len : Nat)
    (n : BitVec 64)
    (hlive : b.freed = false)
    (x : BitVec 32)
    (hget : b.val[n.toNat]? = some x)
    (hlt : n.toNat < len) :
    stdVecGrowIndexFwd b len n = .ok (.i32 x) := by
  simp [stdVecGrowIndexFwd, hlive, hget, hlt]

/-! ## N4d-iv-b2 `vec_push_sum` entry: spec (Fwd level) -/

/-- The closed entry computes `1 + 2 + 3 = 6` (frozen by evaluating
    `vecPushSumEntryFwd`). -/
theorem vecPushSumEntry_correct :
    vecPushSumEntryFwd = .ok (.i32 6) := rfl

/-! ## N7b `vec_reserve_sum` entry: spec (Fwd level) -/

/-- The closed entry computes `1 + 2 = 3` (frozen by evaluating
    `vecReserveSumEntryFwd`). -/
theorem vecReserveSumEntry_correct :
    vecReserveSumEntryFwd = .ok (.i32 3) := rfl

/-! ## N7c `vec_insert_sum` entry: spec (Fwd level) -/

/-- The closed entry computes `1 + 2 + 3 = 6` (frozen by evaluating
    `vecInsertSumEntryFwd`; the middle insert lands `3` at index `1`
    before the reads). -/
theorem vecInsertSumEntry_correct :
    vecInsertSumEntryFwd = .ok (.i32 6) := rfl

/-! ## N7d `vec_erase_sum` entry: spec (Fwd level) -/

/-- The closed entry computes `1 + 3 = 4` (frozen by evaluating
    `vecEraseSumEntryFwd`; the erase at position `1` drops the `2`
    before the reads). -/
theorem vecEraseSumEntry_correct :
    vecEraseSumEntryFwd = .ok (.i32 4) := rfl

/-! ## P2-M1 merge-drain contracts (U2 template instances) -/

/-- Drain-`i` ok leg: fuel covering the remaining `mid - i`
    copies plus succeeding reads discharge the drain at
    `i = mid`, with `k` advanced and length preserved.
    Template instance: sequential-threading callee (see
    VERIFYING.md Contracts). -/
theorem VecMergeRuns.mergeRunsDrainIFwd_ok (la lt : List (BitVec 32))
    (fuel i k mid : Nat)
    (hle : i ≤ mid)
    (hfuel : mid - i ≤ fuel)
    (hread_la : ∀ p, i ≤ p → p < mid → ∃ x, la[p]? = some x)
    (hread_lt : ∀ q, k ≤ q → q < k + (mid - i) → ∃ y, lt[q]? = some y) :
    ∃ k' lt', VecMergeRuns.mergeRunsDrainIFwd la lt fuel i k mid = .ok (mid, k', lt') ∧
      k' = k + (mid - i) ∧ lt'.length = lt.length := by
  induction fuel generalizing i k lt with
  | zero =>
    have him : i = mid := by omega
    subst him
    refine ⟨k, lt, ?_, ?_, rfl⟩
    · simp [VecMergeRuns.mergeRunsDrainIFwd]
    · simp
  | succ n ih =>
    by_cases hlt : i < mid
    · obtain ⟨x, hx⟩ := hread_la i (Nat.le_refl _) hlt
      obtain ⟨y, hy⟩ := hread_lt k (Nat.le_refl _) (by omega)
      have hfuel' : mid - (i + 1) ≤ n := by omega
      have ih' := ih (lt.set k x) (i + 1) (k + 1) (by omega) hfuel'
        (fun p h1 h2 => hread_la p (by omega) h2)
        (fun q h1 h2 => by
          obtain ⟨z, hz⟩ := hread_lt q (by omega) (by omega)
          exact ⟨z, by
            rw [List.getElem?_set_ne (show k ≠ q by omega)]
            exact hz⟩)
      obtain ⟨k', lt', heq, hk', hlen⟩ := ih'
      refine ⟨k', lt', ?_, ?_, ?_⟩
      · simp only [VecMergeRuns.mergeRunsDrainIFwd, dite_eq_left hlt, hy, hx]
        exact heq
      · omega
      · have hset : (lt.set k x).length = lt.length := List.length_set
        exact hlen.trans hset
    · have him : i = mid := by omega
      subst him
      refine ⟨k, lt, ?_, ?_, rfl⟩
      · simp only [VecMergeRuns.mergeRunsDrainIFwd, dite_eq_right hlt]
      · simp

/-- Drain-`i` error leg, `tmp` fails first: the `j`-th `tmp`
    read is `none` while all prior reads succeed. -/
theorem VecMergeRuns.mergeRunsDrainIFwd_err_lt (la lt : List (BitVec 32))
    (fuel i k mid j : Nat)
    (hle : i ≤ mid)
    (hlt : j < mid - i)
    (hfuel : j < fuel)
    (hread : ∀ p, p < j → (∃ x, la[i + p]? = some x) ∧
      (∃ y, lt[k + p]? = some y))
    (hfail : lt[k + j]? = none) :
    VecMergeRuns.mergeRunsDrainIFwd la lt fuel i k mid =
      .error .AssertFail := by
  induction j generalizing i k lt fuel with
  | zero =>
    have hi : i < mid := by omega
    obtain ⟨n, rfl, _⟩ := fuel_step_down 0 hfuel
    have hfail0 : lt[k]? = none := hfail
    simp only [VecMergeRuns.mergeRunsDrainIFwd, dite_eq_left hi, hfail0]
  | succ j ih =>
    have hi : i < mid := by omega
    obtain ⟨x, hx⟩ := (hread 0 (by omega)).1
    obtain ⟨y, hy⟩ := (hread 0 (by omega)).2
    obtain ⟨n, rfl, _⟩ := fuel_step_down (j + 1) hfuel
    have hx0 : la[i]? = some x := hx
    have hy0 : lt[k]? = some y := hy
    have hfail' : (lt.set k x)[(k + 1) + j]? = none := by
      have e : (k + 1) + j = k + (j + 1) := by omega
      have hne : k ≠ (k + 1) + j := by omega
      rw [List.getElem?_set_ne hne, e]
      exact hfail
    have hread' : ∀ p, p < j → (∃ x, la[(i + 1) + p]? = some x) ∧
        (∃ y, (lt.set k x)[(k + 1) + p]? = some y) := by
      intro p hp
      obtain ⟨x', hx'⟩ := (hread (p + 1) (by omega)).1
      obtain ⟨y', hy'⟩ := (hread (p + 1) (by omega)).2
      have e1 : (i + 1) + p = i + (p + 1) := by omega
      have e2 : (k + 1) + p = k + (p + 1) := by omega
      have hne : k ≠ (k + 1) + p := by omega
      refine ⟨⟨x', by rw [e1]; exact hx'⟩, y', ?_⟩
      rw [List.getElem?_set_ne hne, e2]
      exact hy'
    simp only [VecMergeRuns.mergeRunsDrainIFwd, dite_eq_left hi, hy0, hx0]
    exact ih (fuel := n) (lt := lt.set k x) (i := i + 1) (k := k + 1)
      (by omega) (by omega) (by omega) hread' hfail'

/-- Drain-`i` error leg, `la` fails first: the `j`-th `la`
    read is `none` while the `j`-th `tmp` read (checked first)
    and all prior reads succeed. -/
theorem VecMergeRuns.mergeRunsDrainIFwd_err_la (la lt : List (BitVec 32))
    (fuel i k mid j : Nat)
    (hle : i ≤ mid)
    (hlt : j < mid - i)
    (hfuel : j < fuel)
    (hread : ∀ p, p < j → (∃ x, la[i + p]? = some x) ∧
      (∃ y, lt[k + p]? = some y))
    (htmp : ∃ y, lt[k + j]? = some y)
    (hfail : la[i + j]? = none) :
    VecMergeRuns.mergeRunsDrainIFwd la lt fuel i k mid =
      .error .AssertFail := by
  induction j generalizing i k lt fuel with
  | zero =>
    have hi : i < mid := by omega
    obtain ⟨n, rfl, _⟩ := fuel_step_down 0 hfuel
    obtain ⟨y, hy⟩ := htmp
    have hy0 : lt[k]? = some y := hy
    have hfail0 : la[i]? = none := hfail
    simp only [VecMergeRuns.mergeRunsDrainIFwd, dite_eq_left hi, hy0, hfail0]
  | succ j ih =>
    have hi : i < mid := by omega
    obtain ⟨x, hx⟩ := (hread 0 (by omega)).1
    obtain ⟨y, hy⟩ := (hread 0 (by omega)).2
    obtain ⟨n, rfl, _⟩ := fuel_step_down (j + 1) hfuel
    have hx0 : la[i]? = some x := hx
    have hy0 : lt[k]? = some y := hy
    obtain ⟨z, hz⟩ := htmp
    have htmp' : ∃ y, (lt.set k x)[(k + 1) + j]? = some y := by
      have e2 : (k + 1) + j = k + (j + 1) := by omega
      have hne : k ≠ (k + 1) + j := by omega
      refine ⟨z, by rw [List.getElem?_set_ne hne, e2]; exact hz⟩
    have hfail' : la[(i + 1) + j]? = none := by
      have e1 : (i + 1) + j = i + (j + 1) := by omega
      rw [e1]; exact hfail
    have hread' : ∀ p, p < j → (∃ x, la[(i + 1) + p]? = some x) ∧
        (∃ y, (lt.set k x)[(k + 1) + p]? = some y) := by
      intro p hp
      obtain ⟨x', hx'⟩ := (hread (p + 1) (by omega)).1
      obtain ⟨y', hy'⟩ := (hread (p + 1) (by omega)).2
      have e1 : (i + 1) + p = i + (p + 1) := by omega
      have e2 : (k + 1) + p = k + (p + 1) := by omega
      have hne : k ≠ (k + 1) + p := by omega
      refine ⟨⟨x', by rw [e1]; exact hx'⟩, y', ?_⟩
      rw [List.getElem?_set_ne hne, e2]
      exact hy'
    simp only [VecMergeRuns.mergeRunsDrainIFwd, dite_eq_left hi, hy0, hx0]
    exact ih (fuel := n) (lt := lt.set k x) (i := i + 1) (k := k + 1)
      (by omega) (by omega) (by omega) hread' htmp' hfail'

/-- Drain-`j` ok leg: fuel covering the remaining `hi - j`
    copies plus succeeding reads discharge the drain at
    `j = hi`, with `k` advanced and length preserved.
    Template instance: sequential-threading callee (see
    VERIFYING.md Contracts). -/
theorem VecMergeRuns.mergeRunsDrainJFwd_ok (la lt : List (BitVec 32))
    (fuel j k hi : Nat)
    (hle : j ≤ hi)
    (hfuel : hi - j ≤ fuel)
    (hread_la : ∀ p, j ≤ p → p < hi → ∃ x, la[p]? = some x)
    (hread_lt : ∀ q, k ≤ q → q < k + (hi - j) → ∃ y, lt[q]? = some y) :
    ∃ k' lt', VecMergeRuns.mergeRunsDrainJFwd la lt fuel j k hi = .ok (hi, k', lt') ∧
      k' = k + (hi - j) ∧ lt'.length = lt.length := by
  induction fuel generalizing j k lt with
  | zero =>
    have him : j = hi := by omega
    subst him
    refine ⟨k, lt, ?_, ?_, rfl⟩
    · simp [VecMergeRuns.mergeRunsDrainJFwd]
    · simp
  | succ n ih =>
    by_cases hlt : j < hi
    · obtain ⟨x, hx⟩ := hread_la j (Nat.le_refl _) hlt
      obtain ⟨y, hy⟩ := hread_lt k (Nat.le_refl _) (by omega)
      have hfuel' : hi - (j + 1) ≤ n := by omega
      have ih' := ih (lt.set k x) (j + 1) (k + 1) (by omega) hfuel'
        (fun p h1 h2 => hread_la p (by omega) h2)
        (fun q h1 h2 => by
          obtain ⟨z, hz⟩ := hread_lt q (by omega) (by omega)
          exact ⟨z, by
            rw [List.getElem?_set_ne (show k ≠ q by omega)]
            exact hz⟩)
      obtain ⟨k', lt', heq, hk', hlen⟩ := ih'
      refine ⟨k', lt', ?_, ?_, ?_⟩
      · simp only [VecMergeRuns.mergeRunsDrainJFwd, dite_eq_left hlt, hy, hx]
        exact heq
      · omega
      · have hset : (lt.set k x).length = lt.length := List.length_set
        exact hlen.trans hset
    · have him : j = hi := by omega
      subst him
      refine ⟨k, lt, ?_, ?_, rfl⟩
      · simp only [VecMergeRuns.mergeRunsDrainJFwd, dite_eq_right hlt]
      · simp

/-- Drain-`j` error leg, `tmp` fails first: the `d`-th `tmp`
    read is `none` while all prior reads succeed. -/
theorem VecMergeRuns.mergeRunsDrainJFwd_err_lt (la lt : List (BitVec 32))
    (fuel j k hi d : Nat)
    (hle : j ≤ hi)
    (hlt : d < hi - j)
    (hfuel : d < fuel)
    (hread : ∀ p, p < d → (∃ x, la[j + p]? = some x) ∧
      (∃ y, lt[k + p]? = some y))
    (hfail : lt[k + d]? = none) :
    VecMergeRuns.mergeRunsDrainJFwd la lt fuel j k hi =
      .error .AssertFail := by
  induction d generalizing j k lt fuel with
  | zero =>
    have hi : j < hi := by omega
    obtain ⟨n, rfl, _⟩ := fuel_step_down 0 hfuel
    have hfail0 : lt[k]? = none := hfail
    simp only [VecMergeRuns.mergeRunsDrainJFwd, dite_eq_left hi, hfail0]
  | succ d ih =>
    have hi : j < hi := by omega
    obtain ⟨x, hx⟩ := (hread 0 (by omega)).1
    obtain ⟨y, hy⟩ := (hread 0 (by omega)).2
    obtain ⟨n, rfl, _⟩ := fuel_step_down (d + 1) hfuel
    have hx0 : la[j]? = some x := hx
    have hy0 : lt[k]? = some y := hy
    have hfail' : (lt.set k x)[(k + 1) + d]? = none := by
      have e : (k + 1) + d = k + (d + 1) := by omega
      have hne : k ≠ (k + 1) + d := by omega
      rw [List.getElem?_set_ne hne, e]
      exact hfail
    have hread' : ∀ p, p < d → (∃ x, la[(j + 1) + p]? = some x) ∧
        (∃ y, (lt.set k x)[(k + 1) + p]? = some y) := by
      intro p hp
      obtain ⟨x', hx'⟩ := (hread (p + 1) (by omega)).1
      obtain ⟨y', hy'⟩ := (hread (p + 1) (by omega)).2
      have e1 : (j + 1) + p = j + (p + 1) := by omega
      have e2 : (k + 1) + p = k + (p + 1) := by omega
      have hne : k ≠ (k + 1) + p := by omega
      refine ⟨⟨x', by rw [e1]; exact hx'⟩, y', ?_⟩
      rw [List.getElem?_set_ne hne, e2]
      exact hy'
    simp only [VecMergeRuns.mergeRunsDrainJFwd, dite_eq_left hi, hy0, hx0]
    exact ih (fuel := n) (lt := lt.set k x) (j := j + 1) (k := k + 1)
      (by omega) (by omega) (by omega) hread' hfail'

/-- Main-loop ok leg: fuel covering the remaining
    `(mid - i) + (hi - j)` iterations plus succeeding reads
    discharges the merge at an exit (`i = mid` or `j = hi`),
    with `k` advanced by the consumed pairs and length
    preserved. Template instance: sequential-threading callee. -/
theorem VecMergeRuns.mergeRunsMainFwd_ok (la lt : List (BitVec 32))
    (fuel i j k mid hi : Nat)
    (hle_i : i ≤ mid) (hle_j : j ≤ hi)
    (hfuel : (mid - i) + (hi - j) ≤ fuel)
    (hread_i : ∀ p, i ≤ p → p < mid → ∃ x, la[p]? = some x)
    (hread_j : ∀ p, j ≤ p → p < hi → ∃ x, la[p]? = some x)
    (hread_lt : ∀ q, k ≤ q → q < k + ((mid - i) + (hi - j)) →
      ∃ y, lt[q]? = some y) :
    ∃ i' j' k' lt',
      VecMergeRuns.mergeRunsMainFwd la lt fuel i j k mid hi =
        .ok (i', j', k', lt') ∧
      (i' = mid ∨ j' = hi) ∧ i' ≤ mid ∧ j' ≤ hi ∧
      i ≤ i' ∧ j ≤ j' ∧
      k' = k + ((i' - i) + (j' - j)) ∧ lt'.length = lt.length := by
  induction fuel generalizing i j k lt with
  | zero =>
    have him : i = mid := by omega
    have hjm : j = hi := by omega
    rw [him, hjm]
    refine ⟨mid, hi, k, lt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
    · simp [VecMergeRuns.mergeRunsMainFwd]
    · exact Or.inl rfl
    · exact Nat.le_refl _
    · exact Nat.le_refl _
    · exact Nat.le_refl _
    · exact Nat.le_refl _
    · simp
  | succ n ih =>
    by_cases hi_lt : i < mid
    · by_cases hj_lt : j < hi
      · obtain ⟨x, hx⟩ := hread_i i (Nat.le_refl _) hi_lt
        obtain ⟨z, hz⟩ := hread_j j (Nat.le_refl _) hj_lt
        obtain ⟨w, hw⟩ := hread_lt k (Nat.le_refl _) (by omega)
        by_cases hslt : x.slt z = true
        · have ih' := ih (lt.set k x) (i + 1) j (k + 1)
            (by omega) (by omega) (by omega)
            (fun p h1 h2 => hread_i p (by omega) h2)
            (fun p h1 h2 => hread_j p h1 h2)
            (fun q h1 h2 => by
              obtain ⟨v, hv⟩ := hread_lt q (by omega) (by omega)
              exact ⟨v, by
                rw [List.getElem?_set_ne (show k ≠ q by omega)]
                exact hv⟩)
          obtain ⟨i', j', k', lt', heq, hexit, hbi, hbj, hmi', hmj', hk', hlen⟩ := ih'
          refine ⟨i', j', k', lt', ?_, hexit, hbi, hbj, ?_, ?_, ?_, ?_⟩
          · simp only [VecMergeRuns.mergeRunsMainFwd, dite_eq_left hi_lt,
              dite_eq_left hj_lt, hw, hx, hz]
            rw [ite_eq_left hslt]
            exact heq
          · omega
          · omega
          · omega
          · have hset : (lt.set k x).length = lt.length := List.length_set
            exact hlen.trans hset
        · have ih' := ih (lt.set k z) i (j + 1) (k + 1)
            (by omega) (by omega) (by omega)
            (fun p h1 h2 => hread_i p h1 h2)
            (fun p h1 h2 => hread_j p (by omega) h2)
            (fun q h1 h2 => by
              obtain ⟨v, hv⟩ := hread_lt q (by omega) (by omega)
              exact ⟨v, by
                rw [List.getElem?_set_ne (show k ≠ q by omega)]
                exact hv⟩)
          obtain ⟨i', j', k', lt', heq, hexit, hbi, hbj, hmi', hmj', hk', hlen⟩ := ih'
          refine ⟨i', j', k', lt', ?_, hexit, hbi, hbj, ?_, ?_, ?_, ?_⟩
          · simp only [VecMergeRuns.mergeRunsMainFwd, dite_eq_left hi_lt,
              dite_eq_left hj_lt, hw, hx, hz]
            rw [ite_eq_right hslt]
            exact heq
          · exact hmi'
          · omega
          · omega
          · have hset : (lt.set k z).length = lt.length := List.length_set
            exact hlen.trans hset
      · have hjm : j = hi := by omega
        rw [hjm] at hj_lt ⊢
        refine ⟨i, hi, k, lt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
        · simp only [VecMergeRuns.mergeRunsMainFwd, dite_eq_left hi_lt,
            dite_eq_right hj_lt]
        · exact Or.inr rfl
        · exact hle_i
        · exact Nat.le_refl _
        · exact Nat.le_refl _
        · exact Nat.le_refl _
        · simp
    · have him : i = mid := by omega
      rw [him] at hi_lt ⊢
      refine ⟨mid, j, k, lt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
      · simp only [VecMergeRuns.mergeRunsMainFwd, dite_eq_right hi_lt]
      · exact Or.inl rfl
      · exact Nat.le_refl _
      · exact hle_j
      · exact Nat.le_refl _
      · exact Nat.le_refl _
      · simp

/-- Main-loop error leg, `tmp` fails first: with both cursors
    live, a missing `tmp` word fails immediately. -/
theorem VecMergeRuns.mergeRunsMainFwd_err_lt (la lt : List (BitVec 32))
    (fuel i j k mid hi : Nat)
    (hi_lt : i < mid) (hj_lt : j < hi)
    (hfail : lt[k]? = none) :
    VecMergeRuns.mergeRunsMainFwd la lt (fuel + 1) i j k mid hi =
      .error .AssertFail := by
  simp only [VecMergeRuns.mergeRunsMainFwd, dite_eq_left hi_lt,
    dite_eq_left hj_lt, hfail]

/-- Main-loop error leg, `la[i]` fails: `tmp` ok, left read
    missing. -/
theorem VecMergeRuns.mergeRunsMainFwd_err_la (la lt : List (BitVec 32))
    (fuel i j k mid hi : Nat)
    (hi_lt : i < mid) (hj_lt : j < hi)
    (htmp : ∃ y, lt[k]? = some y)
    (hfail : la[i]? = none) :
    VecMergeRuns.mergeRunsMainFwd la lt (fuel + 1) i j k mid hi =
      .error .AssertFail := by
  obtain ⟨y, hy⟩ := htmp
  simp only [VecMergeRuns.mergeRunsMainFwd, dite_eq_left hi_lt,
    dite_eq_left hj_lt, hy, hfail]

/-- Main-loop error leg, `la[j]` fails: `tmp` and left read ok,
    right read missing. -/
theorem VecMergeRuns.mergeRunsMainFwd_err_la_j (la lt : List (BitVec 32))
    (fuel i j k mid hi : Nat)
    (hi_lt : i < mid) (hj_lt : j < hi)
    (htmp : ∃ y, lt[k]? = some y)
    (ha : ∃ x, la[i]? = some x)
    (hfail : la[j]? = none) :
    VecMergeRuns.mergeRunsMainFwd la lt (fuel + 1) i j k mid hi =
      .error .AssertFail := by
  obtain ⟨y, hy⟩ := htmp
  obtain ⟨x, hx⟩ := ha
  simp only [VecMergeRuns.mergeRunsMainFwd, dite_eq_left hi_lt,
    dite_eq_left hj_lt, hy, hx, hfail]

/-- Entry ok leg: sequential threading — main, drain-`i`,
    drain-`j`, one equation per composer `callRet`, exactly the
    U2 `addCaller` shape at three calls. Template instance. -/
theorem VecMergeRuns.mergeRunsFwd_ok (la lt : List (BitVec 32))
    (lo mid hi : Nat) (i j k k' k'' : Nat)
    (lt' lt'' lt''' : List (BitVec 32))
    (hmain : VecMergeRuns.mergeRunsMainFwd la lt
      ((mid - lo) + (hi - mid)) lo mid lo mid hi = .ok (i, j, k, lt'))
    (hdi : VecMergeRuns.mergeRunsDrainIFwd la lt' (mid - i) i k mid =
      .ok (mid, k', lt''))
    (hdj : VecMergeRuns.mergeRunsDrainJFwd la lt'' (hi - j) j k' hi =
      .ok (hi, k'', lt''')) :
    VecMergeRuns.mergeRunsFwd la lt lo mid hi =
      .ok (.stdVecVal lt''') := by
  simp only [VecMergeRuns.mergeRunsFwd, hmain, hdi, hdj]

/-- Entry err leg, main fails: first-failure-wins matches the
    forward's binds (failed callee equation as hypothesis). -/
theorem VecMergeRuns.mergeRunsFwd_err_main (la lt : List (BitVec 32))
    (lo mid hi : Nat) (e : Panic)
    (hmain : VecMergeRuns.mergeRunsMainFwd la lt
      ((mid - lo) + (hi - mid)) lo mid lo mid hi = .error e) :
    VecMergeRuns.mergeRunsFwd la lt lo mid hi = .error e := by
  simp only [VecMergeRuns.mergeRunsFwd, hmain]

/-- Entry err leg, drain-`i` fails: main ok, drain-`i` errors. -/
theorem VecMergeRuns.mergeRunsFwd_err_drainI (la lt : List (BitVec 32))
    (lo mid hi : Nat) (i j k : Nat) (lt' : List (BitVec 32))
    (e : Panic)
    (hmain : VecMergeRuns.mergeRunsMainFwd la lt
      ((mid - lo) + (hi - mid)) lo mid lo mid hi = .ok (i, j, k, lt'))
    (hdi : VecMergeRuns.mergeRunsDrainIFwd la lt' (mid - i) i k mid =
      .error e) :
    VecMergeRuns.mergeRunsFwd la lt lo mid hi = .error e := by
  simp only [VecMergeRuns.mergeRunsFwd, hmain, hdi]

/-- Entry err leg, drain-`j` fails: main and drain-`i` ok,
    drain-`j` errors. -/
theorem VecMergeRuns.mergeRunsFwd_err_drainJ (la lt : List (BitVec 32))
    (lo mid hi : Nat) (i j k k' : Nat)
    (lt' lt'' : List (BitVec 32)) (e : Panic)
    (hmain : VecMergeRuns.mergeRunsMainFwd la lt
      ((mid - lo) + (hi - mid)) lo mid lo mid hi = .ok (i, j, k, lt'))
    (hdi : VecMergeRuns.mergeRunsDrainIFwd la lt' (mid - i) i k mid =
      .ok (mid, k', lt''))
    (hdj : VecMergeRuns.mergeRunsDrainJFwd la lt'' (hi - j) j k' hi =
      .error e) :
    VecMergeRuns.mergeRunsFwd la lt lo mid hi = .error e := by
  simp only [VecMergeRuns.mergeRunsFwd, hmain, hdi, hdj]

/-- Drain-`j` error leg, `la` fails first: the `d`-th `la`
    read is `none` while the `d`-th `tmp` read (checked first)
    and all prior reads succeed. -/
theorem VecMergeRuns.mergeRunsDrainJFwd_err_la (la lt : List (BitVec 32))
    (fuel j k hi d : Nat)
    (hle : j ≤ hi)
    (hlt : d < hi - j)
    (hfuel : d < fuel)
    (hread : ∀ p, p < d → (∃ x, la[j + p]? = some x) ∧
      (∃ y, lt[k + p]? = some y))
    (htmp : ∃ y, lt[k + d]? = some y)
    (hfail : la[j + d]? = none) :
    VecMergeRuns.mergeRunsDrainJFwd la lt fuel j k hi =
      .error .AssertFail := by
  induction d generalizing j k lt fuel with
  | zero =>
    have hi : j < hi := by omega
    obtain ⟨n, rfl, _⟩ := fuel_step_down 0 hfuel
    obtain ⟨y, hy⟩ := htmp
    have hy0 : lt[k]? = some y := hy
    have hfail0 : la[j]? = none := hfail
    simp only [VecMergeRuns.mergeRunsDrainJFwd, dite_eq_left hi, hy0, hfail0]
  | succ d ih =>
    have hi : j < hi := by omega
    obtain ⟨x, hx⟩ := (hread 0 (by omega)).1
    obtain ⟨y, hy⟩ := (hread 0 (by omega)).2
    obtain ⟨n, rfl, _⟩ := fuel_step_down (d + 1) hfuel
    have hx0 : la[j]? = some x := hx
    have hy0 : lt[k]? = some y := hy
    obtain ⟨z, hz⟩ := htmp
    have htmp' : ∃ y, (lt.set k x)[(k + 1) + d]? = some y := by
      have e2 : (k + 1) + d = k + (d + 1) := by omega
      have hne : k ≠ (k + 1) + d := by omega
      refine ⟨z, by rw [List.getElem?_set_ne hne, e2]; exact hz⟩
    have hfail' : la[(j + 1) + d]? = none := by
      have e1 : (j + 1) + d = j + (d + 1) := by omega
      rw [e1]; exact hfail
    have hread' : ∀ p, p < d → (∃ x, la[(j + 1) + p]? = some x) ∧
        (∃ y, (lt.set k x)[(k + 1) + p]? = some y) := by
      intro p hp
      obtain ⟨x', hx'⟩ := (hread (p + 1) (by omega)).1
      obtain ⟨y', hy'⟩ := (hread (p + 1) (by omega)).2
      have e1 : (j + 1) + p = j + (p + 1) := by omega
      have e2 : (k + 1) + p = k + (p + 1) := by omega
      have hne : k ≠ (k + 1) + p := by omega
      refine ⟨⟨x', by rw [e1]; exact hx'⟩, y', ?_⟩
      rw [List.getElem?_set_ne hne, e2]
      exact hy'
    simp only [VecMergeRuns.mergeRunsDrainJFwd, dite_eq_left hi, hy0, hx0]
    exact ih (fuel := n) (lt := lt.set k x) (j := j + 1) (k := k + 1)
      (by omega) (by omega) (by omega) hread' htmp' hfail'

/-! ## M2: out-of-place checked transform (`vec_transform_add`).

Forward contracts for `transformAddFwd`: the ok leg (all reads
succeed, all checked adds succeed) pins the elementwise result and
length; the two per-site err legs pin short-`out` (`AssertFail`)
and checked-add failure (propagated). Fuel inductions generalizing
the index and the output words, threading reads through `set`
(the `getElem?_set_ne` idiom). -/

/-- Transform ok leg: every position reads on both sides and every
    checked add succeeds. Positions before `i` are already done (the
    frame: `lo` and `lo'` agree there); positions from `i` get the
    checked sum. -/
theorem transformAddFwd_ok (li lo : List (BitVec 32)) (c : BitVec 32)
    (fuel i : Nat)
    (hle : i ≤ li.length)
    (hfuel : li.length - i ≤ fuel)
    (hread_lo : ∀ p, p < li.length → ∃ z, lo[p]? = some z)
    (hadd : ∀ p, i ≤ p → p < li.length →
      ∃ x y, li[p]? = some x ∧ checkedAddI32 x c = .ok y) :
    ∃ lo', transformAddFwd li c lo fuel i = .ok (li.length, lo') ∧
      lo'.length = lo.length ∧
      (∀ p, p < i → p < li.length →
        ∃ z, lo[p]? = some z ∧ lo'[p]? = some z) ∧
      (∀ p, i ≤ p → p < li.length →
        ∃ x y, li[p]? = some x ∧ lo'[p]? = some y ∧
          checkedAddI32 x c = .ok y) := by
  induction fuel generalizing i lo with
  | zero =>
    have him : i = li.length := by omega
    subst him
    refine ⟨lo, ?_, rfl, ?_, ?_⟩
    · simp [transformAddFwd]
    · intro p h1 h2
      obtain ⟨z, hz⟩ := hread_lo p h2
      exact ⟨z, hz, hz⟩
    · intro p h1 h2
      exact (by omega : False).elim
  | succ n ih =>
    by_cases hlt : i < li.length
    · obtain ⟨z, hz⟩ := hread_lo i hlt
      obtain ⟨x, y, hx, hy⟩ := hadd i (Nat.le_refl _) hlt
      have hfuel' : li.length - (i + 1) ≤ n := by omega
      have hread_lo' : ∀ p, p < li.length →
          ∃ z, ((lo.set i y)[p]? = some z) := by
        intro p hp
        by_cases hpi : p = i
        · rw [hpi]
          have hlo : i < lo.length := by
            by_cases h : i < lo.length
            · exact h
            · have hle : lo.length ≤ i := by omega
              have hnone : lo[i]? = none := List.getElem?_eq_none hle
              rw [hnone] at hz
              simp at hz
          exact ⟨y, List.getElem?_set_self hlo⟩
        · obtain ⟨z, hz⟩ := hread_lo p hp
          exact ⟨z, by
            rw [List.getElem?_set_ne (show i ≠ p by omega)]
            exact hz⟩
      have hadd' : ∀ p, i + 1 ≤ p → p < li.length →
          ∃ x y, li[p]? = some x ∧ checkedAddI32 x c = .ok y := by
        intro p h1 h2
        exact hadd p (by omega) h2
      obtain ⟨lo', heq, hlen', hframe', hele'⟩ :=
        ih (i := i + 1) (lo := lo.set i y) (by omega) hfuel' hread_lo' hadd'
      refine ⟨lo', ?_, ?_, ?_, ?_⟩
      · simp only [transformAddFwd, dite_eq_left hlt, hz, hx, hy]
        exact heq
      · exact hlen'.trans List.length_set
      · intro p h1 h2
        obtain ⟨z, hz1, hz2⟩ := hframe' p (by omega) h2
        have hlo : lo[p]? = some z := by
          have hne : i ≠ p := by omega
          rw [List.getElem?_set_ne hne] at hz1
          exact hz1
        exact ⟨z, hlo, hz2⟩
      · intro p h1 h2
        by_cases hpi : p = i
        · have hpi' : i = p := hpi.symm
          subst hpi'
          obtain ⟨w, hw1, hw2⟩ := hframe' i (by omega) h2
          have hbound : i < lo.length := by
            by_cases h : i < lo.length
            · exact h
            · have hle : lo.length ≤ i := by omega
              have hnone : lo[i]? = none := List.getElem?_eq_none hle
              rw [hnone] at hz
              simp at hz
          have hss : (lo.set i y)[i]? = some y :=
            List.getElem?_set_self hbound
          have hwy : w = y := by
            rw [hss] at hw1
            cases hw1
            rfl
          rw [hwy] at hw2
          exact ⟨x, y, hx, hw2, hy⟩
        · exact hele' p (by omega) h2
    · have him : i = li.length := by omega
      subst him
      refine ⟨lo, ?_, rfl, ?_, ?_⟩
      · have hneg : ¬ li.length < li.length := by omega
        simp only [transformAddFwd, dite_eq_right hneg]
      · intro p h1 h2
        obtain ⟨z, hz⟩ := hread_lo p h2
        exact ⟨z, hz, hz⟩
      · intro p h1 h2
        exact (by omega : False).elim

/-- Transform error leg, short `out`: position `j` is the first
    missing write while all prior reads and adds succeed. -/
theorem transformAddFwd_err_short (li lo : List (BitVec 32))
    (c : BitVec 32) (fuel i j : Nat)
    (hj : j < li.length)
    (hle : i ≤ j) (hfuel : j - i + 1 ≤ fuel)
    (hreads : ∀ p, i ≤ p → p < j → ∃ z, lo[p]? = some z)
    (hadds : ∀ p, i ≤ p → p < j →
      ∃ x y, li[p]? = some x ∧ checkedAddI32 x c = .ok y)
    (hmiss : lo[j]? = none) :
    transformAddFwd li c lo fuel i = .error .AssertFail := by
  induction fuel generalizing i lo with
  | zero => exact (by omega : False).elim
  | succ n ih =>
    by_cases hij : i = j
    · subst hij
      simp only [transformAddFwd, dite_eq_left hj, hmiss]
    · have hlt : i < j := by omega
      have hlt_len : i < li.length := by omega
      obtain ⟨z, hz⟩ := hreads i (Nat.le_refl _) hlt
      obtain ⟨x, y, hx, hy⟩ := hadds i (Nat.le_refl _) hlt
      have hfuel' : j - (i + 1) + 1 ≤ n := by omega
      have hreads' : ∀ p, i + 1 ≤ p → p < j →
          ∃ z, ((lo.set i y)[p]? = some z) := by
        intro p h1 h2
        obtain ⟨z, hz⟩ := hreads p (by omega) h2
        exact ⟨z, by
          rw [List.getElem?_set_ne (show i ≠ p by omega)]
          exact hz⟩
      have hadds' : ∀ p, i + 1 ≤ p → p < j →
          ∃ x y, li[p]? = some x ∧ checkedAddI32 x c = .ok y := by
        intro p h1 h2
        exact hadds p (by omega) h2
      have heq := ih (i := i + 1) (lo := lo.set i y) (by omega) hfuel'
        hreads' hadds' (by
          rw [List.getElem?_set_ne (show i ≠ j by omega)]
          exact hmiss)
      simp only [transformAddFwd, dite_eq_left hlt_len, hz, hx, hy]
      exact heq

/-- Transform error leg, checked-add failure at `j`: all prior
    positions read and add cleanly; the `j`-th add propagates. -/
theorem transformAddFwd_err_add (li lo : List (BitVec 32))
    (c : BitVec 32) (fuel i j : Nat) (e : Panic)
    (hj : j < li.length)
    (hle : i ≤ j) (hfuel : j - i + 1 ≤ fuel)
    (hreads : ∀ p, i ≤ p → p ≤ j → ∃ z, lo[p]? = some z)
    (hadds : ∀ p, i ≤ p → p < j →
      ∃ x y, li[p]? = some x ∧ checkedAddI32 x c = .ok y)
    (hx : ∃ x, li[j]? = some x)
    (herr : ∀ x, li[j]? = some x → checkedAddI32 x c = .error e) :
    transformAddFwd li c lo fuel i = .error e := by
  induction fuel generalizing i lo with
  | zero => exact (by omega : False).elim
  | succ n ih =>
    by_cases hij : i = j
    · subst hij
      obtain ⟨x, hx'⟩ := hx
      obtain ⟨z, hz⟩ := hreads i (Nat.le_refl _) (Nat.le_refl _)
      simp only [transformAddFwd, dite_eq_left hj, hz, hx', herr x hx']
    · have hlt : i < j := by omega
      have hlt_len : i < li.length := by omega
      obtain ⟨z, hz⟩ := hreads i (Nat.le_refl _) (by omega)
      obtain ⟨x, y, hx, hy⟩ := hadds i (Nat.le_refl _) hlt
      have hfuel' : j - (i + 1) + 1 ≤ n := by omega
      have hreads' : ∀ p, i + 1 ≤ p → p ≤ j →
          ∃ z, ((lo.set i y)[p]? = some z) := by
        intro p h1 h2
        obtain ⟨z, hz⟩ := hreads p (by omega) h2
        exact ⟨z, by
          rw [List.getElem?_set_ne (show i ≠ p by omega)]
          exact hz⟩
      have hadds' : ∀ p, i + 1 ≤ p → p < j →
          ∃ x y, li[p]? = some x ∧ checkedAddI32 x c = .ok y := by
        intro p h1 h2
        exact hadds p (by omega) h2
      have heq := ih (i := i + 1) (lo := lo.set i y) (by omega) hfuel'
        hreads' hadds'
      simp only [transformAddFwd, dite_eq_left hlt_len, hz, hx, hy]
      exact heq

/-! ## P2-M3: in-place partition forward contract -/

/-- M3 forward contract, ok leg: the scan runs to `l.length` with
    full reads (single leg — the kernel is total: every access is
    guard-justified, so the `none` arms never fire in-invariant).
    Fuel induction threading the store bound `s ≤ i`. -/
theorem partitionFwd_ok (pivot : BitVec 32) (l : List (BitVec 32))
    (fuel i s : Nat)
    (hle : i ≤ l.length) (hsle : s ≤ i)
    (hF : l.length - i ≤ fuel)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x) :
    ∃ s' l', partitionFwd pivot l fuel i s = .ok (l.length, s', l') := by
  induction fuel generalizing l i s with
  | zero =>
    have him : i = l.length := by omega
    subst him
    exact ⟨s, l, by simp [partitionFwd]⟩
  | succ n ih =>
    by_cases hlt : i < l.length
    · obtain ⟨x, hx⟩ := hread i hlt
      have hslt : s < l.length := by omega
      obtain ⟨w, hw⟩ := hread s hslt
      have hF' : l.length - (i + 1) ≤ n := by omega
      have hF'_take : ((l.set i w).set s x).length - (i + 1) ≤ n := by
        have : ((l.set i w).set s x).length = l.length := by
          simp [List.length_set]
        omega
      have hread' : ∀ p, p < ((l.set i w).set s x).length →
          ∃ y, ((l.set i w).set s x)[p]? = some y := by
        intro p hp
        have hplen : p < l.length := by
          have : ((l.set i w).set s x).length = l.length := by
            simp [List.length_set]
          omega
        by_cases hpi : p = i
        · rw [hpi]
          by_cases hsi : s = i
          · rw [hsi]
            exact ⟨x, List.getElem?_set_self (by
              rw [List.length_set]; exact hlt)⟩
          · exact ⟨w, by
              rw [List.getElem?_set_ne (show s ≠ i by omega)]
              exact List.getElem?_set_self hlt⟩
        · by_cases hps : p = s
          · rw [hps]
            exact ⟨x, List.getElem?_set_self (by
              rw [List.length_set]; exact hslt)⟩
          · obtain ⟨y, hy⟩ := hread p hplen
            exact ⟨y, by
              rw [List.getElem?_set_ne (show s ≠ p by omega),
                List.getElem?_set_ne (show i ≠ p by omega)]
              exact hy⟩
      by_cases htake : x.slt pivot
      · have hle' : i + 1 ≤ ((l.set i w).set s x).length := by
          have : ((l.set i w).set s x).length = l.length := by
            simp [List.length_set]
          omega
        have hsle' : s + 1 ≤ i + 1 := by omega
        obtain ⟨s'', l'', heq⟩ := ih ((l.set i w).set s x) (i + 1)
          (s + 1) hle' hsle' hF'_take hread'
        have hlen : ((l.set i w).set s x).length = l.length := by
          simp [List.length_set]
        rw [hlen] at heq
        refine ⟨s'', l'', ?_⟩
        simp only [partitionFwd, dite_eq_left hlt, hx, htake, hw]
        exact heq
      · have hle' : i + 1 ≤ l.length := by omega
        have hsle' : s ≤ i + 1 := by omega
        obtain ⟨s'', l'', heq⟩ := ih l (i + 1) s hle' hsle' hF' hread
        refine ⟨s'', l'', ?_⟩
        simp only [partitionFwd, dite_eq_left hlt, hx, htake]
        exact heq
    · have him : i = l.length := by omega
      subst him
      have hneg : ¬ l.length < l.length := by omega
      refine ⟨s, l, ?_⟩
      simp only [partitionFwd, dite_eq_right hneg]

/-! ## P2-M4: selection-sort forward contracts -/

/-- M4 leaf contract, ok leg: the min-scan runs to `l.length`
    with full reads (single leg — the kernel is total: every access
    is guard-justified, so the `none` arms never fire
    in-invariant). The running minimum stays in-bounds (needed by
    the outer swap). Fuel induction threading `m < len`. -/
theorem minIndexFwd_ok (l : List (BitVec 32))
    (fuel j m : Nat)
    (hm : m < l.length) (hle : j ≤ l.length)
    (hF : l.length - j ≤ fuel)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x) :
    ∃ m' j', VecSelectionSort.minIndexFwd l fuel j m =
      .ok (m', j') ∧ m' < l.length := by
  induction fuel generalizing l j m with
  | zero =>
    have him : j = l.length := by omega
    subst him
    exact ⟨m, l.length, by simp [VecSelectionSort.minIndexFwd], hm⟩
  | succ n ih =>
    by_cases hlt : j < l.length
    · obtain ⟨x, hx⟩ := hread j hlt
      obtain ⟨y, hy⟩ := hread m hm
      have hF' : l.length - (j + 1) ≤ n := by omega
      have hle' : j + 1 ≤ l.length := by omega
      by_cases htake : x.slt y
      · obtain ⟨m'', j'', heq, hm''⟩ := ih l (j + 1) j hlt hle' hF' hread
        refine ⟨m'', j'', ?_, hm''⟩
        simp only [VecSelectionSort.minIndexFwd, dite_eq_left hlt,
          hx, hy, htake]
        exact heq
      · obtain ⟨m'', j'', heq, hm''⟩ := ih l (j + 1) m hm hle' hF' hread
        refine ⟨m'', j'', ?_, hm''⟩
        have hskip : (x.slt y) = false := by
          cases h : x.slt y with
          | true => exact absurd h htake
          | false => rfl
        simp only [VecSelectionSort.minIndexFwd, dite_eq_left hlt,
          hx, hy, hskip]
        exact heq
    · have him : j = l.length := by omega
      subst him
      refine ⟨m, l.length, ?_, hm⟩
      simp only [VecSelectionSort.minIndexFwd, dite_eq_right hlt]

/-- M4 outer contract, ok leg: the index scan runs to `l.length`
    with full reads (single leg — the kernel is total). The inner
    scan re-spends the full inner budget every iteration
    (self-contained leaf); the swap preserves length. Fuel
    induction threading the inner sufficiency premise. -/
theorem selectionSortFwd_ok (l : List (BitVec 32))
    (fuel inner i : Nat)
    (hle : i ≤ l.length)
    (hF : l.length - i ≤ fuel)
    (hG : l.length - (i + 1) ≤ inner)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x) :
    ∃ i' l', VecSelectionSort.selectionSortFwd l fuel inner i =
      .ok (i', l') := by
  induction fuel generalizing l i with
  | zero =>
    have him : i = l.length := by omega
    subst him
    exact ⟨l.length, l, by simp [VecSelectionSort.selectionSortFwd]⟩
  | succ n ih =>
    by_cases hlt : i < l.length
    · obtain ⟨x, hx⟩ := hread i hlt
      have hF' : l.length - (i + 1) ≤ n := by omega
      have hle' : i + 1 ≤ l.length := by omega
      obtain ⟨m, j', hmin, hm'⟩ :=
        minIndexFwd_ok l inner (i + 1) i hlt (by omega) hG hread
      obtain ⟨y, hy⟩ := hread m hm'
      have hlen : ((l.set i y).set m x).length = l.length := by
        simp [List.length_set]
      have hle'' : i + 1 ≤ ((l.set i y).set m x).length := by omega
      have hF'' : ((l.set i y).set m x).length - (i + 1) ≤ n := by omega
      have hG' : ((l.set i y).set m x).length - (i + 1 + 1) ≤ inner := by
        omega
      have hread' : ∀ p, p < ((l.set i y).set m x).length →
          ∃ z, ((l.set i y).set m x)[p]? = some z := by
        intro p hp
        have hplen : p < l.length := by omega
        by_cases hpi : p = i
        · rw [hpi]
          by_cases hmi : m = i
          · rw [hmi]; exact ⟨x, List.getElem?_set_self (by
            rw [List.length_set]; exact hlt)⟩
          · exact ⟨y, by
              rw [List.getElem?_set_ne (show m ≠ i by omega)]
              exact List.getElem?_set_self hlt⟩
        · by_cases hpm : p = m
          · rw [hpm]
            exact ⟨x, List.getElem?_set_self (by
              rw [List.length_set]; exact hm')⟩
          · obtain ⟨z, hz⟩ := hread p hplen
            exact ⟨z, by
              rw [List.getElem?_set_ne (show m ≠ p by omega),
                List.getElem?_set_ne (show i ≠ p by omega)]
              exact hz⟩
      obtain ⟨i'', l'', heq⟩ := ih ((l.set i y).set m x) (i + 1)
        hle'' hF'' hG' hread'
      refine ⟨i'', l'', ?_⟩
      simp only [VecSelectionSort.selectionSortFwd, dite_eq_left hlt,
        hmin, hx, hy]
      exact heq
    · have him : i = l.length := by omega
      subst him
      refine ⟨l.length, l, ?_⟩
      have hneg : ¬ l.length < l.length := by omega
      simp only [VecSelectionSort.selectionSortFwd, dite_eq_right hneg]

/-! ## M5b: selection-sort bridge (?-world take/drop surgery).

The outer loop keeps a sorted prefix with everything in the prefix
`≤` everything in the suffix (positional form, so every step closes
by `getElem?_set_ne` / `getElem?_set_self` + `omega`). The swap
preserves `Perm` via an explicit take/drop middle-swap. -/

/-- Split a list at a known `getElem?` position. -/
theorem take_cons_drop (l : List (BitVec 32)) (i : Nat) (x : BitVec 32)
    (hx : l[i]? = some x) :
    l.take i ++ x :: l.drop (i + 1) = l := by
  induction l generalizing i with
  | nil => simp at hx
  | cons y ys ih =>
    cases i with
    | zero =>
      simp only [List.take_zero,
        List.getElem?_cons_zero] at hx ⊢
      simp only [List.nil_append, List.drop_succ_cons,
        List.drop_zero] at ⊢
      rw [Option.some_inj.mp hx]
    | succ i =>
      simp only [List.take_succ_cons, List.drop_succ_cons,
        List.getElem?_cons_succ] at hx ⊢
      have hih := ih i hx
      simp only [List.cons_append]
      rw [hih]

/-- A single write splices one word into the take/drop split. -/
theorem set_take_cons_drop (l : List (BitVec 32)) (i : Nat) (y : BitVec 32)
    (hi : i < l.length) :
    l.set i y = l.take i ++ y :: l.drop (i + 1) := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp
    | succ i =>
      simp only [List.set_cons_succ, List.take_succ_cons,
        List.drop_succ_cons, List.length_cons] at hi ⊢
      have hih := ih i (by omega)
      simp only [List.cons_append] at ⊢
      rw [hih]

/-- Take through an appended cons (strict bound, so the head lands
    inside). Proved by induction to avoid `take_append` shape risk. -/
theorem take_append_cons (A : List (BitVec 32)) (x : BitVec 32)
    (R : List (BitVec 32)) (m' : Nat) (hlt : A.length < m') :
    (A ++ x :: R).take m' = A ++ x :: (R.take (m' - A.length - 1)) := by
  induction A generalizing m' with
  | nil =>
    cases m' with
    | zero => simp at hlt
    | succ m' =>
      simp only [List.nil_append, List.take_succ_cons,
        List.length_nil] at ⊢
      have harith : m' + 1 - 0 - 1 = m' := by omega
      rw [harith]
  | cons a As ih =>
    cases m' with
    | zero => simp at hlt
    | succ m' =>
      simp only [List.cons_append, List.take_succ_cons,
        List.length_cons] at hlt ⊢
      have hih := ih m' (by omega)
      rw [hih]
      have harith : m' + 1 - (As.length + 1) - 1 = m' - As.length - 1 := by
        omega
      rw [harith]

/-- A write at the append boundary splices the head of the tail. -/
theorem set_append_length (A : List (BitVec 32)) (rest : List (BitVec 32))
    (y : BitVec 32) :
    (A ++ rest).set A.length y = A ++ rest.set 0 y := by
  induction A with
  | nil => simp
  | cons a As ih =>
    simp only [List.cons_append, List.length_cons,
      List.set_cons_succ, ih]

/-- Positional sortedness (all earlier positions `≤` all later ones)
    is `Pairwise`. -/
theorem pairwise_of_positional (l : List (BitVec 32))
    (h : ∀ (p q : Nat) (a b : BitVec 32), p < q → l[p]? = some a →
      l[q]? = some b → (b.slt a) = false) :
    l.Pairwise (fun (a b : BitVec 32) => b.slt a = false) := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons x xs ih =>
    rw [List.pairwise_cons]
    refine ⟨?_, ih (fun p q a b hpq hpa hqb => ?_)⟩
    · intro b hb
      obtain ⟨q, hq⟩ := (List.mem_iff_getElem?).mp hb
      have h0 : (x :: xs)[0]? = some x := by simp
      exact h 0 (q + 1) x b (by omega) h0 (by simpa using hq)
    · exact h (p + 1) (q + 1) a b (by omega)
        (by simpa using hpa) (by simpa using hqb)

/-- Middle-swap `Perm`: exchanging the heads across a middle block. -/
theorem middle_swap (T : List (BitVec 32)) (x y : BitVec 32)
    (S : List (BitVec 32)) :
    List.Perm (x :: (T ++ (y :: S))) ((y :: T) ++ (x :: S)) := by
  have q1 : List.Perm (T ++ (y :: S)) (y :: (T ++ S)) :=
    List.perm_middle
  have qx := List.Perm.cons x q1
  have qs : List.Perm (x :: (y :: (T ++ S))) (y :: (x :: (T ++ S))) :=
    List.Perm.symm (List.Perm.swap x y (T ++ S))
  have qy : List.Perm (y :: (x :: (T ++ S))) ((y :: T) ++ (x :: S)) := by
    have q := List.Perm.symm
      (List.perm_middle (l₁ := T) (a := x) (l₂ := S))
    exact List.Perm.cons y q
  exact qx.trans (qs.trans qy)

/-- Swap conclusion from the three splits (all opaque: only forward
    compound rewrites + `trans`, never a bare-variable fold). -/
theorem swap_final (A T S R : List (BitVec 32)) (x y : BitVec 32)
    (l l' : List (BitVec 32))
    (eL' : l' = A ++ ((y :: T) ++ (x :: S)))
    (eA : A ++ x :: R = l)
    (eR : T ++ y :: S = R) :
    List.Perm l' l := by
  rw [eL']
  have eRperm : List.Perm (T ++ y :: S) R := by rw [eR]
  have m : List.Perm ((y :: T) ++ (x :: S)) (x :: R) :=
    (middle_swap T x y S).symm.trans (List.Perm.cons x eRperm)
  have mA : List.Perm (A ++ ((y :: T) ++ (x :: S)))
      (A ++ (x :: R)) :=
    List.Perm.append_left A m
  have mB : List.Perm (A ++ (x :: R)) l := by rw [eA]
  exact mA.trans mB

/-- Position in bounds from a successful `getElem?`. -/
theorem pos_lt_of_getElem?_some {l : List (BitVec 32)} {p : Nat}
    {x : BitVec 32} (h : l[p]? = some x) : p < l.length := by
  by_cases hlt : p < l.length
  · exact hlt
  · have hc' : l.length ≤ p := Nat.le_of_not_lt hlt
    have hnone : l[p]? = none := List.getElem?_eq_none hc'
    rw [hnone] at h
    cases h

/-- A write at the append boundary splices the tail head
    (induction form, no length-lemma risk). -/
theorem set_append_cons_head (A : List (BitVec 32)) (x : BitVec 32)
    (T : List (BitVec 32)) (y : BitVec 32) :
    (A ++ x :: T).set A.length y = A ++ y :: T := by
  induction A with
  | nil => simp
  | cons a As ih =>
    simp only [List.cons_append, List.length_cons,
      List.set_cons_succ, ih]

/-- Redundant writes collapse (induction form). -/
theorem set_set_same (l : List (BitVec 32)) (n : Nat) (a b : BitVec 32) :
    (l.set n a).set n b = l.set n b := by
  induction l generalizing n with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => simp
    | succ n =>
      simp only [List.set_cons_succ, ih]

/-- The scan returns a lower bound of its range: every scanned word
    is `≥` the running minimum (mirror of `minIndexFwd_ok` with the
    `slt_lower_trans` step in the take-leg). -/
theorem minIndexFwd_lower (l : List (BitVec 32))
    (fuel j m : Nat) (ym : BitVec 32) (i₀ : Nat)
    (hm : l[m]? = some ym) (hm_lt : m < l.length)
    (hle : j ≤ l.length) (hi₀m : i₀ ≤ m) (hi₀j : i₀ ≤ j)
    (hF : l.length - j ≤ fuel)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (hmin : ∀ (p : Nat) (x : BitVec 32), i₀ ≤ p → p < j →
      l[p]? = some x → (x.slt ym) = false) :
    ∃ m' j' ym', VecSelectionSort.minIndexFwd l fuel j m = .ok (m', j') ∧
      m' < l.length ∧ i₀ ≤ m' ∧ l[m']? = some ym' ∧
      ∀ (p : Nat) (x : BitVec 32), i₀ ≤ p → p < l.length →
        l[p]? = some x → (x.slt ym') = false := by
  induction fuel generalizing j m ym with
  | zero =>
    have him : j = l.length := by omega
    subst him
    exact ⟨m, l.length, ym, by simp [VecSelectionSort.minIndexFwd],
      hm_lt, hi₀m, hm,
      fun p x hp1 hp2 hpx => hmin p x hp1 (by omega) hpx⟩
  | succ n ih =>
    by_cases hlt : j < l.length
    · obtain ⟨x, hx⟩ := hread j hlt
      have hF' : l.length - (j + 1) ≤ n := by omega
      have hle' : j + 1 ≤ l.length := by omega
      by_cases htake : (x.slt ym) = true
      · have hmin' : ∀ (p : Nat) (x' : BitVec 32), i₀ ≤ p → p < j + 1 →
          l[p]? = some x' → (x'.slt x) = false := by
          intro p x' hp1 hp2 hpx'
          by_cases hpj : p = j
          · subst hpj
            have hxx : x' = x :=
              Option.some_inj.mp (hpx'.symm.trans hx)
            rw [hxx]
            exact VecSelectionSort.slt_irrefl _
          · exact VecSelectionSort.slt_lower_trans htake
              (hmin p x' hp1 (by omega) hpx')
        obtain ⟨m'', j'', ym'', heq, hm'', hi₀m'', hym'', hlower''⟩ :=
          ih (j + 1) j x hx hlt hle' hi₀j (by omega) hF' hmin'
        refine ⟨m'', j'', ym'', ?_, hm'', hi₀m'', hym'', hlower''⟩
        simp only [VecSelectionSort.minIndexFwd, dite_eq_left hlt,
          hx, hm, htake]
        exact heq
      · have hneg : (x.slt ym) = false := by
          cases h : x.slt ym with
          | true => exact absurd h htake
          | false => rfl
        have hmin' : ∀ (p : Nat) (x' : BitVec 32), i₀ ≤ p → p < j + 1 →
            l[p]? = some x' → (x'.slt ym) = false := by
          intro p x' hp1 hp2 hpx'
          by_cases hpj : p = j
          · subst hpj
            have hxx : x' = x :=
              Option.some_inj.mp (hpx'.symm.trans hx)
            rw [hxx]
            exact hneg
          · exact hmin p x' hp1 (by omega) hpx'
        obtain ⟨m'', j'', ym'', heq, hm'', hi₀m'', hym'', hlower''⟩ :=
          ih (j + 1) m ym hm hm_lt hle' hi₀m (by omega) hF' hmin'
        refine ⟨m'', j'', ym'', ?_, hm'', hi₀m'', hym'', hlower''⟩
        simp only [VecSelectionSort.minIndexFwd, dite_eq_left hlt,
          hx, hm, hneg]
        exact heq
    · have him : j = l.length := by omega
      subst him
      exact ⟨m, l.length, ym, by simp [VecSelectionSort.minIndexFwd],
        hm_lt, hi₀m, hm,
        fun p x hp1 hp2 hpx => hmin p x hp1 (by omega) hpx⟩

/-- Swapping two positions preserves `Perm`. -/
theorem swap_perm (l : List (BitVec 32)) (i m' : Nat)
    (x y : BitVec 32)
    (hi : i < l.length) (hm' : m' < l.length) (hle : i ≤ m')
    (hx : l[i]? = some x) (hy : l[m']? = some y) :
    List.Perm ((l.set i y).set m' x) l := by
  by_cases heq : i = m'
  · subst heq
    have hxy : y = x := Option.some_inj.mp (hy.symm.trans hx)
    rw [hxy, set_set_same, set_take_cons_drop l i x hi,
      take_cons_drop l i x hx]
  · have hlt : i < m' := by omega
    have eA : l.take i ++ x :: l.drop (i + 1) = l :=
      take_cons_drop l i x hx
    have hRk : (l.drop (i + 1))[m' - i - 1]? = some y := by
      rw [List.getElem?_drop]
      have hsum : i + 1 + (m' - i - 1) = m' := by omega
      rw [hsum]
      exact hy
    have eRw : (l.drop (i + 1)).take (m' - i - 1) ++ y ::
        l.drop (m' + 1) = l.drop (i + 1) := by
      have h1 := take_cons_drop (l.drop (i + 1)) (m' - i - 1) y hRk
      have h2 : (l.drop (i + 1)).drop (m' - i - 1 + 1) =
          l.drop (m' + 1) := by
        rw [List.drop_drop]
        congr 1
        omega
      rwa [h2] at h1
    -- Take through the written list.
    have hAi : (l.take i).length < m' := by
      rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
      exact hlt
    have eT : (l.set i y).take m' =
        l.take i ++ y :: (l.drop (i + 1)).take (m' - i - 1) := by
      rw [List.take_set]
      have hTm : l.take m' =
          l.take i ++ x :: (l.drop (i + 1)).take (m' - i - 1) := by
        conv => lhs; rw [← eA]
        rw [take_append_cons _ _ _ _ hAi]
        have hlenA : (l.take i).length = i := by
          rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
        rw [hlenA]
      rw [hTm]
      have hlenA : (l.take i).length = i := by
        rw [List.length_take, Nat.min_eq_left (Nat.le_of_lt hi)]
      have hset := set_append_cons_head (l.take i) x
        ((l.drop (i + 1)).take (m' - i - 1)) y
      rwa [hlenA] at hset
    -- Drop through the written list.
    have eD : (l.set i y).drop (m' + 1) = l.drop (m' + 1) := by
      rw [List.drop_set,
        ite_eq_left (show i < m' + 1 by omega)]
    -- Assemble the swapped list.
    have eL' : ((l.set i y).set m' x) =
        l.take i ++ ((y :: (l.drop (i + 1)).take (m' - i - 1)) ++
          (x :: l.drop (m' + 1))) := by
      have hS := set_take_cons_drop (l.set i y) m' x (by
        rw [List.length_set]; exact hm')
      rw [hS, eT, eD, List.append_assoc]
    exact swap_final _ _ _ _ _ _ _ _
      eL' eA eRw
/-- Partition take-step permutation: the double swap-write is a
    permutation, via `swap_perm` after commuting the two sets
    (the `s = i` self-swap matches `swap_perm`'s order
    directly). -/
theorem partitionTake_perm (l : List (BitVec 32)) (i s : Nat)
    (x w : BitVec 32)
    (hilt : i < l.length) (hslt : s < l.length) (hle : s ≤ i)
    (hx : l[i]? = some x) (hw : l[s]? = some w) :
    List.Perm ((l.set i w).set s x) l := by
  by_cases heq : s = i
  · subst heq
    exact swap_perm l s s x w hilt hilt (Nat.le_refl _) hx hw
  · have hne : i ≠ s := fun h => heq h.symm
    have hcomm : ((l.set i w).set s x) = ((l.set s x).set i w) :=
      List.set_comm w x hne
    rw [hcomm]
    exact swap_perm l s i w x hslt hilt hle hw hx

/-- Pure permutation over the partition forward model: every
    take step swaps two positions (`partitionTake_perm`), every
    skip step is the induction hypothesis. -/
theorem partitionFwd_perm (pivot : BitVec 32)
    (G i s : Nat) (l l' : List (BitVec 32)) (i' s' : Nat)
    (hsle : s ≤ i)
    (hfwd : partitionFwd pivot l G i s = .ok (i', s', l')) :
    List.Perm l' l := by
  induction G generalizing i s l with
  | zero =>
    have hpair : (i, s, l) = (i', s', l') := by
      simpa [partitionFwd] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    exact List.Perm.rfl
  | succ G ih =>
    by_cases hlt : i < l.length
    · have hx : l[i]? = some l[i] := List.getElem?_eq_getElem hlt
      have hslt : s < l.length := by omega
      have hw : l[s]? = some l[s] := List.getElem?_eq_getElem hslt
      by_cases htake : (l[i].slt pivot) = true
      · have hfwd' : partitionFwd pivot ((l.set i l[s]).set s l[i]) G
            (i + 1) (s + 1) = .ok (i', s', l') := by
          have h := hfwd
          simp only [partitionFwd, dite_eq_left hlt, hx, htake,
            hw] at h
          exact h
        have hperm := ih (i + 1) (s + 1) _ (by omega) hfwd'
        have htake_perm := partitionTake_perm l i s _ _ hlt hslt
          hsle hx hw
        exact hperm.trans htake_perm
      · have hskip : (l[i].slt pivot) = false := by
          cases h : l[i].slt pivot with
          | true => exact absurd h htake
          | false => rfl
        have hfwd' : partitionFwd pivot l G (i + 1) s =
            .ok (i', s', l') := by
          have h := hfwd
          simp only [partitionFwd, dite_eq_left hlt, hx, hskip] at h
          exact h
        exact ih (i + 1) s _ (by omega) hfwd'
    · have hpair : (i, s, l) = (i', s', l') := by
        simpa [partitionFwd, dite_eq_right hlt] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      exact List.Perm.rfl

/-- Partition boundary: positions below `s` test `slt`-true,
    positions at/above `s` test `slt`-false. -/
def PartitionedAt (l : List (BitVec 32)) (s : Nat)
    (pivot : BitVec 32) : Prop :=
  (∀ j, j < s → ∀ x, l[j]? = some x → (x.slt pivot) = true) ∧
  (∀ j, s ≤ j → j < l.length → ∀ x, l[j]? = some x →
    (x.slt pivot) = false)

/-- Partition invariant over the scan: `[0, s)` tests true,
    `[s, i)` tests false. Take swaps `x` (true) into `s` and
    `w` (false, or the self-swap collapse) into `i`; skip
    extends the false suffix by `x`. -/
theorem partitionFwd_partitioned (pivot : BitVec 32)
    (G i s : Nat) (l l' : List (BitVec 32)) (i' s' : Nat)
    (hle : i ≤ l.length) (hsle : s ≤ i)
    (hG : l.length - i ≤ G)
    (hpref : ∀ j, j < s → ∀ x, l[j]? = some x →
      (x.slt pivot) = true)
    (hsuff : ∀ j, s ≤ j → j < i → ∀ x, l[j]? = some x →
      (x.slt pivot) = false)
    (hfwd : partitionFwd pivot l G i s = .ok (i', s', l')) :
    PartitionedAt l' s' pivot := by
  induction G generalizing i s l with
  | zero =>
    have him : i = l.length := by omega
    have hpair : (i, s, l) = (i', s', l') := by
      simpa [partitionFwd] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    exact ⟨hpref, fun j hsj hjl y hy => hsuff j hsj (by omega) y hy⟩
  | succ G ih =>
    by_cases hlt : i < l.length
    · have hx : l[i]? = some l[i] := List.getElem?_eq_getElem hlt
      have hslt : s < l.length := by omega
      have hw : l[s]? = some l[s] := List.getElem?_eq_getElem hslt
      have hlen : ((l.set i l[s]).set s l[i]).length = l.length := by
        simp [List.length_set]
      by_cases htake : (l[i].slt pivot) = true
      · have hle' : i + 1 ≤ ((l.set i l[s]).set s l[i]).length := by
          rw [hlen]; omega
        have hG' : ((l.set i l[s]).set s l[i]).length - (i + 1) ≤ G := by
          rw [hlen]; omega
        have hpref' : ∀ j, j < s + 1 → ∀ y,
            ((l.set i l[s]).set s l[i])[j]? = some y →
            (y.slt pivot) = true := by
          intro j hj y hy
          by_cases hjs : j = s
          · subst hjs
            have hget : ((l.set i l[j]).set j l[i])[j]? =
                some l[i] :=
              List.getElem?_set_self
                (by rw [List.length_set]; exact hslt)
            rw [hget] at hy
            have : l[i] = y := Option.some_inj.mp hy
            rw [← this]; exact htake
          · have h1 : ((l.set i l[s]).set s l[i])[j]? =
              (l.set i l[s])[j]? := by
              rw [List.getElem?_set_ne (show s ≠ j by omega)]
            have h2 : (l.set i l[s])[j]? = l[j]? := by
              rw [List.getElem?_set_ne (show i ≠ j by omega)]
            rw [h1, h2] at hy
            exact hpref j (by omega) y hy
        have hsuff' : ∀ j, s + 1 ≤ j → j < i + 1 → ∀ y,
            ((l.set i l[s]).set s l[i])[j]? = some y →
            (y.slt pivot) = false := by
          intro j hsj hji y hy
          by_cases hji2 : j = i
          · subst hji2
            have h1 : ((l.set j l[s]).set s l[j])[j]? =
                (l.set j l[s])[j]? := by
              rw [List.getElem?_set_ne (show s ≠ j by omega)]
            have h2 : (l.set j l[s])[j]? = some l[s] :=
              List.getElem?_set_self hlt
            rw [h1, h2] at hy
            have : l[s] = y := Option.some_inj.mp hy
            rw [← this]
            by_cases hsi : s = j
            · omega
            · exact hsuff s (Nat.le_refl _) (by omega) _ hw
          · have h1 : ((l.set i l[s]).set s l[i])[j]? =
              (l.set i l[s])[j]? := by
              rw [List.getElem?_set_ne (show s ≠ j by omega)]
            have h2 : (l.set i l[s])[j]? = l[j]? := by
              rw [List.getElem?_set_ne (show i ≠ j by omega)]
            rw [h1, h2] at hy
            exact hsuff j (by omega) (by omega) y hy
        have hfwd' : partitionFwd pivot ((l.set i l[s]).set s l[i]) G
            (i + 1) (s + 1) = .ok (i', s', l') := by
          have h := hfwd
          simp only [partitionFwd, dite_eq_left hlt, hx, htake,
            hw] at h
          exact h
        exact ih (i + 1) (s + 1) _ hle' (by omega) hG' hpref'
          hsuff' hfwd'
      · have hskip : (l[i].slt pivot) = false := by
          cases h : l[i].slt pivot with
          | true => exact absurd h htake
          | false => rfl
        have hsuff' : ∀ j, s ≤ j → j < i + 1 → ∀ y,
            l[j]? = some y → (y.slt pivot) = false := by
          intro j hsj hji y hy
          by_cases hji2 : j = i
          · subst hji2
            have : y = l[j] :=
              Option.some_inj.mp (hx.symm.trans hy) |>.symm
            rw [this]; exact hskip
          · exact hsuff j hsj (by omega) y hy
        have hfwd' : partitionFwd pivot l G (i + 1) s =
            .ok (i', s', l') := by
          have h := hfwd
          simp only [partitionFwd, dite_eq_left hlt, hx, hskip] at h
          exact h
        have hG' : l.length - (i + 1) ≤ G := by omega
        exact ih (i + 1) s _ (by omega) (by omega) hG' hpref
          hsuff' hfwd'
    · have him : i = l.length := by omega
      have hpair : (i, s, l) = (i', s', l') := by
        simpa [partitionFwd, dite_eq_right hlt] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      exact ⟨hpref, fun j hsj hjl y hy => hsuff j hsj (by omega) y hy⟩

/-! ## P2-M9: erase-compress (`remove`) forward contract -/

/-- Erase-compress forward contract, ok leg: the scan runs to
    `l.length` with full reads (single leg — the kernel is
    total: every access is guard-justified, so the `none` arm
    never fires in-invariant). Fuel induction threading the
    write bound `w ≤ r`. -/
theorem removeFwd_ok (x : BitVec 32) (l : List (BitVec 32))
    (fuel r w : Nat)
    (hle : r ≤ l.length) (hwle : w ≤ r)
    (hF : l.length - r ≤ fuel)
    (hread : ∀ p, p < l.length → ∃ y, l[p]? = some y) :
    ∃ w' l', removeFwd x l fuel r w = .ok (l.length, w', l') := by
  induction fuel generalizing l r w with
  | zero =>
    have him : r = l.length := by omega
    subst him
    exact ⟨w, l, by simp [removeFwd]⟩
  | succ n ih =>
    by_cases hlt : r < l.length
    · obtain ⟨y, hy⟩ := hread r hlt
      have hwlt : w < l.length := by omega
      obtain ⟨wOld, hwget⟩ := hread w hwlt
      have hF' : l.length - (r + 1) ≤ n := by omega
      by_cases hkeep : (y != x) = true
      · have hlen : (l.set w y).length = l.length := by
          simp [List.length_set]
        have hread' : ∀ p, p < (l.set w y).length →
            ∃ z, (l.set w y)[p]? = some z := by
          intro p hp
          have hplen : p < l.length := by rw [hlen] at hp; exact hp
          by_cases hpw : p = w
          · rw [hpw]
            exact ⟨y, List.getElem?_set_self hwlt⟩
          · obtain ⟨z, hz⟩ := hread p hplen
            exact ⟨z, by
              rw [List.getElem?_set_ne (show w ≠ p by omega)]
              exact hz⟩
        obtain ⟨w', l', h'⟩ := ih (l := l.set w y) (r := r + 1)
          (w := w + 1) (by rw [hlen]; omega) (by omega)
          (by rw [hlen]; omega) hread'
        exact ⟨w', l', by
          simpa [removeFwd, dite_eq_left hlt, hy, hkeep] using h'⟩
      · have hdrop : (y != x) = false := by
          cases h : (y != x) with
          | true => exact absurd h hkeep
          | false => rfl
        obtain ⟨w', l', h'⟩ := ih (l := l) (r := r + 1) (w := w)
          (by omega) (by omega) hF' hread
        exact ⟨w', l', by
          simpa [removeFwd, dite_eq_left hlt, hy, hdrop] using h'⟩
    · have him : r = l.length := by omega
      subst him
      exact ⟨w, l, by simp [removeFwd, dite_eq_right hlt]⟩

/-- Erase-compress invariant over the scan, stated against the
    entry list `l₀` (the running list `l` mutates under the
    scan: positions at/above the write cursor still hold the
    entry values). The compacted prefix is the filtered
    scanned prefix of `l₀`; at exit (`r = l₀.length`) this is
    the whole filtered input. -/
theorem removeFwd_prefix (x : BitVec 32) (l₀ : List (BitVec 32))
    (fuel r w w' : Nat) (l l' : List (BitVec 32))
    (hle : r ≤ l₀.length) (hwle : w ≤ r)
    (hF : l₀.length - r ≤ fuel)
    (hlen : l.length = l₀.length)
    (hpre : l.take w =
      (l₀.take r).filter (fun y => (y != x)))
    (hsuf : ∀ j, w ≤ j → l[j]? = l₀[j]?)
    (hfwd : removeFwd x l fuel r w = .ok (l₀.length, w', l')) :
    l'.take w' = l₀.filter (fun y => (y != x)) ∧
      w ≤ w' ∧
      l'.length = l₀.length := by
  induction fuel generalizing l r w with
  | zero =>
    have hpair : (r, w, l) = (l₀.length, w', l') := by
      simpa [removeFwd] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    refine ⟨?_, Nat.le_refl _, hlen⟩
    rw [List.take_length] at hpre
    exact hpre
  | succ n ih =>
    by_cases hlt : r < l.length
    · have hlt₀ : r < l₀.length := by omega
      have hy₀ : l[r]? = some l₀[r] := by
        rw [hsuf r (by omega)]
        exact List.getElem?_eq_getElem hlt₀
      obtain ⟨wOld, hwget⟩ : ∃ z, l[w]? = some z := by
        have hwlt : w < l.length := by omega
        exact ⟨l[w], List.getElem?_eq_getElem hwlt⟩
      have hF' : l₀.length - (r + 1) ≤ n := by omega
      by_cases hkeep : (l₀[r] != x) = true
      · have hlen' : (l.set w l₀[r]).length = l₀.length := by
          simp [List.length_set, hlen]
        have hpre' : (l.set w l₀[r]).take (w + 1) =
            (l₀.take (r + 1)).filter (fun y => (y != x)) := by
          have htake : (l.set w l₀[r]).take (w + 1) =
              l.take w ++ [l₀[r]] := by
            have htakeW : (l.set w l₀[r]).take w = l.take w := by
              apply List.ext_getElem?
              intro j
              rw [List.getElem?_take, List.getElem?_take]
              by_cases hj : j < w
              · rw [List.getElem?_set_ne (show w ≠ j by omega)]
              · simp [hj]
            rw [List.take_add_one,
              List.getElem?_set_self (by omega : w < l.length),
              htakeW]; rfl
          have hfilter : (l₀.take (r + 1)).filter
              (fun y => (y != x)) =
              (l₀.take r).filter (fun y => (y != x)) ++ [l₀[r]] := by
            have htake₀ : l₀.take (r + 1) = l₀.take r ++ [l₀[r]] := by
              rw [List.take_add_one,
                List.getElem?_eq_getElem hlt₀]; rfl
            rw [htake₀, List.filter_append]
            simp [hkeep]
          rw [htake, hfilter, hpre]
        have hsuf' : ∀ j, w + 1 ≤ j → (l.set w l₀[r])[j]? = l₀[j]? := by
          intro j hj
          rw [List.getElem?_set_ne (show w ≠ j by omega)]
          exact hsuf j (by omega)
        have hfwd' : removeFwd x (l.set w l₀[r]) n (r + 1) (w + 1) =
            .ok (l₀.length, w', l') := by
          have h := hfwd
          simpa [removeFwd, dite_eq_left hlt, hy₀, hkeep] using h
        obtain ⟨hA, hB, hC⟩ := ih (l := l.set w l₀[r]) (r := r + 1)
          (w := w + 1) (by omega) (by omega) hF' hlen' hpre' hsuf'
          hfwd'
        exact ⟨hA, by omega, hC⟩
      · have hdrop : (l₀[r] != x) = false := by
          cases h : (l₀[r] != x) with
          | true => exact absurd h hkeep
          | false => rfl
        have hpre' : l.take w =
            (l₀.take (r + 1)).filter (fun y => (y != x)) := by
          have hfilter : (l₀.take (r + 1)).filter
              (fun y => (y != x)) =
              (l₀.take r).filter (fun y => (y != x)) := by
            have htake₀ : l₀.take (r + 1) = l₀.take r ++ [l₀[r]] := by
              rw [List.take_add_one,
                List.getElem?_eq_getElem hlt₀]; rfl
            rw [htake₀, List.filter_append]
            simp [hdrop]
          rw [hfilter]; exact hpre
        have hfwd' : removeFwd x l n (r + 1) w =
            .ok (l₀.length, w', l') := by
          have h := hfwd
          simpa [removeFwd, dite_eq_left hlt, hy₀, hdrop] using h
        obtain ⟨hA, hB, hC⟩ := ih (l := l) (r := r + 1) (w := w)
          (by omega) (by omega) hF' hlen hpre'
          (fun j hj => hsuf j (by omega)) hfwd'
        exact ⟨hA, hB, hC⟩
    · have hpair : (r, w, l) = (l₀.length, w', l') := by
        simpa [removeFwd, dite_eq_right hlt] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      refine ⟨?_, Nat.le_refl _, hlen⟩
      rw [List.take_length] at hpre
      exact hpre

/-! ## P2-M10: prefix-sum scan forward contract -/

/-- Checked independent prefix-scan oracle. Addition is the
    loud checked `i32` add, so a single overflowing adjacent
    pair aborts the whole scan. -/
def scanChecked : List (BitVec 32) → BitVec 32 →
    Result (List (BitVec 32))
  | [], _ => .ok []
  | x :: xs, acc =>
    match checkedAddI32 acc x with
    | .error e => .error e
    | .ok s =>
      match scanChecked xs s with
      | .error e => .error e
      | .ok ss => .ok (s :: ss)

/-- Checked prefix sums of a whole list, starting from zero. -/
def partialSumsChecked (l : List (BitVec 32)) :
    Result (List (BitVec 32)) :=
  scanChecked l 0

/-- Scan composition: scanning a concatenation first scans the
    left part, then continues from its last output (or the
    incoming accumulator for an empty left part). -/
theorem scanChecked_append (a b : List (BitVec 32))
    (acc : BitVec 32) :
    scanChecked (a ++ b) acc =
      match scanChecked a acc with
      | .error e => .error e
      | .ok sa =>
        match scanChecked b (sa.getLast?.getD acc) with
        | .error e => .error e
        | .ok sb => .ok (sa ++ sb) := by
  induction a generalizing acc with
  | nil =>
    cases h : scanChecked b acc <;> simp [scanChecked, h]
  | cons x xs ih =>
    simp only [List.cons_append, scanChecked]
    cases h1 : checkedAddI32 acc x with
    | error e => simp [h1]
    | ok s =>
      simp only [h1]
      cases h2 : scanChecked xs s with
      | error e =>
        simp only [h2]
        rw [ih s]
        simp [h2]
      | ok ss =>
        simp only [h2, ih s]
        have hlast : ((s :: ss).getLast?.getD acc) =
            (ss.getLast?.getD s) := by
          cases ss <;> rfl
        rw [hlast]
        cases h3 : scanChecked b (ss.getLast?.getD s) with
        | error e => simp [h3]
        | ok sb => simp [h3, List.cons_append]
/-- A singleton scan from `0` just returns the element: `0 + x`
    cannot overflow because `x.toInt` is already in range. -/
theorem scanChecked_singleton_zero (x : BitVec 32) :
    scanChecked [x] 0 = .ok [x] := by
  have h0 : (0#32 : BitVec 32).toInt = 0 := by simp
  have hlo := BitVec.le_toInt (x := x)
  have hhi := BitVec.toInt_le (x := x)
  have hrange : inInt32Range ((0#32 : BitVec 32).toInt + x.toInt) = true := by
    rw [inInt32Range_iff, h0, Int.zero_add]
    exact ⟨hlo, hhi⟩
  have hadd0 : checkedAddI32 0#32 x = .ok (0#32 + x) :=
    checkedAddI32_ok _ _ hrange
  simp [scanChecked, hadd0]

/-- Prefix-scan forward contract, ok leg: with the already
    scanned prefix pinned against the entry list and the
    unscanned suffix untouched, a successful forward run to the
    end returns the independent checked scan. -/
theorem partialSumFwd_scan_ok (l₀ : List (BitVec 32))
    (fuel i : Nat) (l taken : List (BitVec 32))
    (l' : List (BitVec 32)) (i' : Nat)
    (hle : i ≤ l₀.length) (hi1 : 1 ≤ i)
    (hF : l₀.length - i ≤ fuel)
    (hlen : l.length = l₀.length)
    (hpre : l.take i = taken)
    (hscan : scanChecked (l₀.take i) 0 = .ok taken)
    (hsuf : l.drop i = l₀.drop i)
    (hfwd : partialSumFwd l fuel i = .ok (i', l')) :
    i' = l₀.length ∧
      scanChecked l₀ 0 = .ok l' ∧
      l'.length = l₀.length := by
  induction fuel generalizing l i taken with
  | zero =>
    have him : i = l₀.length := by omega
    subst him
    have hpair : (l₀.length, l) = (i', l') := by
      simpa [partialSumFwd] using hfwd
    rw [Prod.mk.injEq] at hpair
    obtain ⟨hiEq, hlEq⟩ := hpair
    refine ⟨hiEq.symm, ?_, by rw [← hlEq, hlen]⟩
    have hpre' : l = taken := by
      have h := hpre
      rw [← hlen, List.take_length] at h
      exact h
    have hscan' : scanChecked l₀ 0 = .ok taken := by
      have h := hscan
      rw [List.take_length] at h
      exact h
    rw [← hlEq, hpre']
    exact hscan'
  | succ n ih =>
    by_cases hlt : i < l.length
    · obtain ⟨cur, hgetC⟩ : ∃ x, l[i]? = some x :=
        ⟨l[i], List.getElem?_eq_getElem hlt⟩
      have hprevlt : i - 1 < l.length := by omega
      obtain ⟨prev, hgetP⟩ : ∃ x, l[i - 1]? = some x :=
        ⟨l[i - 1], List.getElem?_eq_getElem hprevlt⟩
      match hadd : checkedAddI32 cur prev with
      | .ok sum =>
        have hcur0 : l₀[i]? = some cur := by
          have h0 : (l.drop i)[0]? = (l₀.drop i)[0]? := by
            rw [hsuf]
          rw [List.getElem?_drop, List.getElem?_drop] at h0
          simp only [Nat.add_zero] at h0 ⊢
          exact h0.symm.trans hgetC
        have htakenN : taken.length = i := by
          rw [← hpre, List.length_take, hlen,
            Nat.min_eq_left hle]
        have hprevTaken : taken[i - 1]? = some prev := by
          have h := congrArg
            (fun xs : List (BitVec 32) => xs[i - 1]?) hpre
          simpa [List.getElem?_take_of_lt
            (show i - 1 < i by omega), hgetP] using h.symm
        have hlast : taken.getLast? = some prev := by
          rw [List.getLast?_eq_getElem?, htakenN]
          exact hprevTaken
        have haccPrev : taken.getLast?.getD 0 = prev := by
          rw [hlast]; rfl
        have hadd' : checkedAddI32 prev cur = .ok sum := by
          rw [checkedAddI32_comm]; exact hadd
        have hval : sum = prev + cur := by
          have h := checkedAddI32_ok_value _ _ _ hadd
          rw [BitVec.add_comm] at h
          exact h
        have hsingleton : scanChecked [cur] prev = .ok [sum] := by
          simp [scanChecked, hadd', hval]
        have htake0 : l₀.take (i + 1) = l₀.take i ++ [cur] := by
          rw [List.take_add_one, hcur0]; rfl
        have hscanNext :
            scanChecked (l₀.take (i + 1)) 0 =
              .ok (taken ++ [sum]) := by
          simp only [htake0, scanChecked_append, hscan, haccPrev,
            hsingleton]
        have htakeW : (l.set i sum).take i = l.take i := by
          apply List.ext_getElem?
          intro j
          rw [List.getElem?_take, List.getElem?_take]
          by_cases hj : j < i
          · rw [List.getElem?_set_ne (show i ≠ j by omega)]
          · simp [hj]
        have htake : (l.set i sum).take (i + 1) =
            l.take i ++ [sum] := by
          rw [List.take_add_one, List.getElem?_set_self hlt,
            htakeW]; rfl
        have hpre' : (l.set i sum).take (i + 1) =
            taken ++ [sum] := by
          rw [htake, hpre]
        have hlen' : (l.set i sum).length = l₀.length := by
          simp [List.length_set, hlen]
        have hsuf' : (l.set i sum).drop (i + 1) =
            l₀.drop (i + 1) := by
          have htails : (l.drop i).tail = (l₀.drop i).tail := by
            rw [hsuf]
          have hsame : l.drop (i + 1) = l₀.drop (i + 1) := by
            rw [List.drop_add_one_eq_tail_drop,
              List.drop_add_one_eq_tail_drop, htails]
          simp [List.drop_set, show i < i + 1 by omega, hsame]
        have hfwd' : partialSumFwd (l.set i sum) n (i + 1) =
            .ok (i', l') := by
          have h := hfwd
          simpa [partialSumFwd, dite_eq_left hlt, hgetC, hgetP,
            hadd] using h
        obtain ⟨hiEq, hscanFull, hlenFull⟩ :=
          ih (i + 1) (l.set i sum) (taken ++ [sum])
            (by omega) (by omega) (by omega) hlen' hpre'
            hscanNext hsuf' hfwd'
        exact ⟨hiEq, hscanFull, hlenFull⟩
      | .error e =>
        have h := hfwd
        simp only [partialSumFwd, dite_eq_left hlt, hgetC, hgetP,
          hadd] at h
        exact absurd h (by simp)
    · have him : i = l.length := by omega
      subst him
      have him0 : l.length = l₀.length := hlen
      have hpair : (l.length, l) = (i', l') := by
        cases n with
        | zero => simpa [partialSumFwd] using hfwd
        | succ _ =>
          have hneg : ¬ l.length < l.length := by omega
          simpa [partialSumFwd, dite_eq_right hneg] using hfwd
      rw [Prod.mk.injEq] at hpair
      obtain ⟨hiEq, hlEq⟩ := hpair
      refine ⟨hiEq.symm.trans him0, ?_,
        by rw [← hlEq, hlen]⟩
      have hpre' : l = taken := by
        have h := hpre
        rw [List.take_length] at h
        exact h
      have hscan' : scanChecked l₀ 0 = .ok taken := by
        have h := hscan
        rw [him0, List.take_length] at h
        exact h
      rw [← hlEq, hpre']
      exact hscan'


/-- Prefix-scan forward contract, error leg: with the same
    already-scanned/unscanned invariant, a loud forward failure is
    also a loud failure of the independent checked scan. -/
theorem partialSumFwd_scan_err (l₀ : List (BitVec 32))
    (fuel i : Nat) (l taken : List (BitVec 32)) (e : Panic)
    (hle : i ≤ l₀.length) (hi1 : 1 ≤ i)
    (hF : l₀.length - i ≤ fuel)
    (hlen : l.length = l₀.length)
    (hpre : l.take i = taken)
    (hscan : scanChecked (l₀.take i) 0 = .ok taken)
    (hsuf : l.drop i = l₀.drop i)
    (hfwd : partialSumFwd l fuel i = .error e) :
    scanChecked l₀ 0 = .error e := by
  induction fuel generalizing l i taken with
  | zero => simpa [partialSumFwd] using hfwd
  | succ n ih =>
    by_cases hlt : i < l.length
    · obtain ⟨cur, hgetC⟩ : ∃ x, l[i]? = some x :=
        ⟨l[i], List.getElem?_eq_getElem hlt⟩
      have hprevlt : i - 1 < l.length := by omega
      obtain ⟨prev, hgetP⟩ : ∃ x, l[i - 1]? = some x :=
        ⟨l[i - 1], List.getElem?_eq_getElem hprevlt⟩
      have hcur0 : l₀[i]? = some cur := by
        have h0 : (l.drop i)[0]? = (l₀.drop i)[0]? := by
          rw [hsuf]
        rw [List.getElem?_drop, List.getElem?_drop] at h0
        simp only [Nat.add_zero] at h0 ⊢
        exact h0.symm.trans hgetC
      have htakenN : taken.length = i := by
        rw [← hpre, List.length_take, hlen,
          Nat.min_eq_left hle]
      have hprevTaken : taken[i - 1]? = some prev := by
        have h := congrArg
          (fun xs : List (BitVec 32) => xs[i - 1]?) hpre
        simpa [List.getElem?_take_of_lt
          (show i - 1 < i by omega), hgetP] using h.symm
      have hlast : taken.getLast? = some prev := by
        rw [List.getLast?_eq_getElem?, htakenN]
        exact hprevTaken
      have haccPrev : taken.getLast?.getD 0 = prev := by
        rw [hlast]; rfl
      have htake0 : l₀.take (i + 1) = l₀.take i ++ [cur] := by
        rw [List.take_add_one, hcur0]; rfl
      match hadd : checkedAddI32 cur prev with
      | .ok sum =>
        have hadd' : checkedAddI32 prev cur = .ok sum := by
          rw [checkedAddI32_comm]; exact hadd
        have hval : sum = prev + cur := by
          have h := checkedAddI32_ok_value _ _ _ hadd
          rw [BitVec.add_comm] at h
          exact h
        have hsingleton : scanChecked [cur] prev = .ok [sum] := by
          simp [scanChecked, hadd', hval]
        have hscanNext :
            scanChecked (l₀.take (i + 1)) 0 =
              .ok (taken ++ [sum]) := by
          simp only [htake0, scanChecked_append, hscan, haccPrev,
            hsingleton]
        have htakeW : (l.set i sum).take i = l.take i := by
          apply List.ext_getElem?
          intro j
          rw [List.getElem?_take, List.getElem?_take]
          by_cases hj : j < i
          · rw [List.getElem?_set_ne (show i ≠ j by omega)]
          · simp [hj]
        have htake : (l.set i sum).take (i + 1) =
            l.take i ++ [sum] := by
          rw [List.take_add_one, List.getElem?_set_self hlt,
            htakeW]; rfl
        have hpre' : (l.set i sum).take (i + 1) =
            taken ++ [sum] := by
          rw [htake, hpre]
        have hlen' : (l.set i sum).length = l₀.length := by
          simp [List.length_set, hlen]
        have hsuf' : (l.set i sum).drop (i + 1) =
            l₀.drop (i + 1) := by
          have htails : (l.drop i).tail = (l₀.drop i).tail := by
            rw [hsuf]
          have hsame : l.drop (i + 1) = l₀.drop (i + 1) := by
            rw [List.drop_add_one_eq_tail_drop,
              List.drop_add_one_eq_tail_drop, htails]
          simp [List.drop_set, show i < i + 1 by omega, hsame]
        have hfwd' : partialSumFwd (l.set i sum) n (i + 1) =
            .error e := by
          have h := hfwd
          simpa [partialSumFwd, dite_eq_left hlt, hgetC, hgetP,
            hadd] using h
        exact ih (i + 1) (l.set i sum) (taken ++ [sum])
          (by omega) (by omega) (by omega) hlen' hpre'
          hscanNext hsuf' hfwd'
      | .error e' =>
        have heEq : e' = e := by
          have h := hfwd
          simpa [partialSumFwd, dite_eq_left hlt, hgetC, hgetP,
            hadd] using h
        have haddCurr : checkedAddI32 prev cur = .error e' := by
          rw [checkedAddI32_comm]; exact hadd
        have hsingErr : scanChecked [cur] prev = .error e' := by
          simp [scanChecked, haddCurr]
        have hscanNextErr :
            scanChecked (l₀.take (i + 1)) 0 = .error e' := by
          simp only [htake0, scanChecked_append, hscan, haccPrev,
            hsingErr]
        have hfull : l₀ = l₀.take (i + 1) ++ l₀.drop (i + 1) :=
          (List.take_append_drop _ _).symm
        rw [hfull, scanChecked_append, hscanNextErr]
        cases heEq
        rfl
    · have hneg : ¬ i < l.length := by omega
      simpa [partialSumFwd, dite_eq_right hneg] using hfwd

/-- Sorted window (M5 positional formulation for a subrange):
    positions in `[lo, hi)` pairwise ascending under `slt`. -/
def SortedSeg (l : List (BitVec 32)) (lo hi : Nat) : Prop :=
  ∀ p q, lo ≤ p → p < q → q < hi → ∀ a b,
    l[p]? = some a → l[q]? = some b → (b.slt a) = false

/-- Appending above a sorted window preserves sortedness when
    the new element tests `slt`-false against every window
    element (the emitted-above-consumed step). -/
theorem sortedSeg_snoc (l : List (BitVec 32)) (lo k : Nat)
    (x : BitVec 32)
    (hs : SortedSeg l lo k)
    (hle : ∀ p, lo ≤ p → p < k → ∀ a, l[p]? = some a →
      (x.slt a) = false)
    (hk : k < l.length) :
    SortedSeg (l.set k x) lo (k + 1) := by
  intro p q hlo hpq hqk a b ha hb
  by_cases hqk2 : q = k
  · subst hqk2
    have hbx : b = x := by
      have hget : (l.set q x)[q]? = some x :=
        List.getElem?_set_self hk
      rw [hget] at hb
      exact (Option.some_inj.mp hb).symm
    have ha' : l[p]? = some a := by
      have h1 : (((l.set q x)[p]? : Option (BitVec 32))) =
          l[p]? := by
        rw [List.getElem?_set_ne (show q ≠ p by omega)]
      rw [h1] at ha
      exact ha
    rw [hbx]
    exact hle p (by omega) (by omega) a ha'
  · have ha' : l[p]? = some a := by
      have h1 : (((l.set k x)[p]? : Option (BitVec 32))) =
          l[p]? := by
        rw [List.getElem?_set_ne (show k ≠ p by omega)]
      rw [h1] at ha
      exact ha
    have hb' : l[q]? = some b := by
      have h1 : (((l.set k x)[q]? : Option (BitVec 32))) =
          l[q]? := by
        rw [List.getElem?_set_ne (show k ≠ q by omega)]
      rw [h1] at hb
      exact hb
    exact hs p q hlo (by omega) (by omega) a b ha' hb'

/-- Take-window snoc: extending the take bound by one appends
    the element. -/
theorem take_snoc (l : List (BitVec 32)) (lo n : Nat)
    (hlo : lo ≤ n) (hn : n < l.length) :
    ((l.drop lo).take (n + 1 - lo)) =
      ((l.drop lo).take (n - lo)) ++ [l[n]] := by
  apply List.ext_getElem?
  intro p
  rw [List.getElem?_take]
  by_cases hp : p < n + 1 - lo
  · rw [ite_eq_left hp]
    rw [List.getElem?_drop]
    by_cases hp2 : p < n - lo
    · have hlen : ((l.drop lo).take (n - lo)).length = n - lo := by
        rw [List.length_take, List.length_drop]
        exact Nat.min_eq_left (by omega)
      rw [List.getElem?_append_left (by rw [hlen]; omega),
        List.getElem?_take, ite_eq_left hp2, List.getElem?_drop]
    · have hpeq : p = n - lo := by omega
      have hlen : ((l.drop lo).take (n - lo)).length = n - lo := by
        rw [List.length_take, List.length_drop]
        exact Nat.min_eq_left (by omega)
      rw [hpeq, List.getElem?_append_right (by rw [hlen]; omega),
        hlen]
      simp only [Nat.sub_self]
      have hnn : lo + (n - lo) = n := by omega
      rw [hnn, List.getElem?_eq_getElem (by omega : n < l.length)]
      rfl
  · rw [ite_eq_right hp]
    have hlen : ((((l.drop lo).take (n - lo)) ++ [l[n]]).length) =
        n + 1 - lo := by
      rw [List.length_append, List.length_take, List.length_drop,
        List.length_singleton]
      omega
    have hle : ((((l.drop lo).take (n - lo)) ++ [l[n]]).length) ≤
        p := by
      rw [hlen]
      omega
    rw [List.getElem?_eq_none hle]

/-- Take-window snoc through a single set at the extension
    point (the merge-emit step on the `tmp` side). -/
theorem perm_seg_snoc (lt : List (BitVec 32)) (lo k : Nat)
    (x : BitVec 32)
    (hlo_k : lo ≤ k) (hk : k < lt.length) :
    ((lt.set k x).drop lo).take (k + 1 - lo) =
      ((lt.drop lo).take (k - lo)) ++ [x] := by
  apply List.ext_getElem?
  intro p
  rw [List.getElem?_take]
  by_cases hp : p < k + 1 - lo
  · rw [ite_eq_left hp]
    rw [List.getElem?_drop]
    by_cases hp2 : p < k - lo
    · have hlen2a : ((lt.drop lo).take (k - lo)).length = k - lo := by
        rw [List.length_take, List.length_drop]
        exact Nat.min_eq_left (by omega)
      rw [List.getElem?_append_left (by rw [hlen2a]; omega),
        List.getElem?_take, ite_eq_left hp2, List.getElem?_drop,
        List.getElem?_set_ne (show k ≠ lo + p by omega)]
    · have hpeq : p = k - lo := by omega
      have hlen2 : ((lt.drop lo).take (k - lo)).length = k - lo := by
        rw [List.length_take, List.length_drop]
        exact Nat.min_eq_left (by omega)
      rw [hpeq, List.getElem?_append_right (by rw [hlen2]; omega),
        hlen2]
      simp only [Nat.sub_self]
      have heq : lo + (k - lo) = k := by omega
      rw [heq]
      exact List.getElem?_set_self hk
  · rw [ite_eq_right hp]
    have hlenR : ((((lt.drop lo).take (k - lo)) ++ [x]).length) =
        k + 1 - lo := by
      rw [List.length_append, List.length_take, List.length_drop,
        List.length_singleton]
      omega
    have hleR : ((((lt.drop lo).take (k - lo)) ++ [x]).length) ≤
        p := by
      rw [hlenR]
      omega
    rw [List.getElem?_eq_none hleR]

/-- Merge main-loop contract: sorted emitted prefix, cross
    invariants against both unread runs, the consumed multiset,
    and the exit shape (one run exhausted). Take-x uses
    run-sortedness plus one `slt` transitivity
    (`slt_lower_trans`); take-y is symmetric
    (`slt_ge_trans`). -/
theorem VecMergeRuns.mergeRunsMainFwd_sorted (la : List (BitVec 32))
    (F' i j k mid hi lo : Nat)
    (lt lt' : List (BitVec 32)) (i' j' k' : Nat)
    (hlo_i : lo ≤ i) (hi_ : i ≤ mid) (hj_ : j ≤ hi)
    (hmid_j : mid ≤ j)
    (hlo_k : lo ≤ k) (hk : k ≤ lt.length)
    (hla_len : hi ≤ la.length)
    (hcount : k - lo = (i - lo) + (j - mid))
    (hleft : SortedSeg la lo mid) (hright : SortedSeg la mid hi)
    (hsorted : SortedSeg lt lo k)
    (hcrossL : ∀ p, lo ≤ p → p < k → ∀ a, lt[p]? = some a →
      ∀ q, i ≤ q → q < mid → ∀ b, la[q]? = some b →
      (b.slt a) = false)
    (hcrossR : ∀ p, lo ≤ p → p < k → ∀ a, lt[p]? = some a →
      ∀ q, j ≤ q → q < hi → ∀ b, la[q]? = some b →
      (b.slt a) = false)
    (hperm : List.Perm ((lt.drop lo).take (k - lo))
      ((la.drop lo).take (i - lo) ++ (la.drop mid).take (j - mid)))
    (hF : (mid - i) + (hi - j) ≤ F')
    (hfwd : VecMergeRuns.mergeRunsMainFwd la lt F' i j k mid hi =
      .ok (i', j', k', lt')) :
    SortedSeg lt' lo k' ∧
    (∀ p, lo ≤ p → p < k' → ∀ a, lt'[p]? = some a →
      ∀ q, i' ≤ q → q < mid → ∀ b, la[q]? = some b →
      (b.slt a) = false) ∧
    (∀ p, lo ≤ p → p < k' → ∀ a, lt'[p]? = some a →
      ∀ q, j' ≤ q → q < hi → ∀ b, la[q]? = some b →
      (b.slt a) = false) ∧
    List.Perm ((lt'.drop lo).take (k' - lo))
      ((la.drop lo).take (i' - lo) ++ (la.drop mid).take (j' - mid)) ∧
    (i' = mid ∨ j' = hi) ∧
    i' ≤ mid ∧ j' ≤ hi ∧ k' ≤ lt'.length ∧
    k' - lo = (i' - lo) + (j' - mid) ∧ lt'.length = lt.length := by
  induction F' generalizing lt i j k with
  | zero =>
    have hpair : (i, j, k, lt) = (i', j', k', lt') := by
      simpa [VecMergeRuns.mergeRunsMainFwd] using hfwd
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
    exact ⟨hsorted, hcrossL, hcrossR, hperm, by omega,
      hi_, hj_, hk, hcount, rfl⟩
  | succ F' ih =>
    by_cases hI : i < mid
    · by_cases hJ : j < hi
      · cases hK : lt[k]? with
        | none =>
          simp only [VecMergeRuns.mergeRunsMainFwd, dite_eq_left hI,
            dite_eq_left hJ, hK] at hfwd
          cases hfwd
        | some w =>
          have hklen : k < lt.length :=
            list_lt_of_getElem?_some lt k w hK
          cases hAi : la[i]? with
          | none =>
            cases hAj : la[j]? with
            | none =>
              simp only [VecMergeRuns.mergeRunsMainFwd, dite_eq_left hI,
                dite_eq_left hJ, hK, hAi, hAj] at hfwd
              cases hfwd
            | some y =>
              simp only [VecMergeRuns.mergeRunsMainFwd, dite_eq_left hI,
                dite_eq_left hJ, hK, hAi, hAj] at hfwd
              cases hfwd
          | some x =>
            cases hAj : la[j]? with
            | none =>
              simp only [VecMergeRuns.mergeRunsMainFwd, dite_eq_left hI,
                dite_eq_left hJ, hK, hAi, hAj] at hfwd
              cases hfwd
            | some y =>
              have hlen : i < la.length := by omega
              have hlenJ : j < la.length := by omega
              have hxi : la[i] = x := by
                have h1 : la[i]? = some la[i] :=
                  List.getElem?_eq_getElem hlen
                have h2 := h1.symm.trans hAi
                exact Option.some_inj.mp h2
              have hyj : la[j] = y := by
                have h1 : la[j]? = some la[j] :=
                  List.getElem?_eq_getElem hlenJ
                have h2 := h1.symm.trans hAj
                exact Option.some_inj.mp h2
              by_cases hslt : (x.slt y) = true
              · have hfwd' : VecMergeRuns.mergeRunsMainFwd la (lt.set k x) F'
                    (i + 1) j (k + 1) mid hi =
                    .ok (i', j', k', lt') := by
                  have h := hfwd
                  simp only [VecMergeRuns.mergeRunsMainFwd, dite_eq_left hI,
                    dite_eq_left hJ, hK, hAi, hAj, hslt] at h
                  exact h
                have hsorted1 : SortedSeg (lt.set k x) lo (k + 1) :=
                  sortedSeg_snoc _ _ _ _ hsorted
                    (fun p hlo_p hpk a ha =>
                      hcrossL p hlo_p hpk a ha i (Nat.le_refl _)
                        hI x hAi)
                    hklen
                have hcrossL1 : ∀ p, lo ≤ p → p < k + 1 → ∀ a,
                    ((lt.set k x)[p]? : Option (BitVec 32)) =
                      some a →
                    ∀ q, i + 1 ≤ q → q < mid → ∀ b,
                      la[q]? = some b → (b.slt a) = false := by
                  intro p hlo_p hpk a ha q hiq hqm b hb
                  by_cases hpk2 : p = k
                  · rw [hpk2] at ha
                    have hget : ((lt.set k x)[k]? :
                        Option (BitVec 32)) = some x :=
                      List.getElem?_set_self hklen
                    rw [hget] at ha
                    have hax : x = a := Option.some_inj.mp ha
                    rw [← hax]
                    exact hleft i q (by omega) (by omega)
                      (by omega) x b hAi hb
                  · have ha' : lt[p]? = some a := by
                      have h1 : (((lt.set k x)[p]? :
                          Option (BitVec 32))) = lt[p]? := by
                        rw [List.getElem?_set_ne
                          (show k ≠ p by omega)]
                      rw [h1] at ha
                      exact ha
                    exact hcrossL p hlo_p (by omega) a ha' q
                      (by omega) hqm b hb
                have hcrossR1 : ∀ p, lo ≤ p → p < k + 1 → ∀ a,
                    ((lt.set k x)[p]? : Option (BitVec 32)) =
                      some a →
                    ∀ q, j ≤ q → q < hi → ∀ b, la[q]? = some b →
                      (b.slt a) = false := by
                  intro p hlo_p hpk a ha q hjq hqh b hb
                  by_cases hpk2 : p = k
                  · rw [hpk2] at ha
                    have hget : ((lt.set k x)[k]? :
                        Option (BitVec 32)) = some x :=
                      List.getElem?_set_self hklen
                    rw [hget] at ha
                    have hax : x = a := Option.some_inj.mp ha
                    have hby : (b.slt y) = false := by
                      by_cases hqj : j = q
                      · subst hqj
                        have hbb : b = y :=
                          Option.some_inj.mp (hb.symm.trans hAj)
                        rw [hbb]
                        simp [BitVec.slt]
                      · exact hright j q (by omega) (by omega)
                          (by omega) y b hAj hb
                    rw [← hax]
                    exact VecSelectionSort.slt_lower_trans hslt hby
                  · have ha' : lt[p]? = some a := by
                      have h1 : (((lt.set k x)[p]? :
                          Option (BitVec 32))) = lt[p]? := by
                        rw [List.getElem?_set_ne
                          (show k ≠ p by omega)]
                      rw [h1] at ha
                      exact ha
                    exact hcrossR p hlo_p (by omega) a ha' q hjq
                      hqh b hb
                have hperm1 : List.Perm
                    ((((lt.set k x).drop lo).take (k + 1 - lo)))
                    (((la.drop lo).take (i + 1 - lo)) ++
                      (la.drop mid).take (j - mid)) := by
                  have hseg : ((lt.set k x).drop lo).take
                      (k + 1 - lo) =
                      ((lt.drop lo).take (k - lo)) ++ [x] :=
                    perm_seg_snoc lt lo k x (by omega) hklen
                  have hsegL : ((la.drop lo).take (i + 1 - lo)) =
                      ((la.drop lo).take (i - lo)) ++ [la[i]] :=
                    take_snoc la lo i (by omega) (by omega)
                  have key : List.Perm ((((la.drop lo).take (i - lo)) ++
                      ((la.drop mid).take (j - mid))) ++ [x])
                      ((((la.drop lo).take (i - lo)) ++ [x]) ++
                        ((la.drop mid).take (j - mid))) := by
                    rw [List.append_assoc,
                      List.append_assoc ((la.drop lo).take (i - lo)) [x]
                        ((la.drop mid).take (j - mid))]
                    exact List.Perm.rfl.append
                      List.perm_append_comm
                  rw [hseg, hsegL, hxi]
                  exact (hperm.append List.Perm.rfl).trans key
                obtain ⟨hs1, hcl1, hcr1, hp1, hd1, hb1, hb2, hb3, hc1,
                    hlen1⟩ :=
                  ih (i + 1) j (k + 1) (lt.set k x)
                    (by omega) (by omega) (by omega) (by omega)
                    (by omega)
                    (by rw [List.length_set]; omega)
                    (by omega)
                    hsorted1 hcrossL1 hcrossR1 hperm1
                    (by omega) hfwd'
                refine ⟨hs1, hcl1, hcr1, hp1, hd1, hb1, hb2, hb3, hc1, ?_⟩
                rw [hlen1, List.length_set]
              · have hsltF : (x.slt y) = false := by
                  cases h : x.slt y with
                  | true => exact absurd h hslt
                  | false => rfl
                have hfwd' : VecMergeRuns.mergeRunsMainFwd la (lt.set k y) F' i
                    (j + 1) (k + 1) mid hi =
                    .ok (i', j', k', lt') := by
                  have h := hfwd
                  simp only [VecMergeRuns.mergeRunsMainFwd, dite_eq_left hI,
                    dite_eq_left hJ, hK, hAi, hAj, hsltF] at h
                  exact h
                have hsorted1 : SortedSeg (lt.set k y) lo (k + 1) :=
                  sortedSeg_snoc _ _ _ _ hsorted
                    (fun p hlo_p hpk a ha =>
                      hcrossR p hlo_p hpk a ha j (Nat.le_refl _)
                        hJ y hAj)
                    hklen
                have hcrossL1 : ∀ p, lo ≤ p → p < k + 1 → ∀ a,
                    ((lt.set k y)[p]? : Option (BitVec 32)) =
                      some a →
                    ∀ q, i ≤ q → q < mid → ∀ b, la[q]? = some b →
                      (b.slt a) = false := by
                  intro p hlo_p hpk a ha q hiq hqm b hb
                  by_cases hpk2 : p = k
                  · rw [hpk2] at ha
                    have hget : ((lt.set k y)[k]? :
                        Option (BitVec 32)) = some y :=
                      List.getElem?_set_self hklen
                    rw [hget] at ha
                    have hay : y = a := Option.some_inj.mp ha
                    rw [← hay]
                    by_cases hqi : q = i
                    · subst hqi
                      have hbx : (x.slt y) = false := hsltF
                      have hxb : x = b := by
                        have h1 : la[q]? = some x := hAi
                        rw [h1] at hb
                        exact Option.some_inj.mp hb
                      rw [← hxb]; exact hbx
                    · exact VecSelectionSort.slt_ge_trans
                        (hleft i q (by omega) (by omega)
                          (by omega) x b hAi hb)
                        hsltF
                  · have ha' : lt[p]? = some a := by
                      have h1 : (((lt.set k y)[p]? :
                          Option (BitVec 32))) = lt[p]? := by
                        rw [List.getElem?_set_ne
                          (show k ≠ p by omega)]
                      rw [h1] at ha
                      exact ha
                    exact hcrossL p hlo_p (by omega) a ha' q hiq
                      hqm b hb
                have hcrossR1 : ∀ p, lo ≤ p → p < k + 1 → ∀ a,
                    ((lt.set k y)[p]? : Option (BitVec 32)) =
                      some a →
                    ∀ q, j + 1 ≤ q → q < hi → ∀ b, la[q]? = some b →
                      (b.slt a) = false := by
                  intro p hlo_p hpk a ha q hjq hqh b hb
                  by_cases hpk2 : p = k
                  · rw [hpk2] at ha
                    have hget : ((lt.set k y)[k]? :
                        Option (BitVec 32)) = some y :=
                      List.getElem?_set_self hklen
                    rw [hget] at ha
                    have hay : y = a := Option.some_inj.mp ha
                    rw [← hay]
                    exact hright j q (by omega) (by omega)
                      (by omega) y b hAj hb
                  · have ha' : lt[p]? = some a := by
                      have h1 : (((lt.set k y)[p]? :
                          Option (BitVec 32))) = lt[p]? := by
                        rw [List.getElem?_set_ne
                          (show k ≠ p by omega)]
                      rw [h1] at ha
                      exact ha
                    exact hcrossR p hlo_p (by omega) a ha' q
                      (by omega) hqh b hb
                have hperm1 : List.Perm
                    ((((lt.set k y).drop lo).take (k + 1 - lo)))
                    (((la.drop lo).take (i - lo)) ++
                      (la.drop mid).take (j + 1 - mid)) := by
                  have hseg : ((lt.set k y).drop lo).take
                      (k + 1 - lo) =
                      ((lt.drop lo).take (k - lo)) ++ [y] :=
                    perm_seg_snoc lt lo k y (by omega) hklen
                  have hsegR : ((la.drop mid).take (j + 1 - mid)) =
                      ((la.drop mid).take (j - mid)) ++ [la[j]] :=
                    take_snoc la mid j (by omega) (by omega)
                  rw [hseg, hsegR, hyj, ← List.append_assoc]
                  exact hperm.append List.Perm.rfl
                obtain ⟨hs1, hcl1, hcr1, hp1, hd1, hb1, hb2, hb3, hc1,
                    hlen1⟩ :=
                  ih i (j + 1) (k + 1) (lt.set k y)
                    (by omega) (by omega) (by omega) (by omega)
                    (by omega)
                    (by rw [List.length_set]; omega)
                    (by omega)
                    hsorted1 hcrossL1 hcrossR1 hperm1
                    (by omega) hfwd'
                refine ⟨hs1, hcl1, hcr1, hp1, hd1, hb1, hb2, hb3, hc1, ?_⟩
                rw [hlen1, List.length_set]
      · have hpair : (i, j, k, lt) = (i', j', k', lt') := by
          simpa [VecMergeRuns.mergeRunsMainFwd, dite_eq_left hI,
            dite_eq_right hJ] using hfwd
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
        exact ⟨hsorted, hcrossL, hcrossR, hperm, Or.inr (by omega),
          hi_, hj_, hk, hcount, rfl⟩
    · have hpair : (i, j, k, lt) = (i', j', k', lt') := by
        simpa [VecMergeRuns.mergeRunsMainFwd, dite_eq_right hI] using hfwd
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
      exact ⟨hsorted, hcrossL, hcrossR, hperm, Or.inl (by omega),
        hi_, hj_, hk, hcount, rfl⟩
/-- Main-loop cursor never moves down. -/
theorem VecMergeRuns.mergeRunsMain_mono (la : List (BitVec 32))
    (F' i j k mid hi : Nat)
    (lt lt' : List (BitVec 32)) (i' j' k' : Nat)
    (hfwd : VecMergeRuns.mergeRunsMainFwd la lt F' i j k mid hi =
      .ok (i', j', k', lt')) :
    k ≤ k' := by
  induction F' generalizing i j k lt with
  | zero =>
    have hpair : (i, j, k, lt) = (i', j', k', lt') := by
      simpa [VecMergeRuns.mergeRunsMainFwd] using hfwd
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
    omega
  | succ F' ih =>
    by_cases hI : i < mid
    · by_cases hJ : j < hi
      · cases hK : lt[k]? with
        | none =>
          simp only [VecMergeRuns.mergeRunsMainFwd, dite_eq_left hI,
            dite_eq_left hJ, hK] at hfwd
          cases hfwd
        | some w =>
          cases hAi : la[i]? with
          | none =>
            simp only [VecMergeRuns.mergeRunsMainFwd, dite_eq_left hI,
              dite_eq_left hJ, hK, hAi] at hfwd
            cases hfwd
          | some x =>
            cases hAj : la[j]? with
            | none =>
              simp only [VecMergeRuns.mergeRunsMainFwd, dite_eq_left hI,
                dite_eq_left hJ, hK, hAi, hAj] at hfwd
              cases hfwd
            | some y =>
              by_cases hslt : (x.slt y) = true
              · have hfwd' : VecMergeRuns.mergeRunsMainFwd la (lt.set k x)
                    F' (i + 1) j (k + 1) mid hi =
                    .ok (i', j', k', lt') := by
                  simpa [VecMergeRuns.mergeRunsMainFwd, dite_eq_left hI,
                    dite_eq_left hJ, hK, hAi, hAj, hslt] using hfwd
                have h1 := ih (i + 1) j (k + 1) (lt.set k x) hfwd'
                omega
              · have hsltF : (x.slt y) = false := by
                  cases h : x.slt y with
                  | true => exact absurd h hslt
                  | false => rfl
                have hfwd' : VecMergeRuns.mergeRunsMainFwd la (lt.set k y)
                    F' i (j + 1) (k + 1) mid hi =
                    .ok (i', j', k', lt') := by
                  simpa [VecMergeRuns.mergeRunsMainFwd, dite_eq_left hI,
                    dite_eq_left hJ, hK, hAi, hAj, hsltF] using hfwd
                have h1 := ih i (j + 1) (k + 1) (lt.set k y) hfwd'
                omega
      · have hpair : (i, j, k, lt) = (i', j', k', lt') := by
          simpa [VecMergeRuns.mergeRunsMainFwd, dite_eq_left hI,
            dite_eq_right hJ] using hfwd
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
        omega
    · have hpair : (i, j, k, lt) = (i', j', k', lt') := by
        simpa [VecMergeRuns.mergeRunsMainFwd, dite_eq_right hI] using hfwd
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
      omega

/-- Main-loop writes stay below the final cursor: reads at or
    above `k'` see the original list. -/
theorem VecMergeRuns.mergeRunsMain_ge (la : List (BitVec 32))
    (F' i j k mid hi : Nat)
    (lt lt' : List (BitVec 32)) (i' j' k' : Nat)
    (hfwd : VecMergeRuns.mergeRunsMainFwd la lt F' i j k mid hi =
      .ok (i', j', k', lt')) :
    ∀ q, k' ≤ q → lt'[q]? = lt[q]? := by
  induction F' generalizing i j k lt with
  | zero =>
    have hpair : (i, j, k, lt) = (i', j', k', lt') := by
      simpa [VecMergeRuns.mergeRunsMainFwd] using hfwd
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
    intro q _
    rfl
  | succ F' ih =>
    by_cases hI : i < mid
    · by_cases hJ : j < hi
      · cases hK : lt[k]? with
        | none =>
          simp only [VecMergeRuns.mergeRunsMainFwd, dite_eq_left hI,
            dite_eq_left hJ, hK] at hfwd
          cases hfwd
        | some w =>
          cases hAi : la[i]? with
          | none =>
            simp only [VecMergeRuns.mergeRunsMainFwd, dite_eq_left hI,
              dite_eq_left hJ, hK, hAi] at hfwd
            cases hfwd
          | some x =>
            cases hAj : la[j]? with
            | none =>
              simp only [VecMergeRuns.mergeRunsMainFwd, dite_eq_left hI,
                dite_eq_left hJ, hK, hAi, hAj] at hfwd
              cases hfwd
            | some y =>
              by_cases hslt : (x.slt y) = true
              · have hfwd' : VecMergeRuns.mergeRunsMainFwd la (lt.set k x)
                    F' (i + 1) j (k + 1) mid hi =
                    .ok (i', j', k', lt') := by
                  simpa [VecMergeRuns.mergeRunsMainFwd, dite_eq_left hI,
                    dite_eq_left hJ, hK, hAi, hAj, hslt] using hfwd
                intro q hq
                have hmono := VecMergeRuns.mergeRunsMain_mono la F'
                  (i + 1) j (k + 1) mid hi (lt.set k x) lt' i' j' k' hfwd'
                have h1 := ih (i + 1) j (k + 1) (lt.set k x) hfwd' q hq
                rw [h1, List.getElem?_set_ne (show k ≠ q by omega)]
              · have hsltF : (x.slt y) = false := by
                  cases h : x.slt y with
                  | true => exact absurd h hslt
                  | false => rfl
                have hfwd' : VecMergeRuns.mergeRunsMainFwd la (lt.set k y)
                    F' i (j + 1) (k + 1) mid hi =
                    .ok (i', j', k', lt') := by
                  simpa [VecMergeRuns.mergeRunsMainFwd, dite_eq_left hI,
                    dite_eq_left hJ, hK, hAi, hAj, hsltF] using hfwd
                intro q hq
                have hmono := VecMergeRuns.mergeRunsMain_mono la F'
                  i (j + 1) (k + 1) mid hi (lt.set k y) lt' i' j' k' hfwd'
                have h1 := ih i (j + 1) (k + 1) (lt.set k y) hfwd' q hq
                rw [h1, List.getElem?_set_ne (show k ≠ q by omega)]
      · have hpair : (i, j, k, lt) = (i', j', k', lt') := by
          simpa [VecMergeRuns.mergeRunsMainFwd, dite_eq_left hI,
            dite_eq_right hJ] using hfwd
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
        intro q _
        rfl
    · have hpair : (i, j, k, lt) = (i', j', k', lt') := by
        simpa [VecMergeRuns.mergeRunsMainFwd, dite_eq_right hI] using hfwd
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
      intro q _
      rfl

/-- Left/right segment split at `mid` (take-window form). -/
theorem take_split_mid (la : List (BitVec 32)) (lo mid hi : Nat)
    (hlo : lo ≤ mid) (hmid : mid ≤ hi) :
    ((la.drop lo).take (hi - lo)) =
      (((la.drop lo).take (mid - lo)) ++
        ((la.drop mid).take (hi - mid))) := by
  have h1 : hi - lo = (mid - lo) + (hi - mid) := by omega
  have h2 : ((la.drop lo).take ((mid - lo) + (hi - mid))) =
      (((la.drop lo).take (mid - lo)) ++
        (((la.drop lo).drop (mid - lo)).take (hi - mid))) :=
    List.take_add
  rw [h1, h2]
  congr 1
  congr 1
  rw [List.drop_drop]
  congr 1
  omega

/-- Drain-`i` sorted+perm: copying the remaining left run keeps
    the merged prefix sorted and extends the permutation. -/
theorem VecMergeRuns.mergeRunsDrainIFwd_sorted_perm (la : List (BitVec 32))
    (F' i k mid lo : Nat) (B : List (BitVec 32))
    (lt lt' : List (BitVec 32)) (k' : Nat)
    (hlo_i : lo ≤ i) (hi_ : i ≤ mid)
    (hlo_k : lo ≤ k) (hk : k ≤ lt.length)
    (hcount : k - lo = (i - lo) + B.length)
    (hla : mid ≤ la.length)
    (hleft : SortedSeg la lo mid)
    (hsorted : SortedSeg lt lo k)
    (hcross : ∀ p, lo ≤ p → p < k → ∀ a, lt[p]? = some a →
      ∀ q, i ≤ q → q < mid → ∀ b, la[q]? = some b →
      (b.slt a) = false)
    (hperm : List.Perm ((lt.drop lo).take (k - lo))
      ((la.drop lo).take (i - lo) ++ B))
    (hread_la : ∀ p, i ≤ p → p < mid → ∃ x, la[p]? = some x)
    (hread_lt : ∀ q, k ≤ q → q < k + (mid - i) → ∃ y, lt[q]? = some y)
    (hF : mid - i ≤ F')
    (hfwd : VecMergeRuns.mergeRunsDrainIFwd la lt F' i k mid =
      .ok (mid, k', lt')) :
    SortedSeg lt' lo k' ∧
    List.Perm ((lt'.drop lo).take (k' - lo))
      (((la.drop lo).take (mid - lo)) ++ B) ∧
    k' = k + (mid - i) ∧ lt'.length = lt.length := by
  induction F' generalizing i k lt with
  | zero =>
    have him : i = mid := by omega
    rw [him] at hfwd hperm ⊢
    have hpair : (mid, k, lt) = (mid, k', lt') := by
      simpa [VecMergeRuns.mergeRunsDrainIFwd] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    exact ⟨hsorted, hperm, by omega, rfl⟩
  | succ F' ih =>
    by_cases hI : i < mid
    · obtain ⟨x, hx⟩ := hread_la i (Nat.le_refl _) hI
      obtain ⟨y, hy⟩ := hread_lt k (Nat.le_refl _) (by omega)
      have hklen : k < lt.length :=
        list_lt_of_getElem?_some lt k y hy
      have hlenA : i < la.length := by omega
      have hxi : la[i] = x := by
        have h1 : la[i]? = some la[i] := List.getElem?_eq_getElem hlenA
        have h2 := h1.symm.trans hx
        exact Option.some_inj.mp h2
      have hfwd' : VecMergeRuns.mergeRunsDrainIFwd la (lt.set k x) F'
          (i + 1) (k + 1) mid = .ok (mid, k', lt') := by
        simpa [VecMergeRuns.mergeRunsDrainIFwd, dite_eq_left hI, hx, hy]
          using hfwd
      have hsorted1 : SortedSeg (lt.set k x) lo (k + 1) :=
        sortedSeg_snoc _ _ _ _ hsorted
          (fun p hlo_p hpk a ha =>
            hcross p hlo_p hpk a ha i (Nat.le_refl _) hI x hx)
          hklen
      have hcross1 : ∀ p, lo ≤ p → p < k + 1 → ∀ a,
          ((lt.set k x)[p]? : Option (BitVec 32)) = some a →
          ∀ q, i + 1 ≤ q → q < mid → ∀ b, la[q]? = some b →
            (b.slt a) = false := by
        intro p hlo_p hpk a ha q hq1 hqm b hb
        by_cases hpk2 : p = k
        · rw [hpk2] at ha
          have hget : ((lt.set k x)[k]? : Option (BitVec 32)) = some x :=
            List.getElem?_set_self hklen
          rw [hget] at ha
          have hax : x = a := Option.some_inj.mp ha
          rw [← hax]
          exact hleft i q (by omega) (by omega) (by omega) x b hx hb
        · have ha' : lt[p]? = some a := by
            have h1 : (((lt.set k x)[p]? : Option (BitVec 32))) =
                lt[p]? := by
              rw [List.getElem?_set_ne (show k ≠ p by omega)]
            rw [h1] at ha
            exact ha
          exact hcross p hlo_p (by omega) a ha' q (by omega) hqm b hb
      have hperm1 : List.Perm ((((lt.set k x).drop lo).take (k + 1 - lo)))
          (((la.drop lo).take (i + 1 - lo)) ++ B) := by
        have hseg : ((lt.set k x).drop lo).take (k + 1 - lo) =
            ((lt.drop lo).take (k - lo)) ++ [x] :=
          perm_seg_snoc lt lo k x (by omega) hklen
        have hsegL : ((la.drop lo).take (i + 1 - lo)) =
            ((la.drop lo).take (i - lo)) ++ [la[i]] :=
          take_snoc la lo i (by omega) (by omega)
        have key : List.Perm ((((la.drop lo).take (i - lo)) ++ B) ++ [x])
            ((((la.drop lo).take (i - lo)) ++ [x]) ++ B) := by
          rw [List.append_assoc,
            List.append_assoc ((la.drop lo).take (i - lo)) [x] B]
          exact List.Perm.rfl.append List.perm_append_comm
        rw [hseg, hsegL, hxi]
        exact (hperm.append List.Perm.rfl).trans key
      obtain ⟨hs1, hp1, hk1, hlen1⟩ :=
        ih (i + 1) (k + 1) (lt.set k x)
          (by omega) (by omega) (by omega)
          (by rw [List.length_set]; omega) (by omega)
          hsorted1 hcross1 hperm1
          (fun p h1 h2 => hread_la p (by omega) h2)
          (fun q h1 h2 => by
            obtain ⟨z, hz⟩ := hread_lt q (by omega) (by omega)
            exact ⟨z, by
              rw [List.getElem?_set_ne (show k ≠ q by omega)]
              exact hz⟩)
          (by omega) hfwd'
      refine ⟨hs1, hp1, by omega, ?_⟩
      rw [hlen1, List.length_set]
    · have him : i = mid := by omega
      rw [him] at hfwd hperm ⊢
      have hpair : (mid, k, lt) = (mid, k', lt') := by
        simpa [VecMergeRuns.mergeRunsDrainIFwd, dite_eq_right hI] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      exact ⟨hsorted, hperm, by omega, rfl⟩

/-- Drain-`j` sorted+perm: copying the remaining right run keeps
    the merged prefix sorted and extends the permutation. -/
theorem VecMergeRuns.mergeRunsDrainJFwd_sorted_perm (la : List (BitVec 32))
    (F' j k mid hi lo : Nat) (P : List (BitVec 32))
    (lt lt' : List (BitVec 32)) (k' : Nat)
    (hmid_j : mid ≤ j) (hj_ : j ≤ hi)
    (hlo_k : lo ≤ k) (hk : k ≤ lt.length)
    (hcount : k - lo = P.length + (j - mid))
    (hla : hi ≤ la.length)
    (hright : SortedSeg la mid hi)
    (hsorted : SortedSeg lt lo k)
    (hcross : ∀ p, lo ≤ p → p < k → ∀ a, lt[p]? = some a →
      ∀ q, j ≤ q → q < hi → ∀ b, la[q]? = some b →
      (b.slt a) = false)
    (hperm : List.Perm ((lt.drop lo).take (k - lo))
      (P ++ (la.drop mid).take (j - mid)))
    (hread_la : ∀ p, j ≤ p → p < hi → ∃ x, la[p]? = some x)
    (hread_lt : ∀ q, k ≤ q → q < k + (hi - j) → ∃ y, lt[q]? = some y)
    (hF : hi - j ≤ F')
    (hfwd : VecMergeRuns.mergeRunsDrainJFwd la lt F' j k hi =
      .ok (hi, k', lt')) :
    SortedSeg lt' lo k' ∧
    List.Perm ((lt'.drop lo).take (k' - lo))
      (P ++ (la.drop mid).take (hi - mid)) ∧
    k' = k + (hi - j) ∧ lt'.length = lt.length := by
  induction F' generalizing j k lt with
  | zero =>
    have hjm : j = hi := by omega
    rw [hjm] at hfwd hperm ⊢
    have hpair : (hi, k, lt) = (hi, k', lt') := by
      simpa [VecMergeRuns.mergeRunsDrainJFwd] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    exact ⟨hsorted, hperm, by omega, rfl⟩
  | succ F' ih =>
    by_cases hJ : j < hi
    · obtain ⟨x, hx⟩ := hread_la j (Nat.le_refl _) hJ
      obtain ⟨y, hy⟩ := hread_lt k (Nat.le_refl _) (by omega)
      have hklen : k < lt.length :=
        list_lt_of_getElem?_some lt k y hy
      have hlenB : j < la.length := by omega
      have hxj : la[j] = x := by
        have h1 : la[j]? = some la[j] := List.getElem?_eq_getElem hlenB
        have h2 := h1.symm.trans hx
        exact Option.some_inj.mp h2
      have hfwd' : VecMergeRuns.mergeRunsDrainJFwd la (lt.set k x) F'
          (j + 1) (k + 1) hi = .ok (hi, k', lt') := by
        simpa [VecMergeRuns.mergeRunsDrainJFwd, dite_eq_left hJ, hx, hy]
          using hfwd
      have hsorted1 : SortedSeg (lt.set k x) lo (k + 1) :=
        sortedSeg_snoc _ _ _ _ hsorted
          (fun p hlo_p hpk a ha =>
            hcross p hlo_p hpk a ha j (Nat.le_refl _) hJ x hx)
          hklen
      have hcross1 : ∀ p, lo ≤ p → p < k + 1 → ∀ a,
          ((lt.set k x)[p]? : Option (BitVec 32)) = some a →
          ∀ q, j + 1 ≤ q → q < hi → ∀ b, la[q]? = some b →
            (b.slt a) = false := by
        intro p hlo_p hpk a ha q hq1 hqh b hb
        by_cases hpk2 : p = k
        · rw [hpk2] at ha
          have hget : ((lt.set k x)[k]? : Option (BitVec 32)) = some x :=
            List.getElem?_set_self hklen
          rw [hget] at ha
          have hax : x = a := Option.some_inj.mp ha
          rw [← hax]
          exact hright j q (by omega) (by omega) (by omega) x b hx hb
        · have ha' : lt[p]? = some a := by
            have h1 : (((lt.set k x)[p]? : Option (BitVec 32))) =
                lt[p]? := by
              rw [List.getElem?_set_ne (show k ≠ p by omega)]
            rw [h1] at ha
            exact ha
          exact hcross p hlo_p (by omega) a ha' q (by omega) hqh b hb
      have hperm1 : List.Perm ((((lt.set k x).drop lo).take (k + 1 - lo)))
          (P ++ ((la.drop mid).take (j + 1 - mid))) := by
        have hseg : ((lt.set k x).drop lo).take (k + 1 - lo) =
            ((lt.drop lo).take (k - lo)) ++ [x] :=
          perm_seg_snoc lt lo k x (by omega) hklen
        have hsegR : ((la.drop mid).take (j + 1 - mid)) =
            ((la.drop mid).take (j - mid)) ++ [la[j]] :=
          take_snoc la mid j (by omega) (by omega)
        rw [hseg, hsegR, hxj, ← List.append_assoc]
        exact hperm.append List.Perm.rfl
      obtain ⟨hs1, hp1, hk1, hlen1⟩ :=
        ih (j + 1) (k + 1) (lt.set k x)
          (by omega) (by omega) (by omega)
          (by rw [List.length_set]; omega) (by omega)
          hsorted1 hcross1 hperm1
          (fun p h1 h2 => hread_la p (by omega) h2)
          (fun q h1 h2 => by
            obtain ⟨z, hz⟩ := hread_lt q (by omega) (by omega)
            exact ⟨z, by
              rw [List.getElem?_set_ne (show k ≠ q by omega)]
              exact hz⟩)
          (by omega) hfwd'
      refine ⟨hs1, hp1, by omega, ?_⟩
      rw [hlen1, List.length_set]
    · have hjm : j = hi := by omega
      rw [hjm] at hfwd hperm ⊢
      have hpair : (hi, k, lt) = (hi, k', lt') := by
        simpa [VecMergeRuns.mergeRunsDrainJFwd, dite_eq_right hJ] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      exact ⟨hsorted, hperm, by omega, rfl⟩

/-- Top-level merge correctness: sorted output window plus
    permutation of the input window, length preserved. -/
theorem VecMergeRuns.mergeRunsFwd_sorted_perm (la lt : List (BitVec 32))
    (lo mid hi : Nat)
    (hlo : lo ≤ mid) (hmid : mid ≤ hi)
    (hla : hi ≤ la.length) (hlt : hi ≤ lt.length)
    (hread_la : ∀ p, lo ≤ p → p < hi → ∃ x, la[p]? = some x)
    (hread_lt : ∀ q, lo ≤ q → q < hi → ∃ y, lt[q]? = some y)
    (hleft : SortedSeg la lo mid) (hright : SortedSeg la mid hi) :
    ∃ lt', VecMergeRuns.mergeRunsFwd la lt lo mid hi = .ok (.stdVecVal lt') ∧
      SortedSeg lt' lo hi ∧
      List.Perm ((lt'.drop lo).take (hi - lo)) ((la.drop lo).take (hi - lo)) ∧
      lt'.length = lt.length := by
  have hsorted0 : SortedSeg lt lo lo := by
    intro p hlo_p hpq hqk a b ha hb
    have hfalse : False := by omega
    exact hfalse.elim
  have hcrossL0 : ∀ p, lo ≤ p → p < lo → ∀ a, lt[p]? = some a →
      ∀ q, lo ≤ q → q < mid → ∀ b, la[q]? = some b →
      (b.slt a) = false := by
    intro p hlo_p hpk a ha q hiq hqm b hb
    have hfalse : False := by omega
    exact hfalse.elim
  have hcrossR0 : ∀ p, lo ≤ p → p < lo → ∀ a, lt[p]? = some a →
      ∀ q, mid ≤ q → q < hi → ∀ b, la[q]? = some b →
      (b.slt a) = false := by
    intro p hlo_p hpk a ha q hjq hqh b hb
    have hfalse : False := by omega
    exact hfalse.elim
  have hperm0 : List.Perm ((lt.drop lo).take (lo - lo))
      ((la.drop lo).take (lo - lo) ++
        (la.drop mid).take (mid - mid)) := by
    have e : lo - lo = 0 := by omega
    have e2 : mid - mid = 0 := by omega
    rw [e, e2]
    simp only [List.take_zero, List.append_nil]
    exact List.Perm.refl _
  obtain ⟨i', j', k', lt', hmain, hexit, hbi, hbj, hm_i, hm_j, _hk_eq,
      hlen_main⟩ :=
    VecMergeRuns.mergeRunsMainFwd_ok la lt ((mid - lo) + (hi - mid))
      lo mid lo mid hi hlo hmid (by omega)
      (fun p h1 h2 => hread_la p (by omega) (by omega))
      (fun p h1 h2 => hread_la p (by omega) (by omega))
      (fun q h1 h2 => hread_lt q (by omega) (by omega))
  obtain ⟨hs_m, hcl_m, hcr_m, hp_m, _, _, _, hk_le, hcount_m, _⟩ :=
    VecMergeRuns.mergeRunsMainFwd_sorted la ((mid - lo) + (hi - mid))
      lo mid lo mid hi lo lt lt' i' j' k'
      (Nat.le_refl _) hlo hmid (Nat.le_refl _) (Nat.le_refl _)
      (by omega) hla (by omega)
      hleft hright hsorted0 hcrossL0 hcrossR0 hperm0 (by omega) hmain
  have esplit := take_split_mid la lo mid hi hlo hmid
  rcases hexit with him | hjm
  · rw [him] at hmain hp_m hcount_m
    have hge := VecMergeRuns.mergeRunsMain_ge la ((mid - lo) + (hi - mid))
      lo mid lo mid hi lt lt' mid j' k' hmain
    have hreadJ : ∀ q, k' ≤ q → q < k' + (hi - j') →
        ∃ y, lt'[q]? = some y := by
      intro q h1 h2
      have hge_q : lt'[q]? = lt[q]? := hge q h1
      rw [hge_q]
      exact hread_lt q (by omega) (by omega)
    have hdi : VecMergeRuns.mergeRunsDrainIFwd la lt' (mid - mid) mid k' mid =
        .ok (mid, k', lt') := by
      have e0 : mid - mid = 0 := Nat.sub_self mid
      rw [e0]
      simp [VecMergeRuns.mergeRunsDrainIFwd]
    obtain ⟨k'', lt'', hdj, _, _⟩ :=
      VecMergeRuns.mergeRunsDrainJFwd_ok la lt' (hi - j') j' k' hi
        (by omega) (by omega)
        (fun p h1 h2 => hread_la p (by omega) (by omega))
        hreadJ
    have hPlen : ((la.drop lo).take (mid - lo)).length = mid - lo := by
      rw [List.length_take, List.length_drop,
        Nat.min_eq_left (by omega)]
    obtain ⟨hs_j, hp_j, hk_j, hlen_j⟩ :=
      VecMergeRuns.mergeRunsDrainJFwd_sorted_perm la (hi - j') j' k'
        mid hi lo ((la.drop lo).take (mid - lo)) lt' lt'' k''
        (by omega) hbj (by omega) hk_le (by omega) hla hright
        hs_m hcr_m hp_m
        (fun p h1 h2 => hread_la p (by omega) (by omega))
        hreadJ
        (by omega) hdj
    have hkhi : k'' = hi := by omega
    refine ⟨lt'', VecMergeRuns.mergeRunsFwd_ok la lt lo mid hi
      mid j' k' k' k'' lt' lt' lt'' hmain hdi hdj, ?_, ?_, ?_⟩
    · rw [hkhi] at hs_j; exact hs_j
    · have e1 : k'' - lo = hi - lo := by omega
      rw [e1] at hp_j
      rw [esplit]
      exact hp_j
    · exact hlen_j.trans hlen_main
  · have hge := VecMergeRuns.mergeRunsMain_ge la ((mid - lo) + (hi - mid))
      lo mid lo mid hi lt lt' i' j' k' hmain
    have hreadI : ∀ q, k' ≤ q → q < k' + (mid - i') →
        ∃ y, lt'[q]? = some y := by
      intro q h1 h2
      have hge_q : lt'[q]? = lt[q]? := hge q h1
      rw [hge_q]
      exact hread_lt q (by omega) (by omega)
    obtain ⟨k'', lt'', hdi, _, _⟩ :=
      VecMergeRuns.mergeRunsDrainIFwd_ok la lt' (mid - i') i' k' mid
        (by omega) (by omega)
        (fun p h1 h2 => hread_la p (by omega) (by omega))
        hreadI
    have hBlen : ((la.drop mid).take (j' - mid)).length = j' - mid := by
      rw [List.length_take, List.length_drop,
        Nat.min_eq_left (by omega)]
    obtain ⟨hs_i, hp_i, hk_i, hlen_i⟩ :=
      VecMergeRuns.mergeRunsDrainIFwd_sorted_perm la (mid - i') i' k'
        mid lo ((la.drop mid).take (j' - mid)) lt' lt'' k''
        (by omega) hbi (by omega) hk_le (by omega) (by omega)
        hleft hs_m hcl_m hp_m
        (fun p h1 h2 => hread_la p (by omega) (by omega))
        hreadI
        (by omega) hdi
    rw [hjm] at hmain hp_i hcount_m hBlen
    have hdj : VecMergeRuns.mergeRunsDrainJFwd la lt'' (hi - hi) hi k'' hi =
        .ok (hi, k'', lt'') := by
      have e0 : hi - hi = 0 := Nat.sub_self hi
      rw [e0]
      simp [VecMergeRuns.mergeRunsDrainJFwd]
    have hkhi : k'' = hi := by omega
    refine ⟨lt'', VecMergeRuns.mergeRunsFwd_ok la lt lo mid hi
      i' hi k' k'' k'' lt' lt'' lt'' hmain hdi hdj, ?_, ?_, ?_⟩
    · rw [hkhi] at hs_i; exact hs_i
    · have e1 : k'' - lo = hi - lo := by omega
      rw [e1] at hp_i
      rw [esplit]
      exact hp_i
    · exact hlen_i.trans hlen_main
/-- Drain-`i` cursor never moves down. -/
theorem VecMergeRuns.mergeRunsDrainI_mono (la : List (BitVec 32))
    (F' i k mid : Nat)
    (lt lt' : List (BitVec 32)) (k' : Nat)
    (hfwd : VecMergeRuns.mergeRunsDrainIFwd la lt F' i k mid =
      .ok (mid, k', lt')) :
    k ≤ k' := by
  induction F' generalizing i k lt with
  | zero =>
    have hpair : (i, k, lt) = (mid, k', lt') := by
      simpa [VecMergeRuns.mergeRunsDrainIFwd] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    omega
  | succ F' ih =>
    by_cases hI : i < mid
    · cases hK : lt[k]? with
      | none =>
        simp only [VecMergeRuns.mergeRunsDrainIFwd, dite_eq_left hI,
          hK] at hfwd
        cases hfwd
      | some y =>
        cases hAi : la[i]? with
        | none =>
          simp only [VecMergeRuns.mergeRunsDrainIFwd, dite_eq_left hI,
            hK, hAi] at hfwd
          cases hfwd
        | some x =>
          have hfwd' : VecMergeRuns.mergeRunsDrainIFwd la (lt.set k x) F'
              (i + 1) (k + 1) mid = .ok (mid, k', lt') := by
            simpa [VecMergeRuns.mergeRunsDrainIFwd, dite_eq_left hI, hK,
              hAi] using hfwd
          have h1 := ih (i + 1) (k + 1) (lt.set k x) hfwd'
          omega
    · have hpair : (i, k, lt) = (mid, k', lt') := by
        simpa [VecMergeRuns.mergeRunsDrainIFwd, dite_eq_right hI] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      omega

/-- Drain-`i` writes stay below the final cursor. -/
theorem VecMergeRuns.mergeRunsDrainI_ge (la : List (BitVec 32))
    (F' i k mid : Nat)
    (lt lt' : List (BitVec 32)) (k' : Nat)
    (hfwd : VecMergeRuns.mergeRunsDrainIFwd la lt F' i k mid =
      .ok (mid, k', lt')) :
    ∀ q, k' ≤ q → lt'[q]? = lt[q]? := by
  induction F' generalizing i k lt with
  | zero =>
    have hpair : (i, k, lt) = (mid, k', lt') := by
      simpa [VecMergeRuns.mergeRunsDrainIFwd] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    intro q _
    rfl
  | succ F' ih =>
    by_cases hI : i < mid
    · cases hK : lt[k]? with
      | none =>
        simp only [VecMergeRuns.mergeRunsDrainIFwd, dite_eq_left hI,
          hK] at hfwd
        cases hfwd
      | some y =>
        cases hAi : la[i]? with
        | none =>
          simp only [VecMergeRuns.mergeRunsDrainIFwd, dite_eq_left hI,
            hK, hAi] at hfwd
          cases hfwd
        | some x =>
          have hfwd' : VecMergeRuns.mergeRunsDrainIFwd la (lt.set k x) F'
              (i + 1) (k + 1) mid = .ok (mid, k', lt') := by
            simpa [VecMergeRuns.mergeRunsDrainIFwd, dite_eq_left hI, hK,
              hAi] using hfwd
          intro q hq
          have hmono := VecMergeRuns.mergeRunsDrainI_mono la F' (i + 1)
            (k + 1) mid (lt.set k x) lt' k' hfwd'
          have h1 := ih (i + 1) (k + 1) (lt.set k x) hfwd' q hq
          rw [h1, List.getElem?_set_ne (show k ≠ q by omega)]
    · have hpair : (i, k, lt) = (mid, k', lt') := by
        simpa [VecMergeRuns.mergeRunsDrainIFwd, dite_eq_right hI] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      intro q _
      rfl

/-- Drain-`j` cursor never moves down. -/
theorem VecMergeRuns.mergeRunsDrainJ_mono (la : List (BitVec 32))
    (F' j k hi : Nat)
    (lt lt' : List (BitVec 32)) (k' : Nat)
    (hfwd : VecMergeRuns.mergeRunsDrainJFwd la lt F' j k hi =
      .ok (hi, k', lt')) :
    k ≤ k' := by
  induction F' generalizing j k lt with
  | zero =>
    have hpair : (j, k, lt) = (hi, k', lt') := by
      simpa [VecMergeRuns.mergeRunsDrainJFwd] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    omega
  | succ F' ih =>
    by_cases hJ : j < hi
    · cases hK : lt[k]? with
      | none =>
        simp only [VecMergeRuns.mergeRunsDrainJFwd, dite_eq_left hJ,
          hK] at hfwd
        cases hfwd
      | some y =>
        cases hAj : la[j]? with
        | none =>
          simp only [VecMergeRuns.mergeRunsDrainJFwd, dite_eq_left hJ,
            hK, hAj] at hfwd
          cases hfwd
        | some x =>
          have hfwd' : VecMergeRuns.mergeRunsDrainJFwd la (lt.set k x) F'
              (j + 1) (k + 1) hi = .ok (hi, k', lt') := by
            simpa [VecMergeRuns.mergeRunsDrainJFwd, dite_eq_left hJ, hK,
              hAj] using hfwd
          have h1 := ih (j + 1) (k + 1) (lt.set k x) hfwd'
          omega
    · have hpair : (j, k, lt) = (hi, k', lt') := by
        simpa [VecMergeRuns.mergeRunsDrainJFwd, dite_eq_right hJ] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      omega

/-- Drain-`j` writes stay below the final cursor. -/
theorem VecMergeRuns.mergeRunsDrainJ_ge (la : List (BitVec 32))
    (F' j k hi : Nat)
    (lt lt' : List (BitVec 32)) (k' : Nat)
    (hfwd : VecMergeRuns.mergeRunsDrainJFwd la lt F' j k hi =
      .ok (hi, k', lt')) :
    ∀ q, k' ≤ q → lt'[q]? = lt[q]? := by
  induction F' generalizing j k lt with
  | zero =>
    have hpair : (j, k, lt) = (hi, k', lt') := by
      simpa [VecMergeRuns.mergeRunsDrainJFwd] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    intro q _
    rfl
  | succ F' ih =>
    by_cases hJ : j < hi
    · cases hK : lt[k]? with
      | none =>
        simp only [VecMergeRuns.mergeRunsDrainJFwd, dite_eq_left hJ,
          hK] at hfwd
        cases hfwd
      | some y =>
        cases hAj : la[j]? with
        | none =>
          simp only [VecMergeRuns.mergeRunsDrainJFwd, dite_eq_left hJ,
            hK, hAj] at hfwd
          cases hfwd
        | some x =>
          have hfwd' : VecMergeRuns.mergeRunsDrainJFwd la (lt.set k x) F'
              (j + 1) (k + 1) hi = .ok (hi, k', lt') := by
            simpa [VecMergeRuns.mergeRunsDrainJFwd, dite_eq_left hJ, hK,
              hAj] using hfwd
          intro q hq
          have hmono := VecMergeRuns.mergeRunsDrainJ_mono la F' (j + 1)
            (k + 1) hi (lt.set k x) lt' k' hfwd'
          have h1 := ih (j + 1) (k + 1) (lt.set k x) hfwd' q hq
          rw [h1, List.getElem?_set_ne (show k ≠ q by omega)]
    · have hpair : (j, k, lt) = (hi, k', lt') := by
        simpa [VecMergeRuns.mergeRunsDrainJFwd, dite_eq_right hJ] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      intro q _
      rfl

/-- Copy-back joint: equation, sortedness, window equality,
    cursor, length, and framing outside `[lo, hi)`. -/
theorem VecMergeSort.sortCopyFwd_joint (lt : List (BitVec 32))
    (F' t hi lo : Nat)
    (la : List (BitVec 32))
    (hlo_t : lo ≤ t) (ht_hi : t ≤ hi)
    (hsorted : SortedSeg lt lo hi)
    (heq : ∀ p, lo ≤ p → p < t → la[p]? = lt[p]?)
    (hread_lt : ∀ q, t ≤ q → q < hi → ∃ y, lt[q]? = some y)
    (hread_la : ∀ p, t ≤ p → p < hi → ∃ x, la[p]? = some x)
    (hF : hi - t ≤ F') :
    ∃ la' t', VecMergeSort.sortCopyFwd lt la F' t hi = .ok (la', t') ∧
    SortedSeg la' lo hi ∧
    (∀ p, lo ≤ p → p < hi → la'[p]? = lt[p]?) ∧
    t' = hi ∧ la'.length = la.length ∧
    (∀ q, (q < lo ∨ hi ≤ q) → la'[q]? = la[q]?) := by
  induction F' generalizing t la with
  | zero =>
    have him : t = hi := by omega
    refine ⟨la, t, ?_, ?_, ?_, him, rfl, ?_⟩
    · simp [VecMergeSort.sortCopyFwd]
    · intro p q hlo_p hpq hqk a b ha hb
      have e1 : lt[p]? = some a := by
        rw [← heq p hlo_p (by omega)]; exact ha
      have e2 : lt[q]? = some b := by
        rw [← heq q (by omega) (by omega)]; exact hb
      exact hsorted p q hlo_p hpq hqk a b e1 e2
    · intro p hlo_p hph
      exact heq p hlo_p (by omega)
    · intro q _
      rfl
  | succ F' ih =>
    by_cases hT : t < hi
    · obtain ⟨x, hx⟩ := hread_lt t (Nat.le_refl _) hT
      obtain ⟨xA, hxA⟩ := hread_la t (Nat.le_refl _) hT
      have hklen : t < lt.length := pos_lt_of_getElem?_some hx
      have hlenA : t < la.length := pos_lt_of_getElem?_some hxA
      have hsorted_la : SortedSeg la lo t := by
        intro p q hlo_p hpq hqk a b ha hb
        have e1 : lt[p]? = some a := by
          rw [← heq p hlo_p (by omega)]; exact ha
        have e2 : lt[q]? = some b := by
          rw [← heq q (by omega) (by omega)]; exact hb
        exact hsorted p q hlo_p (by omega) (by omega) a b e1 e2
      have hsorted1 : SortedSeg (la.set t x) lo (t + 1) :=
        sortedSeg_snoc _ _ _ _ hsorted_la
          (fun p hlo_p hpk a ha =>
            have e : lt[p]? = some a := by
              rw [← heq p hlo_p hpk]; exact ha
            hsorted p t hlo_p hpk (by omega) a x e hx)
          hlenA
      have heq1 : ∀ p, lo ≤ p → p < t + 1 → (la.set t x)[p]? = lt[p]? := by
        intro p h1 h2
        by_cases hpt : p = t
        · rw [hpt, List.getElem?_set_self hlenA]
          exact hx.symm
        · rw [List.getElem?_set_ne (show t ≠ p by omega)]
          exact heq p h1 (by omega)
      obtain ⟨la', t', heq_ih, hs1, heq1', ht1, hlen1, hframe1⟩ :=
        ih (t + 1) (la.set t x)
          (by omega) (by omega) heq1
          (fun q h1 h2 => hread_lt q (by omega) h2)
          (fun p h1 h2 => by
            obtain ⟨z, hz⟩ := hread_la p (by omega) (by omega)
            exact ⟨z, by
              rw [List.getElem?_set_ne (show t ≠ p by omega)]
              exact hz⟩)
          (by omega)
      have hcur : VecMergeSort.sortCopyFwd lt la (F' + 1) t hi =
          .ok (la', t') := by
        simp only [VecMergeSort.sortCopyFwd, dite_eq_left hT, hx, hxA]
        exact heq_ih
      refine ⟨la', t', hcur, hs1, heq1', ht1, ?_, ?_⟩
      · rw [hlen1, List.length_set]
      · intro q hq
        have h1 := hframe1 q hq
        rw [h1, List.getElem?_set_ne (show t ≠ q by omega)]
    · have him : t = hi := by omega
      refine ⟨la, t, ?_, ?_, ?_, him, rfl, ?_⟩
      · simp only [VecMergeSort.sortCopyFwd, dite_eq_right hT]
      · intro p q hlo_p hpq hqk a b ha hb
        have e1 : lt[p]? = some a := by
          rw [← heq p hlo_p (by omega)]; exact ha
        have e2 : lt[q]? = some b := by
          rw [← heq q (by omega) (by omega)]; exact hb
        exact hsorted p q hlo_p hpq hqk a b e1 e2
      · intro p hlo_p hph
        exact heq p hlo_p (by omega)
      · intro q _
        rfl

/-- Take-window congruence from pointwise reads. -/
theorem take_eq_of_frame (l1 l2 : List (BitVec 32)) (lo : Nat)
    (h : ∀ q, q < lo → l1[q]? = l2[q]?) : l1.take lo = l2.take lo := by
  apply List.ext_getElem?
  intro p
  rw [List.getElem?_take, List.getElem?_take]
  by_cases hp : p < lo
  · rw [ite_eq_left hp, ite_eq_left hp]
    exact h p hp
  · rw [ite_eq_right hp, ite_eq_right hp]

/-- Drop congruence from pointwise reads above the cut. -/
theorem drop_eq_of_frame (l1 l2 : List (BitVec 32)) (hi : Nat)
    (h : ∀ q, hi ≤ q → l1[q]? = l2[q]?) : l1.drop hi = l2.drop hi := by
  apply List.ext_getElem?
  intro p
  rw [List.getElem?_drop, List.getElem?_drop]
  exact h (hi + p) (by omega)

/-- Window replacement by a permutation preserves permutation. -/
theorem perm_window_splice (la la'' : List (BitVec 32)) (lo hi : Nat)
    (hlohi : lo ≤ hi)
    (hwin : List.Perm ((la''.drop lo).take (hi - lo))
      ((la.drop lo).take (hi - lo)))
    (hframe : ∀ q, (q < lo ∨ hi ≤ q) → la''[q]? = la[q]?) :
    List.Perm la'' la := by
  have htake : la''.take lo = la.take lo :=
    take_eq_of_frame _ _ _ (fun q hq => hframe q (Or.inl hq))
  have hdrop : la''.drop hi = la.drop hi :=
    drop_eq_of_frame _ _ _ (fun q hq => hframe q (Or.inr hq))
  have splice : ∀ l : List (BitVec 32),
      l = l.take lo ++ ((l.drop lo).take (hi - lo)) ++ (l.drop hi) := by
    intro l
    have hdd : ((l.drop lo).drop (hi - lo)) = l.drop hi := by
      rw [List.drop_drop]
      congr 1
      omega
    have htd : ((l.drop lo).take (hi - lo)) ++
        ((l.drop lo).drop (hi - lo)) = l.drop lo :=
      List.take_append_drop _ _
    calc l = l.take lo ++ l.drop lo := (List.take_append_drop lo l).symm
      _ = l.take lo ++ ((l.drop lo).take (hi - lo)) ++
          ((l.drop lo).drop (hi - lo)) := by
            conv => lhs; rw [← htd, ← List.append_assoc]
      _ = l.take lo ++ ((l.drop lo).take (hi - lo)) ++ (l.drop hi) := by
            rw [hdd]
  rw [splice la'', splice la, htake, hdrop]
  exact List.Perm.append (List.Perm.append (List.Perm.refl _) hwin)
    (List.Perm.refl _)

/-- Sortedness transports across pointwise-equal windows. -/
theorem SortedSeg_congr (l1 l2 : List (BitVec 32)) (lo hi : Nat)
    (h : ∀ p, lo ≤ p → p < hi → l1[p]? = l2[p]?)
    (hs : SortedSeg l1 lo hi) : SortedSeg l2 lo hi := by
  intro p q hlo_p hpq hqk a b ha hb
  have e1 : l1[p]? = some a := by rw [h p hlo_p (by omega)]; exact ha
  have e2 : l1[q]? = some b := by rw [h q (by omega) (by omega)]; exact hb
  exact hs p q hlo_p hpq hqk a b e1 e2

/-- Blocked-sorted: every width-`w` block below `n` is sorted. -/
def BlockedSorted (la : List (BitVec 32)) (w n : Nat) : Prop :=
  ∀ b, b * w < n → SortedSeg la (b * w) (Nat.min ((b + 1) * w) n)

/-- Width-1 blocks are trivially sorted. -/
theorem blockedSorted_one (la : List (BitVec 32)) (n : Nat) :
    BlockedSorted la 1 n := by
  intro b hb
  intro p q hlo_p hpq hqk a b_ ha hb_
  have hfalse : False := by
    have hq1 : q < (b + 1) * 1 :=
      Nat.lt_of_lt_of_le hqk (Nat.min_le_left _ _)
    omega
  exact hfalse.elim

/-- Segment invariant: done 2w-blocks below `lo`, w-blocks from `lo`. -/
def MergeSegInv (la : List (BitVec 32)) (w lo n : Nat) : Prop :=
  (∃ B, lo = B * (w + w)) ∧
  (∀ b, b * (w + w) < lo →
    SortedSeg la (b * (w + w)) (Nat.min ((b + 1) * (w + w)) n)) ∧
  (∀ b, lo ≤ b * w → b * w < n →
    SortedSeg la (b * w) (Nat.min ((b + 1) * w) n))

/-- Add on the left through a truncated subtraction. -/
theorem add_lt_of_sub_lt (lo p hi : Nat) (hle : lo ≤ hi) (hp : p < hi - lo) :
    lo + p < hi := by
  omega

/-- Segment pass joint: equation, lengths, readability,
    permutation, and blocked-sorted output. -/
theorem VecMergeSort.sortSegFwd_joint (la lt : List (BitVec 32))
    (F w lo n : Nat)
    (hw : 0 < w)
    (hla_len : la.length = n) (hlt_len : n ≤ lt.length)
    (hread_la : ∀ p, p < n → ∃ x, la[p]? = some x)
    (hread_lt : ∀ q, q < n → ∃ y, lt[q]? = some y)
    (hinv : MergeSegInv la w lo n)
    (hF : 2 * (n - lo) + 9 ≤ F) :
    ∃ la' lt', VecMergeSort.sortSegFwd la lt F w lo n = .ok (la', lt') ∧
    la'.length = n ∧ n ≤ lt'.length ∧
    (∀ p, p < n → ∃ x, la'[p]? = some x) ∧
    (∀ q, q < n → ∃ y, lt'[q]? = some y) ∧
    List.Perm la' la ∧
    BlockedSorted la' (w + w) n := by
  induction F generalizing la lt lo with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F' ih =>
    obtain ⟨hdiv, hdone, htodo⟩ := hinv
    by_cases hL : lo < n
    · obtain ⟨B, hB⟩ := hdiv
      have eb : (B + B) * w = lo := by
        have e1 : (B + B) * w = B * w + B * w := Nat.add_mul B B w
        have e2 : B * (w + w) = B * w + B * w := Nat.mul_add B w w
        omega
      have eb2 : ((B + B) + 1) * w = lo + w := by
        have eadd : ((B + B) + 1) * w = (B + B) * w + w := by
          have e1 : ((B + B) + 1) * w = (B + B) * w + 1 * w :=
            Nat.add_mul _ _ _
          rw [e1, Nat.one_mul]
        rw [eadd, eb]
      have hT1 : SortedSeg la ((B + B) * w)
          (Nat.min (((B + B) + 1) * w) n) :=
        htodo (B + B) (by omega) (by omega)
      rw [eb, eb2] at hT1
      have step : ∀ (hleft : SortedSeg la lo (Nat.min (lo + w) n))
          (hright : SortedSeg la (Nat.min (lo + w) n)
            (Nat.min (lo + w + w) n)),
          ∃ la' lt', VecMergeSort.sortSegFwd la lt (F' + 1) w lo n =
            .ok (la', lt') ∧
          la'.length = n ∧ n ≤ lt'.length ∧
          (∀ p, p < n → ∃ x, la'[p]? = some x) ∧
          (∀ q, q < n → ∃ y, lt'[q]? = some y) ∧
          List.Perm la' la ∧
          BlockedSorted la' (w + w) n := by
        intro hleft hright
        obtain ⟨ltm, hmerge, hs_m, hp_m, hlen_m⟩ :=
          VecMergeRuns.mergeRunsFwd_sorted_perm la lt lo
            (Nat.min (lo + w) n) (Nat.min (lo + w + w) n)
            (Nat.le_min.mpr ⟨Nat.le_add_right _ _, Nat.le_of_lt hL⟩)
            (Nat.le_min.mpr
              ⟨Nat.le_trans (Nat.min_le_left _ _) (Nat.le_add_right _ _),
                Nat.min_le_right _ _⟩)
            (by rw [← hla_len]; exact Nat.min_le_right _ _)
            (Nat.le_trans (Nat.min_le_right _ _) hlt_len)
            (fun p h1 h2 => hread_la p
              (Nat.lt_of_lt_of_le h2 (Nat.min_le_right _ _)))
            (fun q h1 h2 => hread_lt q
              (Nat.lt_of_lt_of_le h2 (Nat.min_le_right _ _)))
            hleft hright
        obtain ⟨la1, t1, hcopy, hs_c, heq_c, ht1, hlen_c, hframe_c⟩ :=
          VecMergeSort.sortCopyFwd_joint ltm
            (Nat.min (lo + w + w) n - lo) lo
            (Nat.min (lo + w + w) n) lo la
            (Nat.le_refl _)
            (Nat.le_min.mpr ⟨by omega, Nat.le_of_lt hL⟩) hs_m
            (fun p h1 h2 => absurd h2 (by omega))
            (fun q h1 h2 =>
              have hqn : q < n :=
                Nat.lt_of_lt_of_le h2 (Nat.min_le_right _ _)
              have hql : q < ltm.length := by omega
              ⟨ltm[q], List.getElem?_eq_getElem hql⟩)
            (fun p h1 h2 => hread_la p
              (Nat.lt_of_lt_of_le h2 (Nat.min_le_right _ _)))
            (Nat.le_refl _)
        have hwin : List.Perm
            ((la1.drop lo).take (Nat.min (lo + w + w) n - lo))
            ((la.drop lo).take (Nat.min (lo + w + w) n - lo)) := by
          have e : ((la1.drop lo).take (Nat.min (lo + w + w) n - lo)) =
              ((ltm.drop lo).take (Nat.min (lo + w + w) n - lo)) := by
            apply List.ext_getElem?
            intro p
            rw [List.getElem?_take, List.getElem?_take,
              List.getElem?_drop, List.getElem?_drop]
            by_cases hp : p < Nat.min (lo + w + w) n - lo
            · rw [ite_eq_left hp, ite_eq_left hp]
              exact heq_c (lo + p) (by omega)
                (add_lt_of_sub_lt lo p _ (Nat.le_min.mpr
                  ⟨by omega, Nat.le_of_lt hL⟩) hp)
            · rw [ite_eq_right hp, ite_eq_right hp]
          rw [e]; exact hp_m
        have hstep_perm : List.Perm la1 la :=
          perm_window_splice la la1 lo (Nat.min (lo + w + w) n)
            (Nat.le_min.mpr ⟨by omega, Nat.le_of_lt hL⟩)
            hwin (fun q hq => hframe_c q hq)
        have hread_la1 : ∀ p, p < n → ∃ x, la1[p]? = some x := by
          intro p hp
          by_cases hplo : p < lo
          · obtain ⟨x, hx⟩ := hread_la p hp
            exact ⟨x, by rw [hframe_c p (Or.inl hplo)]; exact hx⟩
          · by_cases hphi : Nat.min (lo + w + w) n ≤ p
            · obtain ⟨x, hx⟩ := hread_la p hp
              exact ⟨x, by rw [hframe_c p (Or.inr hphi)]; exact hx⟩
            · have hql : p < la1.length := by omega
              exact ⟨la1[p], List.getElem?_eq_getElem hql⟩
        have hread_lt1 : ∀ q, q < n → ∃ y, ltm[q]? = some y := by
          intro q hq
          exact ⟨ltm[q], List.getElem?_eq_getElem (by omega)⟩
        have hdone1 : ∀ b, b * (w + w) < lo + w + w →
            SortedSeg la1 (b * (w + w))
              (Nat.min ((b + 1) * (w + w)) n) := by
          intro b hb2
          by_cases hbB : b * (w + w) < lo
          · have hble : (b + 1) * (w + w) ≤ lo := by
              have hlt : b + 1 ≤ B := by
                have h1 : b * (w + w) < B * (w + w) := by
                  rw [← hB]; exact hbB
                have h2 : b < B := Nat.lt_of_mul_lt_mul_right h1
                omega
              have hm := Nat.mul_le_mul_right (w + w) hlt
              rw [← hB] at hm
              exact hm
            exact SortedSeg_congr la la1 _ _
              (fun p h1 h2 =>
                have hlt : p < (b + 1) * (w + w) :=
                  Nat.lt_of_lt_of_le h2 (Nat.min_le_left _ _)
                (hframe_c p (Or.inl (by omega))).symm)
              (hdone b hbB)
          · have ebb : b = B := by
              have hgeB : B ≤ b := by
                have h1 : lo ≤ b * (w + w) := Nat.le_of_not_lt hbB
                have eS : (b + 1) * (w + w) =
                    b * (w + w) + (w + w) := by
                  have e1 : (b + 1) * (w + w) =
                      b * (w + w) + 1 * (w + w) := Nat.add_mul _ _ _
                  rw [e1, Nat.one_mul]
                have h2 : B * (w + w) < (b + 1) * (w + w) := by
                  rw [eS]; omega
                have h3 : B < b + 1 := Nat.lt_of_mul_lt_mul_right h2
                omega
              have hlt2 : b * (w + w) < (B + 1) * (w + w) := by
                have eS : (B + 1) * (w + w) =
                    B * (w + w) + (w + w) := by
                  have e1 : (B + 1) * (w + w) =
                      B * (w + w) + 1 * (w + w) := Nat.add_mul _ _ _
                  rw [e1, Nat.one_mul]
                rw [eS]
                omega
              have hltB2 : b < B + 1 := Nat.lt_of_mul_lt_mul_right hlt2
              omega
            have eblk : b * (w + w) = lo := by rw [ebb, hB]
            have eblk2 : (b + 1) * (w + w) = lo + w + w := by
              have eadd : (b + 1) * (w + w) =
                  b * (w + w) + (w + w) := by
                have e1 : (b + 1) * (w + w) =
                    b * (w + w) + 1 * (w + w) := Nat.add_mul _ _ _
                rw [e1, Nat.one_mul]
              rw [eadd, eblk, Nat.add_assoc]
            rw [eblk, eblk2]
            exact hs_c
        have htodo1 : ∀ b, lo + w + w ≤ b * w → b * w < n →
            SortedSeg la1 (b * w) (Nat.min ((b + 1) * w) n) := by
          intro b h1 h2
          have hold : SortedSeg la (b * w) (Nat.min ((b + 1) * w) n) :=
            htodo b (by omega) h2
          exact SortedSeg_congr la la1 _ _
            (fun p hp1 hp2 =>
              have hge : Nat.min (lo + w + w) n ≤ p :=
                Nat.le_trans (Nat.min_le_left _ _)
                  (Nat.le_trans h1 hp1)
              (hframe_c p (Or.inr hge)).symm) hold
        have hinv1 : MergeSegInv la1 w (lo + w + w) n :=
          ⟨⟨B + 1, by
              have e : (B + 1) * (w + w) =
                  B * (w + w) + (w + w) := by
                have e1 : (B + 1) * (w + w) =
                    B * (w + w) + 1 * (w + w) := Nat.add_mul _ _ _
                rw [e1, Nat.one_mul]
              omega⟩, hdone1, htodo1⟩
        obtain ⟨la', lt', heq_ih, hlen1, hltlen1, hread_la2, hread_lt2,
            hperm_ih, hblock⟩ :=
          ih la1 ltm (lo + w + w)
            (by rw [hlen_c]; exact hla_len)
            (by rw [hlen_m]; exact hlt_len)
            hread_la1 hread_lt1 hinv1 (by omega)
        have hcur : VecMergeSort.sortSegFwd la lt (F' + 1) w lo n =
            .ok (la', lt') := by
          simp only [VecMergeSort.sortSegFwd, dite_eq_left hL, hmerge, hcopy]
          exact heq_ih
        exact ⟨la', lt', hcur, hlen1, hltlen1, hread_la2, hread_lt2,
          hperm_ih.trans hstep_perm, hblock⟩
      by_cases hmid : lo + w < n
      · have m1 : Nat.min (lo + w) n = lo + w :=
          Nat.min_eq_left (by omega)
        have hT2 : SortedSeg la (((B + B) + 1) * w)
            (Nat.min (((((B + B) + 1)) + 1) * w) n) :=
          htodo ((B + B) + 1) (by omega) (by omega)
        have eB3 : ((((B + B) + 1)) + 1) * w = lo + w + w := by
          have eadd : ((((B + B) + 1)) + 1) * w =
              (((B + B) + 1)) * w + w := by
            have e1 : ((((B + B) + 1)) + 1) * w =
                (((B + B) + 1)) * w + 1 * w := Nat.add_mul _ _ _
            rw [e1, Nat.one_mul]
          rw [eadd, eb2]
        rw [eb2, eB3] at hT2
        have hT2' : SortedSeg la (Nat.min (lo + w) n)
            (Nat.min (lo + w + w) n) := by
          rw [m1]
          exact hT2
        exact step hT1 hT2'
      · have m1 : Nat.min (lo + w) n = n :=
          Nat.min_eq_right (by omega)
        have m2 : Nat.min (lo + w + w) n = n :=
          Nat.min_eq_right (by omega)
        have hleft : SortedSeg la lo (Nat.min (lo + w) n) := by
          rw [m1] at hT1 ⊢
          exact hT1
        have hright : SortedSeg la (Nat.min (lo + w) n)
            (Nat.min (lo + w + w) n) := by
          rw [m1, m2]
          intro p q hlo_p hpq hqk a b ha hb
          have hfalse : False := by omega
          exact hfalse.elim
        exact step hleft hright
    · have hcur : VecMergeSort.sortSegFwd la lt (F' + 1) w lo n =
        .ok (la, lt) := by
        simp only [VecMergeSort.sortSegFwd, dite_eq_right hL]
      have hblock0 : BlockedSorted la (w + w) n := by
        intro b hb
        exact hdone b (by omega)
      exact ⟨la, lt, hcur, hla_len, hlt_len, hread_la, hread_lt,
        List.Perm.refl _, hblock0⟩

/-- Outer pass joint: equation, lengths, readability,
    permutation to the original input, and full sortedness. -/
theorem VecMergeSort.sortOuterFwd_joint (la lt : List (BitVec 32))
    (F w n : Nat) (la₀ : List (BitVec 32))
    (hw1 : 1 ≤ w)
    (hla_len : la.length = n) (hlt_len : n ≤ lt.length)
    (hread_la : ∀ p, p < n → ∃ x, la[p]? = some x)
    (hread_lt : ∀ q, q < n → ∃ y, lt[q]? = some y)
    (hblock : BlockedSorted la w n)
    (hperm : List.Perm la la₀)
    (hF : 2 * (n - w) + 2 * n + 10 ≤ F) :
    ∃ la' lt', VecMergeSort.sortOuterFwd la lt F w n = .ok (la', lt') ∧
    la'.length = n ∧ n ≤ lt'.length ∧
    (∀ p, p < n → ∃ x, la'[p]? = some x) ∧
    (∀ q, q < n → ∃ y, lt'[q]? = some y) ∧
    List.Perm la' la₀ ∧
    SortedSeg la' 0 n := by
  induction F generalizing la lt w with
  | zero =>
    have hfalse : False := by omega
    exact hfalse.elim
  | succ F' ih =>
    by_cases hW : w < n
    · have hinv0 : MergeSegInv la w 0 n :=
        ⟨⟨0, (Nat.zero_mul _).symm⟩,
          fun b hb => absurd hb (by omega),
          fun b _ h2 => hblock b h2⟩
      obtain ⟨la1, lt1, hseg, hlen1, hltlen1, hread_la1, hread_lt1,
          hperm1, hblock1⟩ :=
        VecMergeSort.sortSegFwd_joint la lt F' w 0 n
          (by omega) hla_len hlt_len hread_la hread_lt hinv0 (by omega)
      obtain ⟨la', lt', heq_ih, hlen2, hltlen2, hread_la2, hread_lt2,
          hperm_ih, hsort⟩ :=
        ih la1 lt1 (w + w)
          (by omega) hlen1 hltlen1 hread_la1 hread_lt1 hblock1
          (hperm1.trans hperm) (by omega)
      have hcur : VecMergeSort.sortOuterFwd la lt (F' + 1) w n =
          .ok (la', lt') := by
        simp only [VecMergeSort.sortOuterFwd, dite_eq_left hW, hseg]
        exact heq_ih
      exact ⟨la', lt', hcur, hlen2, hltlen2, hread_la2, hread_lt2,
        hperm_ih, hsort⟩
    · have hcur : VecMergeSort.sortOuterFwd la lt (F' + 1) w n =
        .ok (la, lt) := by
        simp only [VecMergeSort.sortOuterFwd, dite_eq_right hW]
      have hsort : SortedSeg la 0 n := by
        by_cases hn : 0 < n
        · have hb0 := hblock 0 (by rw [Nat.zero_mul]; exact hn)
          have e1 : (0 + 1) * w = w := by omega
          have e2 : Nat.min ((0 + 1) * w) n = n := by
            rw [e1]; exact Nat.min_eq_right (by omega)
          rw [Nat.zero_mul, e2] at hb0
          exact hb0
        · intro p q hlo_p hpq hqk a b ha hb
          have hfalse : False := by omega
          exact hfalse.elim
      exact ⟨la, lt, hcur, hla_len, hlt_len, hread_la, hread_lt,
        hperm, hsort⟩

/-- Outer correctness with the sort contract: from a sorted prefix
    with everything in the prefix `≤` the suffix (positional), the
    loop returns a sorted permutation of the original input. The
    step swaps in the suffix minimum (`minIndexFwd_lower` locates
    it, `swap_perm` keeps the permutation); the `m' = i` no-op
    case transports along the collapsed writes. -/
theorem selectionSortFwd_sorted_perm (l l₀ : List (BitVec 32))
    (fuel inner i : Nat)
    (hle : i ≤ l.length) (hF : l.length - i ≤ fuel)
    (hG : l.length - (i + 1) ≤ inner)
    (hread : ∀ p, p < l.length → ∃ x, l[p]? = some x)
    (hpref : ∀ (p q : Nat) (a b : BitVec 32), p < q → q < i →
      l[p]? = some a → l[q]? = some b → (b.slt a) = false)
    (hle_pre : ∀ (p q : Nat) (a b : BitVec 32), p < i → i ≤ q →
      q < l.length → l[p]? = some a → l[q]? = some b →
      (b.slt a) = false)
    (hperm : List.Perm l l₀) :
    ∃ i' l', VecSelectionSort.selectionSortFwd l fuel inner i = .ok (i', l') ∧
      l'.Pairwise (fun a b => b.slt a = false) ∧ List.Perm l' l₀ := by
  induction fuel generalizing l i with
  | zero =>
    have him : i = l.length := by omega
    subst him
    refine ⟨l.length, l, by simp [VecSelectionSort.selectionSortFwd],
      ?_, hperm⟩
    apply pairwise_of_positional
    intro p q a b hpq hpa hqb
    exact hpref p q a b hpq
      (by have := pos_lt_of_getElem?_some hqb; omega) hpa hqb
  | succ n ih =>
    by_cases hlt : i < l.length
    · obtain ⟨x, hx⟩ := hread i hlt
      have hle' : i + 1 ≤ l.length := by omega
      have hbase : ∀ (p : Nat) (x' : BitVec 32), i ≤ p → p < i + 1 →
          l[p]? = some x' → (x'.slt x) = false := by
        intro p x' hp1 hp2 hpx'
        have hpi : p = i := by omega
        subst hpi
        have hxx : x' = x := Option.some_inj.mp (hpx'.symm.trans hx)
        rw [hxx]
        exact VecSelectionSort.slt_irrefl _
      obtain ⟨m', j', ym', heqmin, hm', hi₀m', hym', hlower⟩ :=
        minIndexFwd_lower l inner (i + 1) i x i hx hlt hle'
          (Nat.le_refl _) (Nat.le_succ _) hG hread hbase
      by_cases hmi : m' = i
      · have hym'c := hym'
        rw [hmi] at hym'c
        have hxy : ym' = x :=
          Option.some_inj.mp (hym'c.symm.trans hx)
        have hm'x : l[m']? = some x := by
          rw [← hxy]
          exact hym'
        have hl' : ((l.set i x).set i x) = l := by
          rw [set_set_same, set_take_cons_drop l i x hlt,
            take_cons_drop l i x hx]
        have hlen' : ((l.set i x).set i x).length = l.length := by
          rw [List.length_set, List.length_set]
        have hF' : ((l.set i x).set i x).length - (i + 1) ≤ n := by omega
        have hG' : ((l.set i x).set i x).length - (i + 1 + 1) ≤ inner := by
          omega
        have hle'' : i + 1 ≤ ((l.set i x).set i x).length := by omega
        have hread' : ∀ p, p < ((l.set i x).set i x).length → ∃ z,
            ((l.set i x).set i x)[p]? = some z := by
          intro p hp
          have hplen : p < l.length := by omega
          by_cases hpi : p = i
          · subst hpi
            have hxx : ((l.set p x).set p x)[p]? = some x := by
              rw [set_set_same]
              exact List.getElem?_set_self hlt
            exact ⟨x, hxx⟩
          · obtain ⟨z, hz⟩ := hread p hplen
            have hzz : ((l.set i x).set i x)[p]? = some z := by
              rw [set_set_same,
                List.getElem?_set_ne (show i ≠ p by omega)]
              exact hz
            exact ⟨z, hzz⟩
        have hpref' : ∀ (p q : Nat) (a b : BitVec 32), p < q → q < i + 1 →
            ((l.set i x).set i x)[p]? = some a →
            ((l.set i x).set i x)[q]? = some b →
            (b.slt a) = false := by
          intro p q a b hpq hqi hpa hqb
          rw [hl'] at hpa hqb
          by_cases hqiq : q = i
          · rw [hqiq] at hqb hqi
            exact hle_pre p i a b (by omega) (Nat.le_refl _) hlt hpa hqb
          · exact hpref p q a b hpq (by omega) hpa hqb
        have hle_pre' : ∀ (p q : Nat) (a b : BitVec 32), p < i + 1 →
            i + 1 ≤ q → q < ((l.set i x).set i x).length →
            ((l.set i x).set i x)[p]? = some a →
            ((l.set i x).set i x)[q]? = some b →
            (b.slt a) = false := by
          intro p q a b hpi hiq hqlen hpa hqb
          rw [hl'] at hpa hqb hqlen
          by_cases hpi' : p = i
          · subst hpi'
            have hax : a = x := Option.some_inj.mp (hpa.symm.trans hx)
            rw [hax, ← hxy]
            exact hlower q b (by omega) (by omega) hqb
          · exact hle_pre p q a b (by omega) (by omega) (by omega)
              hpa hqb
        have hperm' : List.Perm ((l.set i x).set i x) l₀ := by
          rw [hl']
          exact hperm
        obtain ⟨i'', l'', heq, hsorted, hperm''⟩ :=
          ih ((l.set i x).set i x) (i + 1) hle'' hF' hG' hread'
            hpref' hle_pre' hperm'
        refine ⟨i'', l'', ?_, hsorted, hperm''⟩
        simp only [VecSelectionSort.selectionSortFwd, dite_eq_left hlt,
          heqmin, hx, hmi]
        exact heq
      · have hltm : i < m' := by omega
        have hlen : ((l.set i ym').set m' x).length = l.length := by
          rw [List.length_set, List.length_set]
        have hle'' : i + 1 ≤ ((l.set i ym').set m' x).length := by omega
        have hF'' : ((l.set i ym').set m' x).length - (i + 1) ≤ n := by
          omega
        have hG' : ((l.set i ym').set m' x).length - (i + 1 + 1) ≤ inner := by
          omega
        have hread' : ∀ p, p < ((l.set i ym').set m' x).length → ∃ z,
            ((l.set i ym').set m' x)[p]? = some z := by
          intro p hp
          have hplen : p < l.length := by omega
          by_cases hpm : p = m'
          · subst hpm
            have hxx : ((l.set i ym').set p x)[p]? = some x :=
              List.getElem?_set_self
                (by rw [List.length_set]; exact hm')
            exact ⟨x, hxx⟩
          · by_cases hpi : p = i
            · subst hpi
              have hyy : ((l.set p ym').set m' x)[p]? = some ym' := by
                rw [List.getElem?_set_ne (show m' ≠ p by omega)]
                exact List.getElem?_set_self hlt
              exact ⟨ym', hyy⟩
            · obtain ⟨z, hz⟩ := hread p hplen
              have hzz : ((l.set i ym').set m' x)[p]? = some z := by
                rw [List.getElem?_set_ne (show m' ≠ p by omega),
                  List.getElem?_set_ne (show i ≠ p by omega)]
                exact hz
              exact ⟨z, hzz⟩
        have hli : ((l.set i ym').set m' x)[i]? = some ym' := by
          rw [List.getElem?_set_ne (show m' ≠ i by omega)]
          exact List.getElem?_set_self hlt
        have hlp : ∀ (p : Nat), p ≠ m' → p ≠ i →
            ((l.set i ym').set m' x)[p]? = l[p]? := by
          intro p h1 h2
          rw [List.getElem?_set_ne (Ne.symm h1),
            List.getElem?_set_ne (Ne.symm h2)]
        have hlm : ((l.set i ym').set m' x)[m']? = some x :=
          List.getElem?_set_self (by rw [List.length_set]; exact hm')
        have hpref' : ∀ (p q : Nat) (a b : BitVec 32), p < q → q < i + 1 →
            ((l.set i ym').set m' x)[p]? = some a →
            ((l.set i ym').set m' x)[q]? = some b →
            (b.slt a) = false := by
          intro p q a b hpq hqi hpa hqb
          by_cases hqiq : q = i
          · subst hqiq
            rw [hli] at hqb
            have hby : b = ym' := (Option.some_inj.mp hqb).symm
            rw [hby]
            have hpa' : l[p]? = some a := by
              have hlp' := hlp p (by omega) (by omega)
              rw [hlp'] at hpa
              exact hpa
            exact hle_pre p m' a ym' (by omega) hi₀m' hm' hpa' hym'
          · have hpa' : l[p]? = some a := by
              have hlp' := hlp p (by omega) (by omega)
              rw [hlp'] at hpa
              exact hpa
            have hqb' : l[q]? = some b := by
              have hlp' := hlp q (by omega) (by omega)
              rw [hlp'] at hqb
              exact hqb
            exact hpref p q a b hpq (by omega) hpa' hqb'
        have hle_pre' : ∀ (p q : Nat) (a b : BitVec 32), p < i + 1 →
            i + 1 ≤ q → q < ((l.set i ym').set m' x).length →
            ((l.set i ym').set m' x)[p]? = some a →
            ((l.set i ym').set m' x)[q]? = some b →
            (b.slt a) = false := by
          intro p q a b hpi hiq hqlen hpa hqb
          have hqlen' : q < l.length := by omega
          by_cases hpi' : p = i
          · rw [hpi'] at hpa
            rw [hli] at hpa
            have hax : a = ym' := (Option.some_inj.mp hpa).symm
            rw [hax]
            by_cases hqm : q = m'
            · subst hqm
              rw [hlm] at hqb
              have hbx : b = x := (Option.some_inj.mp hqb).symm
              rw [hbx]
              exact hlower i x (Nat.le_refl _) hlt hx
            · have hqb' : l[q]? = some b := by
                have hlp' := hlp q hqm (by omega)
                rw [hlp'] at hqb
                exact hqb
              exact hlower q b (by omega) hqlen' hqb'
          · have hpa' : l[p]? = some a := by
              have hlp' := hlp p (by omega) (by omega)
              rw [hlp'] at hpa
              exact hpa
            by_cases hqm : q = m'
            · subst hqm
              rw [hlm] at hqb
              have hbx : b = x := (Option.some_inj.mp hqb).symm
              rw [hbx]
              exact hle_pre p i a x (by omega) (Nat.le_refl _) hlt
                hpa' hx
            · have hqb' : l[q]? = some b := by
                have hlp' := hlp q hqm (by omega)
                rw [hlp'] at hqb
                exact hqb
              exact hle_pre p q a b (by omega) (by omega) hqlen'
                hpa' hqb'
        have hperm' : List.Perm ((l.set i ym').set m' x) l₀ :=
          (swap_perm l i m' x ym' hlt hm' hi₀m' hx hym').trans hperm
        obtain ⟨i'', l'', heq, hsorted, hperm''⟩ :=
          ih ((l.set i ym').set m' x) (i + 1) hle'' hF'' hG' hread'
            hpref' hle_pre' hperm'
        refine ⟨i'', l'', ?_, hsorted, hperm''⟩
        simp only [VecSelectionSort.selectionSortFwd, dite_eq_left hlt,
          heqmin, hx, hym']
        exact heq
    · have him : i = l.length := by omega
      subst him
      refine ⟨l.length, l, by simp [VecSelectionSort.selectionSortFwd],
        ?_, hperm⟩
      apply pairwise_of_positional
      intro p q a b hpq hpa hqb
      exact hpref p q a b hpq
        (by have := pos_lt_of_getElem?_some hqb; omega) hpa hqb

/-- Window multiset from a full permutation that agrees outside the
    window (count-based; feeds the quicksort bounds). -/
theorem VecQuicksort.window_perm_of_perm_outside
    (l l' : List (BitVec 32)) (lo hi : Nat)
    (hlo : lo ≤ hi)
    (hlen : l'.length = l.length)
    (hperm : List.Perm l' l)
    (hout : ∀ p, p < lo ∨ hi ≤ p → l'[p]? = l[p]?) :
    List.Perm ((l'.drop lo).take (hi - lo))
      ((l.drop lo).take (hi - lo)) := by
  rw [List.perm_iff_count]
  intro a
  have e5 : l'.take lo = l.take lo := by
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_take, List.getElem?_take]
    by_cases hi2 : i < lo
    · rw [ite_eq_left hi2, ite_eq_left hi2]; exact hout i (Or.inl hi2)
    · rw [ite_eq_right hi2, ite_eq_right hi2]
  have e6 : l'.drop hi = l.drop hi := by
    apply List.ext_getElem?
    intro i
    rw [List.getElem?_drop, List.getElem?_drop]
    exact hout (hi + i) (Or.inr (by omega))
  have e1 : ∀ m : List (BitVec 32),
      List.count a m =
        List.count a (m.take lo) + List.count a (m.drop lo) := by
    intro m
    rw [← List.count_append, List.take_append_drop]
  have e2 : ∀ m : List (BitVec 32),
      List.count a (m.drop lo) =
        List.count a ((m.drop lo).take (hi - lo)) +
        List.count a ((m.drop lo).drop (hi - lo)) := by
    intro m
    rw [← List.count_append, List.take_append_drop]
  have e3 : ∀ m : List (BitVec 32),
      (m.drop lo).drop (hi - lo) = m.drop hi := by
    intro m
    rw [List.drop_drop]
    congr 1
    omega
  have e4 : List.count a l' = List.count a l :=
    (List.perm_iff_count.mp hperm) a
  have c5 : List.count a (l'.take lo) = List.count a (l.take lo) := by
    rw [e5]
  have c6 : List.count a (l'.drop hi) = List.count a (l.drop hi) := by
    rw [e6]
  have g1 := e1 l'
  have g2 := e1 l
  have g3 := e2 l'
  have g4 := e2 l
  rw [e3] at g3 g4
  omega

/-- Window membership as a bounded position read. -/
theorem VecQuicksort.mem_window_iff (l : List (BitVec 32)) (lo hi : Nat)
    (hlo : lo ≤ hi) (x : BitVec 32) :
    x ∈ ((l.drop lo).take (hi - lo)) ↔
      ∃ j, lo ≤ j ∧ j < hi ∧ l[j]? = some x := by
  constructor
  · intro hx
    obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem hx
    have hlen : ((l.drop lo).take (hi - lo)).length ≤ hi - lo := by
      rw [List.length_take, List.length_drop]
      exact Nat.min_le_left _ _
    have h2 : i < hi - lo := by omega
    refine ⟨lo + i, by omega, by omega, ?_⟩
    · have e1 : ((((l.drop lo).take (hi - lo))))[i]? =
          ((l.drop lo))[i]? := by
        rw [List.getElem?_take, ite_eq_left h2]
      have e2 : ((l.drop lo))[i]? = l[lo + i]? := List.getElem?_drop
      have e3 : ((((l.drop lo).take (hi - lo))))[i]? =
          some ((((l.drop lo).take (hi - lo))))[i] :=
        List.getElem?_eq_getElem hi'
      rw [← e2, ← e1]
      exact e3
  · rintro ⟨j, hlo_j, hhi, hx⟩
    apply List.mem_of_getElem?
    have e1 : ((((l.drop lo).take (hi - lo))))[j - lo]? =
        ((l.drop lo))[j - lo]? := by
      rw [List.getElem?_take, ite_eq_left (by omega : j - lo < hi - lo)]
    have e2 : ((l.drop lo))[j - lo]? = l[lo + (j - lo)]? :=
      List.getElem?_drop
    have e3 : lo + (j - lo) = j := by omega
    rw [e1, e2, e3]
    exact hx

/-- Sortedness transports across pointwise-equal windows. -/
theorem VecQuicksort.sortedSeg_congr (m m' : List (BitVec 32))
    (lo hi : Nat)
    (h : SortedSeg m lo hi)
    (heq : ∀ p, lo ≤ p → p < hi → m'[p]? = m[p]?) :
    SortedSeg m' lo hi := by
  intro p q hlo hpq hqh a b ha hb
  rw [heq p hlo (by omega : p < hi)] at ha
  rw [heq q (by omega : lo ≤ q) hqh] at hb
  exact h p q hlo hpq hqh a b ha hb

/-- Quicksort combine: sorted left window below the pivot plus sorted
    right window above it gives a sorted window. -/
theorem VecQuicksort.sort_combine (m : List (BitVec 32))
    (lo s hi : Nat) (pivot : BitVec 32)
    (hleft : SortedSeg m lo s) (hright : SortedSeg m (s + 1) hi)
    (hpiv : m[s]? = some pivot)
    (hlt : ∀ j, lo ≤ j → j < s → ∀ x, m[j]? = some x →
      (x.slt pivot) = true)
    (hge : ∀ j, s + 1 ≤ j → j < hi → ∀ x, m[j]? = some x →
      (x.slt pivot) = false) :
    SortedSeg m lo hi := by
  intro p q hlo hpq hqh a b ha hb
  by_cases hqs : q = s
  · have hps : p < s := by omega
    have hplt := hlt p hlo hps a ha
    have hbv : b = pivot := by
      have hb' : m[s]? = some b := hqs ▸ hb
      exact Option.some_inj.mp (hb'.symm.trans hpiv)
    rw [hbv]
    have hltI : a.toInt < pivot.toInt := by
      rw [BitVec.slt_eq_decide] at hplt
      simpa using hplt
    rw [BitVec.slt_eq_decide]
    simp only [decide_eq_false_iff_not]
    omega
  · by_cases hps : p = s
    · have hbv : a = pivot := by
        have ha' : m[s]? = some a := hps ▸ ha
        exact Option.some_inj.mp (ha'.symm.trans hpiv)
      rw [hbv]
      have hqs : s + 1 ≤ q := by omega
      exact hge q hqs hqh b hb
    · by_cases hq : s < q
      · by_cases hps2 : s < p
        · have hps3 : s + 1 ≤ p := by omega
          exact hright p q hps3 hpq hqh a b ha hb
        · have hplt := hlt p hlo (by omega) a ha
          have hqge := hge q (by omega) hqh b hb
          exact VecSelectionSort.slt_lower_trans hplt hqge
      · have hpq' : p < q := hpq
        have hqs : q < s := by omega
        exact hleft p q hlo hpq' (by omega) a b ha hb
/-- Partition-scan joint: the Lomuto pass preserves length and the
    full permutation, touches nothing outside `[lo, hi - 1]`, and
    splits the scanned prefix below / above the pivot. The bounds
    `hlt`/`hge` are the loop invariant threaded through the fuel
    induction. -/
theorem VecQuicksort.qsPartFwd_joint (pivot : BitVec 32)
    (l : List (BitVec 32)) (F hi i s : Nat) (lo : Nat)
    (hlo_s : lo ≤ s) (hs_i : s ≤ i) (hi_le : i ≤ hi - 1)
    (hhi_le : hi ≤ l.length)
    (hlt : ∀ j, lo ≤ j → j < s → ∀ x, l[j]? = some x →
      (x.slt pivot) = true)
    (hge : ∀ j, s ≤ j → j < i → ∀ x, l[j]? = some x →
      (x.slt pivot) = false)
    (s' : Nat) (l' : List (BitVec 32))
    (h : VecQuicksort.qsPartFwd pivot l F hi i s = .ok (s', l')) :
    l'.length = l.length ∧
    (∀ p, p < lo ∨ hi - 1 ≤ p → l'[p]? = l[p]?) ∧
    List.Perm l' l ∧
    lo ≤ s' ∧ s' ≤ hi - 1 ∧
    (∀ j, lo ≤ j → j < s' → ∀ x, l'[j]? = some x →
      (x.slt pivot) = true) ∧
    (∀ j, s' ≤ j → j < hi - 1 → ∀ x, l'[j]? = some x →
      (x.slt pivot) = false) := by
  induction F generalizing l i s s' l' with
  | zero =>
    simp only [VecQuicksort.qsPartFwd] at h
    by_cases hg : i + 1 < hi
    · rw [ite_eq_left hg] at h
      cases h
    · rw [ite_eq_right hg] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hge0 : ∀ j, s ≤ j → j < hi - 1 → ∀ y,
          l[j]? = some y → (y.slt pivot) = false := by
        intro j hsj hjm y hy
        exact hge j hsj (by omega) y hy
      exact ⟨rfl, fun p _ => rfl, List.Perm.rfl, hlo_s, by omega,
        hlt, hge0⟩
  | succ F ih =>
    simp only [VecQuicksort.qsPartFwd] at h
    by_cases hg : i + 1 < hi
    · rw [ite_eq_left hg] at h
      have hilt : i < l.length := by omega
      have hslt : s < l.length := by omega
      cases hxi : l[i]? with
      | none =>
        have hsome : l[i]? = some l[i] :=
          List.getElem?_eq_getElem hilt
        rw [hsome] at hxi
        cases hxi
      | some x =>
        cases hsj : l[s]? with
        | none =>
          have hsome : l[s]? = some l[s] :=
            List.getElem?_eq_getElem hslt
          rw [hsome] at hsj
          cases hsj
        | some w =>
          simp only [hxi, hsj] at h
          by_cases hsltB : x.slt pivot
          · have htake : (x.slt pivot) = true := hsltB
            rw [ite_eq_left hsltB] at h
            match hr : VecQuicksort.qsPartFwd pivot
                ((l.set i w).set s x) F hi (i + 1) (s + 1) with
            | .error e => simp only [hr] at h; cases h
            | .ok (s'', l'') =>
              simp only [hr, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hlen1 : (((l.set i w).set s x)).length =
                  l.length := by
                simp [List.length_set]
              have hhi_le' : hi ≤ (((l.set i w).set s x)).length := by
                rw [hlen1]; exact hhi_le
              have hlt' : ∀ j, lo ≤ j → j < s + 1 → ∀ y,
                  ((((l.set i w).set s x)))[j]? = some y →
                  (y.slt pivot) = true := by
                intro j hlo_j hjs y hy
                by_cases hjs2 : j = s
                · have ejs : ((((l.set i w).set s x)))[j]? =
                      ((((l.set i w).set s x)))[s]? := by
                    rw [hjs2]
                  rw [ejs] at hy
                  have e1 : ((((l.set i w).set s x)))[s]? =
                      some x :=
                    List.getElem?_set_self (by
                      rw [List.length_set]; exact hslt)
                  rw [e1] at hy
                  have hxy : y = x := Option.some_inj.mp hy.symm
                  rw [hxy]
                  exact htake
                · have hjs' : j < s := by omega
                  have e1 : ((((l.set i w).set s x)))[j]? =
                      ((l.set i w))[j]? :=
                    List.getElem?_set_ne (show s ≠ j by omega)
                  have e2 : ((l.set i w))[j]? = l[j]? :=
                    List.getElem?_set_ne (show i ≠ j by omega)
                  rw [e1, e2] at hy
                  exact hlt j hlo_j hjs' y hy
              have hge' : ∀ j, s + 1 ≤ j → j < i + 1 → ∀ y,
                  ((((l.set i w).set s x)))[j]? = some y →
                  (y.slt pivot) = false := by
                intro j hsjj hji y hy
                by_cases hji2 : j = i
                · have eji : ((((l.set i w).set s x)))[j]? =
                      ((((l.set i w).set s x)))[i]? := by
                    rw [hji2]
                  rw [eji] at hy
                  by_cases hsi : s = i
                  · omega
                  · have e1 : ((((l.set i w).set s x)))[i]? =
                        ((l.set i w))[i]? :=
                      List.getElem?_set_ne
                        (show s ≠ i from hsi)
                    have e2 : ((l.set i w))[i]? = some w :=
                      List.getElem?_set_self hilt
                    rw [e1, e2] at hy
                    have hwy : y = w := Option.some_inj.mp hy.symm
                    rw [hwy]
                    exact hge s (by omega) (by omega) w hsj
                · have hji' : j < i := by omega
                  have e1n : ((((l.set i w).set s x)))[j]? =
                      ((l.set i w))[j]? :=
                    List.getElem?_set_ne (show s ≠ j by omega)
                  have e2n : ((l.set i w))[j]? = l[j]? :=
                    List.getElem?_set_ne (show i ≠ j by omega)
                  rw [e1n, e2n] at hy
                  exact hge j (by omega) hji' y hy
              have hperm1 : List.Perm (((l.set i w).set s x)) l :=
                partitionTake_perm l i s x w hilt hslt
                  (by omega) hxi hsj
              have hout1 : ∀ p, p < lo ∨ hi - 1 ≤ p →
                  ((((l.set i w).set s x)))[p]? = l[p]? := by
                intro p hp
                rw [List.getElem?_set_ne (show s ≠ p by omega),
                  List.getElem?_set_ne (show i ≠ p by omega)]
              have hcomb := ih (((l.set i w).set s x)) (i + 1)
                (s + 1) (by omega) (by omega) (by omega)
                hhi_le' hlt' hge' s'' l'' hr
              obtain ⟨hlenI, houtI, hpermI, hloI, hhiI, hltI,
                hgeI⟩ := hcomb
              exact ⟨hlenI.trans hlen1,
                fun p hp => (houtI p hp).trans (hout1 p hp),
                hpermI.trans hperm1, hloI, hhiI, hltI, hgeI⟩
          · have hskip : (x.slt pivot) = false := by simp [hsltB]
            rw [ite_eq_right hsltB] at h
            match hr : VecQuicksort.qsPartFwd pivot l F hi (i + 1) s with
            | .error e => simp only [hr] at h; cases h
            | .ok (s'', l'') =>
              simp only [hr, Except.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hge' : ∀ j, s ≤ j → j < i + 1 → ∀ y,
                  l[j]? = some y → (y.slt pivot) = false := by
                intro j hsj hji y hy
                by_cases hji2 : j = i
                · subst hji2
                  have hxy : x = y :=
                    Option.some_inj.mp (hxi.symm.trans hy)
                  exact hxy ▸ hskip
                · exact hge j hsj (by omega) y hy
              exact ih l (i + 1) s hlo_s (by omega)
                (by omega) hhi_le hlt hge' s'' l'' hr
    · rw [ite_eq_right hg] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hge0 : ∀ j, s ≤ j → j < hi - 1 → ∀ y,
          l[j]? = some y → (y.slt pivot) = false := by
        intro j hsjj hjm y hy
        exact hge j hsjj (by omega) y hy
      exact ⟨rfl, fun p _ => rfl, List.Perm.rfl, hlo_s, by omega,
        hlt, hge0⟩
/-- Quicksort whole-sort joint: a successful forward run preserves
    length, touches nothing outside `[lo, hi)`, is a permutation, and
    leaves the window sorted. By fuel induction mirroring the evaluator
    bridge: the scan reuses `qsPartFwd_joint`, the place is a single
    transposition (`swap_perm`), and the two recursive windows combine
    via `sort_combine` with cross-bounds transported through window
    permutations. -/
theorem VecQuicksort.vecQuicksortFwd_joint (l : List (BitVec 32)) (F : Nat)
    (lo hi : Nat) (hlo : lo ≤ hi) (hlen : hi ≤ l.length)
    (l' : List (BitVec 32))
    (h : vecQuicksortFwd l F lo hi = .ok l') :
    l'.length = l.length ∧
    (∀ p, p < lo ∨ hi ≤ p → l'[p]? = l[p]?) ∧
    List.Perm l' l ∧
    SortedSeg l' lo hi := by
  induction F generalizing l lo hi l' with
  | zero =>
    simp only [vecQuicksortFwd] at h
    by_cases h1 : lo < hi
    · rw [ite_eq_left h1] at h
      by_cases h2 : 1 < hi - lo
      · rw [ite_eq_left h2] at h
        cases h
      · rw [ite_eq_right h2] at h
        simp only [Except.ok.injEq] at h
        obtain rfl := h
        refine ⟨rfl, fun p _ => rfl, List.Perm.rfl, ?_⟩
        intro p q hlo_p hpq hq a b ha hb
        omega
    · rw [ite_eq_right h1] at h
      simp only [Except.ok.injEq] at h
      obtain rfl := h
      refine ⟨rfl, fun p _ => rfl, List.Perm.rfl, ?_⟩
      intro p q hlo_p hpq hq a b ha hb
      omega
  | succ F ih =>
    simp only [vecQuicksortFwd] at h
    by_cases h1 : lo < hi
    · rw [ite_eq_left h1] at h
      by_cases h2 : 1 < hi - lo
      · rw [ite_eq_left h2] at h
        match hpivM : l[hi - 1]? with
        | none => simp only [hpivM] at h; cases h
        | some pivot =>
          simp only [hpivM] at h
          match hpart : qsPartFwd pivot l (F + 1) hi lo lo with
          | .error e => simp only [hpart] at h; cases h
          | .ok (s, l1) =>
            simp only [hpart] at h
            match hwM : l1[s]? with
            | none => simp only [hwM] at h; cases h
            | some w =>
              simp only [hwM] at h
              match hpM : l1[hi - 1]? with
              | none => simp only [hpM] at h; cases h
              | some _ =>
                simp only [hpM] at h
                match hleft : vecQuicksortFwd
                    ((l1.set (hi - 1) w).set s pivot) F lo s with
                | .error e => simp only [hleft] at h; cases h
                | .ok l2 =>
                  simp only [hleft] at h
                  match hright : vecQuicksortFwd l2 F (s + 1) hi with
                  | .error e => simp only [hright] at h; cases h
                  | .ok l3 =>
                    simp only [hright, Except.ok.injEq] at h
                    obtain rfl := h
                    have hscan := qsPartFwd_joint pivot l (F + 1)
                      hi lo lo lo (by omega) (by omega) (by omega) hlen
                      (by intro j hj1 hj2 x hx; omega)
                      (by intro j hj1 hj2 x hx; omega)
                      s l1 hpart
                    obtain ⟨hlen1, hout1, hperm1, hlo_s, hhi_s, hlt1,
                      hge1⟩ := hscan
                    have hpiv1 : l1[hi - 1]? = some pivot :=
                      (hout1 (hi - 1) (Or.inr (by omega))).trans hpivM
                    have hlen1' : (((l1.set (hi - 1) w).set s pivot)).length =
                        l.length := by
                      simp [List.length_set, hlen1]
                    have hplace_perm : List.Perm
                        (((l1.set (hi - 1) w).set s pivot)) l1 := by
                      by_cases heq : s = hi - 1
                      · subst heq
                        have h1lt : hi - 1 < l1.length := by omega
                        rw [show pivot = w from Option.some_inj.mp
                          (hpiv1.symm.trans hwM)]
                        exact swap_perm l1 (hi - 1) (hi - 1) w w
                          h1lt h1lt (by omega) hwM hwM
                      · have hne : hi - 1 ≠ s :=
                          fun hh => heq hh.symm
                        have hcomm : (((l1.set (hi - 1) w).set s pivot)) =
                            (((l1.set s pivot).set (hi - 1) w)) :=
                          List.set_comm _ _ hne
                        rw [hcomm]
                        exact swap_perm l1 s (hi - 1) w pivot
                          (by omega) (by omega) hhi_s hwM hpiv1
                    have hplace_self : (((l1.set (hi - 1) w).set s pivot))[s]? =
                        some pivot :=
                      List.getElem?_set_self (by
                        rw [List.length_set]; omega)
                    have hplace_out : ∀ p, p < lo ∨ hi ≤ p →
                        (((l1.set (hi - 1) w).set s pivot))[p]? =
                          l1[p]? := by
                      intro p hp
                      rw [List.getElem?_set_ne (show s ≠ p by omega),
                        List.getElem?_set_ne (show hi - 1 ≠ p by omega)]
                    have ihL := ih ((l1.set (hi - 1) w).set s pivot)
                      lo s hlo_s (by omega) l2 hleft
                    obtain ⟨hlen2, hout2, hperm2, hsort2⟩ := ihL
                    have ihR := ih l2 (s + 1) hi (by omega) (by omega)
                      l3 hright
                    obtain ⟨hlenR, houtR, hpermR, hsortR⟩ := ihR
                    have hsortL : SortedSeg l3 lo s :=
                      sortedSeg_congr l2 l3 lo s hsort2
                        (fun p hlo_p hps =>
                          houtR p (Or.inl (by omega : p < s + 1)))
                    have hpiv3 : l3[s]? = some pivot :=
                      ((houtR s (Or.inl (Nat.lt_succ_self s))).trans
                        (hout2 s (Or.inr (by omega : s ≤ s)))).trans
                        hplace_self
                    have hlt3 : ∀ j, lo ≤ j → j < s → ∀ x,
                        l3[j]? = some x → (x.slt pivot) = true := by
                      intro j hlo_j hjs x hx
                      have e2 : l2[j]? = some x :=
                        (houtR j (Or.inl (by omega : j < s + 1))).symm.trans
                          hx
                      have hmem2 : x ∈ ((l2.drop lo).take (s - lo)) :=
                        (mem_window_iff l2 lo s hlo_s x).mpr
                          ⟨j, hlo_j, hjs, e2⟩
                      have hwpL : List.Perm ((l2.drop lo).take (s - lo))
                          ((((l1.set (hi - 1) w).set s pivot).drop lo).take
                            (s - lo)) :=
                        window_perm_of_perm_outside _ _ lo s hlo_s
                          hlen2 hperm2 hout2
                      have hmem1 : x ∈ ((((l1.set (hi - 1) w).set s pivot).drop
                          lo).take (s - lo)) := hwpL.mem_iff.mp hmem2
                      obtain ⟨j', hlo_j', hjs', hx'⟩ :=
                        (mem_window_iff _ lo s hlo_s x).mp hmem1
                      have ee : (((l1.set (hi - 1) w).set s pivot))[j']? =
                          l1[j']? := by
                        rw [List.getElem?_set_ne (show s ≠ j' by omega),
                          List.getElem?_set_ne (show hi - 1 ≠ j' by omega)]
                      exact hlt1 j' hlo_j' hjs' x (ee.symm.trans hx')
                    have hge3 : ∀ j, s + 1 ≤ j → j < hi → ∀ x,
                        l3[j]? = some x → (x.slt pivot) = false := by
                      intro j hlo_j hjs x hx
                      have hs1hi : s + 1 ≤ hi := by omega
                      have hmem3 : x ∈ ((l3.drop (s + 1)).take
                          (hi - (s + 1))) :=
                        (mem_window_iff l3 (s + 1) hi hs1hi x).mpr
                          ⟨j, hlo_j, hjs, hx⟩
                      have hwpR : List.Perm
                          ((l3.drop (s + 1)).take (hi - (s + 1)))
                          ((l2.drop (s + 1)).take (hi - (s + 1))) :=
                        window_perm_of_perm_outside _ _ (s + 1) hi hs1hi
                          hlenR hpermR houtR
                      have hmem2 : x ∈ ((l2.drop (s + 1)).take
                          (hi - (s + 1))) := hwpR.mem_iff.mp hmem3
                      obtain ⟨j', hlo_j', hjs', hx'⟩ :=
                        (mem_window_iff l2 (s + 1) hi hs1hi x).mp hmem2
                      have e1' : (((l1.set (hi - 1) w).set s pivot))[j']? =
                          some x :=
                        (hout2 j' (Or.inr (by omega : s ≤ j'))).symm.trans
                          hx'
                      by_cases hje : j' = hi - 1
                      · have ep : (((l1.set (hi - 1) w).set s pivot))[j']? =
                          some w := by
                          rw [hje,
                            List.getElem?_set_ne (show s ≠ hi - 1 by omega),
                            List.getElem?_set_self (by omega)]
                        have hxw : x = w :=
                          Option.some_inj.mp (e1'.symm.trans ep)
                        rw [hxw]
                        exact hge1 s (by omega) (by omega) w hwM
                      · have ee : (((l1.set (hi - 1) w).set s pivot))[j']? =
                          l1[j']? := by
                          rw [List.getElem?_set_ne (show s ≠ j' by omega),
                            List.getElem?_set_ne
                              (show hi - 1 ≠ j' by omega)]
                        exact hge1 j' (by omega) (by omega) x
                          (ee.symm.trans e1')
                    exact ⟨hlenR.trans (hlen2.trans hlen1'),
                      fun p hp => ((houtR p (by omega)).trans
                        (hout2 p (by omega))).trans
                        ((hplace_out p hp).trans (hout1 p (by omega))),
                      hpermR.trans
                        (hperm2.trans (hplace_perm.trans hperm1)),
                      sort_combine l3 lo s hi pivot hsortL hsortR hpiv3
                        hlt3 hge3⟩
      · rw [ite_eq_right h2] at h
        simp only [Except.ok.injEq] at h
        obtain rfl := h
        refine ⟨rfl, fun p _ => rfl, List.Perm.rfl, ?_⟩
        intro p q hlo_p hpq hq a b ha hb
        omega
    · rw [ite_eq_right h1] at h
      simp only [Except.ok.injEq] at h
      obtain rfl := h
      refine ⟨rfl, fun p _ => rfl, List.Perm.rfl, ?_⟩
      intro p q hlo_p hpq hq a b ha hb
      omega
/-- Quicksort closing spec (value level): a successful evaluator run
    returns a sorted permutation of the input window. The error twin
    rules out model failure (an evaluator success contradicts the
    reflected model error), the ok twin reifies the forward result,
    and `vecQuicksortFwd_joint` supplies length, confinement,
    permutation, and sortedness. -/
theorem VecQuicksort.vecQuicksort_spec (F : Nat)
    (l : List (BitVec 32)) (lo hi : Nat) (loB hiB : BitVec 64)
    (hloN : loB.toNat = lo) (hhiN : hiB.toNat = hi)
    (hl64 : l.length < 2 ^ 64)
    (hlo_le : lo ≤ hi) (hhi_le : hi ≤ l.length)
    (ret : Value)
    (h : evalProgFunc vecQuicksortProg F vecQuicksortFunc
      [.stdVecVal l, .u64 loB, .u64 hiB] = .ok ret) :
    ∃ l', ret = .stdVecVal l' ∧ l'.length = l.length ∧
      (∀ p, p < lo ∨ hi ≤ p → l'[p]? = l[p]?) ∧
      List.Perm l' l ∧ SortedSeg l' lo hi := by
  match hfwd : vecQuicksortFwd l F lo hi with
  | .error e =>
    have heval := evalProgFunc_vecQuicksort_err F l lo hi loB hiB e
      hloN hhiN hl64 hlo_le hhi_le hfwd
    rw [heval] at h
    cases h
  | .ok l' =>
    have heval := evalProgFunc_vecQuicksort_ok F l lo hi loB hiB
      hloN hhiN hl64 hlo_le hhi_le l' hfwd
    obtain ⟨ret', hev, hret'⟩ := heval
    rw [h] at hev
    cases hev
    have hjoint := vecQuicksortFwd_joint l F lo hi hlo_le hhi_le l' hfwd
    exact ⟨l', hret', hjoint.1, hjoint.2.1, hjoint.2.2.1, hjoint.2.2.2⟩

/-- Erase-compress bounds: the write cursor stays behind the
    read cursor, and the read cursor never retreats. -/
theorem removeFwd_bounds (x : BitVec 32) (l l' : List (BitVec 32))
    (fuel r w r' w' : Nat) (hwle : w ≤ r)
    (h : removeFwd x l fuel r w = .ok (r', w', l')) :
    w' ≤ r' ∧ r ≤ r' := by
  induction fuel generalizing l r w with
  | zero =>
    have hpair : (r, w, l) = (r', w', l') := by
      simpa [removeFwd] using h
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    exact ⟨hwle, Nat.le_refl _⟩
  | succ n ih =>
    by_cases hlt : r < l.length
    · obtain ⟨y, hy⟩ : ∃ y, l[r]? = some y := by
        exact ⟨l[r], List.getElem?_eq_getElem hlt⟩
      by_cases hkeep : (y != x) = true
      · have h' : removeFwd x (l.set w y) n (r + 1) (w + 1) =
            .ok (r', w', l') := by
          simpa [removeFwd, dite_eq_left hlt, hy, hkeep] using h
        obtain ⟨h1, h2⟩ := ih (l := l.set w y) (r := r + 1)
          (w := w + 1) (by omega) h'
        exact ⟨h1, by omega⟩
      · have hdrop : (y != x) = false := by
          cases hh : (y != x) with
          | true => exact absurd hh hkeep
          | false => rfl
        have h' : removeFwd x l n (r + 1) w = .ok (r', w', l') := by
          simpa [removeFwd, dite_eq_left hlt, hy, hdrop] using h
        obtain ⟨h1, h2⟩ := ih (l := l) (r := r + 1) (w := w)
          (by omega) h'
        exact ⟨h1, by omega⟩
    · have hpair : (r, w, l) = (r', w', l') := by
        simpa [removeFwd, dite_eq_right hlt] using h
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      exact ⟨hwle, Nat.le_refl _⟩

/-- Squeeze loop is total: the scan runs to `l.length` (fuel
    induction threading the predecessor read; the `w - 1` access
    is justified by the `1 ≤ w` seed fact plus `w ≤ r`). -/
theorem uniqueFwd_ok (l : List (BitVec 32))
    (fuel r w : Nat)
    (hle : r ≤ l.length) (hwle : w ≤ r) (hw1 : 1 ≤ w)
    (hF : l.length - r ≤ fuel)
    (hread : ∀ p, p < l.length → ∃ y, l[p]? = some y) :
    ∃ w' l', uniqueFwd l fuel r w = .ok (l.length, w', l') := by
  induction fuel generalizing l r w with
  | zero =>
    have him : r = l.length := by omega
    subst him
    exact ⟨w, l, by simp [uniqueFwd]⟩
  | succ n ih =>
    by_cases hlt : r < l.length
    · obtain ⟨y, hy⟩ := hread r hlt
      have hwltM : w - 1 < l.length := by omega
      obtain ⟨p, hp⟩ := hread (w - 1) hwltM
      have hwlt : w < l.length := by omega
      obtain ⟨wOld, hwget⟩ := hread w hwlt
      have hF' : l.length - (r + 1) ≤ n := by omega
      by_cases hkeep : (y != p) = true
      · have hlen : (l.set w y).length = l.length := by
          simp [List.length_set]
        have hread' : ∀ q, q < (l.set w y).length →
            ∃ z, (l.set w y)[q]? = some z := by
          intro q hq
          have hplen : q < l.length := by rw [hlen] at hq; exact hq
          by_cases hpw : q = w
          · rw [hpw]
            exact ⟨y, List.getElem?_set_self hwlt⟩
          · obtain ⟨z, hz⟩ := hread q hplen
            exact ⟨z, by
              rw [List.getElem?_set_ne (show w ≠ q by omega)]
              exact hz⟩
        obtain ⟨w', l', h'⟩ := ih (l := l.set w y) (r := r + 1)
          (w := w + 1) (by rw [hlen]; omega) (by omega) (by omega)
          (by rw [hlen]; omega) hread'
        exact ⟨w', l', by
          simpa [uniqueFwd, dite_eq_left hlt, hy, hp,
            hkeep] using h'⟩
      · have hdrop : (y != p) = false := by
          cases h : (y != p) with
          | true => exact absurd h hkeep
          | false => rfl
        obtain ⟨w', l', h'⟩ := ih (l := l) (r := r + 1) (w := w)
          (by omega) (by omega) hw1 (by omega) hread
        exact ⟨w', l', by
          simpa [uniqueFwd, dite_eq_left hlt, hy, hp,
            hdrop] using h'⟩
    · have him : r = l.length := by omega
      subst him
      exact ⟨w, l, by simp [uniqueFwd, dite_eq_right hlt]⟩

/-- Squeeze-loop bounds: the write cursor never passes the read
    cursor, which never passes the exit length. -/
theorem uniqueFwd_bounds (l l' : List (BitVec 32))
    (fuel r w r' w' : Nat) (hwle : w ≤ r) (hw1 : 1 ≤ w)
    (h : uniqueFwd l fuel r w = .ok (r', w', l')) :
    w' ≤ r' ∧ r ≤ r' := by
  induction fuel generalizing l r w with
  | zero =>
    have hpair : (r, w, l) = (r', w', l') := by
      simpa [uniqueFwd] using h
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    exact ⟨hwle, Nat.le_refl _⟩
  | succ n ih =>
    by_cases hlt : r < l.length
    · obtain ⟨y, hy⟩ : ∃ y, l[r]? = some y := by
        exact ⟨l[r], List.getElem?_eq_getElem hlt⟩
      have hwltM : w - 1 < l.length := by omega
      obtain ⟨p, hp⟩ : ∃ p, l[w - 1]? = some p :=
        ⟨l[w - 1], List.getElem?_eq_getElem hwltM⟩
      by_cases hkeep : (y != p) = true
      · have h' : uniqueFwd (l.set w y) n (r + 1) (w + 1) =
            .ok (r', w', l') := by
          simpa [uniqueFwd, dite_eq_left hlt, hy, hp, hkeep] using h
        obtain ⟨h1, h2⟩ := ih (l := l.set w y) (r := r + 1)
          (w := w + 1) (by omega) (by omega) h'
        exact ⟨h1, by omega⟩
      · have hdrop : (y != p) = false := by
          cases hh : (y != p) with
          | true => exact absurd hh hkeep
          | false => rfl
        have h' : uniqueFwd l n (r + 1) w = .ok (r', w', l') := by
          simpa [uniqueFwd, dite_eq_left hlt, hy, hp, hdrop] using h
        obtain ⟨h1, h2⟩ := ih (l := l) (r := r + 1) (w := w)
          (by omega) hw1 h'
        exact ⟨h1, by omega⟩
    · have hpair : (r, w, l) = (r', w', l') := by
        simpa [uniqueFwd, dite_eq_right hlt] using h
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      exact ⟨hwle, Nat.le_refl _⟩

/-- Squeeze invariant over the scan, stated against the entry
    list `l₀` (the running list `l` mutates under the scan:
    positions at/above the write cursor still hold the entry
    values). The compacted prefix is the squeezed scanned prefix
    of `l₀`; at exit (`r = l₀.length`) this is the whole squeezed
    input. -/
theorem uniqueFwd_prefix (l₀ : List (BitVec 32))
    (fuel r w w' : Nat) (l l' : List (BitVec 32))
    (hle : r ≤ l₀.length) (hwle : w ≤ r) (hw1 : 1 ≤ w)
    (hF : l₀.length - r ≤ fuel)
    (hlen : l.length = l₀.length)
    (hpre : l.take w = dedupAdj (l₀.take r))
    (hsuf : ∀ j, w ≤ j → l[j]? = l₀[j]?)
    (hfwd : uniqueFwd l fuel r w = .ok (l₀.length, w', l')) :
    l'.take w' = dedupAdj l₀ ∧
      w ≤ w' ∧
      l'.length = l₀.length := by
  induction fuel generalizing l r w with
  | zero =>
    have hpair : (r, w, l) = (l₀.length, w', l') := by
      simpa [uniqueFwd] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    have htakeFull : l₀.take l₀.length = l₀ := List.take_length
    rw [htakeFull] at hpre
    exact ⟨hpre, Nat.le_refl _, hlen⟩
  | succ n ih =>
    have hlenN : l.length = l₀.length := hlen
    by_cases hlt : r < l.length
    · have hlt₀ : r < l₀.length := by omega
      have hy₀ : l[r]? = some l₀[r] := by
        rw [hsuf r (by omega)]
        exact List.getElem?_eq_getElem hlt₀
      have hwltM : w - 1 < l.length := by omega
      have hDne : l₀.take r ≠ [] := by
        have hlenD : 0 < (l₀.take r).length := by
          rw [List.length_take]; omega
        intro h
        rw [h, List.length_nil] at hlenD
        omega
      have hDnn : dedupAdj (l₀.take r) ≠ [] :=
        dedupAdj_nonempty hDne
      obtain ⟨p, hpD⟩ : ∃ p, (dedupAdj (l₀.take r)).getLast? = some p := by
        have hne : (dedupAdj (l₀.take r)).getLast? ≠ none :=
          fun h => hDnn (List.getLast?_eq_none_iff.mp h)
        exact Option.ne_none_iff_exists'.mp hne
      have hlastL : (l.take w).getLast? = some p := by
        rw [hpre]; exact hpD
      have hlenW : (l.take w).length = w := by
        rw [List.length_take, hlen, Nat.min_eq_left (by omega)]
      have hprevTaken : (l.take w)[w - 1]? = some p := by
        have h := hlastL
        rw [List.getLast?_eq_getElem?, hlenW] at h
        exact h
      have hp : l[w - 1]? = some p := by
        have h := hprevTaken
        rw [List.getElem?_take_of_lt (by omega : w - 1 < w)] at h
        exact h
      have htakeR : l₀.take (r + 1) = l₀.take r ++ [l₀[r]] := by
        rw [List.take_add_one, List.getElem?_eq_getElem hlt₀,
          Option.toList_some]
      have hF' : l₀.length - (r + 1) ≤ n := by omega
      by_cases hkeep : (l₀[r] != p) = true
      · have hwlt : w < l.length := by omega
        have hlen' : (l.set w l₀[r]).length = l₀.length := by
          simp [List.length_set, hlen]
        have hts : (l.set w l₀[r]).take (w + 1) =
            l.take w ++ [l₀[r]] := by
          have htakeW : (l.set w l₀[r]).take w = l.take w := by
            apply List.ext_getElem?
            intro j
            rw [List.getElem?_take, List.getElem?_take]
            by_cases hj : j < w
            · rw [List.getElem?_set_ne (show w ≠ j by omega)]
            · simp [hj]
          rw [List.take_add_one,
            List.getElem?_set_self (by omega : w < l.length),
            htakeW]; rfl
        have hpre' : (l.set w l₀[r]).take (w + 1) =
            dedupAdj (l₀.take (r + 1)) := by
          simp only [hts, hpre, htakeR, dedupAdj_append_single,
            hpD, hkeep, if_true]
        have hsuf' : ∀ j, w + 1 ≤ j →
            (l.set w l₀[r])[j]? = l₀[j]? := by
          intro j hj
          rw [List.getElem?_set_ne (show w ≠ j by omega)]
          exact hsuf j (by omega)
        have hfwd' : uniqueFwd (l.set w l₀[r]) n (r + 1) (w + 1) =
            .ok (l₀.length, w', l') := by
          have h := hfwd
          simp only [uniqueFwd, dite_eq_left hlt, hy₀, hp,
            hkeep] at h
          exact h
        obtain ⟨hA, hB, hC⟩ := ih (l := l.set w l₀[r]) (r := r + 1)
          (w := w + 1) (by omega) (by omega) (by omega) hF' hlen'
          hpre' hsuf' hfwd'
        exact ⟨hA, by omega, hC⟩
      · have hdrop : (l₀[r] != p) = false := by
          cases h : (l₀[r] != p) with
          | true => exact absurd h hkeep
          | false => rfl
        have hpre' : l.take w = dedupAdj (l₀.take (r + 1)) := by
          simp only [htakeR, dedupAdj_append_single, hpD, hkeep,
            hpre]
          rw [if_neg (by decide : ¬ ((false : Bool) = true))]
        have hfwd' : uniqueFwd l n (r + 1) w =
            .ok (l₀.length, w', l') := by
          have h := hfwd
          simp only [uniqueFwd, dite_eq_left hlt, hy₀, hp,
            hdrop] at h
          exact h
        obtain ⟨hA, hB, hC⟩ := ih (l := l) (r := r + 1) (w := w)
          (by omega) (by omega) hw1 hF' hlen hpre'
          (fun j hj => hsuf j (by omega)) hfwd'
        exact ⟨hA, hB, hC⟩
    · have hpair : (r, w, l) = (l₀.length, w', l') := by
        simpa [uniqueFwd, dite_eq_right hlt] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      have htakeFull : l₀.take l₀.length = l₀ := List.take_length
      rw [htakeFull] at hpre
      exact ⟨hpre, Nat.le_refl _, hlen⟩

/-- Whole-function squeeze contract: the returned length is the
    squeezed length, the compacted prefix is the oracle squeeze,
    and the vector length is preserved (the caller owes the
    `erase`: the tail past `w'` is don't-care). -/
theorem vecUniqueFwd_correct (l₀ : List (BitVec 32))
    (hl64 : l₀.length < 2 ^ 64)
    (hread₀ : ∀ p, p < l₀.length → ∃ y, l₀[p]? = some y) :
    ∃ (w' : Nat) (l' : List (BitVec 32)),
      vecUniqueFwd l₀ = .ok (.u64 (BitVec.ofNat 64 w')) ∧
      l'.take w' = dedupAdj l₀ ∧
      w' = (dedupAdj l₀).length ∧
      l'.length = l₀.length := by
  cases l₀ with
  | nil => exact ⟨0, [], by simp [vecUniqueFwd], by simp [dedupAdj], rfl, rfl⟩
  | cons x xs =>
    have hlen1 : 1 ≤ (x :: xs).length := by
      rw [List.length_cons]; omega
    obtain ⟨w', l', hfwd⟩ := uniqueFwd_ok (x :: xs)
      ((x :: xs).length) 1 1 hlen1 (Nat.le_refl _) (Nat.le_refl _)
      (Nat.sub_le _ _) hread₀
    obtain ⟨hpre, hwle, hlen'⟩ := uniqueFwd_prefix (x :: xs)
      ((x :: xs).length) 1 1 w' (x :: xs) l'
      hlen1 (Nat.le_refl _) (Nat.le_refl _) (Nat.sub_le _ _)
      rfl (by simp [dedupAdj]) (fun j _ => rfl) hfwd
    have hbw := uniqueFwd_bounds (x :: xs) l'
      ((x :: xs).length) 1 1 _ w' (Nat.le_refl _) (Nat.le_refl _)
      hfwd
    have hwlen : w' = (dedupAdj (x :: xs)).length :=
      squeeze_length_eq l' _ w' hpre (by rw [hlen']; exact hbw.1)
    exact ⟨w', l', by rw [List.length_cons] at hfwd; simp [vecUniqueFwd, hfwd],
      hpre, hwlen, hlen'⟩

/-! ## P2-M16: caller-record squeeze (`vec_unique_copy`) forward contract -/

/-- Squeeze forward totality: when the full squeeze fits the
    record, the scan from any reachable state returns (fuel
    induction threading the squeezed-prefix invariant, the
    record reads, and the caller-debt bound — the keep leg
    derives `w < lo.length` from the take-length law keyed on
    the last survivor, so the short leg is unreachable). -/
theorem uniqueCopyFwd_ok (la lo : List (BitVec 32))
    (fuel r w : Nat)
    (hle : r ≤ la.length) (hwle : w ≤ r) (hw1 : 1 ≤ w)
    (hF : la.length - r ≤ fuel)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hreadLo : ∀ p, p < lo.length → ∃ y, lo[p]? = some y)
    (hpre : lo.take w = dedupAdj (la.take r))
    (hwlo : w ≤ lo.length)
    (hcap : (dedupAdj la).length ≤ lo.length) :
    ∃ w' lo', uniqueCopyFwd la lo fuel r w = .ok (la.length, w', lo') := by
  induction fuel generalizing lo r w with
  | zero =>
    have him : r = la.length := by omega
    subst him
    exact ⟨w, lo, rfl⟩
  | succ n ih =>
    by_cases hlt : r < la.length
    · obtain ⟨y, hy⟩ := hread r hlt
      have hw1m : w - 1 < lo.length := by omega
      obtain ⟨p, hpred⟩ := hreadLo (w - 1) hw1m
      have hlast : (dedupAdj (la.take r)).getLast? = some p := by
        rw [← hpre]
        exact take_getLast_of_getElem? lo w p hw1 hwlo hpred
      by_cases hkeep : (y != p) = true
      · have hwlen1 : (dedupAdj (la.take (r + 1))).length
          = w + 1 := by
          have h := dedupAdj_take_succ_keep la r y p hy hlast hkeep
          rw [h, ← hpre, List.length_append]
          have htw : (lo.take w).length = w := by
            rw [List.length_take, Nat.min_eq_left hwlo]
          rw [htw, List.length_singleton]
        have hmono := dedupAdj_take_length_le la (r + 1)
        have hwlt : w < lo.length := by omega
        obtain ⟨wOld, hwget⟩ : ∃ z, lo[w]? = some z :=
          ⟨lo[w], List.getElem?_eq_getElem hwlt⟩
        have hF' : la.length - (r + 1) ≤ n := by omega
        have htake_set : (lo.set w y).take (w + 1)
            = (lo.take w) ++ [y] :=
          take_set_succ_self lo w y hwlt
        have hpre' : (lo.set w y).take (w + 1)
            = dedupAdj (la.take (r + 1)) := by
          rw [htake_set, hpre,
            dedupAdj_take_succ_keep la r y p hy hlast hkeep]
        have hwlo' : w + 1 ≤ (lo.set w y).length := by
          have hlen : (lo.set w y).length = lo.length := by
            simp [List.length_set]
          omega
        have hreadLo' : ∀ p, p < (lo.set w y).length →
            ∃ z, ((lo.set w y)[p]? = some z) := by
          intro p hp
          have hplen : p < lo.length := by
            have hlen : (lo.set w y).length = lo.length := by
              simp [List.length_set]
            omega
          by_cases hpw : p = w
          · rw [hpw]
            exact ⟨y, List.getElem?_set_self hwlt⟩
          · obtain ⟨z, hz⟩ := hreadLo p hplen
            exact ⟨z, by
              rw [List.getElem?_set_ne (show w ≠ p by omega)]
              exact hz⟩
        have hcap' : (dedupAdj la).length ≤
            (lo.set w y).length := by
          have hlen : (lo.set w y).length = lo.length := by
            simp [List.length_set]
          rw [hlen]; exact hcap
        obtain ⟨w', lo', h⟩ := ih (lo := lo.set w y)
          (r := r + 1) (w := w + 1)
          (hle := by omega) (hwle := by omega) (hw1 := by omega)
          (hF := hF') (hreadLo := hreadLo') (hpre := hpre')
          (hwlo := hwlo') (hcap := hcap')
        exact ⟨w', lo', by
          simp only [uniqueCopyFwd, dite_eq_left hlt, hy, hpred,
            hkeep, hwget]
          exact h⟩
      · have hdrop : (y != p) = false := by
          cases h : (y != p) with
          | true => exact absurd h hkeep
          | false => rfl
        have hF' : la.length - (r + 1) ≤ n := by omega
        have hpre' : lo.take w = dedupAdj (la.take (r + 1)) := by
          rw [dedupAdj_take_succ_drop la r y p hy hlast hdrop, hpre]
        obtain ⟨w', lo', h⟩ := ih (lo := lo)
          (r := r + 1) (w := w)
          (hle := by omega) (hwle := by omega) (hw1 := hw1)
          (hF := hF') (hreadLo := hreadLo) (hpre := hpre')
          (hwlo := hwlo) (hcap := hcap)
        exact ⟨w', lo', by
          simp only [uniqueCopyFwd, dite_eq_left hlt, hy, hpred,
            hdrop]
          exact h⟩
    · have him : r = la.length := by omega
      subst him
      exact ⟨w, lo, by simp [uniqueCopyFwd]⟩

/-- Squeeze forward prefix contract, ok leg: the written
    prefix is the squeeze of the scanned prefix, the count
    never retreats, the record length is unchanged (fuel
    induction threading the prefix, suffix, bound, reads, and
    capacity facts — the M12 `copyIfFwd_prefix` shape on the
    record list with the M13 squeeze oracle). -/
theorem uniqueCopyFwd_prefix (la lo₀ : List (BitVec 32))
    (fuel r w w' : Nat) (lo lo' : List (BitVec 32))
    (hle : r ≤ la.length) (hwle : w ≤ r) (hw1 : 1 ≤ w)
    (hF : la.length - r ≤ fuel)
    (hlen : lo.length = lo₀.length)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hreadLo : ∀ p, p < lo.length → ∃ y, lo[p]? = some y)
    (hpre : lo.take w = dedupAdj (la.take r))
    (hwlo : w ≤ lo.length)
    (hcap : (dedupAdj la).length ≤ lo₀.length)
    (hsuf : ∀ j, w ≤ j → lo[j]? = lo₀[j]?)
    (hfwd : uniqueCopyFwd la lo fuel r w = .ok (la.length, w', lo')) :
    lo'.take w' = dedupAdj la ∧
      w ≤ w' ∧ lo'.length = lo₀.length := by
  induction fuel generalizing lo r w with
  | zero =>
    have hpair : (r, w, lo) = (la.length, w', lo') := by
      simpa [uniqueCopyFwd] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    refine ⟨?_, Nat.le_refl _, hlen⟩
    rw [List.take_length] at hpre
    exact hpre
  | succ n ih =>
    by_cases hlt : r < la.length
    · obtain ⟨y, hy⟩ := hread r hlt
      have hw1m : w - 1 < lo.length := by omega
      obtain ⟨p, hpred⟩ := hreadLo (w - 1) hw1m
      have hlast : (dedupAdj (la.take r)).getLast? = some p := by
        rw [← hpre]
        exact take_getLast_of_getElem? lo w p hw1 hwlo hpred
      by_cases hkeep : (y != p) = true
      · have hwlen1 : (dedupAdj (la.take (r + 1))).length
          = w + 1 := by
          have h := dedupAdj_take_succ_keep la r y p hy hlast hkeep
          rw [h, ← hpre, List.length_append]
          have htw : (lo.take w).length = w := by
            rw [List.length_take, Nat.min_eq_left hwlo]
          rw [htw, List.length_singleton]
        have hmono := dedupAdj_take_length_le la (r + 1)
        have hwlt : w < lo.length := by omega
        obtain ⟨wOld, hwget⟩ : ∃ z, lo[w]? = some z :=
          ⟨lo[w], List.getElem?_eq_getElem hwlt⟩
        have hF' : la.length - (r + 1) ≤ n := by omega
        have hlen' : (lo.set w y).length = lo₀.length := by
          simp [List.length_set, hlen]
        have htake_set : (lo.set w y).take (w + 1)
            = (lo.take w) ++ [y] :=
          take_set_succ_self lo w y hwlt
        have hpre' : (lo.set w y).take (w + 1)
            = dedupAdj (la.take (r + 1)) := by
          rw [htake_set, hpre,
            dedupAdj_take_succ_keep la r y p hy hlast hkeep]
        have hwlo' : w + 1 ≤ (lo.set w y).length := by
          have hlenS : (lo.set w y).length = lo.length := by
            simp [List.length_set]
          omega
        have hreadLo' : ∀ p, p < (lo.set w y).length →
            ∃ z, ((lo.set w y)[p]? = some z) := by
          intro p hp
          have hplen : p < lo.length := by
            have hlenS : (lo.set w y).length = lo.length := by
              simp [List.length_set]
            omega
          by_cases hpw : p = w
          · rw [hpw]
            exact ⟨y, List.getElem?_set_self hwlt⟩
          · obtain ⟨z, hz⟩ := hreadLo p hplen
            exact ⟨z, by
              rw [List.getElem?_set_ne (show w ≠ p by omega)]
              exact hz⟩
        have hsuf' : ∀ j, w + 1 ≤ j → (lo.set w y)[j]? = lo₀[j]? := by
          intro j hj
          rw [List.getElem?_set_ne (show w ≠ j by omega)]
          exact hsuf j (by omega)
        have hfwd' : uniqueCopyFwd la (lo.set w y) n (r + 1)
            (w + 1) = .ok (la.length, w', lo') := by
          have h := hfwd
          simp only [uniqueCopyFwd, dite_eq_left hlt, hy, hpred,
            hkeep, hwget] at h
          exact h
        obtain ⟨hA, hB, hC⟩ := ih (lo := lo.set w y)
          (r := r + 1) (w := w + 1)
          (hle := by omega) (hwle := by omega) (hw1 := by omega)
          (hF := hF') (hlen := hlen')
          (hreadLo := hreadLo') (hpre := hpre') (hwlo := hwlo')
          (hsuf := hsuf') (hfwd := hfwd')
        exact ⟨hA, by omega, hC⟩
      · have hdrop : (y != p) = false := by
          cases h : (y != p) with
          | true => exact absurd h hkeep
          | false => rfl
        have hF' : la.length - (r + 1) ≤ n := by omega
        have hpre' : lo.take w = dedupAdj (la.take (r + 1)) := by
          rw [dedupAdj_take_succ_drop la r y p hy hlast hdrop, hpre]
        have hfwd' : uniqueCopyFwd la lo n (r + 1) w =
            .ok (la.length, w', lo') := by
          have h := hfwd
          simp only [uniqueCopyFwd, dite_eq_left hlt, hy, hpred,
            hdrop] at h
          exact h
        obtain ⟨hA, hB, hC⟩ := ih (lo := lo)
          (r := r + 1) (w := w)
          (hle := by omega) (hwle := by omega) (hw1 := hw1)
          (hF := hF') (hlen := hlen)
          (hreadLo := hreadLo) (hpre := hpre') (hwlo := hwlo)
          (hsuf := hsuf) (hfwd := hfwd')
        exact ⟨hA, by omega, hC⟩
    · have him : r = la.length := by omega
      subst him
      have hpair : (la.length, w, lo) = (la.length, w', lo') := by
        cases n with
        | zero => simpa [uniqueCopyFwd] using hfwd
        | succ n =>
          have hneg : ¬ la.length < la.length := by omega
          simpa [uniqueCopyFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      refine ⟨?_, Nat.le_refl _, hlen⟩
      rw [List.take_length] at hpre
      exact hpre

/-- Squeeze survivor-count bound: the returned count never
    exceeds the record length while the scan fits (fuel
    induction threading the prefix and capacity facts — the
    ok-leg write rule). -/
theorem uniqueCopyFwd_le (la lo : List (BitVec 32))
    (fuel r w w' : Nat) (lo' : List (BitVec 32))
    (hle : r ≤ la.length) (hwle : w ≤ r) (hw1 : 1 ≤ w)
    (hF : la.length - r ≤ fuel)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hreadLo : ∀ p, p < lo.length → ∃ y, lo[p]? = some y)
    (hpre : lo.take w = dedupAdj (la.take r))
    (hwlo : w ≤ lo.length)
    (hcap : (dedupAdj la).length ≤ lo.length)
    (hfwd : uniqueCopyFwd la lo fuel r w = .ok (la.length, w', lo')) :
    w' ≤ lo.length := by
  induction fuel generalizing lo r w with
  | zero =>
    have hpair : (r, w, lo) = (la.length, w', lo') := by
      simpa [uniqueCopyFwd] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    exact hwlo
  | succ n ih =>
    by_cases hlt : r < la.length
    · obtain ⟨y, hy⟩ := hread r hlt
      have hw1m : w - 1 < lo.length := by omega
      obtain ⟨p, hpred⟩ := hreadLo (w - 1) hw1m
      have hlast : (dedupAdj (la.take r)).getLast? = some p := by
        rw [← hpre]
        exact take_getLast_of_getElem? lo w p hw1 hwlo hpred
      by_cases hkeep : (y != p) = true
      · have hwlen1 : (dedupAdj (la.take (r + 1))).length
          = w + 1 := by
          have h := dedupAdj_take_succ_keep la r y p hy hlast hkeep
          rw [h, ← hpre, List.length_append]
          have htw : (lo.take w).length = w := by
            rw [List.length_take, Nat.min_eq_left hwlo]
          rw [htw, List.length_singleton]
        have hmono := dedupAdj_take_length_le la (r + 1)
        have hwlt : w < lo.length := by omega
        obtain ⟨wOld, hwget⟩ : ∃ z, lo[w]? = some z :=
          ⟨lo[w], List.getElem?_eq_getElem hwlt⟩
        have hF' : la.length - (r + 1) ≤ n := by omega
        have htake_set : (lo.set w y).take (w + 1)
            = (lo.take w) ++ [y] :=
          take_set_succ_self lo w y hwlt
        have hpre' : (lo.set w y).take (w + 1)
            = dedupAdj (la.take (r + 1)) := by
          rw [htake_set, hpre,
            dedupAdj_take_succ_keep la r y p hy hlast hkeep]
        have hwlo' : w + 1 ≤ (lo.set w y).length := by
          have hlenS : (lo.set w y).length = lo.length := by
            simp [List.length_set]
          omega
        have hcap' : (dedupAdj la).length ≤
            (lo.set w y).length := by
          have hlenS : (lo.set w y).length = lo.length := by
            simp [List.length_set]
          rw [hlenS]; exact hcap
        have hfwd' : uniqueCopyFwd la (lo.set w y) n (r + 1)
            (w + 1) = .ok (la.length, w', lo') := by
          have h := hfwd
          simp only [uniqueCopyFwd, dite_eq_left hlt, hy, hpred,
            hkeep, hwget] at h
          exact h
        have h := ih (lo := lo.set w y)
          (r := r + 1) (w := w + 1)
          (hle := by omega) (hwle := by omega) (hw1 := by omega)
          (hF := hF')
          (hreadLo := by
            intro p hp
            have hplen : p < lo.length := by
              have hlenS : (lo.set w y).length = lo.length := by
                simp [List.length_set]
              omega
            by_cases hpw : p = w
            · rw [hpw]
              exact ⟨y, List.getElem?_set_self hwlt⟩
            · obtain ⟨z, hz⟩ := hreadLo p hplen
              exact ⟨z, by
                rw [List.getElem?_set_ne (show w ≠ p by omega)]
                exact hz⟩)
          (hpre := hpre') (hwlo := hwlo') (hcap := hcap')
          (hfwd := hfwd')
        have hlenS : (lo.set w y).length = lo.length := by
          simp [List.length_set]
        omega
      · have hdrop : (y != p) = false := by
          cases h : (y != p) with
          | true => exact absurd h hkeep
          | false => rfl
        have hF' : la.length - (r + 1) ≤ n := by omega
        have hpre' : lo.take w = dedupAdj (la.take (r + 1)) := by
          rw [dedupAdj_take_succ_drop la r y p hy hlast hdrop, hpre]
        have hfwd' : uniqueCopyFwd la lo n (r + 1) w =
            .ok (la.length, w', lo') := by
          have h := hfwd
          simp only [uniqueCopyFwd, dite_eq_left hlt, hy, hpred,
            hdrop] at h
          exact h
        exact ih (lo := lo)
          (r := r + 1) (w := w)
          (hle := by omega) (hwle := by omega) (hw1 := hw1)
          (hF := hF')
          (hreadLo := hreadLo)
          (hpre := hpre') (hwlo := hwlo) (hcap := hcap)
          (hfwd := hfwd')
    · have him : r = la.length := by omega
      subst him
      have hpair : (la.length, w, lo) = (la.length, w', lo') := by
        cases n with
        | zero => simpa [uniqueCopyFwd] using hfwd
        | succ n =>
          have hneg : ¬ la.length < la.length := by omega
          simpa [uniqueCopyFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      exact hwlo

/-- Squeeze forward short-`out` error leg: when the scanned
    prefix fits but the total squeeze overflows the record,
    the scan fails loudly (fuel induction threading the
    squeezed prefix and the record bound; the zero/exhausted
    cases are discharged by the length facts). -/
theorem uniqueCopyFwd_err_short (la lo : List (BitVec 32))
    (fuel r w : Nat)
    (hle : r ≤ la.length) (hwle : w ≤ r) (hw1 : 1 ≤ w)
    (hF : la.length - r ≤ fuel)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hreadLo : ∀ p, p < lo.length → ∃ y, lo[p]? = some y)
    (hpre : lo.take w = dedupAdj (la.take r))
    (hwlo : w ≤ lo.length)
    (hmore : lo.length < (dedupAdj la).length) :
    uniqueCopyFwd la lo fuel r w = .error .AssertFail := by
  induction fuel generalizing lo r w with
  | zero =>
    have him : r = la.length := by omega
    subst him
    have htw : (lo.take w).length = w := by
      rw [List.length_take, Nat.min_eq_left hwlo]
    rw [List.take_length] at hpre
    have hde : (dedupAdj la).length = w := by
      rw [← hpre, htw]
    omega
  | succ n ih =>
    by_cases hlt : r < la.length
    · obtain ⟨y, hy⟩ := hread r hlt
      have hw1m : w - 1 < lo.length := by omega
      obtain ⟨p, hpred⟩ := hreadLo (w - 1) hw1m
      have hlast : (dedupAdj (la.take r)).getLast? = some p := by
        rw [← hpre]
        exact take_getLast_of_getElem? lo w p hw1 hwlo hpred
      by_cases hkeep : (y != p) = true
      · by_cases hmiss : lo[w]? = none
        · simpa [uniqueCopyFwd, dite_eq_left hlt, hy, hpred,
            hkeep, hmiss]
        · have hsome : ∃ z, lo[w]? = some z := by
            match h : lo[w]? with
            | none => exact absurd h hmiss
            | some z => exact ⟨z, rfl⟩
          obtain ⟨wOld, hwget⟩ := hsome
          have hwlt : w < lo.length :=
            transformRead_lt lo w wOld hwget
          have hF' : la.length - (r + 1) ≤ n := by omega
          have htake_set : (lo.set w y).take (w + 1)
              = (lo.take w) ++ [y] :=
            take_set_succ_self lo w y hwlt
          have hpre' : (lo.set w y).take (w + 1)
              = dedupAdj (la.take (r + 1)) := by
            rw [htake_set, hpre,
              dedupAdj_take_succ_keep la r y p hy hlast hkeep]
          have hwlo' : w + 1 ≤ (lo.set w y).length := by
            have hlenS : (lo.set w y).length = lo.length := by
              simp [List.length_set]
            omega
          have hmore' : (lo.set w y).length <
              (dedupAdj la).length := by
            have hlenS : (lo.set w y).length = lo.length := by
              simp [List.length_set]
            rw [hlenS]; exact hmore
          have h := ih (lo := lo.set w y)
            (r := r + 1) (w := w + 1)
            (hle := by omega) (hwle := by omega) (hw1 := by omega)
            (hF := hF')
            (hreadLo := by
              intro p hp
              have hplen : p < lo.length := by
                have hlenS : (lo.set w y).length = lo.length := by
                  simp [List.length_set]
                omega
              by_cases hpw : p = w
              · rw [hpw]
                exact ⟨y, List.getElem?_set_self hwlt⟩
              · obtain ⟨z, hz⟩ := hreadLo p hplen
                exact ⟨z, by
                  rw [List.getElem?_set_ne (show w ≠ p by omega)]
                  exact hz⟩)
            (hpre := hpre') (hwlo := hwlo') (hmore := hmore')
          simpa [uniqueCopyFwd, dite_eq_left hlt, hy, hpred,
            hkeep, hwget] using h
      · have hdrop : (y != p) = false := by
          cases h : (y != p) with
          | true => exact absurd h hkeep
          | false => rfl
        have hF' : la.length - (r + 1) ≤ n := by omega
        have hpre' : lo.take w = dedupAdj (la.take (r + 1)) := by
          rw [dedupAdj_take_succ_drop la r y p hy hlast hdrop, hpre]
        have h := ih (lo := lo)
          (r := r + 1) (w := w)
          (hle := by omega) (hwle := by omega) (hw1 := hw1)
          (hF := hF')
          (hreadLo := hreadLo)
          (hpre := hpre') (hwlo := hwlo) (hmore := hmore)
        simpa [uniqueCopyFwd, dite_eq_left hlt, hy, hpred,
          hdrop] using h
    · have him : r = la.length := by omega
      subst him
      have htw : (lo.take w).length = w := by
        rw [List.length_take, Nat.min_eq_left hwlo]
      rw [List.take_length] at hpre
      have hde : (dedupAdj la).length = w := by
        rw [← hpre, htw]
      omega

/-- Short record fires loudly from the seeded state: more
    squeeze than record words means the forward scan errors. -/
theorem uniqueCopyFwd_err_of_overflow (la : List (BitVec 32))
    (lo₁ : List (BitVec 32))
    (hle : 1 ≤ la.length)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hreadLo₁ : ∀ p, p < lo₁.length → ∃ y, lo₁[p]? = some y)
    (hpre₁ : lo₁.take 1 = dedupAdj (la.take 1))
    (hwlo₁ : 1 ≤ lo₁.length)
    (hmore : lo₁.length < (dedupAdj la).length) :
    uniqueCopyFwd la lo₁ la.length 1 1 = .error .AssertFail :=
  uniqueCopyFwd_err_short la lo₁ la.length 1 1 hle (Nat.le_refl _)
    (Nat.le_refl _) (by omega) hread hreadLo₁ hpre₁ hwlo₁ hmore

/-- Closed caller-record squeeze contract: when the squeeze
    fits, the forward returns the squeeze count over the
    squeeze prefix, record length unchanged. -/
theorem vecUniqueCopyFwd_correct (la lo : List (BitVec 32))
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hcap : (dedupAdj la).length ≤ lo.length) :
    ∃ (w' : Nat) (lo' : List (BitVec 32)),
      vecUniqueCopyFwd la lo = .ok (.u64 (BitVec.ofNat 64 w')) ∧
      lo'.take w' = dedupAdj la ∧
      w' = (dedupAdj la).length ∧
      lo'.length = lo.length := by
  cases la with
  | nil => exact ⟨0, lo, by simp [vecUniqueCopyFwd], by simp [dedupAdj],
      rfl, rfl⟩
  | cons a0 xs =>
    have hlen1 : 1 ≤ (a0 :: xs).length := by simp
    have hcap1 : 0 < lo.length := by
      have hnn := dedupAdj_nonempty (show (a0 :: xs) ≠ [] by simp)
      have hpos : 0 < (dedupAdj (a0 :: xs)).length :=
        List.length_pos_iff.mpr hnn
      omega
    obtain ⟨o0, ho0⟩ : ∃ z, lo[0]? = some z :=
      ⟨lo[0], List.getElem?_eq_getElem (by omega : 0 < lo.length)⟩
    have hreadLo : ∀ p, p < lo.length → ∃ y, lo[p]? = some y := by
      intro p hp
      exact ⟨lo[p], List.getElem?_eq_getElem hp⟩
    have h0lt : 0 < lo.length := by omega
    have hpre₁ : (lo.set 0 a0).take 1
        = dedupAdj ((a0 :: xs).take 1) := by
      rw [show (1 : Nat) = 0 + 1 from rfl,
        take_set_succ_self lo 0 a0 h0lt]
      simp [dedupAdj]
    have hreadLo₁ : ∀ p, p < (lo.set 0 a0).length →
        ∃ y, ((lo.set 0 a0)[p]? = some y) := by
      intro p hp
      have hplen : p < lo.length := by
        have hlenS : (lo.set 0 a0).length = lo.length := by
          simp [List.length_set]
        omega
      by_cases hpw : p = 0
      · rw [hpw]
        exact ⟨a0, List.getElem?_set_self h0lt⟩
      · obtain ⟨z, hz⟩ := hreadLo p hplen
        exact ⟨z, by
          rw [List.getElem?_set_ne (by omega : (0 : Nat) ≠ p)]
          exact hz⟩
    have hcapS : (dedupAdj (a0 :: xs)).length ≤
        (lo.set 0 a0).length := by
      have hlenS : (lo.set 0 a0).length = lo.length := by
        simp [List.length_set]
      rw [hlenS]; exact hcap
    obtain ⟨w', lo', hfwd⟩ := uniqueCopyFwd_ok (a0 :: xs)
      (lo.set 0 a0) ((a0 :: xs).length) 1 1 hlen1 (Nat.le_refl _)
      (Nat.le_refl _) (Nat.sub_le _ _) hread hreadLo₁ hpre₁
      (by simp [List.length_set]; omega) hcapS
    have hsuf : ∀ j, 1 ≤ j → ((lo.set 0 a0)[j]? = lo[j]?) := by
      intro j hj
      rw [List.getElem?_set_ne (show (0 : Nat) ≠ j by omega)]
    obtain ⟨hpref, hleW, hlen'⟩ := uniqueCopyFwd_prefix (a0 :: xs) lo
      ((a0 :: xs).length) 1 1 w' (lo.set 0 a0) lo' hlen1
      (Nat.le_refl _) (Nat.le_refl _) (Nat.sub_le _ _)
      (by simp [List.length_set]) hread hreadLo₁ hpre₁
      (by simp [List.length_set]; omega) hcap hsuf hfwd
    have hb := uniqueCopyFwd_le (a0 :: xs) (lo.set 0 a0)
      ((a0 :: xs).length) 1 1 w' lo' (hle := hlen1)
      (hwle := Nat.le_refl _) (hw1 := Nat.le_refl _)
      (hF := Nat.sub_le _ _) (hread := hread) (hreadLo := hreadLo₁)
      (hpre := hpre₁)
      (hwlo := by simp [List.length_set]; omega) (hcap := hcapS)
      (hfwd := hfwd)
    have hlenS : (lo.set 0 a0).length = lo.length := by
      simp [List.length_set]
    have hwlen : w' = (dedupAdj (a0 :: xs)).length :=
      squeeze_length_eq lo' _ w' hpref (by
        rw [hlen', ← hlenS]; exact hb)
    refine ⟨w', lo', by simp only [vecUniqueCopyFwd, ho0, hfwd], hpref,
      hwlen, hlen'⟩

/-! ## P2-M17: out-of-place reverse (`vec_reverse_copy`) forward contract -/

/-- Reverse-copy forward ok leg: when the record fits, the
    countdown scan succeeds, filling the record prefix with
    `la.reverse` (the `w + j = la.length` coupling plus the
    take-prefix invariant pin the exit: `j = 0` forces
    `w = la.length` and the prefix becomes the full reverse). -/
theorem reverseCopyFwd_ok (la lo : List (BitVec 32))
    (fuel w j : Nat)
    (hwj : w + j = la.length) (hle : j ≤ la.length)
    (hF : j ≤ fuel)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hpre : lo.take w = (la.drop j).reverse)
    (hwlo : w ≤ lo.length)
    (hcap : la.length ≤ lo.length) :
    ∃ w' lo', reverseCopyFwd la lo fuel w j = .ok (w', 0, lo') ∧
      lo'.take w' = la.reverse ∧
      w' = la.length ∧ lo'.length = lo.length := by
  induction fuel generalizing lo w j with
  | zero =>
    have hj0 : j = 0 := by omega
    subst hj0
    have hwlen : w = la.length := by omega
    subst hwlen
    refine ⟨la.length, lo, rfl, ?_, rfl, rfl⟩
    simpa using hpre
  | succ n ih =>
    by_cases hj0 : 0 < j
    · obtain ⟨y, hy⟩ := hread (j - 1) (by omega)
      have hwlt : w < lo.length := by omega
      have hwget : lo[w]? = some lo[w] :=
        List.getElem?_eq_getElem hwlt
      have hF' : j - 1 ≤ n := by omega
      have htake_set : (lo.set w y).take (w + 1)
          = (lo.take w) ++ [y] :=
        take_set_succ_self lo w y hwlt
      have hpre' : (lo.set w y).take (w + 1)
          = ((la.drop (j - 1))).reverse := by
        rw [htake_set, hpre,
          drop_reverse_succ la j y (by omega) hy]
      have hlenS : (lo.set w y).length = lo.length := by
        simp [List.length_set]
      have hwlo' : w + 1 ≤ (lo.set w y).length := by omega
      have hcap' : la.length ≤ (lo.set w y).length := by
        rw [hlenS]; exact hcap
      obtain ⟨w', lo', hfwd, hpref, hwlen, hlen'⟩ :=
        ih (lo := lo.set w y)
        (w := w + 1) (j := j - 1)
        (hwj := by omega) (hle := by omega)
        (hF := hF')
        (hpre := hpre') (hwlo := hwlo') (hcap := hcap')
      refine ⟨w', lo', ?_, hpref, hwlen, ?_⟩
      · simp only [reverseCopyFwd, dite_eq_left hj0, hy, hwget]
        exact hfwd
      · rw [hlen', hlenS]
    · have hj0' : j = 0 := by omega
      subst hj0'
      have hwlen : w = la.length := by omega
      subst hwlen
      refine ⟨la.length, lo, ?_, ?_, rfl, rfl⟩
      · simp [reverseCopyFwd]
      · simpa using hpre

/-- Reverse-copy forward short-`out` error leg: when the scanned
    prefix fits but the total reverse overflows the record, the
    scan fails loudly (fuel induction threading the reversed
    prefix and the record bound; the zero/exhausted cases are
    discharged by the length facts). -/
theorem reverseCopyFwd_err_short (la lo : List (BitVec 32))
    (fuel w j : Nat)
    (hwj : w + j = la.length) (hle : j ≤ la.length)
    (hF : j ≤ fuel)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hpre : lo.take w = (la.drop j).reverse)
    (hwlo : w ≤ lo.length)
    (hmore : lo.length < la.length) :
    reverseCopyFwd la lo fuel w j = .error .AssertFail := by
  induction fuel generalizing lo w j with
  | zero =>
    have hj0 : j = 0 := by omega
    subst hj0
    have hwlen : w = la.length := by omega
    have h := congrArg List.length hpre
    simp only [List.length_take, List.length_reverse,
      List.length_drop] at h
    omega
  | succ n ih =>
    by_cases hj0 : 0 < j
    · obtain ⟨y, hy⟩ := hread (j - 1) (by omega)
      by_cases hmiss : lo[w]? = none
      · simp [reverseCopyFwd, dite_eq_left hj0, hy, hmiss]
      · have hsome : ∃ z, lo[w]? = some z := by
          match h : lo[w]? with
          | none => exact absurd h hmiss
          | some z => exact ⟨z, rfl⟩
        obtain ⟨wOld, hwget⟩ := hsome
        have hwlt : w < lo.length :=
          transformRead_lt lo w wOld hwget
        have hF' : j - 1 ≤ n := by omega
        have htake_set : (lo.set w y).take (w + 1)
            = (lo.take w) ++ [y] :=
          take_set_succ_self lo w y hwlt
        have hpre' : (lo.set w y).take (w + 1)
            = ((la.drop (j - 1))).reverse := by
          rw [htake_set, hpre,
            drop_reverse_succ la j y (by omega) hy]
        have hlenS : (lo.set w y).length = lo.length := by
          simp [List.length_set]
        have hwlo' : w + 1 ≤ (lo.set w y).length := by omega
        have hmore' : (lo.set w y).length < la.length := by
          rw [hlenS]; exact hmore
        have h := ih (lo := lo.set w y)
          (w := w + 1) (j := j - 1)
          (hwj := by omega) (hle := by omega)
          (hF := hF')
          (hpre := hpre') (hwlo := hwlo') (hmore := hmore')
        simpa [reverseCopyFwd, dite_eq_left hj0, hy, hwget] using h
    · have hj0' : j = 0 := by omega
      subst hj0'
      have hwlen : w = la.length := by omega
      have h := congrArg List.length hpre
      simp only [List.length_take, List.length_reverse,
        List.length_drop] at h
      omega

/-- Short record fires loudly from the entry state: more source
    than record words means the forward scan errors. -/
theorem reverseCopyFwd_err_of_overflow (la : List (BitVec 32))
    (lo₁ : List (BitVec 32))
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hmore : lo₁.length < la.length) :
    reverseCopyFwd la lo₁ la.length 0 la.length = .error .AssertFail :=
  reverseCopyFwd_err_short la lo₁ la.length 0 la.length
    (by omega) (Nat.le_refl _) (Nat.le_refl _)
    hread (by simp) (Nat.zero_le _) hmore

/-- Closed caller-record reverse contract: when the reverse fits,
    the forward returns the source length over the reversed
    prefix, record length unchanged. -/
theorem vecReverseCopyFwd_correct (la lo : List (BitVec 32))
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hcap : la.length ≤ lo.length) :
    ∃ (w' : Nat) (lo' : List (BitVec 32)),
      vecReverseCopyFwd la lo = .ok (.u64 (BitVec.ofNat 64 w')) ∧
      lo'.take w' = la.reverse ∧
      w' = la.length ∧
      lo'.length = lo.length := by
  cases la with
  | nil =>
    exact ⟨0, lo, by simp [vecReverseCopyFwd], by simp, rfl, rfl⟩
  | cons a0 xs =>
    have hlen : 0 + (a0 :: xs).length = (a0 :: xs).length := by omega
    obtain ⟨w', lo', hfwd, hpref, hwlen, hlen'⟩ :=
      reverseCopyFwd_ok (a0 :: xs) lo ((a0 :: xs).length) 0
        ((a0 :: xs).length) hlen (Nat.le_refl _)
        (Nat.le_refl _) hread (by simp) (Nat.zero_le _) hcap
    refine ⟨w', lo', ?_, hpref, hwlen, hlen'⟩
    simp only [vecReverseCopyFwd, hfwd]

/-! ## P2-M11: sorted-range intersection (`vec_intersect`) forward contract -/

/-- Sorted-merge intersection oracle with min-count multiplicity:
    heads compare under signed `slt`; the smaller head cannot occur
    in the other (sorted) tail and is dropped, mutually-non-smaller
    heads are recorded once and both cursors advance. -/
def intersectOracle : List (BitVec 32) → List (BitVec 32) →
    List (BitVec 32)
  | [], _ => []
  | _, [] => []
  | x :: xs, y :: ys =>
    if x.slt y then intersectOracle xs (y :: ys)
    else if y.slt x then intersectOracle (x :: xs) ys
    else x :: intersectOracle xs ys
termination_by la lb => la.length + lb.length

/-- Signed `≤` (as `slt`-false) is transitive: `z ≥ y ≥ x`
    gives `z ≥ x`. -/
theorem slt_ge_trans {x y z : BitVec 32}
    (h1 : (y.slt x) = false) (h2 : (z.slt y) = false) :
    (z.slt x) = false := by
  have e1 : ¬ y.toInt < x.toInt := by
    simpa [BitVec.slt_eq_decide] using h1
  have e2 : ¬ z.toInt < y.toInt := by
    simpa [BitVec.slt_eq_decide] using h2
  have e3 : ¬ z.toInt < x.toInt := by omega
  simpa [BitVec.slt_eq_decide] using e3

/-- Split a drop at a known `getElem?` position. -/
theorem drop_cons_of_getElem? (l : List (BitVec 32)) (i : Nat)
    (x : BitVec 32)
    (hx : l[i]? = some x) : l.drop i = x :: l.drop (i + 1) := by
  apply List.ext_getElem?
  intro m
  cases m with
  | zero =>
    simp only [List.getElem?_cons_zero, List.getElem?_drop,
      Nat.add_zero]
    exact hx
  | succ m =>
    simp only [List.getElem?_cons_succ, List.getElem?_drop]
    have heq : i + (m + 1) = i + 1 + m := by omega
    rw [heq]

/-- Taking one past a write exposes the written word after the
    old prefix. -/
theorem take_set_succ (l : List (BitVec 32)) (w : Nat)
    (x : BitVec 32)
    (hw : w < l.length) :
    (l.set w x).take (w + 1) = (l.take w) ++ [x] := by
  rw [set_take_cons_drop l w x hw,
    take_append_cons _ _ _ _ (by rw [List.length_take]; omega)]
  have he : w + 1 - (l.take w).length - 1 = 0 := by
    rw [List.length_take]; omega
  rw [he, List.take_zero]

/-- Oracle head step, advance-`i`: a strictly smaller left head
    drops without recording. -/
theorem intersectOracle_advI (x y : BitVec 32)
    (xs ys : List (BitVec 32))
    (hlt : (x.slt y) = true) :
    intersectOracle (x :: xs) (y :: ys) =
      intersectOracle xs (y :: ys) := by
  simp [intersectOracle, hlt]

/-- Oracle head step, advance-`j`: a strictly smaller right head
    drops without recording. -/
theorem intersectOracle_advJ (x y : BitVec 32)
    (xs ys : List (BitVec 32))
    (hne : (x.slt y) = false) (hgt : (y.slt x) = true) :
    intersectOracle (x :: xs) (y :: ys) =
      intersectOracle (x :: xs) ys := by
  simp [intersectOracle, hne, hgt]

/-- Oracle head step, write: mutually-non-smaller heads record
    once and both sides advance. -/
theorem intersectOracle_write (x y : BitVec 32)
    (xs ys : List (BitVec 32))
    (hge1 : (x.slt y) = false) (hge2 : (y.slt x) = false) :
    intersectOracle (x :: xs) (y :: ys) =
      x :: intersectOracle xs ys := by
  simp [intersectOracle, hge1, hge2]

/-- Forward conservation + sortedness: the recorded prefix plus the
    oracle of the remaining suffixes always equals the initial
    record plus the whole oracle; the record stays sorted; the
    capacity invariant is preserved. Fuel induction threading one
    forward step per branch (the oracle unfolds in lockstep with
    the cursor move). -/
theorem intersectFwd_ok (la lb lo : List (BitVec 32)) (G i j w : Nat)
    (Z : List (BitVec 32)) (i' j' w' : Nat) (lo' : List (BitVec 32))
    (hsA : SortedSeg la 0 la.length) (hsB : SortedSeg lb 0 lb.length)
    (hsO : SortedSeg lo 0 w)
    (hcrossA : ∀ p, p < w → ∀ a, lo[p]? = some a →
      ∀ q, i ≤ q → q < la.length → ∀ b, la[q]? = some b →
      (b.slt a) = false)
    (hcrossB : ∀ p, p < w → ∀ a, lo[p]? = some a →
      ∀ q, j ≤ q → q < lb.length → ∀ b, lb[q]? = some b →
      (b.slt a) = false)
    (hcap : w + min (la.length - i) (lb.length - j) ≤ lo.length)
    (hZ : lo.take w ++ intersectOracle (la.drop i) (lb.drop j) =
      Z ++ intersectOracle la lb)
    (hfwd : intersectFwd la lb lo G i j w = .ok (i', j', w', lo')) :
    (lo'.take w' ++ intersectOracle (la.drop i') (lb.drop j') =
      Z ++ intersectOracle la lb) ∧
    SortedSeg lo' 0 w' ∧
    w' + min (la.length - i') (lb.length - j') ≤ lo'.length := by
  induction G generalizing la lb lo i j w Z with
  | zero =>
    have hpair : (i, j, w, lo) = (i', j', w', lo') := by
      simpa [intersectFwd] using hfwd
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
    exact ⟨hZ, hsO, hcap⟩
  | succ G ih =>
    by_cases hltA : i < la.length
    · by_cases hltB : j < lb.length
      · obtain ⟨x, hgetA⟩ : ∃ x, la[i]? = some x :=
          ⟨_, List.getElem?_eq_getElem hltA⟩
        obtain ⟨y, hgetB⟩ : ∃ y, lb[j]? = some y :=
          ⟨_, List.getElem?_eq_getElem hltB⟩
        have hdropA : la.drop i = x :: la.drop (i + 1) :=
          drop_cons_of_getElem? la i x hgetA
        have hdropB : lb.drop j = y :: lb.drop (j + 1) :=
          drop_cons_of_getElem? lb j y hgetB
        by_cases hlt : (x.slt y) = true
        · have hfwd' : intersectFwd la lb lo G (i + 1) j w =
              .ok (i', j', w', lo') := by
            simpa [intersectFwd, dite_eq_left hltA, dite_eq_left hltB,
              hgetA, hgetB, hlt] using hfwd
          have hstep : intersectOracle (la.drop i) (lb.drop j) =
              intersectOracle (la.drop (i + 1)) (lb.drop j) := by
            rw [hdropA, hdropB, intersectOracle_advI _ _ _ _ hlt]
          have hZ' : lo.take w ++
              intersectOracle (la.drop (i + 1)) (lb.drop j) =
              Z ++ intersectOracle la lb := by
            rw [← hstep]; exact hZ
          have hcrossA' : ∀ p, p < w → ∀ a, lo[p]? = some a →
              ∀ q, i + 1 ≤ q → q < la.length → ∀ b, la[q]? = some b →
              (b.slt a) = false := by
            intro p hp a ha q hiq hqm b hb
            exact hcrossA p hp a ha q (by omega) hqm b hb
          have hcap' : w + min (la.length - (i + 1)) (lb.length - j) ≤
              lo.length := by
            omega
          obtain ⟨hcons, hsorted, hcapI⟩ :=
            ih (la := la) (lb := lb) (lo := lo) (i := i + 1) (j := j)
              (w := w) (Z := Z) (hsA := hsA) (hsB := hsB) (hsO := hsO)
              (hcrossA := hcrossA') (hcrossB := hcrossB) (hcap := hcap')
              (hZ := hZ') (hfwd := hfwd')
          exact ⟨hcons, hsorted, hcapI⟩
        · by_cases hgt : (y.slt x) = true
          · have hne : (x.slt y) = false := by
              cases hxy : x.slt y with
              | true => exact absurd hxy hlt
              | false => rfl
            have hfwd' : intersectFwd la lb lo G i (j + 1) w =
                .ok (i', j', w', lo') := by
              simpa [intersectFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hne, hgt] using hfwd
            have hstep : intersectOracle (la.drop i) (lb.drop j) =
                intersectOracle (la.drop i) (lb.drop (j + 1)) := by
              rw [hdropA, hdropB, intersectOracle_advJ _ _ _ _ hne hgt]
            have hZ' : lo.take w ++
                intersectOracle (la.drop i) (lb.drop (j + 1)) =
                Z ++ intersectOracle la lb := by
              rw [← hstep]; exact hZ
            have hcrossB' : ∀ p, p < w → ∀ a, lo[p]? = some a →
                ∀ q, j + 1 ≤ q → q < lb.length → ∀ b, lb[q]? = some b →
                (b.slt a) = false := by
              intro p hp a ha q hjq hqm b hb
              exact hcrossB p hp a ha q (by omega) hqm b hb
            have hcap' : w + min (la.length - i) (lb.length - (j + 1)) ≤
                lo.length := by
              omega
            obtain ⟨hcons, hsorted, hcapI⟩ :=
              ih (la := la) (lb := lb) (lo := lo) (i := i) (j := j + 1)
                (w := w) (Z := Z) (hsA := hsA) (hsB := hsB) (hsO := hsO)
                (hcrossA := hcrossA) (hcrossB := hcrossB') (hcap := hcap')
                (hZ := hZ') (hfwd := hfwd')
            exact ⟨hcons, hsorted, hcapI⟩
          · have hge1 : (x.slt y) = false := by
              cases hxy : x.slt y with
              | true => exact absurd hxy hlt
              | false => rfl
            have hge2 : (y.slt x) = false := by
              cases hyx : y.slt x with
              | true => exact absurd hyx hgt
              | false => rfl
            have hwlt : w < lo.length := by omega
            have htake : ((lo.set w x).take (w + 1)) =
                (lo.take w) ++ [x] := take_set_succ lo w x hwlt
            have hfwd' : intersectFwd la lb (lo.set w x) G (i + 1)
                (j + 1) (w + 1) = .ok (i', j', w', lo') := by
              simpa [intersectFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hge1, hge2] using hfwd
            have hstep : intersectOracle (la.drop i) (lb.drop j) =
                x :: intersectOracle (la.drop (i + 1))
                  (lb.drop (j + 1)) := by
              rw [hdropA, hdropB, intersectOracle_write _ _ _ _ hge1 hge2]
            have hZ' : (lo.set w x).take (w + 1) ++
                intersectOracle (la.drop (i + 1)) (lb.drop (j + 1)) =
                Z ++ intersectOracle la lb := by
              have hZZ := hZ
              rw [hstep] at hZZ
              rw [htake, List.append_assoc, List.cons_append,
                List.nil_append]
              exact hZZ
            have hsorted1 : SortedSeg (lo.set w x) 0 (w + 1) :=
              sortedSeg_snoc lo 0 w x hsO
                (fun p _ hpk a ha =>
                  hcrossA p hpk a ha i (Nat.le_refl _) hltA x hgetA)
                hwlt
            have hcrossA' : ∀ p, p < w + 1 → ∀ a,
                ((lo.set w x)[p]? : Option (BitVec 32)) = some a →
                ∀ q, i + 1 ≤ q → q < la.length → ∀ b, la[q]? = some b →
                (b.slt a) = false := by
              intro p hpw a ha q hiq hqm b hb
              by_cases hpk : p = w
              · rw [hpk] at ha
                have hax : a = x := by
                  have hget := List.getElem?_set_self hwlt (a := x)
                  rw [hget] at ha
                  exact (Option.some_inj.mp ha).symm
                rw [hax]
                exact hsA i q (by omega) (by omega) (by omega) x b
                  hgetA hb
              · have ha' : lo[p]? = some a := by
                  have h1 : (((lo.set w x)[p]? : Option (BitVec 32))) =
                      lo[p]? := by
                    rw [List.getElem?_set_ne (show w ≠ p by omega)]
                  rw [h1] at ha
                  exact ha
                exact hcrossA p (by omega) a ha' q (by omega) hqm b hb
            have hcrossB' : ∀ p, p < w + 1 → ∀ a,
                ((lo.set w x)[p]? : Option (BitVec 32)) = some a →
                ∀ q, j + 1 ≤ q → q < lb.length → ∀ b, lb[q]? = some b →
                (b.slt a) = false := by
              intro p hpw a ha q hjq hqm b hb
              by_cases hpk : p = w
              · rw [hpk] at ha
                have hax : a = x := by
                  have hget := List.getElem?_set_self hwlt (a := x)
                  rw [hget] at ha
                  exact (Option.some_inj.mp ha).symm
                rw [hax]
                have hby : (b.slt y) = false :=
                  hsB j q (by omega) (by omega) (by omega) y b hgetB hb
                exact slt_ge_trans hge2 hby
              · have ha' : lo[p]? = some a := by
                  have h1 : (((lo.set w x)[p]? : Option (BitVec 32))) =
                      lo[p]? := by
                    rw [List.getElem?_set_ne (show w ≠ p by omega)]
                  rw [h1] at ha
                  exact ha
                exact hcrossB p (by omega) a ha' q (by omega) hqm b hb
            have hcap' : (w + 1) +
                min (la.length - (i + 1)) (lb.length - (j + 1)) ≤
                (lo.set w x).length := by
              rw [List.length_set]; omega
            obtain ⟨hcons, hsorted, hcapI⟩ :=
              ih (la := la) (lb := lb) (lo := (lo.set w x))
                (i := i + 1) (j := j + 1) (w := w + 1) (Z := Z)
                (hsA := hsA) (hsB := hsB) (hsO := hsorted1)
                (hcrossA := hcrossA') (hcrossB := hcrossB')
                (hcap := hcap') (hZ := hZ') (hfwd := hfwd')
            exact ⟨hcons, hsorted, hcapI⟩
      · have hpair : (i, j, w, lo) = (i', j', w', lo') := by
          have hnegB : ¬ j < lb.length := by omega
          simpa [intersectFwd, dite_eq_left hltA,
            dite_eq_right hnegB] using hfwd
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
        exact ⟨hZ, hsO, hcap⟩
    · have hpair : (i, j, w, lo) = (i', j', w', lo') := by
        have hnegA : ¬ i < la.length := by omega
        simpa [intersectFwd, dite_eq_right hnegA] using hfwd
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
      exact ⟨hZ, hsO, hcap⟩

/-- Forward exhaustion: with fuel covering the remaining cursor
    distance, the scan ends with a cursor at its end. -/
theorem intersectFwd_exhausted (la lb lo : List (BitVec 32))
    (G i j w : Nat)
    (i' j' w' : Nat) (lo' : List (BitVec 32))
    (hile : i ≤ la.length) (hjle : j ≤ lb.length)
    (hF : (la.length - i) + (lb.length - j) ≤ G)
    (hfwd : intersectFwd la lb lo G i j w = .ok (i', j', w', lo')) :
    i' = la.length ∨ j' = lb.length := by
  induction G generalizing la lb lo i j w with
  | zero =>
    have hpair : (i, j, w, lo) = (i', j', w', lo') := by
      simpa [intersectFwd] using hfwd
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
    left; omega
  | succ G ih =>
    by_cases hltA : i < la.length
    · by_cases hltB : j < lb.length
      · obtain ⟨x, hgetA⟩ : ∃ x, la[i]? = some x :=
          ⟨_, List.getElem?_eq_getElem hltA⟩
        obtain ⟨y, hgetB⟩ : ∃ y, lb[j]? = some y :=
          ⟨_, List.getElem?_eq_getElem hltB⟩
        by_cases hlt : (x.slt y) = true
        · have hfwd' : intersectFwd la lb lo G (i + 1) j w =
              .ok (i', j', w', lo') := by
            simpa [intersectFwd, dite_eq_left hltA, dite_eq_left hltB,
              hgetA, hgetB, hlt] using hfwd
          exact ih (la := la) (lb := lb) (lo := lo)
            (i := i + 1) (j := j) (w := w) (by omega) hjle
            (by omega) (hfwd := hfwd')
        · by_cases hgt : (y.slt x) = true
          · have hne : (x.slt y) = false := by
              cases hxy : x.slt y with
              | true => exact absurd hxy hlt
              | false => rfl
            have hfwd' : intersectFwd la lb lo G i (j + 1) w =
                .ok (i', j', w', lo') := by
              simpa [intersectFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hne, hgt] using hfwd
            exact ih (la := la) (lb := lb) (lo := lo)
              (i := i) (j := j + 1) (w := w) hile (by omega)
              (by omega) (hfwd := hfwd')
          · have hge1 : (x.slt y) = false := by
              cases hxy : x.slt y with
              | true => exact absurd hxy hlt
              | false => rfl
            have hge2 : (y.slt x) = false := by
              cases hyx : y.slt x with
              | true => exact absurd hyx hgt
              | false => rfl
            have hfwd' : intersectFwd la lb (lo.set w x) G (i + 1)
                (j + 1) (w + 1) = .ok (i', j', w', lo') := by
              simpa [intersectFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hge1, hge2] using hfwd
            exact ih (la := la) (lb := lb) (lo := (lo.set w x))
              (i := i + 1) (j := j + 1) (w := w + 1) (by omega)
              (by omega) (by omega) (hfwd := hfwd')
      · have hpair : (i, j, w, lo) = (i', j', w', lo') := by
          have hnegB : ¬ j < lb.length := by omega
          simpa [intersectFwd, dite_eq_left hltA,
            dite_eq_right hnegB] using hfwd
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
        right; omega
    · have hpair : (i, j, w, lo) = (i', j', w', lo') := by
        have hnegA : ¬ i < la.length := by omega
        simpa [intersectFwd, dite_eq_right hnegA] using hfwd
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
      left; omega

/-- Forward totality: every in-bounds index failure is guarded
    away, so the scan always succeeds with enough fuel. -/
theorem intersectFwd_noFail (la lb lo : List (BitVec 32))
    (G i j w : Nat)
    (hile : i ≤ la.length) (hjle : j ≤ lb.length)
    (hF : (la.length - i) + (lb.length - j) ≤ G) :
    ∃ i' j' w' lo',
      intersectFwd la lb lo G i j w = .ok (i', j', w', lo') := by
  induction G generalizing la lb lo i j w with
  | zero =>
    exact ⟨i, j, w, lo, by simp [intersectFwd]⟩
  | succ G ih =>
    by_cases hltA : i < la.length
    · by_cases hltB : j < lb.length
      · obtain ⟨x, hgetA⟩ : ∃ x, la[i]? = some x :=
          ⟨_, List.getElem?_eq_getElem hltA⟩
        obtain ⟨y, hgetB⟩ : ∃ y, lb[j]? = some y :=
          ⟨_, List.getElem?_eq_getElem hltB⟩
        by_cases hlt : (x.slt y) = true
        · have hstep : intersectFwd la lb lo (G + 1) i j w =
              intersectFwd la lb lo G (i + 1) j w := by
            simp [intersectFwd, dite_eq_left hltA, dite_eq_left hltB,
              hgetA, hgetB, hlt]
          rw [hstep]
          exact ih (la := la) (lb := lb) (lo := lo)
            (i := i + 1) (j := j) (w := w) (by omega) hjle (by omega)
        · by_cases hgt : (y.slt x) = true
          · have hne : (x.slt y) = false := by
              cases hxy : x.slt y with
              | true => exact absurd hxy hlt
              | false => rfl
            have hstep : intersectFwd la lb lo (G + 1) i j w =
                intersectFwd la lb lo G i (j + 1) w := by
              simp [intersectFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hne, hgt]
            rw [hstep]
            exact ih (la := la) (lb := lb) (lo := lo)
              (i := i) (j := j + 1) (w := w) hile (by omega) (by omega)
          · have hge1 : (x.slt y) = false := by
              cases hxy : x.slt y with
              | true => exact absurd hxy hlt
              | false => rfl
            have hge2 : (y.slt x) = false := by
              cases hyx : y.slt x with
              | true => exact absurd hyx hgt
              | false => rfl
            have hstep : intersectFwd la lb lo (G + 1) i j w =
                intersectFwd la lb (lo.set w x) G (i + 1) (j + 1)
                  (w + 1) := by
              simp [intersectFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hge1, hge2]
            rw [hstep]
            exact ih (la := la) (lb := lb) (lo := (lo.set w x))
              (i := i + 1) (j := j + 1) (w := w + 1) (by omega)
              (by omega) (by omega)
      · exact ⟨i, j, w, lo, by
          have hnegB : ¬ j < lb.length := by omega
          simpa [intersectFwd, dite_eq_left hltA,
            dite_eq_right hnegB]⟩
    · exact ⟨i, j, w, lo, by
        have hnegA : ¬ i < la.length := by omega
        simpa [intersectFwd, dite_eq_right hnegA]⟩

/-- Top-level forward correctness: from sorted inputs and a
    caller-sized record, the full-fuel scan records exactly the
    intersection oracle, stays sorted, and reports its length. -/
theorem intersectFwd_correct (la lb lo : List (BitVec 32))
    (hsA : SortedSeg la 0 la.length) (hsB : SortedSeg lb 0 lb.length)
    (hcap0 : min la.length lb.length ≤ lo.length)
    (i' j' w' : Nat) (lo' : List (BitVec 32))
    (hfwd : intersectFwd la lb lo (la.length + lb.length + 1) 0 0 0 =
      .ok (i', j', w', lo')) :
    lo'.take w' = intersectOracle la lb ∧
    SortedSeg lo' 0 w' ∧
    w' = (intersectOracle la lb).length := by
  have hZ0 : (lo.take 0) ++ intersectOracle (la.drop 0) (lb.drop 0) =
      [] ++ intersectOracle la lb := by simp
  have hsO0 : SortedSeg lo 0 0 := by
    intro p hlo hpq hqk a b ha hb
    have hfalse : False := by omega
    exact hfalse.elim
  have hcrossA0 : ∀ p, p < 0 → ∀ a, lo[p]? = some a →
      ∀ q, 0 ≤ q → q < la.length → ∀ b, la[q]? = some b →
      (b.slt a) = false := by
    intro p hp
    have hfalse : False := by omega
    exact hfalse.elim
  have hcrossB0 : ∀ p, p < 0 → ∀ a, lo[p]? = some a →
      ∀ q, 0 ≤ q → q < lb.length → ∀ b, lb[q]? = some b →
      (b.slt a) = false := by
    intro p hp
    have hfalse : False := by omega
    exact hfalse.elim
  have hcap : 0 + min (la.length - 0) (lb.length - 0) ≤ lo.length := by
    simpa using hcap0
  obtain ⟨hcons, hsorted, hcap'⟩ :=
    intersectFwd_ok la lb lo (la.length + lb.length + 1) 0 0 0 [] i' j'
      w' lo' hsA hsB hsO0 hcrossA0 hcrossB0 hcap hZ0 hfwd
  obtain hexh := intersectFwd_exhausted la lb lo
    (la.length + lb.length + 1) 0 0 0 i' j' w' lo' (by omega) (by omega)
    (by omega) hfwd
  have hsuf : intersectOracle (la.drop i') (lb.drop j') = [] := by
    rcases hexh with h | h
    · rw [h, List.drop_length]; exact intersectOracle.eq_1 _
    · rw [h, List.drop_length]
      cases e : la.drop i' with
      | nil => exact intersectOracle.eq_1 _
      | cons x xs => simp [intersectOracle]
  have hlen : lo'.length = lo.length :=
    intersectFwd_length _ _ _ _ _ _ _ _ _ _ _ hfwd
  have hwle : w' ≤ lo'.length := by omega
  rw [hsuf, List.append_nil, List.nil_append] at hcons
  refine ⟨hcons, hsorted, ?_⟩
  have htake : (lo'.take w').length = w' := by
    rw [List.length_take]
    exact Nat.min_eq_left hwle
  rw [← htake, hcons]

/-- Whole-function forward correctness: the `u64` survivor count
    is the oracle length. The recorded list is discarded by the
    wrapper, so only the count is exposed here. -/
theorem vecIntersectFwd_correct (la lb lo : List (BitVec 32))
    (hsA : SortedSeg la 0 la.length) (hsB : SortedSeg lb 0 lb.length)
    (hcap0 : min la.length lb.length ≤ lo.length) :
    ∃ w', vecIntersectFwd la lb lo = .ok (.u64 (BitVec.ofNat 64 w')) ∧
      w' = (intersectOracle la lb).length := by
  obtain ⟨i', j', w', lo', hfwd⟩ :=
    intersectFwd_noFail la lb lo (la.length + lb.length + 1) 0 0 0
      (by omega) (by omega) (by omega)
  obtain ⟨_, _, hlen⟩ :=
    intersectFwd_correct la lb lo hsA hsB hcap0 i' j' w' lo' hfwd
  exact ⟨w', by simp only [vecIntersectFwd, hfwd], hlen⟩

/-! ## P2-M14: sorted-range union (`vec_union`) forward contract -/

/-- Sorted-merge union oracle with max-count multiplicity: heads
    compare under signed `slt`; the strictly smaller head is
    recorded and its side advances; mutually-non-smaller heads
    record once and both advance. An exhausted side contributes
    its survivor suffix. -/
def unionOracle : List (BitVec 32) → List (BitVec 32) →
    List (BitVec 32)
  | [], ys => ys
  | xs, [] => xs
  | x :: xs, y :: ys =>
    if x.slt y then x :: unionOracle xs (y :: ys)
    else if y.slt x then y :: unionOracle (x :: xs) ys
    else x :: unionOracle xs ys
termination_by la lb => la.length + lb.length

/-- Oracle head step, take-`a`: a strictly smaller left head is
    recorded and the left cursor advances. -/
theorem unionOracle_takeA (x y : BitVec 32)
    (xs ys : List (BitVec 32))
    (hlt : (x.slt y) = true) :
    unionOracle (x :: xs) (y :: ys) =
      x :: unionOracle xs (y :: ys) := by
  simp [unionOracle, hlt]

/-- Oracle head step, take-`b`: a strictly smaller right head is
    recorded and the right cursor advances. -/
theorem unionOracle_takeB (x y : BitVec 32)
    (xs ys : List (BitVec 32))
    (hne : (x.slt y) = false) (hgt : (y.slt x) = true) :
    unionOracle (x :: xs) (y :: ys) =
      y :: unionOracle (x :: xs) ys := by
  simp [unionOracle, hne, hgt]

/-- Oracle head step, take-both: mutually-non-smaller heads
    record once and both sides advance. -/
theorem unionOracle_takeBoth (x y : BitVec 32)
    (xs ys : List (BitVec 32))
    (hge1 : (x.slt y) = false) (hge2 : (y.slt x) = false) :
    unionOracle (x :: xs) (y :: ys) =
      x :: unionOracle xs ys := by
  simp [unionOracle, hge1, hge2]

/-- Strict-then-nonstrict chains through `slt`: `x < y ≤ b`
    gives `x ≤ b` (the take-branch cross fact: the recorded
    strict head stays below the surviving suffix). -/
theorem slt_lt_ge_trans {x y b : BitVec 32}
    (hlt : (x.slt y) = true) (hle : (b.slt y) = false) :
    (b.slt x) = false := by
  have e1 : x.toInt < y.toInt := by
    simpa [BitVec.slt_eq_decide] using hlt
  have e2 : ¬ b.toInt < y.toInt := by
    simpa [BitVec.slt_eq_decide] using hle
  have e3 : ¬ b.toInt < x.toInt := by omega
  simpa [BitVec.slt_eq_decide] using e3

/-- Forward conservation + sortedness: the recorded prefix plus the
    oracle of the remaining suffixes always equals the initial
    record plus the whole oracle; the record stays sorted; the
    capacity invariant is preserved. Fuel induction threading one
    forward step per branch (the oracle unfolds in lockstep with
    the cursor move). -/
theorem unionMainFwd_ok (la lb lo : List (BitVec 32)) (G i j w : Nat)
    (Z : List (BitVec 32)) (i' j' w' : Nat) (lo' : List (BitVec 32))
    (hsA : SortedSeg la 0 la.length) (hsB : SortedSeg lb 0 lb.length)
    (hsO : SortedSeg lo 0 w)
    (hcrossA : ∀ p, p < w → ∀ a, lo[p]? = some a →
      ∀ q, i ≤ q → q < la.length → ∀ b, la[q]? = some b →
      (b.slt a) = false)
    (hcrossB : ∀ p, p < w → ∀ a, lo[p]? = some a →
      ∀ q, j ≤ q → q < lb.length → ∀ b, lb[q]? = some b →
      (b.slt a) = false)
    (hcap : w + (la.length - i) + (lb.length - j) ≤ lo.length)
    (hZ : lo.take w ++ unionOracle (la.drop i) (lb.drop j) =
      Z ++ unionOracle la lb)
    (hfwd : unionMainFwd la lb lo G i j w = .ok (i', j', w', lo')) :
    (lo'.take w' ++ unionOracle (la.drop i') (lb.drop j') =
      Z ++ unionOracle la lb) ∧
    SortedSeg lo' 0 w' ∧
    w' + (la.length - i') + (lb.length - j') ≤ lo'.length ∧
    (∀ p, p < w' → ∀ a, lo'[p]? = some a →
      ∀ q, i' ≤ q → q < la.length → ∀ b, la[q]? = some b →
      (b.slt a) = false) ∧
    (∀ p, p < w' → ∀ a, lo'[p]? = some a →
      ∀ q, j' ≤ q → q < lb.length → ∀ b, lb[q]? = some b →
      (b.slt a) = false) := by
  induction G generalizing la lb lo i j w Z with
  | zero =>
    have hpair : (i, j, w, lo) = (i', j', w', lo') := by
      simpa [unionMainFwd] using hfwd
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
    exact ⟨hZ, hsO, hcap, hcrossA, hcrossB⟩
  | succ G ih =>
    by_cases hltA : i < la.length
    · by_cases hltB : j < lb.length
      · obtain ⟨x, hgetA⟩ : ∃ x, la[i]? = some x :=
          ⟨_, List.getElem?_eq_getElem hltA⟩
        obtain ⟨y, hgetB⟩ : ∃ y, lb[j]? = some y :=
          ⟨_, List.getElem?_eq_getElem hltB⟩
        have hdropA : la.drop i = x :: la.drop (i + 1) :=
          drop_cons_of_getElem? la i x hgetA
        have hdropB : lb.drop j = y :: lb.drop (j + 1) :=
          drop_cons_of_getElem? lb j y hgetB
        by_cases hlt : (x.slt y) = true
        · have hfwd' : unionMainFwd la lb (lo.set w x) G (i + 1) j
              (w + 1) = .ok (i', j', w', lo') := by
            simpa [unionMainFwd, dite_eq_left hltA, dite_eq_left hltB,
              hgetA, hgetB, hlt] using hfwd
          have hstep : unionOracle (la.drop i) (lb.drop j) =
              x :: unionOracle (la.drop (i + 1)) (lb.drop j) := by
            rw [hdropA, hdropB, unionOracle_takeA _ _ _ _ hlt]
          have hwlt : w < lo.length := by omega
          have htake : ((lo.set w x).take (w + 1)) =
              (lo.take w) ++ [x] := take_set_succ lo w x hwlt
          have hZ' : (lo.set w x).take (w + 1) ++
              unionOracle (la.drop (i + 1)) (lb.drop j) =
              Z ++ unionOracle la lb := by
            have hZZ := hZ
            rw [hstep] at hZZ
            rw [htake, List.append_assoc, List.cons_append,
              List.nil_append]
            exact hZZ
          have hsorted1 : SortedSeg (lo.set w x) 0 (w + 1) :=
            sortedSeg_snoc lo 0 w x hsO
              (fun p _ hpk a ha =>
                hcrossA p hpk a ha i (Nat.le_refl _) hltA x hgetA)
              hwlt
          have hcrossA' : ∀ p, p < w + 1 → ∀ a,
              ((lo.set w x)[p]? : Option (BitVec 32)) = some a →
              ∀ q, i + 1 ≤ q → q < la.length → ∀ b, la[q]? = some b →
              (b.slt a) = false := by
            intro p hpw a ha q hiq hqm b hb
            by_cases hpk : p = w
            · rw [hpk] at ha
              have hax : a = x := by
                have hget := List.getElem?_set_self hwlt (a := x)
                rw [hget] at ha
                exact (Option.some_inj.mp ha).symm
              rw [hax]
              exact hsA i q (by omega) (by omega) (by omega) x b
                hgetA hb
            · have ha' : lo[p]? = some a := by
                have h1 : (((lo.set w x)[p]? : Option (BitVec 32))) =
                    lo[p]? := by
                  rw [List.getElem?_set_ne (show w ≠ p by omega)]
                rw [h1] at ha
                exact ha
              exact hcrossA p (by omega) a ha' q (by omega) hqm b hb
          have hcrossB' : ∀ p, p < w + 1 → ∀ a,
              ((lo.set w x)[p]? : Option (BitVec 32)) = some a →
              ∀ q, j ≤ q → q < lb.length → ∀ b, lb[q]? = some b →
              (b.slt a) = false := by
            intro p hpw a ha q hjq hqm b hb
            by_cases hpk : p = w
            · rw [hpk] at ha
              have hax : a = x := by
                have hget := List.getElem?_set_self hwlt (a := x)
                rw [hget] at ha
                exact (Option.some_inj.mp ha).symm
              rw [hax]
              by_cases heq : q = j
              · subst heq
                have hbyy : b = y := by
                  rw [hgetB] at hb
                  exact (Option.some_inj.mp hb).symm
                rw [hbyy]
                have hirr : (y.slt y) = false := by
                  have e : ¬ y.toInt < y.toInt := by omega
                  simpa [BitVec.slt_eq_decide] using e
                exact slt_lt_ge_trans hlt hirr
              · have hby : (b.slt y) = false :=
                  hsB j q (by omega) (by omega) (by omega) y b
                    hgetB hb
                exact slt_lt_ge_trans hlt hby
            · have ha' : lo[p]? = some a := by
                have h1 : (((lo.set w x)[p]? : Option (BitVec 32))) =
                    lo[p]? := by
                  rw [List.getElem?_set_ne (show w ≠ p by omega)]
                rw [h1] at ha
                exact ha
              exact hcrossB p (by omega) a ha' q hjq hqm b hb
          have hcap' : (w + 1) + (la.length - (i + 1)) +
              (lb.length - j) ≤ (lo.set w x).length := by
            rw [List.length_set]; omega
          obtain ⟨hcons, hsorted, hcapI, hcrossAfin, hcrossBfin⟩ :=
            ih (la := la) (lb := lb) (lo := (lo.set w x))
              (i := i + 1) (j := j) (w := w + 1) (Z := Z)
              (hsA := hsA) (hsB := hsB) (hsO := hsorted1)
              (hcrossA := hcrossA') (hcrossB := hcrossB')
              (hcap := hcap') (hZ := hZ') (hfwd := hfwd')
          exact ⟨hcons, hsorted, hcapI, hcrossAfin, hcrossBfin⟩
        · by_cases hgt : (y.slt x) = true
          · have hne : (x.slt y) = false := by
              cases hxy : x.slt y with
              | true => exact absurd hxy hlt
              | false => rfl
            have hfwd' : unionMainFwd la lb (lo.set w y) G i (j + 1)
                (w + 1) = .ok (i', j', w', lo') := by
              simpa [unionMainFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hne, hgt] using hfwd
            have hstep : unionOracle (la.drop i) (lb.drop j) =
                y :: unionOracle (la.drop i) (lb.drop (j + 1)) := by
              rw [hdropA, hdropB, unionOracle_takeB _ _ _ _ hne hgt]
            have hwlt : w < lo.length := by omega
            have htake : ((lo.set w y).take (w + 1)) =
                (lo.take w) ++ [y] := take_set_succ lo w y hwlt
            have hZ' : (lo.set w y).take (w + 1) ++
                unionOracle (la.drop i) (lb.drop (j + 1)) =
                Z ++ unionOracle la lb := by
              have hZZ := hZ
              rw [hstep] at hZZ
              rw [htake, List.append_assoc, List.cons_append,
                List.nil_append]
              exact hZZ
            have hsorted1 : SortedSeg (lo.set w y) 0 (w + 1) :=
              sortedSeg_snoc lo 0 w y hsO
                (fun p _ hpk a ha =>
                  hcrossB p hpk a ha j (Nat.le_refl _) hltB y hgetB)
                hwlt
            have hcrossA' : ∀ p, p < w + 1 → ∀ a,
                ((lo.set w y)[p]? : Option (BitVec 32)) = some a →
                ∀ q, i ≤ q → q < la.length → ∀ b, la[q]? = some b →
                (b.slt a) = false := by
              intro p hpw a ha q hiq hqm b hb
              by_cases hpk : p = w
              · rw [hpk] at ha
                have hay : a = y := by
                  have hget := List.getElem?_set_self hwlt (a := y)
                  rw [hget] at ha
                  exact (Option.some_inj.mp ha).symm
                rw [hay]
                by_cases heq : q = i
                · subst heq
                  have hbxx : b = x := by
                    rw [hgetA] at hb
                    exact (Option.some_inj.mp hb).symm
                  rw [hbxx]
                  have hirr : (x.slt x) = false := by
                    have e : ¬ x.toInt < x.toInt := by omega
                    simpa [BitVec.slt_eq_decide] using e
                  exact slt_lt_ge_trans hgt hirr
                · have hbx : (b.slt x) = false :=
                    hsA i q (by omega) (by omega) (by omega) x b
                      hgetA hb
                  exact slt_lt_ge_trans hgt hbx
              · have ha' : lo[p]? = some a := by
                  have h1 : (((lo.set w y)[p]? : Option (BitVec 32))) =
                      lo[p]? := by
                    rw [List.getElem?_set_ne (show w ≠ p by omega)]
                  rw [h1] at ha
                  exact ha
                exact hcrossA p (by omega) a ha' q hiq hqm b hb
            have hcrossB' : ∀ p, p < w + 1 → ∀ a,
                ((lo.set w y)[p]? : Option (BitVec 32)) = some a →
                ∀ q, j + 1 ≤ q → q < lb.length → ∀ b, lb[q]? = some b →
                (b.slt a) = false := by
              intro p hpw a ha q hjq hqm b hb
              by_cases hpk : p = w
              · rw [hpk] at ha
                have hay : a = y := by
                  have hget := List.getElem?_set_self hwlt (a := y)
                  rw [hget] at ha
                  exact (Option.some_inj.mp ha).symm
                rw [hay]
                exact hsB j q (by omega) (by omega) (by omega) y b
                  hgetB hb
              · have ha' : lo[p]? = some a := by
                  have h1 : (((lo.set w y)[p]? : Option (BitVec 32))) =
                      lo[p]? := by
                    rw [List.getElem?_set_ne (show w ≠ p by omega)]
                  rw [h1] at ha
                  exact ha
                exact hcrossB p (by omega) a ha' q (by omega) hqm b hb
            have hcap' : (w + 1) + (la.length - i) +
                (lb.length - (j + 1)) ≤ (lo.set w y).length := by
              rw [List.length_set]; omega
            obtain ⟨hcons, hsorted, hcapI, hcrossAfin, hcrossBfin⟩ :=
              ih (la := la) (lb := lb) (lo := (lo.set w y))
                (i := i) (j := j + 1) (w := w + 1) (Z := Z)
                (hsA := hsA) (hsB := hsB) (hsO := hsorted1)
                (hcrossA := hcrossA') (hcrossB := hcrossB')
                (hcap := hcap') (hZ := hZ') (hfwd := hfwd')
            exact ⟨hcons, hsorted, hcapI, hcrossAfin, hcrossBfin⟩
          · have hge1 : (x.slt y) = false := by
              cases hxy : x.slt y with
              | true => exact absurd hxy hlt
              | false => rfl
            have hge2 : (y.slt x) = false := by
              cases hyx : y.slt x with
              | true => exact absurd hyx hgt
              | false => rfl
            have hfwd' : unionMainFwd la lb (lo.set w x) G (i + 1)
                (j + 1) (w + 1) = .ok (i', j', w', lo') := by
              simpa [unionMainFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hge1, hge2] using hfwd
            have hstep : unionOracle (la.drop i) (lb.drop j) =
                x :: unionOracle (la.drop (i + 1))
                  (lb.drop (j + 1)) := by
              rw [hdropA, hdropB, unionOracle_takeBoth _ _ _ _ hge1 hge2]
            have hwlt : w < lo.length := by omega
            have htake : ((lo.set w x).take (w + 1)) =
                (lo.take w) ++ [x] := take_set_succ lo w x hwlt
            have hZ' : (lo.set w x).take (w + 1) ++
                unionOracle (la.drop (i + 1)) (lb.drop (j + 1)) =
                Z ++ unionOracle la lb := by
              have hZZ := hZ
              rw [hstep] at hZZ
              rw [htake, List.append_assoc, List.cons_append,
                List.nil_append]
              exact hZZ
            have hsorted1 : SortedSeg (lo.set w x) 0 (w + 1) :=
              sortedSeg_snoc lo 0 w x hsO
                (fun p _ hpk a ha =>
                  hcrossA p hpk a ha i (Nat.le_refl _) hltA x hgetA)
                hwlt
            have hcrossA' : ∀ p, p < w + 1 → ∀ a,
                ((lo.set w x)[p]? : Option (BitVec 32)) = some a →
                ∀ q, i + 1 ≤ q → q < la.length → ∀ b, la[q]? = some b →
                (b.slt a) = false := by
              intro p hpw a ha q hiq hqm b hb
              by_cases hpk : p = w
              · rw [hpk] at ha
                have hax : a = x := by
                  have hget := List.getElem?_set_self hwlt (a := x)
                  rw [hget] at ha
                  exact (Option.some_inj.mp ha).symm
                rw [hax]
                exact hsA i q (by omega) (by omega) (by omega) x b
                  hgetA hb
              · have ha' : lo[p]? = some a := by
                  have h1 : (((lo.set w x)[p]? : Option (BitVec 32))) =
                      lo[p]? := by
                    rw [List.getElem?_set_ne (show w ≠ p by omega)]
                  rw [h1] at ha
                  exact ha
                exact hcrossA p (by omega) a ha' q (by omega) hqm b hb
            have hcrossB' : ∀ p, p < w + 1 → ∀ a,
                ((lo.set w x)[p]? : Option (BitVec 32)) = some a →
                ∀ q, j + 1 ≤ q → q < lb.length → ∀ b, lb[q]? = some b →
                (b.slt a) = false := by
              intro p hpw a ha q hjq hqm b hb
              by_cases hpk : p = w
              · rw [hpk] at ha
                have hax : a = x := by
                  have hget := List.getElem?_set_self hwlt (a := x)
                  rw [hget] at ha
                  exact (Option.some_inj.mp ha).symm
                rw [hax]
                have hby : (b.slt y) = false :=
                  hsB j q (by omega) (by omega) (by omega) y b
                    hgetB hb
                exact slt_ge_trans hge2 hby
              · have ha' : lo[p]? = some a := by
                  have h1 : (((lo.set w x)[p]? : Option (BitVec 32))) =
                      lo[p]? := by
                    rw [List.getElem?_set_ne (show w ≠ p by omega)]
                  rw [h1] at ha
                  exact ha
                exact hcrossB p (by omega) a ha' q (by omega) hqm b hb
            have hcap' : (w + 1) + (la.length - (i + 1)) +
                (lb.length - (j + 1)) ≤ (lo.set w x).length := by
              rw [List.length_set]; omega
            obtain ⟨hcons, hsorted, hcapI, hcrossAfin, hcrossBfin⟩ :=
              ih (la := la) (lb := lb) (lo := (lo.set w x))
                (i := i + 1) (j := j + 1) (w := w + 1) (Z := Z)
                (hsA := hsA) (hsB := hsB) (hsO := hsorted1)
                (hcrossA := hcrossA') (hcrossB := hcrossB')
                (hcap := hcap') (hZ := hZ') (hfwd := hfwd')
            exact ⟨hcons, hsorted, hcapI, hcrossAfin, hcrossBfin⟩
      · have hpair : (i, j, w, lo) = (i', j', w', lo') := by
          have hnegB : ¬ j < lb.length := by omega
          simpa [unionMainFwd, dite_eq_left hltA,
            dite_eq_right hnegB] using hfwd
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
        exact ⟨hZ, hsO, hcap, hcrossA, hcrossB⟩
    · have hpair : (i, j, w, lo) = (i', j', w', lo') := by
        have hnegA : ¬ i < la.length := by omega
        simpa [unionMainFwd, dite_eq_right hnegA] using hfwd
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
      exact ⟨hZ, hsO, hcap, hcrossA, hcrossB⟩

/-- Forward exhaustion: with fuel covering the remaining cursor
    distance, the scan ends with a cursor at its end. -/
theorem unionMainFwd_exhausted (la lb lo : List (BitVec 32))
    (G i j w : Nat)
    (i' j' w' : Nat) (lo' : List (BitVec 32))
    (hile : i ≤ la.length) (hjle : j ≤ lb.length)
    (hF : (la.length - i) + (lb.length - j) ≤ G)
    (hfwd : unionMainFwd la lb lo G i j w = .ok (i', j', w', lo')) :
    i' = la.length ∨ j' = lb.length := by
  induction G generalizing la lb lo i j w with
  | zero =>
    have hpair : (i, j, w, lo) = (i', j', w', lo') := by
      simpa [unionMainFwd] using hfwd
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
    left; omega
  | succ G ih =>
    by_cases hltA : i < la.length
    · by_cases hltB : j < lb.length
      · obtain ⟨x, hgetA⟩ : ∃ x, la[i]? = some x :=
          ⟨_, List.getElem?_eq_getElem hltA⟩
        obtain ⟨y, hgetB⟩ : ∃ y, lb[j]? = some y :=
          ⟨_, List.getElem?_eq_getElem hltB⟩
        by_cases hlt : (x.slt y) = true
        · have hfwd' : unionMainFwd la lb (lo.set w x) G (i + 1) j
              (w + 1) = .ok (i', j', w', lo') := by
            simpa [unionMainFwd, dite_eq_left hltA, dite_eq_left hltB,
              hgetA, hgetB, hlt] using hfwd
          exact ih (la := la) (lb := lb) (lo := (lo.set w x))
            (i := i + 1) (j := j) (w := w + 1) (by omega) hjle
            (by omega) (hfwd := hfwd')
        · by_cases hgt : (y.slt x) = true
          · have hne : (x.slt y) = false := by
              cases hxy : x.slt y with
              | true => exact absurd hxy hlt
              | false => rfl
            have hfwd' : unionMainFwd la lb (lo.set w y) G i (j + 1)
                (w + 1) = .ok (i', j', w', lo') := by
              simpa [unionMainFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hne, hgt] using hfwd
            exact ih (la := la) (lb := lb) (lo := (lo.set w y))
              (i := i) (j := j + 1) (w := w + 1) hile (by omega)
              (by omega) (hfwd := hfwd')
          · have hge1 : (x.slt y) = false := by
              cases hxy : x.slt y with
              | true => exact absurd hxy hlt
              | false => rfl
            have hge2 : (y.slt x) = false := by
              cases hyx : y.slt x with
              | true => exact absurd hyx hgt
              | false => rfl
            have hfwd' : unionMainFwd la lb (lo.set w x) G (i + 1)
                (j + 1) (w + 1) = .ok (i', j', w', lo') := by
              simpa [unionMainFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hge1, hge2] using hfwd
            exact ih (la := la) (lb := lb) (lo := (lo.set w x))
              (i := i + 1) (j := j + 1) (w := w + 1) (by omega)
              (by omega) (by omega) (hfwd := hfwd')
      · have hpair : (i, j, w, lo) = (i', j', w', lo') := by
          have hnegB : ¬ j < lb.length := by omega
          simpa [unionMainFwd, dite_eq_left hltA,
            dite_eq_right hnegB] using hfwd
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
        right; omega
    · have hpair : (i, j, w, lo) = (i', j', w', lo') := by
        have hnegA : ¬ i < la.length := by omega
        simpa [unionMainFwd, dite_eq_right hnegA] using hfwd
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
      left; omega

/-- Forward totality: every in-bounds index failure is guarded
    away, so the scan always succeeds with enough fuel. -/
theorem unionMainFwd_noFail (la lb lo : List (BitVec 32))
    (G i j w : Nat)
    (hile : i ≤ la.length) (hjle : j ≤ lb.length)
    (hF : (la.length - i) + (lb.length - j) ≤ G) :
    ∃ i' j' w' lo',
      unionMainFwd la lb lo G i j w = .ok (i', j', w', lo') := by
  induction G generalizing la lb lo i j w with
  | zero =>
    exact ⟨i, j, w, lo, by simp [unionMainFwd]⟩
  | succ G ih =>
    by_cases hltA : i < la.length
    · by_cases hltB : j < lb.length
      · obtain ⟨x, hgetA⟩ : ∃ x, la[i]? = some x :=
          ⟨_, List.getElem?_eq_getElem hltA⟩
        obtain ⟨y, hgetB⟩ : ∃ y, lb[j]? = some y :=
          ⟨_, List.getElem?_eq_getElem hltB⟩
        by_cases hlt : (x.slt y) = true
        · have hstep : unionMainFwd la lb lo (G + 1) i j w =
              unionMainFwd la lb (lo.set w x) G (i + 1) j (w + 1) := by
            simp [unionMainFwd, dite_eq_left hltA, dite_eq_left hltB,
              hgetA, hgetB, hlt]
          rw [hstep]
          exact ih (la := la) (lb := lb) (lo := (lo.set w x))
            (i := i + 1) (j := j) (w := w + 1) (by omega) hjle (by omega)
        · by_cases hgt : (y.slt x) = true
          · have hne : (x.slt y) = false := by
              cases hxy : x.slt y with
              | true => exact absurd hxy hlt
              | false => rfl
            have hstep : unionMainFwd la lb lo (G + 1) i j w =
                unionMainFwd la lb (lo.set w y) G i (j + 1) (w + 1) := by
              simp [unionMainFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hne, hgt]
            rw [hstep]
            exact ih (la := la) (lb := lb) (lo := (lo.set w y))
              (i := i) (j := j + 1) (w := w + 1) hile (by omega) (by omega)
          · have hge1 : (x.slt y) = false := by
              cases hxy : x.slt y with
              | true => exact absurd hxy hlt
              | false => rfl
            have hge2 : (y.slt x) = false := by
              cases hyx : y.slt x with
              | true => exact absurd hyx hgt
              | false => rfl
            have hstep : unionMainFwd la lb lo (G + 1) i j w =
                unionMainFwd la lb (lo.set w x) G (i + 1) (j + 1)
                  (w + 1) := by
              simp [unionMainFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hge1, hge2]
            rw [hstep]
            exact ih (la := la) (lb := lb) (lo := (lo.set w x))
              (i := i + 1) (j := j + 1) (w := w + 1) (by omega)
              (by omega) (by omega)
      · exact ⟨i, j, w, lo, by
          have hnegB : ¬ j < lb.length := by omega
          simpa [unionMainFwd, dite_eq_left hltA,
            dite_eq_right hnegB]⟩
    · exact ⟨i, j, w, lo, by
        have hnegA : ¬ i < la.length := by omega
        simpa [unionMainFwd, dite_eq_right hnegA]⟩

/-- Drain-`a` conservation + sortedness: the copied survivor
    prefix plus the remaining `a` suffix always equals the initial
    record; the record stays sorted; the capacity invariant is
    preserved. -/
theorem unionDrainAFwd_ok (la : List (BitVec 32)) (lo : List (BitVec 32))
    (G i w : Nat)
    (Z : List (BitVec 32)) (i' w' : Nat) (lo' : List (BitVec 32))
    (hsuf : SortedSeg la i la.length)
    (hsO : SortedSeg lo 0 w)
    (hcross : ∀ p, p < w → ∀ a, lo[p]? = some a →
      ∀ q, i ≤ q → q < la.length → ∀ b, la[q]? = some b →
      (b.slt a) = false)
    (hcap : w + (la.length - i) ≤ lo.length)
    (hZ : lo.take w ++ la.drop i = Z)
    (hfwd : unionDrainAFwd la lo G i w = .ok (i', w', lo')) :
    (lo'.take w' ++ la.drop i' = Z) ∧
    SortedSeg lo' 0 w' ∧
    w' + (la.length - i') ≤ lo'.length ∧
    (∀ p, p < w' → ∀ a, lo'[p]? = some a →
      ∀ q, i' ≤ q → q < la.length → ∀ b, la[q]? = some b →
      (b.slt a) = false) := by
  induction G generalizing la lo i w Z with
  | zero =>
    have hpair : (i, w, lo) = (i', w', lo') := by
      simpa [unionDrainAFwd] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    exact ⟨hZ, hsO, hcap, hcross⟩
  | succ G ih =>
    by_cases hltA : i < la.length
    · obtain ⟨x, hgetA⟩ : ∃ x, la[i]? = some x :=
        ⟨_, List.getElem?_eq_getElem hltA⟩
      have hdropA : la.drop i = x :: la.drop (i + 1) :=
        drop_cons_of_getElem? la i x hgetA
      have hfwd' : unionDrainAFwd la (lo.set w x) G (i + 1) (w + 1) =
          .ok (i', w', lo') := by
        simpa [unionDrainAFwd, dite_eq_left hltA, hgetA] using hfwd
      have hwlt : w < lo.length := by omega
      have htake : ((lo.set w x).take (w + 1)) =
          (lo.take w) ++ [x] := take_set_succ lo w x hwlt
      have hstep : lo.take w ++ la.drop i =
          ((lo.take w) ++ [x]) ++ la.drop (i + 1) := by
        rw [hdropA]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      have hZ' : (lo.set w x).take (w + 1) ++ la.drop (i + 1) = Z := by
        rw [htake, ← hstep]; exact hZ
      have hsorted1 : SortedSeg (lo.set w x) 0 (w + 1) :=
        sortedSeg_snoc lo 0 w x hsO
          (fun p _ hpk a ha =>
            hcross p hpk a ha i (Nat.le_refl _) hltA x hgetA)
          hwlt
      have hcross' : ∀ p, p < w + 1 → ∀ a,
          ((lo.set w x)[p]? : Option (BitVec 32)) = some a →
          ∀ q, i + 1 ≤ q → q < la.length → ∀ b, la[q]? = some b →
          (b.slt a) = false := by
        intro p hpw a ha q hiq hqm b hb
        by_cases hpk : p = w
        · rw [hpk] at ha
          have hax : a = x := by
            have hget := List.getElem?_set_self hwlt (a := x)
            rw [hget] at ha
            exact (Option.some_inj.mp ha).symm
          rw [hax]
          exact hsuf i q (by omega) (by omega) (by omega) x b
            hgetA hb
        · have ha' : lo[p]? = some a := by
            have h1 : (((lo.set w x)[p]? : Option (BitVec 32))) =
                lo[p]? := by
              rw [List.getElem?_set_ne (show w ≠ p by omega)]
            rw [h1] at ha
            exact ha
          exact hcross p (by omega) a ha' q (by omega) hqm b hb
      have hcap' : (w + 1) + (la.length - (i + 1)) ≤
          (lo.set w x).length := by
        rw [List.length_set]; omega
      have hsuf' : SortedSeg la (i + 1) la.length := by
        intro p q hpq1 hpq2 hpq3 a b ha hb
        exact hsuf p q (by omega) hpq2 hpq3 a b ha hb
      obtain ⟨hcons, hsorted, hcapI, hcrossFin⟩ :=
        ih (la := la) (lo := (lo.set w x))
          (i := i + 1) (w := w + 1) (Z := Z)
          (hsuf := hsuf') (hsO := hsorted1)
          (hcross := hcross') (hcap := hcap') (hZ := hZ')
          (hfwd := hfwd')
      exact ⟨hcons, hsorted, hcapI, hcrossFin⟩
    · have hpair : (i, w, lo) = (i', w', lo') := by
        have hnegA : ¬ i < la.length := by omega
        simpa [unionDrainAFwd, dite_eq_right hnegA] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      exact ⟨hZ, hsO, hcap, hcross⟩

/-- Drain-`b` conservation + sortedness: the copied survivor
    prefix plus the remaining `b` suffix always equals the initial
    record; the record stays sorted; the capacity invariant is
    preserved. -/
theorem unionDrainBFwd_ok (lb : List (BitVec 32)) (lo : List (BitVec 32))
    (G j w : Nat)
    (Z : List (BitVec 32)) (j' w' : Nat) (lo' : List (BitVec 32))
    (hsuf : SortedSeg lb j lb.length)
    (hsO : SortedSeg lo 0 w)
    (hcross : ∀ p, p < w → ∀ a, lo[p]? = some a →
      ∀ q, j ≤ q → q < lb.length → ∀ b, lb[q]? = some b →
      (b.slt a) = false)
    (hcap : w + (lb.length - j) ≤ lo.length)
    (hZ : lo.take w ++ lb.drop j = Z)
    (hfwd : unionDrainBFwd lb lo G j w = .ok (j', w', lo')) :
    (lo'.take w' ++ lb.drop j' = Z) ∧
    SortedSeg lo' 0 w' ∧
    w' + (lb.length - j') ≤ lo'.length ∧
    (∀ p, p < w' → ∀ a, lo'[p]? = some a →
      ∀ q, j' ≤ q → q < lb.length → ∀ b, lb[q]? = some b →
      (b.slt a) = false) := by
  induction G generalizing lb lo j w Z with
  | zero =>
    have hpair : (j, w, lo) = (j', w', lo') := by
      simpa [unionDrainBFwd] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    exact ⟨hZ, hsO, hcap, hcross⟩
  | succ G ih =>
    by_cases hltB : j < lb.length
    · obtain ⟨y, hgetB⟩ : ∃ y, lb[j]? = some y :=
        ⟨_, List.getElem?_eq_getElem hltB⟩
      have hdropB : lb.drop j = y :: lb.drop (j + 1) :=
        drop_cons_of_getElem? lb j y hgetB
      have hfwd' : unionDrainBFwd lb (lo.set w y) G (j + 1) (w + 1) =
          .ok (j', w', lo') := by
        simpa [unionDrainBFwd, dite_eq_left hltB, hgetB] using hfwd
      have hwlt : w < lo.length := by omega
      have htake : ((lo.set w y).take (w + 1)) =
          (lo.take w) ++ [y] := take_set_succ lo w y hwlt
      have hstep : lo.take w ++ lb.drop j =
          ((lo.take w) ++ [y]) ++ lb.drop (j + 1) := by
        rw [hdropB]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      have hZ' : (lo.set w y).take (w + 1) ++ lb.drop (j + 1) = Z := by
        rw [htake, ← hstep]; exact hZ
      have hsorted1 : SortedSeg (lo.set w y) 0 (w + 1) :=
        sortedSeg_snoc lo 0 w y hsO
          (fun p _ hpk a ha =>
            hcross p hpk a ha j (Nat.le_refl _) hltB y hgetB)
          hwlt
      have hcross' : ∀ p, p < w + 1 → ∀ a,
          ((lo.set w y)[p]? : Option (BitVec 32)) = some a →
          ∀ q, j + 1 ≤ q → q < lb.length → ∀ b, lb[q]? = some b →
          (b.slt a) = false := by
        intro p hpw a ha q hjq hqm b hb
        by_cases hpk : p = w
        · rw [hpk] at ha
          have hay : a = y := by
            have hget := List.getElem?_set_self hwlt (a := y)
            rw [hget] at ha
            exact (Option.some_inj.mp ha).symm
          rw [hay]
          exact hsuf j q (by omega) (by omega) (by omega) y b
            hgetB hb
        · have ha' : lo[p]? = some a := by
            have h1 : (((lo.set w y)[p]? : Option (BitVec 32))) =
                lo[p]? := by
              rw [List.getElem?_set_ne (show w ≠ p by omega)]
            rw [h1] at ha
            exact ha
          exact hcross p (by omega) a ha' q (by omega) hqm b hb
      have hcap' : (w + 1) + (lb.length - (j + 1)) ≤
          (lo.set w y).length := by
        rw [List.length_set]; omega
      have hsuf' : SortedSeg lb (j + 1) lb.length := by
        intro p q hpq1 hpq2 hpq3 a b ha hb
        exact hsuf p q (by omega) hpq2 hpq3 a b ha hb
      obtain ⟨hcons, hsorted, hcapI, hcrossFin⟩ :=
        ih (lb := lb) (lo := (lo.set w y))
          (j := j + 1) (w := w + 1) (Z := Z)
          (hsuf := hsuf') (hsO := hsorted1)
          (hcross := hcross') (hcap := hcap') (hZ := hZ')
          (hfwd := hfwd')
      exact ⟨hcons, hsorted, hcapI, hcrossFin⟩
    · have hpair : (j, w, lo) = (j', w', lo') := by
        have hnegB : ¬ j < lb.length := by omega
        simpa [unionDrainBFwd, dite_eq_right hnegB] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      exact ⟨hZ, hsO, hcap, hcross⟩

/-- Drain-`a` totality: with fuel covering the survivor suffix,
    the copy always succeeds. -/
theorem unionDrainAFwd_noFail (la : List (BitVec 32))
    (lo : List (BitVec 32)) (G i w : Nat)
    (hF : la.length - i ≤ G) :
    ∃ i' w' lo',
      unionDrainAFwd la lo G i w = .ok (i', w', lo') := by
  induction G generalizing la lo i w with
  | zero =>
    exact ⟨i, w, lo, by simp [unionDrainAFwd]⟩
  | succ G ih =>
    by_cases hltA : i < la.length
    · obtain ⟨x, hgetA⟩ : ∃ x, la[i]? = some x :=
        ⟨_, List.getElem?_eq_getElem hltA⟩
      have hstep : unionDrainAFwd la lo (G + 1) i w =
          unionDrainAFwd la (lo.set w x) G (i + 1) (w + 1) := by
        simp [unionDrainAFwd, dite_eq_left hltA, hgetA]
      rw [hstep]
      exact ih (la := la) (lo := (lo.set w x))
        (i := i + 1) (w := w + 1) (by omega)
    · exact ⟨i, w, lo, by
        have hnegA : ¬ i < la.length := by omega
        simpa [unionDrainAFwd, dite_eq_right hnegA]⟩

/-- Drain-`b` totality: with fuel covering the survivor suffix,
    the copy always succeeds. -/
theorem unionDrainBFwd_noFail (lb : List (BitVec 32))
    (lo : List (BitVec 32)) (G j w : Nat)
    (hF : lb.length - j ≤ G) :
    ∃ j' w' lo',
      unionDrainBFwd lb lo G j w = .ok (j', w', lo') := by
  induction G generalizing lb lo j w with
  | zero =>
    exact ⟨j, w, lo, by simp [unionDrainBFwd]⟩
  | succ G ih =>
    by_cases hltB : j < lb.length
    · obtain ⟨y, hgetB⟩ : ∃ y, lb[j]? = some y :=
        ⟨_, List.getElem?_eq_getElem hltB⟩
      have hstep : unionDrainBFwd lb lo (G + 1) j w =
          unionDrainBFwd lb (lo.set w y) G (j + 1) (w + 1) := by
        simp [unionDrainBFwd, dite_eq_left hltB, hgetB]
      rw [hstep]
      exact ih (lb := lb) (lo := (lo.set w y))
        (j := j + 1) (w := w + 1) (by omega)
    · exact ⟨j, w, lo, by
        have hnegB : ¬ j < lb.length := by omega
        simpa [unionDrainBFwd, dite_eq_right hnegB]⟩

/-- Drain-`a` exhaustion: with exact fuel the copy runs the
    survivor suffix to its end. -/
theorem unionDrainAFwd_exhausted (la : List (BitVec 32))
    (lo : List (BitVec 32)) (G i w : Nat)
    (i' w' : Nat) (lo' : List (BitVec 32))
    (hile : i ≤ la.length)
    (hF : la.length - i ≤ G)
    (hfwd : unionDrainAFwd la lo G i w = .ok (i', w', lo')) :
    i' = la.length := by
  induction G generalizing la lo i w with
  | zero =>
    have hpair : (i, w, lo) = (i', w', lo') := by
      simpa [unionDrainAFwd] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    omega
  | succ G ih =>
    by_cases hltA : i < la.length
    · obtain ⟨x, hgetA⟩ : ∃ x, la[i]? = some x :=
        ⟨_, List.getElem?_eq_getElem hltA⟩
      have hfwd' : unionDrainAFwd la (lo.set w x) G (i + 1) (w + 1) =
          .ok (i', w', lo') := by
        simpa [unionDrainAFwd, dite_eq_left hltA, hgetA] using hfwd
      exact ih (la := la) (lo := (lo.set w x))
        (i := i + 1) (w := w + 1) (by omega) (by omega)
        (hfwd := hfwd')
    · have hpair : (i, w, lo) = (i', w', lo') := by
        have hnegA : ¬ i < la.length := by omega
        simpa [unionDrainAFwd, dite_eq_right hnegA] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      omega

/-- Drain-`b` exhaustion: with exact fuel the copy runs the
    survivor suffix to its end. -/
theorem unionDrainBFwd_exhausted (lb : List (BitVec 32))
    (lo : List (BitVec 32)) (G j w : Nat)
    (j' w' : Nat) (lo' : List (BitVec 32))
    (hjle : j ≤ lb.length)
    (hF : lb.length - j ≤ G)
    (hfwd : unionDrainBFwd lb lo G j w = .ok (j', w', lo')) :
    j' = lb.length := by
  induction G generalizing lb lo j w with
  | zero =>
    have hpair : (j, w, lo) = (j', w', lo') := by
      simpa [unionDrainBFwd] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    omega
  | succ G ih =>
    by_cases hltB : j < lb.length
    · obtain ⟨y, hgetB⟩ : ∃ y, lb[j]? = some y :=
        ⟨_, List.getElem?_eq_getElem hltB⟩
      have hfwd' : unionDrainBFwd lb (lo.set w y) G (j + 1) (w + 1) =
          .ok (j', w', lo') := by
        simpa [unionDrainBFwd, dite_eq_left hltB, hgetB] using hfwd
      exact ih (lb := lb) (lo := (lo.set w y))
        (j := j + 1) (w := w + 1) (by omega) (by omega)
        (hfwd := hfwd')
    · have hpair : (j, w, lo) = (j', w', lo') := by
        have hnegB : ¬ j < lb.length := by omega
        simpa [unionDrainBFwd, dite_eq_right hnegB] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      omega

/-- Whole-function forward correctness: from sorted inputs and a
    caller-sized record (`a.size() + b.size()` slots), the
    main-plus-drains scan records exactly the union oracle,
    stays sorted, and reports its length. The three forward runs
    are hypotheses (the entries and the transfer feed the same
    runs, so no determinism argument is needed). -/
theorem vecUnionFwd_correct (la lb lo : List (BitVec 32))
    (hsA : SortedSeg la 0 la.length) (hsB : SortedSeg lb 0 lb.length)
    (hcap0 : la.length + lb.length ≤ lo.length)
    (i j w : Nat) (lo₁ : List (BitVec 32))
    (i₂ w₂ : Nat) (lo₂ : List (BitVec 32))
    (j₃ w₃ : Nat) (lo₃ : List (BitVec 32))
    (hfwdM : unionMainFwd la lb lo (la.length + lb.length + 1) 0 0 0 =
      .ok (i, j, w, lo₁))
    (hfwdA : unionDrainAFwd la lo₁ (la.length - i) i w =
      .ok (i₂, w₂, lo₂))
    (hfwdB : unionDrainBFwd lb lo₂ (lb.length - j) j w₂ =
      .ok (j₃, w₃, lo₃)) :
    (lo₃.take w₃ = unionOracle la lb) ∧
      SortedSeg lo₃ 0 w₃ ∧
      w₃ = (unionOracle la lb).length := by
  have hZ0 : (lo.take 0) ++ unionOracle (la.drop 0) (lb.drop 0) =
      [] ++ unionOracle la lb := by simp
  have hsO0 : SortedSeg lo 0 0 := by
    intro p hlo hpq hqk a b ha hb
    have hfalse : False := by omega
    exact hfalse.elim
  have hcrossA0 : ∀ p, p < 0 → ∀ a, lo[p]? = some a →
      ∀ q, 0 ≤ q → q < la.length → ∀ b, la[q]? = some b →
      (b.slt a) = false := by
    intro p hp
    have hfalse : False := by omega
    exact hfalse.elim
  have hcrossB0 : ∀ p, p < 0 → ∀ a, lo[p]? = some a →
      ∀ q, 0 ≤ q → q < lb.length → ∀ b, lb[q]? = some b →
      (b.slt a) = false := by
    intro p hp
    have hfalse : False := by omega
    exact hfalse.elim
  have hcap : 0 + (la.length - 0) + (lb.length - 0) ≤ lo.length := by
    simpa using hcap0
  obtain ⟨hconsM, hsortedM, hcapM, hcrossA1, hcrossB1⟩ :=
    unionMainFwd_ok la lb lo (la.length + lb.length + 1) 0 0 0 [] i j
      w lo₁ hsA hsB hsO0 hcrossA0 hcrossB0 hcap hZ0 hfwdM
  obtain ⟨hi_le, hj_le, hw_le, hlenM⟩ :=
    unionMainFwd_le la lb (la.length + lb.length + 1) 0 0 0 lo i j w lo₁
      (by omega) (by omega) hcap hfwdM
  obtain hexh := unionMainFwd_exhausted la lb lo
    (la.length + lb.length + 1) 0 0 0 i j w lo₁ (by omega) (by omega)
    (by omega) hfwdM
  have hsufA : SortedSeg la i la.length := by
    intro p q hpq1 hpq2 hpq3 a b ha hb
    exact hsA p q (by omega) hpq2 hpq3 a b ha hb
  have hsufB : SortedSeg lb j lb.length := by
    intro p q hpq1 hpq2 hpq3 a b ha hb
    exact hsB p q (by omega) hpq2 hpq3 a b ha hb
  have hcapA0 : w + (la.length - i) ≤ lo₁.length := by omega
  obtain ⟨hconsA, hsortedA, hcapA, hcrossA2⟩ :=
    unionDrainAFwd_ok la lo₁ (la.length - i) i w
      (lo₁.take w ++ la.drop i) i₂ w₂ lo₂
      hsufA hsortedM hcrossA1 hcapA0 rfl hfwdA
  have hexhA := unionDrainAFwd_exhausted la lo₁ (la.length - i) i w
    i₂ w₂ lo₂ hi_le (by omega) hfwdA
  have hw₂le : w₂ ≤ lo₂.length := by omega
  have hwle : w ≤ lo₁.length := by omega
  have hlenA : lo₂.length = lo₁.length :=
    unionDrainAFwd_length _ _ _ _ _ _ _ _ hfwdA
  have hcntA : w₂ + (la.length - i₂) = w + (la.length - i) := by
    have h := congrArg List.length hconsA
    simp only [List.length_append, List.length_take, List.length_drop,
      Nat.min_eq_left hw₂le, Nat.min_eq_left hwle] at h
    exact h
  have hcapB0 : w₂ + (lb.length - j) ≤ lo₂.length := by
    rw [hexhA] at hcntA
    simp only [Nat.sub_self, Nat.add_zero] at hcntA
    omega
  -- Drain-`a` take-equality (needed for the entry cross below).
  have htakeA : lo₂.take w₂ = lo₁.take w ++ la.drop i := by
    have h := hconsA
    rw [hexhA, List.drop_length, List.append_nil] at h
    exact h
  -- Drain-`b` entry cross: old records via the main exit cross;
  -- `a`-copied records are vacuous on one side or the other (the
  -- finished side contributes nothing).
  have hcrossB_entry : ∀ p, p < w₂ → ∀ a, lo₂[p]? = some a →
      ∀ q, j ≤ q → q < lb.length → ∀ b, lb[q]? = some b →
      (b.slt a) = false := by
    rcases hexh with hAi | hBj
    · have hw₂ : w₂ = w := by omega
      intro p hpw a ha q hjq hqm b hb
      have hpw' : p < w := by omega
      have e1 : (lo₂.take w₂)[p]? = lo₂[p]? :=
        List.getElem?_take_of_lt hpw
      have e2 : (lo₁.take w)[p]? = lo₁[p]? :=
        List.getElem?_take_of_lt hpw'
      have hplen : p < (lo₁.take w).length := by
        rw [List.length_take]; omega
      have h1 : (lo₂.take w₂)[p]? = (lo₁.take w)[p]? := by
        rw [htakeA, List.getElem?_append_left hplen]
      rw [e1, e2] at h1
      rw [h1] at ha
      exact hcrossB1 p hpw' a ha q hjq hqm b hb
    · intro p hpw a ha q hjq hqm b hb
      have hfalse : False := by omega
      exact hfalse.elim
  obtain ⟨hconsB, hsortedB, hcapB, hcrossB2⟩ :=
    unionDrainBFwd_ok lb lo₂ (lb.length - j) j w₂
      (lo₂.take w₂ ++ lb.drop j) j₃ w₃ lo₃
      hsufB hsortedA hcrossB_entry hcapB0 rfl hfwdB
  have hexhB := unionDrainBFwd_exhausted lb lo₂ (lb.length - j) j w₂
    j₃ w₃ lo₃ hj_le (by omega) hfwdB
  -- Chain the three conservations: each drain appends its
  -- survivor suffix to the incoming record.
  have htakeB : lo₃.take w₃ = lo₂.take w₂ ++ lb.drop j := by
    have h := hconsB
    rw [hexhB, List.drop_length, List.append_nil] at h
    exact h
  have hfin : lo₃.take w₃ = unionOracle la lb := by
    have hM := hconsM
    rw [List.nil_append] at hM
    -- hM : lo₁.take w ++ unionOracle (la.drop i) (lb.drop j) = unionOracle la lb
    rcases hexh with hAi | hBj
    · rw [hAi, List.drop_length] at hM
      -- oracle of ([], drop j) is the survivor tail
      have hor : unionOracle [] (lb.drop j) = lb.drop j := by
        simp [unionOracle]
      rw [hor] at hM
      rw [htakeB, htakeA, hAi, List.drop_length, List.append_nil]
      exact hM
    · rw [hBj, List.drop_length] at hM
      have hor : unionOracle (la.drop i) [] = la.drop i := by
        cases e : la.drop i with
        | nil => simp [unionOracle]
        | cons x xs => simp [unionOracle]
      rw [hor] at hM
      rw [htakeB, htakeA, hBj, List.drop_length, List.append_nil]
      exact hM
  have hcnt : w₃ = (unionOracle la lb).length := by
    have htake : (lo₃.take w₃).length = w₃ := by
      rw [List.length_take]
      have := hcapB
      omega
    rw [← htake, hfin]
  exact ⟨hfin, hsortedB, hcnt⟩

/-! ## P2-M15: sorted-range difference (`set_difference`) oracle -/

/-- Independent `set_difference`: a strictly smaller left head is
    recorded and the left cursor advances; a strictly smaller
    right head advances only the right cursor; equal heads
    advance both and record nothing (extra left copies beyond
    the right count survive). -/
def differenceOracle : List (BitVec 32) → List (BitVec 32) →
    List (BitVec 32)
  | [], _ => []
  | l, [] => l
  | x :: xs, y :: ys =>
    if x.slt y then x :: differenceOracle xs (y :: ys)
    else if y.slt x then differenceOracle (x :: xs) ys
    else differenceOracle xs ys
termination_by la lb => la.length + lb.length

/-- Oracle head step, take-left: a strictly smaller left head is
    recorded and the left cursor advances. -/
theorem differenceOracle_takeLeft (x y : BitVec 32)
    (xs ys : List (BitVec 32))
    (hlt : (x.slt y) = true) :
    differenceOracle (x :: xs) (y :: ys) =
      x :: differenceOracle xs (y :: ys) := by
  simp [differenceOracle, hlt]

/-- Oracle head step, advance-right: a strictly smaller right
    head advances only the right cursor. -/
theorem differenceOracle_advRight (x y : BitVec 32)
    (xs ys : List (BitVec 32))
    (hne : (x.slt y) = false) (hgt : (y.slt x) = true) :
    differenceOracle (x :: xs) (y :: ys) =
      differenceOracle (x :: xs) ys := by
  simp [differenceOracle, hne, hgt]

/-- Oracle head step, skip-both: mutually-non-smaller heads
    advance both sides and record nothing. -/
theorem differenceOracle_skipBoth (x y : BitVec 32)
    (xs ys : List (BitVec 32))
    (hge1 : (x.slt y) = false) (hge2 : (y.slt x) = false) :
    differenceOracle (x :: xs) (y :: ys) =
      differenceOracle xs ys := by
  simp [differenceOracle, hge1, hge2]

/-- Forward conservation + sortedness: the recorded prefix plus
    the oracle of the remaining suffixes always equals the
    initial record plus the whole oracle; the record stays
    sorted; the capacity invariant is preserved. Only the
    take-left leg writes (so capacity counts left remainder
    only); the advance-right and skip-both legs narrow the
    suffixes silently. Fuel induction threading one forward step
    per branch (the oracle unfolds in lockstep with the cursor
    move). -/
theorem differenceMainFwd_ok (la lb lo : List (BitVec 32)) (G i j w : Nat)
    (Z : List (BitVec 32)) (i' j' w' : Nat) (lo' : List (BitVec 32))
    (hsA : SortedSeg la 0 la.length) (hsB : SortedSeg lb 0 lb.length)
    (hsO : SortedSeg lo 0 w)
    (hcrossA : ∀ p, p < w → ∀ a, lo[p]? = some a →
      ∀ q, i ≤ q → q < la.length → ∀ b, la[q]? = some b →
      (b.slt a) = false)
    (hcrossB : ∀ p, p < w → ∀ a, lo[p]? = some a →
      ∀ q, j ≤ q → q < lb.length → ∀ b, lb[q]? = some b →
      (b.slt a) = false)
    (hcap : w + (la.length - i) ≤ lo.length)
    (hZ : lo.take w ++ differenceOracle (la.drop i) (lb.drop j) =
      Z ++ differenceOracle la lb)
    (hfwd : differenceMainFwd la lb lo G i j w = .ok (i', j', w', lo')) :
    (lo'.take w' ++ differenceOracle (la.drop i') (lb.drop j') =
      Z ++ differenceOracle la lb) ∧
    SortedSeg lo' 0 w' ∧
    w' + (la.length - i') ≤ lo'.length ∧
    (∀ p, p < w' → ∀ a, lo'[p]? = some a →
      ∀ q, i' ≤ q → q < la.length → ∀ b, la[q]? = some b →
      (b.slt a) = false) ∧
    (∀ p, p < w' → ∀ a, lo'[p]? = some a →
      ∀ q, j' ≤ q → q < lb.length → ∀ b, lb[q]? = some b →
      (b.slt a) = false) := by
  induction G generalizing la lb lo i j w Z with
  | zero =>
    have hpair : (i, j, w, lo) = (i', j', w', lo') := by
      simpa [differenceMainFwd] using hfwd
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
    exact ⟨hZ, hsO, hcap, hcrossA, hcrossB⟩
  | succ G ih =>
    by_cases hltA : i < la.length
    · by_cases hltB : j < lb.length
      · obtain ⟨x, hgetA⟩ : ∃ x, la[i]? = some x :=
          ⟨_, List.getElem?_eq_getElem hltA⟩
        obtain ⟨y, hgetB⟩ : ∃ y, lb[j]? = some y :=
          ⟨_, List.getElem?_eq_getElem hltB⟩
        have hdropA : la.drop i = x :: la.drop (i + 1) :=
          drop_cons_of_getElem? la i x hgetA
        have hdropB : lb.drop j = y :: lb.drop (j + 1) :=
          drop_cons_of_getElem? lb j y hgetB
        by_cases hlt : (x.slt y) = true
        · have hfwd' : differenceMainFwd la lb (lo.set w x) G (i + 1) j
              (w + 1) = .ok (i', j', w', lo') := by
            simpa [differenceMainFwd, dite_eq_left hltA, dite_eq_left hltB,
              hgetA, hgetB, hlt] using hfwd
          have hstep : differenceOracle (la.drop i) (lb.drop j) =
              x :: differenceOracle (la.drop (i + 1)) (lb.drop j) := by
            rw [hdropA, hdropB, differenceOracle_takeLeft _ _ _ _ hlt]
          have hwlt : w < lo.length := by omega
          have htake : ((lo.set w x).take (w + 1)) =
              (lo.take w) ++ [x] := take_set_succ lo w x hwlt
          have hZ' : (lo.set w x).take (w + 1) ++
              differenceOracle (la.drop (i + 1)) (lb.drop j) =
              Z ++ differenceOracle la lb := by
            have hZZ := hZ
            rw [hstep] at hZZ
            rw [htake, List.append_assoc, List.cons_append,
              List.nil_append]
            exact hZZ
          have hsorted1 : SortedSeg (lo.set w x) 0 (w + 1) :=
            sortedSeg_snoc lo 0 w x hsO
              (fun p _ hpk a ha =>
                hcrossA p hpk a ha i (Nat.le_refl _) hltA x hgetA)
              hwlt
          have hcrossA' : ∀ p, p < w + 1 → ∀ a,
              ((lo.set w x)[p]? : Option (BitVec 32)) = some a →
              ∀ q, i + 1 ≤ q → q < la.length → ∀ b, la[q]? = some b →
              (b.slt a) = false := by
            intro p hpw a ha q hiq hqm b hb
            by_cases hpk : p = w
            · rw [hpk] at ha
              have hax : a = x := by
                have hget := List.getElem?_set_self hwlt (a := x)
                rw [hget] at ha
                exact (Option.some_inj.mp ha).symm
              rw [hax]
              exact hsA i q (by omega) (by omega) (by omega) x b
                hgetA hb
            · have ha' : lo[p]? = some a := by
                have h1 : (((lo.set w x)[p]? : Option (BitVec 32))) =
                    lo[p]? := by
                  rw [List.getElem?_set_ne (show w ≠ p by omega)]
                rw [h1] at ha
                exact ha
              exact hcrossA p (by omega) a ha' q (by omega) hqm b hb
          have hcrossB' : ∀ p, p < w + 1 → ∀ a,
              ((lo.set w x)[p]? : Option (BitVec 32)) = some a →
              ∀ q, j ≤ q → q < lb.length → ∀ b, lb[q]? = some b →
              (b.slt a) = false := by
            intro p hpw a ha q hjq hqm b hb
            by_cases hpk : p = w
            · rw [hpk] at ha
              have hax : a = x := by
                have hget := List.getElem?_set_self hwlt (a := x)
                rw [hget] at ha
                exact (Option.some_inj.mp ha).symm
              rw [hax]
              by_cases heq : q = j
              · subst heq
                have hbyy : b = y := by
                  rw [hgetB] at hb
                  exact (Option.some_inj.mp hb).symm
                rw [hbyy]
                have hirr : (y.slt y) = false := by
                  have e : ¬ y.toInt < y.toInt := by omega
                  simpa [BitVec.slt_eq_decide] using e
                exact slt_lt_ge_trans hlt hirr
              · have hby : (b.slt y) = false :=
                  hsB j q (by omega) (by omega) (by omega) y b
                    hgetB hb
                exact slt_lt_ge_trans hlt hby
            · have ha' : lo[p]? = some a := by
                have h1 : (((lo.set w x)[p]? : Option (BitVec 32))) =
                    lo[p]? := by
                  rw [List.getElem?_set_ne (show w ≠ p by omega)]
                rw [h1] at ha
                exact ha
              exact hcrossB p (by omega) a ha' q hjq hqm b hb
          have hcap' : (w + 1) + (la.length - (i + 1)) ≤
              (lo.set w x).length := by
            rw [List.length_set]; omega
          obtain ⟨hcons, hsorted, hcapI, hcrossAfin, hcrossBfin⟩ :=
            ih (la := la) (lb := lb) (lo := (lo.set w x))
              (i := i + 1) (j := j) (w := w + 1) (Z := Z)
              (hsA := hsA) (hsB := hsB) (hsO := hsorted1)
              (hcrossA := hcrossA') (hcrossB := hcrossB')
              (hcap := hcap') (hZ := hZ') (hfwd := hfwd')
          exact ⟨hcons, hsorted, hcapI, hcrossAfin, hcrossBfin⟩
        · by_cases hgt : (y.slt x) = true
          · have hne : (x.slt y) = false := by
              cases hxy : x.slt y with
              | true => exact absurd hxy hlt
              | false => rfl
            have hfwd' : differenceMainFwd la lb lo G i (j + 1) w =
                .ok (i', j', w', lo') := by
              simpa [differenceMainFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hne, hgt] using hfwd
            have hstep : differenceOracle (la.drop i) (lb.drop j) =
                differenceOracle (la.drop i) (lb.drop (j + 1)) := by
              rw [hdropA, hdropB,
                differenceOracle_advRight _ _ _ _ hne hgt]
            have hZ' : lo.take w ++
                differenceOracle (la.drop i) (lb.drop (j + 1)) =
                Z ++ differenceOracle la lb := by
              have hZZ := hZ
              rw [hstep] at hZZ
              exact hZZ
            have hcrossB' : ∀ p, p < w → ∀ a, lo[p]? = some a →
                ∀ q, j + 1 ≤ q → q < lb.length → ∀ b, lb[q]? = some b →
                (b.slt a) = false := by
              intro p hpw a ha q hjq hqm b hb
              exact hcrossB p hpw a ha q (by omega) hqm b hb
            obtain ⟨hcons, hsorted, hcapI, hcrossAfin, hcrossBfin⟩ :=
              ih (la := la) (lb := lb) (lo := lo)
                (i := i) (j := j + 1) (w := w) (Z := Z)
                (hsA := hsA) (hsB := hsB) (hsO := hsO)
                (hcrossA := hcrossA) (hcrossB := hcrossB')
                (hcap := hcap) (hZ := hZ') (hfwd := hfwd')
            exact ⟨hcons, hsorted, hcapI, hcrossAfin, hcrossBfin⟩
          · have hge1 : (x.slt y) = false := by
              cases hxy : x.slt y with
              | true => exact absurd hxy hlt
              | false => rfl
            have hge2 : (y.slt x) = false := by
              cases hyx : y.slt x with
              | true => exact absurd hyx hgt
              | false => rfl
            have hfwd' : differenceMainFwd la lb lo G (i + 1) (j + 1) w =
                .ok (i', j', w', lo') := by
              simpa [differenceMainFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hge1, hge2] using hfwd
            have hstep : differenceOracle (la.drop i) (lb.drop j) =
                differenceOracle (la.drop (i + 1)) (lb.drop (j + 1)) := by
              rw [hdropA, hdropB,
                differenceOracle_skipBoth _ _ _ _ hge1 hge2]
            have hZ' : lo.take w ++
                differenceOracle (la.drop (i + 1)) (lb.drop (j + 1)) =
                Z ++ differenceOracle la lb := by
              have hZZ := hZ
              rw [hstep] at hZZ
              exact hZZ
            have hcrossA' : ∀ p, p < w → ∀ a, lo[p]? = some a →
                ∀ q, i + 1 ≤ q → q < la.length → ∀ b, la[q]? = some b →
                (b.slt a) = false := by
              intro p hpw a ha q hiq hqm b hb
              exact hcrossA p hpw a ha q (by omega) hqm b hb
            have hcrossB' : ∀ p, p < w → ∀ a, lo[p]? = some a →
                ∀ q, j + 1 ≤ q → q < lb.length → ∀ b, lb[q]? = some b →
                (b.slt a) = false := by
              intro p hpw a ha q hjq hqm b hb
              exact hcrossB p hpw a ha q (by omega) hqm b hb
            have hcap' : w + (la.length - (i + 1)) ≤ lo.length := by
              omega
            obtain ⟨hcons, hsorted, hcapI, hcrossAfin, hcrossBfin⟩ :=
              ih (la := la) (lb := lb) (lo := lo)
                (i := i + 1) (j := j + 1) (w := w) (Z := Z)
                (hsA := hsA) (hsB := hsB) (hsO := hsO)
                (hcrossA := hcrossA') (hcrossB := hcrossB')
                (hcap := hcap') (hZ := hZ') (hfwd := hfwd')
            exact ⟨hcons, hsorted, hcapI, hcrossAfin, hcrossBfin⟩
      · have hpair : (i, j, w, lo) = (i', j', w', lo') := by
          have hnegB : ¬ j < lb.length := by omega
          simpa [differenceMainFwd, dite_eq_left hltA,
            dite_eq_right hnegB] using hfwd
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
        exact ⟨hZ, hsO, hcap, hcrossA, hcrossB⟩
    · have hpair : (i, j, w, lo) = (i', j', w', lo') := by
        have hnegA : ¬ i < la.length := by omega
        simpa [differenceMainFwd, dite_eq_right hnegA] using hfwd
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
      exact ⟨hZ, hsO, hcap, hcrossA, hcrossB⟩

/-- Main-scan exhaustion: with exact fuel the scan runs until a
    cursor reaches its end. -/
theorem differenceMainFwd_exhausted (la lb lo : List (BitVec 32))
    (G i j w : Nat)
    (i' j' w' : Nat) (lo' : List (BitVec 32))
    (hile : i ≤ la.length) (hjle : j ≤ lb.length)
    (hF : (la.length - i) + (lb.length - j) ≤ G)
    (hfwd : differenceMainFwd la lb lo G i j w = .ok (i', j', w', lo')) :
    i' = la.length ∨ j' = lb.length := by
  induction G generalizing la lb lo i j w with
  | zero =>
    have hpair : (i, j, w, lo) = (i', j', w', lo') := by
      simpa [differenceMainFwd] using hfwd
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
    left; omega
  | succ G ih =>
    by_cases hltA : i < la.length
    · by_cases hltB : j < lb.length
      · obtain ⟨x, hgetA⟩ : ∃ x, la[i]? = some x :=
          ⟨_, List.getElem?_eq_getElem hltA⟩
        obtain ⟨y, hgetB⟩ : ∃ y, lb[j]? = some y :=
          ⟨_, List.getElem?_eq_getElem hltB⟩
        by_cases hlt : (x.slt y) = true
        · have hfwd' : differenceMainFwd la lb (lo.set w x) G (i + 1) j
              (w + 1) = .ok (i', j', w', lo') := by
            simpa [differenceMainFwd, dite_eq_left hltA, dite_eq_left hltB,
              hgetA, hgetB, hlt] using hfwd
          exact ih (la := la) (lb := lb) (lo := (lo.set w x))
            (i := i + 1) (j := j) (w := w + 1) (by omega) hjle
            (by omega) (hfwd := hfwd')
        · by_cases hgt : (y.slt x) = true
          · have hne : (x.slt y) = false := by
              cases hxy : x.slt y with
              | true => exact absurd hxy hlt
              | false => rfl
            have hfwd' : differenceMainFwd la lb lo G i (j + 1) w =
                .ok (i', j', w', lo') := by
              simpa [differenceMainFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hne, hgt] using hfwd
            exact ih (la := la) (lb := lb) (lo := lo)
              (i := i) (j := j + 1) (w := w) hile (by omega)
              (by omega) (hfwd := hfwd')
          · have hge1 : (x.slt y) = false := by
              cases hxy : x.slt y with
              | true => exact absurd hxy hlt
              | false => rfl
            have hge2 : (y.slt x) = false := by
              cases hyx : y.slt x with
              | true => exact absurd hyx hgt
              | false => rfl
            have hfwd' : differenceMainFwd la lb lo G (i + 1) (j + 1) w =
                .ok (i', j', w', lo') := by
              simpa [differenceMainFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hge1, hge2] using hfwd
            exact ih (la := la) (lb := lb) (lo := lo)
              (i := i + 1) (j := j + 1) (w := w) (by omega) (by omega)
              (by omega) (hfwd := hfwd')
      · have hpair : (i, j, w, lo) = (i', j', w', lo') := by
          have hnegB : ¬ j < lb.length := by omega
          simpa [differenceMainFwd, dite_eq_left hltA,
            dite_eq_right hnegB] using hfwd
        obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
        right; omega
    · have hpair : (i, j, w, lo) = (i', j', w', lo') := by
        have hnegA : ¬ i < la.length := by omega
        simpa [differenceMainFwd, dite_eq_right hnegA] using hfwd
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hpair
      left; omega

/-- Forward totality: every in-bounds index failure is guarded
    away, so the scan always succeeds with enough fuel. -/
theorem differenceMainFwd_noFail (la lb lo : List (BitVec 32))
    (G i j w : Nat)
    (hile : i ≤ la.length) (hjle : j ≤ lb.length)
    (hF : (la.length - i) + (lb.length - j) ≤ G) :
    ∃ i' j' w' lo',
      differenceMainFwd la lb lo G i j w = .ok (i', j', w', lo') := by
  induction G generalizing la lb lo i j w with
  | zero =>
    exact ⟨i, j, w, lo, by simp [differenceMainFwd]⟩
  | succ G ih =>
    by_cases hltA : i < la.length
    · by_cases hltB : j < lb.length
      · obtain ⟨x, hgetA⟩ : ∃ x, la[i]? = some x :=
          ⟨_, List.getElem?_eq_getElem hltA⟩
        obtain ⟨y, hgetB⟩ : ∃ y, lb[j]? = some y :=
          ⟨_, List.getElem?_eq_getElem hltB⟩
        by_cases hlt : (x.slt y) = true
        · have hstep : differenceMainFwd la lb lo (G + 1) i j w =
              differenceMainFwd la lb (lo.set w x) G (i + 1) j
                (w + 1) := by
            simp [differenceMainFwd, dite_eq_left hltA, dite_eq_left hltB,
              hgetA, hgetB, hlt]
          rw [hstep]
          exact ih (la := la) (lb := lb) (lo := (lo.set w x))
            (i := i + 1) (j := j) (w := w + 1) (by omega) hjle
            (by omega)
        · by_cases hgt : (y.slt x) = true
          · have hne : (x.slt y) = false := by
              cases hxy : x.slt y with
              | true => exact absurd hxy hlt
              | false => rfl
            have hstep : differenceMainFwd la lb lo (G + 1) i j w =
                differenceMainFwd la lb lo G i (j + 1) w := by
              simp [differenceMainFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hne, hgt]
            rw [hstep]
            exact ih (la := la) (lb := lb) (lo := lo)
              (i := i) (j := j + 1) (w := w) hile (by omega)
              (by omega)
          · have hge1 : (x.slt y) = false := by
              cases hxy : x.slt y with
              | true => exact absurd hxy hlt
              | false => rfl
            have hge2 : (y.slt x) = false := by
              cases hyx : y.slt x with
              | true => exact absurd hyx hgt
              | false => rfl
            have hstep : differenceMainFwd la lb lo (G + 1) i j w =
                differenceMainFwd la lb lo G (i + 1) (j + 1) w := by
              simp [differenceMainFwd, dite_eq_left hltA, dite_eq_left hltB,
                hgetA, hgetB, hge1, hge2]
            rw [hstep]
            exact ih (la := la) (lb := lb) (lo := lo)
              (i := i + 1) (j := j + 1) (w := w) (by omega) (by omega)
              (by omega)
      · exact ⟨i, j, w, lo, by
          have hnegB : ¬ j < lb.length := by omega
          simpa [differenceMainFwd, dite_eq_left hltA,
            dite_eq_right hnegB]⟩
    · exact ⟨i, j, w, lo, by
        have hnegA : ¬ i < la.length := by omega
        simpa [differenceMainFwd, dite_eq_right hnegA]⟩

/-- Drain conservation: copying the left survivor suffix
    appends exactly the remaining tail to the record. -/
theorem differenceDrainFwd_ok (la : List (BitVec 32)) (lo : List (BitVec 32))
    (G i w : Nat)
    (Z : List (BitVec 32)) (i' w' : Nat) (lo' : List (BitVec 32))
    (hsuf : SortedSeg la i la.length)
    (hsO : SortedSeg lo 0 w)
    (hcross : ∀ p, p < w → ∀ a, lo[p]? = some a →
      ∀ q, i ≤ q → q < la.length → ∀ b, la[q]? = some b →
      (b.slt a) = false)
    (hcap : w + (la.length - i) ≤ lo.length)
    (hZ : lo.take w ++ la.drop i = Z)
    (hfwd : differenceDrainFwd la lo G i w = .ok (i', w', lo')) :
    (lo'.take w' ++ la.drop i' = Z) ∧
    SortedSeg lo' 0 w' ∧
    w' + (la.length - i') ≤ lo'.length ∧
    (∀ p, p < w' → ∀ a, lo'[p]? = some a →
      ∀ q, i' ≤ q → q < la.length → ∀ b, la[q]? = some b →
      (b.slt a) = false) := by
  induction G generalizing la lo i w Z with
  | zero =>
    have hpair : (i, w, lo) = (i', w', lo') := by
      simpa [differenceDrainFwd] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    exact ⟨hZ, hsO, hcap, hcross⟩
  | succ G ih =>
    by_cases hltA : i < la.length
    · obtain ⟨x, hgetA⟩ : ∃ x, la[i]? = some x :=
        ⟨_, List.getElem?_eq_getElem hltA⟩
      have hdropA : la.drop i = x :: la.drop (i + 1) :=
        drop_cons_of_getElem? la i x hgetA
      have hfwd' : differenceDrainFwd la (lo.set w x) G (i + 1) (w + 1) =
          .ok (i', w', lo') := by
        simpa [differenceDrainFwd, dite_eq_left hltA, hgetA] using hfwd
      have hwlt : w < lo.length := by omega
      have htake : ((lo.set w x).take (w + 1)) =
          (lo.take w) ++ [x] := take_set_succ lo w x hwlt
      have hstep : lo.take w ++ la.drop i =
          ((lo.take w) ++ [x]) ++ la.drop (i + 1) := by
        rw [hdropA]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      have hZ' : (lo.set w x).take (w + 1) ++ la.drop (i + 1) = Z := by
        rw [htake, ← hstep]; exact hZ
      have hsorted1 : SortedSeg (lo.set w x) 0 (w + 1) :=
        sortedSeg_snoc lo 0 w x hsO
          (fun p _ hpk a ha =>
            hcross p hpk a ha i (Nat.le_refl _) hltA x hgetA)
          hwlt
      have hcross' : ∀ p, p < w + 1 → ∀ a,
          ((lo.set w x)[p]? : Option (BitVec 32)) = some a →
          ∀ q, i + 1 ≤ q → q < la.length → ∀ b, la[q]? = some b →
          (b.slt a) = false := by
        intro p hpw a ha q hiq hqm b hb
        by_cases hpk : p = w
        · rw [hpk] at ha
          have hax : a = x := by
            have hget := List.getElem?_set_self hwlt (a := x)
            rw [hget] at ha
            exact (Option.some_inj.mp ha).symm
          rw [hax]
          exact hsuf i q (by omega) (by omega) (by omega) x b
            hgetA hb
        · have ha' : lo[p]? = some a := by
            have h1 : (((lo.set w x)[p]? : Option (BitVec 32))) =
                lo[p]? := by
              rw [List.getElem?_set_ne (show w ≠ p by omega)]
            rw [h1] at ha
            exact ha
          exact hcross p (by omega) a ha' q (by omega) hqm b hb
      have hcap' : (w + 1) + (la.length - (i + 1)) ≤
          (lo.set w x).length := by
        rw [List.length_set]; omega
      have hsuf' : SortedSeg la (i + 1) la.length := by
        intro p q hpq1 hpq2 hpq3 a b ha hb
        exact hsuf p q (by omega) hpq2 hpq3 a b ha hb
      obtain ⟨hcons, hsorted, hcapI, hcrossFin⟩ :=
        ih (la := la) (lo := (lo.set w x))
          (i := i + 1) (w := w + 1) (Z := Z)
          (hsuf := hsuf') (hsO := hsorted1)
          (hcross := hcross') (hcap := hcap') (hZ := hZ')
          (hfwd := hfwd')
      exact ⟨hcons, hsorted, hcapI, hcrossFin⟩
    · have hpair : (i, w, lo) = (i', w', lo') := by
        have hnegA : ¬ i < la.length := by omega
        simpa [differenceDrainFwd, dite_eq_right hnegA] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      exact ⟨hZ, hsO, hcap, hcross⟩

/-- Drain totality: with fuel covering the survivor suffix, the
    copy always succeeds. -/
theorem differenceDrainFwd_noFail (la : List (BitVec 32))
    (lo : List (BitVec 32)) (G i w : Nat)
    (hF : la.length - i ≤ G) :
    ∃ i' w' lo',
      differenceDrainFwd la lo G i w = .ok (i', w', lo') := by
  induction G generalizing la lo i w with
  | zero =>
    exact ⟨i, w, lo, by simp [differenceDrainFwd]⟩
  | succ G ih =>
    by_cases hltA : i < la.length
    · obtain ⟨x, hgetA⟩ : ∃ x, la[i]? = some x :=
        ⟨_, List.getElem?_eq_getElem hltA⟩
      have hstep : differenceDrainFwd la lo (G + 1) i w =
          differenceDrainFwd la (lo.set w x) G (i + 1) (w + 1) := by
        simp [differenceDrainFwd, dite_eq_left hltA, hgetA]
      rw [hstep]
      exact ih (la := la) (lo := (lo.set w x))
        (i := i + 1) (w := w + 1) (by omega)
    · exact ⟨i, w, lo, by
        have hnegA : ¬ i < la.length := by omega
        simpa [differenceDrainFwd, dite_eq_right hnegA]⟩

/-- Drain exhaustion: with exact fuel the copy runs the survivor
    suffix to its end. -/
theorem differenceDrainFwd_exhausted (la : List (BitVec 32))
    (lo : List (BitVec 32)) (G i w : Nat)
    (i' w' : Nat) (lo' : List (BitVec 32))
    (hile : i ≤ la.length)
    (hF : la.length - i ≤ G)
    (hfwd : differenceDrainFwd la lo G i w = .ok (i', w', lo')) :
    i' = la.length := by
  induction G generalizing la lo i w with
  | zero =>
    have hpair : (i, w, lo) = (i', w', lo') := by
      simpa [differenceDrainFwd] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    omega
  | succ G ih =>
    by_cases hltA : i < la.length
    · obtain ⟨x, hgetA⟩ : ∃ x, la[i]? = some x :=
        ⟨_, List.getElem?_eq_getElem hltA⟩
      have hfwd' : differenceDrainFwd la (lo.set w x) G (i + 1) (w + 1) =
          .ok (i', w', lo') := by
        simpa [differenceDrainFwd, dite_eq_left hltA, hgetA] using hfwd
      exact ih (la := la) (lo := (lo.set w x))
        (i := i + 1) (w := w + 1) (by omega) (by omega)
        (hfwd := hfwd')
    · have hpair : (i, w, lo) = (i', w', lo') := by
        have hnegA : ¬ i < la.length := by omega
        simpa [differenceDrainFwd, dite_eq_right hnegA] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      omega

/-- Whole-function forward correctness: from sorted inputs and a
    caller-sized record (`a.size()` slots), the main-plus-drain
    scan records exactly the difference oracle, stays sorted,
    and reports its length. The two forward runs are hypotheses
    (the entries and the transfer feed the same runs, so no
    determinism argument is needed). No drain-`b`: leftover
    right elements are never recorded. -/
theorem vecDifferenceFwd_correct (la lb : List (BitVec 32))
    (lo : List (BitVec 32))
    (hsA : SortedSeg la 0 la.length) (hsB : SortedSeg lb 0 lb.length)
    (hcap0 : la.length ≤ lo.length)
    (i j w : Nat) (lo₁ : List (BitVec 32))
    (i₂ w₂ : Nat) (lo₂ : List (BitVec 32))
    (hfwdM : differenceMainFwd la lb lo (la.length + lb.length + 1) 0 0 0 =
      .ok (i, j, w, lo₁))
    (hfwdA : differenceDrainFwd la lo₁ (la.length - i) i w =
      .ok (i₂, w₂, lo₂)) :
    (lo₂.take w₂ = differenceOracle la lb) ∧
    SortedSeg lo₂ 0 w₂ ∧
    w₂ = (differenceOracle la lb).length := by
  have hZ0 : (lo.take 0) ++ differenceOracle (la.drop 0) (lb.drop 0) =
      [] ++ differenceOracle la lb := by simp
  have hsO0 : SortedSeg lo 0 0 := by
    intro p hlo hpq hqk a b ha hb
    have hfalse : False := by omega
    exact hfalse.elim
  have hcrossA0 : ∀ p, p < 0 → ∀ a, lo[p]? = some a →
      ∀ q, 0 ≤ q → q < la.length → ∀ b, la[q]? = some b →
      (b.slt a) = false := by
    intro p hp
    have hfalse : False := by omega
    exact hfalse.elim
  have hcrossB0 : ∀ p, p < 0 → ∀ a, lo[p]? = some a →
      ∀ q, 0 ≤ q → q < lb.length → ∀ b, lb[q]? = some b →
      (b.slt a) = false := by
    intro p hp
    have hfalse : False := by omega
    exact hfalse.elim
  have hcap : 0 + (la.length - 0) ≤ lo.length := by
    simpa using hcap0
  obtain ⟨hconsM, hsortedM, hcapM, hcrossA1, hcrossB1⟩ :=
    differenceMainFwd_ok la lb lo (la.length + lb.length + 1) 0 0 0 [] i j
      w lo₁ hsA hsB hsO0 hcrossA0 hcrossB0 hcap hZ0 hfwdM
  obtain ⟨hi_le, hj_le, hw_le, hlenM⟩ :=
    differenceMainFwd_le la lb (la.length + lb.length + 1) 0 0 0 lo i j w
      lo₁ (by omega) (by omega) hcap hfwdM
  obtain hexh := differenceMainFwd_exhausted la lb lo
    (la.length + lb.length + 1) 0 0 0 i j w lo₁ (by omega) (by omega)
    (by omega) hfwdM
  have hsufA : SortedSeg la i la.length := by
    intro p q hpq1 hpq2 hpq3 a b ha hb
    exact hsA p q (by omega) hpq2 hpq3 a b ha hb
  have hcapA0 : w + (la.length - i) ≤ lo₁.length := by omega
  obtain ⟨hconsA, hsortedA, hcapA, hcrossA2⟩ :=
    differenceDrainFwd_ok la lo₁ (la.length - i) i w
      (lo₁.take w ++ la.drop i) i₂ w₂ lo₂
      hsufA hsortedM hcrossA1 hcapA0 rfl hfwdA
  obtain ⟨hi_le1, hw_le1, hlenA⟩ :=
    differenceDrainFwd_le la (la.length - i) i w lo₁ i₂ w₂ lo₂
      hi_le hcapA0 hfwdA
  have hexhA := differenceDrainFwd_exhausted la lo₁ (la.length - i) i w
    i₂ w₂ lo₂ hi_le (by omega) hfwdA
  have hw₂le : w₂ ≤ lo₂.length := by omega
  have hwle : w ≤ lo₁.length := by omega
  -- Chain the two conservations: the drain appends the left
  -- survivor suffix to the main-scan record.
  have htakeA : lo₂.take w₂ = lo₁.take w ++ la.drop i := by
    have h := hconsA
    rw [hexhA, List.drop_length, List.append_nil] at h
    exact h
  have hfin : lo₂.take w₂ = differenceOracle la lb := by
    have hM := hconsM
    rw [List.nil_append] at hM
    -- hM : lo₁.take w ++ differenceOracle (la.drop i) (lb.drop j) = differenceOracle la lb
    rcases hexh with hAi | hBj
    · rw [hAi, List.drop_length] at hM
      -- oracle of ([], drop j) is empty
      have hor : differenceOracle [] (lb.drop j) = [] := by
        simp [differenceOracle]
      rw [hor, List.append_nil] at hM
      rw [htakeA, hAi, List.drop_length, List.append_nil]
      exact hM
    · rw [hBj, List.drop_length] at hM
      have hor : differenceOracle (la.drop i) [] = la.drop i := by
        cases e : la.drop i with
        | nil => simp [differenceOracle, e]
        | cons x xs => simp [differenceOracle, e]
      rw [hor] at hM
      rw [htakeA]
      exact hM
  have hcnt : w₂ = (differenceOracle la lb).length := by
    have htake : (lo₂.take w₂).length = w₂ := by
      rw [List.length_take]
      have := hcapA
      omega
    rw [← htake, hfin]
  exact ⟨hfin, hsortedA, hcnt⟩

/-! ## P2-M12: out-of-place filter (`copy_if`) forward contract -/

/-- Filter forward totality, ok leg: the scan runs to
    `la.length` with full reads and fitting writes (fuel
    induction threading the keep count and the capacity
    bound). -/
theorem copyIfFwd_ok (x : BitVec 32) (la lo : List (BitVec 32))
    (fuel r w : Nat)
    (hle : r ≤ la.length)
    (hF : la.length - r ≤ fuel)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hwcnt : ((la.take r).filter (fun y => (y != x))).length = w)
    (hcap : (la.filter (fun y => (y != x))).length ≤ lo.length) :
    ∃ w' lo', copyIfFwd x la lo fuel r w = .ok (la.length, w', lo') := by
  induction fuel generalizing lo r w with
  | zero =>
    have him : r = la.length := by omega
    subst him
    exact ⟨w, lo, by simp [copyIfFwd]⟩
  | succ n ih =>
    by_cases hlt : r < la.length
    · obtain ⟨y, hy⟩ := hread r hlt
      by_cases hkeep : (y != x) = true
      · have hkeeps1 : (((la.take (r + 1)).filter
            (fun z => (z != x))).length = w + 1) := by
          rw [copyIfFilter_take_succ x la r y hy hkeep, hwcnt]
        have hwlt : w < lo.length := by
          have hsplit := copyIfFilter_split x la r (by omega)
          omega
        obtain ⟨wOld, hwget⟩ : ∃ z, lo[w]? = some z :=
          ⟨lo[w], List.getElem?_eq_getElem hwlt⟩
        have hF' : la.length - (r + 1) ≤ n := by omega
        have hwcnt' : (((la.take (r + 1)).filter
            (fun z => (z != x))).length = w + 1) := hkeeps1
        have hcap' : (la.filter (fun y => (y != x))).length ≤
            (lo.set w y).length := by
          have hlen : (lo.set w y).length = lo.length := by
            simp [List.length_set]
          rw [hlen]; exact hcap
        obtain ⟨w', lo', h⟩ := ih (lo := lo.set w y)
          (r := r + 1) (w := w + 1)
          (hle := by omega) (hF := hF')
          (hwcnt := hwcnt') (hcap := hcap')
        exact ⟨w', lo', by
          simp only [copyIfFwd, dite_eq_left hlt, hy, hkeep, hwget]
          exact h⟩
      · have hdrop : (y != x) = false := by
          cases h : (y != x) with
          | true => exact absurd h hkeep
          | false => rfl
        have hwcnt' : (((la.take (r + 1)).filter
            (fun z => (z != x))).length = w) := by
          rw [copyIfFilter_take_succ_drop x la r y hy hdrop, hwcnt]
        have hF' : la.length - (r + 1) ≤ n := by omega
        obtain ⟨w', lo', h⟩ := ih (lo := lo)
          (r := r + 1) (w := w)
          (hle := by omega) (hF := hF')
          (hwcnt := hwcnt') (hcap := hcap)
        exact ⟨w', lo', by
          simp only [copyIfFwd, dite_eq_left hlt, hy, hdrop]
          exact h⟩
    · have him : r = la.length := by omega
      subst him
      exact ⟨w, lo, by simp [copyIfFwd]⟩

/-- Filter forward prefix contract, ok leg: the written prefix
    is the filter of the scanned prefix, the count never
    retreats, the output length is unchanged (fuel induction
    threading the prefix, suffix, keep-count, and capacity
    facts — the M9 `removeFwd_prefix` shape on the `out`
    list). -/
theorem copyIfFwd_prefix (x : BitVec 32) (la lo₀ : List (BitVec 32))
    (fuel r w w' : Nat) (lo lo' : List (BitVec 32))
    (hle : r ≤ la.length)
    (hF : la.length - r ≤ fuel)
    (hlen : lo.length = lo₀.length)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hwcnt : ((la.take r).filter (fun y => (y != x))).length = w)
    (hcap : (la.filter (fun y => (y != x))).length ≤ lo₀.length)
    (hpre : lo.take w = ((la.take r).filter (fun y => (y != x))))
    (hsuf : ∀ j, w ≤ j → lo[j]? = lo₀[j]?)
    (hfwd : copyIfFwd x la lo fuel r w = .ok (la.length, w', lo')) :
    lo'.take w' = la.filter (fun y => (y != x)) ∧
      w ≤ w' ∧ lo'.length = lo₀.length := by
  induction fuel generalizing lo r w with
  | zero =>
    have hpair : (r, w, lo) = (la.length, w', lo') := by
      simpa [copyIfFwd] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    refine ⟨?_, Nat.le_refl _, hlen⟩
    rw [List.take_length] at hpre
    exact hpre
  | succ n ih =>
    by_cases hlt : r < la.length
    · obtain ⟨y, hy⟩ := hread r hlt
      by_cases hkeep : (y != x) = true
      · have hkeeps1 : (((la.take (r + 1)).filter
            (fun z => (z != x))).length = w + 1) := by
          rw [copyIfFilter_take_succ x la r y hy hkeep, hwcnt]
        have hwlt : w < lo.length := by
          have hsplit := copyIfFilter_split x la r (by omega)
          have hcap' : (la.filter (fun y => (y != x))).length ≤
              lo.length := by
            rw [hlen]; exact hcap
          omega
        have hwget : lo[w]? = some lo[w] :=
          List.getElem?_eq_getElem hwlt
        have hF' : la.length - (r + 1) ≤ n := by omega
        have hlen' : (lo.set w y).length = lo₀.length := by
          simp [List.length_set, hlen]
        have hwcnt' : (((la.take (r + 1)).filter
            (fun z => (z != x))).length = w + 1) := hkeeps1
        have hcap' : (la.filter (fun y => (y != x))).length ≤
            lo₀.length := hcap
        have hpre' : (lo.set w y).take (w + 1) =
            ((la.take (r + 1)).filter (fun y => (y != x))) := by
          have htake : (lo.set w y).take (w + 1) =
              lo.take w ++ [y] := by
            have htakeW : (lo.set w y).take w = lo.take w := by
              apply List.ext_getElem?
              intro j
              rw [List.getElem?_take, List.getElem?_take]
              by_cases hj : j < w
              · rw [List.getElem?_set_ne (show w ≠ j by omega)]
              · simp [hj]
            rw [List.take_add_one,
              List.getElem?_set_self (by omega : w < lo.length),
              htakeW]; rfl
          have hfilter : ((la.take (r + 1)).filter
              (fun z => (z != x))) =
              (la.take r).filter (fun z => (z != x)) ++ [y] := by
            have htake₀ : la.take (r + 1) = la.take r ++ [y] := by
              have h0 : la.take (r + 1) = la.take r ++ la[r]?.toList :=
                List.take_add_one
              have h1 : la[r]?.toList = [y] := by rw [hy]; rfl
              rwa [h1] at h0
            rw [htake₀, List.filter_append]
            simp [hkeep]
          rw [htake, hfilter, hpre]
        have hsuf' : ∀ j, w + 1 ≤ j → (lo.set w y)[j]? = lo₀[j]? := by
          intro j hj
          rw [List.getElem?_set_ne (show w ≠ j by omega)]
          exact hsuf j (by omega)
        have hfwd' : copyIfFwd x la (lo.set w y) n (r + 1) (w + 1) =
            .ok (la.length, w', lo') := by
          have h := hfwd
          simp only [copyIfFwd, dite_eq_left hlt, hy, hkeep, hwget] at h
          exact h
        obtain ⟨hA, hB, hC⟩ := ih (lo := lo.set w y)
          (r := r + 1) (w := w + 1)
          (hle := by omega) (hF := hF') (hlen := hlen')
          (hwcnt := hwcnt')
          (hpre := hpre') (hsuf := hsuf')
          (hfwd := hfwd')
        exact ⟨hA, by omega, hC⟩
      · have hdrop : (y != x) = false := by
          cases h : (y != x) with
          | true => exact absurd h hkeep
          | false => rfl
        have hwcnt' : (((la.take (r + 1)).filter
            (fun z => (z != x))).length = w) := by
          rw [copyIfFilter_take_succ_drop x la r y hy hdrop, hwcnt]
        have hF' : la.length - (r + 1) ≤ n := by omega
        have hpre' : lo.take w =
            ((la.take (r + 1)).filter (fun y => (y != x))) := by
          rw [copyIfFilter_take_succ_drop x la r y hy hdrop]
          exact hpre
        have hfwd' : copyIfFwd x la lo n (r + 1) w =
            .ok (la.length, w', lo') := by
          have h := hfwd
          simp only [copyIfFwd, dite_eq_left hlt, hy, hdrop] at h
          exact h
        obtain ⟨hA, hB, hC⟩ := ih (lo := lo)
          (r := r + 1) (w := w)
          (hle := by omega) (hF := hF') (hlen := hlen)
          (hwcnt := hwcnt')
          (hpre := hpre') (hsuf := hsuf)
          (hfwd := hfwd')
        exact ⟨hA, by omega, hC⟩
    · have him : r = la.length := by omega
      subst him
      have hpair : (la.length, w, lo) = (la.length, w', lo') := by
        cases n with
        | zero => simpa [copyIfFwd] using hfwd
        | succ n =>
          have hneg : ¬ la.length < la.length := by omega
          simpa [copyIfFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      refine ⟨?_, Nat.le_refl _, hlen⟩
      rw [List.take_length] at hpre
      exact hpre

/-- Filter forward short-`out` error leg: when the keeps so
    far fit but the total keeps overflow the output, the scan
    fails loudly (fuel induction threading the keep count;
    the zero/exhausted cases are discharged by the count
    facts). -/
theorem copyIfFwd_err_short (x : BitVec 32) (la lo : List (BitVec 32))
    (fuel r w : Nat)
    (hle : r ≤ la.length)
    (hF : la.length - r ≤ fuel)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hwcnt : ((la.take r).filter (fun y => (y != x))).length = w)
    (hwle : w ≤ lo.length)
    (hmore : lo.length < (la.filter (fun y => (y != x))).length) :
    copyIfFwd x la lo fuel r w = .error .AssertFail := by
  induction fuel generalizing lo r w with
  | zero =>
    have him : r = la.length := by omega
    subst him
    rw [List.take_length] at hwcnt
    omega
  | succ n ih =>
    by_cases hlt : r < la.length
    · obtain ⟨y, hy⟩ := hread r hlt
      by_cases hkeep : (y != x) = true
      · by_cases hmiss : lo[w]? = none
        · simpa [copyIfFwd, dite_eq_left hlt, hy, hkeep, hmiss]
        · have hsome : ∃ z, lo[w]? = some z := by
            match h : lo[w]? with
            | none => exact absurd h hmiss
            | some z => exact ⟨z, rfl⟩
          obtain ⟨wOld, hwget⟩ := hsome
          have hwlt : w < lo.length := by
            have hne : w ≠ lo.length := by
              intro heq
              subst heq
              have hnone : lo[lo.length]? = none :=
                List.getElem?_eq_none (Nat.le_refl _)
              rw [hnone] at hwget
              simp at hwget
            exact Nat.lt_of_le_of_ne hwle hne
          have hF' : la.length - (r + 1) ≤ n := by omega
          have hwcnt' : (((la.take (r + 1)).filter
              (fun z => (z != x))).length = w + 1) := by
            rw [copyIfFilter_take_succ x la r y hy hkeep, hwcnt]
          have hwle' : w + 1 ≤ (lo.set w y).length := by
            have hlen : (lo.set w y).length = lo.length := by
              simp [List.length_set]
            omega
          have hmore' : (lo.set w y).length <
              (la.filter (fun y => (y != x))).length := by
            have hlen : (lo.set w y).length = lo.length := by
              simp [List.length_set]
            rw [hlen]; exact hmore
          have h := ih (lo := lo.set w y)
            (r := r + 1) (w := w + 1)
            (hle := by omega) (hF := hF')
            (hwcnt := hwcnt') (hwle := hwle') (hmore := hmore')
          simpa [copyIfFwd, dite_eq_left hlt, hy, hkeep, hwget] using h
      · have hdrop : (y != x) = false := by
          cases h : (y != x) with
          | true => exact absurd h hkeep
          | false => rfl
        have hwcnt' : (((la.take (r + 1)).filter
            (fun z => (z != x))).length = w) := by
          rw [copyIfFilter_take_succ_drop x la r y hy hdrop, hwcnt]
        have hF' : la.length - (r + 1) ≤ n := by omega
        have h := ih (lo := lo)
          (r := r + 1) (w := w)
          (hle := by omega) (hF := hF')
          (hwcnt := hwcnt') (hwle := hwle) (hmore := hmore)
        simpa [copyIfFwd, dite_eq_left hlt, hy, hdrop] using h
    · have him : r = la.length := by omega
      subst him
      rw [List.take_length] at hwcnt
      omega

/-- Short-`out` fires loudly from the entry: more keeps than
    output words means the forward scan errors. -/
theorem copyIfFwd_err_of_overflow (x : BitVec 32)
    (la lo : List (BitVec 32))
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hmore : lo.length < (la.filter (fun y => (y != x))).length) :
    copyIfFwd x la lo la.length 0 0 = .error .AssertFail :=
  copyIfFwd_err_short x la lo la.length 0 0 (Nat.zero_le _)
    (by omega) hread (by simp) (Nat.zero_le _) hmore

/-- Count bound: the survivor count never exceeds the output
    length while the scan fits (fuel induction threading the
    keep count and the capacity bound — the ok-leg write
    rule). -/
theorem copyIfFwd_le (x : BitVec 32) (la lo : List (BitVec 32))
    (fuel r w w' : Nat) (lo' : List (BitVec 32))
    (hle : r ≤ la.length)
    (hF : la.length - r ≤ fuel)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hwcnt : ((la.take r).filter (fun y => (y != x))).length = w)
    (hcap : (la.filter (fun y => (y != x))).length ≤ lo.length)
    (hfwd : copyIfFwd x la lo fuel r w = .ok (la.length, w', lo')) :
    w' ≤ lo.length := by
  induction fuel generalizing lo r w with
  | zero =>
    have him : r = la.length := by omega
    subst him
    have hpair : (la.length, w, lo) = (la.length, w', lo') := by
      simpa [copyIfFwd] using hfwd
    obtain ⟨rfl, rfl, rfl⟩ := hpair
    rw [List.take_length] at hwcnt
    omega
  | succ n ih =>
    by_cases hlt : r < la.length
    · obtain ⟨y, hy⟩ := hread r hlt
      by_cases hkeep : (y != x) = true
      · have hkeeps1 : (((la.take (r + 1)).filter
            (fun z => (z != x))).length = w + 1) := by
          rw [copyIfFilter_take_succ x la r y hy hkeep, hwcnt]
        have hwlt : w < lo.length := by
          have hsplit := copyIfFilter_split x la r (by omega)
          omega
        obtain ⟨wOld, hwget⟩ : ∃ z, lo[w]? = some z :=
          ⟨lo[w], List.getElem?_eq_getElem hwlt⟩
        have hF' : la.length - (r + 1) ≤ n := by omega
        have hwcnt' : (((la.take (r + 1)).filter
            (fun z => (z != x))).length = w + 1) := hkeeps1
        have hcap' : (la.filter (fun y => (y != x))).length ≤
            (lo.set w y).length := by
          have hlen : (lo.set w y).length = lo.length := by
            simp [List.length_set]
          rw [hlen]; exact hcap
        have hfwd' : copyIfFwd x la (lo.set w y) n (r + 1) (w + 1) =
            .ok (la.length, w', lo') := by
          have h := hfwd
          simp only [copyIfFwd, dite_eq_left hlt, hy, hkeep, hwget] at h
          exact h
        have h := ih (lo := lo.set w y)
          (r := r + 1) (w := w + 1)
          (hle := by omega) (hF := hF')
          (hwcnt := hwcnt') (hcap := hcap')
          (hfwd := hfwd')
        have hlen : (lo.set w y).length = lo.length := by
          simp [List.length_set]
        omega
      · have hdrop : (y != x) = false := by
          cases h : (y != x) with
          | true => exact absurd h hkeep
          | false => rfl
        have hwcnt' : (((la.take (r + 1)).filter
            (fun z => (z != x))).length = w) := by
          rw [copyIfFilter_take_succ_drop x la r y hy hdrop, hwcnt]
        have hF' : la.length - (r + 1) ≤ n := by omega
        have hfwd' : copyIfFwd x la lo n (r + 1) w =
            .ok (la.length, w', lo') := by
          have h := hfwd
          simp only [copyIfFwd, dite_eq_left hlt, hy, hdrop] at h
          exact h
        exact ih (lo := lo)
          (r := r + 1) (w := w)
          (hle := by omega) (hF := hF')
          (hwcnt := hwcnt') (hcap := hcap)
          (hfwd := hfwd')
    · have him : r = la.length := by omega
      subst him
      have hpair : (la.length, w, lo) = (la.length, w', lo') := by
        cases n with
        | zero => simpa [copyIfFwd] using hfwd
        | succ n =>
          have hneg : ¬ la.length < la.length := by omega
          simpa [copyIfFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl, rfl⟩ := hpair
      rw [List.take_length] at hwcnt
      omega

/-- Closed copy_if contract: when the keeps fit, the forward
    returns the filter count over the filter prefix, output
    length unchanged. -/
theorem vecCopyIfFwd_correct (x : BitVec 32)
    (la lo : List (BitVec 32))
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hcap : (la.filter (fun y => (y != x))).length ≤ lo.length) :
    ∃ (w' : Nat) (lo' : List (BitVec 32)),
      vecCopyIfFwd la lo x = .ok (.u64 (BitVec.ofNat 64 w')) ∧
      lo'.take w' = la.filter (fun y => (y != x)) ∧
      w' = (la.filter (fun y => (y != x))).length ∧
      lo'.length = lo.length := by
  obtain ⟨w', lo', hfwd⟩ := copyIfFwd_ok x la lo la.length 0 0
    (Nat.zero_le _) (by omega) hread (by simp) hcap
  obtain ⟨hpref, hle, hlen⟩ := copyIfFwd_prefix x la lo la.length 0 0 w'
    lo lo' (Nat.zero_le _) (by omega) rfl hread (by simp) hcap
    (by simp) (fun j _ => rfl) hfwd
  have hb := copyIfFwd_le x la lo la.length 0 0 w' lo'
    (Nat.zero_le _) (by omega) hread (by simp) hcap hfwd
  refine ⟨w', lo', by simp only [vecCopyIfFwd, hfwd], hpref, ?_, hlen⟩
  have htw : (lo'.take w').length = w' := by
    rw [List.length_take, Nat.min_eq_left (by omega : w' ≤ lo'.length)]
  have hflen : (lo'.take w').length =
      (la.filter (fun y => (y != x))).length := by rw [hpref]
  omega

/-! ## Dual-record partition (`partition_copy`) forward contract -/

/-- Partition forward totality, ok leg: the scan runs to
    `la.length` with full reads and fitting writes on both
    records (fuel induction threading both keep counts and
    both capacity bounds). -/
theorem partitionCopyFwd_ok (pivot : BitVec 32)
    (la yes no : List (BitVec 32))
    (fuel r wYes wNo : Nat)
    (hle : r ≤ la.length)
    (hF : la.length - r ≤ fuel)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hwcntYes : ((la.take r).filter (fun z => z.slt pivot)).length
      = wYes)
    (hwcntNo : ((la.take r).filter
      (fun z => !(z.slt pivot))).length = wNo)
    (hcapYes : (la.filter (fun y => y.slt pivot)).length ≤ yes.length)
    (hcapNo : (la.filter (fun y => !(y.slt pivot))).length
      ≤ no.length) :
    ∃ wYes' wNo' yes' no',
      partitionCopyFwd pivot la yes no fuel r wYes wNo =
        .ok (la.length, wYes', wNo', yes', no') ∧
      ((la.take la.length).filter (fun z => z.slt pivot)).length
        = wYes' ∧
      ((la.take la.length).filter
        (fun z => !(z.slt pivot))).length = wNo' := by
  induction fuel generalizing yes no r wYes wNo with
  | zero =>
    have him : r = la.length := by omega
    subst him
    exact ⟨wYes, wNo, yes, no, by simp [partitionCopyFwd],
      hwcntYes, hwcntNo⟩
  | succ n ih =>
    by_cases hlt : r < la.length
    · obtain ⟨y, hy⟩ := hread r hlt
      by_cases hkeep : (y.slt pivot) = true
      · have hstepY :=
          partFilterYes_take_succ pivot la r y hy hkeep
        have hkeeps1 := congrArg List.length hstepY
        rw [List.length_append, hwcntYes,
          List.length_singleton] at hkeeps1
        have hwlt : wYes < yes.length := by
          have hsplit := partFilterYes_split pivot la r (by omega)
          omega
        obtain ⟨wOld, hwget⟩ : ∃ z, yes[wYes]? = some z :=
          ⟨yes[wYes], List.getElem?_eq_getElem hwlt⟩
        have hF' : la.length - (r + 1) ≤ n := by omega
        have hwcntYes' := hkeeps1
        have hdropNo : (!(y.slt pivot)) = false := by
          simp [hkeep]
        have hstepNo :=
          partFilterNo_take_succ_drop pivot la r y hy hdropNo
        have hwcntNo' := congrArg List.length hstepNo
        rw [hwcntNo] at hwcntNo'
        have hlenS : (yes.set wYes y).length = yes.length := by
          simp [List.length_set]
        have hcapYes' : (la.filter (fun y => y.slt pivot)).length ≤
            (yes.set wYes y).length := by
          rw [hlenS]; exact hcapYes
        obtain ⟨wYes', wNo', yes', no', h, hcntYes, hcntNo⟩ :=
          ih (yes := yes.set wYes y)
            (r := r + 1) (wYes := wYes + 1) (wNo := wNo)
            (hle := by omega) (hF := hF')
            (hwcntYes := hwcntYes') (hwcntNo := hwcntNo')
            (hcapYes := hcapYes') (hcapNo := hcapNo)
        exact ⟨wYes', wNo', yes', no', by
          simp only [partitionCopyFwd, dite_eq_left hlt, hy, hkeep,
            hwget]
          exact h, hcntYes, hcntNo⟩
      · have hdrop : (y.slt pivot) = false := by
          cases h : (y.slt pivot) with
          | true => exact absurd h hkeep
          | false => rfl
        have hkeepNo : (!(y.slt pivot)) = true := by simp [hdrop]
        have hstepN :=
          partFilterNo_take_succ pivot la r y hy hkeepNo
        have hkeeps1 := congrArg List.length hstepN
        rw [List.length_append, hwcntNo,
          List.length_singleton] at hkeeps1
        have hwlt : wNo < no.length := by
          have hsplit := partFilterNo_split pivot la r (by omega)
          omega
        obtain ⟨wOld, hwget⟩ : ∃ z, no[wNo]? = some z :=
          ⟨no[wNo], List.getElem?_eq_getElem hwlt⟩
        have hF' : la.length - (r + 1) ≤ n := by omega
        have hwcntNo' := hkeeps1
        have hstepY :=
          partFilterYes_take_succ_drop pivot la r y hy hdrop
        have hwcntYes' := congrArg List.length hstepY
        rw [hwcntYes] at hwcntYes'
        have hlenS : (no.set wNo y).length = no.length := by
          simp [List.length_set]
        have hcapNo' : (la.filter (fun y => !(y.slt pivot))).length ≤
            (no.set wNo y).length := by
          rw [hlenS]; exact hcapNo
        obtain ⟨wYes', wNo', yes', no', h, hcntYes, hcntNo⟩ :=
          ih (no := no.set wNo y)
            (r := r + 1) (wYes := wYes) (wNo := wNo + 1)
            (hle := by omega) (hF := hF')
            (hwcntYes := hwcntYes') (hwcntNo := hwcntNo')
            (hcapYes := hcapYes) (hcapNo := hcapNo')
        exact ⟨wYes', wNo', yes', no', by
          simp only [partitionCopyFwd, dite_eq_left hlt, hy, hdrop,
            hwget]
          exact h, hcntYes, hcntNo⟩
    · have him : r = la.length := by omega
      subst him
      exact ⟨wYes, wNo, yes, no, by simp [partitionCopyFwd],
        hwcntYes, hwcntNo⟩

/-- Partition forward prefix contract, ok leg: both written
    prefixes are the filters of the scanned prefix, neither
    count retreats, both record lengths are unchanged (fuel
    induction threading both prefixes, suffixes, keep-counts
    and capacity facts). -/
theorem partitionCopyFwd_prefix (pivot : BitVec 32)
    (la yes₀ no₀ : List (BitVec 32))
    (fuel r wYes wNo wYes' wNo' : Nat)
    (yes no yes' no' : List (BitVec 32))
    (hle : r ≤ la.length)
    (hF : la.length - r ≤ fuel)
    (hlenYes : yes.length = yes₀.length)
    (hlenNo : no.length = no₀.length)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hwcntYes : ((la.take r).filter (fun z => z.slt pivot)).length
      = wYes)
    (hwcntNo : ((la.take r).filter
      (fun z => !(z.slt pivot))).length = wNo)
    (hcapYes : (la.filter (fun y => y.slt pivot)).length
      ≤ yes₀.length)
    (hcapNo : (la.filter (fun y => !(y.slt pivot))).length
      ≤ no₀.length)
    (hpreYes : yes.take wYes =
      ((la.take r).filter (fun z => z.slt pivot)))
    (hpreNo : no.take wNo =
      ((la.take r).filter (fun z => !(z.slt pivot))))
    (hsufYes : ∀ j, wYes ≤ j → yes[j]? = yes₀[j]?)
    (hsufNo : ∀ j, wNo ≤ j → no[j]? = no₀[j]?)
    (hfwd : partitionCopyFwd pivot la yes no fuel r wYes wNo =
      .ok (la.length, wYes', wNo', yes', no')) :
    yes'.take wYes' = la.filter (fun y => y.slt pivot) ∧
      no'.take wNo' = la.filter (fun y => !(y.slt pivot)) ∧
      wYes ≤ wYes' ∧ wNo ≤ wNo' ∧
      yes'.length = yes₀.length ∧ no'.length = no₀.length := by
  induction fuel generalizing yes no r wYes wNo with
  | zero =>
    have hpair : (r, wYes, wNo, yes, no) =
        (la.length, wYes', wNo', yes', no') := by
      simpa [partitionCopyFwd] using hfwd
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hpair
    refine ⟨?_, ?_, Nat.le_refl _, Nat.le_refl _, hlenYes,
      hlenNo⟩
    · rw [List.take_length] at hpreYes
      exact hpreYes
    · rw [List.take_length] at hpreNo
      exact hpreNo
  | succ n ih =>
    by_cases hlt : r < la.length
    · obtain ⟨y, hy⟩ := hread r hlt
      by_cases hkeep : (y.slt pivot) = true
      · have hstepY :=
          partFilterYes_take_succ pivot la r y hy hkeep
        have hkeeps1 := congrArg List.length hstepY
        rw [List.length_append, hwcntYes,
          List.length_singleton] at hkeeps1
        have hwlt : wYes < yes.length := by
          have hsplit := partFilterYes_split pivot la r (by omega)
          have hcapYes' : (la.filter
              (fun y => y.slt pivot)).length ≤ yes.length := by
            rw [hlenYes]; exact hcapYes
          omega
        have hwget : yes[wYes]? = some yes[wYes] :=
          List.getElem?_eq_getElem hwlt
        have hF' : la.length - (r + 1) ≤ n := by omega
        have hlenYes' : (yes.set wYes y).length = yes₀.length := by
          simp [List.length_set, hlenYes]
        have hwcntYes' := hkeeps1
        have hdropNo : (!(y.slt pivot)) = false := by
          simp [hkeep]
        have hstepNo :=
          partFilterNo_take_succ_drop pivot la r y hy hdropNo
        have hwcntNo' := congrArg List.length hstepNo
        rw [hwcntNo] at hwcntNo'
        have hpreYes' : (yes.set wYes y).take (wYes + 1) =
            ((la.take (r + 1)).filter
              (fun z => z.slt pivot)) := by
          rw [take_set_succ_self yes wYes y hwlt, hpreYes, hstepY]
        have hpreNo' : no.take wNo =
            ((la.take (r + 1)).filter
              (fun z => !(z.slt pivot))) := by
          rw [partFilterNo_take_succ_drop pivot la r y hy hdropNo,
            hpreNo]
        have hsufYes' : ∀ j, wYes + 1 ≤ j →
            (yes.set wYes y)[j]? = yes₀[j]? := by
          intro j hj
          rw [List.getElem?_set_ne (show wYes ≠ j by omega)]
          exact hsufYes j (by omega)
        have hfwd' : partitionCopyFwd pivot la (yes.set wYes y)
            no n (r + 1) (wYes + 1) wNo =
            .ok (la.length, wYes', wNo', yes', no') := by
          have h := hfwd
          simp only [partitionCopyFwd, dite_eq_left hlt, hy,
            hkeep, hwget] at h
          exact h
        obtain ⟨hprefYes, hprefNo, hleW, hleN, hlenY, hlenN⟩ :=
          ih (yes := yes.set wYes y) (no := no)
            (r := r + 1) (wYes := wYes + 1) (wNo := wNo)
            (hle := by omega) (hF := hF')
            (hlenYes := hlenYes') (hlenNo := hlenNo)
            (hwcntYes := hwcntYes') (hwcntNo := hwcntNo')
            (hpreYes := hpreYes') (hpreNo := hpreNo')
            (hsufYes := hsufYes') (hsufNo := hsufNo)
            (hfwd := hfwd')
        exact ⟨hprefYes, hprefNo, by omega, by omega, hlenY,
          hlenN⟩
      · have hdrop : (y.slt pivot) = false := by
          cases h : (y.slt pivot) with
          | true => exact absurd h hkeep
          | false => rfl
        have hkeepNo : (!(y.slt pivot)) = true := by simp [hdrop]
        have hstepN :=
          partFilterNo_take_succ pivot la r y hy hkeepNo
        have hkeeps1 := congrArg List.length hstepN
        rw [List.length_append, hwcntNo,
          List.length_singleton] at hkeeps1
        have hwlt : wNo < no.length := by
          have hsplit := partFilterNo_split pivot la r (by omega)
          have hcapNo' : (la.filter
              (fun y => !(y.slt pivot))).length ≤ no.length := by
            rw [hlenNo]; exact hcapNo
          omega
        have hwget : no[wNo]? = some no[wNo] :=
          List.getElem?_eq_getElem hwlt
        have hF' : la.length - (r + 1) ≤ n := by omega
        have hlenNo' : (no.set wNo y).length = no₀.length := by
          simp [List.length_set, hlenNo]
        have hwcntNo' := hkeeps1
        have hstepY :=
          partFilterYes_take_succ_drop pivot la r y hy hdrop
        have hwcntYes' := congrArg List.length hstepY
        rw [hwcntYes] at hwcntYes'
        have hpreNo' : (no.set wNo y).take (wNo + 1) =
            ((la.take (r + 1)).filter
              (fun z => !(z.slt pivot))) := by
          rw [take_set_succ_self no wNo y hwlt, hpreNo, hstepN]
        have hpreYes' : yes.take wYes =
            ((la.take (r + 1)).filter
              (fun z => z.slt pivot)) := by
          rw [partFilterYes_take_succ_drop pivot la r y hy hdrop,
            hpreYes]
        have hsufNo' : ∀ j, wNo + 1 ≤ j →
            (no.set wNo y)[j]? = no₀[j]? := by
          intro j hj
          rw [List.getElem?_set_ne (show wNo ≠ j by omega)]
          exact hsufNo j (by omega)
        have hfwd' : partitionCopyFwd pivot la yes
            (no.set wNo y) n (r + 1) wYes (wNo + 1) =
            .ok (la.length, wYes', wNo', yes', no') := by
          have h := hfwd
          simp only [partitionCopyFwd, dite_eq_left hlt, hy,
            hdrop, hwget] at h
          exact h
        obtain ⟨hprefYes, hprefNo, hleW, hleN, hlenY, hlenN⟩ :=
          ih (yes := yes) (no := no.set wNo y)
            (r := r + 1) (wYes := wYes) (wNo := wNo + 1)
            (hle := by omega) (hF := hF')
            (hlenYes := hlenYes) (hlenNo := hlenNo')
            (hwcntYes := hwcntYes') (hwcntNo := hwcntNo')
            (hpreYes := hpreYes') (hpreNo := hpreNo')
            (hsufYes := hsufYes) (hsufNo := hsufNo')
            (hfwd := hfwd')
        exact ⟨hprefYes, hprefNo, by omega, by omega, hlenY,
          hlenN⟩
    · have him : r = la.length := by omega
      subst him
      have hpair : (la.length, wYes, wNo, yes, no) =
          (la.length, wYes', wNo', yes', no') := by
        cases n with
        | zero => simpa [partitionCopyFwd] using hfwd
        | succ n =>
          have hneg : ¬ la.length < la.length := by omega
          simpa [partitionCopyFwd, dite_eq_right hneg] using hfwd
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hpair
      refine ⟨?_, ?_, Nat.le_refl _, Nat.le_refl _, hlenYes,
        hlenNo⟩
      · rw [List.take_length] at hpreYes
        exact hpreYes
      · rw [List.take_length] at hpreNo
        exact hpreNo

/-- Partition forward short-`yes` error leg: when the scanned
    prefix fits but the total keepers overflow the `yes`
    record, the scan fails loud (fuel induction; the `no`
    side needs no capacity facts — a `no` miss fails loud
    directly, a hit threads untouched). -/
theorem partitionCopyFwd_err_shortYes (pivot : BitVec 32)
    (la yes no : List (BitVec 32))
    (fuel r wYes wNo : Nat)
    (hle : r ≤ la.length)
    (hF : la.length - r ≤ fuel)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hwcntYes : ((la.take r).filter (fun z => z.slt pivot)).length
      = wYes)
    (hwcntNo : ((la.take r).filter
      (fun z => !(z.slt pivot))).length = wNo)
    (hwloYes : wYes ≤ yes.length)
    (hmoreYes : yes.length <
      (la.filter (fun y => y.slt pivot)).length) :
    partitionCopyFwd pivot la yes no fuel r wYes wNo =
      .error .AssertFail := by
  induction fuel generalizing yes no r wYes wNo with
  | zero =>
    have him : r = la.length := by omega
    subst him
    have htakeL : la.take la.length = la := List.take_length
    rw [htakeL] at hwcntYes
    omega
  | succ n ih =>
    by_cases hlt : r < la.length
    · obtain ⟨y, hy⟩ := hread r hlt
      by_cases hkeep : (y.slt pivot) = true
      · by_cases hmiss : yes[wYes]? = none
        · simp [partitionCopyFwd, dite_eq_left hlt, hy, hkeep,
            hmiss]
        · have hsome : ∃ z, yes[wYes]? = some z := by
            match h : yes[wYes]? with
            | none => exact absurd h hmiss
            | some z => exact ⟨z, rfl⟩
          obtain ⟨wOld, hwget⟩ := hsome
          have hwltYes : wYes < yes.length :=
            transformRead_lt yes wYes wOld hwget
          have hstepY :=
            partFilterYes_take_succ pivot la r y hy hkeep
          have hkeeps1 := congrArg List.length hstepY
          rw [List.length_append, hwcntYes,
            List.length_singleton] at hkeeps1
          have hwcntYes' := hkeeps1
          have hdropNo : (!(y.slt pivot)) = false := by
            simp [hkeep]
          have hstepNo :=
            partFilterNo_take_succ_drop pivot la r y hy hdropNo
          have hwcntNo' := congrArg List.length hstepNo
          rw [hwcntNo] at hwcntNo'
          have hlenS : (yes.set wYes y).length = yes.length := by
            simp [List.length_set]
          have hwloYes' : wYes + 1 ≤ (yes.set wYes y).length := by
            omega
          have hmoreYes' : (yes.set wYes y).length <
              (la.filter (fun y => y.slt pivot)).length := by
            rw [hlenS]; exact hmoreYes
          have hF' : la.length - (r + 1) ≤ n := by omega
          have h := ih (yes := yes.set wYes y) (no := no)
            (r := r + 1) (wYes := wYes + 1) (wNo := wNo)
            (hle := by omega) (hF := hF')
            (hwcntYes := hwcntYes') (hwcntNo := hwcntNo')
            (hwloYes := hwloYes') (hmoreYes := hmoreYes')
          simpa [partitionCopyFwd, dite_eq_left hlt, hy, hkeep,
            hwget] using h
      · have hdrop : (y.slt pivot) = false := by
          cases h : (y.slt pivot) with
          | true => exact absurd h hkeep
          | false => rfl
        by_cases hmiss : no[wNo]? = none
        · simp [partitionCopyFwd, dite_eq_left hlt, hy, hdrop,
            hmiss]
        · have hsome : ∃ z, no[wNo]? = some z := by
            match h : no[wNo]? with
            | none => exact absurd h hmiss
            | some z => exact ⟨z, rfl⟩
          obtain ⟨wOld, hwget⟩ := hsome
          have hkeepNo : (!(y.slt pivot)) = true := by
            simp [hdrop]
          have hstepN :=
            partFilterNo_take_succ pivot la r y hy hkeepNo
          have hkeeps1 := congrArg List.length hstepN
          rw [List.length_append, hwcntNo,
            List.length_singleton] at hkeeps1
          have hwcntNo' := hkeeps1
          have hstepY :=
            partFilterYes_take_succ_drop pivot la r y hy hdrop
          have hwcntYes' := congrArg List.length hstepY
          rw [hwcntYes] at hwcntYes'
          have hF' : la.length - (r + 1) ≤ n := by omega
          have h := ih (yes := yes) (no := no.set wNo y)
            (r := r + 1) (wYes := wYes) (wNo := wNo + 1)
            (hle := by omega) (hF := hF')
            (hwcntYes := hwcntYes') (hwcntNo := hwcntNo')
            (hwloYes := hwloYes) (hmoreYes := hmoreYes)
          simpa [partitionCopyFwd, dite_eq_left hlt, hy, hdrop,
            hwget] using h
    · have him : r = la.length := by omega
      subst him
      have htakeL : la.take la.length = la := List.take_length
      rw [htakeL] at hwcntYes
      omega

/-- Partition forward short-`no` error leg: mirror image —
    when the total droppers overflow the `no` record, the
    scan fails loud. -/
theorem partitionCopyFwd_err_shortNo (pivot : BitVec 32)
    (la yes no : List (BitVec 32))
    (fuel r wYes wNo : Nat)
    (hle : r ≤ la.length)
    (hF : la.length - r ≤ fuel)
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hwcntYes : ((la.take r).filter (fun z => z.slt pivot)).length
      = wYes)
    (hwcntNo : ((la.take r).filter
      (fun z => !(z.slt pivot))).length = wNo)
    (hwloNo : wNo ≤ no.length)
    (hmoreNo : no.length <
      (la.filter (fun y => !(y.slt pivot))).length) :
    partitionCopyFwd pivot la yes no fuel r wYes wNo =
      .error .AssertFail := by
  induction fuel generalizing yes no r wYes wNo with
  | zero =>
    have him : r = la.length := by omega
    subst him
    have htakeL : la.take la.length = la := List.take_length
    rw [htakeL] at hwcntNo
    omega
  | succ n ih =>
    by_cases hlt : r < la.length
    · obtain ⟨y, hy⟩ := hread r hlt
      by_cases hkeep : (y.slt pivot) = true
      · by_cases hmiss : yes[wYes]? = none
        · simp [partitionCopyFwd, dite_eq_left hlt, hy, hkeep,
            hmiss]
        · have hsome : ∃ z, yes[wYes]? = some z := by
            match h : yes[wYes]? with
            | none => exact absurd h hmiss
            | some z => exact ⟨z, rfl⟩
          obtain ⟨wOld, hwget⟩ := hsome
          have hstepY :=
            partFilterYes_take_succ pivot la r y hy hkeep
          have hkeeps1 := congrArg List.length hstepY
          rw [List.length_append, hwcntYes,
            List.length_singleton] at hkeeps1
          have hwcntYes' := hkeeps1
          have hdropNo : (!(y.slt pivot)) = false := by
            simp [hkeep]
          have hstepNo :=
            partFilterNo_take_succ_drop pivot la r y hy hdropNo
          have hwcntNo' := congrArg List.length hstepNo
          rw [hwcntNo] at hwcntNo'
          have hlenS : (yes.set wYes y).length = yes.length := by
            simp [List.length_set]
          have hF' : la.length - (r + 1) ≤ n := by omega
          have h := ih (yes := yes.set wYes y) (no := no)
            (r := r + 1) (wYes := wYes + 1) (wNo := wNo)
            (hle := by omega) (hF := hF')
            (hwcntYes := hwcntYes') (hwcntNo := hwcntNo')
            (hwloNo := hwloNo) (hmoreNo := hmoreNo)
          simpa [partitionCopyFwd, dite_eq_left hlt, hy, hkeep,
            hwget] using h
      · have hdrop : (y.slt pivot) = false := by
          cases h : (y.slt pivot) with
          | true => exact absurd h hkeep
          | false => rfl
        by_cases hmiss : no[wNo]? = none
        · simp [partitionCopyFwd, dite_eq_left hlt, hy, hdrop,
            hmiss]
        · have hsome : ∃ z, no[wNo]? = some z := by
            match h : no[wNo]? with
            | none => exact absurd h hmiss
            | some z => exact ⟨z, rfl⟩
          obtain ⟨wOld, hwget⟩ := hsome
          have hwltNo : wNo < no.length :=
            transformRead_lt no wNo wOld hwget
          have hkeepNo : (!(y.slt pivot)) = true := by
            simp [hdrop]
          have hstepN :=
            partFilterNo_take_succ pivot la r y hy hkeepNo
          have hkeeps1 := congrArg List.length hstepN
          rw [List.length_append, hwcntNo,
            List.length_singleton] at hkeeps1
          have hwcntNo' := hkeeps1
          have hstepY :=
            partFilterYes_take_succ_drop pivot la r y hy hdrop
          have hwcntYes' := congrArg List.length hstepY
          rw [hwcntYes] at hwcntYes'
          have hlenS : (no.set wNo y).length = no.length := by
            simp [List.length_set]
          have hwloNo' : wNo + 1 ≤ (no.set wNo y).length := by
            omega
          have hmoreNo' : (no.set wNo y).length <
              (la.filter (fun y => !(y.slt pivot))).length := by
            rw [hlenS]; exact hmoreNo
          have hF' : la.length - (r + 1) ≤ n := by omega
          have h := ih (yes := yes) (no := no.set wNo y)
            (r := r + 1) (wYes := wYes) (wNo := wNo + 1)
            (hle := by omega) (hF := hF')
            (hwcntYes := hwcntYes') (hwcntNo := hwcntNo')
            (hwloNo := hwloNo') (hmoreNo := hmoreNo')
          simpa [partitionCopyFwd, dite_eq_left hlt, hy, hdrop,
            hwget] using h
    · have him : r = la.length := by omega
      subst him
      have htakeL : la.take la.length = la := List.take_length
      rw [htakeL] at hwcntNo
      omega

/-- Short `yes` record fires loudly from the entry state. -/
theorem partitionCopyFwd_err_of_yes_short (pivot : BitVec 32)
    (la yes no : List (BitVec 32))
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hmoreYes : yes.length <
      (la.filter (fun y => y.slt pivot)).length) :
    partitionCopyFwd pivot la yes no la.length 0 0 0 =
      .error .AssertFail :=
  partitionCopyFwd_err_shortYes pivot la yes no la.length 0 0 0
    (Nat.zero_le _) (Nat.le_refl _)
    hread (by simp) (by simp) (Nat.zero_le _) hmoreYes

/-- Short `no` record fires loudly from the entry state. -/
theorem partitionCopyFwd_err_of_no_short (pivot : BitVec 32)
    (la yes no : List (BitVec 32))
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hmoreNo : no.length <
      (la.filter (fun y => !(y.slt pivot))).length) :
    partitionCopyFwd pivot la yes no la.length 0 0 0 =
      .error .AssertFail :=
  partitionCopyFwd_err_shortNo pivot la yes no la.length 0 0 0
    (Nat.zero_le _) (Nat.le_refl _)
    hread (by simp) (by simp) (Nat.zero_le _) hmoreNo

/-- Closed dual-record partition contract: when both records
    fit, the forward returns the keeper count over the keeper
    prefix and the dropper prefix, both record lengths
    unchanged. -/
theorem vecPartitionCopyFwd_correct (pivot : BitVec 32)
    (la yes no : List (BitVec 32))
    (hread : ∀ p, p < la.length → ∃ y, la[p]? = some y)
    (hcapYes : (la.filter (fun y => y.slt pivot)).length
      ≤ yes.length)
    (hcapNo : (la.filter (fun y => !(y.slt pivot))).length
      ≤ no.length) :
    ∃ (wYes' : Nat) (wNo' : Nat) (yes' no' : List (BitVec 32)),
      vecPartitionCopyFwd la yes no pivot =
        .ok (.u64 (BitVec.ofNat 64 wYes')) ∧
      yes'.take wYes' = la.filter (fun y => y.slt pivot) ∧
      no'.take wNo' = la.filter (fun y => !(y.slt pivot)) ∧
      wYes' = (la.filter (fun y => y.slt pivot)).length ∧
      wNo' = (la.filter (fun y => !(y.slt pivot))).length ∧
      yes'.length = yes.length ∧ no'.length = no.length := by
  obtain ⟨wYes', wNo', yes', no', hfwd, hcntYes, hcntNo⟩ :=
    partitionCopyFwd_ok pivot la yes no la.length 0 0 0
      (Nat.zero_le _) (Nat.le_refl _) hread (by simp) (by simp)
      hcapYes hcapNo
  obtain ⟨hprefYes, hprefNo, -, -, hlenYes, hlenNo⟩ :=
    partitionCopyFwd_prefix pivot la yes no la.length 0 0 0
      wYes' wNo' yes no yes' no' (Nat.zero_le _) (Nat.le_refl _)
      rfl rfl hread (by simp) (by simp) hcapYes hcapNo
      (by simp) (by simp) (fun j _ => rfl) (fun j _ => rfl) hfwd
  rw [List.take_length] at hcntYes hcntNo
  refine ⟨wYes', wNo', yes', no', ?_, hprefYes, hprefNo,
    hcntYes.symm, hcntNo.symm, hlenYes, hlenNo⟩
  simp only [vecPartitionCopyFwd, hfwd]

/-! ## P2-M19: first-difference query (`vec_mismatch`) oracle contract -/

/-- Below the first difference, reads agree (as `getElem?`): the
    scan only reports the first position where the heads differ. -/
theorem firstDiff_mem_eq (la lb : List (BitVec 32)) (k : Nat)
    (hk : k < firstDiff la lb) : la[k]? = lb[k]? := by
  induction la generalizing lb k with
  | nil =>
    rw [firstDiff_nil_left] at hk
    omega
  | cons x xs ih =>
    cases lb with
    | nil =>
      rw [firstDiff_nil_right] at hk
      omega
    | cons y ys =>
      rw [firstDiff_cons] at hk
      by_cases hne : x != y
      · rw [ite_eq_left hne] at hk
        omega
      · rw [ite_eq_right hne] at hk
        cases k with
        | zero =>
          have hxy : x = y :=
            Classical.byContradiction (fun h => hne (bne_iff_ne.mpr h))
          subst hxy
          rfl
        | succ j =>
          simp only [List.getElem?_cons_succ]
          exact ih ys j (by omega)

/-- The first-difference position is either an exhaustion side or a
    genuine unequal pair at that position. -/
theorem firstDiff_first (la lb : List (BitVec 32)) :
    firstDiff la lb = la.length ∨ firstDiff la lb = lb.length ∨
      (∃ x y, la[firstDiff la lb]? = some x ∧
        lb[firstDiff la lb]? = some y ∧ x ≠ y) := by
  induction la generalizing lb with
  | nil =>
    rw [firstDiff_nil_left]
    exact Or.inl rfl
  | cons x xs ih =>
    cases lb with
    | nil =>
      rw [firstDiff_nil_right]
      exact Or.inr (Or.inl rfl)
    | cons y ys =>
      by_cases hne : x != y
      · rw [firstDiff_cons, ite_eq_left hne]
        exact Or.inr (Or.inr ⟨x, y, rfl, rfl, bne_iff_ne.mp hne⟩)
      · have heq : firstDiff (x :: xs) (y :: ys) =
            firstDiff xs ys + 1 := by
          rw [firstDiff_cons, ite_eq_right hne]
          omega
        rw [heq]
        cases ih ys with
        | inl h =>
          refine Or.inl ?_
          simp only [List.length_cons] at h ⊢
          omega
        | inr h =>
          cases h with
          | inl h =>
            refine Or.inr (Or.inl ?_)
            simp only [List.length_cons] at h ⊢
            omega
          | inr h =>
            refine Or.inr (Or.inr ?_)
            obtain ⟨x', y', hx', hy', hne'⟩ := h
            refine ⟨x', y', ?_, ?_, hne'⟩
            · simp only [List.getElem?_cons_succ]
              exact hx'
            · simp only [List.getElem?_cons_succ]
              exact hy'
