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
