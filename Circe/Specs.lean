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
    map lemmas). -/
theorem addCaller_correct_ok (x y z t r : BitVec 32)
    (h1 : checkedAddI32 x y = .ok t) (h2 : checkedAddI32 t z = .ok r) :
    addCallerFwd x y z = .ok (.i32 r) := by
  simp only [addCallerFwd, h1, h2] <;> cir_simp

/-- First-add failure propagates (and determines the error). -/
theorem addCaller_correct_err (x y z : BitVec 32) (e : Panic)
    (h : checkedAddI32 x y = .error e) :
    addCallerFwd x y z = .error e := by
  simp only [addCallerFwd, h] <;> cir_simp

/-- `sum_caller` delegates: in-range lengths deliver the taken-prefix
    sum (`cir_simp` discharges the delegation rewrite — the spec —
    leaving exactly `sum_correct`). -/
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
    under `simp`; cf. `accAddFwd_ok` usage in `Circe.Emit.Acc`). -/
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
