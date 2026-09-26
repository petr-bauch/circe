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
    `free` is value-invisible (contents kept, token set); missing-`free`
    strictness lives in `validate`, not here. -/
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
