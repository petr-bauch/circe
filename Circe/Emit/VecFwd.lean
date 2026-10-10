/-
Circe.Emit.VecFwd — M1 heap-family program translations (value level).

Canonical home of the loop/entry definitions the M1 goldens render and
the `DiffVec*` fuzzers execute: fill/sum/copy loops + whole-program
entries (`vecFillSumU32`, `vecFillSumU64`, `vecReallocFillSumU32`) with
their dedicated supporting lemmas and spec bridges. Names are unchanged
from their former `Circe.Base` home; only the address moved (Base keeps
the evaluator vocabulary: block types + `vecNew/vecSet/vecGet/vecFree`
ops, which `Eval`/`Mem` themselves call). Proofs of the emitted CoreIR
entries (`emit_correct_vec*`, `memTransfer_*`) stay in their fragment
modules and import this module.
-/
import Circe.Base
import Circe.Emit.SumFwd

/-! ## Fill/sum loops + whole-program entry (`vec_alloc`, u32) -/

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

/-! ## Fill/sum loops + whole-program entry (`vec_alloc_u64`, u64) -/

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

/-! ## Realloc entry (`vec_realloc`, u32) -/

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

/-! ## Realloc whole-program bridge (spec world) -/

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
