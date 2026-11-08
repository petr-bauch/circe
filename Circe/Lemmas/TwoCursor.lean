/-
Circe.Lemmas.TwoCursor — U3 two-cursor compaction pack.

The one repeated shape across the compacting slices (P2-M9 remove,
P2-M13 unique): closing the survivor count from a pinned prefix.
Both `evalProgFunc_vecRemove_spec` and
`evalProgFunc_vecUnique_spec` proved the same `take`-length chain
inline — `List.length_take` plus a `Nat.min_eq_left` discharge —
before rewriting with the slice prefix equation. That chain now
lives here once, as `take_length_of_le`, with the full
prefix-to-count step as `squeeze_length_eq`. The squeeze oracle
itself (`dedupAdj` plus its boundary lemmas, including the
`snoc_keep`/`snoc_drop` steps for the `list_unique` chase)
lives here too, shared by the `vec_unique` forward contract and
the `list_unique` invariant.

Design notes (read before extending):
- Bounds side-goals (`w' ≤ l'.length`) stay at the call site —
  each slice already holds the bound from its `*_bounds` lemma,
  so the pack takes it as a hypothesis instead of rediscovering
  it (CheckedIx precedent: `by omega` with the invariant in
  context is already the automation).
- Seed arithmetic (`1 ≤ (x :: xs).length`) and per-step cursor
  facts (`w + 1 ≤ r + 1`) stay `by simp` / `by omega` at the
  call site for the same reason: one-liners, no shared shape.
-/

/-- Take prefixes preserve the count they are bounded by: taking
    `w` words of a list with at least `w` words yields `w`
    words. The `length_take` + `min_eq_left` chain shared by the
    remove/unique closings. -/
theorem take_length_of_le (l : List α) (w : Nat)
    (h : w ≤ l.length) :
    (l.take w).length = w := by
  rw [List.length_take, Nat.min_eq_left h]

/-- Survivor-count closing for two-cursor compactions: when the
    `w'`-prefix of the final words is the oracle squeeze, the
    returned count is the oracle length. Instantiated with
    `filter` (remove) and `dedupAdj` (unique) prefixes. -/
theorem squeeze_length_eq (l' oracle : List α) (w' : Nat)
    (hpre : l'.take w' = oracle)
    (hle : w' ≤ l'.length) :
    w' = oracle.length := by
  have h1 := take_length_of_le l' w' hle
  rw [← h1, hpre]

/-! ## The squeeze oracle (`dedupAdj`) - moved here from
    `Circe.Specs` (P3-N pack consolidation): the oracle is
    shared by the `vec_unique` forward contract and the
    `list_unique` chase invariant, so it lives in the
    compaction pack both import. -/

/-- Adjacent-duplicate oracle: keep the first element of each
    equal run (insert-first-of-run recursion). -/
def dedupAdj : List (BitVec 32) → List (BitVec 32)
  | [] => []
  | [x] => [x]
  | x :: y :: rest =>
    if x != y then x :: dedupAdj (y :: rest)
    else dedupAdj (y :: rest)

/-- One-step unfolding of the oracle on a two-element head. -/
theorem dedupAdj_cons_cons (x y : BitVec 32)
    (rest : List (BitVec 32)) :
    dedupAdj (x :: y :: rest)
      = if x != y then x :: dedupAdj (y :: rest)
        else dedupAdj (y :: rest) := rfl

/-- A false `bne` test is equality (the upper-bound-flip
    direction of the keep test). -/
theorem bne_eq_false_eq {x y : BitVec 32}
    (h : (x != y) = false) : x = y := by
  have hbeq : (x == y) = true := by
    have h1 : (!(x == y)) = false := by simpa [bne_eq] using h
    simpa using h1
  exact beq_iff_eq.mp hbeq

/-- The oracle never squeezes a nonempty list to nothing. -/
theorem dedupAdj_nonempty {D : List (BitVec 32)} (h : D ≠ []) :
    dedupAdj D ≠ [] := by
  cases D with
  | nil => exact absurd rfl h
  | cons x xs =>
    cases xs with
    | nil => simp [dedupAdj]
    | cons z zs =>
      simp only [dedupAdj]
      by_cases hxz : (x != z) = true
      · simp [hxz]
      · have hne : (x != z) = false := eq_false_of_ne_true hxz
        simp only [hne, if_false]
        exact dedupAdj_nonempty (by simp)

/-- Squeeze-then-append: squeezing `D ++ [y]` keeps the squeezed
    prefix and appends `y` iff it differs from the last survivor
    (an empty squeeze appends unconditionally). -/
theorem dedupAdj_append_single (D : List (BitVec 32)) (y : BitVec 32) :
    dedupAdj (D ++ [y]) =
      match (dedupAdj D).getLast? with
      | none => [y]
      | some p => if y != p then dedupAdj D ++ [y] else dedupAdj D := by
  induction D with
  | nil => simp [dedupAdj]
  | cons x xs ih =>
    cases xs with
    | nil =>
      simp only [List.cons_append, List.nil_append, dedupAdj]
      by_cases h : (x != y) = true
      · have h' : (y != x) = true := by rw [bne_comm]; exact h
        simp [h, h']
      · have hf : (x != y) = false := Bool.eq_false_of_ne_true h
        have h'f : (y != x) = false := by rw [bne_comm]; exact hf
        have hxy : x = y := bne_eq_false_eq hf
        subst hxy
        simp [hf, h'f]
    | cons z zs =>
      by_cases hxz : (x != z) = true
      · have hne : dedupAdj (z :: zs) ≠ [] :=
          dedupAdj_nonempty (by simp)
        have hlast : ((x :: dedupAdj (z :: zs)).getLast?
            = (dedupAdj (z :: zs)).getLast?) :=
          List.getLast?_cons_of_ne_nil hne
        have e : dedupAdj ((x :: z :: zs) ++ [y])
            = x :: dedupAdj ((z :: zs) ++ [y]) := by
          have n1 : (x :: z :: zs) ++ [y]
              = x :: z :: (zs ++ [y]) := by simp
          rw [n1, dedupAdj_cons_cons, ite_eq_left hxz,
            List.cons_append]
        have eR : dedupAdj (x :: z :: zs)
            = x :: dedupAdj (z :: zs) := by
          rw [dedupAdj_cons_cons, ite_eq_left hxz]
        rw [e, eR, hlast, ih]
        cases hD : (dedupAdj (z :: zs)).getLast? with
        | none =>
          exact absurd (List.getLast?_eq_none_iff.mp hD) hne
        | some p =>
          by_cases h : (y != p) = true <;> simp [h]
      · have hne : (x != z) = false := Bool.eq_false_of_ne_true hxz
        have hnc : ¬ (x != z) = true := by
          intro h
          rw [h] at hne
          exact Bool.noConfusion hne
        have e : dedupAdj ((x :: z :: zs) ++ [y])
            = dedupAdj ((z :: zs) ++ [y]) := by
          have n1 : (x :: z :: zs) ++ [y]
              = x :: z :: (zs ++ [y]) := by simp
          rw [n1, dedupAdj_cons_cons, ite_eq_right hnc,
            List.cons_append]
        have eR : dedupAdj (x :: z :: zs)
            = dedupAdj (z :: zs) := by
          rw [dedupAdj_cons_cons, ite_eq_right hnc]
        rw [e, eR, ih]

/-- Squeeze snoc, keep leg (P1-unique boundary): appending a
    value that differs from the last survivor extends the
    squeeze. The `getLast?` match in `dedupAdj_append_single`
    is discharged by the caller's last-kept fact. -/
theorem dedupAdj_snoc_keep (D : List (BitVec 32)) (y p : BitVec 32)
    (hlast : (dedupAdj D).getLast? = some p)
    (hne : (y != p) = true) :
    dedupAdj (D ++ [y]) = dedupAdj D ++ [y] := by
  rw [dedupAdj_append_single, hlast]
  simp [hne]

/-- Squeeze snoc, drop leg (P1-unique boundary): appending a
    value equal to the last survivor leaves the squeeze
    unchanged. -/
theorem dedupAdj_snoc_drop (D : List (BitVec 32)) (y p : BitVec 32)
    (hlast : (dedupAdj D).getLast? = some p)
    (heq : (y != p) = false) :
    dedupAdj (D ++ [y]) = dedupAdj D := by
  rw [dedupAdj_append_single, hlast]
  simp [heq]

