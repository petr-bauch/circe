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

/-- The running prefix's last element is the predecessor read:
    from `l[w - 1]? = some p`, the taken prefix ends in `p`.
    Moved here from `Circe.Specs` (P2-M16 pack consolidation):
    the out-of-place squeeze invariant reads its predecessor
    from the record prefix, and Emit cannot import Specs. -/
theorem take_getLast_of_getElem? (l : List (BitVec 32)) (w : Nat)
    (p : BitVec 32)
    (hw : 0 < w) (hle : w ≤ l.length)
    (h : l[w - 1]? = some p) :
    (l.take w).getLast? = some p := by
  have htakenN : (l.take w).length = w := by
    rw [List.length_take, Nat.min_eq_left hle]
  have hprevTaken : (l.take w)[w - 1]? = some p := by
    rw [List.getElem?_take_of_lt (by omega : w - 1 < w)]
    exact h
  rw [List.getLast?_eq_getElem?, htakenN]
  exact hprevTaken

/-- Squeeze prefix step, keep leg (P2-M16 boundary): scanning one
    element further and finding a value that differs from the
    last survivor extends the squeezed prefix. Packages the
    `take (r+1)` split with `dedupAdj_snoc_keep`, so the loop
    proofs never unfold `take` themselves. -/
theorem dedupAdj_take_succ_keep (la : List (BitVec 32)) (r : Nat)
    (y p : BitVec 32)
    (hr : la[r]? = some y)
    (hlast : (dedupAdj (la.take r)).getLast? = some p)
    (hne : (y != p) = true) :
    dedupAdj (la.take (r + 1)) = dedupAdj (la.take r) ++ [y] := by
  have hsplit : la.take (r + 1) = la.take r ++ [y] := by
    simp [List.take_add_one, hr]
  rw [hsplit]
  exact dedupAdj_snoc_keep _ _ _ hlast hne

/-- Squeeze prefix step, drop leg (P2-M16 boundary): scanning one
    element further and finding the last survivor again leaves
    the squeezed prefix unchanged. -/
theorem dedupAdj_take_succ_drop (la : List (BitVec 32)) (r : Nat)
    (y p : BitVec 32)
    (hr : la[r]? = some y)
    (hlast : (dedupAdj (la.take r)).getLast? = some p)
    (heq : (y != p) = false) :
    dedupAdj (la.take (r + 1)) = dedupAdj (la.take r) := by
  have hsplit : la.take (r + 1) = la.take r ++ [y] := by
    simp [List.take_add_one, hr]
  rw [hsplit]
  exact dedupAdj_snoc_drop _ _ _ hlast heq

/-- Reverse-countdown step (P2-M17 boundary): dropping one
    fewer element from the front extends the reversed suffix by
    the scanned element. Packages the `drop (j-1)` split with
    `reverse_append`, so the loop proof never unfolds `drop`
    itself. -/
theorem drop_reverse_succ (la : List (BitVec 32)) (j : Nat)
    (y : BitVec 32)
    (hj : 1 ≤ j) (hy : la[j - 1]? = some y) :
    (la.drop (j - 1)).reverse = (la.drop j).reverse ++ [y] := by
  have hsplit : la.drop (j - 1) = [y] ++ la.drop j := by
    have h := List.drop_sub_one (l := la) (i := j) (by omega)
    simpa [hy] using h
  simp [hsplit, List.reverse_append]

/-- Take-set at the write head: storing at `w` then taking
    `w + 1` is the old `w`-prefix with the new word snocced
    (moved here from `Circe.Emit.VecUniqueCopy`, which uses it
    for the shared record discipline; no core lemma packages
    both steps). -/
theorem take_set_succ_self (lo : List (BitVec 32)) (w : Nat)
    (y : BitVec 32) (hwlt : w < lo.length) :
    (lo.set w y).take (w + 1) = (lo.take w) ++ [y] := by
  have h1 : (lo.set w y).take w = lo.take w :=
    List.take_set_of_le (Nat.le_refl w)
  have h2 : ((lo.set w y)[w]?.toList) = [y] :=
    congrArg Option.toList (List.getElem?_set_self hwlt)
  have h3 : (lo.set w y).take (w + 1)
      = (lo.set w y).take w ++ ((lo.set w y)[w]?.toList) :=
    List.take_add_one
  rw [h3, h1, h2]

/-- Squeeze is append-monotone as a prefix: appending more
    input can only extend the squeeze at the tail (each snoc
    either keeps the squeeze or snocs one survivor). -/
theorem dedupAdj_append_prefix (D E : List (BitVec 32)) :
    dedupAdj D <+: dedupAdj (D ++ E) := by
  induction E generalizing D with
  | nil => simpa using List.prefix_rfl (dedupAdj D)
  | cons y ys ih =>
    have hsnoc : dedupAdj D <+: dedupAdj (D ++ [y]) := by
      rw [dedupAdj_append_single]
      cases hD : (dedupAdj D).getLast? with
      | none =>
        have hnil : dedupAdj D = [] := List.getLast?_eq_none_iff.mp hD
        rw [hnil]
        exact List.prefix_append [] [y]
      | some p =>
        by_cases hne : (y != p) = true
        · simp only [hne, ite_true]
          exact List.prefix_append _ _
        · simp only [hne, ite_false]
          exact List.prefix_rfl
    have htail := ih (D ++ [y])
    have happend : D ++ y :: ys = (D ++ [y]) ++ ys := by simp
    rw [happend]
    exact List.IsPrefix.trans hsnoc htail

/-- Squeezing a scanned prefix yields a prefix of the full
    squeeze (prefix-monotonicity through `take_append_drop`). -/
theorem dedupAdj_take_prefix (la : List (BitVec 32)) (k : Nat) :
    dedupAdj (la.take k) <+: dedupAdj la := by
  have h := dedupAdj_append_prefix (la.take k) (la.drop k)
  rwa [List.take_append_drop] at h

/-- Squeeze length is monotone under `take`: the scanned
    prefix never squeezes longer than the whole input. The
    load-bearing bound for the caller-debt propagation
    (every keep step extends the squeezed prefix by exactly
    one, so the record bound on the full squeeze bounds each
    step). -/
theorem dedupAdj_take_length_le (la : List (BitVec 32)) (k : Nat) :
    (dedupAdj (la.take k)).length ≤ (dedupAdj la).length :=
  List.IsPrefix.length_le (dedupAdj_take_prefix la k)

