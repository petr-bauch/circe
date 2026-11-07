/-
Circe.Lemmas.TwoCursor — U3 two-cursor compaction pack.

The one repeated shape across the compacting slices (P2-M9 remove,
P2-M13 unique): closing the survivor count from a pinned prefix.
Both `evalProgFunc_vecRemove_spec` and
`evalProgFunc_vecUnique_spec` proved the same `take`-length chain
inline — `List.length_take` plus a `Nat.min_eq_left` discharge —
before rewriting with the slice prefix equation. That chain now
lives here once, as `take_length_of_le`, with the full
prefix-to-count step as `squeeze_length_eq`.

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
