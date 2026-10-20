/-
Circe.Lemmas.CheckedIx — U3 P1 checked-index pack.

The one repeated shape across the swap-loop slices (R/S, and the
merge-sort drains that reuse them): a pointwise read of two
sequential positional writes. Both `RevInv_step` (R) and
`SegInv_step` (S) proved the four-case `getElem?_set` dispatch
inline, verbatim — including the touching-case subtlety
(`i = j - 1`: both reads see one cell, so the reads agree and the
second write wins). That dispatch now lives here once, as
`doubleSet_read`, with the touching case discharged by an explicit
`hab` hypothesis instead of a second look at the reads.

Design notes (read before extending):
- The `if` nests `i` outside `j`: `if p = i then some b else
  if p = j then some a else l[p]?`. The touching case (`p = i = j`)
  therefore needs `hab : i = j → a = b`, proved at each call site
  from the two checked reads (`Option.some_inj` on `ha`/`hb`).
- Bounds side-goals (`i < l.length`, `j < (l.set i b).length`) stay
  `by omega` at the call site — with the invariant in context that
  one-liner *is* the automation, and a bundle lemma would just move
  the same `omega` behind an extra name.
- `doubleSet_length` is the `length_set` preservation chain that
  precedes every such dispatch.
-/

/-- Pointwise read of two sequential positional writes: position
    `p` sees the second write at `j`, else the first write at `i`,
    else the original word. The `hab` hypothesis discharges the
    touching case (`i = j`), where both writes land on one cell. -/
theorem doubleSet_read (l : List α) (i j : Nat) (a b : α)
    (hi : i < l.length) (hj : j < (l.set i b).length)
    (hab : i = j → a = b) (p : Nat) :
    ((l.set i b).set j a)[p]? =
      if p = i then some b else if p = j then some a else l[p]? := by
  by_cases h1 : p = i <;> by_cases h2 : p = j
  · have hij : i = j := by omega
    rw [List.getElem?_set, if_pos h2.symm, if_pos hj, if_pos h1,
      hab hij]
  · have o1 : ¬ j = p := by omega
    rw [List.getElem?_set, if_neg o1, h1,
      List.getElem?_set_self hi, if_pos rfl]
  · rw [List.getElem?_set, if_pos h2.symm, if_pos hj, if_neg h1,
      if_pos h2]
  · have o1 : ¬ j = p := Ne.symm h2
    have o2 : i ≠ p := Ne.symm h1
    rw [List.getElem?_set, if_neg o1, List.getElem?_set_ne o2,
      if_neg h1, if_neg h2]

/-- Two positional writes preserve length (the `length_set` chain
    that precedes every `doubleSet_read` use). -/
theorem doubleSet_length (l : List α) (i j : Nat) (a b : α) :
    ((l.set i b).set j a).length = l.length := by
  rw [List.length_set, List.length_set]
