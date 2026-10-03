/-
Circe.ReadOnly — N2a read-only sharing discipline.

Today `validate` admits only proven-disjoint inputs. The next ring out
is code that is *safe but not statically disjoint*: several `const`
readers over the same array. This module pins down, model-side, which
`const` aliasing shapes are value-sound and proves the corresponding
footprints:

- `IsReadOnlyParams`: no `mutBorrow` among the params (every array
  param is `sharedBorrow`, everything else `owned`). `HasWriter` is
  the negation witness; any writer present — including a writer
  alongside readers — is outside the discipline
  (`writer_reader_excluded`; the per-cause rejection catalog is N2b).
- Two-reader footprint: binding two `sharedBorrow` arrays (+ the owned
  length) pins two fresh blocks, so `LayoutNoAlias` holds by
  construction (`bindMemArgs_twoShared`, `twoShared_noalias`) and both
  pins are consistent (`twoShared_consistent`).
- Alias soundness (`twoShared_alias_sound`): when both params receive
  the *same* list (the aliased call `f(a, a, n)`), reads through either
  pin agree — duplication is invisible because readers never write, so
  the model may always split one shared block into two identical pins.

Non-goals (stay loud): any writer + reader combination, raw-pointer
arithmetic, lifetime inference. Text-gate admission of multi-reader
shapes (`derivedNoalias` / `validate`) is N2b/N2c work; N2a is the
model-side discipline these gates will rest on.
-/
import Circe.Mem

/-! ## Discipline predicates -/

/-- Read-only params: no `mutBorrow` anywhere (array params are
    `sharedBorrow`, everything else `owned`). -/
def IsReadOnlyParams (ps : List Param) : Prop :=
  ∀ p ∈ ps, ∀ r, p.role ≠ .mutBorrow r

/-- A live writer: some param is a `mutBorrow`. -/
def HasWriter (ps : List Param) : Prop :=
  ∃ p ∈ ps, ∃ r, p.role = .mutBorrow r

/-- A writer anywhere kills read-only status. -/
theorem hasWriter_not_readOnly (ps : List Param) (h : HasWriter ps) :
    ¬ IsReadOnlyParams ps := by
  obtain ⟨p, hp, r, hr⟩ := h
  intro hro
  exact hro p hp r hr

/-- A writer alongside (any) readers is outside the discipline — the
    N2b rejection catalog hook: writer + reader still rejects. -/
theorem writer_reader_excluded (ps : List Param) (p : Param) (r : Nat)
    (hp : p ∈ ps) (hw : p.role = .mutBorrow r) :
    ¬ IsReadOnlyParams ps :=
  fun hro => hro p hp r hw

/-! ## Canonical two-reader params -/

/-- Canonical two-reader params (the `sum_two(a, b, n)` discipline
    shape): two `sharedBorrow` arrays + the owned length. -/
def twoReaderParams : List Param :=
  [{ name := "a", ty := .array (.u 32) 4096, role := .sharedBorrow },
   { name := "b", ty := .array (.u 32) 4096, role := .sharedBorrow },
   { name := "n", ty := .u 32, role := .owned }]

/-- The canonical two-reader params are read-only. -/
theorem twoReaderParams_readOnly : IsReadOnlyParams twoReaderParams := by
  intro p hp r hcon
  simp only [twoReaderParams, List.mem_cons, List.not_mem_nil,
    or_false] at hp
  rcases hp with rfl | rfl | rfl <;> simp at hcon

/-! ## Two-reader footprint -/

/-- Binding two `sharedBorrow` arrays pins two fresh blocks (disjoint
    by construction — tag creation at bind hands out `0` then `1`). -/
theorem bindMemArgs_twoShared (l₁ l₂ : List (BitVec 32)) (nv : BitVec 32) :
    bindMemArgs twoReaderParams [.arr32 l₁, .arr32 l₂, .u32 nv] emptyMem =
      some ([("a", .arr32 l₁), ("b", .arr32 l₂), ("n", .u32 nv)],
        ⟨2, [(1, ⟨1, true, l₁⟩), (0, ⟨0, true, l₂⟩)], []⟩,
        [("a", 1, 1), ("b", 0, 0)]) := by
  rfl

/-- The two-reader entry footprint is pairwise disjoint. -/
theorem twoShared_noalias : LayoutNoAlias [("a", 1, 1), ("b", 0, 0)] := by
  simp [LayoutNoAlias, layoutAddrs]

/-- The two-reader footprint (the `oracleNoalias` existential, stated
    over the params directly — no `Func` wrapper needed for the
    discipline). -/
theorem twoShared_footprint (l₁ l₂ : List (BitVec 32)) (nv : BitVec 32) :
    ∃ ρ m π, bindMemArgs twoReaderParams [.arr32 l₁, .arr32 l₂, .u32 nv]
      emptyMem = some (ρ, m, π) ∧ LayoutNoAlias π :=
  ⟨_, _, _, bindMemArgs_twoShared l₁ l₂ nv, twoShared_noalias⟩

/-- Both pins are consistent: each resolves to a live block holding
    exactly its value-level list. -/
theorem twoShared_consistent (l₁ l₂ : List (BitVec 32)) (nv : BitVec 32) :
    MemConsistent [("a", .arr32 l₁), ("b", .arr32 l₂), ("n", .u32 nv)]
      ⟨2, [(1, ⟨1, true, l₁⟩), (0, ⟨0, true, l₂⟩)], []⟩
      [("a", 1, 1), ("b", 0, 0)] := by
  have hlayA : layoutLookup [("a", 1, 1), ("b", 0, 0)] "a" = some (1, 1) :=
    layoutLookup_hit "a" 1 1 _
  have hlayB : layoutLookup [("a", 1, 1), ("b", 0, 0)] "b" = some (0, 0) := by
    simp [layoutLookup, show ("b" : String) ≠ "a" by decide]
  have harrA : envLookup [("a", .arr32 l₁), ("b", .arr32 l₂), ("n", .u32 nv)]
      "a" = some (.arr32 l₁) := rfl
  have harrB : envLookup [("a", .arr32 l₁), ("b", .arr32 l₂), ("n", .u32 nv)]
      "b" = some (.arr32 l₂) := by
    simp [envLookup, show ("b" : String) ≠ "a" by decide]
  have hlayB' : layoutLookup [("b", 0, 0)] "b" = some (0, 0) :=
    layoutLookup_hit "b" 0 0 _
  have hfindA : memFind ⟨2, [(1, ⟨1, true, l₁⟩), (0, ⟨0, true, l₂⟩)], []⟩ 1 =
      some ⟨1, true, l₁⟩ := by
    simp [memFind]
  have hfindB : memFind ⟨2, [(1, ⟨1, true, l₁⟩), (0, ⟨0, true, l₂⟩)], []⟩ 0 =
      some ⟨0, true, l₂⟩ := by
    have h01 : (0 == 1) = false := by decide
    simp [memFind, h01]
  intro x ad tg h
  by_cases ha : x = "a"
  · subst ha
    rw [hlayA] at h
    cases h
    exact Or.inl ⟨l₁, Or.inl harrA, _, hfindA, rfl, rfl, rfl⟩
  · rw [layoutLookup_miss "a" x 1 1 _ ha] at h
    by_cases hb : x = "b"
    · subst hb
      rw [hlayB'] at h
      cases h
      exact Or.inl ⟨l₂, Or.inl harrB, _, hfindB, rfl, rfl, rfl⟩
    · rw [layoutLookup_miss "b" x 0 0 _ hb] at h
      simp [layoutLookup] at h

/-! ## Alias soundness: one shared block reads identically through both pins -/

/-- Loads through either pin agree when both hold the same list (the
    aliased call `f(a, a, n)` duplicates one shared block into two
    identical pins). -/
theorem twoShared_load_agree (l : List (BitVec 32)) (i : Nat)
    (x : BitVec 32) (hval : l[i]? = some x) :
    memLoad ⟨2, [(1, ⟨1, true, l⟩), (0, ⟨0, true, l⟩)], []⟩ 1 1 i = .ok x ∧
    memLoad ⟨2, [(1, ⟨1, true, l⟩), (0, ⟨0, true, l⟩)], []⟩ 0 0 i = .ok x := by
  have hfindA : memFind ⟨2, [(1, ⟨1, true, l⟩), (0, ⟨0, true, l⟩)], []⟩ 1 =
      some ⟨1, true, l⟩ := by
    simp [memFind]
  have hfindB : memFind ⟨2, [(1, ⟨1, true, l⟩), (0, ⟨0, true, l⟩)], []⟩ 0 =
      some ⟨0, true, l⟩ := by
    have h01 : (0 == 1) = false := by decide
    simp [memFind, h01]
  exact ⟨memLoad_hit _ _ _ _ _ _ hfindA rfl rfl hval,
    memLoad_hit _ _ _ _ _ _ hfindB rfl rfl hval⟩

/-- Reads through either pin agree with each other (and with `Eval`):
    aliasing multiple `sharedBorrow` readers is value-sound. -/
theorem twoShared_alias_sound (l : List (BitVec 32)) (nv : BitVec 32)
    (ie : CExpr) (i x : BitVec 32)
    (hieMem : memEvalExpr ie [("a", .arr32 l), ("b", .arr32 l), ("n", .u32 nv)]
      ⟨2, [(1, ⟨1, true, l⟩), (0, ⟨0, true, l⟩)], []⟩
      [("a", 1, 1), ("b", 0, 0)] =
      evalExpr ie [("a", .arr32 l), ("b", .arr32 l), ("n", .u32 nv)])
    (hie : evalExpr ie [("a", .arr32 l), ("b", .arr32 l), ("n", .u32 nv)] =
      .ok (.u32 i))
    (hval : l[i.toNat]? = some x) :
    memEvalExpr (.idx "a" ie) [("a", .arr32 l), ("b", .arr32 l), ("n", .u32 nv)]
      ⟨2, [(1, ⟨1, true, l⟩), (0, ⟨0, true, l⟩)], []⟩
      [("a", 1, 1), ("b", 0, 0)] =
    memEvalExpr (.idx "b" ie) [("a", .arr32 l), ("b", .arr32 l), ("n", .u32 nv)]
      ⟨2, [(1, ⟨1, true, l⟩), (0, ⟨0, true, l⟩)], []⟩
      [("a", 1, 1), ("b", 0, 0)] := by
  have hlayA : layoutLookup [("a", 1, 1), ("b", 0, 0)] "a" = some (1, 1) :=
    layoutLookup_hit "a" 1 1 _
  have hlayB : layoutLookup [("a", 1, 1), ("b", 0, 0)] "b" = some (0, 0) := by
    simp [layoutLookup, show ("b" : String) ≠ "a" by decide]
  have harrA : envLookup [("a", .arr32 l), ("b", .arr32 l), ("n", .u32 nv)]
      "a" = some (.arr32 l) := rfl
  have harrB : envLookup [("a", .arr32 l), ("b", .arr32 l), ("n", .u32 nv)]
      "b" = some (.arr32 l) := by
    simp [envLookup, show ("b" : String) ≠ "a" by decide]
  obtain ⟨hmemA, hmemB⟩ := twoShared_load_agree l i.toNat x hval
  have hA := memEvalExpr_idx_hit "a" ie _ _ _ l i x 1 1
    hlayA harrA hieMem hie hmemA hval
  have hB := memEvalExpr_idx_hit "b" ie _ _ _ l i x 0 0
    hlayB harrB hieMem hie hmemB hval
  rw [hA, hB]
  simp only [evalExpr, hie, harrA, harrB, hval]
