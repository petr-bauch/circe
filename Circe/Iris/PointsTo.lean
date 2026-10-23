/-
Circe.Iris.PointsTo — Phase 1 MVP core: `Mem` points-to in the
classical Iris separation logic + one reusable frame rule.

The classical instance (`Iris.Instances.Classical`: `HeapProp`
over a total `Nat → StateResult` state, no CMRA/ghost setup,
no program logic) hosts our `Block` directly as its value
type. `stateOf` reifies a concrete `Mem` lookup map as a
classical state; `cellAtI`/`cellsAtI` are the `↦` points-to
over it. Bridges connect them back to `cellAt`/`cellsAt`.

The deliverable is `frame_memStore`: a store to one cell
preserves an *arbitrary* frame assertion over the rest —
proved once from `memFind_memStore_other` (+ the write leg
`memFind_cell_store`), applied at every site. `star_intro`
assembles two disjoint points-to facts into one star.
-/
import Circe.Mem
import Iris.Instances.Classical.Instance
import Iris.Instances.Classical.Notation
import Iris.ProofMode

@[expose] public section

open Iris BI
open Iris.Instances.Data Iris.Instances.Classical

namespace Circe.Iris

/-- Reify a concrete `Mem` as a classical separation-logic
    state: bound addresses map to `result`, unbound to
    `unknown` (never `conflict` — `Mem` is a map). -/
def stateOf (m : Mem) : State Block :=
  fun a => match memFind m a with
    | none => unknown
    | some b => result b

theorem stateOf_memFind (m : Mem) (a : Addr) :
    stateOf m a = match memFind m a with
      | none => (unknown : StateResult Block)
      | some b => result b := rfl

/-- Points-to over reified memory: address `a` holds exactly
    the block `b`. -/
def pt (a : Nat) (b : Block) : HeapProp Block :=
  maps_to a b

/-- Single-cell points-to (`cellAt` under the reification). -/
def cellAtI (a : Addr) (t : Nat) (v : BitVec 32) : HeapProp Block :=
  pt a ⟨t, true, [v]⟩

/-- Whole-block points-to (`cellsAt` under the reification). -/
def cellsAtI (a : Addr) (t : Nat) (l : List (BitVec 32)) : HeapProp Block :=
  pt a ⟨t, true, l⟩

/-- Bridge: `cellAt` holds iff its points-to holds of the
    reified state. -/
theorem cellAt_stateOf (m : Mem) (a : Addr) (t : Nat) (v : BitVec 32) :
    cellAt m a t v ↔ cellAtI a t v (stateOf m) := by
  unfold cellAt cellAtI pt maps_to stateOf
  constructor
  · intro h
    simp [h]
  · intro h
    cases hfind : memFind m a with
    | none => simp [hfind] at h
    | some b => simp_all

/-- Bridge: `cellsAt` holds iff its points-to holds of the
    reified state. -/
theorem cellsAt_stateOf (m : Mem) (a : Addr) (t : Nat)
    (l : List (BitVec 32)) :
    cellsAt m a t l ↔ cellsAtI a t l (stateOf m) := by
  unfold cellsAt cellsAtI pt maps_to stateOf
  constructor
  · intro h
    simp [h]
  · intro h
    cases hfind : memFind m a with
    | none => simp [hfind] at h
    | some b => simp_all

/-- Unfolded star over a reified state (the `∗`/`↔` syntax
    only elaborates inside `iprop`, and the global `∃` macro
    means BI-exists, so the helper is stated with `Eq`,
    `Exists`, and `||` — sites rewrite through this once
    instead of unfolding instance projections by hand). -/
theorem sep_unfold (P Q : HeapProp Block) (σ : State Block) :
    (iprop(P ∗ Q)) σ = Exists (fun σ₁ => Exists (fun σ₂ =>
      σ = σ₁ ∪ σ₂ ∧ σ₁ || σ₂ ∧ P σ₁ ∧ Q σ₂)) := by
  rfl

/-- Two disjoint points-to facts assemble into one star over
    the reified state (proved once; every multi-cell post
    starts here instead of re-splitting the state by hand). -/
theorem star_intro (m : Mem) (a b : Addr) (ba bb : Block)
    (hne : b ≠ a)
    (ha : memFind m a = some ba) (hb : memFind m b = some bb) :
    (iprop(pt a ba ∗ pt b bb)) (stateOf m) := by
  rw [sep_unfold]
  refine ⟨(fun i => if i = a then stateOf m i else unknown),
    (fun i => if i = a then unknown else stateOf m i), ?_, ?_, ?_, ?_⟩
  · apply funext
    intro i
    simp only [Union.union]
    by_cases h : i = a
    · simp [h]
      cases hσ : stateOf m a <;> rfl
    · simp [h]
      cases hσ : stateOf m i <;> rfl
  · intro i
    simp only []
    by_cases h : i = a
    · simp [h]
    · simp [h]
  · unfold pt maps_to stateOf
    simp [ha]
  · unfold pt maps_to stateOf
    simp [hb, hne]

/-- The reusable frame rule: a successful index-0 cell store
    updates its cell's points-to and preserves an *arbitrary*
    frame `R` over the rest. Sites apply this; nobody re-proves
    the `memFind_memStore_other` threading again. -/
theorem frame_memStore (m m' : Mem) (a : Addr) (t : Nat)
    (p x : BitVec 32) (R : HeapProp Block)
    (hp : cellAt m a t p)
    (hstore : memStore m a t 0 x = .ok m')
    (h : (iprop(cellAtI a t p ∗ R)) (stateOf m)) :
    (iprop(cellAtI a t x ∗ R)) (stateOf m') := by
  have hwrite : memFind m' a = some ⟨t, true, [x]⟩ :=
    memFind_cell_store m a t p x hp m' hstore
  have hrest : ∀ b : Addr, b ≠ a →
      stateOf m' b = stateOf m b := by
    intro b hne
    unfold stateOf
    rw [memFind_memStore_other m m' a b t 0 x hstore hne]
  rw [sep_unfold] at h ⊢
  obtain ⟨σ₁, σ₂, hunion, hdisj, hP, hR⟩ := h
  have hσ₁ : σ₁ a = result ⟨t, true, [p]⟩ := by
    have := hP
    unfold cellAtI pt maps_to at this
    exact this
  have hσ₂ : σ₂ a = unknown := by
    have hdisj' := hdisj
    unfold Disjoint.disjoint at hdisj'
    have hcase := hdisj' a
    cases hcase with
    | inl hl =>
      rw [hl] at hσ₁
      simp at hσ₁
    | inr hr => exact hr
  refine ⟨(fun i => if i = a then result (⟨t, true, [x]⟩ : Block) else σ₁ i),
    σ₂, ?_, ?_, ?_, hR⟩
  · apply funext
    intro i
    simp only [Union.union]
    by_cases h : i = a
    · subst h
      rw [hσ₂]
      simp
      simp only [stateOf, hwrite]
    · have hU : (σ₁ ∪ σ₂) i = stateOf m i := by rw [hunion]
      simp only [Union.union] at hU
      simp [h]
      rw [hU]
      exact hrest i h
  · intro i
    simp only []
    by_cases h : i = a
    · subst h
      exact Or.inr hσ₂
    · simp [h]
      have hdisj' := hdisj
      unfold Disjoint.disjoint at hdisj'
      exact hdisj' i
  · show (if a = a then result (⟨t, true, [x]⟩ : Block) else σ₁ a) =
        result (⟨t, true, [x]⟩ : Block)
    simp

/-- Adequacy core: from an explicit split (`hunion`,
    `hdisj`) plus the points-to on the left substate, recover
    the ordinary `cellAt` fact on the full state (written cell
    from its split, frame from disjointness, union for the
    lookup). -/
theorem split_cellAt (m : Mem) (a : Addr) (t : Nat) (v : BitVec 32)
    (σ₁ σ₂ : State Block)
    (hunion : stateOf m = σ₁ ∪ σ₂) (hdisj : σ₁ || σ₂)
    (hσ : σ₁ a = result ⟨t, true, [v]⟩) : cellAt m a t v := by
  have hσ₂ : σ₂ a = unknown := by
    have hdisj' := hdisj
    unfold Disjoint.disjoint at hdisj'
    have hcase := hdisj' a
    cases hcase with
    | inl hl =>
      rw [hl] at hσ
      simp at hσ
    | inr hr => exact hr
  have hfull : stateOf m a = result ⟨t, true, [v]⟩ := by
    have hU : (σ₁ ∪ σ₂) a = stateOf m a := by rw [hunion]
    rw [← hU]
    simp only [Union.union]
    rw [hσ, hσ₂]
  have hI : cellAtI a t v (stateOf m) := by
    unfold cellAtI pt maps_to
    exact hfull
  exact (cellAt_stateOf m a t v).mpr hI

/-- Adequacy, left side: a star over the reified state yields
    back the `cellAt` fact for its left points-to. -/
theorem star_cellAt (m : Mem) (a : Addr) (t : Nat) (v : BitVec 32)
    (R : HeapProp Block)
    (h : (iprop(cellAtI a t v ∗ R)) (stateOf m)) : cellAt m a t v := by
  rw [sep_unfold] at h
  obtain ⟨σ₁, σ₂, hunion, hdisj, hP, hR⟩ := h
  have hσ : σ₁ a = result ⟨t, true, [v]⟩ := by
    have := hP
    unfold cellAtI pt maps_to at this
    exact this
  exact split_cellAt m a t v σ₁ σ₂ hunion hdisj hσ

/-- Adequacy, frame side: a star over the reified state yields
    back the `cellAt` fact for its right (framed) points-to —
    the union/disjoint commutativity does the side swap. -/
theorem star_frame_cellAt (m : Mem) (a : Addr) (t : Nat)
    (v : BitVec 32) (P : HeapProp Block)
    (h : (iprop(P ∗ cellAtI a t v)) (stateOf m)) : cellAt m a t v := by
  rw [sep_unfold] at h
  obtain ⟨σ₁, σ₂, hunion, hdisj, hP, hR⟩ := h
  have hσ : σ₂ a = result ⟨t, true, [v]⟩ := by
    have := hR
    unfold cellAtI pt maps_to at this
    exact this
  have hunion' : stateOf m = σ₂ ∪ σ₁ := by
    rw [union_comm]
    exact hunion
  exact split_cellAt m a t v σ₂ σ₁ hunion' (disjoint_comm.mp hdisj) hσ

end Circe.Iris
