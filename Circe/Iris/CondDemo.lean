/-
Circe.Iris.CondDemo — Phase 1 MVP demo: the `alias_cond`
disjunctive post through the reusable frame rule.

`condPost_disjoint_star` proves both legs with `frame_memStore`
(the other cell rides the frame — no manual `rw` threading) and
`star_intro` assembles the initial stars. `condPost_disjoint_parity`
then recovers the EXACT native `condPost_disjoint` conclusions
via `star_cellAt`: same statements, frame-rule proofs. The
aliased leg (`condPost_aliased_parity`) needs no star at all —
one cell, branch-exclusive update — discharged through the
`cellAt_stateOf` bridge.

The closing section exercises MoSeL tactics over our instance
(`HeapProp Block`): commutativity via `isplitr`, and the
frame-congruence pattern (`P ⊢ Q` lifts through an arbitrary
frame `R`) via `iapply`. No hypotheses are dropped, so no
affinity instance is needed.
-/
import Circe.Iris.PointsTo

@[expose] public section

open Iris BI
open Iris.Instances.Data Iris.Instances.Classical

namespace Circe.Iris

/-- Disjoint leg, star form: each store updates its cell while
    the other cell rides the frame. Compare the native proof,
    which re-pays one `memFind_memStore_other` rewrite per leg. -/
theorem condPost_disjoint_star (m m₁ m₂ : Mem) (a b t₁ t₂ : Nat)
    (p q : BitVec 32)
    (hp : cellAt m a t₁ p) (hq : cellAt m b t₂ q) (hne : b ≠ a)
    (h1 : memStore m a t₁ 0 11 = .ok m₁)
    (h2 : memStore m b t₂ 0 22 = .ok m₂) :
    (iprop(cellAtI a t₁ 11 ∗ cellAtI b t₂ q)) (stateOf m₁) ∧
    (iprop(cellAtI b t₂ 22 ∗ cellAtI a t₁ p)) (stateOf m₂) := by
  refine ⟨?_, ?_⟩
  · exact frame_memStore m m₁ a t₁ p 11 _ hp h1
      (star_intro m a b _ _ hne hp hq)
  · exact frame_memStore m m₂ b t₂ q 22 _ hq h2
      (star_intro m b a _ _ (Ne.symm hne) hq hp)

/-- Parity: the exact native `condPost_disjoint` conclusions,
    recovered from the star form — the written cells via
    `star_cellAt`, the framed cells via `star_frame_cellAt`. -/
theorem condPost_disjoint_parity (m m₁ m₂ : Mem) (a b t₁ t₂ : Nat)
    (p q : BitVec 32)
    (hp : cellAt m a t₁ p) (hq : cellAt m b t₂ q) (hne : b ≠ a)
    (h1 : memStore m a t₁ 0 11 = .ok m₁)
    (h2 : memStore m b t₂ 0 22 = .ok m₂) :
    (cellAt m₁ a t₁ 11 ∧ cellAt m₁ b t₂ q) ∧
    (cellAt m₂ b t₂ 22 ∧ cellAt m₂ a t₁ p) := by
  obtain ⟨hleg1, hleg2⟩ := condPost_disjoint_star m m₁ m₂ a b t₁ t₂ p q
    hp hq hne h1 h2
  exact ⟨⟨star_cellAt m₁ a t₁ 11 _ hleg1,
      star_frame_cellAt m₁ b t₂ q _ hleg1⟩,
    ⟨star_cellAt m₂ b t₂ 22 _ hleg2,
      star_frame_cellAt m₂ a t₁ p _ hleg2⟩⟩

/-- Aliased leg parity: one cell, no star — the bridge alone
    closes both conclusions. This is the case a
    star-conjunction would conflate. -/
theorem condPost_aliased_parity (m m₁ m₂ : Mem) (a t : Nat)
    (p : BitVec 32)
    (hp : cellAt m a t p)
    (h1 : memStore m a t 0 11 = .ok m₁)
    (h2 : memStore m a t 0 22 = .ok m₂) :
    cellAt m₁ a t 11 ∧ cellAt m₂ a t 22 :=
  ⟨(cellAt_stateOf m₁ a t 11).mpr (by
      unfold cellAtI pt maps_to
      show stateOf m₁ a = _
      unfold stateOf
      rw [memFind_cell_store m a t p 11 hp m₁ h1]),
   (cellAt_stateOf m₂ a t 22).mpr (by
      unfold cellAtI pt maps_to
      show stateOf m₂ a = _
      unfold stateOf
      rw [memFind_cell_store m a t p 22 hp m₂ h2])⟩

/-! ## Stretch: sequential stores reuse the rule -/

/-- Two sequential stores to one cell with a standing frame
    (the take-branch store pattern: the second application
    frames over the first result — no new rule, no re-proof). -/
theorem double_store_frame (m m₁ m₂ : Mem) (a : Addr) (t : Nat)
    (p x y : BitVec 32) (R : HeapProp Block)
    (hp : cellAt m a t p)
    (h1 : memStore m a t 0 x = .ok m₁)
    (h2 : memStore m₁ a t 0 y = .ok m₂)
    (h : (iprop(cellAtI a t p ∗ R)) (stateOf m)) :
    (iprop(cellAtI a t y ∗ R)) (stateOf m₂) := by
  have hmid := frame_memStore m m₁ a t p x R hp h1 h
  have hp' : cellAt m₁ a t x :=
    memFind_cell_store m a t p x hp m₁ h1
  exact frame_memStore m₁ m₂ a t x y R hp' h2 hmid

/-! ## MoSeL tactics over our instance -/

/-- Commutativity, MoSeL style: keep the left hypothesis
    for the left goal, close both sides by assumption. -/
example (P Q : HeapProp Block) :
    (P ∗ Q) ⊢ (Q ∗ P) := by
  iintro ⟨HP, HQ⟩
  isplitl [HQ]
  · iexact HQ
  · iexact HP

/-- Frame congruence: a wand lifts through an arbitrary
    frame — the tactic face of `frame_memStore`. -/
example (P Q R : HeapProp Block) (h : P -∗ Q) :
    (P ∗ R) ⊢ (Q ∗ R) := by
  iintro ⟨HP, HR⟩
  ihave HQ : Q $$ [HP]
  · iapply h $$ HP
  isplitl [HQ]
  · iexact HQ
  · iexact HR

end Circe.Iris
