/-
Circe.CondFrame — F2 native conditional-framing spike (report-only).

Proves the `alias_cond` disjunctive post natively over `Mem`, reusing
`memFind_memStore_other` per arm, and measures the manual-frame
burden (the plan's MoSeL question). NOT wired to `validate`/`Emit`:
no `Func` is produced, no text is consumed — the F0 addresses and
the branch enter as hypotheses (see `condPost_disjoint` /
`condPost_aliased`).

Why not full admission (see `docs/ROADMAP.md` F2 report): (B1) a
triple output `(r, p', q')` is inexpressible — `pmk` builds exactly
a two-field `Point` `structVal` (anything else is `AssertFail`) and
no other struct-building expression exists; (B2) scalar writes
cannot land in `Mem` — no `CStmt` stores scalar blocks (`.vset` is
vector-only, `.assign` is env-only), so a single-output `Func` with
a `Mem`-writing transfer is equally inexpressible. The single-output
read projection (`r = c ? p : q`, choose-shaped) is NOT admitted:
it would silently drop the writes.

Imported by `Test/Driver.lean` for build coverage only (no suite
row — report-only spike).
-/
import Circe.Mem

/-- A live 1-word `i32` cell holding `v` (the F0 address facts say
    which address: `p` resolves to `param0`'s address, `q` to
    `param1`'s; L2 says the ranges overlap, so F1-style sequencing
    does not apply — the arms are branch-exclusive instead). -/
def cellAt (m : Mem) (a : Addr) (t : Nat) (v : BitVec 32) : Prop :=
  memFind m a = some ⟨t, true, [v]⟩

/-- Storing to a known live 1-word cell succeeds with the updated
    block pushed on top (proved once, reused by every arm below —
    this threading is what a separation-logic frame rule would
    automate). -/
theorem memStore_cell (m : Mem) (a t : Nat) (p x : BitVec 32)
    (hp : cellAt m a t p) :
    memStore m a t 0 x =
      .ok ⟨m.next, (a, ⟨t, true, [x]⟩) :: m.blocks, m.blocks64⟩ := by
  unfold cellAt at hp
  unfold memStore
  rw [hp]
  simp

/-- Reading back the cell just stored (the write leg of each arm). -/
theorem memFind_cell_store (m : Mem) (a t : Nat) (p x : BitVec 32)
    (hp : cellAt m a t p) (m' : Mem)
    (hstore : memStore m a t 0 x = .ok m') :
    cellAt m' a t x := by
  have h := memStore_cell m a t p x hp
  rw [hstore] at h
  cases h
  unfold cellAt
  simp [memFind]

/-- Disjoint case (`b ≠ a`, e.g. distinct caller addresses): each arm
    writes its own cell (read back above) and frames the other
    (`memFind_memStore_other`). This is the disjunctive post: both
    arms verified, footprints caller-dependent through `a`/`b`. -/
theorem condPost_disjoint (m m₁ m₂ : Mem) (a b t₁ t₂ : Nat)
    (p q : BitVec 32)
    (hp : cellAt m a t₁ p) (hq : cellAt m b t₂ q) (hne : b ≠ a)
    (h1 : memStore m a t₁ 0 11 = .ok m₁)
    (h2 : memStore m b t₂ 0 22 = .ok m₂) :
    (cellAt m₁ a t₁ 11 ∧ cellAt m₁ b t₂ q) ∧
    (cellAt m₂ b t₂ 22 ∧ cellAt m₂ a t₁ p) := by
  refine ⟨⟨memFind_cell_store _ _ _ _ _ hp _ h1, ?_⟩,
    ⟨memFind_cell_store _ _ _ _ _ hq _ h2, ?_⟩⟩
  · unfold cellAt
    rw [memFind_memStore_other m m₁ a b t₁ 0 11 h1 hne]
    exact hq
  · unfold cellAt
    rw [memFind_memStore_other m m₂ b a t₂ 0 22 h2 (Ne.symm hne)]
    exact hp

/-- Aliased case (`a = b`, e.g. the caller passes the same variable
    twice): one cell, branch-exclusive sequential update — sound with
    no framing at all. This is the case the `unknown` verdict must
    also cover, and the one a star-conjunction would conflate. -/
theorem condPost_aliased (m m₁ m₂ : Mem) (a t : Nat) (p : BitVec 32)
    (hp : cellAt m a t p)
    (h1 : memStore m a t 0 11 = .ok m₁)
    (h2 : memStore m a t 0 22 = .ok m₂) :
    cellAt m₁ a t 11 ∧ cellAt m₂ a t 22 :=
  ⟨memFind_cell_store _ _ _ _ _ hp _ h1,
   memFind_cell_store _ _ _ _ _ hp _ h2⟩
