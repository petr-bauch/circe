/-
Circe.CondFrame — F2 native conditional-framing spike (report-only).

Proves the `alias_cond` disjunctive post natively over `Mem`, reusing
`memFind_memStore_other` per arm, and measures the manual-frame
burden (the plan's MoSeL question). NOT wired to `validate`/`Emit`:
no `Func` is produced, no text is consumed — the F0 addresses and
the branch enter as hypotheses (see `condPost_disjoint` /
`condPost_aliased`). G3 promotes the S0 open contract here
(`condExec` + inversions below): the `Mem` program transfer runs
its closure step against, fed by the S1 `mstore` equations and the
S2 pin facts. The F0 addresses and the branch still enter as
hypotheses — the gate supplies them (S3 verdict branch).

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

/-- A live `i32`-word cell holding a whole word list (A-track):
    `cellAt` is the singleton case. Array loops thread this
    instead of one fact per index. -/
def cellsAt (m : Mem) (a : Addr) (t : Nat)
    (l : List (BitVec 32)) : Prop :=
  memFind m a = some ⟨t, true, l⟩

/-- Singleton bridge, both directions. -/
theorem cellAt_cellsAt (m : Mem) (a : Addr) (t : Nat)
    (v : BitVec 32) :
    cellAt m a t v ↔ cellsAt m a t [v] := by
  simp [cellAt, cellsAt]

/-- Storing into a known live multi-word cell succeeds with the
    `List.set` block pushed on top (generalizes `memStore_cell`,
    which is the index-0 singleton case). -/
theorem memStore_cellsAt (m : Mem) (a t i : Nat)
    (l : List (BitVec 32)) (x : BitVec 32)
    (hl : cellsAt m a t l) (hlt : i < l.length) :
    memStore m a t i x =
      .ok ⟨m.next, (a, ⟨t, true, l.set i x⟩) :: m.blocks,
        m.blocks64⟩ := by
  unfold cellsAt at hl
  unfold memStore
  rw [hl]
  simp [hlt]

/-- Reading back the list just stored into (the multi-word write
    leg; mirrors `memFind_cell_store`). -/
theorem memFind_cellsAt_store (m : Mem) (a t i : Nat)
    (l : List (BitVec 32)) (x : BitVec 32) (m' : Mem)
    (hl : cellsAt m a t l) (hlt : i < l.length)
    (hstore : memStore m a t i x = .ok m') :
    cellsAt m' a t (l.set i x) := by
  have h := memStore_cellsAt m a t i l x hl hlt
  rw [hstore] at h
  cases h
  unfold cellsAt
  simp [memFind]

/-- Loading from a known live multi-word cell at a present index
    (the array-loop read leg, via `getElem?`). -/
theorem memLoad_cellsAt (m : Mem) (a t i : Nat)
    (l : List (BitVec 32)) (x : BitVec 32)
    (hl : cellsAt m a t l) (hget : l[i]? = some x) :
    memLoad m a t i = .ok x := by
  unfold cellsAt at hl
  unfold memLoad
  rw [hl]
  simp [hget]

/-- Visited-prefix lookup: the frontier word of the evolving
    prefix shape is the unvisited list word (array-loop read). -/
theorem take_map_drop_getElem (l : List (BitVec 32)) (n : Nat)
    (h : n < l.length) :
    (((l.take n).map (· + 1) ++ l.drop n)[n]? = some l[n]) := by
  have hlenA : ((l.take n).map (· + 1)).length = n := by
    simp only [List.length_map, List.length_take]; omega
  rw [List.getElem?_append_right (by omega), hlenA, Nat.sub_self,
    List.getElem?_drop, Nat.add_zero]
  exact List.getElem?_eq_getElem h

/-- Drop-head under `set 0`: replacing the head of a dropped
    suffix is consing over the deeper drop (prefix-bridge step). -/
theorem drop_set_zero_cons (l : List (BitVec 32)) (n : Nat)
    (h : n < l.length) (x : BitVec 32) :
    ((l.drop n).set 0 x = x :: l.drop (n + 1)) := by
  apply List.ext_getElem?
  intro i
  cases i with
  | zero =>
    have hne : l.length - n ≠ 0 := by omega
    simp [List.getElem?_set, hne]
  | succ i =>
    simp only [List.getElem?_set, show ¬(0 = i + 1) from by omega, ite_false,
      List.getElem?_cons_succ, List.getElem?_drop]
    congr 1
    omega

/-- Visited-prefix bridge: storing the incremented word at the
    frontier turns the current prefix shape into the next one
    (take/map/drop is the spec shape, `set` the residue). -/
theorem take_map_drop_set_succ (l : List (BitVec 32)) (n : Nat)
    (h : n < l.length) :
    (((l.take n).map (· + 1) ++ l.drop n).set n (l[n] + 1) =
     ((l.take (n + 1)).map (· + 1) ++ l.drop (n + 1))) := by
  have hlenA : ((l.take n).map (· + 1)).length = n := by
    simp only [List.length_map, List.length_take]; omega
  have hget : l[n]? = some l[n] := List.getElem?_eq_getElem h
  rw [List.set_append_right n _ (by omega), hlenA, Nat.sub_self,
    drop_set_zero_cons l n h, List.take_add_one, List.map_append, hget,
    Option.toList_some, List.map_cons, List.map_nil, List.append_assoc]
  rfl

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

/-! ## G3 open contract (S0 spike promoted, S3).

A `Mem` program mirroring the cond body (`if (c) *p += 1; *q += 2`)
with the cells addressed by hypotheses. `q` is re-read after the
branch store, so an aliased caller observes `p`'s write — the
phenomenon no pure `(p,q,c)→(p′,q′)` function captures (G2).
Both verdicts invert program equations back to per-cell posts
(`condExec_invert_disjoint` / `condExec_invert_aliased`, the
closure step transfer runs); the executable prototype smoked all
six legs (disjoint add, aliased double-add, overflow errors under
`c=true`, masks under `c=false`).
-/


def loadCell (m : Mem) (a t : Nat) : Except Panic (BitVec 32) :=
  match memFind m a with
  | some ⟨t', true, [v]⟩ => if t' == t then .ok v else .error .AssertFail
  | _ => .error .AssertFail

theorem loadCell_cell (m : Mem) (a t : Nat) (v : BitVec 32)
    (h : cellAt m a t v) : loadCell m a t = .ok v := by
  unfold loadCell cellAt at *
  rw [h]
  simp

/-- Mem program mirroring `alias_cond` (`if (c) *p += 1; *q += 2`)
    with the cells addressed by hypotheses. `q` is re-read after
    the branch store, so an aliased caller observes `p`'s write. -/
def condExec (m : Mem) (a b t₁ t₂ : Nat) (c : Bool) :
    Except Panic Mem := do
  let p ← loadCell m a t₁
  match c with
  | true =>
    let pa ← checkedAddI32 p 1
    let m₁ ← memStore m a t₁ 0 pa
    let q ← loadCell m₁ b t₂
    let qb ← checkedAddI32 q 2
    memStore m₁ b t₂ 0 qb
  | false =>
    let q ← loadCell m b t₂
    let qb ← checkedAddI32 q 2
    memStore m b t₂ 0 qb

theorem loadCell_frame (m m₁ : Mem) (a b t t₂ : Nat) (q v : BitVec 32)
    (hq : cellAt m b t₂ q) (hne : b ≠ a)
    (h : memStore m a t 0 v = .ok m₁) :
    loadCell m₁ b t₂ = .ok q := by
  unfold loadCell cellAt at *
  rw [memFind_memStore_other m m₁ a b t 0 v h hne]
  rw [hq]
  simp

/-- Invert a successful cell load back to the `cellAt` fact. -/
theorem cellAt_of_loadCell (m : Mem) (a t : Nat) (q : BitVec 32)
    (h : loadCell m a t = .ok q) : cellAt m a t q := by
  unfold loadCell at h
  cases hm : memFind m a with
  | none => simp [hm] at h
  | some b =>
    cases b with
    | mk tag live data =>
      cases live with
      | false => simp [hm] at h
      | true =>
        cases data with
        | nil => simp [hm] at h
        | cons v rest =>
          cases rest with
          | nil =>
            cases heq : (tag == t) with
            | false => simp [hm, heq] at h
            | true =>
              simp [hm, heq] at h
              unfold cellAt
              rw [hm]
              simp_all
          | cons _ _ => simp [hm] at h

/-- Disjoint taken-branch: `q` re-read frames across `p`'s store,
    both writes land, the other cell frames. -/
theorem condExec_disjoint_true (m m₁ m' : Mem) (a b t₁ t₂ : Nat)
    (p q pa qb : BitVec 32)
    (hp : cellAt m a t₁ p) (hq : cellAt m b t₂ q) (hne : b ≠ a)
    (hs1 : memStore m a t₁ 0 pa = .ok m₁)
    (hq1 : loadCell m₁ b t₂ = .ok q)
    (hs2 : memStore m₁ b t₂ 0 qb = .ok m') :
    cellAt m' a t₁ pa ∧ cellAt m' b t₂ qb := by
  have hcell : cellAt m₁ a t₁ pa :=
    memFind_cell_store m a t₁ p pa hp m₁ hs1
  have hqcell : cellAt m₁ b t₂ q := cellAt_of_loadCell _ _ _ _ hq1
  refine ⟨?_, memFind_cell_store m₁ b t₂ q qb hqcell m' hs2⟩
  unfold cellAt
  rw [memFind_memStore_other m₁ m' b a t₂ 0 qb hs2 (Ne.symm hne)]
  exact hcell

/-- Aliased taken-branch: one cell, the re-read observes `p`'s
    write (`q = pa`), the second store wins. -/
theorem condExec_aliased_true (m m₁ m' : Mem) (a b t₁ t₂ : Nat)
    (p q pa qb : BitVec 32)
    (hp : cellAt m a t₁ p) (hq : cellAt m b t₂ q) (heq : b = a)
    (hs1 : memStore m a t₁ 0 pa = .ok m₁)
    (hq1 : loadCell m₁ b t₂ = .ok q)
    (hs2 : memStore m₁ b t₂ 0 qb = .ok m') :
    cellAt m' a t₁ qb := by
  rw [heq] at hq hq1 hs2
  have hsame : (⟨t₁, true, [p]⟩ : Block) = ⟨t₂, true, [q]⟩ := by
    have h1 := hp
    have h2 := hq
    unfold cellAt at h1 h2
    rw [h1] at h2
    exact (Option.some_inj.mp h2)
  cases hsame
  exact memFind_cell_store m₁ a t₁ _ qb
    (cellAt_of_loadCell _ _ _ _ hq1) m' hs2

/-- Capstone (disjoint): a `condExec` program equation inverts into
    per-cell post facts — the closure step transfer would run. The
    disequality is the gate-supplied `OracleNoalias` fact. -/
theorem condExec_invert_disjoint (m : Mem) (a b t₁ t₂ : Nat)
    (p q r₁ r₂ : BitVec 32)
    (hp : cellAt m a t₁ p) (hq : cellAt m b t₂ q) (hne : b ≠ a)
    (hp1 : checkedAddI32 p 1 = .ok r₁)
    (hq2 : checkedAddI32 q 2 = .ok r₂)
    (m' : Mem) (heq : condExec m a b t₁ t₂ true = .ok m') :
    cellAt m' a t₁ r₁ ∧ cellAt m' b t₂ r₂ := by
  unfold condExec at heq
  rw [loadCell_cell m a t₁ p hp] at heq
  simp only [Bind.bind, Except.bind] at heq
  rw [hp1] at heq
  simp only [Bind.bind, Except.bind] at heq
  cases hsto : memStore m a t₁ 0 r₁ with
  | error e => simp [hsto] at heq
  | ok m₁ =>
    rw [hsto] at heq
    simp only [Bind.bind, Except.bind] at heq
    have hq1 : loadCell m₁ b t₂ = .ok q :=
      loadCell_frame m m₁ a b t₁ t₂ q r₁ hq hne hsto
    rw [hq1] at heq
    simp only [Bind.bind, Except.bind] at heq
    rw [hq2] at heq
    simp only [Bind.bind, Except.bind] at heq
    exact condExec_disjoint_true m m₁ m' a b t₁ t₂ p q r₁ r₂
      hp hq hne hsto hq1 heq

/-- Capstone (aliased): the re-read observes `p`'s write, so the
    second addition runs on the stored value, not the stale `q` —
    transfer evaluates it in order (`hpa2`). The shared address
    identifies the tags first (`hsame`), then the second store wins. -/
theorem condExec_invert_aliased (m : Mem) (a b t₁ t₂ : Nat)
    (p q r₁ r₂ : BitVec 32)
    (hp : cellAt m a t₁ p) (hq : cellAt m b t₂ q) (heq : b = a)
    (hp1 : checkedAddI32 p 1 = .ok r₁)
    (hpa2 : checkedAddI32 r₁ 2 = .ok r₂)
    (m' : Mem) (heqE : condExec m a b t₁ t₂ true = .ok m') :
    cellAt m' a t₁ r₂ := by
  unfold condExec at heqE
  rw [loadCell_cell m a t₁ p hp] at heqE
  simp only [Bind.bind, Except.bind] at heqE
  rw [hp1] at heqE
  simp only [Bind.bind, Except.bind] at heqE
  cases hsto : memStore m a t₁ 0 r₁ with
  | error e => simp [hsto] at heqE
  | ok m₁ =>
    rw [hsto] at heqE
    simp only [Bind.bind, Except.bind] at heqE
    have hcell : cellAt m₁ a t₁ r₁ :=
      memFind_cell_store m a t₁ p r₁ hp m₁ hsto
    have hsame : (⟨t₁, true, [p]⟩ : Block) = ⟨t₂, true, [q]⟩ := by
      have h1 := hp
      have h2 := hq
      unfold cellAt at h1 h2
      rw [heq] at h2
      rw [h1] at h2
      exact (Option.some_inj.mp h2)
    cases hsame
    have hq1 : loadCell m₁ b t₁ = .ok r₁ := by
      rw [heq]
      exact loadCell_cell m₁ a t₁ r₁ hcell
    rw [hq1] at heqE
    simp only [Bind.bind, Except.bind] at heqE
    rw [hpa2] at heqE
    simp only [Bind.bind, Except.bind] at heqE
    rw [heq] at heqE
    exact memFind_cell_store m₁ a t₁ r₁ r₂ hcell m' heqE
