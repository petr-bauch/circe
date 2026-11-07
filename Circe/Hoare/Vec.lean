/-
Circe.Hoare.Vec — vector/cursor assertions for Hoare proofs (P3-N4).

The `HTriple` / `HTripleProg` rules in `Circe.Hoare.Rules` speak
the raw state `(ρ, m, π)`: every pre/postcondition repeats
`envLookup`, `layoutLookup`, and `memFind` shape facts plus
`BitVec.toNat` plumbing for cursors. This module names the three
recurring shapes so user proofs state vector facts instead:

- `vecEnv v l`: the environment binds `v` to the word list `l`;
- `cursorAt x n`: cursor `x` holds the natural number `n`
  (the `BitVec` witness stays inside the predicate);
- `vecSnapshot v l`: the layout pins the single `mutBorrow`
  block and the block holds the length word plus `l`
  (the transfer footprint, cf. `bindMemArgs_vecUnique`).

Plus `htripleProg_let_at`, the program-level pure-`let_` triple
missing from `Circe.Hoare.Rules` (proved from
`memEvalProgStmt_let_fb` + `memEvalStmtFuel_let_pure`, so no
`Transfer` import is needed here). All definitions reduce to the
existing predicates and equations: no new semantics.
-/
import Circe.Hoare.Def

/-- The environment binds vector variable `v` to the word list
    `l` (value layer; the memory side is `vecSnapshot`). -/
def vecEnv (v : String) (l : List (BitVec 32)) :
    Env × Mem × Layout → Prop :=
  fun st => envLookup st.1 v = some (.stdVecVal l)

/-- Cursor variable `x` holds the natural number `n`. The
    `BitVec 64` witness is existentially hidden: callers state
    and combine cursor facts without `.toNat` plumbing. -/
def cursorAt (x : String) (n : Nat) :
    Env × Mem × Layout → Prop :=
  fun st => ∃ b : BitVec 64,
    envLookup st.1 x = some (.u64 b) ∧ b.toNat = n

/-- Pinned memory snapshot for a borrowed vector: the layout maps
    `v` to block `(a, t)` and the block holds the length word
    plus the words `l` (the single-`mutBorrow` footprint shared
    by the compacting slices). -/
def vecSnapshot (v : String) (l : List (BitVec 32)) :
    Env × Mem × Layout → Prop :=
  fun st => ∃ a t n, layoutLookup st.2.2 v = some (a, t) ∧
    memFind st.2.1 a = some ⟨t, true, n :: l⟩ ∧
    n = BitVec.ofNat 32 l.length

/-- Introduce a `vecEnv` fact from its lookup equation. -/
theorem vecEnv_of (v : String) (l : List (BitVec 32))
    (ρ : Env) (m : Mem) (π : Layout)
    (h : envLookup ρ v = some (.stdVecVal l)) :
    vecEnv v l (ρ, m, π) := h

/-- Introduce a `cursorAt` fact from a lookup plus the
    `toNat` bridge (the two hypotheses the transfer proofs
    already thread as `hr`/`hrN`). -/
theorem cursorAt_of (x : String) (n : Nat)
    (ρ : Env) (m : Mem) (π : Layout) (b : BitVec 64)
    (h : envLookup ρ x = some (.u64 b)) (hn : b.toNat = n) :
    cursorAt x n (ρ, m, π) := ⟨b, h, hn⟩

/-- Introduce a `vecSnapshot` fact from its three equations
    (layout pin, block find, length word). -/
theorem vecSnapshot_of (v : String) (l : List (BitVec 32))
    (ρ : Env) (m : Mem) (π : Layout) (a t : Nat) (n : BitVec 32)
    (hlay : layoutLookup π v = some (a, t))
    (hmem : memFind m a = some ⟨t, true, n :: l⟩)
    (hn : n = BitVec.ofNat 32 l.length) :
    vecSnapshot v l (ρ, m, π) := ⟨a, t, n, hlay, hmem, hn⟩

/-- Program-level `vecSet` store with framing: records `xv`
    at cursor `i` into the snapshot, preserves one framed cell
    (address-distinct) across the store. Thin wrapper over
    `memEvalStmtFuel_vecSet` (the store leg every vector loop
    with stores re-proves by hand): the snapshot premise is the
    `vecSnapshot` vocabulary, the post re-pins it via
    `memStore_cellsAt_pin` (length word untouched — the store
    lands at `i+1`), and the framed cell rides
    `memFind_memStore_other`. First-order premises only, no new
    semantics. -/
theorem htripleProg_vecSet_at (prog : Prog) (F : Nat)
    (x : String) (ie ve : CExpr)
    (ρ : Env) (m : Mem) (π : Layout)
    (i : BitVec 64) (xv : BitVec 32) (a t : Nat)
    (l : List (BitVec 32)) (w : BitVec 32) (n : BitVec 32)
    (m' : Mem) (ρ' : Env)
    (b : Addr) (t₂ : Nat) (qv : BitVec 32)
    (hi : memEvalExpr ie ρ m π = .ok (.u64 i))
    (hv : memEvalExpr ve ρ m π = .ok (.i32 xv))
    (hvec : envLookup ρ x = some (.stdVecVal l))
    (hlay : layoutLookup π x = some (a, t))
    (hget : l[i.toNat]? = some w)
    (hmem : memFind m a = some ⟨t, true, n :: l⟩)
    (hn : n = BitVec.ofNat 32 l.length)
    (hmstore : memStore m a t (i.toNat + 1) xv = .ok m')
    (hu : envUpdate ρ x (.stdVecVal (l.set i.toNat xv)) = some ρ')
    (hq : cellAt m b t₂ qv) (hne : b ≠ a) :
    HTripleProgAt prog F (fun st => st = (ρ, m, π))
      (.vecSet x ie ve)
      (fun st o => st = (ρ', m', π) ∧ o = .fellThrough ∧
        vecSnapshot x (l.set i.toNat xv) st ∧
        cellAt m' b t₂ qv) := by
  intro ρ₀ m₀ π₀ hP
  simp only [Prod.mk.injEq] at hP
  obtain ⟨rfl, rfl, rfl⟩ := hP
  have hev : memEvalProgStmt prog F (.vecSet x ie ve) ρ₀ m₀ π₀ =
      .ok ((ρ', m', π₀), .fellThrough) := by
    simpa [memEvalProgStmt] using
      (memEvalStmtFuel_vecSet F x ie ve ρ₀ m₀ π₀ i xv a t l w m' ρ'
        hi hv hvec hlay hget hmstore hu)
  have hlt : i.toNat + 1 < (n :: l).length := by
    have hblt : i.toNat < l.length := by
      by_cases h : i.toNat < l.length
      · exact h
      · have hle' : l.length ≤ i.toNat := by omega
        rw [List.getElem?_eq_none hle'] at hget
        cases hget
    simp only [List.length_cons]
    omega
  have hcells : cellsAt m₀ a t (n :: l) := hmem
  obtain ⟨m'', hmstore', hmem'⟩ :=
    memStore_cellsAt_pin m₀ a t xv hcells hlt
  have hm' : m'' = m' := by
    have h := hmstore
    rw [hmstore'] at h
    simpa using h
  rw [hm'] at hmem'
  have hn' : n = BitVec.ofNat 32 (l.set i.toNat xv).length := by
    rw [List.length_set]; exact hn
  refine ⟨ρ', m', π₀, .fellThrough, hev, rfl, rfl, ?_, ?_⟩
  · exact vecSnapshot_of x (l.set i.toNat xv) ρ' m' π₀ a t n
      hlay hmem' hn'
  · unfold cellAt
    rw [memFind_memStore_other _ _ a b t (i.toNat + 1) _ hmstore hne]
    exact hq

/-- Fuel-generic program-level `vecSet` store, pointwise from the
    fixed-fuel rule. -/
theorem htripleProg_vecSet (prog : Prog)
    (x : String) (ie ve : CExpr)
    (ρ : Env) (m : Mem) (π : Layout)
    (i : BitVec 64) (xv : BitVec 32) (a t : Nat)
    (l : List (BitVec 32)) (w : BitVec 32) (n : BitVec 32)
    (m' : Mem) (ρ' : Env)
    (b : Addr) (t₂ : Nat) (qv : BitVec 32)
    (hi : memEvalExpr ie ρ m π = .ok (.u64 i))
    (hv : memEvalExpr ve ρ m π = .ok (.i32 xv))
    (hvec : envLookup ρ x = some (.stdVecVal l))
    (hlay : layoutLookup π x = some (a, t))
    (hget : l[i.toNat]? = some w)
    (hmem : memFind m a = some ⟨t, true, n :: l⟩)
    (hn : n = BitVec.ofNat 32 l.length)
    (hmstore : memStore m a t (i.toNat + 1) xv = .ok m')
    (hu : envUpdate ρ x (.stdVecVal (l.set i.toNat xv)) = some ρ')
    (hq : cellAt m b t₂ qv) (hne : b ≠ a) :
    HTripleProg prog (fun st => st = (ρ, m, π))
      (.vecSet x ie ve)
      (fun st o => st = (ρ', m', π) ∧ o = .fellThrough ∧
        vecSnapshot x (l.set i.toNat xv) st ∧
        cellAt m' b t₂ qv) := by
  intro F
  exact htripleProg_vecSet_at prog F x ie ve ρ m π i xv a t l w n
    m' ρ' b t₂ qv hi hv hvec hlay hget hmem hn hmstore hu hq hne

/-- Program-level pure-`let_` triple: binding a pure value
    extends the environment, memory and layout untouched.
    Allocating right-hand sides are excluded by constructor
    discrimination, mirroring `htriple_let` one level up. -/
theorem htripleProg_let_at (prog : Prog) (F : Nat)
    (x : String) (ty : CType) (e : CExpr)
    (ρ : Env) (m : Mem) (π : Layout) (v : Value)
    (hnot : ∀ se, e ≠ .vnew se)
    (hnotBox : ∀ se, e ≠ .boxNew se)
    (hnotGrow : ∀ ce, e ≠ .vgrowNew ce)
    (hnotN : e ≠ .nnew)
    (h : memEvalExpr e ρ m π = evalExpr e ρ)
    (hv : evalExpr e ρ = .ok v) :
    HTripleProgAt prog F (fun st => st = (ρ, m, π)) (.let_ x ty e)
      (fun st o => st = (envExtend ρ x v, m, π) ∧
        o = .fellThrough) := by
  intro ρ₀ m₀ π₀ hP
  obtain ⟨rfl, rfl, rfl⟩ := hP
  have hev : memEvalProgStmt prog F (.let_ x ty e) ρ m π =
      .ok ((envExtend ρ x v, m, π), .fellThrough) := by
    rw [memEvalProgStmt_let_fb prog F x ty e ρ m π]
    exact memEvalStmtFuel_let_pure F x ty e ρ m π v
      hnot hnotBox hnotGrow hnotN h hv
  exact ⟨_, _, _, _, hev, rfl, rfl⟩
