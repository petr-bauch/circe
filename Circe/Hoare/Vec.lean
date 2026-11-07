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
