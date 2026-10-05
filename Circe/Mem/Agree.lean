/-
Circe.Mem.Agree — per-leaf transfer instances (`oracleNoalias →
memEval = Eval`), statement-agreement combinators, lockstep bridges,
and the N4d-iv-b1 statement agreement, over `Circe.Mem.Model`.
-/
import Circe.Base
import Circe.CoreIR
import Circe.Eval
import Circe.Mem.Model

/-! ## Per-leaf transfer (`oracleNoalias → memEval = Eval`) -/

/-- `add` binding: owned scalars, empty layout. -/
theorem bindMemArgs_add (a b : BitVec 32) :
    bindMemArgs [{ name := "a", ty := .i 32, role := .owned },
                 { name := "b", ty := .i 32, role := .owned }]
      [.i32 a, .i32 b] emptyMem =
      some ([("a", .i32 a), ("b", .i32 b)], emptyMem, []) := by
  rfl

/-- `add` entry footprints are trivially disjoint (nothing pinned). -/
theorem oracleNoalias_add (a b : BitVec 32) :
    oracleNoalias
      ⟨"add", [{ name := "a", ty := .i 32, role := .owned },
               { name := "b", ty := .i 32, role := .owned }], .i 32,
       .return_ (.add (.var "a") (.var "b"))⟩ [.i32 a, .i32 b] := by
  exact ⟨_, _, _, bindMemArgs_add a b, layoutNoAlias_nil⟩

/-- Transfer for `add` (any fuel): the body is a pure `return_`, so
    memory is untouched and both sides reduce identically. -/
theorem memTransfer_add (F : Nat) (a b : BitVec 32)
    (_h : oracleNoalias
      ⟨"add", [{ name := "a", ty := .i 32, role := .owned },
               { name := "b", ty := .i 32, role := .owned }], .i 32,
       .return_ (.add (.var "a") (.var "b"))⟩ [.i32 a, .i32 b]) :
    memEvalFuncFuel F
      ⟨"add", [{ name := "a", ty := .i 32, role := .owned },
               { name := "b", ty := .i 32, role := .owned }], .i 32,
       .return_ (.add (.var "a") (.var "b"))⟩ [.i32 a, .i32 b] =
    evalFuncFuel F
      ⟨"add", [{ name := "a", ty := .i 32, role := .owned },
               { name := "b", ty := .i 32, role := .owned }], .i 32,
       .return_ (.add (.var "a") (.var "b"))⟩ [.i32 a, .i32 b] := by
  have hb := bindMemArgs_add a b
  have ha : envLookup [("a", .i32 a), ("b", .i32 b)] "a" = some (.i32 a) := by
    simp [envLookup]
  have hbb : envLookup [("a", .i32 a), ("b", .i32 b)] "b" = some (.i32 b) := by
    simp [envLookup, show ("b" : String) ≠ "a" by decide]
  simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hb]
  cases F <;>
    simp only [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      evalStmtFuel, evalStmtZero, evalStmtWith, memEvalExpr, evalExpr,
      ha, hbb] <;>
    (cases h : checkedAddI32 a b <;> rfl)

/-- `incr` binding: the borrow is functionalized (value in, value out),
    so there is no footprint and the layout is empty. -/
theorem bindMemArgs_incr (p : BitVec 32) :
    bindMemArgs [{ name := "p", ty := .i 32, role := .mutBorrow 0 }]
      [.i32 p] emptyMem =
      some ([("p", .i32 p)], emptyMem, []) := by
  rfl

/-- Transfer for `incr` (any fuel): same pure shape as `add`. -/
theorem memTransfer_incr (F : Nat) (p : BitVec 32)
    (_h : oracleNoalias
      ⟨"incr", [{ name := "p", ty := .i 32, role := .mutBorrow 0 }], .i 32,
       .return_ (.add (.var "p") (.lit (.i32 1)))⟩ [.i32 p]) :
    memEvalFuncFuel F
      ⟨"incr", [{ name := "p", ty := .i 32, role := .mutBorrow 0 }], .i 32,
       .return_ (.add (.var "p") (.lit (.i32 1)))⟩ [.i32 p] =
    evalFuncFuel F
      ⟨"incr", [{ name := "p", ty := .i 32, role := .mutBorrow 0 }], .i 32,
       .return_ (.add (.var "p") (.lit (.i32 1)))⟩ [.i32 p] := by
  have hb := bindMemArgs_incr p
  have hp : envLookup [("p", .i32 p)] "p" = some (.i32 p) := by
    simp [envLookup]
  simp only [memEvalFuncFuel, evalFuncFuel, bindArgs, hb]
  cases F <;>
    simp only [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      evalStmtFuel, evalStmtZero, evalStmtWith, memEvalExpr, evalExpr,
      litVal, hp] <;>
    (cases h : checkedAddI32 p 1#32 <;> rfl)

/-! ## Statement agreement combinators (straight-line code) -/

/-- `skip` agrees with memory untouched. -/
theorem memEvalStmtFuel_skip (f : Nat) (ρ : Env) (m : Mem) (π : Layout) :
    memEvalStmtFuel f .skip ρ m π =
      ((evalStmtFuel f .skip ρ).map fun (ρ', o) => ((ρ', m, π), o)) := by
  cases f <;> rfl

/-- `seq` agrees when both components do (memory threaded). -/
theorem memEvalStmtFuel_seq (f : Nat) (a b : CStmt) (ρ : Env)
    (m : Mem) (π : Layout) (ρ₁ : Env) (m₁ : Mem) (π₁ : Layout)
    (ρ₂ : Env) (m₂ : Mem) (π₂ : Layout) (o : Outcome)
    (ha : memEvalStmtFuel f a ρ m π = .ok ((ρ₁, m₁, π₁), .fellThrough))
    (hb : memEvalStmtFuel f b ρ₁ m₁ π₁ = .ok ((ρ₂, m₂, π₂), o)) :
    memEvalStmtFuel f (.seq a b) ρ m π = .ok ((ρ₂, m₂, π₂), o) := by
  cases f with
  | zero =>
    simp only [memEvalStmtFuel, memEvalStmtZero] at ha hb ⊢
    simp only [memEvalStmtWith, ha, hb]
  | succ n =>
    simp only [memEvalStmtFuel] at ha hb ⊢
    simp only [memEvalStmtWith, ha, hb]

/-- `seq` propagates first-statement errors (any fuel; mirrors
    `evalStmtFuel_seq_err`). -/
theorem memEvalStmtFuel_seq_err (f : Nat) (a b : CStmt) (ρ : Env)
    (m : Mem) (π : Layout) (e : Panic)
    (h : memEvalStmtFuel f a ρ m π = .error e) :
    memEvalStmtFuel f (.seq a b) ρ m π = .error e := by
  cases f with
  | zero =>
    simp only [memEvalStmtFuel, memEvalStmtZero] at h ⊢
    simp only [memEvalStmtWith, h]
  | succ g =>
    simp only [memEvalStmtFuel] at h ⊢
    simp only [memEvalStmtWith, h]

/-- `seq` threads the environment on fall-through (any fuel, no
    condition on the second statement; mirrors
    `evalStmtFuel_seq_fallthrough`). -/
theorem memEvalStmtFuel_seq_fallthrough (f : Nat) (a b : CStmt) (ρ : Env)
    (m : Mem) (π : Layout) (ρ₁ : Env) (m₁ : Mem) (π₁ : Layout)
    (ha : memEvalStmtFuel f a ρ m π = .ok ((ρ₁, m₁, π₁), .fellThrough)) :
    memEvalStmtFuel f (.seq a b) ρ m π =
      memEvalStmtFuel f b ρ₁ m₁ π₁ := by
  cases f with
  | zero =>
    simp only [memEvalStmtFuel, memEvalStmtZero] at ha ⊢
    simp only [memEvalStmtWith, ha]
  | succ g =>
    simp only [memEvalStmtFuel] at ha ⊢
    simp only [memEvalStmtWith, ha]

/-- Pure `let_` agrees when the bound expression does (`vnew` takes
    the allocating arm instead — see `memEvalStmtFuel_let_vnew`;
    `boxNew` takes its own allocating arm — see
    `memEvalStmtFuel_let_boxNew`). -/
theorem memEvalStmtFuel_let_pure (f : Nat) (x : String) (ty : CType)
    (e : CExpr) (ρ : Env) (m : Mem) (π : Layout) (v : Value)
    (hnot : ∀ se, e ≠ .vnew se)
    (hnotBox : ∀ se, e ≠ .boxNew se)
    (hnotGrow : ∀ ce, e ≠ .vgrowNew ce)
    (h : memEvalExpr e ρ m π = evalExpr e ρ)
    (hv : evalExpr e ρ = .ok v) :
    memEvalStmtFuel f (.let_ x ty e) ρ m π =
      .ok ((((x, v) :: ρ, m, π)), .fellThrough) := by
  match e with
  | .vnew se => exact absurd rfl (hnot se)
  | .boxNew se => exact absurd rfl (hnotBox se)
  | .vgrowNew ce => exact absurd rfl (hnotGrow ce)
  | _ =>
    cases f <;> simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, h, hv]

/-- Pure `let_` propagates expression errors (any fuel; mirrors
    `evalStmtFuel_let_err`; allocating arms are excluded as in
    `memEvalStmtFuel_let_pure`). -/
theorem memEvalStmtFuel_let_err (f : Nat) (x : String) (ty : CType)
    (e : CExpr) (ρ : Env) (m : Mem) (π : Layout) (err : Panic)
    (hnot : ∀ se, e ≠ .vnew se)
    (hnotBox : ∀ se, e ≠ .boxNew se)
    (hnotGrow : ∀ ce, e ≠ .vgrowNew ce)
    (h : memEvalExpr e ρ m π = .error err) :
    memEvalStmtFuel f (.let_ x ty e) ρ m π = .error err := by
  match e with
  | .vnew se => exact absurd rfl (hnot se)
  | .boxNew se => exact absurd rfl (hnotBox se)
  | .vgrowNew ce => exact absurd rfl (hnotGrow ce)
  | _ =>
    cases f <;> simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, h]

/-- Allocating `let_` (`vnew`): the value side runs `vecNew`, the
    memory side additionally pins a fresh block holding the same words,
    extending the layout. -/
theorem memEvalStmtFuel_let_vnew (f : Nat) (x : String) (ty : CType)
    (se : CExpr) (ρ : Env) (m : Mem) (π : Layout) (n : BitVec 32)
    (v : Vec32)
    (h : memEvalExpr se ρ m π = evalExpr se ρ)
    (hse : evalExpr se ρ = .ok (.u32 n))
    (hnew : vecNew n.toNat = .ok v) :
    memEvalStmtFuel f (.let_ x ty (.vnew se)) ρ m π =
      let (m', a) := memAllocData m v.val
      .ok (((x, .vecVal v) :: ρ, m', (x, a, a) :: π), .fellThrough) := by
  cases f <;>
    simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, h, hse, hnew]

/-- Allocating `let_` (`vnew` over a `u64` size): the value side runs
    `vecNew64`, the memory side pins a fresh 64-bit block. -/
theorem memEvalStmtFuel_let_vnew64 (f : Nat) (x : String) (ty : CType)
    (se : CExpr) (ρ : Env) (m : Mem) (π : Layout) (n : BitVec 64)
    (v : Vec64)
    (h : memEvalExpr se ρ m π = evalExpr se ρ)
    (hse : evalExpr se ρ = .ok (.u64 n))
    (hnew : vecNew64 n.toNat = .ok v) :
    memEvalStmtFuel f (.let_ x ty (.vnew se)) ρ m π =
      let (m', a) := memAllocData64 m v.val
      .ok (((x, .vecVal64 v) :: ρ, m', (x, a, a) :: π), .fellThrough) := by
  cases f <;>
    simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, h, hse, hnew]

/-- Allocating `let_` (`boxNew`): the value side runs `boxNew`, the
    memory side additionally pins a fresh single-word block holding
    the box value, extending the layout (M2c). -/
theorem memEvalStmtFuel_let_boxNew (f : Nat) (x : String) (ty : CType)
    (se : CExpr) (ρ : Env) (m : Mem) (π : Layout) (xv : BitVec 32)
    (b : Box32)
    (h : memEvalExpr se ρ m π = evalExpr se ρ)
    (hse : evalExpr se ρ = .ok (.i32 xv))
    (hnew : boxNew xv = .ok b) :
    memEvalStmtFuel f (.let_ x ty (.boxNew se)) ρ m π =
      let (m', a) := memAllocData m [b.val]
      .ok (((x, .boxVal b) :: ρ, m', (x, a, a) :: π), .fellThrough) := by
  cases f <;>
    simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, h, hse, hnew]

/-- Allocating `let_` (`vgrowNew` over a `u64` capacity): the value
    side builds the empty triple over fresh zeroed storage, the memory
    side pins a fresh block holding the two header words plus the
    storage words (N4d-iv-b1). -/
theorem memEvalStmtFuel_let_vgrowNew (f : Nat) (x : String) (ty : CType)
    (ce : CExpr) (ρ : Env) (m : Mem) (π : Layout) (n : BitVec 64)
    (v : Vec32)
    (h : memEvalExpr ce ρ m π = evalExpr ce ρ)
    (hce : evalExpr ce ρ = .ok (.u64 n))
    (hnew : vecNew n.toNat = .ok v) :
    memEvalStmtFuel f (.let_ x ty (.vgrowNew ce)) ρ m π =
      let (m', a) := memAllocData m
        ((BitVec.ofNat 32 0) :: (BitVec.ofNat 32 n.toNat) :: v.val)
      .ok (((x, .stdVecOwned v 0 n.toNat) :: ρ, m', (x, a, a) :: π),
        .fellThrough) := by
  cases f <;>
    simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, h, hce, hnew]

/-! ## Lockstep bridges (value op ⟺ memory op under the pin invariant) -/

/-- Pin invariant for one heap block: the layout pins `x` to `(a, a)`,
    the block carries the matching tag, is live, holds exactly the
    value's words, and the value token is live. Preserved by lockstep
    writes, consumed by `vfree`. -/
def VecPinInvariant (m : Mem) (a : Addr) (x : String) (blk : Vec32)
    (π : Layout) : Prop :=
  memFind m a = some ⟨a, true, blk.val⟩ ∧
  layoutLookup π x = some (a, a) ∧
  blk.freed = false

/-- Lookup after a shadowing update at `a` finds the new block
    (updates cons, newest binding wins; stale entries underneath are
    unreachable since allocation never reuses an address). -/
theorem memFind_cons_hit (n : Nat) (bs : List (Nat × Block))
    (g64 : List (Nat × Block64)) (a : Addr)
    (b : Block) :
    memFind ⟨n, (a, b) :: bs, g64⟩ a = some b := by
  simp [memFind]

/-- Shadowing updates preserve every other address. -/
theorem memFind_cons_miss (n : Nat) (bs : List (Nat × Block))
    (g64 : List (Nat × Block64)) (a a' : Addr)
    (b : Block) (h : a' ≠ a) :
    memFind ⟨n, (a, b) :: bs, g64⟩ a' = memFind ⟨n, bs, g64⟩ a' := by
  have hbe : (a' == a) = false := by
    cases heq : (a' == a) with
    | true => exact absurd (beq_iff_eq.mp heq) h
    | false => rfl
  simp [memFind, hbe]

/-- Shadowing 64-bit updates hit. -/
theorem memFind64_cons_hit (n : Nat) (bs : List (Nat × Block))
    (g64 : List (Nat × Block64)) (a : Addr)
    (b : Block64) :
    memFind64 ⟨n, bs, (a, b) :: g64⟩ a = some b := by
  simp [memFind64]

/-- Shadowing 64-bit updates preserve every other address. -/
theorem memFind64_cons_miss (n : Nat) (bs : List (Nat × Block))
    (g64 : List (Nat × Block64)) (a a' : Addr)
    (b : Block64) (h : a' ≠ a) :
    memFind64 ⟨n, bs, (a, b) :: g64⟩ a' = memFind64 ⟨n, bs, g64⟩ a' := by
  have hbe : (a' == a) = false := by
    cases heq : (a' == a) with
    | true => exact absurd (beq_iff_eq.mp heq) h
    | false => rfl
  simp [memFind64, hbe]

/-- `memStore` preserves every other address (two-block loops: writing
    one block never disturbs the other's pin fact). -/
theorem memFind_memStore_other (m m' : Mem) (a b : Addr) (t i : Nat)
    (x : BitVec 32)
    (hstore : memStore m a t i x = .ok m') (hne : b ≠ a) :
    memFind m' b = memFind m b := by
  unfold memStore at hstore
  split at hstore
  · cases hstore
  · next blk hfind =>
    split at hstore
    · cases hstore
    · next htag =>
      split at hstore
      · cases hstore
      · next hlive =>
        split at hstore
        · next hblen =>
          cases hstore
          exact memFind_cons_miss _ _ _ _ _ _ hne
        · cases hstore

/-- `memFree` preserves every other address (freeing one block never
    disturbs the other's pin fact). -/
theorem memFind_memFree_other (m m' : Mem) (a b : Addr) (t : Nat)
    (hfree : memFree m a t = .ok m') (hne : b ≠ a) :
    memFind m' b = memFind m b := by
  unfold memFree at hfree
  split at hfree
  · cases hfree
  · next blk hfind =>
    split at hfree
    · cases hfree
    · next htag =>
      split at hfree
      · cases hfree
      · next hlive =>
        cases hfree
        exact memFind_cons_miss _ _ _ _ _ _ hne

/-- `memStore64` preserves every other 64-bit address. -/
theorem memFind64_memStore64_other (m m' : Mem) (a b : Addr) (t i : Nat)
    (x : BitVec 64)
    (hstore : memStore64 m a t i x = .ok m') (hne : b ≠ a) :
    memFind64 m' b = memFind64 m b := by
  unfold memStore64 at hstore
  split at hstore
  · cases hstore
  · next blk hfind =>
    split at hstore
    · cases hstore
    · next htag =>
      split at hstore
      · cases hstore
      · next hlive =>
        split at hstore
        · next hblen =>
          cases hstore
          exact memFind64_cons_miss _ _ _ _ _ _ hne
        · cases hstore

/-- `memFree64` preserves every other 64-bit address. -/
theorem memFind64_memFree64_other (m m' : Mem) (a b : Addr) (t : Nat)
    (hfree : memFree64 m a t = .ok m') (hne : b ≠ a) :
    memFind64 m' b = memFind64 m b := by
  unfold memFree64 at hfree
  split at hfree
  · cases hfree
  · next blk hfind =>
    split at hfree
    · cases hfree
    · next htag =>
      split at hfree
      · cases hfree
      · next hlive =>
        cases hfree
        exact memFind64_cons_miss _ _ _ _ _ _ hne

/-- A successful `vecSet` carries its bounds + liveness. -/
theorem vecSet_ok_bound (b : Vec32) (i : Nat) (x : BitVec 32) (b' : Vec32)
    (h : vecSet b i x = .ok b') : i < b.val.length ∧ b.freed = false := by
  unfold vecSet at h
  by_cases hf : b.freed = true
  · simp [hf] at h
  · by_cases hb : i < b.val.length
    · exact ⟨hb, Bool.eq_false_iff.mpr hf⟩
    · simp [hf, hb] at h

/-- A successful 64-bit `vecSet64` carries its bounds + liveness. -/
theorem vecSet64_ok_bound (b : Vec64) (i : Nat) (x : BitVec 64) (b' : Vec64)
    (h : vecSet64 b i x = .ok b') : i < b.val.length ∧ b.freed = false := by
  unfold vecSet64 at h
  by_cases hf : b.freed = true
  · simp [hf] at h
  · by_cases hb : i < b.val.length
    · exact ⟨hb, Bool.eq_false_iff.mpr hf⟩
    · simp [hf, hb] at h

/-- 64-bit `vset` lockstep: `vecSet64` and `memStore64` succeed together
    with synced state. -/
theorem vset64_lockstep (m : Mem) (a t : Nat) (b : Vec64) (i : Nat)
    (x : BitVec 64) (blk : Block64) (b' : Vec64)
    (hfind : memFind64 m a = some blk) (htag : blk.tag = t)
    (hlive : blk.live = true) (hdata : blk.data = b.val)
    (hunfreed : b.freed = false)
    (hset : vecSet64 b i x = .ok b') :
    ∃ m', memStore64 m a t i x = .ok m' ∧
      memFind64 m' a = some ⟨t, true, b'.val⟩ := by
  obtain ⟨hb, _⟩ := vecSet64_ok_bound b i x b' hset
  have hset' : vecSet64 b i x = .ok ⟨b.val.set i x, false⟩ :=
    vecSet64_ok b i x hunfreed hb
  rw [hset'] at hset
  cases hset
  show ∃ m', memStore64 m a t i x = .ok m' ∧
    memFind64 m' a = some ⟨t, true, (b.val.set i x)⟩
  have hblen : i < blk.data.length := by rw [hdata]; exact hb
  have hstore : memStore64 m a t i x =
      .ok ⟨m.next, m.blocks,
        (a, ⟨blk.tag, blk.live, blk.data.set i x⟩) ::
        m.blocks64⟩ := by
    simp [memStore64, hfind, htag, hlive, hblen]
  refine ⟨_, hstore, ?_⟩
  have hhit := memFind64_cons_hit m.next m.blocks m.blocks64 a
    ⟨blk.tag, blk.live, blk.data.set i x⟩
  simpa only [htag, hlive, hdata] using hhit

/-- 64-bit `vfree` lockstep: `vecFree64` and `memFree64` consume their
    tokens together. -/
theorem vfree64_lockstep (m : Mem) (a t : Nat) (b : Vec64) (blk : Block64)
    (b' : Vec64)
    (hfind : memFind64 m a = some blk) (htag : blk.tag = t)
    (hlive : blk.live = true) (hdata : blk.data = b.val)
    (hunfreed : b.freed = false)
    (hfree : vecFree64 b = .ok b') :
    ∃ m', memFree64 m a t = .ok m' ∧
      memFind64 m' a = some ⟨t, false, b.val⟩ := by
  have hfree' : b' = ⟨b.val, true⟩ := by
    rw [vecFree64_ok b hunfreed] at hfree
    cases hfree
    rfl
  subst hfree'
  show ∃ m', memFree64 m a t = .ok m' ∧
    memFind64 m' a = some ⟨t, false, b.val⟩
  have hmfree : memFree64 m a t =
      .ok ⟨m.next, m.blocks, (a, ⟨blk.tag, false, blk.data⟩) ::
        m.blocks64⟩ := by
    simp [memFree64, hfind, htag, hlive]
  refine ⟨_, hmfree, ?_⟩
  have hhit := memFind64_cons_hit m.next m.blocks m.blocks64 a
    ⟨blk.tag, false, blk.data⟩
  simpa only [htag, hdata] using hhit

/-- `vset` lockstep: under the pin invariant (matching tag, live block,
    block data = value words, live token), `vecSet` and `memStore`
    succeed together with synced state. -/
theorem vset_lockstep (m : Mem) (a t : Nat) (b : Vec32) (i : Nat)
    (x : BitVec 32) (blk : Block) (b' : Vec32)
    (hfind : memFind m a = some blk) (htag : blk.tag = t)
    (hlive : blk.live = true) (hdata : blk.data = b.val)
    (hunfreed : b.freed = false)
    (hset : vecSet b i x = .ok b') :
    ∃ m', memStore m a t i x = .ok m' ∧
      memFind m' a = some ⟨t, true, b'.val⟩ := by
  obtain ⟨hb, _⟩ := vecSet_ok_bound b i x b' hset
  have hset' : vecSet b i x = .ok ⟨b.val.set i x, false⟩ :=
    vecSet_ok b i x hunfreed hb
  rw [hset'] at hset
  cases hset
  show ∃ m', memStore m a t i x = .ok m' ∧
    memFind m' a = some ⟨t, true, (b.val.set i x)⟩
  have hblen : i < blk.data.length := by rw [hdata]; exact hb
  have hstore : memStore m a t i x =
      .ok ⟨m.next, (a, ⟨blk.tag, blk.live, blk.data.set i x⟩) ::
        m.blocks, m.blocks64⟩ := by
    simp [memStore, hfind, htag, hlive, hblen]
  refine ⟨_, hstore, ?_⟩
  have hhit := memFind_cons_hit m.next m.blocks m.blocks64 a
    ⟨blk.tag, blk.live, blk.data.set i x⟩
  simpa only [htag, hlive, hdata] using hhit

/-- `vfree` lockstep: under the pin invariant, `vecFree` and `memFree`
    consume their tokens together. -/
theorem vfree_lockstep (m : Mem) (a t : Nat) (b : Vec32) (blk : Block)
    (b' : Vec32)
    (hfind : memFind m a = some blk) (htag : blk.tag = t)
    (hlive : blk.live = true) (hdata : blk.data = b.val)
    (hunfreed : b.freed = false)
    (hfree : vecFree b = .ok b') :
    ∃ m', memFree m a t = .ok m' ∧
      memFind m' a = some ⟨t, false, b.val⟩ := by
  have hfree' : b' = ⟨b.val, true⟩ := by
    rw [vecFree_ok b hunfreed] at hfree
    cases hfree
    rfl
  subst hfree'
  show ∃ m', memFree m a t = .ok m' ∧
    memFind m' a = some ⟨t, false, b.val⟩
  have hmfree : memFree m a t =
      .ok ⟨m.next, (a, ⟨blk.tag, false, blk.data⟩) :: m.blocks,
        m.blocks64⟩ := by
    simp [memFree, hfind, htag, hlive]
  refine ⟨_, hmfree, ?_⟩
  have hhit := memFind_cons_hit m.next m.blocks m.blocks64 a
    ⟨blk.tag, false, blk.data⟩
  simpa only [htag, hdata] using hhit

/-- Setting past the two header words preserves them: the store lands
    in the storage suffix exactly where `vecSet` lands in `b.val`
    (N4d-iv-b1). -/
theorem header_set_succ (l c : BitVec 32) (w : List (BitVec 32))
    (i : Nat) (x : BitVec 32) :
    (l :: c :: w).set (i + 2) x = l :: c :: (w.set i x) := by
  have e : i + 2 = (i + 1) + 1 := by omega
  rw [e, List.set_cons_succ, List.set_cons_succ]

/-- Reading past the two header words lands in the storage suffix
    exactly where the buffer list is read (N4d-iv-b1; the `get?`
    sibling of `header_set_succ`). -/
theorem header_get_succ (l c : BitVec 32) (w : List (BitVec 32))
    (i : Nat) :
    (l :: c :: w)[i + 2]? = w[i]? := by
  cases i with
  | zero => rfl
  | succ _ => rfl

/-- `vgrowSet` lockstep: under the triple pin invariant (matching tag,
    live block, header words plus exactly the buffer words), `vecSet`
    and the header-shifted `memStore` update together (N4d-iv-b1;
    mirrors `vset_lockstep`). -/
theorem vgrowSet_lockstep (m : Mem) (a t : Nat) (b : Vec32)
    (len cap i : Nat) (x : BitVec 32) (blk : Block) (b' : Vec32)
    (hfind : memFind m a = some blk) (htag : blk.tag = t)
    (hlive : blk.live = true)
    (hdata : blk.data = (BitVec.ofNat 32 len) ::
      (BitVec.ofNat 32 cap) :: b.val)
    (hunfreed : b.freed = false)
    (hset : vecSet b i x = .ok b') :
    ∃ m', memStore m a t (i + 2) x = .ok m' ∧
      memFind m' a = some ⟨t, true, (BitVec.ofNat 32 len) ::
        (BitVec.ofNat 32 cap) :: b'.val⟩ := by
  obtain ⟨hb, _⟩ := vecSet_ok_bound b i x b' hset
  have hset' : vecSet b i x = .ok ⟨b.val.set i x, false⟩ :=
    vecSet_ok b i x hunfreed hb
  rw [hset'] at hset
  cases hset
  show ∃ m', memStore m a t (i + 2) x = .ok m' ∧
    memFind m' a = some ⟨t, true, (BitVec.ofNat 32 len) ::
      (BitVec.ofNat 32 cap) :: (b.val.set i x)⟩
  have hblen : i + 2 < blk.data.length := by rw [hdata]; simp; omega
  have hstore : memStore m a t (i + 2) x =
      .ok ⟨m.next, (a, ⟨blk.tag, blk.live, blk.data.set (i + 2) x⟩) ::
        m.blocks, m.blocks64⟩ := by
    simp [memStore, hfind, htag, hlive, hblen]
  rw [hdata, header_set_succ] at hstore
  refine ⟨_, hstore, ?_⟩
  have hhit := memFind_cons_hit m.next m.blocks m.blocks64 a
    ⟨blk.tag, blk.live, blk.data.set (i + 2) x⟩
  rw [hdata, header_set_succ] at hhit
  simpa only [htag, hlive] using hhit

/-- `vgrowFree` lockstep: under the triple pin invariant, `vecFree`
    and `memFree` consume their tokens together, keeping the header
    words (N4d-iv-b1; mirrors `vfree_lockstep`). -/
theorem vgrowFree_lockstep (m : Mem) (a t : Nat) (b : Vec32)
    (len cap : Nat) (blk : Block) (b' : Vec32)
    (hfind : memFind m a = some blk) (htag : blk.tag = t)
    (hlive : blk.live = true)
    (hdata : blk.data = (BitVec.ofNat 32 len) ::
      (BitVec.ofNat 32 cap) :: b.val)
    (hunfreed : b.freed = false)
    (hfree : vecFree b = .ok b') :
    ∃ m', memFree m a t = .ok m' ∧
      memFind m' a = some ⟨t, false, (BitVec.ofNat 32 len) ::
        (BitVec.ofNat 32 cap) :: b.val⟩ := by
  have hfree' : b' = ⟨b.val, true⟩ := by
    rw [vecFree_ok b hunfreed] at hfree
    cases hfree
    rfl
  subst hfree'
  show ∃ m', memFree m a t = .ok m' ∧
    memFind m' a = some ⟨t, false, (BitVec.ofNat 32 len) ::
      (BitVec.ofNat 32 cap) :: b.val⟩
  have hmfree : memFree m a t =
      .ok ⟨m.next, (a, ⟨blk.tag, false, blk.data⟩) :: m.blocks,
        m.blocks64⟩ := by
    simp [memFree, hfind, htag, hlive]
  refine ⟨_, hmfree, ?_⟩
  have hhit := memFind_cons_hit m.next m.blocks m.blocks64 a
    ⟨blk.tag, false, blk.data⟩
  simpa only [htag, hdata] using hhit

/-- `boxFree` lockstep: `boxFree` and `memFree` consume their tokens
    together over the single-word block (M2c). -/
theorem vboxFree_lockstep (m : Mem) (a t : Nat) (b : Box32) (blk : Block)
    (b' : Box32)
    (hfind : memFind m a = some blk) (htag : blk.tag = t)
    (hlive : blk.live = true) (hdata : blk.data = [b.val])
    (hunfreed : b.freed = false)
    (hfree : boxFree b = .ok b') :
    ∃ m', memFree m a t = .ok m' ∧
      memFind m' a = some ⟨t, false, [b.val]⟩ := by
  have hfree' : b' = ⟨b.val, true⟩ := by
    rw [boxFree_ok b hunfreed] at hfree
    cases hfree
    rfl
  subst hfree'
  show ∃ m', memFree m a t = .ok m' ∧
    memFind m' a = some ⟨t, false, [b.val]⟩
  have hmfree : memFree m a t =
      .ok ⟨m.next, (a, ⟨blk.tag, false, blk.data⟩) :: m.blocks,
        m.blocks64⟩ := by
    simp [memFree, hfind, htag, hlive]
  refine ⟨_, hmfree, ?_⟩
  have hhit := memFind_cons_hit m.next m.blocks m.blocks64 a
    ⟨blk.tag, false, blk.data⟩
  simpa only [htag, hdata] using hhit

/-- `boxFree` consumes the token and updates the binding, freeing the
    single-word block (M2c, any fuel; mirrors `evalStmtFuel_boxFree`). -/
theorem memEvalStmtFuel_boxFree (f : Nat) (x : String) (ρ : Env)
    (m : Mem) (π : Layout) (a t : Nat)
    (b b' : Box32) (ρ' : Env) (m' : Mem)
    (harr : envLookup ρ x = some (.boxVal b))
    (hlay : layoutLookup π x = some (a, t))
    (hfree : boxFree b = .ok b')
    (hmfree : memFree m a t = .ok m')
    (hup : envUpdate ρ x (.boxVal b') = some ρ') :
    memEvalStmtFuel f (.boxFree x) ρ m π =
      .ok ((ρ', m', π), .fellThrough) := by
  cases f <;>
    simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      harr, hlay, hfree, hmfree, hup]

/-- `vrealloc` lockstep: under the pin invariant, `vecRealloc` and
    `memRealloc` resize together with synced state (tag kept, live,
    resized words). -/
theorem vrealloc_lockstep (m : Mem) (a t : Nat) (b : Vec32) (newSize : Nat)
    (blk : Block) (b' : Vec32)
    (hfind : memFind m a = some blk) (htag : blk.tag = t)
    (hlive : blk.live = true) (hdata : blk.data = b.val)
    (hunfreed : b.freed = false)
    (hre : vecRealloc b newSize = .ok b') :
    ∃ m', memRealloc m a t newSize = .ok m' ∧
      memFind m' a = some ⟨t, true, b'.val⟩ := by
  have hre' : vecRealloc b newSize =
      .ok ⟨b.val.take newSize ++
        List.replicate (newSize - b.val.length) 0, false⟩ :=
    vecRealloc_ok b newSize hunfreed
  rw [hre'] at hre
  cases hre
  show ∃ m', memRealloc m a t newSize = .ok m' ∧
    memFind m' a =
      some ⟨t, true, b.val.take newSize ++
        List.replicate (newSize - b.val.length) 0⟩
  have hmre : memRealloc m a t newSize =
      .ok ⟨m.next, (a, ⟨blk.tag, true, blk.data.take newSize ++
        List.replicate (newSize - blk.data.length) 0⟩) :: m.blocks,
        m.blocks64⟩ := by
    simp [memRealloc, hfind, htag, hlive]
  refine ⟨_, hmre, ?_⟩
  have hhit := memFind_cons_hit m.next m.blocks m.blocks64 a
    ⟨blk.tag, true, blk.data.take newSize ++
      List.replicate (newSize - blk.data.length) 0⟩
  simpa only [htag, hdata] using hhit

/-- `vrealloc` statement on memory (any fuel): the size expression runs
    on memory, the value side resizes via `vecRealloc`, the memory side
    via `memRealloc` in lockstep (mirrors `evalStmtFuel_vrealloc`). -/
theorem memEvalStmtFuel_vrealloc (f : Nat) (x : String) (se : CExpr)
    (ρ : Env) (m : Mem) (π : Layout) (n : BitVec 32)
    (a t : Addr) (b b' : Vec32) (m' : Mem) (ρ' : Env)
    (hse : memEvalExpr se ρ m π = .ok (.u32 n))
    (harr : envLookup ρ x = some (.vecVal b))
    (hlay : layoutLookup π x = some (a, t))
    (hre : vecRealloc b n.toNat = .ok b')
    (hmre : memRealloc m a t n.toNat = .ok m')
    (hup : envUpdate ρ x (.vecVal b') = some ρ') :
    memEvalStmtFuel f (.vrealloc x se) ρ m π =
      .ok (((ρ', m', π)), .fellThrough) := by
  cases f <;>
    simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      hse, harr, hlay, hre, hmre, hup]

/-! ## N4d-iv-b1 statement agreement (`if_` / `fail` / `vgrowSet` / `vgrowFree`) -/

/-- `if_` on `true` takes the then-branch (any fuel; mirrors
    `evalStmtFuel_if_true`). -/
theorem memEvalStmtFuel_if_true (f : Nat) (c : CExpr) (t e : CStmt)
    (ρ : Env) (m : Mem) (π : Layout)
    (h : memEvalExpr c ρ m π = .ok (.b true)) :
    memEvalStmtFuel f (.if_ c t e) ρ m π =
      memEvalStmtFuel f t ρ m π := by
  cases f <;>
    simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, h]

/-- `if_` on `false` takes the else-branch (any fuel; mirrors
    `evalStmtFuel_if_false`). -/
theorem memEvalStmtFuel_if_false (f : Nat) (c : CExpr) (t e : CStmt)
    (ρ : Env) (m : Mem) (π : Layout)
    (h : memEvalExpr c ρ m π = .ok (.b false)) :
    memEvalStmtFuel f (.if_ c t e) ρ m π =
      memEvalStmtFuel f e ρ m π := by
  cases f <;>
    simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, h]

/-- `fail` aborts loudly at any fuel (mirrors `evalStmtFuel_fail`). -/
theorem memEvalStmtFuel_fail (f : Nat) (ρ : Env) (m : Mem) (π : Layout) :
    memEvalStmtFuel f .fail ρ m π = .error .AssertFail := by
  cases f <;> simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith]

/-- `vgrowSet` statement on memory (any fuel): the index/value
    expressions run on memory, the value side stores via `vecSet`, the
    memory side via the header-shifted `memStore` in lockstep (mirrors
    `evalStmtFuel_vgrowSet`; the `+ 2` skips the length/capacity
    header words). -/
theorem memEvalStmtFuel_vgrowSet (f : Nat) (x : String) (ie ve : CExpr)
    (ρ : Env) (m : Mem) (π : Layout) (i : BitVec 64) (xv : BitVec 32)
    (a t : Nat) (b b' : Vec32) (len cap : Nat) (m' : Mem) (ρ' : Env)
    (hi : memEvalExpr ie ρ m π = .ok (.u64 i))
    (hv : memEvalExpr ve ρ m π = .ok (.i32 xv))
    (harr : envLookup ρ x = some (.stdVecOwned b len cap))
    (hlay : layoutLookup π x = some (a, t))
    (hset : vecSet b i.toNat xv = .ok b')
    (hmstore : memStore m a t (i.toNat + 2) xv = .ok m')
    (hup : envUpdate ρ x (.stdVecOwned b' len cap) = some ρ') :
    memEvalStmtFuel f (.vgrowSet x ie ve) ρ m π =
      .ok ((ρ', m', π), .fellThrough) := by
  cases f <;>
    simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      hi, hv, harr, hlay, hset, hmstore, hup]

/-- `vgrowSet` errors propagate (any fuel; mirrors
    `evalStmtFuel_vgrowSet_err`). -/
theorem memEvalStmtFuel_vgrowSet_err (f : Nat) (x : String) (ie ve : CExpr)
    (ρ : Env) (m : Mem) (π : Layout) (i : BitVec 64) (xv : BitVec 32)
    (a t : Nat) (b : Vec32) (len cap : Nat) (e : Panic)
    (hi : memEvalExpr ie ρ m π = .ok (.u64 i))
    (hv : memEvalExpr ve ρ m π = .ok (.i32 xv))
    (harr : envLookup ρ x = some (.stdVecOwned b len cap))
    (hlay : layoutLookup π x = some (a, t))
    (hset : vecSet b i.toNat xv = .error e) :
    memEvalStmtFuel f (.vgrowSet x ie ve) ρ m π = .error e := by
  cases f <;>
    simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      hi, hv, harr, hlay, hset]

/-- `vgrowFree` statement on memory (any fuel): the value side consumes
    via `vecFree`, the memory side via `memFree` in lockstep (mirrors
    `evalStmtFuel_vgrowFree`). -/
theorem memEvalStmtFuel_vgrowFree (f : Nat) (x : String)
    (ρ : Env) (m : Mem) (π : Layout)
    (a t : Nat) (b b' : Vec32) (len cap : Nat) (m' : Mem) (ρ' : Env)
    (harr : envLookup ρ x = some (.stdVecOwned b len cap))
    (hlay : layoutLookup π x = some (a, t))
    (hfree : vecFree b = .ok b')
    (hmfree : memFree m a t = .ok m')
    (hup : envUpdate ρ x (.stdVecOwned b' len cap) = some ρ') :
    memEvalStmtFuel f (.vgrowFree x) ρ m π =
      .ok ((ρ', m', π), .fellThrough) := by
  cases f <;>
    simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      harr, hlay, hfree, hmfree, hup]

/-- `vgrowFree` errors (double-free) propagate (any fuel; mirrors
    `evalStmtFuel_vgrowFree_err`). -/
theorem memEvalStmtFuel_vgrowFree_err (f : Nat) (x : String)
    (ρ : Env) (m : Mem) (π : Layout)
    (a t : Nat) (b : Vec32) (len cap : Nat) (e : Panic)
    (harr : envLookup ρ x = some (.stdVecOwned b len cap))
    (hlay : layoutLookup π x = some (a, t))
    (hfree : vecFree b = .error e) :
    memEvalStmtFuel f (.vgrowFree x) ρ m π = .error e := by
  cases f <;>
    simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
      harr, hlay, hfree]

/-- A successful `vecGet` carries its list read + liveness, so the
    mirrored memory load agrees. -/
theorem memLoad_of_vecGet (m : Mem) (a : Addr) (blk : Vec32) (j : Nat)
    (hfind : memFind m a = some ⟨a, true, blk.val⟩)
    (hget : vecGet blk j = .ok (BitVec.ofNat 32 j)) :
    memLoad m a a j = .ok (BitVec.ofNat 32 j) := by
  have hlive_v : blk.freed = false := by
    cases hbf : blk.freed with
    | true => rw [vecGet_freed blk j hbf] at hget; simp at hget
    | false => rfl
  have hgetl : blk.val[j]? = some (BitVec.ofNat 32 j) := by
    match hm : blk.val[j]? with
    | some z =>
      have h2 : vecGet blk j = .ok z := vecGet_ok blk j z hlive_v hm
      have hzy : z = BitVec.ofNat 32 j := by
        rw [h2] at hget
        simpa using hget
      exact congrArg some hzy
    | none =>
      have h2 : vecGet blk j = .error .OOB := vecGet_oob blk j hlive_v hm
      rw [h2] at hget
      simp at hget
  exact memLoad_hit m a a j _ _ hfind rfl rfl hgetl

/-- A live single-word box block reads its value back at index `0`. -/
theorem memLoad_box_hit (m : Mem) (a : Addr) (x : BitVec 32)
    (hfind : memFind m a = some ⟨a, true, [x]⟩) :
    memLoad m a a 0 = .ok x := by
  exact memLoad_hit m a a 0 _ _ hfind rfl rfl rfl

/-- A successful 64-bit `vecGet64` carries its list read + liveness, so
    the mirrored memory load agrees. -/
theorem memLoad64_of_vecGet64 (m : Mem) (a : Addr) (blk : Vec64) (j : Nat)
    (hfind : memFind64 m a = some ⟨a, true, blk.val⟩)
    (hget : vecGet64 blk j = .ok (BitVec.ofNat 64 j)) :
    memLoad64 m a a j = .ok (BitVec.ofNat 64 j) := by
  have hlive_v : blk.freed = false := by
    cases hbf : blk.freed with
    | true => rw [vecGet64_freed blk j hbf] at hget; simp at hget
    | false => rfl
  have hgetl : blk.val[j]? = some (BitVec.ofNat 64 j) := by
    match hm : blk.val[j]? with
    | some z =>
      have h2 : vecGet64 blk j = .ok z := vecGet64_ok blk j z hlive_v hm
      have hzy : z = BitVec.ofNat 64 j := by
        rw [h2] at hget
        simpa using hget
      exact congrArg some hzy
    | none =>
      have h2 : vecGet64 blk j = .error .OOB := vecGet64_oob blk j hlive_v hm
      rw [h2] at hget
      simp at hget
  exact memLoad64_hit m a a j _ _ hfind rfl rfl hgetl

/-- The M3c goal, stated (M3a proves the per-leaf instances above and
    `Transfer` proves `sum` / `vec_alloc`; M3c discharges the general
    fragment): entry-footprint disjointness implies memory/value
    agreement at any fuel. A `Prop`-valued statement, not an axiom —
    nothing trusts it until M3c proves it. -/
def m3c_transfer_statement (f : Func) (args : List Value) (F : Nat) : Prop :=
  oracleNoalias f args → memEvalFuncFuel F f args = evalFuncFuel F f args

/-- M3a memory fuel: its own bound alongside `EVAL_FUEL` (equal value
    today; separate name so M3c can generalize them independently). -/
def MEM_FUEL : Nat := 4096

theorem MEM_FUEL_eq : MEM_FUEL = EVAL_FUEL := rfl
