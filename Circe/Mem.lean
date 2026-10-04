/-
Circe.Mem — addressful memory model for M3 (shrinking oracle trust).

M3a (C only): a flat block map with lightweight borrow tags, just strong
enough for our three uniqueness sources (`__restrict__` / `noalias`
attrs, disjoint `malloc` results, length-paired stride loops). No
retag/protect generality beyond what the admitted shapes express (see
docs/ROADMAP.md M3); full Stacked Borrows is an explicit non-goal.

State shape (locked): flat block map. `Mem` is a next-address counter +
an `Addr → Block` list-map; a block is a tag (= allocating epoch, so
fresh tags are distinct by construction) + live flag (mirrors the
`Vec32.freed` token: `live = !freed`) + word list. `Layout` maps bound
variable names to `(addr, expected tag)`: the borrow check is tag
equality + liveness + bounds on every access.

`memEval` mirrors `Eval` on the M3a fragment (call-free C leaves +
`sum` / `vec_alloc`): pure constructors delegate to `evalExpr` with
`Mem`/`Layout` untouched; `idx` / `vget` resolve the layout, check the
tag, and cross-check the memory read against the value-level read (both
must agree, else `AssertFail`); `vset` / `vfree` update the value *and*
the block in lockstep (either side failing is loud). `Eval` itself is
untouched.

The transfer `oracleNoalias → memEval = Eval` lands here as the M3c
conjecture (`m3c_transfer` axiom); M3a proves the per-leaf instances
(`memTransfer_add/incr/sum/vec`) as evidence. `oracleNoalias` is the
entry-footprint disjointness the M3b `derivedNoalias` check will imply.
-/
import Circe.Base
import Circe.CoreIR
import Circe.Eval

/-! ## Addresses, blocks, memory -/

/-- Addresses are a flat counter (no pointer arithmetic in the subset:
    the only indexing is length-paired stride, checked per access). -/
abbrev Addr := Nat

/-- A heap block: allocating-epoch tag + live flag + words. `live`
    mirrors the value-level affine token (`Vec32.freed = !live`;
    `arr32` lists are always live). -/
structure Block where
  tag : Nat
  live : Bool
  data : List (BitVec 32)
  deriving DecidableEq, Repr

/-- A 64-bit heap block: same tag/live discipline as `Block`, holding
    `u64` words (the `vec_alloc_u64` shape, M1b). The two widths live in
    separate maps (no mixed-width block: every `Func` is monomorphized),
    so 32-bit operations never disturb 64-bit pins and vice versa. -/
structure Block64 where
  tag : Nat
  live : Bool
  data : List (BitVec 64)
  deriving DecidableEq, Repr

/-- Flat block map: next-address counter + `Addr → Block` association +
    `Addr → Block64` association. The counter is shared (fresh addresses
    never alias across widths either); each map's lookup only sees its
    own bindings. -/
structure Mem where
  next : Nat
  blocks : List (Nat × Block)
  blocks64 : List (Nat × Block64)
  deriving DecidableEq, Repr

/-- Empty memory (function entry before lifting: nothing allocated). -/
def emptyMem : Mem := ⟨0, [], []⟩

/-- Block lookup (first binding wins). -/
def memFind : Mem → Addr → Option Block
  | ⟨_, [], _⟩, _ => none
  | ⟨n, (k, v) :: rest, g64⟩, a =>
    if a == k then some v else memFind ⟨n, rest, g64⟩ a

theorem memFind_empty (a : Addr) : memFind emptyMem a = none := by
  simp [memFind, emptyMem]

/-- 64-bit block lookup (first binding wins; ignores the 32-bit map). -/
def memFind64 : Mem → Addr → Option Block64
  | ⟨_, _, []⟩, _ => none
  | ⟨n, bs, (k, v) :: rest⟩, a =>
    if a == k then some v else memFind64 ⟨n, bs, rest⟩ a

theorem memFind64_empty (a : Addr) : memFind64 emptyMem a = none := by
  simp [memFind64, emptyMem]

/-- Allocate `data` words with a fresh tag (= fresh address, so distinct
    allocations never alias by construction). The 64-bit map rides along
    untouched. -/
def memAllocData (m : Mem) (data : List (BitVec 32)) : Mem × Addr :=
  let a := m.next
  (⟨m.next + 1, (a, ⟨a, true, data⟩) :: m.blocks, m.blocks64⟩, a)

/-- Allocate 64-bit `data` words with a fresh tag (the 32-bit map rides
    along untouched). -/
def memAllocData64 (m : Mem) (data : List (BitVec 64)) : Mem × Addr :=
  let a := m.next
  (⟨m.next + 1, m.blocks, (a, ⟨a, true, data⟩) :: m.blocks64⟩, a)

/-- Allocate `n` zeroed words (the `malloc` shape). -/
def memAlloc (m : Mem) (n : Nat) : Mem × Addr :=
  memAllocData m (List.replicate n 0)

/-- Allocate `n` zeroed 64-bit words. -/
def memAlloc64 (m : Mem) (n : Nat) : Mem × Addr :=
  memAllocData64 m (List.replicate n 0)

theorem memAllocData_next (m : Mem) (data : List (BitVec 32)) :
    (memAllocData m data).2 = m.next := by
  simp [memAllocData]

theorem memAllocData64_next (m : Mem) (data : List (BitVec 64)) :
    (memAllocData64 m data).2 = m.next := by
  simp [memAllocData64]

theorem memAlloc_next (m : Mem) (n : Nat) :
    (memAlloc m n).2 = m.next := by
  simp [memAlloc, memAllocData_next]

theorem memAlloc64_next (m : Mem) (n : Nat) :
    (memAlloc64 m n).2 = m.next := by
  simp [memAlloc64, memAllocData64_next]

/-- Fresh allocation is found with its tag, live, holding the data. -/
theorem memFind_alloc_hit (m : Mem) (data : List (BitVec 32)) :
    memFind (memAllocData m data).1 (memAllocData m data).2 =
      some ⟨(memAllocData m data).2, true, data⟩ := by
  simp [memAllocData, memFind]

/-- `memFind` ignores the next-address counter and the 64-bit map (only
    the 32-bit map matters). -/
theorem memFind_next_irrelevant (n₁ n₂ : Nat) (bs : List (Nat × Block))
    (g₁ g₂ : List (Nat × Block64))
    (a : Addr) :
    memFind ⟨n₁, bs, g₁⟩ a = memFind ⟨n₂, bs, g₂⟩ a := by
  induction bs with
  | nil => simp [memFind]
  | cons kv rest ih =>
    obtain ⟨k, v⟩ := kv
    simp [memFind, ih]

/-- `memFind64` ignores the counter and the 32-bit map. -/
theorem memFind64_next_irrelevant (n₁ n₂ : Nat) (bs₁ bs₂ : List (Nat × Block))
    (g : List (Nat × Block64))
    (a : Addr) :
    memFind64 ⟨n₁, bs₁, g⟩ a = memFind64 ⟨n₂, bs₂, g⟩ a := by
  induction g with
  | nil => simp [memFind64]
  | cons kv rest ih =>
    obtain ⟨k, v⟩ := kv
    simp [memFind64, ih]

/-- Allocation preserves every old binding (monotone growth, never
    reuses an address). -/
theorem memFind_alloc_miss (m : Mem) (data : List (BitVec 32)) (a : Addr)
    (h : a ≠ m.next) :
    memFind (memAllocData m data).1 a = memFind m a := by
  obtain ⟨n, bs, g64⟩ := m
  have hbe : (a == n) = false := by
    cases heq : (a == n) with
    | true => exact absurd (beq_iff_eq.mp heq) h
    | false => rfl
  simp only [memAllocData, memFind, hbe, Bool.false_eq_true, ite_false]
  exact memFind_next_irrelevant _ _ _ _ _ _

/-- 64-bit allocation preserves every old 64-bit binding. -/
theorem memFind64_alloc_miss (m : Mem) (data : List (BitVec 64)) (a : Addr)
    (h : a ≠ m.next) :
    memFind64 (memAllocData64 m data).1 a = memFind64 m a := by
  obtain ⟨n, bs, g64⟩ := m
  have hbe : (a == n) = false := by
    cases heq : (a == n) with
    | true => exact absurd (beq_iff_eq.mp heq) h
    | false => rfl
  simp only [memAllocData64, memFind64, hbe, Bool.false_eq_true, ite_false]
  exact memFind64_next_irrelevant _ _ _ _ _ _

/-- 32-bit allocation preserves every 64-bit binding (separate maps). -/
theorem memFind64_alloc32_miss (m : Mem) (data : List (BitVec 32)) (a : Addr) :
    memFind64 (memAllocData m data).1 a = memFind64 m a := by
  obtain ⟨n, bs, g64⟩ := m
  simp only [memAllocData]
  exact memFind64_next_irrelevant _ _ _ _ _ _

/-- 64-bit allocation preserves every 32-bit binding (separate maps). -/
theorem memFind_alloc64_miss (m : Mem) (data : List (BitVec 64)) (a : Addr) :
    memFind (memAllocData64 m data).1 a = memFind m a := by
  obtain ⟨n, bs, g64⟩ := m
  simp only [memAllocData64]
  exact memFind_next_irrelevant _ _ _ _ _ _

/-- Checked load: the block must exist, carry the expected tag (the
    borrow check), be live (no use-after-free), and cover `i`
    (bounds). Anything else is loud (`AssertFail`, `OOB` for bounds —
    the same codes `Eval` reports on the value side). -/
def memLoad (m : Mem) (a : Addr) (t : Nat) (i : Nat) : Result (BitVec 32) :=
  match memFind m a with
  | none => .error .AssertFail
  | some b =>
    if b.tag != t then .error .AssertFail
    else if !b.live then .error .AssertFail
    else
      match b.data[i]? with
      | some x => .ok x
      | none => .error .OOB

/-- Fresh `memAlloc` is found with its tag, live, holding zeroes. -/
theorem memFind_memAlloc (m : Mem) (n : Nat) :
    memFind (memAlloc m n).1 (memAlloc m n).2 =
      some ⟨(memAlloc m n).2, true, List.replicate n 0⟩ := by
  have h1 : (memAlloc m n).1 =
      ⟨m.next + 1, (m.next, ⟨m.next, true, List.replicate n 0⟩) ::
        m.blocks, m.blocks64⟩ := rfl
  have h2 : (memAlloc m n).2 = m.next := rfl
  rw [h1, h2]
  simp [memFind]

/-- Fresh 64-bit allocation is found with its tag, live, holding zeroes. -/
theorem memFind64_memAlloc64 (m : Mem) (n : Nat) :
    memFind64 (memAlloc64 m n).1 (memAlloc64 m n).2 =
      some ⟨(memAlloc64 m n).2, true, List.replicate n 0⟩ := by
  have h1 : (memAlloc64 m n).1 =
      ⟨m.next + 1, m.blocks,
        (m.next, ⟨m.next, true, List.replicate n 0⟩) :: m.blocks64⟩ := rfl
  have h2 : (memAlloc64 m n).2 = m.next := rfl
  rw [h1, h2]
  simp [memFind64]

/-- Load from a known live block with matching tag. -/
theorem memLoad_hit (m : Mem) (a t i : Nat) (b : Block) (x : BitVec 32)
    (hfind : memFind m a = some b) (htag : b.tag = t)
    (hlive : b.live = true) (hget : b.data[i]? = some x) :
    memLoad m a t i = .ok x := by
  simp [memLoad, hfind, htag, hlive, hget]

/-- Zeroed words read back `0` in bounds. -/
theorem replicate_getElem?_zero (n i : Nat) (h : i < n) :
    (List.replicate n (0 : BitVec 32))[i]? = some 0 := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.replicate_succ, List.getElem?_cons_succ]
      exact ih i (by omega)

/-- Fresh blocks read back zeroes in bounds. -/
theorem memLoad_alloc_zero (m : Mem) (n i : Nat) (h : i < n) :
    memLoad (memAlloc m n).1 (memAlloc m n).2 (memAlloc m n).2 i =
      .ok 0 := by
  have hfind := memFind_memAlloc m n
  have htag : (⟨(memAlloc m n).2, true, List.replicate n 0⟩ : Block).tag =
      (memAlloc m n).2 := rfl
  have hlive : (⟨(memAlloc m n).2, true, List.replicate n 0⟩ : Block).live =
      true := rfl
  have hget : (⟨(memAlloc m n).2, true,
      List.replicate n 0⟩ : Block).data[i]? = some 0 := by
    have h2 : (memAlloc m n).2 = m.next := memAlloc_next m n
    rw [h2]
    exact replicate_getElem?_zero n i h
  exact memLoad_hit _ _ _ _ _ _ hfind htag hlive hget

/-- Checked store: same tag/liveness/bounds discipline as `memLoad`;
    the data update is exactly `List.set` (the `vecSet` update on the
    value side — see `memStore_vecSet`). -/
def memStore (m : Mem) (a : Addr) (t : Nat) (i : Nat)
    (x : BitVec 32) : Result Mem :=
  match memFind m a with
  | none => .error .AssertFail
  | some b =>
    if b.tag != t then .error .AssertFail
    else if !b.live then .error .AssertFail
    else if _ : i < b.data.length then
      .ok ⟨m.next, (a, ⟨b.tag, b.live, b.data.set i x⟩) :: m.blocks,
        m.blocks64⟩
    else .error .OOB

/-- Checked free: consumes the live token (double-free is `AssertFail`,
    like `vecFree_double`); contents kept (value-invisible, M1d). -/
def memFree (m : Mem) (a : Addr) (t : Nat) : Result Mem :=
  match memFind m a with
  | none => .error .AssertFail
  | some b =>
    if b.tag != t then .error .AssertFail
    else if !b.live then .error .AssertFail
    else
      .ok ⟨m.next, (a, ⟨b.tag, false, b.data⟩) :: m.blocks, m.blocks64⟩

/-- Checked realloc: same tag/liveness discipline as `memStore`; resize
    preserves the `min(old, new)` prefix and zero-fills growth — exactly
    the `vecRealloc` update on the value side (see `memRealloc_vecRealloc`).
    The address/tag are kept (in-place model: `realloc` never moves the
    block, so the layout pin survives); the counter is untouched. -/
def memRealloc (m : Mem) (a : Addr) (t : Nat) (newSize : Nat) : Result Mem :=
  match memFind m a with
  | none => .error .AssertFail
  | some b =>
    if b.tag != t then .error .AssertFail
    else if !b.live then .error .AssertFail
    else
      .ok ⟨m.next, (a, ⟨b.tag, true,
        b.data.take newSize ++ List.replicate (newSize - b.data.length) 0⟩) ::
        m.blocks, m.blocks64⟩

/-! ## 64-bit operations (the `vec_alloc_u64` shape, M1b) -/

/-- Checked 64-bit load: same tag/liveness/bounds discipline as
    `memLoad`, over the 64-bit map. -/
def memLoad64 (m : Mem) (a : Addr) (t : Nat) (i : Nat) : Result (BitVec 64) :=
  match memFind64 m a with
  | none => .error .AssertFail
  | some b =>
    if b.tag != t then .error .AssertFail
    else if !b.live then .error .AssertFail
    else
      match b.data[i]? with
      | some x => .ok x
      | none => .error .OOB

/-- Load from a known live 64-bit block with matching tag. -/
theorem memLoad64_hit (m : Mem) (a t i : Nat) (b : Block64) (x : BitVec 64)
    (hfind : memFind64 m a = some b) (htag : b.tag = t)
    (hlive : b.live = true) (hget : b.data[i]? = some x) :
    memLoad64 m a t i = .ok x := by
  simp [memLoad64, hfind, htag, hlive, hget]

/-- Checked 64-bit store (the 32-bit map rides along untouched). -/
def memStore64 (m : Mem) (a : Addr) (t : Nat) (i : Nat)
    (x : BitVec 64) : Result Mem :=
  match memFind64 m a with
  | none => .error .AssertFail
  | some b =>
    if b.tag != t then .error .AssertFail
    else if !b.live then .error .AssertFail
    else if _ : i < b.data.length then
      .ok ⟨m.next, m.blocks,
        (a, ⟨b.tag, b.live, b.data.set i x⟩) :: m.blocks64⟩
    else .error .OOB

/-- Checked 64-bit free: consumes the live token, contents kept. -/
def memFree64 (m : Mem) (a : Addr) (t : Nat) : Result Mem :=
  match memFind64 m a with
  | none => .error .AssertFail
  | some b =>
    if b.tag != t then .error .AssertFail
    else if !b.live then .error .AssertFail
    else
      .ok ⟨m.next, m.blocks, (a, ⟨b.tag, false, b.data⟩) :: m.blocks64⟩

/-- 64-bit zeroed words read back `0` in bounds. -/
theorem replicate_getElem?_zero64 (n i : Nat) (h : i < n) :
    (List.replicate n (0 : BitVec 64))[i]? = some 0 := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i =>
      simp only [List.replicate_succ, List.getElem?_cons_succ]
      exact ih i (by omega)

/-! ## Layout: which variable pins which `(addr, tag)` -/

/-- Borrow layout: bound variable → address + expected tag. Scalars
    (`i32`/`u32` values) need no entry (no footprint); heap-like values
    (`arr32`/`vecVal`) pin exactly one entry at function entry. -/
abbrev Layout := List (String × Addr × Nat)

/-- Addresses pinned by a layout (the footprint set). -/
def layoutAddrs : Layout → List Addr := List.map (fun p => p.2.1)

/-- Entry footprints are pairwise disjoint (the M3a `oracleNoalias`:
    no two live params alias). Fresh allocation establishes it by
    construction (`memAlloc` never reuses an address). -/
def LayoutNoAlias (π : Layout) : Prop := (layoutAddrs π).Nodup

theorem layoutNoAlias_nil : LayoutNoAlias [] := by
  simp [LayoutNoAlias, layoutAddrs]

/-- Layout lookup (first binding wins). -/
def layoutLookup : Layout → String → Option (Addr × Nat)
  | [], _ => none
  | (k, a, t) :: rest, x =>
    if x = k then some (a, t) else layoutLookup rest x

theorem layoutLookup_hit (k : String) (a : Addr) (t : Nat)
    (rest : Layout) :
    layoutLookup ((k, a, t) :: rest) k = some (a, t) := by
  simp [layoutLookup]

theorem layoutLookup_miss (k x : String) (a : Addr) (t : Nat)
    (rest : Layout) (h : x ≠ k) :
    layoutLookup ((k, a, t) :: rest) x = layoutLookup rest x := by
  simp [layoutLookup, h]

/-! ## Consistency: memory mirrors the values -/

/-- Memory/value consistency: every pinned variable resolves in `ρ` to
    a heap-like value whose words equal the block data, with matching
    tag and a live block. Scalars are unconstrained (no footprint).
    64-bit blocks (`vecVal64`) pin the 64-bit map; boxes (`boxVal`)
    pin a single-word 32-bit block holding `[val]`. -/
def MemConsistent (ρ : Env) (m : Mem) (π : Layout) : Prop :=
  ∀ x a t, layoutLookup π x = some (a, t) →
    (∃ l, (envLookup ρ x = some (.arr32 l) ∨
          ∃ v : Vec32, envLookup ρ x = some (.vecVal v) ∧ v.val = l) ∧
    ∃ b, memFind m a = some b ∧ b.tag = t ∧ b.live = true ∧ b.data = l) ∨
    (∃ v : Vec64, envLookup ρ x = some (.vecVal64 v) ∧
    ∃ b, memFind64 m a = some b ∧ b.tag = t ∧ b.live = true ∧
      b.data = v.val) ∨
    (∃ b : Box32, envLookup ρ x = some (.boxVal b) ∧
    ∃ blk, memFind m a = some blk ∧ blk.tag = t ∧ blk.live = true ∧
      blk.data = [b.val])

/-- The empty layout is consistent with anything. -/
theorem memConsistent_nil (ρ : Env) (m : Mem) : MemConsistent ρ m [] := by
  intro x a t h
  simp [layoutLookup] at h

/-! ## `memEval`: `Eval` mirrored over memory -/

/-- Memory-level expression evaluation. Pure constructors delegate to
    `evalExpr` with memory untouched; `idx` / `idxi` / `vget` resolve
    the layout, run the tag/liveness/bounds check in `memLoad`, and
    cross-check the memory word against the value-level read
    (disagreement is `AssertFail`: memory and values can never silently
    diverge). -/
def memEvalExpr : CExpr → Env → Mem → Layout → Result Value
  | .lit l, _, _, _ => .ok (litVal l)
  | .var x, ρ, _, _ =>
    match envLookup ρ x with
    | some v => .ok v
    | none => .error .Uninit
  | .add a b, ρ, m, π =>
    match memEvalExpr a ρ m π, memEvalExpr b ρ m π with
    | .ok (.i32 x), .ok (.i32 y) => (checkedAddI32 x y).map .i32
    | .ok (.i64 x), .ok (.i64 y) => (checkedAddI64 x y).map .i64
    | .ok _, .ok _ => .error .AssertFail
    | .error e, _ => .error e
    | _, .error e => .error e
  | .uadd a b, ρ, m, π =>
    match memEvalExpr a ρ m π, memEvalExpr b ρ m π with
    | .ok (.u32 x), .ok (.u32 y) => .ok (.u32 (x + y))
    | .ok (.u64 x), .ok (.u64 y) => .ok (.u64 (x + y))
    | .ok _, .ok _ => .error .AssertFail
    | .error e, _ => .error e
    | _, .error e => .error e
  | .umul a b, ρ, m, π =>
    match memEvalExpr a ρ m π, memEvalExpr b ρ m π with
    | .ok (.u32 x), .ok (.u32 y) => .ok (.u32 (x * y))
    | .ok (.u64 x), .ok (.u64 y) => .ok (.u64 (x * y))
    | .ok _, .ok _ => .error .AssertFail
    | .error e, _ => .error e
    | _, .error e => .error e
  | .ult a b, ρ, m, π =>
    match memEvalExpr a ρ m π, memEvalExpr b ρ m π with
    | .ok (.u32 x), .ok (.u32 y) => .ok (.b (x.ult y))
    | .ok (.u64 x), .ok (.u64 y) => .ok (.b (x.ult y))
    | .ok _, .ok _ => .error .AssertFail
    | .error e, _ => .error e
    | _, .error e => .error e
  | .ueq a b, ρ, m, π =>
    match memEvalExpr a ρ m π, memEvalExpr b ρ m π with
    | .ok (.u32 x), .ok (.u32 y) => .ok (.b (x == y))
    | .ok (.u64 x), .ok (.u64 y) => .ok (.b (x == y))
    | .ok (.i32 x), .ok (.i32 y) => .ok (.b (x == y))
    | .ok (.i64 x), .ok (.i64 y) => .ok (.b (x == y))
    | .ok _, .ok _ => .error .AssertFail
    | .error e, _ => .error e
    | _, .error e => .error e
  | .idx arr ie, ρ, m, π =>
    match layoutLookup π arr with
    | none => .error .AssertFail
    | some (a, t) =>
      match memEvalExpr ie ρ m π, envLookup ρ arr with
      | .ok (.u32 i), some (.arr32 l) =>
        match memLoad m a t i.toNat, l[i.toNat]? with
        | .ok w, some v => if w == v then .ok (.u32 v) else .error .AssertFail
        | .error e, _ => .error e
        | _, _ => .error .AssertFail
      | .ok _, _ => .error .AssertFail
      | .error e, _ => .error e
  | .idxi arr ie, ρ, m, π =>
    match layoutLookup π arr with
    | none => .error .AssertFail
    | some (a, t) =>
      match memEvalExpr ie ρ m π, envLookup ρ arr with
      | .ok (.u64 i), some (.arr32 l) =>
        match memLoad m a t i.toNat, l[i.toNat]? with
        | .ok w, some v => if w == v then .ok (.i32 v) else .error .AssertFail
        | .error e, _ => .error e
        | _, _ => .error .AssertFail
      | .ok _, _ => .error .AssertFail
      | .error e, _ => .error e
  | .optHas o, ρ, m, π =>
    match layoutLookup π o with
    | none => .error .AssertFail
    | some (a, t) =>
      match memLoad m a t 1, envLookup ρ o with
      | .ok ew, some (.optVal v) =>
        if ew == (if v.isSome then 1 else 0 : BitVec 32) then
          .ok (.b v.isSome)
        else .error .AssertFail
      | .error e, _ => .error e
      | _, _ => .error .AssertFail
  | .optGet o, ρ, m, π =>
    match layoutLookup π o with
    | none => .error .AssertFail
    | some (a, t) =>
      match memLoad m a t 0, memLoad m a t 1, envLookup ρ o with
      | .ok w, .ok ew, some (.optVal (some x)) =>
        if w == x then
          if ew == 1 then .ok (.i32 x) else .error .AssertFail
        else .error .AssertFail
      | .ok _, .ok _, some (.optVal none) => .error .AssertFail
      | .error e, _, _ => .error e
      | _, .error e, _ => .error e
      | _, _, _ => .error .AssertFail
  | .spanLen s, ρ, m, π =>
    match layoutLookup π s with
    | none => .error .AssertFail
    | some (a, t) =>
      match memLoad m a t 0, envLookup ρ s with
      | .ok w, some (.spanVal l) =>
        if w == BitVec.ofNat 32 l.length then
          .ok (.u64 (BitVec.ofNat 64 l.length))
        else .error .AssertFail
      | .error e, _ => .error e
      | _, _ => .error .AssertFail
  | .spanAt s ie, ρ, m, π =>
    match layoutLookup π s with
    | none => .error .AssertFail
    | some (a, t) =>
      match memEvalExpr ie ρ m π, envLookup ρ s with
      | .ok (.u64 i), some (.spanVal l) =>
        match memLoad m a t (i.toNat + 1), l[i.toNat]? with
        | .ok w, some v => if w == v then .ok (.i32 v) else .error .AssertFail
        | .error e, _ => .error e
        | _, _ => .error .AssertFail
      | .ok _, _ => .error .AssertFail
      | .error e, _ => .error e
  | .stdVecLen s, ρ, m, π =>
    match layoutLookup π s with
    | none => .error .AssertFail
    | some (a, t) =>
      match memLoad m a t 0, envLookup ρ s with
      | .ok w, some (.stdVecVal l) =>
        if w == BitVec.ofNat 32 l.length then
          .ok (.u64 (BitVec.ofNat 64 l.length))
        else .error .AssertFail
      | .error e, _ => .error e
      | _, _ => .error .AssertFail
  | .stdVecAt s ie, ρ, m, π =>
    match layoutLookup π s with
    | none => .error .AssertFail
    | some (a, t) =>
      match memEvalExpr ie ρ m π, envLookup ρ s with
      | .ok (.u64 i), some (.stdVecVal l) =>
        match memLoad m a t (i.toNat + 1), l[i.toNat]? with
        | .ok w, some v => if w == v then .ok (.i32 v) else .error .AssertFail
        | .error e, _ => .error e
        | _, _ => .error .AssertFail
      | .ok _, _ => .error .AssertFail
      | .error e, _ => .error e
  | .vnew se, ρ, m, π =>
    match memEvalExpr se ρ m π with
    | .error e => .error e
    | .ok (.u32 n) =>
      match vecNew n.toNat with
      | .error e => .error e
      | .ok v => .ok (.vecVal v)
    | .ok (.u64 n) =>
      match vecNew64 n.toNat with
      | .error e => .error e
      | .ok v => .ok (.vecVal64 v)
    | .ok _ => .error .AssertFail
  | .vget arr ie, ρ, m, π =>
    match layoutLookup π arr with
    | none => .error .AssertFail
    | some (a, t) =>
      match memEvalExpr ie ρ m π, envLookup ρ arr with
      | .ok (.u32 i), some (.vecVal v) =>
        match memLoad m a t i.toNat, vecGet v i.toNat with
        | .ok w, .ok x => if w == x then .ok (.u32 x) else .error .AssertFail
        | .error e, _ => .error e
        | _, .error e => .error e
      | .ok (.u64 i), some (.vecVal64 v) =>
        match memLoad64 m a t i.toNat, vecGet64 v i.toNat with
        | .ok w, .ok x => if w == x then .ok (.u64 x) else .error .AssertFail
        | .error e, _ => .error e
        | _, .error e => .error e
      | .ok _, _ => .error .AssertFail
      | .error e, _ => .error e
  | .boxNew se, ρ, m, π =>
    match memEvalExpr se ρ m π with
    | .error e => .error e
    | .ok (.i32 x) =>
      match boxNew x with
      | .error e => .error e
      | .ok b => .ok (.boxVal b)
    | .ok _ => .error .AssertFail
  | .boxGet b, ρ, m, π =>
    match layoutLookup π b with
    | none => .error .AssertFail
    | some (a, t) =>
      match envLookup ρ b with
      | some (.boxVal v) =>
        match memLoad m a t 0, boxGet v with
        | .ok w, .ok x => if w == x then .ok (.i32 x) else .error .AssertFail
        | .error e, _ => .error e
        | _, .error e => .error e
      | _ => .error .AssertFail
  | .fget obj field, ρ, _, _ =>
    match envLookup ρ obj with
    | none => .error .Uninit
    | some (.structVal _ fields) =>
      match fieldLookup fields field with
      | some x => .ok (.i32 x)
      | none => .error .AssertFail
    | some _ => .error .AssertFail
  | .pmk x y, ρ, m, π =>
    match memEvalExpr x ρ m π, memEvalExpr y ρ m π with
    | .ok (.i32 xv), .ok (.i32 yv) =>
      .ok (.structVal "Point" [("x", xv), ("y", yv)])
    | .ok _, .ok _ => .error .AssertFail
    | .error e, _ => .error e
    | _, .error e => .error e

/-- Pure-expression agreement for closed shapes: `lit`/`var` hold by
    definition; binary operators agree once their discriminants are
    constructor-headed (supplied per use-site via env facts — the
    equation-lemma unfolding of a `match` never reproduces a
    hand-written `match`, so there is deliberately no general
    conditional lemma for `add`/`uadd`/`umul`/`ult`/`ueq`: every
    transfer/body proof below reduces both sides fully from concrete
    facts instead, exactly like the existing `emit_correct` proofs). -/
theorem memEvalExpr_lit (l : CLit) (ρ : Env) (m : Mem) (π : Layout) :
    memEvalExpr (.lit l) ρ m π = evalExpr (.lit l) ρ := rfl

theorem memEvalExpr_var (x : String) (ρ : Env) (m : Mem) (π : Layout) :
    memEvalExpr (.var x) ρ m π = evalExpr (.var x) ρ := rfl

/-- `fget` is pure (struct values need no footprint): memory untouched,
    agreement with `Eval` by definition. -/
theorem memEvalExpr_fget (obj field : String) (ρ : Env) (m : Mem)
    (π : Layout) :
    memEvalExpr (.fget obj field) ρ m π = evalExpr (.fget obj field) ρ := rfl

/-- `add` over `fget`/`var` agrees (the `translate` shape): both sides
    read the same field and delta, then run `checkedAddI32`. -/
theorem memEvalExpr_add_fget_var (ρ : Env) (m : Mem) (π : Layout)
    (obj f xv : String) (tag : String) (fields : List (String × BitVec 32))
    (px dx : BitVec 32)
    (hobj : envLookup ρ obj = some (.structVal tag fields))
    (hfield : fieldLookup fields f = some px)
    (hvar : envLookup ρ xv = some (.i32 dx)) :
    memEvalExpr (.add (.fget obj f) (.var xv)) ρ m π =
      (checkedAddI32 px dx).map .i32 := by
  simp [memEvalExpr, hobj, hfield, hvar]

/-- `idx` agreement under consistency: the layout pin resolves, the tag
    matches, the block is live, and the memory word equals the
    value-level element — so the cross-check succeeds and both sides
    read the same word. -/
theorem memEvalExpr_idx_hit (arr : String) (ie : CExpr) (ρ : Env)
    (m : Mem) (π : Layout) (l : List (BitVec 32)) (i : BitVec 32)
    (x : BitVec 32) (a : Addr) (t : Nat)
    (hlay : layoutLookup π arr = some (a, t))
    (harr : envLookup ρ arr = some (.arr32 l))
    (hie : memEvalExpr ie ρ m π = evalExpr ie ρ)
    (hieval : evalExpr ie ρ = .ok (.u32 i))
    (hmem : memLoad m a t i.toNat = .ok x)
    (hval : l[i.toNat]? = some x) :
    memEvalExpr (.idx arr ie) ρ m π = evalExpr (.idx arr ie) ρ := by
  simp only [memEvalExpr, evalExpr, hlay, hie, hieval, harr, hmem, hval,
    beq_self_eq_true, ↓reduceIte]

/-- `idxi` agreement under consistency (the `std::array` read
    shape): same tag/liveness discipline as `idx`, at a `u64` index
    with the word delivered as `i32` — so the cross-check succeeds and
    both sides read the same word. -/
theorem memEvalExpr_idxi_hit (arr : String) (ie : CExpr) (ρ : Env)
    (m : Mem) (π : Layout) (l : List (BitVec 32)) (i : BitVec 64)
    (x : BitVec 32) (a : Addr) (t : Nat)
    (hlay : layoutLookup π arr = some (a, t))
    (harr : envLookup ρ arr = some (.arr32 l))
    (hie : memEvalExpr ie ρ m π = evalExpr ie ρ)
    (hieval : evalExpr ie ρ = .ok (.u64 i))
    (hmem : memLoad m a t i.toNat = .ok x)
    (hval : l[i.toNat]? = some x) :
    memEvalExpr (.idxi arr ie) ρ m π = evalExpr (.idxi arr ie) ρ := by
  simp only [memEvalExpr, evalExpr, hlay, hie, hieval, harr, hmem, hval,
    beq_self_eq_true, ↓reduceIte]

/-- `idxi` OOB agreement: when both the memory load and the value
    read fail `OOB` off the end, both sides fail loudly together
    (mirrors `evalExpr_idxi_oob`). -/
theorem memEvalExpr_idxi_oob (arr : String) (ie : CExpr) (ρ : Env)
    (m : Mem) (π : Layout) (l : List (BitVec 32)) (i : BitVec 64)
    (a : Addr) (t : Nat)
    (hlay : layoutLookup π arr = some (a, t))
    (harr : envLookup ρ arr = some (.arr32 l))
    (hie : memEvalExpr ie ρ m π = evalExpr ie ρ)
    (hieval : evalExpr ie ρ = .ok (.u64 i))
    (hmem : memLoad m a t i.toNat = .error .OOB)
    (hval : l[i.toNat]? = none) :
    memEvalExpr (.idxi arr ie) ρ m π = evalExpr (.idxi arr ie) ρ := by
  simp only [memEvalExpr, evalExpr, hlay, hie, hieval, harr, hmem, hval]

/-- `optHas` agreement: the engaged-bit word in memory matches the
    `optVal` flag, so both sides report the same boolean (mirrors
    `evalExpr_optHas_some`/`evalExpr_optHas_none`; the hypothesis
    is stated per case via the `ew` word to avoid case-splitting on
    `v` inside the proof). -/
theorem memEvalExpr_optHas_hit (o : String) (ρ : Env)
    (m : Mem) (π : Layout) (v : Option (BitVec 32)) (a : Addr) (t : Nat)
    (ew : BitVec 32)
    (hlay : layoutLookup π o = some (a, t))
    (ho : envLookup ρ o = some (.optVal v))
    (hmem : memLoad m a t 1 = .ok ew)
    (hval : ew = (if v.isSome then 1 else 0 : BitVec 32)) :
    memEvalExpr (.optHas o) ρ m π = evalExpr (.optHas o) ρ := by
  simp only [memEvalExpr, evalExpr, hlay, ho, hmem, hval, beq_self_eq_true,
    ↓reduceIte]

/-- `optGet` agreement on an engaged optional: both memory words
    (payload + engaged bit) match the `optVal` word, so both sides
    deliver it. -/
theorem memEvalExpr_optGet_hit (o : String) (ρ : Env)
    (m : Mem) (π : Layout) (x : BitVec 32) (a : Addr) (t : Nat)
    (hlay : layoutLookup π o = some (a, t))
    (ho : envLookup ρ o = some (.optVal (some x)))
    (hmem0 : memLoad m a t 0 = .ok x)
    (hmem1 : memLoad m a t 1 = .ok 1) :
    memEvalExpr (.optGet o) ρ m π = evalExpr (.optGet o) ρ := by
  simp only [memEvalExpr, evalExpr, hlay, ho, hmem0, hmem1, beq_self_eq_true,
    ↓reduceIte]

/-- `optGet` agreement on a disengaged optional: both sides fail
    `AssertFail` loudly (the `unreachable` assert made loud). -/
theorem memEvalExpr_optGet_oob (o : String) (ρ : Env)
    (m : Mem) (π : Layout) (w ew : BitVec 32) (a : Addr) (t : Nat)
    (hlay : layoutLookup π o = some (a, t))
    (ho : envLookup ρ o = some (.optVal none))
    (hmem0 : memLoad m a t 0 = .ok w)
    (hmem1 : memLoad m a t 1 = .ok ew) :
    memEvalExpr (.optGet o) ρ m π = evalExpr (.optGet o) ρ := by
  simp only [memEvalExpr, evalExpr, hlay, ho, hmem0, hmem1]

/-- `spanLen` agreement: the extent word in memory matches the
    `spanVal` length, so both sides report the same `u64` word. -/
theorem memEvalExpr_spanLen_hit (s : String) (ρ : Env)
    (m : Mem) (π : Layout) (l : List (BitVec 32)) (a : Addr) (t : Nat)
    (hlay : layoutLookup π s = some (a, t))
    (hs : envLookup ρ s = some (.spanVal l))
    (hmem : memLoad m a t 0 = .ok (BitVec.ofNat 32 l.length)) :
    memEvalExpr (.spanLen s) ρ m π = evalExpr (.spanLen s) ρ := by
  simp only [memEvalExpr, evalExpr, hlay, hs, hmem, beq_self_eq_true,
    ↓reduceIte]

/-- `spanAt` agreement on an in-bounds index: the reified word in
    memory matches the `spanVal` word, so both sides deliver it
    (mirrors `memEvalExpr_idxi_hit`; the extent word shifts memory
    offsets by one). -/
theorem memEvalExpr_spanAt_hit (s : String) (ie : CExpr) (ρ : Env)
    (m : Mem) (π : Layout) (l : List (BitVec 32)) (i : BitVec 64)
    (x : BitVec 32) (a : Addr) (t : Nat)
    (hlay : layoutLookup π s = some (a, t))
    (hs : envLookup ρ s = some (.spanVal l))
    (hie : memEvalExpr ie ρ m π = evalExpr ie ρ)
    (hieval : evalExpr ie ρ = .ok (.u64 i))
    (hmem : memLoad m a t (i.toNat + 1) = .ok x)
    (hval : l[i.toNat]? = some x) :
    memEvalExpr (.spanAt s ie) ρ m π = evalExpr (.spanAt s ie) ρ := by
  simp only [memEvalExpr, evalExpr, hlay, hie, hieval, hs, hmem, hval,
    beq_self_eq_true, ↓reduceIte]

/-- `spanAt` OOB agreement: the memory load itself fails `OOB`
    past the reified words, so both sides fail `OOB` loudly
    (mirrors `memEvalExpr_idxi_oob`). -/
theorem memEvalExpr_spanAt_oob (s : String) (ie : CExpr) (ρ : Env)
    (m : Mem) (π : Layout) (l : List (BitVec 32)) (i : BitVec 64)
    (a : Addr) (t : Nat)
    (hlay : layoutLookup π s = some (a, t))
    (hs : envLookup ρ s = some (.spanVal l))
    (hie : memEvalExpr ie ρ m π = evalExpr ie ρ)
    (hieval : evalExpr ie ρ = .ok (.u64 i))
    (hmem : memLoad m a t (i.toNat + 1) = .error .OOB)
    (hval : l[i.toNat]? = none) :
    memEvalExpr (.spanAt s ie) ρ m π = evalExpr (.spanAt s ie) ρ := by
  simp only [memEvalExpr, evalExpr, hlay, hie, hieval, hs, hmem, hval]

/-- `stdVecLen` agreement: the length word in memory matches the
    `stdVecVal` length, so both sides report the same `u64` word. -/
theorem memEvalExpr_stdVecLen_hit (s : String) (ρ : Env)
    (m : Mem) (π : Layout) (l : List (BitVec 32)) (a : Addr) (t : Nat)
    (hlay : layoutLookup π s = some (a, t))
    (hs : envLookup ρ s = some (.stdVecVal l))
    (hmem : memLoad m a t 0 = .ok (BitVec.ofNat 32 l.length)) :
    memEvalExpr (.stdVecLen s) ρ m π = evalExpr (.stdVecLen s) ρ := by
  simp only [memEvalExpr, evalExpr, hlay, hs, hmem, beq_self_eq_true,
    ↓reduceIte]

/-- `stdVecAt` agreement on an in-bounds index: the reified word in
    memory matches the `stdVecVal` word, so both sides deliver it
    (mirrors `memEvalExpr_spanAt_hit`; the length word shifts memory
    offsets by one). -/
theorem memEvalExpr_stdVecAt_hit (s : String) (ie : CExpr) (ρ : Env)
    (m : Mem) (π : Layout) (l : List (BitVec 32)) (i : BitVec 64)
    (x : BitVec 32) (a : Addr) (t : Nat)
    (hlay : layoutLookup π s = some (a, t))
    (hs : envLookup ρ s = some (.stdVecVal l))
    (hie : memEvalExpr ie ρ m π = evalExpr ie ρ)
    (hieval : evalExpr ie ρ = .ok (.u64 i))
    (hmem : memLoad m a t (i.toNat + 1) = .ok x)
    (hval : l[i.toNat]? = some x) :
    memEvalExpr (.stdVecAt s ie) ρ m π = evalExpr (.stdVecAt s ie) ρ := by
  simp only [memEvalExpr, evalExpr, hlay, hie, hieval, hs, hmem, hval,
    beq_self_eq_true, ↓reduceIte]

/-- `stdVecAt` OOB agreement: the memory load itself fails `OOB`
    past the reified words, so both sides fail `OOB` loudly
    (mirrors `memEvalExpr_spanAt_oob`). -/
theorem memEvalExpr_stdVecAt_oob (s : String) (ie : CExpr) (ρ : Env)
    (m : Mem) (π : Layout) (l : List (BitVec 32)) (i : BitVec 64)
    (a : Addr) (t : Nat)
    (hlay : layoutLookup π s = some (a, t))
    (hs : envLookup ρ s = some (.stdVecVal l))
    (hie : memEvalExpr ie ρ m π = evalExpr ie ρ)
    (hieval : evalExpr ie ρ = .ok (.u64 i))
    (hmem : memLoad m a t (i.toNat + 1) = .error .OOB)
    (hval : l[i.toNat]? = none) :
    memEvalExpr (.stdVecAt s ie) ρ m π = evalExpr (.stdVecAt s ie) ρ := by
  simp only [memEvalExpr, evalExpr, hlay, hie, hieval, hs, hmem, hval]

/-- `vget` agreement under consistency (the `vec_alloc` loop shape):
    same tag/liveness discipline as `idx`, cross-checked against
    `vecGet` on the value side. -/
theorem memEvalExpr_vget_hit (arr : String) (ie : CExpr) (ρ : Env)
    (m : Mem) (π : Layout) (v : Vec32) (i : BitVec 32)
    (x : BitVec 32) (a : Addr) (t : Nat)
    (hlay : layoutLookup π arr = some (a, t))
    (harr : envLookup ρ arr = some (.vecVal v))
    (hie : memEvalExpr ie ρ m π = evalExpr ie ρ)
    (hieval : evalExpr ie ρ = .ok (.u32 i))
    (hmem : memLoad m a t i.toNat = .ok x)
    (hval : vecGet v i.toNat = .ok x) :
    memEvalExpr (.vget arr ie) ρ m π = evalExpr (.vget arr ie) ρ := by
  simp only [memEvalExpr, evalExpr, hlay, hie, hieval, harr, hmem, hval,
    beq_self_eq_true, ↓reduceIte]

/-- 64-bit `vget` agreement under consistency (the `vec_alloc_u64` loop
    shape): same tag/liveness discipline over the 64-bit map,
    cross-checked against `vecGet64`. -/
theorem memEvalExpr_vget64_hit (arr : String) (ie : CExpr) (ρ : Env)
    (m : Mem) (π : Layout) (v : Vec64) (i : BitVec 64)
    (x : BitVec 64) (a : Addr) (t : Nat)
    (hlay : layoutLookup π arr = some (a, t))
    (harr : envLookup ρ arr = some (.vecVal64 v))
    (hie : memEvalExpr ie ρ m π = evalExpr ie ρ)
    (hieval : evalExpr ie ρ = .ok (.u64 i))
    (hmem : memLoad64 m a t i.toNat = .ok x)
    (hval : vecGet64 v i.toNat = .ok x) :
    memEvalExpr (.vget arr ie) ρ m π = evalExpr (.vget arr ie) ρ := by
  simp only [memEvalExpr, evalExpr, hlay, hie, hieval, harr, hmem, hval,
    beq_self_eq_true, ↓reduceIte]

/-- `boxGet` agreement under consistency (the `box_through` shape):
    the layout pin resolves, the tag matches, the block is live, and
    the single memory word equals the box value — so the cross-check
    succeeds and both sides read the same word. -/
theorem memEvalExpr_boxGet_hit (b : String) (ρ : Env)
    (m : Mem) (π : Layout) (v : Box32)
    (x : BitVec 32) (a : Addr) (t : Nat)
    (hlay : layoutLookup π b = some (a, t))
    (harr : envLookup ρ b = some (.boxVal v))
    (hmem : memLoad m a t 0 = .ok x)
    (hval : boxGet v = .ok x) :
    memEvalExpr (.boxGet b) ρ m π = evalExpr (.boxGet b) ρ := by
  simp only [memEvalExpr, evalExpr, hlay, harr, hmem, hval,
    beq_self_eq_true, ↓reduceIte]

/-! ## `memEval`: statement layer (fuel-bounded `while_`) -/

/-- Loop-free statement skeleton threaded over `(Env, Mem, Layout)`,
    parameterized by the `while_` handler (mirrors `evalStmtWith`). -/
def memEvalStmtWith
    (wh : CExpr → CStmt → Env → Mem → Layout →
      Result ((Env × Mem × Layout) × Outcome)) :
    CStmt → Env → Mem → Layout → Result ((Env × Mem × Layout) × Outcome)
  | .skip, ρ, m, π => .ok ((ρ, m, π), .fellThrough)
  | .seq a b, ρ, m, π =>
    match memEvalStmtWith wh a ρ m π with
    | .error e => .error e
    | .ok ((ρ', m', π'), .returned v) => .ok ((ρ', m', π'), .returned v)
    | .ok ((ρ', m', π'), .broke) => .ok ((ρ', m', π'), .broke)
    | .ok ((ρ', m', π'), .continued) => .ok ((ρ', m', π'), .continued)
    | .ok ((ρ', m', π'), .fellThrough) => memEvalStmtWith wh b ρ' m' π'
  | .cleanup body, ρ, m, π => memEvalStmtWith wh body ρ m π
  | .let_ x _ (.vnew se), ρ, m, π =>
    match memEvalExpr se ρ m π with
    | .error err => .error err
    | .ok (.u32 n) =>
      match vecNew n.toNat with
      | .error e => .error e
      | .ok v =>
        let (m', a) := memAllocData m v.val
        .ok (((x, .vecVal v) :: ρ, m', (x, a, a) :: π), .fellThrough)
    | .ok (.u64 n) =>
      match vecNew64 n.toNat with
      | .error e => .error e
      | .ok v =>
        let (m', a) := memAllocData64 m v.val
        .ok (((x, .vecVal64 v) :: ρ, m', (x, a, a) :: π), .fellThrough)
    | .ok _ => .error .AssertFail
  | .let_ x _ (.boxNew se), ρ, m, π =>
    match memEvalExpr se ρ m π with
    | .error err => .error err
    | .ok (.i32 xv) =>
      match boxNew xv with
      | .error e => .error e
      | .ok b =>
        let (m', a) := memAllocData m [b.val]
        .ok (((x, .boxVal b) :: ρ, m', (x, a, a) :: π), .fellThrough)
    | .ok _ => .error .AssertFail
  | .let_ x _ e, ρ, m, π =>
    match memEvalExpr e ρ m π with
    | .error err => .error err
    | .ok v => .ok (((x, v) :: ρ, m, π), .fellThrough)
  | .assign x e, ρ, m, π =>
    match memEvalExpr e ρ m π with
    | .error err => .error err
    | .ok v =>
      match envUpdate ρ x v with
      | none => .error .Uninit
      | some ρ' => .ok ((ρ', m, π), .fellThrough)
  | .vset x ie ve, ρ, m, π =>
    match memEvalExpr ie ρ m π, memEvalExpr ve ρ m π,
        envLookup ρ x, layoutLookup π x with
    | .ok (.u32 i), .ok (.u32 xv), some (.vecVal b), some (a, t) =>
      match vecSet b i.toNat xv, memStore m a t i.toNat xv with
      | .ok b', .ok m' =>
        match envUpdate ρ x (.vecVal b') with
        | none => .error .Uninit
        | some ρ' => .ok ((ρ', m', π), .fellThrough)
      | .error e, _ => .error e
      | _, .error e => .error e
    | .ok (.u64 i), .ok (.u64 xv), some (.vecVal64 b), some (a, t) =>
      match vecSet64 b i.toNat xv, memStore64 m a t i.toNat xv with
      | .ok b', .ok m' =>
        match envUpdate ρ x (.vecVal64 b') with
        | none => .error .Uninit
        | some ρ' => .ok ((ρ', m', π), .fellThrough)
      | .error e, _ => .error e
      | _, .error e => .error e
    | .ok _, .ok _, _, _ => .error .AssertFail
    | .error e, _, _, _ => .error e
    | _, .error e, _, _ => .error e
  | .vrealloc x se, ρ, m, π =>
    match memEvalExpr se ρ m π, envLookup ρ x, layoutLookup π x with
    | .ok (.u32 n), some (.vecVal b), some (a, t) =>
      match vecRealloc b n.toNat, memRealloc m a t n.toNat with
      | .ok b', .ok m' =>
        match envUpdate ρ x (.vecVal b') with
        | none => .error .Uninit
        | some ρ' => .ok ((ρ', m', π), .fellThrough)
      | .error e, _ => .error e
      | _, .error e => .error e
    | .ok _, _, _ => .error .AssertFail
    | .error e, _, _ => .error e
  | .vfree x, ρ, m, π =>
    match envLookup ρ x, layoutLookup π x with
    | some (.vecVal b), some (a, t) =>
      match vecFree b, memFree m a t with
      | .ok b', .ok m' =>
        match envUpdate ρ x (.vecVal b') with
        | none => .error .Uninit
        | some ρ' => .ok ((ρ', m', π), .fellThrough)
      | .error e, _ => .error e
      | _, .error e => .error e
    | some (.vecVal64 b), some (a, t) =>
      match vecFree64 b, memFree64 m a t with
      | .ok b', .ok m' =>
        match envUpdate ρ x (.vecVal64 b') with
        | none => .error .Uninit
        | some ρ' => .ok ((ρ', m', π), .fellThrough)
      | .error e, _ => .error e
      | _, .error e => .error e
    | _, _ => .error .AssertFail
  | .boxFree x, ρ, m, π =>
    match envLookup ρ x, layoutLookup π x with
    | some (.boxVal b), some (a, t) =>
      match boxFree b, memFree m a t with
      | .ok b', .ok m' =>
        match envUpdate ρ x (.boxVal b') with
        | none => .error .Uninit
        | some ρ' => .ok ((ρ', m', π), .fellThrough)
      | .error e, _ => .error e
      | _, .error e => .error e
    | _, _ => .error .AssertFail
  | .if_ c t e, ρ, m, π =>
    match memEvalExpr c ρ m π with
    | .error err => .error err
    | .ok (.b true) => memEvalStmtWith wh t ρ m π
    | .ok (.b false) => memEvalStmtWith wh e ρ m π
    | .ok _ => .error .AssertFail
  | .while_ c b, ρ, m, π => wh c b ρ m π
  | .break_, ρ, m, π => .ok ((ρ, m, π), .broke)
  | .continue_, ρ, m, π => .ok ((ρ, m, π), .continued)
  | .call _ _, ρ, m, π => .ok ((ρ, m, π), .fellThrough)
  | .callRet _ _ _, _, _, _ => .error .AssertFail
  | .return_ e, ρ, m, π =>
    match memEvalExpr e ρ m π with
    | .error err => .error err
    | .ok v => .ok ((ρ, m, π), .returned v)

/-- Zero-fuel `while_` handler (mirrors `evalStmtZeroHandler`). -/
def memEvalStmtZeroHandler : CExpr → CStmt → Env → Mem → Layout →
    Result ((Env × Mem × Layout) × Outcome) :=
  fun c _ ρ m π =>
    match memEvalExpr c ρ m π with
    | .ok (.b false) => .ok ((ρ, m, π), .fellThrough)
    | .ok _ => .error .AssertFail
    | .error err => .error err

/-- Zero fuel (mirrors `evalStmtZero`). -/
def memEvalStmtZero : CStmt → Env → Mem → Layout →
    Result ((Env × Mem × Layout) × Outcome) :=
  memEvalStmtWith memEvalStmtZeroHandler

/-- Positive-fuel `while_` handler (mirrors `evalStmtSuccHandler`). -/
def memEvalSuccHandler
    (rec : CStmt → Env → Mem → Layout →
      Result ((Env × Mem × Layout) × Outcome)) :
    CExpr → CStmt → Env → Mem → Layout →
      Result ((Env × Mem × Layout) × Outcome) :=
  fun c b ρ m π =>
    match memEvalExpr c ρ m π with
    | .error err => .error err
    | .ok (.b false) => .ok ((ρ, m, π), .fellThrough)
    | .ok (.b true) =>
      match rec b ρ m π with
      | .error e => .error e
      | .ok ((ρ', m', π'), .returned v) => .ok ((ρ', m', π'), .returned v)
      | .ok ((ρ', m', π'), .broke) => .ok ((ρ', m', π'), .fellThrough)
      | .ok ((ρ', m', π'), .continued) => rec (.while_ c b) ρ' m' π'
      | .ok ((ρ', m', π'), .fellThrough) => rec (.while_ c b) ρ' m' π'
    | .ok _ => .error .AssertFail

/-- Fuel-bounded memory statement evaluator (mirrors `evalStmtFuel`). -/
def memEvalStmtFuel : Nat → CStmt → Env → Mem → Layout →
    Result ((Env × Mem × Layout) × Outcome)
  | 0, s, ρ, m, π => memEvalStmtZero s ρ m π
  | f + 1, s, ρ, m, π =>
    memEvalStmtWith (memEvalSuccHandler (memEvalStmtFuel f)) s ρ m π

/-- `return_` agrees when the returned expression does. -/
theorem memEvalStmtFuel_return (f : Nat) (e : CExpr) (ρ : Env)
    (m : Mem) (π : Layout) (v : Value)
    (h : memEvalExpr e ρ m π = evalExpr e ρ)
    (hv : evalExpr e ρ = .ok v) :
    memEvalStmtFuel f (.return_ e) ρ m π =
      .ok ((ρ, m, π), .returned v) := by
  cases f <;>
    simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, h, hv]

/-- `return_` propagates expression errors (any fuel; mirrors
    `evalStmtFuel_return_err`). -/
theorem memEvalStmtFuel_return_err (f : Nat) (e : CExpr) (ρ : Env)
    (m : Mem) (π : Layout) (err : Panic)
    (h : memEvalExpr e ρ m π = .error err) :
    memEvalStmtFuel f (.return_ e) ρ m π = .error err := by
  cases f with
  | zero =>
    simp only [memEvalStmtFuel, memEvalStmtZero] at h ⊢
    simp only [memEvalStmtWith, h]
  | succ g =>
    simp only [memEvalStmtFuel] at h ⊢
    simp only [memEvalStmtWith, h]

/-- `assign` agrees when the assigned expression does. -/
theorem memEvalStmtFuel_assign (f : Nat) (x : String) (e : CExpr)
    (ρ : Env) (m : Mem) (π : Layout) (v : Value) (ρ' : Env)
    (h : memEvalExpr e ρ m π = evalExpr e ρ)
    (hv : evalExpr e ρ = .ok v) (hu : envUpdate ρ x v = some ρ') :
    memEvalStmtFuel f (.assign x e) ρ m π =
      .ok ((ρ', m, π), .fellThrough) := by
  cases f <;> simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, h, hv, hu]

/-! ## Function entry: argument binding with tag creation -/

/-- Bind actuals to formals, lifting heap-like values into fresh blocks
    (tag creation at bind: each `arr32` / live `vecVal` gets a fresh
    `(addr, tag)` pin; scalars need none). Lifting a freed block keeps
    it dead (`live = !freed`, so use-after-free stays loud). -/
def bindMemArgs : List Param → List Value → Mem → Option (Env × Mem × Layout)
  | [], [], m => some ([], m, [])
  | p :: ps, v :: vs, m =>
    match bindMemArgs ps vs m with
    | none => none
    | some (ρ, m', π) =>
      match v with
      | .arr32 l =>
        let (m'', a) := memAllocData m' l
        some (((p.name, v) :: ρ), m'', (p.name, a, a) :: π)
      | .vecVal b =>
        let (m'', a) := memAllocData m' b.val
        some (((p.name, v) :: ρ),
          ⟨m''.next, (a, ⟨a, !b.freed, b.val⟩) :: m''.blocks, m''.blocks64⟩,
          (p.name, a, a) :: π)
      | .vecVal64 b =>
        let (m'', a) := memAllocData64 m' b.val
        some (((p.name, v) :: ρ),
          ⟨m''.next, m''.blocks,
            (a, ⟨a, !b.freed, b.val⟩) :: m''.blocks64⟩,
          (p.name, a, a) :: π)
      | .optVal v =>
        let words : List (BitVec 32) :=
          match v with
          | some x => [x, 1]
          | none => [0, 0]
        let (m'', a) := memAllocData m' words
        some (((p.name, .optVal v) :: ρ), m'', (p.name, a, a) :: π)
      | .spanVal l =>
        -- The reified view plus the 32-bit extent word up front
        -- (the `{ptr, extent}` object model: word 0 is the extent,
        -- words `1+i` are the viewed elements; N4d-iii).
        let (m'', a) := memAllocData m' ((BitVec.ofNat 32 l.length) :: l)
        some (((p.name, .spanVal l) :: ρ), m'', (p.name, a, a) :: π)
      | .stdVecVal l =>
        -- The reified elements plus the 32-bit length word up front
        -- (the heap-triple snapshot model: word 0 is the length,
        -- words `1+i` are the elements; N4d-iv-a, reads only).
        let (m'', a) := memAllocData m' ((BitVec.ofNat 32 l.length) :: l)
        some (((p.name, .stdVecVal l) :: ρ), m'', (p.name, a, a) :: π)
      | _ => some (((p.name, v) :: ρ), m', π)
  | _, _, _ => none

/-- Whole-function memory semantics at explicit fuel (mirrors
    `evalFuncFuel`; the final `Mem`/`Layout` are discarded — the
    transfer only equates the returned value — but any tag failure on
    the path is loud). -/
def memEvalFuncFuel (fuel : Nat) (f : Func) (args : List Value) :
    Result Value :=
  match bindMemArgs f.args args emptyMem with
  | none => .error .AssertFail
  | some (ρ, m, π) =>
    match memEvalStmtFuel fuel f.body ρ m π with
    | .error e => .error e
    | .ok (_, .returned v) => .ok v
    | .ok _ => .error .AssertFail

/-! ## Memory program layer (S1 callers: `callRet` dispatch) -/

/-- Depth-1 memory program statement evaluation. Mirrors `evalProgStmt`
    step for step: `callRet dst f xs` looks up the actuals, dispatches
    to the call-free callee via `memEvalFuncFuel` at the same fuel, and
    extends the environment with the result (caller `Mem`/`Layout`
    threaded through untouched — the callee runs on its own fresh
    entry blocks, so no aliasing is introduced); `seq` recurses;
    everything else delegates to `memEvalStmtFuel`. Callee errors
    propagate; unknown callees / unbound actuals are loud. -/
def memEvalProgStmt (prog : Prog) (fuel : Nat) : CStmt → Env → Mem → Layout →
    Result ((Env × Mem × Layout) × Outcome)
  | .callRet dst f xs, ρ, m, π =>
    match lookupArgs ρ xs with
    | none => .error .Uninit
    | some vs =>
      match findFunc prog f with
      | none => .error .AssertFail
      | some callee =>
        match memEvalFuncFuel fuel callee vs with
        | .error e => .error e
        | .ok ret => .ok ((envExtend ρ dst ret, m, π), .fellThrough)
  | .seq a b, ρ, m, π =>
    match memEvalProgStmt prog fuel a ρ m π with
    | .error e => .error e
    | .ok ((ρ', m', π'), .returned v) => .ok ((ρ', m', π'), .returned v)
    | .ok ((ρ', m', π'), .broke) => .ok ((ρ', m', π'), .broke)
    | .ok ((ρ', m', π'), .continued) => .ok ((ρ', m', π'), .continued)
    | .ok ((ρ', m', π'), .fellThrough) =>
      memEvalProgStmt prog fuel b ρ' m' π'
  | .cleanup body, ρ, m, π => memEvalProgStmt prog fuel body ρ m π
  | .if_ c t e, ρ, m, π =>
    match memEvalExpr c ρ m π with
    | .ok (.b true) => memEvalProgStmt prog fuel t ρ m π
    | .ok (.b false) => memEvalProgStmt prog fuel e ρ m π
    | _ => .error .AssertFail
  | s, ρ, m, π => memEvalStmtFuel fuel s ρ m π

/-- `cleanup` scopes sequence on the memory program layer too (the M2b
    `acc_two` entry shape; mirrors `evalProgStmt_cleanup`). -/
theorem memEvalProgStmt_cleanup (prog : Prog) (fuel : Nat) (body : CStmt)
    (ρ : Env) (m : Mem) (π : Layout) :
    memEvalProgStmt prog fuel (.cleanup body) ρ m π =
      memEvalProgStmt prog fuel body ρ m π := rfl

/-- `callRet` with resolved actuals + callee runs the callee. -/
theorem memEvalProgStmt_callRet_ok (prog : Prog) (fuel : Nat)
    (dst f : String) (xs : List String) (ρ : Env) (m : Mem) (π : Layout)
    (vs : List Value) (callee : Func) (ret : Value)
    (hargs : lookupArgs ρ xs = some vs)
    (hfind : findFunc prog f = some callee)
    (hcall : memEvalFuncFuel fuel callee vs = .ok ret) :
    memEvalProgStmt prog fuel (.callRet dst f xs) ρ m π =
      .ok ((envExtend ρ dst ret, m, π), .fellThrough) := by
  simp [memEvalProgStmt, hargs, hfind, hcall]

/-- `callRet` propagates callee errors. -/
theorem memEvalProgStmt_callRet_err (prog : Prog) (fuel : Nat)
    (dst f : String) (xs : List String) (ρ : Env) (m : Mem) (π : Layout)
    (vs : List Value) (callee : Func) (e : Panic)
    (hargs : lookupArgs ρ xs = some vs)
    (hfind : findFunc prog f = some callee)
    (hcall : memEvalFuncFuel fuel callee vs = .error e) :
    memEvalProgStmt prog fuel (.callRet dst f xs) ρ m π = .error e := by
  simp [memEvalProgStmt, hargs, hfind, hcall]

/-- `callRet` to an unknown callee is rejected, never silently modeled. -/
theorem memEvalProgStmt_callRet_unknown (prog : Prog) (fuel : Nat)
    (dst f : String) (xs : List String) (ρ : Env) (m : Mem) (π : Layout)
    (vs : List Value)
    (hargs : lookupArgs ρ xs = some vs)
    (hfind : findFunc prog f = none) :
    memEvalProgStmt prog fuel (.callRet dst f xs) ρ m π =
      .error .AssertFail := by
  simp [memEvalProgStmt, hargs, hfind]

/-- `callRet` with unbound actuals is `Uninit`. -/
theorem memEvalProgStmt_callRet_unbound (prog : Prog) (fuel : Nat)
    (dst f : String) (xs : List String) (ρ : Env) (m : Mem) (π : Layout)
    (hargs : lookupArgs ρ xs = none) :
    memEvalProgStmt prog fuel (.callRet dst f xs) ρ m π =
      .error .Uninit := by
  simp [memEvalProgStmt, hargs]

/-- Whole-program memory function semantics: bind via `bindMemArgs`
    (fresh entry blocks), run the body under the program, demand a
    `return` (falling off the end is `AssertFail`, as before). -/
def memEvalProgFunc (prog : Prog) (fuel : Nat) (f : Func)
    (args : List Value) : Result Value :=
  match bindMemArgs f.args args emptyMem with
  | none => .error .AssertFail
  | some (ρ, m, π) =>
    match memEvalProgStmt prog fuel f.body ρ m π with
    | .error e => .error e
    | .ok (_, .returned v) => .ok v
    | .ok (_, .broke) => .error .AssertFail
    | .ok (_, .continued) => .error .AssertFail
    | .ok (_, .fellThrough) => .error .AssertFail

/-- `seq` short-circuits on error in the first component. -/
theorem memEvalProgStmt_seq_err (prog : Prog) (fuel : Nat) (a b : CStmt)
    (ρ : Env) (m : Mem) (π : Layout) (e : Panic)
    (h : memEvalProgStmt prog fuel a ρ m π = .error e) :
    memEvalProgStmt prog fuel (.seq a b) ρ m π = .error e := by
  simp only [memEvalProgStmt, h]

/-- `seq` threads the environment on fall-through. -/
theorem memEvalProgStmt_seq_fallthrough (prog : Prog) (fuel : Nat)
    (a b : CStmt) (ρ : Env) (m : Mem) (π : Layout)
    (ρ' : Env) (m' : Mem) (π' : Layout)
    (h : memEvalProgStmt prog fuel a ρ m π =
      .ok ((ρ', m', π'), .fellThrough)) :
    memEvalProgStmt prog fuel (.seq a b) ρ m π =
      memEvalProgStmt prog fuel b ρ' m' π' := by
  simp only [memEvalProgStmt, h]

/-- `seq` short-circuits on `returned` in the first component (N4b: the
    early-return branch of `scope_early`). -/
theorem memEvalProgStmt_seq_returned (prog : Prog) (fuel : Nat)
    (a b : CStmt) (ρ : Env) (m : Mem) (π : Layout)
    (ρ' : Env) (m' : Mem) (π' : Layout) (v : Value)
    (h : memEvalProgStmt prog fuel a ρ m π =
      .ok ((ρ', m', π'), .returned v)) :
    memEvalProgStmt prog fuel (.seq a b) ρ m π =
      .ok ((ρ', m', π'), .returned v) := by
  simp only [memEvalProgStmt, h]

/-- `if_` on `true` runs the branch at memory-program level (N4b). -/
theorem memEvalProgStmt_if_true (prog : Prog) (fuel : Nat)
    (c : CExpr) (t e : CStmt) (ρ : Env) (m : Mem) (π : Layout)
    (h : memEvalExpr c ρ m π = .ok (.b true)) :
    memEvalProgStmt prog fuel (.if_ c t e) ρ m π =
      memEvalProgStmt prog fuel t ρ m π := by
  simp only [memEvalProgStmt, h]

/-- `if_` on `false` runs the else-branch at memory-program level. -/
theorem memEvalProgStmt_if_false (prog : Prog) (fuel : Nat)
    (c : CExpr) (t e : CStmt) (ρ : Env) (m : Mem) (π : Layout)
    (h : memEvalExpr c ρ m π = .ok (.b false)) :
    memEvalProgStmt prog fuel (.if_ c t e) ρ m π =
      memEvalProgStmt prog fuel e ρ m π := by
  simp only [memEvalProgStmt, h]

/-- `return_` under a program delegates to the memory evaluator. -/
theorem memEvalProgStmt_return (prog : Prog) (fuel : Nat) (e : CExpr)
    (ρ : Env) (m : Mem) (π : Layout) (v : Value)
    (h : memEvalExpr e ρ m π = .ok v) :
    memEvalProgStmt prog fuel (.return_ e) ρ m π =
      .ok ((ρ, m, π), .returned v) := by
  cases fuel with
  | zero => simp [memEvalProgStmt, memEvalStmtFuel, memEvalStmtZero,
      memEvalStmtWith, h]
  | succ g => simp [memEvalProgStmt, memEvalStmtFuel, memEvalStmtWith, h]

/-- Entry footprints are pairwise disjoint (the M3a `oracleNoalias`:
    M3b will show the `derivedNoalias` text check implies it). -/
def oracleNoalias (f : Func) (args : List Value) : Prop :=
  ∃ ρ m π, bindMemArgs f.args args emptyMem = some (ρ, m, π) ∧
    LayoutNoAlias π

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
    (h : memEvalExpr e ρ m π = evalExpr e ρ)
    (hv : evalExpr e ρ = .ok v) :
    memEvalStmtFuel f (.let_ x ty e) ρ m π =
      .ok ((((x, v) :: ρ, m, π)), .fellThrough) := by
  match e with
  | .vnew se => exact absurd rfl (hnot se)
  | .boxNew se => exact absurd rfl (hnotBox se)
  | _ =>
    cases f <;> simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith, h, hv]

/-- Pure `let_` propagates expression errors (any fuel; mirrors
    `evalStmtFuel_let_err`; allocating arms are excluded as in
    `memEvalStmtFuel_let_pure`). -/
theorem memEvalStmtFuel_let_err (f : Nat) (x : String) (ty : CType)
    (e : CExpr) (ρ : Env) (m : Mem) (π : Layout) (err : Panic)
    (hnot : ∀ se, e ≠ .vnew se)
    (hnotBox : ∀ se, e ≠ .boxNew se)
    (h : memEvalExpr e ρ m π = .error err) :
    memEvalStmtFuel f (.let_ x ty e) ρ m π = .error err := by
  match e with
  | .vnew se => exact absurd rfl (hnot se)
  | .boxNew se => exact absurd rfl (hnotBox se)
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
