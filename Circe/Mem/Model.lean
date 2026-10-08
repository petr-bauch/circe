/-
Circe.Mem.Model — the addressful memory model: blocks, layout,
consistency, `memEval`/`memEvalProgStmt`/`memEvalProgFunc`,
`bindMemArgs`, and `oracleNoalias`; transfer instances live in
`Circe.Mem.Agree`.
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
  | .usub a b, ρ, m, π =>
    match memEvalExpr a ρ m π, memEvalExpr b ρ m π with
    | .ok (.u32 x), .ok (.u32 y) => .ok (.u32 (x - y))
    | .ok (.u64 x), .ok (.u64 y) => .ok (.u64 (x - y))
    | .ok _, .ok _ => .error .AssertFail
    | .error e, _ => .error e
    | _, .error e => .error e
  | .s64diff a b, ρ, m, π =>
    match memEvalExpr a ρ m π, memEvalExpr b ρ m π with
    | .ok (.u64 x), .ok (.u64 y) => .ok (.i64 (x - y))
    | .ok _, .ok _ => .error .AssertFail
    | .error e, _ => .error e
    | _, .error e => .error e
  | .tif c t e, ρ, m, π =>
    match memEvalExpr c ρ m π with
    | .error err => .error err
    | .ok (.b true) => memEvalExpr t ρ m π
    | .ok (.b false) => memEvalExpr e ρ m π
    | .ok _ => .error .AssertFail
  | .umul a b, ρ, m, π =>
    match memEvalExpr a ρ m π, memEvalExpr b ρ m π with
    | .ok (.u32 x), .ok (.u32 y) => .ok (.u32 (x * y))
    | .ok (.u64 x), .ok (.u64 y) => .ok (.u64 (x * y))
    | .ok _, .ok _ => .error .AssertFail
    | .error e, _ => .error e
    | _, .error e => .error e
  | .neg a, ρ, m, π =>
    match memEvalExpr a ρ m π with
    | .ok (.i32 x) => (checkedNegI32 x).map .i32
    | .ok _ => .error .AssertFail
    | .error e => .error e
  | .sdiv a b, ρ, m, π =>
    match memEvalExpr a ρ m π, memEvalExpr b ρ m π with
    | .ok (.i32 x), .ok (.i32 y) => (checkedDivI32 x y).map .i32
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
  | .une a b, ρ, m, π =>
    match memEvalExpr a ρ m π, memEvalExpr b ρ m π with
    | .ok (.u32 x), .ok (.u32 y) => .ok (.b (x != y))
    | .ok (.u64 x), .ok (.u64 y) => .ok (.b (x != y))
    | .ok (.i32 x), .ok (.i32 y) => .ok (.b (x != y))
    | .ok (.i64 x), .ok (.i64 y) => .ok (.b (x != y))
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
  | .idxu arr ie, ρ, m, π =>
    match layoutLookup π arr with
    | none => .error .AssertFail
    | some (a, t) =>
      match memEvalExpr ie ρ m π, envLookup ρ arr with
      | .ok (.u64 i), some (.arr32 l) =>
        match memLoad m a t i.toNat, l[i.toNat]? with
        | .ok w, some v => if w == v then .ok (.u32 v) else .error .AssertFail
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
  | .viewLen s, ρ, m, π =>
    match layoutLookup π s with
    | none => .error .AssertFail
    | some (a, t) =>
      match memLoad m a t 0, envLookup ρ s with
      | .ok w, some (.viewVal l) =>
        if w == BitVec.ofNat 32 l.length then
          .ok (.u64 (BitVec.ofNat 64 l.length))
        else .error .AssertFail
      | .error e, _ => .error e
      | _, _ => .error .AssertFail
  | .viewAt s ie, ρ, m, π =>
    match layoutLookup π s with
    | none => .error .AssertFail
    | some (a, t) =>
      match memEvalExpr ie ρ m π, envLookup ρ s with
      | .ok (.u64 i), some (.viewVal l) =>
        match memLoad m a t (i.toNat + 1), l[i.toNat]? with
        | .ok w, some x =>
          if w == BitVec.ofNat 32 x.toNat then
            .ok (.i32 (x.signExtend 32))
          else .error .AssertFail
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
  | .vgrowLen s, ρ, m, π =>
    match layoutLookup π s with
    | none => .error .AssertFail
    | some (a, t) =>
      match memLoad m a t 0, envLookup ρ s with
      | .ok w, some (.stdVecOwned _ len _) =>
        if w == BitVec.ofNat 32 len then
          .ok (.u64 (BitVec.ofNat 64 len))
        else .error .AssertFail
      | .error e, _ => .error e
      | _, _ => .error .AssertFail
  | .vgrowCap s, ρ, m, π =>
    match layoutLookup π s with
    | none => .error .AssertFail
    | some (a, t) =>
      match memLoad m a t 1, envLookup ρ s with
      | .ok w, some (.stdVecOwned _ _ cap) =>
        if w == BitVec.ofNat 32 cap then
          .ok (.u64 (BitVec.ofNat 64 cap))
        else .error .AssertFail
      | .error e, _ => .error e
      | _, _ => .error .AssertFail
  | .vgrowAt s ie, ρ, m, π =>
    match layoutLookup π s with
    | none => .error .AssertFail
    | some (a, t) =>
      match memEvalExpr ie ρ m π, envLookup ρ s with
      | .ok (.u64 i), some (.stdVecOwned b len _) =>
        match memLoad m a t (i.toNat + 2), b.val[i.toNat]? with
        | .ok w, some v =>
          if w == v then
            if i.toNat < len then .ok (.i32 v) else .error .OOB
          else .error .AssertFail
        | .error e, _ => .error e
        | _, _ => .error .AssertFail
      | .ok _, _ => .error .AssertFail
      | .error e, _ => .error e
  | .vgrowNew ce, ρ, m, π =>
    match memEvalExpr ce ρ m π with
    | .error e => .error e
    | .ok (.u64 n) =>
      match vecNew n.toNat with
      | .error e => .error e
      | .ok v => .ok (.stdVecOwned v 0 n.toNat)
    | .ok _ => .error .AssertFail
  | .vgrowSetLen s e, ρ, m, π =>
    match envLookup ρ s with
    | none => .error .Uninit
    | some (.stdVecOwned b _ cap) =>
      match memEvalExpr e ρ m π with
      | .error err => .error err
      | .ok (.u64 n) => .ok (.stdVecOwned b n.toNat cap)
      | .ok _ => .error .AssertFail
    | some _ => .error .AssertFail
  | .u64ofI64 e, ρ, m, π =>
    match memEvalExpr e ρ m π with
    | .error err => .error err
    | .ok (.i64 d) => .ok (.u64 d)
    | .ok _ => .error .AssertFail
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

/-- `idxu` agreement under consistency (N9: the unsigned array read
    for the insertion-sort element comparison) — mirrors `idxi`, with
    the word delivered as `u32`. -/
theorem memEvalExpr_idxu_hit (arr : String) (ie : CExpr) (ρ : Env)
    (m : Mem) (π : Layout) (l : List (BitVec 32)) (i : BitVec 64)
    (x : BitVec 32) (a : Addr) (t : Nat)
    (hlay : layoutLookup π arr = some (a, t))
    (harr : envLookup ρ arr = some (.arr32 l))
    (hie : memEvalExpr ie ρ m π = evalExpr ie ρ)
    (hieval : evalExpr ie ρ = .ok (.u64 i))
    (hmem : memLoad m a t i.toNat = .ok x)
    (hval : l[i.toNat]? = some x) :
    memEvalExpr (.idxu arr ie) ρ m π = evalExpr (.idxu arr ie) ρ := by
  simp only [memEvalExpr, evalExpr, hlay, hie, hieval, harr, hmem, hval,
    beq_self_eq_true, ↓reduceIte]

/-- `idxu` OOB agreement (mirrors `evalExpr_idxu_oob`). -/
theorem memEvalExpr_idxu_oob (arr : String) (ie : CExpr) (ρ : Env)
    (m : Mem) (π : Layout) (l : List (BitVec 32)) (i : BitVec 64)
    (a : Addr) (t : Nat)
    (hlay : layoutLookup π arr = some (a, t))
    (harr : envLookup ρ arr = some (.arr32 l))
    (hie : memEvalExpr ie ρ m π = evalExpr ie ρ)
    (hieval : evalExpr ie ρ = .ok (.u64 i))
    (hmem : memLoad m a t i.toNat = .error .OOB)
    (hval : l[i.toNat]? = none) :
    memEvalExpr (.idxu arr ie) ρ m π = evalExpr (.idxu arr ie) ρ := by
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

/-- `viewLen` agreement: the length word in memory matches the
    `viewVal` length, so both sides report the same `u64` word. -/
theorem memEvalExpr_viewLen_hit (s : String) (ρ : Env)
    (m : Mem) (π : Layout) (l : List (BitVec 8)) (a : Addr) (t : Nat)
    (hlay : layoutLookup π s = some (a, t))
    (hs : envLookup ρ s = some (.viewVal l))
    (hmem : memLoad m a t 0 = .ok (BitVec.ofNat 32 l.length)) :
    memEvalExpr (.viewLen s) ρ m π = evalExpr (.viewLen s) ρ := by
  simp only [memEvalExpr, evalExpr, hlay, hs, hmem, beq_self_eq_true,
    ↓reduceIte]

/-- `viewAt` agreement on an in-bounds index: the memory word holds
    the zero-extended byte (one byte per word cell, the word-level
    abstraction — native packs bytes, the model does not), so both
    sides deliver the sign-extended `i32`. -/
theorem memEvalExpr_viewAt_hit (s : String) (ie : CExpr) (ρ : Env)
    (m : Mem) (π : Layout) (l : List (BitVec 8)) (i : BitVec 64)
    (x : BitVec 8) (a : Addr) (t : Nat)
    (hlay : layoutLookup π s = some (a, t))
    (hs : envLookup ρ s = some (.viewVal l))
    (hie : memEvalExpr ie ρ m π = evalExpr ie ρ)
    (hieval : evalExpr ie ρ = .ok (.u64 i))
    (hmem : memLoad m a t (i.toNat + 1) = .ok (BitVec.ofNat 32 x.toNat))
    (hval : l[i.toNat]? = some x) :
    memEvalExpr (.viewAt s ie) ρ m π = evalExpr (.viewAt s ie) ρ := by
  simp only [memEvalExpr, evalExpr, hlay, hie, hieval, hs, hmem, hval,
    beq_self_eq_true, ↓reduceIte]

/-- `viewAt` OOB agreement: the memory load itself fails `OOB`
    past the reified bytes, so both sides fail `OOB` loudly. -/
theorem memEvalExpr_viewAt_oob (s : String) (ie : CExpr) (ρ : Env)
    (m : Mem) (π : Layout) (l : List (BitVec 8)) (i : BitVec 64)
    (a : Addr) (t : Nat)
    (hlay : layoutLookup π s = some (a, t))
    (hs : envLookup ρ s = some (.viewVal l))
    (hie : memEvalExpr ie ρ m π = evalExpr ie ρ)
    (hieval : evalExpr ie ρ = .ok (.u64 i))
    (hmem : memLoad m a t (i.toNat + 1) = .error .OOB)
    (hval : l[i.toNat]? = none) :
    memEvalExpr (.viewAt s ie) ρ m π = evalExpr (.viewAt s ie) ρ := by
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

/-- `usub` agreement: both sides evaluate the operands the same way,
    so the wrapping subtraction agrees (N4d-iv-b1). -/
theorem memEvalExpr_usub_agree (a b : CExpr) (ρ : Env) (m : Mem)
    (π : Layout)
    (ha : memEvalExpr a ρ m π = evalExpr a ρ)
    (hb : memEvalExpr b ρ m π = evalExpr b ρ) :
    memEvalExpr (.usub a b) ρ m π = evalExpr (.usub a b) ρ := by
  simp only [memEvalExpr, evalExpr, ha, hb]
  rfl

/-- `s64diff` agreement: both sides evaluate the offsets the same way,
    so the bit-exact difference agrees (N4d-iv-b1). -/
theorem memEvalExpr_s64diff_agree (a b : CExpr) (ρ : Env) (m : Mem)
    (π : Layout)
    (ha : memEvalExpr a ρ m π = evalExpr a ρ)
    (hb : memEvalExpr b ρ m π = evalExpr b ρ) :
    memEvalExpr (.s64diff a b) ρ m π = evalExpr (.s64diff a b) ρ := by
  simp only [memEvalExpr, evalExpr, ha, hb]
  rfl

/-- `ult` agreement: both sides compare the same words
    (N4d-iv-b1; mirrors `memEvalExpr_usub_agree`). -/
theorem memEvalExpr_ult_agree (a b : CExpr) (ρ : Env) (m : Mem)
    (π : Layout)
    (ha : memEvalExpr a ρ m π = evalExpr a ρ)
    (hb : memEvalExpr b ρ m π = evalExpr b ρ) :
    memEvalExpr (.ult a b) ρ m π = evalExpr (.ult a b) ρ := by
  simp only [memEvalExpr, evalExpr, ha, hb]
  rfl

/-- `uadd` agreement: both sides add the same words
    (N4d-iv-b1; mirrors `memEvalExpr_usub_agree`). -/
theorem memEvalExpr_uadd_agree (a b : CExpr) (ρ : Env) (m : Mem)
    (π : Layout)
    (ha : memEvalExpr a ρ m π = evalExpr a ρ)
    (hb : memEvalExpr b ρ m π = evalExpr b ρ) :
    memEvalExpr (.uadd a b) ρ m π = evalExpr (.uadd a b) ρ := by
  simp only [memEvalExpr, evalExpr, ha, hb]
  rfl

/-- `vgrowNew` agreement: the capacity expression agrees, and
    `vecNew` runs purely on both sides (no memory interaction;
    N4d-iv-b1). -/
theorem memEvalExpr_vgrowNew_agree (ce : CExpr) (ρ : Env) (m : Mem)
    (π : Layout)
    (h : memEvalExpr ce ρ m π = evalExpr ce ρ) :
    memEvalExpr (.vgrowNew ce) ρ m π = evalExpr (.vgrowNew ce) ρ := by
  simp only [memEvalExpr, evalExpr, h]
  rfl

/-- `vgrowSetLen` agreement: the rebuild is pure on both sides (same
    buffer and capacity, length from the agreed subexpression;
    N4d-iv-b2). -/
theorem memEvalExpr_vgrowSetLen_agree (s : String) (e : CExpr) (ρ : Env)
    (m : Mem) (π : Layout)
    (h : memEvalExpr e ρ m π = evalExpr e ρ) :
    memEvalExpr (.vgrowSetLen s e) ρ m π =
      evalExpr (.vgrowSetLen s e) ρ := by
  simp only [memEvalExpr, evalExpr, h]
  rfl

/-- `u64ofI64` agreement: the retag is pure on both sides (N4d-iv-b2). -/
theorem memEvalExpr_u64ofI64_agree (e : CExpr) (ρ : Env) (m : Mem)
    (π : Layout)
    (h : memEvalExpr e ρ m π = evalExpr e ρ) :
    memEvalExpr (.u64ofI64 e) ρ m π = evalExpr (.u64ofI64 e) ρ := by
  simp only [memEvalExpr, evalExpr, h]
  rfl

/-- `une` agreement: the retag-free comparison is pure on both sides
    (N4d-iv-b2: the emplace `len ≠ cap` guard). -/
theorem memEvalExpr_une_agree (a b : CExpr) (ρ : Env) (m : Mem)
    (π : Layout)
    (ha : memEvalExpr a ρ m π = evalExpr a ρ)
    (hb : memEvalExpr b ρ m π = evalExpr b ρ) :
    memEvalExpr (.une a b) ρ m π = evalExpr (.une a b) ρ := by
  simp only [memEvalExpr, evalExpr, ha, hb]
  rfl

/-- `ueq` agreement: both sides compare the same words
    (N7c: the const-iterator `operator==`). -/
theorem memEvalExpr_ueq_agree (a b : CExpr) (ρ : Env) (m : Mem)
    (π : Layout)
    (ha : memEvalExpr a ρ m π = evalExpr a ρ)
    (hb : memEvalExpr b ρ m π = evalExpr b ρ) :
    memEvalExpr (.ueq a b) ρ m π = evalExpr (.ueq a b) ρ := by
  simp only [memEvalExpr, evalExpr, ha, hb]
  rfl

/-- `tif` agreement on a true condition: both sides take the
    then-branch. -/
theorem memEvalExpr_tif_true (c t e : CExpr) (ρ : Env) (m : Mem)
    (π : Layout)
    (hc : memEvalExpr c ρ m π = evalExpr c ρ)
    (hvc : evalExpr c ρ = .ok (.b true))
    (ht : memEvalExpr t ρ m π = evalExpr t ρ) :
    memEvalExpr (.tif c t e) ρ m π = evalExpr (.tif c t e) ρ := by
  simp only [memEvalExpr, evalExpr, hc, hvc, ht,
    evalExpr_tif_true c t e ρ hvc]

/-- `tif` agreement on a false condition: both sides take the
    else-branch. -/
theorem memEvalExpr_tif_false (c t e : CExpr) (ρ : Env) (m : Mem)
    (π : Layout)
    (hc : memEvalExpr c ρ m π = evalExpr c ρ)
    (hvc : evalExpr c ρ = .ok (.b false))
    (he : memEvalExpr e ρ m π = evalExpr e ρ) :
    memEvalExpr (.tif c t e) ρ m π = evalExpr (.tif c t e) ρ := by
  simp only [memEvalExpr, evalExpr, hc, hvc, he,
    evalExpr_tif_false c t e ρ hvc]

/-- `vgrowLen` agreement: the length header word in memory matches the
    triple length, so both sides report the same `u64` word
    (N4d-iv-b1; mirrors `memEvalExpr_stdVecLen_hit`). -/
theorem memEvalExpr_vgrowLen_hit (s : String) (ρ : Env)
    (m : Mem) (π : Layout) (b : Vec32) (len cap : Nat)
    (a : Addr) (t : Nat)
    (hlay : layoutLookup π s = some (a, t))
    (hs : envLookup ρ s = some (.stdVecOwned b len cap))
    (hmem : memLoad m a t 0 = .ok (BitVec.ofNat 32 len)) :
    memEvalExpr (.vgrowLen s) ρ m π = evalExpr (.vgrowLen s) ρ := by
  simp only [memEvalExpr, evalExpr, hlay, hs, hmem, beq_self_eq_true,
    ↓reduceIte]

/-- `vgrowCap` agreement: the capacity header word in memory matches
    the triple capacity (N4d-iv-b1). -/
theorem memEvalExpr_vgrowCap_hit (s : String) (ρ : Env)
    (m : Mem) (π : Layout) (b : Vec32) (len cap : Nat)
    (a : Addr) (t : Nat)
    (hlay : layoutLookup π s = some (a, t))
    (hs : envLookup ρ s = some (.stdVecOwned b len cap))
    (hmem : memLoad m a t 1 = .ok (BitVec.ofNat 32 cap)) :
    memEvalExpr (.vgrowCap s) ρ m π = evalExpr (.vgrowCap s) ρ := by
  simp only [memEvalExpr, evalExpr, hlay, hs, hmem, beq_self_eq_true,
    ↓reduceIte]

/-- `vgrowAt` agreement on an in-bounds offset: the stored word in
    memory matches the buffer word, so both sides deliver it
    (N4d-iv-b1; the two-word header shifts memory offsets by two). -/
theorem memEvalExpr_vgrowAt_hit (s : String) (ie : CExpr) (ρ : Env)
    (m : Mem) (π : Layout) (b : Vec32) (len cap : Nat)
    (i : BitVec 64) (x : BitVec 32) (a : Addr) (t : Nat)
    (hlay : layoutLookup π s = some (a, t))
    (hs : envLookup ρ s = some (.stdVecOwned b len cap))
    (hie : memEvalExpr ie ρ m π = evalExpr ie ρ)
    (hieval : evalExpr ie ρ = .ok (.u64 i))
    (hlive : b.freed = false)
    (hmem : memLoad m a t (i.toNat + 2) = .ok x)
    (hval : b.val[i.toNat]? = some x)
    (hlt : i.toNat < len) :
    memEvalExpr (.vgrowAt s ie) ρ m π = evalExpr (.vgrowAt s ie) ρ := by
  simp only [memEvalExpr, evalExpr, hlay, hie, hieval, hs, hmem, hval,
    hlive, hlt, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]

/-- `vgrowAt` agreement past the length: the slot is live storage but
    uninitialized, so both sides fail `OOB`. -/
theorem memEvalExpr_vgrowAt_oob_len (s : String) (ie : CExpr) (ρ : Env)
    (m : Mem) (π : Layout) (b : Vec32) (len cap : Nat)
    (i : BitVec 64) (x : BitVec 32) (a : Addr) (t : Nat)
    (hlay : layoutLookup π s = some (a, t))
    (hs : envLookup ρ s = some (.stdVecOwned b len cap))
    (hie : memEvalExpr ie ρ m π = evalExpr ie ρ)
    (hieval : evalExpr ie ρ = .ok (.u64 i))
    (hlive : b.freed = false)
    (hmem : memLoad m a t (i.toNat + 2) = .ok x)
    (hval : b.val[i.toNat]? = some x)
    (hlt : ¬ i.toNat < len) :
    memEvalExpr (.vgrowAt s ie) ρ m π = evalExpr (.vgrowAt s ie) ρ := by
  simp only [memEvalExpr, evalExpr, hlay, hie, hieval, hs, hmem, hval,
    hlive, hlt, beq_self_eq_true, Bool.false_eq_true, ↓reduceIte]

/-- `vgrowAt` agreement past the storage words: both sides fail `OOB`. -/
theorem memEvalExpr_vgrowAt_oob_miss (s : String) (ie : CExpr) (ρ : Env)
    (m : Mem) (π : Layout) (b : Vec32) (len cap : Nat)
    (i : BitVec 64) (a : Addr) (t : Nat)
    (hlay : layoutLookup π s = some (a, t))
    (hs : envLookup ρ s = some (.stdVecOwned b len cap))
    (hie : memEvalExpr ie ρ m π = evalExpr ie ρ)
    (hieval : evalExpr ie ρ = .ok (.u64 i))
    (hlive : b.freed = false)
    (hmem : memLoad m a t (i.toNat + 2) = .error .OOB)
    (hval : b.val[i.toNat]? = none) :
    memEvalExpr (.vgrowAt s ie) ρ m π = evalExpr (.vgrowAt s ie) ρ := by
  simp only [memEvalExpr, evalExpr, hlay, hie, hieval, hs, hmem, hval,
    hlive, Bool.false_eq_true, if_false]

/-- `vgrowAt` agreement on a consumed buffer: the dead block loads
    `AssertFail`, matching the value-side use-after-free. -/
theorem memEvalExpr_vgrowAt_freed (s : String) (ie : CExpr) (ρ : Env)
    (m : Mem) (π : Layout) (b : Vec32) (len cap : Nat)
    (i : BitVec 64) (a : Addr) (t : Nat)
    (hlay : layoutLookup π s = some (a, t))
    (hs : envLookup ρ s = some (.stdVecOwned b len cap))
    (hie : memEvalExpr ie ρ m π = evalExpr ie ρ)
    (hieval : evalExpr ie ρ = .ok (.u64 i))
    (hfree : b.freed = true)
    (hmem : memLoad m a t (i.toNat + 2) = .error .AssertFail) :
    memEvalExpr (.vgrowAt s ie) ρ m π = evalExpr (.vgrowAt s ie) ρ := by
  simp only [memEvalExpr, evalExpr, hlay, hie, hieval, hs, hmem, hfree,
    ↓reduceIte]

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
  | .let_ x _ (.vgrowNew ce), ρ, m, π =>
    match memEvalExpr ce ρ m π with
    | .error err => .error err
    | .ok (.u64 n) =>
      match vecNew n.toNat with
      | .error e => .error e
      | .ok v =>
        let (m', a) := memAllocData m
          ((BitVec.ofNat 32 0) :: (BitVec.ofNat 32 n.toNat) :: v.val)
        .ok (((x, .stdVecOwned v 0 n.toNat) :: ρ, m', (x, a, a) :: π),
          .fellThrough)
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
  | .vgrowSet x ie ve, ρ, m, π =>
    match memEvalExpr ie ρ m π, memEvalExpr ve ρ m π,
        envLookup ρ x, layoutLookup π x with
    | .ok (.u64 i), .ok (.i32 xv), some (.stdVecOwned b len cap),
        some (a, t) =>
      match vecSet b i.toNat xv, memStore m a t (i.toNat + 2) xv with
      | .ok b', .ok m' =>
        match envUpdate ρ x (.stdVecOwned b' len cap) with
        | none => .error .Uninit
        | some ρ' => .ok ((ρ', m', π), .fellThrough)
      | .error e, _ => .error e
      | _, .error e => .error e
    | .ok _, .ok _, _, _ => .error .AssertFail
    | .error e, _, _, _ => .error e
    | _, .error e, _, _ => .error e
  | .arrSet x ie ve, ρ, m, π =>
    match memEvalExpr ie ρ m π, memEvalExpr ve ρ m π,
        envLookup ρ x, layoutLookup π x with
    | .ok (.u64 i), .ok (.u32 xv), some (.arr32 l),
        some (a, t) =>
      match l[i.toNat]? with
      | none => .error .OOB
      | some _ =>
        match memStore m a t i.toNat xv with
        | .error e => .error e
        | .ok m' =>
          match envUpdate ρ x (.arr32 (l.set i.toNat xv)) with
          | none => .error .Uninit
          | some ρ' => .ok ((ρ', m', π), .fellThrough)
    | .ok _, .ok _, _, _ => .error .AssertFail
    | .error e, _, _, _ => .error e
    | _, .error e, _, _ => .error e
  | .vgrowFree x, ρ, m, π =>
    match envLookup ρ x, layoutLookup π x with
    | some (.stdVecOwned b len cap), some (a, t) =>
      match vecFree b, memFree m a t with
      | .ok b', .ok m' =>
        match envUpdate ρ x (.stdVecOwned b' len cap) with
        | none => .error .Uninit
        | some ρ' => .ok ((ρ', m', π), .fellThrough)
      | .error e, _ => .error e
      | _, .error e => .error e
    | _, _ => .error .AssertFail
  | .fail, _, _, _ => .error .AssertFail
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
  | .callProg _ _ _, _, _, _ => .error .AssertFail
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
      | .viewVal l =>
        -- The reified bytes plus the 32-bit length word up front
        -- (one byte per word cell, zero-extended — the word-level
        -- abstraction, matching `memEvalExpr_viewAt_hit`; N7a).
        let (m'', a) := memAllocData m'
          ((BitVec.ofNat 32 l.length) ::
            l.map (fun x => BitVec.ofNat 32 x.toNat))
        some (((p.name, .viewVal l) :: ρ), m'', (p.name, a, a) :: π)
      | .stdVecVal l =>
        -- The reified elements plus the 32-bit length word up front
        -- (the heap-triple snapshot model: word 0 is the length,
        -- words `1+i` are the elements; N4d-iv-a, reads only).
        let (m'', a) := memAllocData m' ((BitVec.ofNat 32 l.length) :: l)
        some (((p.name, .stdVecVal l) :: ρ), m'', (p.name, a, a) :: π)
      | .stdVecOwned b len cap =>
        -- The owned triple pins the two-word header plus the storage
        -- words (word 0 is the length, word 1 the capacity, words
        -- `2+i` the elements; N4d-iv-b1, growth leaves). Lifting a
        -- freed buffer keeps it dead, like `vecVal`.
        let (m'', a) := memAllocData m'
          ((BitVec.ofNat 32 len) :: (BitVec.ofNat 32 cap) :: b.val)
        some (((p.name, .stdVecOwned b len cap) :: ρ),
          ⟨m''.next, (a, ⟨a, !b.freed, (BitVec.ofNat 32 len) ::
            (BitVec.ofNat 32 cap) :: b.val⟩) :: m''.blocks, m''.blocks64⟩,
          (p.name, a, a) :: π)
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

mutual
/-- Memory program statement evaluation. Mirrors `evalProgStmt`
    step for step: `callRet dst f xs` looks up the actuals, dispatches
    to the call-free callee via `memEvalFuncFuel` at the same fuel, and
    extends the environment with the result (caller `Mem`/`Layout`
    threaded through untouched — the callee runs on its own fresh
    entry blocks, so no aliasing is introduced); `callProg dst f xs`
    is the depth-n twin (N4d-iv-b2): the callee runs under
    `memEvalProgFunc` at one less fuel; `seq` recurses;
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
  | .callProg dst f xs, ρ, m, π =>
    match lookupArgs ρ xs with
    | none => .error .Uninit
    | some vs =>
      match findFunc prog f with
      | none => .error .AssertFail
      | some callee =>
        match fuel with
        | 0 => .error .AssertFail
        | fuel + 1 =>
          match memEvalProgFunc prog fuel callee vs with
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
  termination_by s _ _ _ => (fuel, 0, s)

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
  termination_by (fuel, 1, f.body)
end

/-- `cleanup` scopes sequence on the memory program layer too (the M2b
    `acc_two` entry shape; mirrors `evalProgStmt_cleanup`). -/
theorem memEvalProgStmt_cleanup (prog : Prog) (fuel : Nat) (body : CStmt)
    (ρ : Env) (m : Mem) (π : Layout) :
    memEvalProgStmt prog fuel (.cleanup body) ρ m π =
      memEvalProgStmt prog fuel body ρ m π := by
  simp only [memEvalProgStmt]

/-- Prog-level `let_` runs the call-free memory evaluator (the fallback
    arm of `memEvalProgStmt`; cf. `memEvalProgStmt_return` delegating to
    `memEvalStmtFuel_return`, and `evalProgStmt_let_fb` on the value
    side). -/
theorem memEvalProgStmt_let_fb (prog : Prog) (fuel : Nat) (x : String)
    (ty : CType) (e : CExpr) (ρ : Env) (m : Mem) (π : Layout) :
    memEvalProgStmt prog fuel (.let_ x ty e) ρ m π =
      memEvalStmtFuel fuel (.let_ x ty e) ρ m π := by
  simp only [memEvalProgStmt]

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

/-- `callProg` with resolved actuals + callee runs the callee under the
    program evaluator (one fuel less; N4d-iv-b2 composer calls). -/
theorem memEvalProgStmt_callProg_ok (prog : Prog) (fuel : Nat)
    (dst f : String) (xs : List String) (ρ : Env) (m : Mem) (π : Layout)
    (vs : List Value) (callee : Func) (ret : Value)
    (hargs : lookupArgs ρ xs = some vs)
    (hfind : findFunc prog f = some callee)
    (hcall : memEvalProgFunc prog fuel callee vs = .ok ret) :
    memEvalProgStmt prog (fuel + 1) (.callProg dst f xs) ρ m π =
      .ok ((envExtend ρ dst ret, m, π), .fellThrough) := by
  simp [memEvalProgStmt, hargs, hfind, hcall]

/-- `callProg` propagates callee errors. -/
theorem memEvalProgStmt_callProg_err (prog : Prog) (fuel : Nat)
    (dst f : String) (xs : List String) (ρ : Env) (m : Mem) (π : Layout)
    (vs : List Value) (callee : Func) (e : Panic)
    (hargs : lookupArgs ρ xs = some vs)
    (hfind : findFunc prog f = some callee)
    (hcall : memEvalProgFunc prog fuel callee vs = .error e) :
    memEvalProgStmt prog (fuel + 1) (.callProg dst f xs) ρ m π = .error e := by
  simp [memEvalProgStmt, hargs, hfind, hcall]

/-- `callProg` to an unknown callee is rejected, never silently modeled. -/
theorem memEvalProgStmt_callProg_unknown (prog : Prog) (fuel : Nat)
    (dst f : String) (xs : List String) (ρ : Env) (m : Mem) (π : Layout)
    (vs : List Value)
    (hargs : lookupArgs ρ xs = some vs)
    (hfind : findFunc prog f = none) :
    memEvalProgStmt prog fuel (.callProg dst f xs) ρ m π =
      .error .AssertFail := by
  simp [memEvalProgStmt, hargs, hfind]

/-- `callProg` with unbound actuals is `Uninit`. -/
theorem memEvalProgStmt_callProg_unbound (prog : Prog) (fuel : Nat)
    (dst f : String) (xs : List String) (ρ : Env) (m : Mem) (π : Layout)
    (hargs : lookupArgs ρ xs = none) :
    memEvalProgStmt prog fuel (.callProg dst f xs) ρ m π =
      .error .Uninit := by
  simp [memEvalProgStmt, hargs]

/-- `callProg` at zero fuel is loud (the call-depth budget is spent). -/
theorem memEvalProgStmt_callProg_nofuel (prog : Prog) (fuel : Nat)
    (dst f : String) (xs : List String) (ρ : Env) (m : Mem) (π : Layout)
    (vs : List Value) (callee : Func)
    (hargs : lookupArgs ρ xs = some vs)
    (hfind : findFunc prog f = some callee) :
    memEvalProgStmt prog 0 (.callProg dst f xs) ρ m π =
      .error .AssertFail := by
  simp [memEvalProgStmt, hargs, hfind]

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

