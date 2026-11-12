/-
Pillar-1 tree-kit goal: iterative inorder flatten (`bst_inorder`):
`int bst_inorder(Node *root, int *out, int cap)` writes the
inorder keys into the caller buffer, returning the count (or `-1`
on stack/out overflow). The traversal uses an explicit 64-entry
local word stack (no recursion): push the left spine, pop, emit,
swing right. Stack slots hold `linkWord`-encoded addresses as
`u32` words (`linkOf`/`ptrOf`); the stack block itself is a fresh
`arrNew` zeroed block with a layout pin. Faults are loud as usual.
-/
import Circe.Emit.BstSearch
import Circe.Emit.BstInsert

/-- C name (unmangled: pure-C corpus entry). -/
def bstInorderName : String :=
  "bst_inorder"

/-- Fixed stack depth (the `st[64]` local array). -/
def bstInorderStackSize : Nat := 64

/-- Push leg: store the cursor encoding, bump the top,
    swing the cursor left. -/
def bstInorderPushSeq : CStmt :=
  (.seq (.arrSet "st" (.var "top") (.linkOf (.var "cur")))
  (.seq (.assign "top"
            (.uadd (.var "top") (.lit (.u64 (BitVec.ofNat 64 1)))))
        (.assign "cur" (.pgetNext (.var "cur")))))

/-- Loud overflow leg (shared by both capacity checks). -/
def bstInorderBail : CStmt :=
  (.return_ (.lit (.i32 (BitVec.ofNat 32 (2 ^ 32 - 1)))))

/-- Inner loop: push the left spine (`while (cur != NULL)`).
    The room check branches around the push: no room returns
    `-1` (the loud stack-overflow leg). -/
def bstInorderSpineBody : CStmt :=
  (.if_ (.ult (.var "top") (.lit (.u64 (BitVec.ofNat 64 64))))
    bstInorderPushSeq
    bstInorderBail)

/-- Inner `while (cur != nullptr)` (left-spine push). -/
def bstInorderSpineLoop : CStmt :=
  (.while_ (.une (.var "cur") (.lit .nullptr)) bstInorderSpineBody)

/-- Outer-loop step past the spine: pop the top, emit, swing
    right. The capacity check branches around the emit: no room
    returns `-1` (the loud out-overflow leg). -/
def bstInorderStepBody : CStmt :=
  (.seq (.assign "top"
          (.usub (.var "top") (.lit (.u64 (BitVec.ofNat 64 1)))))
  (.seq (.assign "cur" (.ptrOf (.idxu "st" (.var "top"))))
  (.seq (.if_ (.ult (.var "n") (.var "capU"))
    (.seq (.mstore "out" (.var "n") (.pgetVal (.var "cur")))
    (.seq (.assign "n"
              (.uadd (.var "n") (.lit (.u64 (BitVec.ofNat 64 1)))))
          (.assign "cur" (.pgetRight (.var "cur")))))
    (.return_ (.lit (.i32 (BitVec.ofNat 32 (2 ^ 32 - 1))))))
    .skip)))

/-- Outer `while (cur != NULL || top > 0)`: spine, step, repeat. -/
def bstInorderOuterLoop : CStmt :=
  (.while_
    (.tif (.une (.var "cur") (.lit .nullptr))
      (.lit (.b true))
      (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "top")))
    (.seq bstInorderSpineLoop bstInorderStepBody))

/-- Whole function: fresh stack, counters, cursor, capacity word,
    outer loop, count return. -/
def bstInorderBody : CStmt :=
  (.seq (.let_ "st" (.array (.u 32) bstInorderStackSize)
          (.arrNew (.lit (.u64 (BitVec.ofNat 64 bstInorderStackSize)))))
  (.seq (.let_ "top" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
  (.seq (.let_ "cur" nodeTy (.var "root"))
  (.seq (.let_ "n" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
  (.seq (.let_ "capU" (.u 64) (.u64ofI32 (.var "cap")))
        (.seq bstInorderOuterLoop
              (.return_ (.i32ofU64 (.var "n")))))))))

/-- The inorder entry: `Node*` root + `i32*` out + `i32` cap in,
    `i32` count (or `-1`) out. The `out` slot is documentary
    (pointer params share the nominal pointer slot; `bindArgs`
    checks arity only) — the pin comes from the caller buffer
    hypothesis in `bstInorderFunc_correct`. -/
def bstInorderFunc : Func :=
  ⟨bstInorderName,
   [{ name := "root", ty := nodeTy, role := .owned },
    { name := "out", ty := nodeTy, role := .owned },
    { name := "cap", ty := (.i 32), role := .owned }],
   (.i 32),
   bstInorderBody⟩

/-- Inorder environment: root/out/cap slots, then the stack,
    counters, cursor, and capacity-word slots. -/
def mkBstInorderEnv (root out : Option Addr) (cap : BitVec 32)
    (st : List (BitVec 32)) (top : BitVec 64) (cur : Option Addr)
    (n capU : BitVec 64) : Env :=
  [("capU", .u64 capU), ("n", .u64 n), ("cur", .ptrVal cur),
    ("top", .u64 top), ("st", .arr32 st),
    ("root", .ptrVal root), ("out", .ptrVal out),
    ("cap", .i32 cap)]

/-- Spine result: `bail` (stack overflow, whole function returns
    `-1`) or `cont` with the descended cursor, grown stack, and
    threaded memory. -/
inductive SpineRes
  | bail (m : Mem)
  | cont (cur : Option Addr) (stk : List Addr) (m : Mem)

/-- Inner-loop forward: push the left spine, or bail on overflow.
    `stA`/`stT` pin the stack block; `stk` is the pure stack
    (bottom-first, `length = top`; entries are always live
    addresses, never null). -/
def bstInorderSpine (F : Nat) (m : Mem) (cur : Option Addr)
    (stk : List Addr) (stA : Addr) (stT : Nat) :
    Result SpineRes :=
  match cur with
  | none => .ok (.cont none stk m)
  | some a =>
    match F with
    | 0 => .error .AssertFail
    | F + 1 =>
      if stk.length >= bstInorderStackSize then .ok (.bail m)
      else
        match memFind m a with
        | none => .error .AssertFail
        | some b =>
          match memLoad m a b.tag 1 with
          | .error e => .error e
          | .ok l =>
            match memStore m stA stT stk.length
                (linkWord (some a)) with
            | .error e => .error e
            | .ok m' =>
              bstInorderSpine F m' (addrOfWord l)
                (stk ++ [a]) stA stT

/-- Outer-loop forward: spine, then pop-emit-right or finish.
    `n` counts emitted keys; `capU` is the widened capacity.
Returns `some` count on finish, `none` on overflow, with the
    threaded memory. -/
def bstInorderOuter (F : Nat) (m : Mem) (cur : Option Addr)
    (stk : List Addr) (stA : Addr) (stT : Nat)
    (outA : Addr) (outT : Nat) (cap : BitVec 32) (n : BitVec 64) :
    Result (Option (BitVec 64) × Mem) :=
  match F with
  | 0 => .error .AssertFail
  | F + 1 =>
    match bstInorderSpine F m cur stk stA stT with
    | .error e => .error e
    | .ok (.bail m') => .ok (none, m')
    | .ok (.cont cur' stk' m') =>
      match cur', stk' with
      | none, [] => .ok (some n, m')
      | _, _ =>
        match stk'.getLast? with
        | none => .error .AssertFail
        | some a =>
          match memFind m' a with
          | none => .error .AssertFail
          | some b =>
            match memLoad m' a b.tag 0, memLoad m' a b.tag 2 with
            | .ok k, .ok r =>
              if n.toNat < (cap.signExtend 64).toNat then
                match memStore m' outA outT n.toNat k with
                | .error e => .error e
                | .ok m'' =>
                  bstInorderOuter F m'' (addrOfWord r)
                    stk'.dropLast stA stT outA outT cap (n + 1)
              else .ok (none, m')
            | .error e, _ => .error e
            | _, .error e => .error e

/-- Entry forward: fresh-stack allocation is handled by the
    caller (`arrNew` pins `stA`/`stT` with zeros); the chase runs
    from the empty stack. -/
def bstInorderFwd (F : Nat) (m : Mem) (root : Option Addr)
    (stA : Addr) (stT : Nat) (outA : Addr) (outT : Nat)
    (cap : BitVec 32) : Result (Option (BitVec 64) × Mem) :=
  bstInorderOuter F m root [] stA stT outA outT cap 0

/-- Stack frames as inorder frames (top-first, for `drain`):
    each pushed address contributes its key and pending right
    subtree. Snoc on the address stack conses on the frames. -/
inductive FramesOf : Mem → List Addr → List InorderFrame → Prop
  | nil (m : Mem) : FramesOf m [] []
  | cons {m : Mem} {stk : List Addr} {fr : List InorderFrame}
      {a : Addr} {tp : Nat} {k : BitVec 32}
      {lp rp : Option Addr} {r : BTree} :
      nodeAt3 m a tp k lp rp → TreeSeg m rp r →
      FramesOf m stk fr →
      FramesOf m (stk ++ [a]) ((k, r) :: fr)

/-- The stack block mirrors the pure stack on its live prefix
    (`top = stk.length`); popped slots keep stale links, so only
    the `take`-prefix is pinned, plus the fixed block length. -/
def StackMirror (m : Mem) (stA : Addr) (stT : Nat)
    (stk : List Addr) : Prop :=
  ∃ data, memFind m stA = some ⟨stT, true, data⟩ ∧
    data.length = bstInorderStackSize ∧
    data.take stk.length = stk.map fun a => linkWord (some a)

/-- The out buffer starts with the emitted prefix. -/
def OutPrefix (m : Mem) (outA : Addr) (outT : Nat)
    (emitted : List (BitVec 32)) : Prop :=
  ∃ data, memFind m outA = some ⟨outT, true, data⟩ ∧
    data.take emitted.length = emitted

/-- Flatten length is the node count (fuel-measure bridge). -/
theorem BTree.length_flatten_eq_bsize (t : BTree) :
    t.flatten.length = t.bsize := by
  induction t with
  | leaf => rfl
  | node k l r ihl ihr =>
    simp [BTree.flatten, BTree.bsize, ihl, ihr, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm]

/-- `nodeAt3` survives a store elsewhere (block identity is
    untouched off the written address). -/
theorem nodeAt3_store_other {m : Mem} {a t : Nat} {k : BitVec 32}
    {l r : Option Addr}
    (h : nodeAt3 m a t k l r)
    {a' tg i : Nat} {x : BitVec 32} {m' : Mem}
    (hstore : memStore m a' tg i x = .ok m')
    (hne : a ≠ a') : nodeAt3 m' a t k l r := by
  unfold nodeAt3 cellsAt at h ⊢
  rw [memFind_memStore_other _ _ _ _ _ _ _ hstore hne]
  exact h

/-- Membership transfers across a store elsewhere (induction
    with per-step exclusion lifted from the outer segment). -/
theorem TreeSegMem_store_other {m : Mem} {s : Option Addr} {a : Addr}
    (h : TreeSegMem (m := m) s a)
    {a' tg i : Nat} {x : BitVec 32} {m' : Mem}
    (hstore : memStore m a' tg i x = .ok m')
    (hne : ∀ b, TreeSegMem (m := m) s b → b ≠ a') :
    TreeSegMem (m := m') s a := by
  induction h with
  | here hnode =>
    have hne' : _ ≠ a' := hne _ (.here hnode)
    exact .here (nodeAt3_store_other hnode hstore hne')
  | left hnode _ ih =>
    have hne' : _ ≠ a' := hne _ (.here hnode)
    exact .left (nodeAt3_store_other hnode hstore hne')
      (ih (fun b hb => hne b (.left hnode hb)))
  | right hnode _ ih =>
    have hne' : _ ≠ a' := hne _ (.here hnode)
    exact .right (nodeAt3_store_other hnode hstore hne')
      (ih (fun b hb => hne b (.right hnode hb)))

/-- A derivation concluding written-address membership is
    impossible when the written block cannot be a tree node
    (the `hlen3` pin: 64-word stack, non-3-word out buffer).
    Structural induction — the `.here` base case is exactly
    the pinned impossibility. -/
theorem TreeSegMem_store_fresh {m' : Mem} {s : Option Addr}
    {a' : Addr}
    (hlen3 : ∀ t k l r, ¬ nodeAt3 m' a' t k l r)
    {b : Addr} (h : TreeSegMem (m := m') s b) (heq : b = a') :
    False := by
  induction h with
  | here hnode =>
    subst heq
    exact hlen3 _ _ _ _ hnode
  | left hnode _ ih =>
    exact ih heq
  | right hnode _ ih =>
    exact ih heq

/-- Membership lifts along reachability (transitivity of the
    footprint). -/
theorem TreeSegMem_trans {m : Mem} {s : Option Addr} {c b : Addr}
    (D1 : TreeSegMem (m := m) s c)
    (D2 : TreeSegMem (m := m) (some c) b) :
    TreeSegMem (m := m) s b := by
  revert D2
  induction D1 with
  | here _ =>
    intro D2
    exact D2
  | left hnode _ ih =>
    intro D2
    exact .left hnode (ih D2)
  | right hnode _ ih =>
    intro D2
    exact .right hnode (ih D2)

/-- Descending a live left link stays in the footprint. -/
theorem TreeSegMem_child_left {m : Mem} {s : Option Addr} {a : Addr}
    (D : TreeSegMem (m := m) s a)
    {t : Nat} {k : BitVec 32} {lp rp : Option Addr}
    (hnode : nodeAt3 m a t k lp rp)
    {tl : BTree} (hl : TreeSeg m lp tl)
    {c : Addr} (heq : lp = some c) :
    TreeSegMem (m := m) s c := by
  have h1 : TreeSegMem (m := m) (some a) c := by
    cases hl with
    | nil =>
      cases heq
    | cons hnode_c _ _ =>
      have hcc := Option.some_inj.mp heq
      subst hcc
      exact .left hnode (.here hnode_c)
  exact TreeSegMem_trans D h1

/-- Descending a live right link stays in the footprint. -/
theorem TreeSegMem_child_right {m : Mem} {s : Option Addr} {a : Addr}
    (D : TreeSegMem (m := m) s a)
    {t : Nat} {k : BitVec 32} {lp rp : Option Addr}
    (hnode : nodeAt3 m a t k lp rp)
    {tr : BTree} (hr : TreeSeg m rp tr)
    {c : Addr} (heq : rp = some c) :
    TreeSegMem (m := m) s c := by
  have h1 : TreeSegMem (m := m) (some a) c := by
    cases hr with
    | nil =>
      cases heq
    | cons hnode_c _ _ =>
      have hcc := Option.some_inj.mp heq
      subst hcc
      exact .right hnode (.here hnode_c)
  exact TreeSegMem_trans D h1

/-- Nothing lives under the empty segment. -/
theorem TreeSegMem_none_empty {m : Mem} {b : Addr}
    (h : TreeSegMem (m := m) none b) : False := by
  cases h

structure InorderInv (m : Mem) (root : Option Addr) (t : BTree)
    (stA : Addr) (stT : Nat) (outA : Addr) (outT : Nat)
    (cap : BitVec 32) (n : BitVec 64)
    (emitted : List (BitVec 32)) (cur : Option Addr)
    (focus : BTree) (stk : List Addr)
    (frames : List InorderFrame) : Prop where
  hseg : TreeSeg m root t
  hfocus : TreeSeg m cur focus
  hframes : FramesOf m stk frames
  hstack : StackMirror m stA stT stk
  hstacklen : stk.length ≤ bstInorderStackSize
  hout : OutPrefix m outA outT emitted
  hn : emitted.length = n.toNat
  heq : emitted ++ drain (pushSpine focus frames) = t.flatten
  hmemCur : ∀ c, cur = some c → TreeSegMem (m := m) root c
  hmemFr : ∀ a, a ∈ stk → TreeSegMem (m := m) root a
  hneSt : ∀ b, TreeSegMem (m := m) root b → b ≠ stA
  hneOut : ∀ b, TreeSegMem (m := m) root b → b ≠ outA
  hstNeOut : stA ≠ outA
  houtLen : ∀ data, memFind m outA = some ⟨outT, true, data⟩ →
    data.length ≠ 3
  houtCap : ∀ data, memFind m outA = some ⟨outT, true, data⟩ →
    (cap.signExtend 64).toNat ≤ data.length

/-- Setting the next slot extends the live prefix by exactly
    the new word (the `arrSet` mirror step; popped slots may hold
    stale links, so only the prefix is pinned). -/
private theorem take_set_succ (l : List α) (n : Nat) (x : α)
    (h : n < l.length) :
    (l.set n x).take (n + 1) = l.take n ++ [x] := by
  induction l generalizing n with
  | nil => simp at h
  | cons y ys ih =>
    cases n with
    | zero => rfl
    | succ n =>
      have hn : n < ys.length := by
        simp only [List.length_cons] at h
        omega
      simp only [List.set_cons_succ, List.take_succ_cons]
      rw [ih n hn, List.cons_append]

/-- Frames survive a store elsewhere: node facts transfer
    pointwise, right subtrees via the stored exclusion lifted
    from root membership. -/
theorem FramesOf_store_other {m : Mem} {root : Option Addr}
    {stk : List Addr} {fr : List InorderFrame}
    (hfr : FramesOf m stk fr)
    {a' tg i : Nat} {x : BitVec 32} {m' : Mem}
    (hstore : memStore m a' tg i x = .ok m')
    (hne : ∀ b, TreeSegMem (m := m) root b → b ≠ a')
    (hmem : ∀ a, a ∈ stk → TreeSegMem (m := m) root a) :
    FramesOf m' stk fr := by
  induction hfr with
  | nil =>
    exact .nil _
  | cons hnode hr _ ih =>
    have hmemA : TreeSegMem (m := m) root _ :=
      hmem _ (List.mem_append_right _ (List.mem_singleton_self _))
    have hneA : _ ≠ a' := hne _ hmemA
    have hnode' := nodeAt3_store_other hnode hstore hneA
    refine .cons hnode' (TreeSeg.store_other hr hstore ?_) (ih
      (fun a ha => hmem a (List.mem_append_left _ ha)))
    intro b hb
    apply hne
    cases hr with
    | nil =>
      cases hb
    | cons h1 h2 h3 =>
      exact TreeSegMem_trans
        (TreeSegMem_child_right hmemA hnode
          (TreeSeg.cons h1 h2 h3) rfl) hb

/-- Frames determine the stack length (snoc-cons lockstep). -/
theorem FramesOf.length_eq {m : Mem} {stk : List Addr}
    {fr : List InorderFrame} (h : FramesOf m stk fr) :
    stk.length = fr.length := by
  induction h with
  | nil => rfl
  | cons _ _ _ ih => simp [ih]

/-- Snoc-append injectivity (suffix-first split). -/
theorem snoc_inj_append {s₁ s₂ : List α} {a b : α}
    (h : s₁ ++ [a] = s₂ ++ [b]) : s₁ = s₂ ∧ a = b := by
  have hlen : s₁.length = s₂.length := by
    have hL := congrArg List.length h
    simp only [List.length_append, List.length_singleton] at hL
    omega
  obtain ⟨h1, h2⟩ := List.append_inj h hlen
  exact ⟨h1, by simpa using h2⟩

/-- Inverting a snoc-push frame: the top address owns the head
    frame (key plus pending right subtree). -/
theorem FramesOf.snoc_inv {m : Mem} {stk : List Addr}
    {fr : List InorderFrame} (h : FramesOf m stk fr) :
    ∀ {stk₀ : List Addr} {a : Addr}, stk = stk₀ ++ [a] →
    ∃ tp k lp rp r fr', nodeAt3 m a tp k lp rp ∧ TreeSeg m rp r ∧
      fr = (k, r) :: fr' ∧ FramesOf m stk₀ fr' := by
  induction h with
  | nil =>
    intro stk₀ a heq
    exact absurd heq.symm (by simp)
  | cons hnode hr htail _ih =>
    intro stk₀ a heq
    obtain ⟨rfl, rfl⟩ := snoc_inj_append heq
    exact ⟨_, _, _, _, _, _, hnode, hr, rfl, htail⟩

/-- Membership pins a live block (for freshness side-goals). -/
theorem TreeSegMem_find_some {m : Mem} {s : Option Addr} {a : Addr}
    (h : TreeSegMem (m := m) s a) :
    (memFind m a).isSome = true := by
  induction h with
  | here hnode =>
    unfold nodeAt3 cellsAt at hnode
    rw [hnode]
    rfl
  | left _ _ ih => exact ih
  | right _ _ ih => exact ih

/-- Membership bottoms out at a live node (for block-shape
    freshness arguments). -/
theorem TreeSegMem_nodeAt3 {m : Mem} {s : Option Addr} {a : Addr}
    (h : TreeSegMem (m := m) s a) :
    ∃ t k l r, nodeAt3 m a t k l r := by
  induction h with
  | here hnode => exact ⟨_, _, _, _, hnode⟩
  | left _ _ ih => exact ih
  | right _ _ ih => exact ih

/-- The head of a segment is a member (for root-membership
    after a fresh allocation). -/
theorem TreeSegMem_head {m : Mem} {s : Option Addr} {t : BTree}
    (h : TreeSeg m s t) : ∀ {c}, s = some c →
    TreeSegMem (m := m) s c := by
  intro c hs
  subst hs
  cases h with
  | cons hnode _ _ => exact .here hnode

/-- A segment survives a fresh allocation elsewhere. -/
theorem TreeSeg.alloc_other {m : Mem} {s : Option Addr} {t : BTree}
    (h : TreeSeg m s t) (d : List (BitVec 32))
    (hne : ∀ b, TreeSegMem (m := m) s b → b ≠ m.next) :
    TreeSeg (memAllocData m d).1 s t := by
  induction h with
  | nil => exact .nil
  | cons hnode _ _ ihl ihr =>
    have hneA : _ ≠ m.next := hne _ (.here hnode)
    exact .cons (nodeAt3_alloc_other hnode d hneA)
      (ihl (fun b hb => hne b (.left hnode hb)))
      (ihr (fun b hb => hne b (.right hnode hb)))

/-- Inner-loop agreement: the spine loop pushes the left spine
    (returning the descended cursor, grown stack, threaded
    memory and environment) or bails with `-1` on a full stack.
    Fuel `focus.bsize + 1` covers the pushes plus the exit. -/
theorem bstInorderSpine_ok (F : Nat) :
    ∀ (m : Mem) (π : Layout)
      (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
      (root : Option Addr) (t : BTree)
      (cur : Option Addr) (focus : BTree)
      (stk : List Addr) (frames : List InorderFrame)
      (stA : Addr) (stT : Nat) (stList : List (BitVec 32))
      (top n capU : BitVec 64) (cap : BitVec 32)
      (out : Option Addr) (outA : Addr) (outT : Nat)
      (emitted : List (BitVec 32)),
    InorderInv m root t stA stT outA outT cap n emitted cur focus
      stk frames →
    stList.take stk.length =
      (stk.map fun a => linkWord (some a)) →
    stList.length = bstInorderStackSize →
    top.toNat = stk.length →
    stT = stA →
    layoutLookup π "st" = some (stA, stT) →
    focus.bsize + 1 ≤ F →
    (∃ cur' focus' stk' frames' m' stList' top' ρ' pushed,
      memEvalStmtFuel F bstInorderSpineLoop
        (mkBstInorderEnv root out cap stList top cur n capU) m π =
        .ok ((ρ', m', π), .fellThrough)
      ∧ bstInorderSpine F m cur stk stA stT =
        .ok (.cont cur' stk' m')
      ∧ ρ' = mkBstInorderEnv root out cap stList' top' cur' n capU
      ∧ stList'.take stk'.length =
        (stk'.map fun a => linkWord (some a))
      ∧ stList'.length = bstInorderStackSize
      ∧ top'.toNat = stk'.length
      ∧ cur' = none
      ∧ stk' = stk ++ pushed
      ∧ (cur ≠ none → stk' ≠ [])
      ∧ (∀ x, (memFind m' x).isSome = true → x + 1 < 2 ^ 32)
      ∧ InorderInv m' root t stA stT outA outT cap n emitted
        cur' focus' stk' frames')
    ∨ (∃ ρ' m',
      memEvalStmtFuel F bstInorderSpineLoop
        (mkBstInorderEnv root out cap stList top cur n capU) m π =
        .ok ((ρ', m', π), .returned (.i32 (BitVec.ofNat 32 (2 ^ 32 - 1))))
      ∧ bstInorderSpine F m cur stk stA stT = .ok (.bail m')) := by
  induction F with
  | zero =>
    intro m π hex root t cur focus stk frames stA stT stList top n
      capU cap out outA outT emitted hInv hstList hstLen htop hstT
      hlay hlen
    cases focus with
    | leaf =>
      simp only [BTree.bsize] at hlen
      omega
    | node k l r =>
      simp only [BTree.bsize] at hlen
      omega
  | succ F ih =>
    intro m π hex root t cur focus stk frames stA stT stList top n
      capU cap out outA outT emitted hInv hstList hstLen htop hstT
      hlay hlen
    cases hcur : cur with
    | none =>
      subst hcur
      have hfocus0 : focus = .leaf := by
        cases hInv.hfocus with
        | nil => rfl
      subst hfocus0
      have hcurE : memEvalExpr (.var "cur")
          (mkBstInorderEnv root out cap stList top none n capU)
          m π = .ok (.ptrVal none) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _
          (by simp [envLookup, mkBstInorderEnv])
      have hnullE : memEvalExpr (.lit .nullptr)
          (mkBstInorderEnv root out cap stList top none n capU)
          m π = .ok (.ptrVal none) := by
        simp [memEvalExpr, litVal]
      have hgF : memEvalExpr
          (.une (.var "cur") (.lit .nullptr))
          (mkBstInorderEnv root out cap stList top none n capU)
          m π = .ok (.b false) := by
        have hg := memEvalExpr_une_ptrVal _ _ _ _ _ none none
          hcurE hnullE
        have hbe : ((none : Option Addr) != none) = false := by
          simp
        rw [hbe] at hg
        exact hg
      have hw := memEvalStmtFuel_while_false (F + 1)
        (.une (.var "cur") (.lit .nullptr)) bstInorderSpineBody
        _ _ _ hgF
      have hF : bstInorderSpine (F + 1) m none stk stA stT =
          .ok (.cont none stk m) := by
        simp [bstInorderSpine]
      exact Or.inl ⟨_, _, _, _, _, _, _, _, [], hw, hF, rfl, hstList,
        hstLen, htop, rfl, by simp, fun h => (h rfl).elim, hex,
        hInv⟩
    | some a =>
      subst hcur
      have hfc := hInv.hfocus
      have hcons : ∃ tp k lp rp l r,
          nodeAt3 m a tp k lp rp ∧ TreeSeg m lp l ∧ TreeSeg m rp r ∧
          focus = BTree.node k l r := by
        cases hfc with
        | cons hnode hl hr =>
          exact ⟨_, _, _, _, _, _, hnode, hl, hr, rfl⟩
      obtain ⟨tp, k, lp, rp, l, r, hnode, hl, hr, hfocus_eq⟩ := hcons
      subst hfocus_eq
      have hsz : bstInorderStackSize = 64 := rfl
      have hstklen := hInv.hstacklen
      have hlenA : (stk ++ [a]).length = stk.length + 1 := by
        simp [List.length_append]
      have hfind : memFind m a =
          some ⟨tp, true, [k, linkWord lp, linkWord rp]⟩ := hnode
      have hcurE : memEvalExpr (.var "cur")
          (mkBstInorderEnv root out cap stList top (some a) n capU)
          m π = .ok (.ptrVal (some a)) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _
          (by simp [envLookup, mkBstInorderEnv])
      have hnullE : memEvalExpr (.lit .nullptr)
          (mkBstInorderEnv root out cap stList top (some a) n capU)
          m π = .ok (.ptrVal none) := by
        simp [memEvalExpr, litVal]
      have hgT : memEvalExpr
          (.une (.var "cur") (.lit .nullptr))
          (mkBstInorderEnv root out cap stList top (some a) n capU)
          m π = .ok (.b true) := by
        have hg := memEvalExpr_une_ptrVal _ _ _ _ _ (some a) none
          hcurE hnullE
        have hbe : ((some a : Option Addr) != none) = true := by
          simp
        rw [hbe] at hg
        exact hg
      have hwLoop : memEvalStmtFuel (F + 1) bstInorderSpineLoop
          (mkBstInorderEnv root out cap stList top (some a) n capU)
          m π =
          match memEvalStmtFuel F bstInorderSpineBody
            (mkBstInorderEnv root out cap stList top (some a) n capU)
            m π with
          | .error e => .error e
          | .ok ((ρ', m', π'), .returned v) =>
            .ok ((ρ', m', π'), .returned v)
          | .ok ((ρ', m', π'), .broke) =>
            .ok ((ρ', m', π'), .fellThrough)
          | .ok ((ρ', m', π'), .continued) =>
            memEvalStmtFuel F bstInorderSpineLoop ρ' m' π'
          | .ok ((ρ', m', π'), .fellThrough) =>
            memEvalStmtFuel F bstInorderSpineLoop ρ' m' π' :=
        memEvalStmtFuel_while_true F _ _ _ _ _ hgT
      have htopE : memEvalExpr (.var "top")
          (mkBstInorderEnv root out cap stList top (some a) n capU)
          m π = .ok (.u64 top) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _
          (by simp [envLookup, mkBstInorderEnv])
      have h64E : memEvalExpr
          (.lit (.u64 (BitVec.ofNat 64 64)))
          (mkBstInorderEnv root out cap stList top (some a) n capU)
          m π = .ok (.u64 (BitVec.ofNat 64 64)) := by
        simp [memEvalExpr, litVal]
      have htopV : evalExpr (.var "top")
          (mkBstInorderEnv root out cap stList top (some a) n capU) =
          .ok (.u64 top) :=
        evalExpr_var_hit _ _ _
          (by simp [envLookup, mkBstInorderEnv])
      have h64V : evalExpr
          (.lit (.u64 (BitVec.ofNat 64 64)))
          (mkBstInorderEnv root out cap stList top (some a) n capU) =
          .ok (.u64 (BitVec.ofNat 64 64)) := by
        simp [evalExpr, litVal]
      have hultM := memEvalExpr_ult_agree _ _ _ _ _ htopE h64E
      have hultV := evalExpr_ult_u64 _ _ _ _ _ htopV h64V
      by_cases hroom : stk.length < bstInorderStackSize
      · -- Room: push, descend left, apply IH.
        have hultTb : (top.ult (BitVec.ofNat 64 64)) = true := by
          have hlt : top.toNat < (BitVec.ofNat 64 64).toNat := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)]
            omega
          rw [BitVec.ult_eq_decide]
          exact decide_eq_true hlt
        have hultT : memEvalExpr
            (.ult (.var "top")
              (.lit (.u64 (BitVec.ofNat 64 64))))
            (mkBstInorderEnv root out cap stList top (some a) n capU)
            m π = .ok (.b true) := by
          rw [hultM, hultV, hultTb]
        have hifT : memEvalStmtFuel F bstInorderSpineBody
            (mkBstInorderEnv root out cap stList top (some a) n capU)
            m π =
            memEvalStmtFuel F bstInorderPushSeq
            (mkBstInorderEnv root out cap stList top (some a) n capU)
            m π :=
          memEvalStmtFuel_if_true F _ bstInorderPushSeq
            bstInorderBail _ _ _ hultT
        have hcurL : envLookup
            (mkBstInorderEnv root out cap stList top (some a) n capU)
            "cur" = some (.ptrVal (some a)) := by
          simp [envLookup, mkBstInorderEnv]
        have hlinkM : memEvalExpr (.linkOf (.var "cur"))
            (mkBstInorderEnv root out cap stList top (some a) n capU)
            m π = .ok (.u32 (linkWord (some a))) := by
          have h1 : memEvalExpr (.var "cur")
              (mkBstInorderEnv root out cap stList top (some a) n capU)
              m π = evalExpr (.var "cur")
              (mkBstInorderEnv root out cap stList top (some a) n capU) :=
            memEvalExpr_var _ _ _ _
          have h2 : evalExpr (.var "cur")
              (mkBstInorderEnv root out cap stList top (some a) n capU) =
              .ok (.ptrVal (some a)) :=
            evalExpr_var_hit _ _ _ hcurL
          have h3 : evalExpr (.linkOf (.var "cur"))
              (mkBstInorderEnv root out cap stList top (some a) n capU) =
              .ok (.u32 (linkWord (some a))) :=
            evalExpr_linkOf_hit _ _ _ h2
          have h4 := memEvalExpr_linkOf_agree _ _ _ _ h1
          rw [h4]
          exact h3
        have htopL : envLookup
            (mkBstInorderEnv root out cap stList top (some a) n capU)
            "top" = some (.u64 top) := by
          simp [envLookup, mkBstInorderEnv]
        have htopM : memEvalExpr (.var "top")
            (mkBstInorderEnv root out cap stList top (some a) n capU)
            m π = .ok (.u64 top) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _ htopL
        have harr : envLookup
            (mkBstInorderEnv root out cap stList top (some a) n capU)
            "st" = some (.arr32 stList) := by
          simp [envLookup, mkBstInorderEnv]
        have hle64 : stk.length ≤ 64 := by
          rw [hsz] at hstklen
          exact hstklen
        have hlt : top.toNat < stList.length := by
          omega
        have hw' := List.getElem?_eq_getElem hlt
        obtain ⟨stData, hfindSt, hlenSt, htakeSt⟩ := hInv.hstack
        have hltR : top.toNat < stData.length := by
          omega
        have hwR' := List.getElem?_eq_getElem hltR
        obtain ⟨m', hstore, hfindSt'⟩ := arrSet_lockstep m stA stT
          stData top.toNat (linkWord (some a)) _ _ hfindSt rfl
          rfl rfl hwR'
        have hu : envUpdate
            (mkBstInorderEnv root out cap stList top (some a) n capU)
            "st" (.arr32 (stList.set top.toNat (linkWord (some a)))) =
            some (mkBstInorderEnv root out cap
              (stList.set top.toNat (linkWord (some a))) top (some a)
              n capU) := by
          simp [envUpdate, mkBstInorderEnv]
        have harrSet : memEvalStmtFuel F
            (.arrSet "st" (.var "top") (.linkOf (.var "cur")))
            (mkBstInorderEnv root out cap stList top (some a) n capU)
            m π =
            .ok (((mkBstInorderEnv root out cap
              (stList.set top.toNat (linkWord (some a))) top
              (some a) n capU, m', π)), .fellThrough) := by
          cases F <;>
            simp [memEvalStmtFuel, memEvalStmtZero, memEvalStmtWith,
              htopM, hlinkM, harr, hlay, hw', hstore, hu]
        have htopV1 : evalExpr (.var "top")
            (mkBstInorderEnv root out cap
              (stList.set top.toNat (linkWord (some a))) top (some a)
              n capU) = .ok (.u64 top) :=
          evalExpr_var_hit _ _ _
            (by simp [envLookup, mkBstInorderEnv])
        have h1V : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
            (mkBstInorderEnv root out cap
              (stList.set top.toNat (linkWord (some a))) top (some a)
              n capU) = .ok (.u64 (BitVec.ofNat 64 1)) := by
          simp [evalExpr, litVal]
        have huaddV : evalExpr
            (.uadd (.var "top") (.lit (.u64 (BitVec.ofNat 64 1))))
            (mkBstInorderEnv root out cap
              (stList.set top.toNat (linkWord (some a))) top (some a)
              n capU) =
            .ok (.u64 (top + BitVec.ofNat 64 1)) :=
          evalExpr_u64_uadd _ _ _ _ _ htopV1 h1V
        have htop1 : (top + BitVec.ofNat 64 1).toNat = top.toNat + 1 := by
          have h1 : (BitVec.ofNat 64 1).toNat = 1 := by decide
          rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
        have htopM1 : memEvalExpr (.var "top")
            (mkBstInorderEnv root out cap
              (stList.set top.toNat (linkWord (some a))) top (some a)
              n capU) m' π = evalExpr (.var "top")
            (mkBstInorderEnv root out cap
              (stList.set top.toNat (linkWord (some a))) top (some a)
              n capU) := memEvalExpr_var _ _ _ _
        have h1M : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
            (mkBstInorderEnv root out cap
              (stList.set top.toNat (linkWord (some a))) top (some a)
              n capU) m' π = evalExpr
            (.lit (.u64 (BitVec.ofNat 64 1)))
            (mkBstInorderEnv root out cap
              (stList.set top.toNat (linkWord (some a))) top (some a)
              n capU) := by
          simp [memEvalExpr, evalExpr, litVal]
        have huaddM : memEvalExpr
            (.uadd (.var "top") (.lit (.u64 (BitVec.ofNat 64 1))))
            (mkBstInorderEnv root out cap
              (stList.set top.toNat (linkWord (some a))) top (some a)
              n capU) m' π =
            .ok (.u64 (top + BitVec.ofNat 64 1)) := by
          rw [memEvalExpr_uadd_agree _ _ _ _ _ htopM1 h1M]
          exact huaddV
        have hu2 : envUpdate
            (mkBstInorderEnv root out cap
              (stList.set top.toNat (linkWord (some a))) top (some a)
              n capU)
            "top" (.u64 (top + BitVec.ofNat 64 1)) =
            some (mkBstInorderEnv root out cap
              (stList.set top.toNat (linkWord (some a)))
              (top + BitVec.ofNat 64 1) (some a) n capU) := by
          simp [envUpdate, mkBstInorderEnv]
        have htopAssign : memEvalStmtFuel F
            (.assign "top"
              (.uadd (.var "top") (.lit (.u64 (BitVec.ofNat 64 1)))))
            (mkBstInorderEnv root out cap
              (stList.set top.toNat (linkWord (some a))) top (some a)
              n capU) m' π =
            .ok (((mkBstInorderEnv root out cap
              (stList.set top.toNat (linkWord (some a)))
              (top + BitVec.ofNat 64 1) (some a) n capU, m', π)),
              .fellThrough) :=
          memEvalStmtFuel_assign_mem F _ _ _ _ _ _ _ huaddM hu2
        have hmemFrA : TreeSegMem (m := m) root a :=
          hInv.hmemCur a rfl
        have hneA : a ≠ stA := hInv.hneSt a hmemFrA
        have hfind1 : memFind m' a =
            some ⟨tp, true, [k, linkWord lp, linkWord rp]⟩ := by
          have hfm : memFind m' a = memFind m a :=
            memFind_memStore_other _ _ _ _ _ _ _ hstore hneA
          rw [hfm]
          exact hfind
        have hmem1 : memLoad m' a tp 1 = .ok (linkWord lp) := by
          have hmeq : memLoad m' a tp 1 = memLoad m a tp 1 := by
            simp only [memLoad, hfind, hfind1]
          rw [hmeq]
          exact nodeLoadLeft hnode
        have hdec : addrOfWord (linkWord lp) = lp := by
          cases hlp : lp with
          | none =>
            subst hlp
            exact addrOfWord_linkWord_none
          | some c =>
            subst hlp
            have halloc : ∀ c', (some c) = some c' →
                (memFind m c').isSome = true := by
              intro c' hc'
              rw [hc'] at hl
              exact TreeSeg_head_alloc hl
            exact nodeAt3_link_roundtrip hex halloc
        have hcurV2 : evalExpr (.var "cur")
            (mkBstInorderEnv root out cap
              (stList.set top.toNat (linkWord (some a)))
              (top + BitVec.ofNat 64 1) (some a) n capU) =
            .ok (.ptrVal (some a)) :=
          evalExpr_var_hit _ _ _
            (by simp [envLookup, mkBstInorderEnv])
        have hcurM2 : memEvalExpr (.var "cur")
            (mkBstInorderEnv root out cap
              (stList.set top.toNat (linkWord (some a)))
              (top + BitVec.ofNat 64 1) (some a) n capU) m' π =
            evalExpr (.var "cur")
              (mkBstInorderEnv root out cap
                (stList.set top.toNat (linkWord (some a)))
                (top + BitVec.ofNat 64 1) (some a) n capU) :=
          memEvalExpr_var _ _ _ _
        have hcurV : memEvalExpr (.pgetNext (.var "cur"))
            (mkBstInorderEnv root out cap
              (stList.set top.toNat (linkWord (some a)))
              (top + BitVec.ofNat 64 1) (some a) n capU) m' π =
            .ok (.ptrVal (addrOfWord (linkWord lp))) :=
          memEvalExpr_pgetNext_hit _ _ _ _ _ _ _ hcurM2 hfind1 hmem1
        have hu3 : envUpdate
            (mkBstInorderEnv root out cap
              (stList.set top.toNat (linkWord (some a)))
              (top + BitVec.ofNat 64 1) (some a) n capU)
            "cur" (.ptrVal (addrOfWord (linkWord lp))) =
            some (mkBstInorderEnv root out cap
              (stList.set top.toNat (linkWord (some a)))
              (top + BitVec.ofNat 64 1) (addrOfWord (linkWord lp))
              n capU) := by
          simp [envUpdate, mkBstInorderEnv]
        have hcurAssign : memEvalStmtFuel F
            (.assign "cur" (.pgetNext (.var "cur")))
            (mkBstInorderEnv root out cap
              (stList.set top.toNat (linkWord (some a)))
              (top + BitVec.ofNat 64 1) (some a) n capU) m' π =
            .ok (((mkBstInorderEnv root out cap
              (stList.set top.toNat (linkWord (some a)))
              (top + BitVec.ofNat 64 1) (addrOfWord (linkWord lp))
              n capU, m', π)), .fellThrough) :=
          memEvalStmtFuel_assign_mem F _ _ _ _ _ _ _ hcurV hu3
        have hseqInner : memEvalStmtFuel F
            (.seq (.assign "top"
              (.uadd (.var "top") (.lit (.u64 (BitVec.ofNat 64 1)))))
              (.assign "cur" (.pgetNext (.var "cur"))))
            (mkBstInorderEnv root out cap
              (stList.set top.toNat (linkWord (some a))) top (some a)
              n capU) m' π =
            .ok (((mkBstInorderEnv root out cap
              (stList.set top.toNat (linkWord (some a)))
              (top + BitVec.ofNat 64 1) (addrOfWord (linkWord lp))
              n capU, m', π)), .fellThrough) :=
          memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _
            htopAssign hcurAssign
        have hbody : memEvalStmtFuel F bstInorderPushSeq
            (mkBstInorderEnv root out cap stList top (some a) n capU)
            m π =
            .ok (((mkBstInorderEnv root out cap
              (stList.set top.toNat (linkWord (some a)))
              (top + BitVec.ofNat 64 1) (addrOfWord (linkWord lp))
              n capU, m', π)), .fellThrough) :=
          memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _
            harrSet hseqInner
        have hroomN : ¬ stk.length ≥ bstInorderStackSize := by
          omega
        have hFwd : bstInorderSpine (F + 1) m (some a) stk stA stT =
            bstInorderSpine F m' (addrOfWord (linkWord lp))
              (stk ++ [a]) stA stT := by
          simp only [bstInorderSpine]
          rw [ite_eq_right hroomN, hfind]
          simp only []
          rw [nodeLoadLeft hnode, ← htop, hstore]
        have hex' : ∀ x, (memFind m' x).isSome = true → x + 1 < 2 ^ 32 := by
          intro x hx
          by_cases heq : x = stA
          · have hfindStX : memFind m x =
                some ⟨stT, true, stData⟩ := by
              rw [heq]
              exact hfindSt
            have hmem : (memFind m x).isSome = true := by
              rw [hfindStX]
              rfl
            rw [heq] at hmem ⊢
            exact hex _ hmem
          · have hfindEq : memFind m' x = memFind m x :=
              memFind_memStore_other _ _ _ _ _ _ _ hstore heq
            rw [hfindEq] at hx
            exact hex x hx
        have hlen' : l.bsize + 1 ≤ F := by
          have hbs : (BTree.node k l r).bsize = l.bsize + r.bsize + 1 :=
            rfl
          omega
        have htop' : (top + BitVec.ofNat 64 1).toNat =
            (stk ++ [a]).length := by
          rw [htop1, htop]
          simp [List.length_append]
        have hset : (stList.set top.toNat (linkWord (some a))).take
            ((stk ++ [a]).length) =
            ((stk ++ [a]).map fun a => linkWord (some a)) := by
          rw [hlenA, htop, take_set_succ _ _ _ (by omega), hstList]
          simp [List.map_append]
        have hlenGhost' : (stList.set top.toNat
            (linkWord (some a))).length = bstInorderStackSize := by
          simp [List.length_set, hstLen]
        have hstack' : StackMirror m' stA stT (stk ++ [a]) := by
          refine ⟨_, hfindSt', ?_, ?_⟩
          · rw [List.length_set]
            exact hlenSt
          · rw [hlenA, htop, take_set_succ _ _ _ (by omega), htakeSt]
            simp [List.map_append]
        have hstacklen' : (stk ++ [a]).length ≤ bstInorderStackSize := by
          rw [hlenA, hsz]
          omega
        have hneLp : ∀ b, TreeSegMem (m := m) lp b → b ≠ stA := by
          intro b hb
          cases lp with
          | none =>
            exact (TreeSegMem_none_empty hb).elim
          | some c =>
            have hmemLp : TreeSegMem (m := m) root c :=
              TreeSegMem_child_left hmemFrA hnode hl rfl
            exact hInv.hneSt b (TreeSegMem_trans hmemLp hb)
        have hneRp : ∀ b, TreeSegMem (m := m) rp b → b ≠ stA := by
          intro b hb
          cases rp with
          | none =>
            exact (TreeSegMem_none_empty hb).elim
          | some c =>
            have hmemRp : TreeSegMem (m := m) root c :=
              TreeSegMem_child_right hmemFrA hnode hr rfl
            exact hInv.hneSt b (TreeSegMem_trans hmemRp hb)
        have hlen3st : ∀ t k l r, ¬ nodeAt3 m' stA t k l r := by
          intro t k' l' r' h3
          unfold nodeAt3 cellsAt at h3
          obtain ⟨stData', hfindSt'', hlenSt'', _⟩ := hstack'
          rw [hfindSt''] at h3
          have hX : (⟨stT, true, stData'⟩ : Block) =
              ⟨t, true, [k', linkWord l', linkWord r']⟩ :=
            Option.some.inj h3
          have hlenEq : stData' = [k', linkWord l', linkWord r'] :=
            (Block.mk.inj hX).2.2
          rw [hlenEq, hsz] at hlenSt''
          simp at hlenSt''
        have hneSt' : ∀ b, TreeSegMem (m := m') root b → b ≠ stA := by
          intro b hb heq
          exact TreeSegMem_store_fresh hlen3st hb heq
        obtain ⟨outData, hfindOut, htake⟩ := hInv.hout
        have hfindOut' : memFind m' outA = some ⟨outT, true, outData⟩ := by
          rw [memFind_memStore_other _ _ _ _ _ _ _ hstore
            hInv.hstNeOut.symm]
          exact hfindOut
        have hlen3out : ∀ t k l r, ¬ nodeAt3 m' outA t k l r := by
          intro t k' l' r' h3
          unfold nodeAt3 cellsAt at h3
          rw [hfindOut'] at h3
          have hX : (⟨outT, true, outData⟩ : Block) =
              ⟨t, true, [k', linkWord l', linkWord r']⟩ :=
            Option.some.inj h3
          have hlenEq : outData = [k', linkWord l', linkWord r'] :=
            (Block.mk.inj hX).2.2
          have hL : outData.length = 3 := by
            simp [hlenEq]
          exact (hInv.houtLen outData hfindOut) hL
        have houtNe' : ∀ b, TreeSegMem (m := m') root b → b ≠ outA := by
          intro b hb heq
          exact TreeSegMem_store_fresh hlen3out hb heq
        have houtLen' : ∀ data, memFind m' outA = some ⟨outT, true, data⟩ →
            data.length ≠ 3 := by
          intro data hd
          rw [memFind_memStore_other _ _ _ _ _ _ _ hstore
            hInv.hstNeOut.symm] at hd
          exact hInv.houtLen data hd
        have houtCap' : ∀ data, memFind m' outA = some ⟨outT, true, data⟩ →
            (cap.signExtend 64).toNat ≤ data.length := by
          intro data hd
          rw [memFind_memStore_other _ _ _ _ _ _ _ hstore
            hInv.hstNeOut.symm] at hd
          exact hInv.houtCap data hd
        have hout' : OutPrefix m' outA outT emitted :=
          ⟨outData, hfindOut', htake⟩
        have hmemCur' : ∀ c, addrOfWord (linkWord lp) = some c →
            TreeSegMem (m := m') root c := by
          intro c hc
          rw [hdec] at hc
          have hmemLp : TreeSegMem (m := m) root c :=
            TreeSegMem_child_left hmemFrA hnode hl hc
          exact TreeSegMem_store_other hmemLp hstore hInv.hneSt
        have hmemFr' : ∀ x, x ∈ stk ++ [a] → TreeSegMem (m := m') root x := by
          intro x hx
          cases List.mem_append.mp hx with
          | inl hmem =>
            exact TreeSegMem_store_other (hInv.hmemFr x hmem) hstore
              hInv.hneSt
          | inr hmem =>
            have hxa : x = a := by simpa using hmem
            subst hxa
            exact TreeSegMem_store_other hmemFrA hstore hInv.hneSt
        have hseg' : TreeSeg m' root t :=
          TreeSeg.store_other hInv.hseg hstore hInv.hneSt
        have hfocusLp : TreeSeg m' lp l :=
          TreeSeg.store_other hl hstore hneLp
        have hfocus' : TreeSeg m' (addrOfWord (linkWord lp)) l := by
          rw [hdec]
          exact hfocusLp
        have hnode' : nodeAt3 m' a tp k lp rp :=
          nodeAt3_store_other hnode hstore hneA
        have hr' : TreeSeg m' rp r :=
          TreeSeg.store_other hr hstore hneRp
        have hframes' : FramesOf m' (stk ++ [a]) ((k, r) :: frames) :=
          FramesOf.cons hnode' hr'
            (FramesOf_store_other hInv.hframes hstore hInv.hneSt
              hInv.hmemFr)
        have heq' : emitted ++
            drain (pushSpine l ((k, r) :: frames)) = t.flatten :=
          hInv.heq
        have hInv' : InorderInv m' root t stA stT outA outT cap n
            emitted (addrOfWord (linkWord lp)) l (stk ++ [a])
            ((k, r) :: frames) :=
          ⟨hseg', hfocus', hframes', hstack', hstacklen', hout',
            hInv.hn, heq', hmemCur', hmemFr', hneSt', houtNe',
            hInv.hstNeOut, houtLen', houtCap'⟩
        have hIH := ih m' π hex' root t (addrOfWord (linkWord lp)) l
          (stk ++ [a]) ((k, r) :: frames) stA stT
          (stList.set top.toNat (linkWord (some a)))
          (top + BitVec.ofNat 64 1) n capU cap out outA outT emitted
          hInv' hset hlenGhost' htop' hstT hlay hlen'
        cases hIH with
        | inl h =>
          obtain ⟨cur'', focus'', stk'', frames'', m'', stList'', top'',
            ρ'', pushed₂, hbody'', hFwd'', hρ'', hstList'', hlen'',
            htop'', hnone'', hpush'', _, hex'', hInv''⟩ := h
          rw [List.append_assoc] at hpush''
          rw [hwLoop, hifT, hbody, hFwd]
          simp only []
          exact Or.inl ⟨_, _, _, _, _, _, _, _, [a] ++ pushed₂,
            hbody'', hFwd'', hρ'', hstList'', hlen'', htop'',
            hnone'', hpush'', fun _ => by rw [hpush'']; simp,
            hex'', hInv''⟩
        | inr h =>
          obtain ⟨ρ'', m'', hbodyE, hFwdE⟩ := h
          rw [hwLoop, hifT, hbody, hFwd]
          simp only []
          exact Or.inr ⟨_, _, hbodyE, hFwdE⟩
      · -- No room: loud `-1`, fwd bails.
        have hge : stk.length ≥ bstInorderStackSize := by omega
        have hultF : (top.ult (BitVec.ofNat 64 64)) = false := by
          have hle : (BitVec.ofNat 64 64).toNat ≤ top.toNat := by
            rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by decide)]
            omega
          rw [BitVec.ult_eq_decide]
          exact decide_eq_false (Nat.not_lt.mpr hle)
        have hultF' : memEvalExpr
            (.ult (.var "top")
              (.lit (.u64 (BitVec.ofNat 64 64))))
            (mkBstInorderEnv root out cap stList top (some a) n capU)
            m π = .ok (.b false) := by
          rw [hultM, hultV, hultF]
        have hifF : memEvalStmtFuel F bstInorderSpineBody
            (mkBstInorderEnv root out cap stList top (some a) n capU)
            m π =
            memEvalStmtFuel F bstInorderBail
            (mkBstInorderEnv root out cap stList top (some a) n capU)
            m π :=
          memEvalStmtFuel_if_false F _ bstInorderPushSeq
            bstInorderBail _ _ _ hultF'
        have hagreeR : memEvalExpr
            (.lit (.i32 (BitVec.ofNat 32 (2 ^ 32 - 1))))
            (mkBstInorderEnv root out cap stList top (some a) n capU)
            m π = evalExpr
            (.lit (.i32 (BitVec.ofNat 32 (2 ^ 32 - 1))))
            (mkBstInorderEnv root out cap stList top (some a) n capU) := by
          simp [memEvalExpr, evalExpr, litVal]
        have hevRV : evalExpr
            (.lit (.i32 (BitVec.ofNat 32 (2 ^ 32 - 1))))
            (mkBstInorderEnv root out cap stList top (some a) n capU) =
            .ok (.i32 (BitVec.ofNat 32 (2 ^ 32 - 1))) := by
          simp [evalExpr, litVal]
        have hret : memEvalStmtFuel F bstInorderBail
            (mkBstInorderEnv root out cap stList top (some a) n capU)
            m π =
            .ok (((mkBstInorderEnv root out cap stList top (some a)
              n capU, m, π)),
              .returned (.i32 (BitVec.ofNat 32 (2 ^ 32 - 1)))) :=
          memEvalStmtFuel_return F _ _ _ _ _ hagreeR hevRV
        have hFwdB : bstInorderSpine (F + 1) m (some a) stk stA stT =
            .ok (.bail m) := by
          simp only [bstInorderSpine]
          rw [ite_eq_left hge]
        rw [hwLoop, hifF, hret]
        simp only []
        exact Or.inr ⟨_, _, rfl, hFwdB⟩

/-- `seq` propagates a first-statement `returned` (any fuel;
    the loud-leg threading for early `-1` legs). -/
theorem memEvalStmtFuel_seq_returned_first (f : Nat) (a b : CStmt)
    (ρ : Env) (m : Mem) (π : Layout)
    (ρ' : Env) (m' : Mem) (π' : Layout) (v : Value)
    (ha : memEvalStmtFuel f a ρ m π = .ok ((ρ', m', π'), .returned v)) :
    memEvalStmtFuel f (.seq a b) ρ m π =
      .ok ((ρ', m', π'), .returned v) := by
  cases f with
  | zero =>
    simp only [memEvalStmtFuel, memEvalStmtZero] at ha ⊢
    simp only [memEvalStmtWith, ha]
  | succ n =>
    simp only [memEvalStmtFuel] at ha ⊢
    simp only [memEvalStmtWith, ha]

/-- Outer-loop agreement: each iteration pushes a spine then
    pops-emits-or-finishes. Fuel covers the remaining keys plus
    the exit. On finish the out buffer holds the full flatten;
    on overflow the function bails with `-1`. -/
theorem bstInorderOuter_ok (F : Nat) :
    ∀ (m : Mem) (π : Layout)
      (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
      (root : Option Addr) (t : BTree)
      (cur : Option Addr) (focus : BTree)
      (stk : List Addr) (frames : List InorderFrame)
      (stA : Addr) (stT : Nat) (stList : List (BitVec 32))
      (top n capU : BitVec 64) (cap : BitVec 32)
      (out : Option Addr) (outA : Addr) (outT : Nat)
      (emitted : List (BitVec 32)),
    InorderInv m root t stA stT outA outT cap n emitted cur focus
      stk frames →
    stList.take stk.length =
      (stk.map fun a => linkWord (some a)) →
    stList.length = bstInorderStackSize →
    top.toNat = stk.length →
    stT = stA →
    layoutLookup π "st" = some (stA, stT) →
    (t.flatten.length - emitted.length) + 2 ≤ F →
    capU.toNat = (cap.signExtend 64).toNat →
    layoutLookup π "out" = some (outA, outT) →
    t.flatten.length < 2 ^ 64 →
    (∃ (nCnt : BitVec 64) (m' : Mem) (ρ' : Env)
        (stList' : List (BitVec 32)) (top' : BitVec 64)
        (emitted' : List (BitVec 32)),
      memEvalStmtFuel F bstInorderOuterLoop
        (mkBstInorderEnv root out cap stList top cur n capU) m π =
        .ok ((ρ', m', π), .fellThrough)
      ∧ bstInorderOuter F m cur stk stA stT outA outT cap n =
        .ok (some nCnt, m')
      ∧ ρ' = mkBstInorderEnv root out cap stList' top' none nCnt
        capU
      ∧ InorderInv m' root t stA stT outA outT cap nCnt emitted'
        none .leaf [] []
      ∧ emitted' = t.flatten)
    ∨ (∃ ρ' m',
      memEvalStmtFuel F bstInorderOuterLoop
        (mkBstInorderEnv root out cap stList top cur n capU) m π =
        .ok ((ρ', m', π), .returned
          (.i32 (BitVec.ofNat 32 (2 ^ 32 - 1))))
      ∧ bstInorderOuter F m cur stk stA stT outA outT cap n =
        .ok (none, m')) := by
  induction F with
  | zero =>
    intro m π hex root t cur focus stk frames stA stT stList top n
      capU cap out outA outT emitted hInv hstList hstLen htop hstT
      hlay hbound hcapU hlayOut h64
    omega
  | succ F ih =>
    intro m π hex root t cur focus stk frames stA stT stList top n
      capU cap out outA outT emitted hInv hstList hstLen htop hstT
      hlay hbound hcapU hlayOut h64
    have hcurE : memEvalExpr (.var "cur")
        (mkBstInorderEnv root out cap stList top cur n capU)
        m π = .ok (.ptrVal cur) := by
      rw [memEvalExpr_var]
      exact evalExpr_var_hit _ _ _
        (by simp [envLookup, mkBstInorderEnv])
    have hnullE : memEvalExpr (.lit .nullptr)
        (mkBstInorderEnv root out cap stList top cur n capU)
        m π = .ok (.ptrVal none) := by
      simp [memEvalExpr, litVal]
    have huneE : memEvalExpr (.une (.var "cur") (.lit .nullptr))
        (mkBstInorderEnv root out cap stList top cur n capU)
        m π = .ok (.b (cur != none)) :=
      memEvalExpr_une_ptrVal _ _ _ _ _ _ _ hcurE hnullE
    by_cases hfin : cur = none ∧ stk = []
    · -- FINISH: cursor drained and stack empty; the out buffer
      -- already holds the full flatten.
      obtain ⟨hcurN, hstkN⟩ := hfin
      subst hcurN
      subst hstkN
      have hbeF : ((none : Option Addr) != none) = false := by decide
      rw [hbeF] at huneE
      have htop0 : top.toNat = 0 := by simpa using htop
      have h0M : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
          (mkBstInorderEnv root out cap stList top none n capU)
          m π = .ok (.u64 (BitVec.ofNat 64 0)) := by
        simp [memEvalExpr, litVal]
      have htopEM : memEvalExpr (.var "top")
          (mkBstInorderEnv root out cap stList top none n capU)
          m π = .ok (.u64 top) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _
          (by simp [envLookup, mkBstInorderEnv])
      have hultM := memEvalExpr_ult_agree _ _ _ _ _ h0M htopEM
      have h0V : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
          (mkBstInorderEnv root out cap stList top none n capU) =
          .ok (.u64 (BitVec.ofNat 64 0)) := by
        simp [evalExpr, litVal]
      have htopV : evalExpr (.var "top")
          (mkBstInorderEnv root out cap stList top none n capU) =
          .ok (.u64 top) :=
        evalExpr_var_hit _ _ _
          (by simp [envLookup, mkBstInorderEnv])
      have hultV := evalExpr_ult_u64 _ _ _ _ _ h0V htopV
      have h0nat : (BitVec.ofNat 64 0).toNat = 0 := by decide
      have hultb : ((BitVec.ofNat 64 0).ult top) = false := by
        rw [BitVec.ult_eq_decide, h0nat, htop0]
        exact decide_eq_false (by omega)
      have hcurV : evalExpr (.var "cur")
          (mkBstInorderEnv root out cap stList top none n capU) =
          .ok (.ptrVal none) :=
        evalExpr_var_hit _ _ _
          (by simp [envLookup, mkBstInorderEnv])
      have hnullV : evalExpr (.lit .nullptr)
          (mkBstInorderEnv root out cap stList top none n capU) =
          .ok (.ptrVal none) := by
        simp [evalExpr, litVal]
      have hevalC := evalExpr_une_ptrVal _ _ _ _ _ hcurV hnullV
      rw [hbeF] at hevalC
      have hc : memEvalExpr (.une (.var "cur") (.lit .nullptr))
          (mkBstInorderEnv root out cap stList top none n capU)
          m π =
          evalExpr (.une (.var "cur") (.lit .nullptr))
            (mkBstInorderEnv root out cap stList top none n capU) := by
        rw [huneE, hevalC]
      have hgM := memEvalExpr_tif_false
        (.une (.var "cur") (.lit .nullptr)) (.lit (.b true))
        (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "top"))
        _ _ _ hc hevalC hultM
      have hgV := evalExpr_tif_false
        (.une (.var "cur") (.lit .nullptr)) (.lit (.b true))
        (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "top"))
        _ hevalC
      have hguard : memEvalExpr
          (.tif (.une (.var "cur") (.lit .nullptr))
            (.lit (.b true))
            (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "top")))
          (mkBstInorderEnv root out cap stList top none n capU)
          m π = .ok (.b false) := by
        rw [hgM, hgV, hultV, hultb]
      have hw := memEvalStmtFuel_while_false (F + 1)
        (.tif (.une (.var "cur") (.lit .nullptr))
          (.lit (.b true))
          (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "top")))
        (.seq bstInorderSpineLoop bstInorderStepBody) _ _ _
        hguard
      have hFwd : bstInorderOuter (F + 1) m none [] stA stT outA
          outT cap n = .ok (some n, m) := by
        simp [bstInorderOuter, bstInorderSpine]
      have hfocusLeaf : focus = .leaf := by
        cases hInv.hfocus with
        | nil => rfl
      have hfrLen : frames.length = 0 := by
        have hFL := FramesOf.length_eq hInv.hframes
        simpa using hFL.symm
      have hfrNil : frames = [] :=
        List.eq_nil_of_length_eq_zero hfrLen
      have heqF : emitted = t.flatten := by
        simpa [hfocusLeaf, hfrNil, pushSpine, drain, drainF,
          stackCost] using hInv.heq
      have heqField : emitted ++ drain (pushSpine .leaf []) =
          t.flatten := by
        simp only [pushSpine, drain, drainF, stackCost,
          List.append_nil]
        exact heqF
      exact Or.inl ⟨n, m, _, stList, top, emitted,
        hw, hFwd, rfl,
        ⟨hInv.hseg, TreeSeg.nil, FramesOf.nil _, hInv.hstack,
          hInv.hstacklen, hInv.hout, hInv.hn, heqField,
          (fun c h => by cases h),
          (fun a h => absurd h (by simp)),
          hInv.hneSt, hInv.hneOut, hInv.hstNeOut, hInv.houtLen,
          hInv.houtCap⟩,
        heqF⟩
    · -- Guard-true leg: push a spine, then pop-emit-or-bail.
      have hne_or : cur ≠ none ∨ stk ≠ [] := by
        by_cases hcn : cur = none
        · right
          intro hstk
          exact hfin ⟨hcn, hstk⟩
        · left
          exact hcn
      have hgT : memEvalExpr
          (.tif (.une (.var "cur") (.lit .nullptr))
            (.lit (.b true))
            (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "top")))
          (mkBstInorderEnv root out cap stList top cur n capU)
          m π = .ok (.b true) := by
        by_cases hcn : cur = none
        · -- Cursor drained: the stack is live, so `0 < top` fires.
          have hstkNe : stk ≠ [] := fun h => hfin ⟨hcn, h⟩
          have hbeC : (cur != none) = false := by
            rw [hcn]
            simp
          have huneE' : memEvalExpr (.une (.var "cur") (.lit .nullptr))
              (mkBstInorderEnv root out cap stList top cur n capU)
              m π = .ok (.b false) := by
            rw [huneE, hbeC]
          have h0M : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
              (mkBstInorderEnv root out cap stList top cur n capU)
              m π = .ok (.u64 (BitVec.ofNat 64 0)) := by
            simp [memEvalExpr, litVal]
          have htopEM : memEvalExpr (.var "top")
              (mkBstInorderEnv root out cap stList top cur n capU)
              m π = .ok (.u64 top) := by
            rw [memEvalExpr_var]
            exact evalExpr_var_hit _ _ _
              (by simp [envLookup, mkBstInorderEnv])
          have hultM := memEvalExpr_ult_agree _ _ _ _ _ h0M htopEM
          have h0V : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
              (mkBstInorderEnv root out cap stList top cur n capU) =
              .ok (.u64 (BitVec.ofNat 64 0)) := by
            simp [evalExpr, litVal]
          have htopV : evalExpr (.var "top")
              (mkBstInorderEnv root out cap stList top cur n capU) =
              .ok (.u64 top) :=
            evalExpr_var_hit _ _ _
              (by simp [envLookup, mkBstInorderEnv])
          have hultV := evalExpr_ult_u64 _ _ _ _ _ h0V htopV
          have h0nat : (BitVec.ofNat 64 0).toNat = 0 := by decide
          have hlenPos : 0 < stk.length :=
            Nat.pos_of_ne_zero
              (fun h => hstkNe (List.eq_nil_of_length_eq_zero h))
          have htopPos : 0 < top.toNat := by
            rw [htop]
            exact hlenPos
          have hultT : ((BitVec.ofNat 64 0).ult top) = true := by
            rw [BitVec.ult_eq_decide, h0nat]
            exact decide_eq_true htopPos
          have hcurV : evalExpr (.var "cur")
              (mkBstInorderEnv root out cap stList top cur n capU) =
              .ok (.ptrVal cur) :=
            evalExpr_var_hit _ _ _
              (by simp [envLookup, mkBstInorderEnv])
          have hnullV : evalExpr (.lit .nullptr)
              (mkBstInorderEnv root out cap stList top cur n capU) =
              .ok (.ptrVal none) := by
            simp [evalExpr, litVal]
          have hevalC := evalExpr_une_ptrVal _ _ _ _ _ hcurV hnullV
          rw [hbeC] at hevalC
          have hc : memEvalExpr (.une (.var "cur") (.lit .nullptr))
              (mkBstInorderEnv root out cap stList top cur n capU)
              m π =
              evalExpr (.une (.var "cur") (.lit .nullptr))
                (mkBstInorderEnv root out cap stList top cur n capU) := by
            rw [huneE', hevalC]
          have hgM := memEvalExpr_tif_false
            (.une (.var "cur") (.lit .nullptr)) (.lit (.b true))
            (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "top"))
            _ _ _ hc hevalC hultM
          have hgV := evalExpr_tif_false
            (.une (.var "cur") (.lit .nullptr)) (.lit (.b true))
            (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "top"))
            _ hevalC
          rw [hgM, hgV, hultV, hultT]
        · -- Cursor live: the `une` leg fires directly.
          have hbeC : (cur != none) = true := by
            cases cur with
            | none => exact absurd rfl hcn
            | some a => rfl
          have huneE' : memEvalExpr (.une (.var "cur") (.lit .nullptr))
              (mkBstInorderEnv root out cap stList top cur n capU)
              m π = .ok (.b true) := by
            rw [huneE, hbeC]
          have hcurV : evalExpr (.var "cur")
              (mkBstInorderEnv root out cap stList top cur n capU) =
              .ok (.ptrVal cur) :=
            evalExpr_var_hit _ _ _
              (by simp [envLookup, mkBstInorderEnv])
          have hnullV : evalExpr (.lit .nullptr)
              (mkBstInorderEnv root out cap stList top cur n capU) =
              .ok (.ptrVal none) := by
            simp [evalExpr, litVal]
          have hevalC := evalExpr_une_ptrVal _ _ _ _ _ hcurV hnullV
          rw [hbeC] at hevalC
          have hc : memEvalExpr (.une (.var "cur") (.lit .nullptr))
              (mkBstInorderEnv root out cap stList top cur n capU)
              m π =
              evalExpr (.une (.var "cur") (.lit .nullptr))
                (mkBstInorderEnv root out cap stList top cur n capU) := by
            rw [huneE', hevalC]
          have ht : memEvalExpr (.lit (.b true))
              (mkBstInorderEnv root out cap stList top cur n capU)
              m π =
              evalExpr (.lit (.b true))
                (mkBstInorderEnv root out cap stList top cur n capU) :=
            memEvalExpr_lit _ _ _ _
          have hgM := memEvalExpr_tif_true
            (.une (.var "cur") (.lit .nullptr)) (.lit (.b true))
            (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "top"))
            _ _ _ hc hevalC ht
          have hgV := evalExpr_tif_true
            (.une (.var "cur") (.lit .nullptr)) (.lit (.b true))
            (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.var "top"))
            _ hevalC
          have hlitT : evalExpr (.lit (.b true))
              (mkBstInorderEnv root out cap stList top cur n capU) =
              .ok (.b true) := by
            simp [evalExpr, litVal]
          rw [hgM, hgV, hlitT]
      have hwLoop : memEvalStmtFuel (F + 1) bstInorderOuterLoop
          (mkBstInorderEnv root out cap stList top cur n capU) m π =
          match memEvalStmtFuel F
            (.seq bstInorderSpineLoop bstInorderStepBody)
            (mkBstInorderEnv root out cap stList top cur n capU) m π with
          | .error e => .error e
          | .ok ((ρ', m', π'), .returned v) =>
            .ok ((ρ', m', π'), .returned v)
          | .ok ((ρ', m', π'), .broke) =>
            .ok ((ρ', m', π'), .fellThrough)
          | .ok ((ρ', m', π'), .continued) =>
            memEvalStmtFuel F bstInorderOuterLoop ρ' m' π'
          | .ok ((ρ', m', π'), .fellThrough) =>
            memEvalStmtFuel F bstInorderOuterLoop ρ' m' π' :=
        memEvalStmtFuel_while_true F _ _ _ _ _ hgT
      -- Spine fuel: the remaining keys cover the descent plus exit.
      have hrem : (drain (pushSpine focus frames)).length =
          t.flatten.length - emitted.length := by
        have hL := congrArg List.length hInv.heq
        simp only [List.length_append] at hL
        omega
      have hfocusLe : focus.bsize ≤
          (drain (pushSpine focus frames)).length := by
        rw [drain_pushSpine]
        simp only [List.length_append, BTree.length_flatten_eq_bsize]
        exact Nat.le_add_right _ _
      have hspFuel : focus.bsize + 1 ≤ F := by omega
      have hsp := bstInorderSpine_ok F m π hex root t cur focus stk
        frames stA stT stList top n capU cap out outA outT emitted
        hInv hstList hstLen htop hstT hlay hspFuel
      cases hsp with
      | inr hBail =>
        obtain ⟨ρb, mb, hbodyB, hfwdB⟩ := hBail
        have hseqB := memEvalStmtFuel_seq_returned_first F _
          bstInorderStepBody _ _ _ _ _ _ _ hbodyB
        have hFwd : bstInorderOuter (F + 1) m cur stk stA stT outA
            outT cap n = .ok (none, mb) := by
          simp only [bstInorderOuter]
          rw [hfwdB]
        have hbody : memEvalStmtFuel (F + 1) bstInorderOuterLoop
            (mkBstInorderEnv root out cap stList top cur n capU) m π =
            .ok ((ρb, mb, π), .returned
              (.i32 (BitVec.ofNat 32 (2 ^ 32 - 1)))) := by
          rw [hwLoop, hseqB]
        exact Or.inr ⟨_, _, hbody, hFwd⟩
      | inl hCont =>
        obtain ⟨cur', focus', stk', frames', m₁, stList', top', ρ₁,
          pushed, hbodyS, hfwdS, hρ₁, hstListS, hlenS, htopS,
          hnoneS, hpushS, hcondS, hex₁, hInvS⟩ := hCont
        subst hnoneS
        subst hρ₁
        have hne : stk' ≠ [] := by
          by_cases hcn : cur = none
          · have hstkNe : stk ≠ [] := fun h => hfin ⟨hcn, h⟩
            have hpos : 0 < stk.length :=
              Nat.pos_of_ne_zero
                (fun h => hstkNe (List.eq_nil_of_length_eq_zero h))
            have hlen : 0 < (stk ++ pushed).length := by
              simp only [List.length_append]
              omega
            rw [hpushS]
            intro hcon
            rw [hcon] at hlen
            simp at hlen
          · exact hcondS hcn
        obtain ⟨init, alast, hstkEq⟩ :
            ∃ init alast, stk' = init ++ [alast] := by
          have hrev : stk'.reverse ≠ [] := by simpa using hne
          obtain ⟨al, rinit, hrfl⟩ := List.exists_cons_of_ne_nil hrev
          refine ⟨rinit.reverse, al, ?_⟩
          have hrr := (List.reverse_reverse stk').symm
          rw [hrfl, List.reverse_cons] at hrr
          exact hrr
        subst hstkEq
        obtain ⟨tp₀, k₀, lp₀, rp₀, r₀, rest, hnode₀, hr₀, hfrEq,
          hframesRest⟩ := FramesOf.snoc_inv hInvS.hframes rfl
        subst hfrEq
        have hfocusLeaf : focus' = .leaf := by
          cases hInvS.hfocus with
          | nil => rfl
        subst hfocusLeaf
        -- Pop index: `top - 1` lands on the last pushed word.
        have h1lt : 1 ≤ top'.toNat := by
          rw [htopS]
          simp only [List.length_append, List.length_cons,
            List.length_nil]
          omega
        have hle1 : BitVec.ofNat 64 1 ≤ top' := by
          rw [BitVec.le_def]
          have h1v : (BitVec.ofNat 64 1).toNat = 1 := by decide
          rw [h1v]
          exact h1lt
        have hidxNat : (top' - BitVec.ofNat 64 1).toNat =
            init.length := by
          have hsub := BitVec.toNat_sub_of_le hle1
          have h1v : (BitVec.ofNat 64 1).toNat = 1 := by decide
          rw [hsub, h1v, htopS]
          simp only [List.length_append, List.length_cons,
            List.length_nil]
          omega
        -- S1: `top := top - 1`.
        have htopM₁ : memEvalExpr (.var "top")
            (mkBstInorderEnv root out cap stList' top' none n capU)
            m₁ π = .ok (.u64 top') := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _
            (by simp [envLookup, mkBstInorderEnv])
        have h1M₁ : memEvalExpr
            (.lit (.u64 (BitVec.ofNat 64 1)))
            (mkBstInorderEnv root out cap stList' top' none n capU)
            m₁ π = .ok (.u64 (BitVec.ofNat 64 1)) := by
          simp [memEvalExpr, litVal]
        have htopV₁ : evalExpr (.var "top")
            (mkBstInorderEnv root out cap stList' top' none n capU) =
            .ok (.u64 top') :=
          evalExpr_var_hit _ _ _
            (by simp [envLookup, mkBstInorderEnv])
        have h1V₁ : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
            (mkBstInorderEnv root out cap stList' top' none n capU) =
            .ok (.u64 (BitVec.ofNat 64 1)) := by
          simp [evalExpr, litVal]
        have husubM := memEvalExpr_usub_agree _ _ _ _ _ htopM₁ h1M₁
        have husubV := evalExpr_usub_u64u64 _ _ _ _ _ htopV₁ h1V₁
        have hu₂ : envUpdate
            (mkBstInorderEnv root out cap stList' top' none n capU)
            "top" (.u64 (top' - BitVec.ofNat 64 1)) =
            some (mkBstInorderEnv root out cap stList'
              (top' - BitVec.ofNat 64 1) none n capU) := by
          simp [envUpdate, mkBstInorderEnv]
        have hS1 := memEvalStmtFuel_assign F _ _ _ _ _ _ _ husubM
          husubV hu₂
        -- The popped address: ghost and real block agree on the
        -- top word, which is the last pushed link.
        have hvalGet : stList'[(top' - BitVec.ofNat 64 1).toNat]? =
            some (linkWord (some alast)) := by
          rw [hidxNat]
          have hL : init.length < (init ++ [alast]).length := by
            simp [List.length_append]
          have h1 : stList'[init.length]? =
              (List.take (init ++ [alast]).length stList')[init.length]? := by
            rw [List.getElem?_take]
            simp
          rw [h1, hstListS]
          simp
        obtain ⟨stDataS, hfindSt, hlenStS, htakeSS⟩ := hInvS.hstack
        have hgetR : stDataS[(top' - BitVec.ofNat 64 1).toNat]? =
            some (linkWord (some alast)) := by
          rw [hidxNat]
          have hL : init.length < (init ++ [alast]).length := by
            simp [List.length_append]
          have h1 : stDataS[init.length]? =
              (List.take (init ++ [alast]).length stDataS)[init.length]? := by
            rw [List.getElem?_take]
            simp
          rw [h1, htakeSS]
          simp
        have hcSt : cellsAt m₁ stA stT stDataS := hfindSt
        have hmemLoad : memLoad m₁ stA stT
            (top' - BitVec.ofNat 64 1).toNat =
            .ok (linkWord (some alast)) :=
          memLoad_cellsAt _ _ _ _ _ _ hcSt hgetR
        -- S2: `cur := ptrOf (st[top])`.
        have htopM₂ : memEvalExpr (.var "top")
            (mkBstInorderEnv root out cap stList'
              (top' - BitVec.ofNat 64 1) none n capU)
            m₁ π = .ok (.u64 (top' - BitVec.ofNat 64 1)) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _
            (by simp [envLookup, mkBstInorderEnv])
        have htopV₂ : evalExpr (.var "top")
            (mkBstInorderEnv root out cap stList'
              (top' - BitVec.ofNat 64 1) none n capU) =
            .ok (.u64 (top' - BitVec.ofNat 64 1)) :=
          evalExpr_var_hit _ _ _
            (by simp [envLookup, mkBstInorderEnv])
        have hidxAgree : memEvalExpr (.var "top")
            (mkBstInorderEnv root out cap stList'
              (top' - BitVec.ofNat 64 1) none n capU)
            m₁ π =
            evalExpr (.var "top")
              (mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1) none n capU) := by
          rw [htopM₂, htopV₂]
        have harr₂ : envLookup
            (mkBstInorderEnv root out cap stList'
              (top' - BitVec.ofNat 64 1) none n capU)
            "st" = some (.arr32 stList') := by
          simp [envLookup, mkBstInorderEnv]
        have htopL₂ : envLookup
            (mkBstInorderEnv root out cap stList'
              (top' - BitVec.ofNat 64 1) none n capU)
            "top" = some (.u64 (top' - BitVec.ofNat 64 1)) := by
          simp [envLookup, mkBstInorderEnv]
        have hidxM := memEvalExpr_idxu_hit _ _ _ _ _ _ _ _ _ _
          hlay harr₂ hidxAgree htopV₂ hmemLoad hvalGet
        have hptrM := memEvalExpr_ptrOf_agree _ _ _ _ hidxM
        have hptrV : evalExpr (.ptrOf (.idxu "st" (.var "top")))
            (mkBstInorderEnv root out cap stList'
              (top' - BitVec.ofNat 64 1) none n capU) =
            .ok (.ptrVal (addrOfWord (linkWord (some alast)))) := by
          simp only [evalExpr, htopL₂, harr₂, hvalGet]
        have hfindA : memFind m₁ alast =
            some ⟨tp₀, true, [k₀, linkWord lp₀, linkWord rp₀]⟩ := by
          have h := hnode₀
          unfold nodeAt3 cellsAt at h
          exact h
        have hmemAb : (memFind m₁ alast).isSome = true := by
          rw [hfindA]
          rfl
        have hbndA : alast + 1 < 2 ^ 32 := hex₁ _ hmemAb
        have hdecA : addrOfWord (linkWord (some alast)) =
            some alast :=
          addrOfWord_linkWord_some hbndA
        rw [hdecA] at hptrV
        have hu₂c : envUpdate
            (mkBstInorderEnv root out cap stList'
              (top' - BitVec.ofNat 64 1) none n capU)
            "cur" (.ptrVal (some alast)) =
            some (mkBstInorderEnv root out cap stList'
              (top' - BitVec.ofNat 64 1) (some alast) n capU) := by
          simp [envUpdate, mkBstInorderEnv]
        have hS2 := memEvalStmtFuel_assign F _ _ _ _ _ _ _ hptrM
          hptrV hu₂c
        -- Capacity check on the emit counter.
        have hnM : memEvalExpr (.var "n")
            (mkBstInorderEnv root out cap stList'
              (top' - BitVec.ofNat 64 1) (some alast) n capU)
            m₁ π = .ok (.u64 n) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _
            (by simp [envLookup, mkBstInorderEnv])
        have hcapM : memEvalExpr (.var "capU")
            (mkBstInorderEnv root out cap stList'
              (top' - BitVec.ofNat 64 1) (some alast) n capU)
            m₁ π = .ok (.u64 capU) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _
            (by simp [envLookup, mkBstInorderEnv])
        have hnV : evalExpr (.var "n")
            (mkBstInorderEnv root out cap stList'
              (top' - BitVec.ofNat 64 1) (some alast) n capU) =
            .ok (.u64 n) :=
          evalExpr_var_hit _ _ _
            (by simp [envLookup, mkBstInorderEnv])
        have hcapV : evalExpr (.var "capU")
            (mkBstInorderEnv root out cap stList'
              (top' - BitVec.ofNat 64 1) (some alast) n capU) =
            .ok (.u64 capU) :=
          evalExpr_var_hit _ _ _
            (by simp [envLookup, mkBstInorderEnv])
        have hultM₃ := memEvalExpr_ult_agree _ _ _ _ _ hnM hcapM
        have hultV₃ := evalExpr_ult_u64 _ _ _ _ _ hnV hcapV
        by_cases hultT : n.toNat < capU.toNat
        · -- Emit leg: the out buffer has room.
          have hultTb : (n.ult capU) = true := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_true hultT
          have hifT : memEvalExpr (.ult (.var "n") (.var "capU"))
              (mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1) (some alast) n capU)
              m₁ π = .ok (.b true) := by
            rw [hultM₃, hultV₃, hultTb]
          obtain ⟨outData, hfindOut, htakeOut⟩ := hInvS.hout
          have hcapLe : capU.toNat ≤ outData.length := by
            rw [hcapU]
            exact hInvS.houtCap _ hfindOut
          have hblen : n.toNat < outData.length := by omega
          have hgetOut := List.getElem?_eq_getElem hblen
          obtain ⟨m₂, hstoreOut, hfindOutM⟩ := arrSet_lockstep m₁
            outA outT outData n.toNat k₀ _ _ hfindOut rfl rfl
            rfl hgetOut
          have he₂c : memEvalExpr (.var "cur")
              (mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1) (some alast) n capU)
              m₁ π = .ok (.ptrVal (some alast)) := by
            rw [memEvalExpr_var]
            exact evalExpr_var_hit _ _ _
              (by simp [envLookup, mkBstInorderEnv])
          have hveM := memEvalExpr_pgetVal_hit _ _ _ _ _ _ _
            he₂c hfindA (nodeLoadKey hnode₀)
          have hieM : memEvalExpr (.var "n")
              (mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1) (some alast) n capU)
              m₁ π = .ok (.u64 n) := hnM
          have hmstore := memEvalStmtFuel_mstore_ok F _ _ _ _ _ _ _ _ _ _ _
            hieM hveM hlayOut hstoreOut
          -- `n := n + 1`.
          have hnM₂ : memEvalExpr (.var "n")
              (mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1) (some alast) n capU)
              m₂ π = .ok (.u64 n) := by
            rw [memEvalExpr_var]
            exact evalExpr_var_hit _ _ _
              (by simp [envLookup, mkBstInorderEnv])
          have h1M₂ : memEvalExpr
              (.lit (.u64 (BitVec.ofNat 64 1)))
              (mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1) (some alast) n capU)
              m₂ π = .ok (.u64 (BitVec.ofNat 64 1)) := by
            simp [memEvalExpr, litVal]
          have hnV₂ : evalExpr (.var "n")
              (mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1) (some alast) n capU) =
              .ok (.u64 n) :=
            evalExpr_var_hit _ _ _
              (by simp [envLookup, mkBstInorderEnv])
          have h1V₂ : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
              (mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1) (some alast) n capU) =
              .ok (.u64 (BitVec.ofNat 64 1)) := by
            simp [evalExpr, litVal]
          have huaddM := memEvalExpr_uadd_agree _ _ _ _ _ hnM₂ h1M₂
          have huaddV := evalExpr_uadd_u64 _ _ _ _ _ hnV₂ h1V₂
          have hu₂n : envUpdate
              (mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1) (some alast) n capU)
              "n" (.u64 (n + BitVec.ofNat 64 1)) =
              some (mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1) (some alast)
                (n + BitVec.ofNat 64 1) capU) := by
            simp [envUpdate, mkBstInorderEnv]
          have hnPlus := memEvalStmtFuel_assign F _ _ _ _ _ _ _
            huaddM huaddV hu₂n
          -- `cur := cur->right`.
          have heR : memEvalExpr (.var "cur")
              (mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1) (some alast)
                (n + BitVec.ofNat 64 1) capU)
              m₂ π = .ok (.ptrVal (some alast)) := by
            rw [memEvalExpr_var]
            exact evalExpr_var_hit _ _ _
              (by simp [envLookup, mkBstInorderEnv])
          have hneAOut : alast ≠ outA :=
            hInvS.hneOut alast (hInvS.hmemFr alast (by simp))
          have hfindA₂ : memFind m₂ alast =
              some ⟨tp₀, true, [k₀, linkWord lp₀, linkWord rp₀]⟩ := by
            rw [memFind_memStore_other _ _ _ _ _ _ _ hstoreOut hneAOut]
            exact hfindA
          have hnodeA₂ : nodeAt3 m₂ alast tp₀ k₀ lp₀ rp₀ :=
            nodeAt3_store_other hnode₀ hstoreOut hneAOut
          have hpgetR := memEvalExpr_pgetRight_hit _ _ _ _ _ _ _
            heR hfindA₂ (nodeLoadRight hnodeA₂)
          have hu₃ : envUpdate
              (mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1) (some alast)
                (n + BitVec.ofNat 64 1) capU)
              "cur" (.ptrVal (addrOfWord (linkWord rp₀))) =
              some (mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1)
                (addrOfWord (linkWord rp₀))
                (n + BitVec.ofNat 64 1) capU) := by
            simp [envUpdate, mkBstInorderEnv]
          have hcurR := memEvalStmtFuel_assign_mem F _ _ _ _ _ _ _
            hpgetR hu₃
          have hSkip : memEvalStmtFuel F .skip
              (mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1)
                (addrOfWord (linkWord rp₀))
                (n + BitVec.ofNat 64 1) capU)
              m₂ π =
              .ok (((mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1)
                (addrOfWord (linkWord rp₀))
                (n + BitVec.ofNat 64 1) capU), m₂, π),
                .fellThrough) := by
            cases F <;>
              simp [memEvalStmtFuel, memEvalStmtZero,
                memEvalStmtWith]
          have hEmitRest := memEvalStmtFuel_seq F _ _ _ _ _ _ _ _ _ _ _ _
            hnPlus hcurR
          have hEmit := memEvalStmtFuel_seq F _ _ _ _ _ _ _ _ _ _ _ _
            hmstore hEmitRest
          have hIfE := memEvalStmtFuel_if_true F
            (.ult (.var "n") (.var "capU"))
            (.seq (.mstore "out" (.var "n")
              (.pgetVal (.var "cur")))
            (.seq (.assign "n" (.uadd (.var "n")
              (.lit (.u64 (BitVec.ofNat 64 1)))))
            (.assign "cur" (.pgetRight (.var "cur")))))
            (.return_ (.lit (.i32 (BitVec.ofNat 32 (2 ^ 32 - 1)))))
            _ _ _ hifT
          have hS3pre : memEvalStmtFuel F
              (.if_ (.ult (.var "n") (.var "capU"))
                (.seq (.mstore "out" (.var "n")
                  (.pgetVal (.var "cur")))
                (.seq (.assign "n" (.uadd (.var "n")
                  (.lit (.u64 (BitVec.ofNat 64 1)))))
                (.assign "cur" (.pgetRight (.var "cur")))))
                (.return_ (.lit (.i32 (BitVec.ofNat 32 (2 ^ 32 - 1))))))
              (mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1) (some alast) n capU)
              m₁ π =
              .ok (((mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1)
                (addrOfWord (linkWord rp₀))
                (n + BitVec.ofNat 64 1) capU), m₂, π),
                .fellThrough) := by
            rw [hIfE]
            exact hEmit
          have hS3 := memEvalStmtFuel_seq F _ _ _ _ _ _ _ _ _ _ _ _
            hS3pre hSkip
          have hStep23 := memEvalStmtFuel_seq F _ _ _ _ _ _ _ _ _ _ _ _
            hS2 hS3
          have hStepRest := memEvalStmtFuel_seq F _ _ _ _ _ _ _ _ _ _ _ _
            hS1 hStep23
          have hStep : memEvalStmtFuel F
              (.seq bstInorderSpineLoop bstInorderStepBody)
              (mkBstInorderEnv root out cap stList top cur n capU)
              m π =
              .ok (((mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1)
                (addrOfWord (linkWord rp₀))
                (n + BitVec.ofNat 64 1) capU), m₂, π),
                .fellThrough) := by
            simp only [bstInorderStepBody]
            exact memEvalStmtFuel_seq F _ _ _ _ _ _ _ _ _ _ _ _
              hbodyS hStepRest
          have hbody : memEvalStmtFuel (F + 1) bstInorderOuterLoop
              (mkBstInorderEnv root out cap stList top cur n capU) m π =
              memEvalStmtFuel F bstInorderOuterLoop
                (mkBstInorderEnv root out cap stList'
                  (top' - BitVec.ofNat 64 1)
                  (addrOfWord (linkWord rp₀))
                  (n + BitVec.ofNat 64 1) capU)
                m₂ π := by
            rw [hwLoop, hStep]
          -- Forward pop-branch: the same pop-emit-right.
          have hFwd : bstInorderOuter (F + 1) m cur stk stA stT outA
              outT cap n =
              bstInorderOuter F m₂ (addrOfWord (linkWord rp₀)) init
                stA stT outA outT cap (n + BitVec.ofNat 64 1) := by
            simp only [bstInorderOuter]
            rw [hfwdS]
            simp only []
            split
            · rename_i h
              have hL := congrArg List.length h
              simp only [List.length_append, List.length_cons,
                List.length_nil] at hL
              omega
            · rw [List.getLast?_concat]
              simp only []
              rw [hfindA]
              simp only []
              rw [nodeLoadKey hnode₀, nodeLoadRight hnode₀]
              simp only []
              rw [← hcapU, ite_eq_left hultT, hstoreOut,
                List.dropLast_concat]
              simp only []
              rfl
          -- Post-step footprint: the out block grew by the key,
          -- the stack block is untouched.
          have hfindA₂ : memFind m₂ stA = some ⟨stT, true, stDataS⟩ := by
            rw [memFind_memStore_other _ _ _ _ _ _ _ hstoreOut
              hInvS.hstNeOut]
            exact hfindSt
          have hlen3st₂ : ∀ t k l r, ¬ nodeAt3 m₂ stA t k l r := by
            intro t k' l' r' h3
            unfold nodeAt3 cellsAt at h3
            rw [hfindA₂] at h3
            have hX := Option.some.inj h3
            have hlenEq : stDataS = [k', linkWord l', linkWord r'] :=
              (Block.mk.inj hX).2.2
            have hL : stDataS.length = 3 := by
              rw [hlenEq]
              simp
            rw [hlenStS] at hL
            have hsz : bstInorderStackSize = 64 := rfl
            rw [hsz] at hL
            omega
          have hneSt₂ : ∀ b, TreeSegMem (m := m₂) root b → b ≠ stA := by
            intro b hb heq
            exact TreeSegMem_store_fresh hlen3st₂ hb heq
          have hdataEq : ∀ data, memFind m₂ outA =
              some ⟨outT, true, data⟩ →
              data = outData.set n.toNat k₀ := by
            intro data hd
            have hX := Option.some.inj (hfindOutM.symm.trans hd)
            exact (Block.mk.inj hX).2.2.symm
          have houtCap₂ : ∀ data, memFind m₂ outA =
              some ⟨outT, true, data⟩ →
              (cap.signExtend 64).toNat ≤ data.length := by
            intro data hd
            rw [hdataEq data hd, List.length_set]
            exact hInvS.houtCap _ hfindOut
          have houtLen₂ : ∀ data, memFind m₂ outA =
              some ⟨outT, true, data⟩ → data.length ≠ 3 := by
            intro data hd
            rw [hdataEq data hd, List.length_set]
            exact hInvS.houtLen _ hfindOut
          have hlen3out₂ : ∀ t k l r, ¬ nodeAt3 m₂ outA t k l r := by
            intro t k' l' r' h3
            unfold nodeAt3 cellsAt at h3
            rw [hfindOutM] at h3
            have hX := Option.some.inj h3
            have hlenEq : outData.set n.toNat k₀ =
                [k', linkWord l', linkWord r'] :=
              (Block.mk.inj hX).2.2
            have hL := congrArg List.length hlenEq
            simp only [List.length_set, List.length_cons,
              List.length_nil] at hL
            exact hInvS.houtLen _ hfindOut hL
          have hneOut₂ : ∀ b, TreeSegMem (m := m₂) root b → b ≠ outA := by
            intro b hb heq
            exact TreeSegMem_store_fresh hlen3out₂ hb heq
          -- Prefix narrowing for the popped stack.
          have htake₂ : stDataS.take init.length =
              init.map fun a => linkWord (some a) := by
            have e1 : stDataS.take init.length =
                (stDataS.take (init ++ [alast]).length).take
                  init.length := by
              rw [List.take_take,
                Nat.min_eq_left (by simp [List.length_append])]
            have eL : init.length =
                ((init.map fun a => linkWord (some a))).length := by
              simp
            rw [e1, htakeSS, List.map_append, eL,
              List.take_append_length]
          have hstList₂ : stList'.take init.length =
              init.map fun a => linkWord (some a) := by
            have e1 : stList'.take init.length =
                (stList'.take (init ++ [alast]).length).take
                  init.length := by
              rw [List.take_take,
                Nat.min_eq_left (by simp [List.length_append])]
            have eL : init.length =
                ((init.map fun a => linkWord (some a))).length := by
              simp
            rw [e1, hstListS, List.map_append, eL,
              List.take_append_length]
          have hstack₂ : StackMirror m₂ stA stT init :=
            ⟨stDataS, hfindA₂, hlenStS, htake₂⟩
          have hstacklen₂ : init.length ≤ bstInorderStackSize := by
            have hL := hInvS.hstacklen
            simp only [List.length_append, List.length_cons,
              List.length_nil] at hL
            omega
          -- Key counting for the emitted prefix.
          have he₂ : (emitted ++ [k₀]).length = emitted.length + 1 := by
            simp
          have hn1 : (n + BitVec.ofNat 64 1).toNat = n.toNat + 1 := by
            have h1 : (BitVec.ofNat 64 1).toNat = 1 := by decide
            rw [BitVec.toNat_add, h1, Nat.mod_eq_of_lt (by omega)]
          have hn₂ : (emitted ++ [k₀]).length =
              (n + BitVec.ofNat 64 1).toNat := by
            rw [he₂, hInvS.hn, hn1]
          have htakeOut₂ : (outData.set n.toNat k₀).take
              (emitted ++ [k₀]).length = emitted ++ [k₀] := by
            rw [he₂]
            have e := take_set_succ outData n.toNat k₀ hblen
            rw [← hInvS.hn] at e ⊢
            rw [e, htakeOut]
          have hout₂ : OutPrefix m₂ outA outT (emitted ++ [k₀]) :=
            ⟨outData.set n.toNat k₀, hfindOutM, htakeOut₂⟩
          have heq₂ : (emitted ++ [k₀]) ++
              drain (pushSpine r₀ rest) = t.flatten := by
            have e := hInvS.heq
            simp only [pushSpine, drain_cons] at e
            rw [List.append_assoc]
            exact e
          have hlen₂ : emitted.length + 1 +
              (drain (pushSpine r₀ rest)).length =
              t.flatten.length := by
            have hL := congrArg List.length heq₂
            simp only [List.length_append, List.length_cons,
              List.length_nil] at hL
            omega
          have hbound₂ : (t.flatten.length - (emitted ++ [k₀]).length) +
              2 ≤ F := by
            rw [he₂]
            omega
          have hex₂ : ∀ x, (memFind m₂ x).isSome = true →
              x + 1 < 2 ^ 32 := by
            intro x hx
            by_cases heq : x = outA
            · rw [heq]
              exact hex₁ outA (by rw [hfindOut]; rfl)
            · have hfindEq : memFind m₂ x = memFind m₁ x :=
                memFind_memStore_other _ _ _ _ _ _ _ hstoreOut heq
              rw [hfindEq] at hx
              exact hex₁ x hx
          have hmemCur₂ : ∀ c, addrOfWord (linkWord rp₀) = some c →
              TreeSegMem (m := m₂) root c := by
            intro c hc
            cases rp₀ with
            | none =>
              rw [addrOfWord_linkWord_none] at hc
              cases hc
            | some b =>
              have hsome : addrOfWord (linkWord (some b)) = some b := by
                have hmemBb : (memFind m₁ b).isSome = true :=
                  TreeSeg_head_alloc hr₀
                exact addrOfWord_linkWord_some (hex₁ _ hmemBb)
              rw [hsome] at hc
              have hcb : c = b := (Option.some.inj hc).symm
              subst c
              have hmemA : TreeSegMem (m := m₁) root alast :=
                hInvS.hmemFr alast (by simp)
              have hmemB : TreeSegMem (m := m₁) root b :=
                TreeSegMem_child_right hmemA hnode₀ hr₀ rfl
              exact TreeSegMem_store_other hmemB hstoreOut
                hInvS.hneOut
          have hmemFr₂ : ∀ x, x ∈ init → TreeSegMem (m := m₂) root x := by
            intro x hx
            exact TreeSegMem_store_other
              (hInvS.hmemFr x (List.mem_append.mpr (Or.inl hx)))
              hstoreOut hInvS.hneOut
          have hseg₂ : TreeSeg m₂ root t :=
            TreeSeg.store_other hInvS.hseg hstoreOut hInvS.hneOut
          have hsegR₂ : TreeSeg m₂ (addrOfWord (linkWord rp₀)) r₀ := by
            cases rp₀ with
            | none =>
              have hr0leaf : r₀ = .leaf := by
                cases hr₀ with
                | nil => rfl
              subst hr0leaf
              rw [addrOfWord_linkWord_none]
              exact TreeSeg.nil
            | some b =>
              have hmemBb : (memFind m₁ b).isSome = true :=
                TreeSeg_head_alloc hr₀
              have hcur₂ : addrOfWord (linkWord (some b)) = some b :=
                addrOfWord_linkWord_some (hex₁ _ hmemBb)
              rw [hcur₂]
              have hmemB₂ : TreeSegMem (m := m₁) root b :=
                TreeSegMem_child_right
                  (hInvS.hmemFr alast (by simp)) hnode₀ hr₀ rfl
              have hneRpOut : ∀ a, TreeSegMem (m := m₁) (some b) a →
                  a ≠ outA := by
                intro a ha
                exact hInvS.hneOut a (TreeSegMem_trans hmemB₂ ha)
              exact TreeSeg.store_other hr₀ hstoreOut hneRpOut
          have hmemR : ∀ a, a ∈ init → TreeSegMem (m := m₁) root a :=
            fun a ha => hInvS.hmemFr a (List.mem_append.mpr (Or.inl ha))
          have hframes₂ : FramesOf m₂ init rest :=
            FramesOf_store_other hframesRest hstoreOut hInvS.hneOut
              hmemR
          have hInv₂ : InorderInv m₂ root t stA stT outA outT cap
              (n + BitVec.ofNat 64 1) (emitted ++ [k₀])
              (addrOfWord (linkWord rp₀)) r₀ init rest :=
            ⟨hseg₂, hsegR₂, hframes₂, hstack₂, hstacklen₂, hout₂,
              hn₂, heq₂, hmemCur₂, hmemFr₂, hneSt₂, hneOut₂,
              hInvS.hstNeOut, houtLen₂, houtCap₂⟩
          have hIH := ih m₂ π hex₂ root t
              (addrOfWord (linkWord rp₀)) r₀ init rest stA stT
              stList' (top' - BitVec.ofNat 64 1)
              (n + BitVec.ofNat 64 1) capU cap out outA outT
              (emitted ++ [k₀])
              hInv₂ hstList₂ hlenS hidxNat hstT hlay hbound₂
              hcapU hlayOut h64
          cases hIH with
          | inl hFin =>
            obtain ⟨nCnt, m', ρ', stList'', top'', emitted'',
              hbodyF, hfwdF, hρF, hInvF, hemF⟩ := hFin
            have hbody' : memEvalStmtFuel (F + 1) bstInorderOuterLoop
                (mkBstInorderEnv root out cap stList top cur n capU) m π =
                .ok ((ρ', m', π), .fellThrough) := by
              rw [hbody, hbodyF]
            have hFwd' : bstInorderOuter (F + 1) m cur stk stA stT outA
                outT cap n = .ok (some nCnt, m') := by
              rw [hFwd, hfwdF]
            exact Or.inl ⟨_, _, _, _, _, _,
              hbody', hFwd', hρF, hInvF, hemF⟩
          | inr hBail₂ =>
            obtain ⟨ρ', m', hbodyB₂, hfwdB₂⟩ := hBail₂
            have hbody' : memEvalStmtFuel (F + 1) bstInorderOuterLoop
                (mkBstInorderEnv root out cap stList top cur n capU) m π =
                .ok ((ρ', m', π), .returned
                  (.i32 (BitVec.ofNat 32 (2 ^ 32 - 1)))) := by
              rw [hbody, hbodyB₂]
            have hFwd' : bstInorderOuter (F + 1) m cur stk stA stT outA
                outT cap n = .ok (none, m') := by
              rw [hFwd, hfwdB₂]
            exact Or.inr ⟨_, _, hbody', hFwd'⟩
        · -- Capacity-bail leg: the out buffer is full, return `-1`.
          have hultFb : (n.ult capU) = false := by
            rw [BitVec.ult_eq_decide]
            exact decide_eq_false hultT
          have hifF : memEvalExpr (.ult (.var "n") (.var "capU"))
              (mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1) (some alast) n capU)
              m₁ π = .ok (.b false) := by
            rw [hultM₃, hultV₃, hultFb]
          have hIfB := memEvalStmtFuel_if_false F
            (.ult (.var "n") (.var "capU"))
            (.seq (.mstore "out" (.var "n")
              (.pgetVal (.var "cur")))
            (.seq (.assign "n" (.uadd (.var "n")
              (.lit (.u64 (BitVec.ofNat 64 1)))))
            (.assign "cur" (.pgetRight (.var "cur")))))
            (.return_ (.lit (.i32 (BitVec.ofNat 32 (2 ^ 32 - 1)))))
            _ _ _ hifF
          have hagreeR : memEvalExpr
              (.lit (.i32 (BitVec.ofNat 32 (2 ^ 32 - 1))))
              (mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1) (some alast) n capU)
              m₁ π =
              evalExpr
              (.lit (.i32 (BitVec.ofNat 32 (2 ^ 32 - 1))))
              (mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1) (some alast) n capU) := by
            simp [memEvalExpr, evalExpr, litVal]
          have hevR : evalExpr
              (.lit (.i32 (BitVec.ofNat 32 (2 ^ 32 - 1))))
              (mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1) (some alast) n capU) =
              .ok (.i32 (BitVec.ofNat 32 (2 ^ 32 - 1))) := by
            simp [evalExpr, litVal]
          have hret := memEvalStmtFuel_return F _ _ _ _ _ hagreeR hevR
          have hS3preB : memEvalStmtFuel F
              (.if_ (.ult (.var "n") (.var "capU"))
                (.seq (.mstore "out" (.var "n")
                  (.pgetVal (.var "cur")))
                (.seq (.assign "n" (.uadd (.var "n")
                  (.lit (.u64 (BitVec.ofNat 64 1)))))
                (.assign "cur" (.pgetRight (.var "cur")))))
                (.return_ (.lit (.i32 (BitVec.ofNat 32 (2 ^ 32 - 1))))))
              (mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1) (some alast) n capU)
              m₁ π =
              .ok (((mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1) (some alast) n capU),
                m₁, π),
                .returned
                  (.i32 (BitVec.ofNat 32 (2 ^ 32 - 1)))) := by
            rw [hIfB]
            exact hret
          have hS3B := memEvalStmtFuel_seq_returned_first F _ .skip _ _ _ _ _ _ _
            hS3preB
          have hStep23B := memEvalStmtFuel_seq F _ _ _ _ _ _ _ _ _ _ _ _
            hS2 hS3B
          have hStepRestB := memEvalStmtFuel_seq F _ _ _ _ _ _ _ _ _ _ _ _
            hS1 hStep23B
          have hStepB : memEvalStmtFuel F
              (.seq bstInorderSpineLoop bstInorderStepBody)
              (mkBstInorderEnv root out cap stList top cur n capU)
              m π =
              .ok (((mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1) (some alast) n capU),
                m₁, π),
                .returned
                  (.i32 (BitVec.ofNat 32 (2 ^ 32 - 1)))) := by
            simp only [bstInorderStepBody]
            exact memEvalStmtFuel_seq F _ _ _ _ _ _ _ _ _ _ _ _
              hbodyS hStepRestB
          have hbodyB : memEvalStmtFuel (F + 1) bstInorderOuterLoop
              (mkBstInorderEnv root out cap stList top cur n capU) m π =
              .ok (((mkBstInorderEnv root out cap stList'
                (top' - BitVec.ofNat 64 1) (some alast) n capU),
                m₁, π),
                .returned
                  (.i32 (BitVec.ofNat 32 (2 ^ 32 - 1)))) := by
            rw [hwLoop, hStepB]
          have hFwdC : bstInorderOuter (F + 1) m cur stk stA stT outA
              outT cap n = .ok (none, m₁) := by
            simp only [bstInorderOuter]
            rw [hfwdS]
            simp only []
            split
            · rename_i h
              have hL := congrArg List.length h
              simp only [List.length_append, List.length_cons,
                List.length_nil] at hL
              omega
            · rw [List.getLast?_concat]
              simp only []
              rw [hfindA]
              simp only []
              rw [nodeLoadKey hnode₀, nodeLoadRight hnode₀]
              simp only []
              rw [← hcapU, ite_eq_right hultT]
          exact Or.inr ⟨_, _, hbodyB, hFwdC⟩

/-- Entry correctness: with a sane caller buffer (big enough,
    non-node-shaped, disjoint) and sufficient fuel, `bst_inorder`
    writes exactly the inorder keys and returns the count; the
    loud legs are modelled by the `-1` disjunct. -/
theorem bstInorderFunc_correct (F : Nat) (m : Mem) (π : Layout)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (hmfresh : memFind m m.next = none)
    (hnext : m.next + 1 < 2 ^ 32)
    (root : Option Addr) (t : BTree)
    (out : Option Addr) (cap : BitVec 32)
    (outA : Addr) (outT : Nat) (outData : List (BitVec 32))
    (hbst : Bst none none t)
    (hseg : TreeSeg m root t)
    (hout : memFind m outA = some ⟨outT, true, outData⟩)
    (houtLen : outData.length ≠ 3)
    (houtNe : ∀ b, TreeSegMem (m := m) root b → b ≠ outA)
    (hlen : t.bsize + 2 ≤ F)
    (hcapLen : (cap.signExtend 64).toNat ≤ outData.length)
    (hcapFit : t.flatten.length ≤ (cap.signExtend 64).toNat)
    (hsize : t.flatten.length < 2 ^ 32)
    (houtV : out = some outA)
    (hlayOut₀ : layoutLookup π "out" = some (outA, outT)) :
    ∃ (ρ' : Env) (m' : Mem) (n' : BitVec 32) (π' : Layout),
      memEvalStmtFuel F bstInorderFunc.body
        [("root", .ptrVal root), ("out", .ptrVal out),
          ("cap", .i32 cap)] m π =
        .ok ((ρ', m', π'), .returned (.i32 n')) ∧
      ((∃ emitted' : List (BitVec 32),
          OutPrefix m' outA outT emitted' ∧
            emitted' = t.flatten ∧ n'.toNat = emitted'.length)
        ∨ n' = BitVec.ofNat 32 (2 ^ 32 - 1)) := by
  have hn64 : (BitVec.ofNat 64 bstInorderStackSize).toNat = 64 := by
    decide
  have hseM : memEvalExpr
      (.lit (.u64 (BitVec.ofNat 64 bstInorderStackSize)))
      [("root", .ptrVal root), ("out", .ptrVal out),
        ("cap", .i32 cap)] m π =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 bstInorderStackSize)))
        [("root", .ptrVal root), ("out", .ptrVal out),
          ("cap", .i32 cap)] :=
    memEvalExpr_lit _ _ _ _
  have hseV : evalExpr
      (.lit (.u64 (BitVec.ofNat 64 bstInorderStackSize)))
      [("root", .ptrVal root), ("out", .ptrVal out),
        ("cap", .i32 cap)] =
      .ok (.u64 (BitVec.ofNat 64 bstInorderStackSize)) := by
    simp [evalExpr, litVal]
  have hpair : ∃ m₁ stA, (m₁, stA) = memAllocData m
      (List.replicate (BitVec.ofNat 64 bstInorderStackSize).toNat 0) :=
    ⟨_, _, rfl⟩
  obtain ⟨m₁, stA, hpair⟩ := hpair
  have hArr := memEvalStmtFuel_let_arrNew F "st"
    (.array (.u 32) bstInorderStackSize)
    (.lit (.u64 (BitVec.ofNat 64 bstInorderStackSize)))
    [("root", .ptrVal root), ("out", .ptrVal out),
      ("cap", .i32 cap)] m π
    (BitVec.ofNat 64 bstInorderStackSize) hseM hseV
  have hLetSt : memEvalStmtFuel F
      (.let_ "st" (.array (.u 32) bstInorderStackSize)
        (.arrNew (.lit (.u64 (BitVec.ofNat 64 bstInorderStackSize)))))
      [("root", .ptrVal root), ("out", .ptrVal out),
        ("cap", .i32 cap)] m π =
      .ok (((("st", .arr32 (List.replicate
        (BitVec.ofNat 64 bstInorderStackSize).toNat 0)) ::
        [("root", .ptrVal root), ("out", .ptrVal out),
          ("cap", .i32 cap)], m₁, ("st", stA, stA) :: π)),
        .fellThrough) := by
    rw [hArr, ← hpair]
  have hstNext : stA = m.next := by
    have h := memAllocData_next m
      (List.replicate (BitVec.ofNat 64 bstInorderStackSize).toNat 0)
    rw [← hpair] at h
    exact h
  have hzeros : List.replicate
      (BitVec.ofNat 64 bstInorderStackSize).toNat (0 : BitVec 32) =
      List.replicate 64 0 := by
    rw [hn64]
  have hfindSt₁ : memFind m₁ stA =
      some ⟨stA, true, List.replicate 64 0⟩ := by
    have h := memFind_alloc_hit m
      (List.replicate (BitVec.ofNat 64 bstInorderStackSize).toNat 0)
    rw [← hpair, hn64] at h
    simpa using h
  have hneOutNext : outA ≠ m.next := by
    intro hcon
    rw [hcon, hmfresh] at hout
    cases hout
  have hm₁ : m₁ = (memAllocData m (List.replicate
      (BitVec.ofNat 64 bstInorderStackSize).toNat 0)).1 :=
    congrArg Prod.fst hpair
  have hstA : stA = (memAllocData m (List.replicate
      (BitVec.ofNat 64 bstInorderStackSize).toNat 0)).2 :=
    congrArg Prod.snd hpair
  have hfindOut₁ : memFind m₁ outA =
      some ⟨outT, true, outData⟩ := by
    have h := memFind_memAllocData_other m
      (List.replicate (BitVec.ofNat 64 bstInorderStackSize).toNat 0)
      outA hneOutNext
    rw [← hm₁] at h
    rw [h]
    exact hout
  have hneNext : ∀ b, TreeSegMem (m := m) root b → b ≠ m.next := by
    intro b hb heq
    have hs := TreeSegMem_find_some hb
    rw [heq, hmfresh] at hs
    cases hs
  have hseg₁ : TreeSeg m₁ root t := by
    have h := TreeSeg.alloc_other hseg
      (List.replicate (BitVec.ofNat 64 bstInorderStackSize).toNat 0)
      hneNext
    rw [← hm₁] at h
    exact h
  have hex₁ : ∀ x, (memFind m₁ x).isSome = true → x + 1 < 2 ^ 32 := by
    intro x hx
    by_cases heq : x = stA
    · subst heq
      rw [hstNext] at *
      exact hnext
    · have hne : x ≠ m.next := by
        rw [← hstNext]
        exact heq
      have hfindEq : memFind m₁ x = memFind m x := by
        have h := memFind_memAllocData_other m
          (List.replicate (BitVec.ofNat 64 bstInorderStackSize).toNat 0)
          x hne
        rw [← hm₁] at h
        exact h
      rw [hfindEq] at hx
      exact hex _ hx
  -- Remaining lets: `top`, `cur`, `n`, `capU`.
  have hTopM : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (("st", .arr32 (List.replicate
        (BitVec.ofNat 64 bstInorderStackSize).toNat 0)) ::
        [("root", .ptrVal root), ("out", .ptrVal out),
          ("cap", .i32 cap)]) m₁
      (("st", stA, stA) :: π) =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        ((("st", .arr32 (List.replicate
          (BitVec.ofNat 64 bstInorderStackSize).toNat 0)) ::
          [("root", .ptrVal root), ("out", .ptrVal out),
            ("cap", .i32 cap)])) :=
    memEvalExpr_lit _ _ _ _
  have hTopV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      ((("st", .arr32 (List.replicate
        (BitVec.ofNat 64 bstInorderStackSize).toNat 0)) ::
        [("root", .ptrVal root), ("out", .ptrVal out),
          ("cap", .i32 cap)])) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  have hTop := memEvalStmtFuel_let_pure F "top" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0))) _ _ _
    (.u64 (BitVec.ofNat 64 0))
    (by simp) (by simp) (by simp) (by simp) hTopM hTopV
  have hCurM : memEvalExpr (.var "root")
      (("top", .u64 (BitVec.ofNat 64 0)) ::
        ("st", .arr32 (List.replicate
          (BitVec.ofNat 64 bstInorderStackSize).toNat 0)) ::
        [("root", .ptrVal root), ("out", .ptrVal out),
          ("cap", .i32 cap)]) m₁
      (("st", stA, stA) :: π) =
      evalExpr (.var "root")
        ((("top", .u64 (BitVec.ofNat 64 0)) ::
          ("st", .arr32 (List.replicate
            (BitVec.ofNat 64 bstInorderStackSize).toNat 0)) ::
          [("root", .ptrVal root), ("out", .ptrVal out),
            ("cap", .i32 cap)])) :=
    memEvalExpr_var _ _ _ _
  have hCurV : evalExpr (.var "root")
      ((("top", .u64 (BitVec.ofNat 64 0)) ::
        ("st", .arr32 (List.replicate
          (BitVec.ofNat 64 bstInorderStackSize).toNat 0)) ::
        [("root", .ptrVal root), ("out", .ptrVal out),
          ("cap", .i32 cap)])) =
      .ok (.ptrVal root) := by
    simp [evalExpr, envLookup]
  have hCur := memEvalStmtFuel_let_pure F "cur" nodeTy (.var "root")
    _ _ _ (.ptrVal root)
    (by simp) (by simp) (by simp) (by simp) hCurM hCurV
  have hNM : memEvalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (("cur", .ptrVal root) ::
        ("top", .u64 (BitVec.ofNat 64 0)) ::
        ("st", .arr32 (List.replicate
          (BitVec.ofNat 64 bstInorderStackSize).toNat 0)) ::
        [("root", .ptrVal root), ("out", .ptrVal out),
          ("cap", .i32 cap)]) m₁
      (("st", stA, stA) :: π) =
      evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        ((("cur", .ptrVal root) ::
          ("top", .u64 (BitVec.ofNat 64 0)) ::
          ("st", .arr32 (List.replicate
            (BitVec.ofNat 64 bstInorderStackSize).toNat 0)) ::
          [("root", .ptrVal root), ("out", .ptrVal out),
            ("cap", .i32 cap)])) :=
    memEvalExpr_lit _ _ _ _
  have hNV : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      ((("cur", .ptrVal root) ::
        ("top", .u64 (BitVec.ofNat 64 0)) ::
        ("st", .arr32 (List.replicate
          (BitVec.ofNat 64 bstInorderStackSize).toNat 0)) ::
        [("root", .ptrVal root), ("out", .ptrVal out),
          ("cap", .i32 cap)])) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  have hN := memEvalStmtFuel_let_pure F "n" (.u 64)
    (.lit (.u64 (BitVec.ofNat 64 0))) _ _ _
    (.u64 (BitVec.ofNat 64 0))
    (by simp) (by simp) (by simp) (by simp) hNM hNV
  have hCapVM : memEvalExpr (.var "cap")
      (("n", .u64 (BitVec.ofNat 64 0)) ::
        ("cur", .ptrVal root) ::
        ("top", .u64 (BitVec.ofNat 64 0)) ::
        ("st", .arr32 (List.replicate
          (BitVec.ofNat 64 bstInorderStackSize).toNat 0)) ::
        [("root", .ptrVal root), ("out", .ptrVal out),
          ("cap", .i32 cap)]) m₁
      (("st", stA, stA) :: π) =
      evalExpr (.var "cap")
        ((("n", .u64 (BitVec.ofNat 64 0)) ::
          ("cur", .ptrVal root) ::
          ("top", .u64 (BitVec.ofNat 64 0)) ::
          ("st", .arr32 (List.replicate
            (BitVec.ofNat 64 bstInorderStackSize).toNat 0)) ::
          [("root", .ptrVal root), ("out", .ptrVal out),
            ("cap", .i32 cap)])) :=
    memEvalExpr_var _ _ _ _
  have hCapVV : evalExpr (.var "cap")
      ((("n", .u64 (BitVec.ofNat 64 0)) ::
        ("cur", .ptrVal root) ::
        ("top", .u64 (BitVec.ofNat 64 0)) ::
        ("st", .arr32 (List.replicate
          (BitVec.ofNat 64 bstInorderStackSize).toNat 0)) ::
        [("root", .ptrVal root), ("out", .ptrVal out),
          ("cap", .i32 cap)])) =
      .ok (.i32 cap) := by
    simp [evalExpr, envLookup]
  have hCapUM := memEvalExpr_u64ofI32_agree _ _ _ _ hCapVM
  have hCapUV : evalExpr (.u64ofI32 (.var "cap"))
      ((("n", .u64 (BitVec.ofNat 64 0)) ::
        ("cur", .ptrVal root) ::
        ("top", .u64 (BitVec.ofNat 64 0)) ::
        ("st", .arr32 (List.replicate
          (BitVec.ofNat 64 bstInorderStackSize).toNat 0)) ::
        [("root", .ptrVal root), ("out", .ptrVal out),
          ("cap", .i32 cap)])) =
      .ok (.u64 (cap.signExtend 64)) :=
    evalExpr_u64ofI32_ok _ _ _ hCapVV
  have hCapU := memEvalStmtFuel_let_pure F "capU" (.u 64)
    (.u64ofI32 (.var "cap")) _ _ _
    (.u64 (cap.signExtend 64))
    (by simp) (by simp) (by simp) (by simp) hCapUM hCapUV
  -- Initial invariant: empty stack, no keys emitted, full tree ahead.
  have hfindSt₁ : memFind m₁ stA =
      some ⟨stA, true, List.replicate 64 0⟩ := by
    have h := memFind_alloc_hit m
      (List.replicate (BitVec.ofNat 64 bstInorderStackSize).toNat 0)
    rw [← hm₁, ← hstA, hn64] at h
    exact h
  have hmemCur₁ : ∀ c, root = some c → TreeSegMem (m := m₁) root c :=
    fun c hc => TreeSegMem_head hseg₁ hc
  have hstack₁ : StackMirror m₁ stA stA [] := by
    refine ⟨_, hfindSt₁, ?_, ?_⟩
    · simp [bstInorderStackSize]
    · simp
  have hout₁ : OutPrefix m₁ outA outT [] := by
    have hfindEq : memFind m₁ outA = memFind m outA := by
      have h := memFind_memAllocData_other m
        (List.replicate (BitVec.ofNat 64 bstInorderStackSize).toNat 0)
        outA hneOutNext
      rw [← hm₁] at h
      exact h
    refine ⟨outData, ?_, ?_⟩
    · rw [hfindEq]
      exact hout
    · simp
  have hneSt₁ : ∀ b, TreeSegMem (m := m₁) root b → b ≠ stA := by
    intro b hb heq
    obtain ⟨tp, k, l, r, h3⟩ := TreeSegMem_nodeAt3 hb
    rw [heq] at h3
    unfold nodeAt3 cellsAt at h3
    rw [hfindSt₁] at h3
    have hX := Option.some.inj h3
    have hlenEq : List.replicate 64 (0 : BitVec 32) =
        [k, linkWord l, linkWord r] :=
      (Block.mk.inj hX).2.2
    have hL := congrArg List.length hlenEq
    simp at hL
  have houtLen₁ : ∀ data, memFind m₁ outA =
      some ⟨outT, true, data⟩ → data.length ≠ 3 := by
    intro data hd
    have hfindEq : memFind m₁ outA = memFind m outA := by
      have h := memFind_memAllocData_other m
        (List.replicate (BitVec.ofNat 64 bstInorderStackSize).toNat 0)
        outA hneOutNext
      rw [← hm₁] at h
      exact h
    rw [hfindEq] at hd
    have hdeq : data = outData := by
      have hX := Option.some.inj (hd.symm.trans hout)
      exact (Block.mk.inj hX).2.2
    rw [hdeq]
    exact houtLen
  have hneOut₁ : ∀ b, TreeSegMem (m := m₁) root b → b ≠ outA := by
    intro b hb heq
    obtain ⟨tp, k, l, r, h3⟩ := TreeSegMem_nodeAt3 hb
    rw [heq] at h3
    unfold nodeAt3 cellsAt at h3
    have hfindEq : memFind m₁ outA = memFind m outA := by
      have h := memFind_memAllocData_other m
        (List.replicate (BitVec.ofNat 64 bstInorderStackSize).toNat 0)
        outA hneOutNext
      rw [← hm₁] at h
      exact h
    rw [hfindEq, hout] at h3
    have hX := Option.some.inj h3
    have hlenEq : outData = [k, linkWord l, linkWord r] :=
      (Block.mk.inj hX).2.2
    have hL := congrArg List.length hlenEq
    simp only [List.length_cons, List.length_nil] at hL
    exact houtLen (by omega)
  have hstT₁ : stA = stA := rfl
  have hlay₁ : layoutLookup (("st", stA, stA) :: π) "st" =
      some (stA, stA) :=
    layoutLookup_hit _ _ _ _
  have hlayOut₁ : layoutLookup (("st", stA, stA) :: π) "out" =
      some (outA, outT) := by
    rw [layoutLookup_miss _ _ _ _ _ (by decide)]
    exact hlayOut₀
  have hbound₁ : (t.flatten.length - ([] : List (BitVec 32)).length) +
      2 ≤ F := by
    have hfl := BTree.length_flatten_eq_bsize t
    omega
  have hcapU₁ : (cap.signExtend 64).toNat =
      (cap.signExtend 64).toNat := rfl
  have hstListG : (List.replicate
        (BitVec.ofNat 64 bstInorderStackSize).toNat
        (0 : BitVec 32)).take ([] : List Addr).length =
      ([] : List Addr).map fun a => linkWord (some a) := by
    simp
  have hstLenG : (List.replicate
      (BitVec.ofNat 64 bstInorderStackSize).toNat
      (0 : BitVec 32)).length = bstInorderStackSize := by
    simp [List.length_replicate, hn64, bstInorderStackSize]
  have htopG : (BitVec.ofNat 64 0).toNat =
      ([] : List Addr).length := by
    simp
  have hnG : List.length ([] : List (BitVec 32)) =
      (BitVec.ofNat 64 0).toNat := by
    simp
  have heqG : ([] : List (BitVec 32)) ++
      drain (pushSpine t []) = t.flatten := by
    simp [drain_pushSpine_nil]
  have hmemFrG : ∀ a, a ∈ ([] : List Addr) →
      TreeSegMem (m := m₁) root a :=
    fun a h => absurd h (by simp)
  have hstNeOut₁ : stA ≠ outA := by
    rw [hstNext]
    exact Ne.symm hneOutNext
  have houtCap₁ : ∀ data, memFind m₁ outA =
      some ⟨outT, true, data⟩ →
      (cap.signExtend 64).toNat ≤ data.length := by
    intro data hd
    have hfindEq : memFind m₁ outA = memFind m outA := by
      have h := memFind_memAllocData_other m
        (List.replicate (BitVec.ofNat 64 bstInorderStackSize).toNat 0)
        outA hneOutNext
      rw [← hm₁] at h
      exact h
    rw [hfindEq] at hd
    have hdeq : data = outData := by
      have hX := Option.some.inj (hd.symm.trans hout)
      exact (Block.mk.inj hX).2.2
    rw [hdeq]
    exact hcapLen
  have hInv₁ : InorderInv m₁ root t stA stA outA outT cap
      (BitVec.ofNat 64 0) [] root t [] [] :=
    ⟨hseg₁, hseg₁, FramesOf.nil _, hstack₁,
      by simp [bstInorderStackSize], hout₁, hnG, heqG, hmemCur₁,
      hmemFrG, hneSt₁, hneOut₁, hstNeOut₁, houtLen₁, houtCap₁⟩
  have h64 : t.flatten.length < 2 ^ 64 := by
    have hle : (2 : Nat) ^ 32 < 2 ^ 64 := by decide
    omega
  have hOuter := bstInorderOuter_ok F m₁ (("st", stA, stA) :: π)
    hex₁ root t root t [] [] stA stA
    (List.replicate (BitVec.ofNat 64 bstInorderStackSize).toNat 0)
    (BitVec.ofNat 64 0) (BitVec.ofNat 64 0) (cap.signExtend 64) cap
    out outA outT []
    hInv₁ hstListG hstLenG htopG rfl hlay₁ hbound₁ rfl hlayOut₁ h64
  cases hOuter with
  | inl hFin =>
    obtain ⟨nCnt, m', ρ₅, stList'', top'', emitted',
      hbodyF, hfwdF, hρF, hInvF, hemF⟩ := hFin
    have hRetM : memEvalExpr (.var "n") ρ₅ m' (("st", stA, stA) :: π) =
        evalExpr (.var "n") ρ₅ :=
      memEvalExpr_var _ _ _ _
    have hRetV : evalExpr (.var "n") ρ₅ = .ok (.u64 nCnt) := by
      rw [hρF]
      exact evalExpr_var_hit _ _ _
        (by simp [envLookup, mkBstInorderEnv])
    have hRetM' := memEvalExpr_i32ofU64_agree _ _ _ _ hRetM
    have hRetV' : evalExpr (.i32ofU64 (.var "n")) ρ₅ =
        .ok (.i32 (BitVec.ofNat 32 nCnt.toNat)) :=
      evalExpr_i32ofU64_ok _ _ _ hRetV
    have hRet := memEvalStmtFuel_return F _ _ _ _ _ hRetM' hRetV'
    have hR5 := memEvalStmtFuel_seq F _ _ _ _ _ _ _ _ _ _ _ _
      hbodyF hRet
    have hR4 := memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _
      hCapU hR5
    have hR3 := memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _
      hN hR4
    have hR2 := memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _
      hCur hR3
    have hR1 := memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _
      hTop hR2
    have hBody := memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _
      hLetSt hR1
    have hnCnt : nCnt.toNat = emitted'.length := by
      have h := hInvF.hn
      rw [hemF] at *
      exact h.symm
    have hfin : emitted' = t.flatten := hemF
    have hBody' : memEvalStmtFuel F bstInorderFunc.body
        [("root", .ptrVal root), ("out", .ptrVal out),
          ("cap", .i32 cap)] m π =
        .ok ((ρ₅, m', (("st", stA, stA) :: π)),
          .returned (.i32 (BitVec.ofNat 32 nCnt.toNat))) :=
      hBody
    refine ⟨_, _, _, _, hBody', Or.inl ⟨emitted', ?_, hfin, ?_⟩⟩
    · obtain ⟨d, hd, ht⟩ := hInvF.hout
      exact ⟨d, hd, ht⟩
    · have hlen : emitted'.length = t.flatten.length := by
        rw [hfin]
      have hmod : nCnt.toNat % 2 ^ 32 = nCnt.toNat := by
        apply Nat.mod_eq_of_lt
        omega
      simp only [BitVec.toNat_ofNat] at hmod ⊢
      omega
  | inr hBail =>
    obtain ⟨ρb, mb, hbodyB, hfwdB⟩ := hBail
    have hR5B := memEvalStmtFuel_seq_returned_first F _
      (.return_ (.i32ofU64 (.var "n"))) _ _ _ _ _ _ _
      hbodyB
    have hR4B := memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _
      hCapU hR5B
    have hR3B := memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _
      hN hR4B
    have hR2B := memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _
      hCur hR3B
    have hR1B := memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _
      hTop hR2B
    have hBodyB := memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _
      hLetSt hR1B
    have hBodyB' : memEvalStmtFuel F bstInorderFunc.body
        [("root", .ptrVal root), ("out", .ptrVal out),
          ("cap", .i32 cap)] m π =
        .ok ((ρb, mb, (("st", stA, stA) :: π)),
          .returned
            (.i32 (BitVec.ofNat 32 (2 ^ 32 - 1)))) :=
      hBodyB
    refine ⟨_, _, _, _, hBodyB', Or.inr rfl⟩
