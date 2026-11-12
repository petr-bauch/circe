/-
Pillar-1 tree-kit goal: iterative BST insert with per-element
`malloc` (`bst_insert`): `Node* bst_insert(Node *root, int key)`
descends like `bst_search` (signed `<` picks the side), recording
the parent and the side taken; a duplicate key returns the old
root untouched (no allocation), otherwise a fresh 3-word node
(`key`, null, null) is attached at the empty child link and the
(old, or new-for-empty-tree) root returned. Write leg over the
read-only chase: one `nnew3`, one `psetVal`, one `psetNext`, one
`psetRight`, one attach store. Faults are loud as usual.
-/
import Circe.Emit.BstSearch
import Circe.Emit.ListCopy

/-- C name (unmangled: pure-C corpus entry). -/
def bstInsertName : String :=
  "bst_insert"

/-- Loop body: duplicate returns the old root early; otherwise
    swing the parent down, descend, and record the side taken. -/
def bstInsertLoopBody : CStmt :=
  (.if_ (.ueq (.pgetVal (.var "cur")) (.var "key"))
    (.return_ (.var "root"))
    (.if_ (.slt (.var "key") (.pgetVal (.var "cur")))
      (.seq (.assign "parent" (.var "cur"))
      (.seq (.assign "cur" (.pgetNext (.var "cur")))
            (.assign "went_left" (.lit (.i32 1)))))
      (.seq (.assign "parent" (.var "cur"))
      (.seq (.assign "cur" (.pgetRight (.var "cur")))
            (.assign "went_left" (.lit (.i32 0)))))))

/-- Loop `while (cur != nullptr) body` (the search guard). -/
def bstInsertLoop : CStmt :=
  (.while_ (.une (.var "cur") (.lit .nullptr)) bstInsertLoopBody)

/-- Attach: fresh 3-word node, init key/null/null, swing the
    recorded link (empty tree returns the fresh node). -/
def bstInsertAttach : CStmt :=
  (.seq (.let_ "nd" nodeTy .nnew3)
  (.seq (.psetVal (.var "nd") (.var "key"))
  (.seq (.psetNext (.var "nd") (.lit .nullptr))
  (.seq (.psetRight (.var "nd") (.lit .nullptr))
  (.if_ (.ueq (.var "parent") (.lit .nullptr))
    (.return_ (.var "nd"))
    (.if_ (.une (.var "went_left") (.lit (.i32 0)))
      (.psetNext (.var "parent") (.var "nd"))
      (.psetRight (.var "parent") (.var "nd"))))))))

/-- Whole function: seed parent/cur/side, chase, attach, return
    the old root. -/
def bstInsertBody : CStmt :=
  (.seq (.let_ "parent" nodeTy (.lit .nullptr))
  (.seq (.let_ "cur" nodeTy (.var "root"))
  (.seq (.let_ "went_left" (.i 32) (.lit (.i32 0)))
  (.seq bstInsertLoop
  (.seq bstInsertAttach
        (.return_ (.var "root")))))))

/-- The insert entry: `Node*` root + `i32` key in, (possibly new)
    `Node*` root out. -/
def bstInsertFunc : Func :=
  ⟨bstInsertName,
   [{ name := "root", ty := nodeTy, role := .owned },
    { name := "key", ty := (.i 32), role := .owned }],
   nodeTy,
   bstInsertBody⟩

/-- Insert environment: root/key slots, then the parent, cursor,
    and side-flag slots (the entry binds root/key first, then the
    three lets cons in order). -/
def mkBstInsertEnv (root : Option Addr) (key : BitVec 32)
    (parent cur : Option Addr) (wl : BitVec 32) : Env :=
  [("went_left", .i32 wl), ("cur", .ptrVal cur),
    ("parent", .ptrVal parent), ("root", .ptrVal root),
    ("key", .i32 key)]

theorem mkBstInsertEnv_root (root : Option Addr) (key : BitVec 32)
    (parent cur : Option Addr) (wl : BitVec 32) :
    envLookup (mkBstInsertEnv root key parent cur wl) "root" =
      some (.ptrVal root) := by
  simp [mkBstInsertEnv, envLookup]

theorem mkBstInsertEnv_key (root : Option Addr) (key : BitVec 32)
    (parent cur : Option Addr) (wl : BitVec 32) :
    envLookup (mkBstInsertEnv root key parent cur wl) "key" =
      some (.i32 key) := by
  simp [mkBstInsertEnv, envLookup]

theorem mkBstInsertEnv_parent (root : Option Addr) (key : BitVec 32)
    (parent cur : Option Addr) (wl : BitVec 32) :
    envLookup (mkBstInsertEnv root key parent cur wl) "parent" =
      some (.ptrVal parent) := by
  simp [mkBstInsertEnv, envLookup]

theorem mkBstInsertEnv_cur (root : Option Addr) (key : BitVec 32)
    (parent cur : Option Addr) (wl : BitVec 32) :
    envLookup (mkBstInsertEnv root key parent cur wl) "cur" =
      some (.ptrVal cur) := by
  simp [mkBstInsertEnv, envLookup]

theorem mkBstInsertEnv_wl (root : Option Addr) (key : BitVec 32)
    (parent cur : Option Addr) (wl : BitVec 32) :
    envLookup (mkBstInsertEnv root key parent cur wl) "went_left" =
      some (.i32 wl) := by
  simp [mkBstInsertEnv, envLookup]

/-! ## Forward mirror (descent with parent/side, then attach) -/

/-- Chase outcome: duplicate (no-op, old root kept) or the attach
    point (parent to swing, side taken to reach the hole). -/
inductive BstInsertRes
  | dup
  | attach (parent : Option Addr) (wentLeft : Bool)

/-- Descent recording parent and side: read-only (each visit
    reads the key at `[0]` and one link); a key match reports
    `dup` (the no-op path allocates nothing), exhaustion reports
    the attach point. Faults abort loudly at any fuel; each visit
    consumes fuel (the attach needs fuel too — no, the chase
    alone: exhaustion returns at any positive fuel on `none`). -/
def bstInsertChase (F : Nat) (m : Mem) (cur : Option Addr)
    (key : BitVec 32) (parent : Option Addr)
    (wentLeft : Bool) : Result BstInsertRes :=
  match cur with
  | none => .ok (.attach parent wentLeft)
  | some a =>
    match F with
    | 0 => .error .AssertFail
    | F + 1 =>
      match memFind m a with
      | none => .error .AssertFail
      | some b =>
        match memLoad m a b.tag 0 with
        | .error e => .error e
        | .ok w =>
          if w == key then .ok .dup
          else if key.slt w then
            match memLoad m a b.tag 1 with
            | .error e => .error e
            | .ok w' =>
              bstInsertChase F m (addrOfWord w') key (some a) true
          else
            match memLoad m a b.tag 2 with
            | .error e => .error e
            | .ok w' =>
              bstInsertChase F m (addrOfWord w') key (some a) false

/-- Entry mirror: chase, then duplicate keeps `(root, m)`
    untouched; attach allocates the 3-word node, inits
    key/null/null, and swings the recorded link (empty tree
    returns the fresh node). -/
def bstInsertFwd (F : Nat) (m : Mem) (root : Option Addr)
    (key : BitVec 32) : Result (Option Addr × Mem) :=
  match bstInsertChase F m root key none false with
  | .error e => .error e
  | .ok .dup => .ok (root, m)
  | .ok (.attach parent side) =>
    let (m1, a) := memAlloc m 3
    match memStore m1 a a 0 key with
    | .error e => .error e
    | .ok m2 =>
      match memStore m2 a a 1 (linkWord none) with
      | .error e => .error e
      | .ok m3 =>
        match memStore m3 a a 2 (linkWord none) with
        | .error e => .error e
        | .ok m4 =>
          match parent with
          | none => .ok (some a, m4)
          | some p =>
            match memFind m4 p with
            | none => .error .AssertFail
            | some b =>
              match memStore m4 p b.tag (if side then 1 else 2)
                  (linkWord (some a)) with
              | .error e => .error e
              | .ok m5 => .ok (root, m5)

/-- The chase succeeds on a fueled segment (faults ruled out by
    the segment hypotheses; exhaustion by node-count fuel; the
    parent/side passengers ride along untouched). -/
theorem bstInsertChase_ok (F : Nat) :
    ∀ (m : Mem)
      (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
      (key : BitVec 32) (cur : Option Addr)
      (t : BTree) (hseg : TreeSeg m cur t)
      (hlen : t.bsize ≤ F)
      (parent : Option Addr) (wentLeft : Bool),
    ∃ r, bstInsertChase F m cur key parent wentLeft = .ok r := by
  induction F with
  | zero =>
    intro m hex key cur t hseg hlen parent wentLeft
    cases hseg with
    | nil => exact ⟨.attach parent wentLeft, by simp [bstInsertChase]⟩
    | cons hnode _ _ =>
      simp only [BTree.bsize] at hlen
      omega
  | succ F ih =>
    intro m hex key cur t hseg hlen parent wentLeft
    cases hseg with
    | nil => exact ⟨.attach parent wentLeft, by simp [bstInsertChase]⟩
    | @cons a tg k l r tl tr hnode hl hr =>
      have hfb : memFind m a = some _ := hnode
      have hmem0 : memLoad m a tg 0 = .ok k := nodeLoadKey hnode
      have hmem1 : memLoad m a tg 1 = .ok (linkWord l) :=
        nodeLoadLeft hnode
      have hmem2 : memLoad m a tg 2 = .ok (linkWord r) :=
        nodeLoadRight hnode
      have hlenL : tl.bsize ≤ F := by
        simp only [BTree.bsize] at hlen
        omega
      have hlenR : tr.bsize ≤ F := by
        simp only [BTree.bsize] at hlen
        omega
      by_cases heq : (k == key) = true
      · exact ⟨.dup, by
          unfold bstInsertChase
          simp only [hfb, hmem0, ite_eq_left heq]⟩
      · have hallocL : ∀ c', l = some c' →
            (memFind m c').isSome = true := by
          intro c' hc'
          cases hnxt : l with
          | none => rw [hnxt] at hc'; cases hc'
          | some c'' =>
            cases hc'
            exact TreeSeg_head_alloc hl
        have hdecL := nodeAt3_link_roundtrip hex hallocL
        have hl' : TreeSeg m (addrOfWord (linkWord l)) tl := by
          rw [hdecL]; exact hl
        have hallocR : ∀ c', r = some c' →
            (memFind m c').isSome = true := by
          intro c' hc'
          cases hnxt : r with
          | none => rw [hnxt] at hc'; cases hc'
          | some c'' =>
            cases hc'
            exact TreeSeg_head_alloc hr
        have hdecR := nodeAt3_link_roundtrip hex hallocR
        have hr' : TreeSeg m (addrOfWord (linkWord r)) tr := by
          rw [hdecR]; exact hr
        by_cases hslt : (key.slt k) = true
        · obtain ⟨rL, hC'⟩ :=
            ih m hex key (addrOfWord (linkWord l)) tl hl' hlenL
              (some a) true
          exact ⟨rL, by
            unfold bstInsertChase
            simp only [hfb, hmem0, hmem1, ite_eq_right heq,
              ite_eq_left hslt, hC']⟩
        · obtain ⟨rR, hC'⟩ :=
            ih m hex key (addrOfWord (linkWord r)) tr hr' hlenR
              (some a) false
          have hnslt : ¬((key.slt k) = true) := hslt
          exact ⟨rR, by
            unfold bstInsertChase
            simp only [hfb, hmem0, hmem2, ite_eq_right heq,
              ite_eq_right hnslt, hC']⟩

/-! ## Memory surgery (allocation framing + attach) -/

/-- A node survives allocation elsewhere (the fresh binding sits
    at the head, so a different address skips it). -/
theorem nodeAt3_alloc_other {m : Mem} {a t : Nat}
    {k : BitVec 32} {l r : Option Addr}
    (h : nodeAt3 m a t k l r) (d : List (BitVec 32))
    (hne : a ≠ m.next) :
    nodeAt3 (memAllocData m d).1 a t k l r := by
  unfold nodeAt3 cellsAt at h ⊢
  rw [memFind_memAllocData_other m d a hne]
  exact h

/-- The fresh 3-word block, after the three init stores, is a
    leaf node holding the key (tag = its own address, both links
    null). -/
theorem freshLeaf_init (m : Mem) (key : BitVec 32)
    (m1 : Mem) (a : Addr) (halloc : (m1, a) = memAlloc m 3)
    (m2 m3 m4 : Mem)
    (h0 : memStore m1 a a 0 key = .ok m2)
    (h1 : memStore m2 a a 1 (linkWord none) = .ok m3)
    (h2 : memStore m3 a a 2 (linkWord none) = .ok m4) :
    nodeAt3 m4 a a key none none := by
  have hrep : List.replicate 3 (0 : BitVec 32) = [0, 0, 0] := rfl
  have hfind : memFind m1 a = some ⟨a, true, [0, 0, 0]⟩ := by
    have h := memFind_memAlloc m 3
    rw [← halloc] at h
    simp only [hrep] at h
    have ha : (memAlloc m 3).2 = m.next := memAlloc_next m 3
    have ham : a = m.next := by rw [← ha]; exact congrArg Prod.snd halloc
    rw [ham] at h ⊢
    have h1eq : m1 = (memAlloc m 3).1 := congrArg Prod.fst halloc
    rw [h1eq] at h ⊢
    exact h
  have c0 : cellsAt m1 a a [0, 0, 0] := hfind
  have c1 := memFind_cellsAt_store m1 a a 0 [0, 0, 0] key m2
    c0 (by simp) h0
  have e0 : ([0, 0, 0].set 0 key) = [key, 0, 0] := by simp
  rw [e0] at c1
  have c2 := memFind_cellsAt_store m2 a a 1 [key, 0, 0]
    (linkWord none) m3 c1 (by simp) h1
  have e1 : ([key, (0 : BitVec 32), 0].set 1 (linkWord none)) =
      [key, 0, 0] := by simp [linkWord_none]
  rw [e1] at c2
  have c3 := memFind_cellsAt_store m3 a a 2 [key, 0, 0]
    (linkWord none) m4 c2 (by simp) h2
  have e2 : ([key, (0 : BitVec 32), 0].set 2 (linkWord none)) =
      [key, 0, 0] := by simp [linkWord_none]
  rw [e2] at c3
  unfold nodeAt3
  have el : [key, linkWord none, linkWord none] = [key, 0, 0] := by
    simp [linkWord_none]
  rw [el]
  exact c3

/-- `==` on keys flips (the chase compares `k == key` while
    `binsert` compares `key == k`). -/
theorem beq_flip_false {x y : BitVec 32}
    (h : (x == y) = false) : (y == x) = false := by
  by_cases hkk : (y == x) = true
  · have hxy : y = x := beq_iff_eq.mp hkk
    subst hxy
    rw [beq_iff_eq.mpr rfl] at h
    cases h
  · cases h2 : (y == x) with
    | true => exact absurd h2 hkk
    | false => rfl

/-- Acyclicity for the insert framing: node addresses in the
    segment are pairwise distinct. A DAG heap would let the
    attach store corrupt an off-path subtree sharing the attach
    node, making the post-state segment false; the C contract
    rules cycles out, and this is the formal pin. Indexed by the
    segment proof itself (not just the endpoints), so casing on
    both pins the same links — a separately-indexed statement
    would leave the two link sets disconnected. -/
inductive SegDistinct (m : Mem) : (s : Option Addr) → (t : BTree) →
    TreeSeg m s t → Prop
  | nil : SegDistinct m none .leaf .nil
  | cons {a t k l r tl tr} {hnode : nodeAt3 m a t k l r}
      {hl : TreeSeg m l tl} {hr : TreeSeg m r tr}
      (dL : SegDistinct m l tl hl) (dR : SegDistinct m r tr hr)
      (hnl : ∀ b, TreeSegMem (m := m) l b → b ≠ a)
      (hnr : ∀ b, TreeSegMem (m := m) r b → b ≠ a)
      (hdisj : ∀ b, TreeSegMem (m := m) l b →
        ∀ c, TreeSegMem (m := m) r c → b ≠ c) :
      SegDistinct m (some a) (.node k tl tr) (.cons hnode hl hr)

/-- The chase attach point is the last-visited node or a node of
    the current footprint: every `At` parent is either the
    incoming parent or a visited (hence in-segment) address.
    Induction on fuel, stepping through links with the roundtrip
    (needs the exactness bound, as in the chase). -/
theorem bstInsertChase_at_mem (F : Nat) (m : Mem)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (cur : Option Addr) (key : BitVec 32)
    (par : Option Addr) (side : Bool)
    (pp : Option Addr) (s : Bool) (t : BTree)
    (hC : bstInsertChase F m cur key par side = .ok (.attach pp s))
    (hseg : TreeSeg m cur t) :
    par = pp ∨ (∃ a, pp = some a ∧ TreeSegMem (m := m) cur a) := by
  induction F generalizing cur par side t hseg with
  | zero =>
    cases hseg with
    | nil =>
      simp only [bstInsertChase] at hC
      simp only [Except.ok.injEq, BstInsertRes.attach.injEq] at hC
      obtain ⟨hpar, -⟩ := hC
      exact Or.inl hpar
    | cons hnode _ _ =>
      cases hC
  | succ F ih =>
    cases hseg with
    | nil =>
      simp only [bstInsertChase] at hC
      simp only [Except.ok.injEq, BstInsertRes.attach.injEq] at hC
      obtain ⟨hpar, -⟩ := hC
      exact Or.inl hpar
    | @cons a tg k l r tl tr hnode hl hr =>
      have hfb : memFind m a = some _ := hnode
      have hmem0 : memLoad m a tg 0 = .ok k := nodeLoadKey hnode
      have hmem1 : memLoad m a tg 1 = .ok (linkWord l) :=
        nodeLoadLeft hnode
      have hmem2 : memLoad m a tg 2 = .ok (linkWord r) :=
        nodeLoadRight hnode
      have hallocL : ∀ c', l = some c' →
          (memFind m c').isSome = true := by
        intro c' hc'
        cases hnxt : l with
        | none => rw [hnxt] at hc'; cases hc'
        | some c'' =>
          cases hc'
          exact TreeSeg_head_alloc hl
      have hdecL := nodeAt3_link_roundtrip hex hallocL
      have hl' : TreeSeg m (addrOfWord (linkWord l)) tl := by
        rw [hdecL]; exact hl
      have hallocR : ∀ c', r = some c' →
          (memFind m c').isSome = true := by
        intro c' hc'
        cases hnxt : r with
        | none => rw [hnxt] at hc'; cases hc'
        | some c'' =>
          cases hc'
          exact TreeSeg_head_alloc hr
      have hdecR := nodeAt3_link_roundtrip hex hallocR
      have hr' : TreeSeg m (addrOfWord (linkWord r)) tr := by
        rw [hdecR]; exact hr
      unfold bstInsertChase at hC
      simp only [hfb, hmem0] at hC
      by_cases heq : (k == key) = true
      · rw [ite_eq_left heq] at hC
        cases hC
      · rw [ite_eq_right heq] at hC
        by_cases hslt : (key.slt k) = true
        · simp only [hmem1, ite_eq_left hslt] at hC
          have hsub := ih (cur := addrOfWord (linkWord l))
            (par := some a) (side := true) (t := tl)
            (hseg := hl') (hC := hC)
          rcases hsub with hsub | ⟨a', hpa', hmem⟩
          · exact Or.inr ⟨a, hsub.symm, .here hnode⟩
          · have hsub' : TreeSegMem (m := m) l a' := by
              rw [hdecL] at hmem; exact hmem
            exact Or.inr ⟨a', hpa', .left hnode hsub'⟩
        · have hnslt : ¬((key.slt k) = true) := hslt
          simp only [hmem2, ite_eq_right hnslt] at hC
          have hsub := ih (cur := addrOfWord (linkWord r))
            (par := some a) (side := false) (t := tr)
            (hseg := hr') (hC := hC)
          rcases hsub with hsub | ⟨a', hpa', hmem⟩
          · exact Or.inr ⟨a, hsub.symm, .here hnode⟩
          · have hsub' : TreeSegMem (m := m) r a' := by
              rw [hdecR] at hmem; exact hmem
            exact Or.inr ⟨a', hpa', .right hnode hsub'⟩

/-- A pre-node survives allocation plus the three fresh-node
    init stores (all at the fresh address, which differs by
    `hmfresh` + allocatedness). -/
theorem node_to_m4 {m : Mem} {q tq : Nat}
    {kq : BitVec 32} {lq rq : Option Addr}
    (hq : nodeAt3 m q tq kq lq rq)
    (m1 m2 m3 m4 : Mem) (a : Addr)
    (halloc : (m1, a) = memAlloc m 3)
    (hmfresh : memFind m m.next = none)
    (ha : a = m.next)
    (x0 x1 x2 : BitVec 32)
    (h0 : memStore m1 a a 0 x0 = .ok m2)
    (h1 : memStore m2 a a 1 x1 = .ok m3)
    (h2 : memStore m3 a a 2 x2 = .ok m4) :
    nodeAt3 m4 q tq kq lq rq := by
  have hfindq : memFind m q = some _ := hq
  have hqfresh : q ≠ m.next := by
    intro hcon
    rw [hcon] at hfindq
    rw [hmfresh] at hfindq
    cases hfindq
  have hq_a : q ≠ a := by rw [ha]; exact hqfresh
  have e1 : (memAllocData m (List.replicate 3 0)).1 = m1 := by
    have h := congrArg Prod.fst halloc
    simpa [memAlloc] using h.symm
  have n1 : nodeAt3 m1 q tq kq lq rq := by
    rw [← e1]
    exact nodeAt3_alloc_other hq (List.replicate 3 0) hqfresh
  have n2 : nodeAt3 m2 q tq kq lq rq := by
    unfold nodeAt3 cellsAt at n1 ⊢
    rw [memFind_memStore_other m1 m2 a q a 0 x0 h0 hq_a]
    exact n1
  have n3 : nodeAt3 m3 q tq kq lq rq := by
    unfold nodeAt3 cellsAt at n2 ⊢
    rw [memFind_memStore_other m2 m3 a q a 1 x1 h1 hq_a]
    exact n2
  have n4 : nodeAt3 m4 q tq kq lq rq := by
    unfold nodeAt3 cellsAt at n3 ⊢
    rw [memFind_memStore_other m3 m4 a q a 2 x2 h2 hq_a]
    exact n3
  exact n4

/-- A pre-node away from the attach target survives the whole
    attach sequence (the step above plus the attach store). -/
theorem nodePost {m : Mem} {q tq : Nat}
    {kq : BitVec 32} {lq rq : Option Addr}
    (hq : nodeAt3 m q tq kq lq rq)
    (m1 m2 m3 m4 m5 : Mem) (a pp : Addr)
    (halloc : (m1, a) = memAlloc m 3)
    (hmfresh : memFind m m.next = none)
    (ha : a = m.next)
    (hne_pp : q ≠ pp)
    (x0 x1 x2 : BitVec 32)
    (h0 : memStore m1 a a 0 x0 = .ok m2)
    (h1 : memStore m2 a a 1 x1 = .ok m3)
    (h2 : memStore m3 a a 2 x2 = .ok m4)
    (tA idxA : Nat) (xA : BitVec 32)
    (hA : memStore m4 pp tA idxA xA = .ok m5) :
    nodeAt3 m5 q tq kq lq rq := by
  have n4 := node_to_m4 hq m1 m2 m3 m4 a halloc hmfresh ha
    x0 x1 x2 h0 h1 h2
  unfold nodeAt3 cellsAt at n4 ⊢
  rw [memFind_memStore_other m4 m5 pp q tA idxA xA hA hne_pp]
  exact n4

/-- A segment away from the attach target survives the whole
    attach sequence (the frame leg for off-path subtrees: every
    member differs from the fresh address by `hmfresh`, from the
    attach target by hypothesis). -/
theorem TreeSeg_surgery_preserved {m : Mem} {s : Option Addr}
    {t' : BTree} (h : TreeSeg m s t')
    (m1 m2 m3 m4 m5 : Mem) (a pp : Addr)
    (halloc : (m1, a) = memAlloc m 3)
    (hmfresh : memFind m m.next = none)
    (ha : a = m.next)
    (x0 x1 x2 : BitVec 32)
    (h0 : memStore m1 a a 0 x0 = .ok m2)
    (h1 : memStore m2 a a 1 x1 = .ok m3)
    (h2 : memStore m3 a a 2 x2 = .ok m4)
    (tA idxA : Nat) (xA : BitVec 32)
    (hA : memStore m4 pp tA idxA xA = .ok m5)
    (hout_pp : ∀ c, TreeSegMem (m := m) s c → c ≠ pp) :
    TreeSeg m5 s t' := by
  revert hout_pp
  induction h with
  | nil =>
    intro _
    exact .nil
  | cons hnode _ _ ihl ihr =>
    intro hout_pp
    apply TreeSeg.cons
    · exact nodePost hnode m1 m2 m3 m4 m5 a pp halloc
        hmfresh ha (hout_pp _ (.here hnode))
        x0 x1 x2 h0 h1 h2 tA idxA xA hA
    · exact ihl (fun b hb => hout_pp b (.left hnode hb))
    · exact ihr (fun b hb => hout_pp b (.right hnode hb))

/-! ## Post-state assembly (the attach adds exactly one leaf) -/

/-- The stopped chase saw a null link: a sub-chase returning to
    its incoming parent visited nothing, so the link it stepped
    through is null (the attach hole). Induction on fuel with a
    visit step; the deeper chase either stops at the visited
    node (a revisit, ruled out by distinctness) or below it
    (transported back up into the footprint). -/
theorem chase_stop_null {m : Mem} {l : Option Addr} {tl : BTree}
    {a₀ : Addr} {key : BitVec 32} {F' : Nat} {s : Bool} {wl0 : Bool}
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (hl : TreeSeg m l tl)
    (hsubC : bstInsertChase F' m (addrOfWord (linkWord l)) key (some a₀)
      wl0 = .ok (.attach (some a₀) s))
    (hdisj : ∀ b, TreeSegMem (m := m) l b → b ≠ a₀)
    (hlen : tl.bsize ≤ F') :
    l = none := by
  cases hll : l with
  | none => rfl
  | some c =>
    rw [hll] at hsubC hl
    have hcc : addrOfWord (linkWord (some c)) = some c := by
      have hcA : (memFind m c).isSome = true :=
        TreeSeg_head_alloc hl
      exact addrOfWord_linkWord_some (hex c hcA)
    rw [hcc] at hsubC
    cases F' with
    | zero =>
      simp only [bstInsertChase] at hsubC
      cases hsubC
    | succ F'' =>
      cases hl with
      | @cons _ t_c k2 l2 r2 tl2 tr2 hnode_c hlc hrc =>
      have hfb_c : memFind m c = some _ := hnode_c
      have hmem0_c : memLoad m c t_c 0 = .ok k2 :=
        nodeLoadKey hnode_c
      unfold bstInsertChase at hsubC
      simp only [hfb_c, hmem0_c] at hsubC
      by_cases heq_c : (k2 == key) = true
      · rw [ite_eq_left heq_c] at hsubC
        cases hsubC
      · rw [ite_eq_right heq_c] at hsubC
        have hlen2 : (BTree.node k2 tl2 tr2).bsize ≤ F'' + 1 := hlen
        by_cases hslt_c : (key.slt k2) = true
        · have hmem1_c : memLoad m c t_c 1 =
            .ok (linkWord l2) := nodeLoadLeft hnode_c
          have hallocL2 : ∀ c', l2 = some c' →
              (memFind m c').isSome = true := by
            intro c' hc'
            cases hnxt : l2 with
            | none => rw [hnxt] at hc'; cases hc'
            | some c'' =>
              cases hc'
              exact TreeSeg_head_alloc hlc
          have hdecL2 := nodeAt3_link_roundtrip hex hallocL2
          have hl2' : TreeSeg m (addrOfWord (linkWord l2)) tl2 := by
            rw [hdecL2]; exact hlc
          have hlenL2 : tl2.bsize ≤ F'' := by
            simp only [BTree.bsize] at hlen2
            omega
          simp only [hmem1_c, ite_eq_left hslt_c] at hsubC
          have hsub2 := bstInsertChase_at_mem F'' m hex
            (addrOfWord (linkWord l2)) key (some c) true (some a₀) s
            tl2 hsubC hl2'
          rcases hsub2 with hsub2 | ⟨a', hpa', hmem⟩
          · have hca : c = a₀ := Option.some_inj.mp hsub2
            exact absurd rfl
              (hdisj _ (by rw [hll, ← hca]; exact .here hnode_c))
          · have h2 : a' = a₀ := Option.some_inj.mp hpa'.symm
            rw [hdecL2] at hmem
            rw [h2] at hmem
            have hup : TreeSegMem (m := m) (some c) a₀ :=
              .left hnode_c hmem
            exact absurd rfl (hdisj _ (by rw [hll]; exact hup))
        · have hnslt_c : ¬((key.slt k2) = true) := hslt_c
          have hmem2_c : memLoad m c t_c 2 =
              .ok (linkWord r2) := nodeLoadRight hnode_c
          have hallocR2 : ∀ c', r2 = some c' →
              (memFind m c').isSome = true := by
            intro c' hc'
            cases hnxt : r2 with
            | none => rw [hnxt] at hc'; cases hc'
            | some c'' =>
              cases hc'
              exact TreeSeg_head_alloc hrc
          have hdecR2 := nodeAt3_link_roundtrip hex hallocR2
          have hr2' : TreeSeg m (addrOfWord (linkWord r2)) tr2 := by
            rw [hdecR2]; exact hrc
          have hlenR2 : tr2.bsize ≤ F'' := by
            simp only [BTree.bsize] at hlen2
            omega
          simp only [hmem2_c, ite_eq_right hnslt_c] at hsubC
          have hsub2 := bstInsertChase_at_mem F'' m hex
            (addrOfWord (linkWord r2)) key (some c) false (some a₀) s
            tr2 hsubC hr2'
          rcases hsub2 with hsub2 | ⟨a', hpa', hmem⟩
          · have hca : c = a₀ := Option.some_inj.mp hsub2
            exact absurd rfl
              (hdisj _ (by rw [hll, ← hca]; exact .here hnode_c))
          · have h2 : a' = a₀ := Option.some_inj.mp hpa'.symm
            rw [hdecR2] at hmem
            rw [h2] at hmem
            have hup : TreeSegMem (m := m) (some c) a₀ :=
              .right hnode_c hmem
            exact absurd rfl (hdisj _ (by rw [hll]; exact hup))

/-- Post-state assembly: after alloc + init + attach, the root
    holds the functional insertion. Induction on the tree with
    chase steering (the chase outcome says where the attach
    went): on-path nodes recurse, off-path subtrees frame over
    the surgery (distinctness rules out sharing the attach
    node), and the attach level links the fresh leaf. -/
theorem bstInsertAttach_seg (F : Nat) (m : Mem)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (hmfresh : memFind m m.next = none)
    (root : Option Addr) (key : BitVec 32) (t : BTree)
    (lo hi : Option (BitVec 32))
    (hbst : Bst lo hi t) (hseg : TreeSeg m root t)
    (hd : SegDistinct m root t hseg)
    (hlen : t.bsize ≤ F)
    (p : Addr) (s : Bool)
    (par : Option Addr) (side : Bool)
    (hC : bstInsertChase F m root key par side = .ok (.attach (some p) s))
    (hmem : TreeSegMem (m := m) root p)
    (m1 m2 m3 m4 m5 : Mem) (a : Addr)
    (ha : a = m.next)
    (halloc : (m1, a) = memAlloc m 3)
    (h0 : memStore m1 a a 0 key = .ok m2)
    (h1 : memStore m2 a a 1 (linkWord none) = .ok m3)
    (h2 : memStore m3 a a 2 (linkWord none) = .ok m4)
    (b : Block) (hfind4 : memFind m4 p = some b)
    (idxA : Nat) (xA : BitVec 32)
    (hA : memStore m4 p b.tag idxA xA = .ok m5)
    (hidx : idxA = (if s then 1 else 2))
    (hxA : xA = linkWord (some a)) :
    TreeSeg m5 root (BTree.binsert t key) := by
  induction hd generalizing F lo hi par side with
  | nil =>
    cases hmem
  | @cons a₀ t₀ k l r tl tr hnode hl hr hdL hdR hnl hnr hdisj ihl ihr =>
    have hloB : boundLo lo k := by
      cases hbst with
      | node h _ _ _ => exact h
    have hhiB : boundHi k hi := by
      cases hbst with
      | node _ h _ _ => exact h
    have hlB : Bst lo (some k) tl := by
      cases hbst with
      | node _ _ h _ => exact h
    have hrB : Bst (some k) hi tr := by
      cases hbst with
      | node _ _ _ h => exact h
    have hfb : memFind m a₀ = some _ := hnode
    have hmem0 : memLoad m a₀ t₀ 0 = .ok k := nodeLoadKey hnode
    cases F with
    | zero =>
      simp only [bstInsertChase] at hC
      cases hC
    | succ F' =>
      simp only [BTree.bsize] at hlen
      unfold bstInsertChase at hC
      simp only [hfb, hmem0] at hC
      by_cases heq : (k == key) = true
      · rw [ite_eq_left heq] at hC
        cases hC
      · have heqF : (k == key) = false := by
          cases h : (k == key) with
          | true => exact absurd h heq
          | false => rfl
        have heqk : (key == k) = false := beq_flip_false heqF
        rw [ite_eq_right heq] at hC
        by_cases hslt : (key.slt k) = true
        · have hmem1 : memLoad m a₀ t₀ 1 = .ok (linkWord l) :=
            nodeLoadLeft hnode
          have hallocL : ∀ c', l = some c' →
              (memFind m c').isSome = true := by
            intro c' hc'
            cases hnxt : l with
            | none => rw [hnxt] at hc'; cases hc'
            | some c'' =>
              cases hc'
              exact TreeSeg_head_alloc hl
          have hdecL := nodeAt3_link_roundtrip hex hallocL
          have hlenL : tl.bsize ≤ F' := by omega
          simp only [hmem1, ite_eq_left hslt] at hC
          have hsubC := hC
          have hpath := bstInsertChase_at_mem F' m hex
            (addrOfWord (linkWord l)) key (some a₀) true (some p) s
            tl hsubC (by rw [hdecL]; exact hl)
          rcases hpath with hpath | hpath
          · have hpa : p = a₀ := Option.some_inj.mp hpath.symm
            subst p
            have hlnone : l = none :=
              chase_stop_null hex hl hsubC hnl hlenL
            by_cases hs0 : s = true
            · have htlleaf : tl = .leaf := by
                rw [hlnone] at hl
                cases hl
                rfl
              have hnode4 := node_to_m4 hnode m1 m2 m3 m4 a halloc
                hmfresh ha key (linkWord none) (linkWord none)
                h0 h1 h2
              have hfind4' : memFind m4 a₀ = some _ := hnode4
              have htag0 : b.tag = t₀ := by
                rw [hfind4'] at hfind4
                simp only [Option.some.injEq] at hfind4
                exact congrArg Block.tag hfind4.symm
              simp only [htag0, hidx, hxA, hs0, ite_true] at hA
              have hnode5 := nodeStoreLeft_nodeAt3 hnode4 hA
              have hfresh := freshLeaf_init m key m1 a halloc m2 m3 m4
                h0 h1 h2
              have hne_af : a ≠ a₀ := by
                rw [ha]
                intro hcon
                have hfind0 : memFind m a₀ = some _ := hnode
                rw [← hcon] at hfind0
                rw [hmfresh] at hfind0
                cases hfind0
              have hfresh5 : nodeAt3 m5 a a key none none := by
                unfold nodeAt3 cellsAt at hfresh ⊢
                rw [memFind_memStore_other m4 m5 a₀ a _ _ _ hA hne_af]
                exact hfresh
              have hleafSeg : TreeSeg m5 (some a)
                  (BTree.node key .leaf .leaf) :=
                .cons hfresh5 .nil .nil
              have hpresR : TreeSeg m5 r tr :=
                TreeSeg_surgery_preserved hr m1 m2 m3 m4 m5 a a₀ halloc
                  hmfresh ha key (linkWord none) (linkWord none)
                  h0 h1 h2 _ _ _ hA hnr
              simp only [BTree.binsert, heqk, hslt, htlleaf, ite_true]
              exact TreeSeg.cons hnode5 hleafSeg hpresR
            · rw [hlnone, addrOfWord_linkWord_none] at hsubC
              simp only [bstInsertChase] at hsubC
              simp only [Except.ok.injEq, BstInsertRes.attach.injEq] at hsubC
              obtain ⟨-, hs⟩ := hsubC
              exact absurd hs.symm hs0
          · obtain ⟨a', hpa', hmem⟩ := hpath
            have hpa2 : a' = p := Option.some_inj.mp hpa'.symm
            rw [hdecL] at hmem
            rw [hpa2] at hmem
            have hmemT : TreeSegMem (m := m) l p := hmem
            rw [hdecL] at hsubC
            have hIHL : TreeSeg m5 l (BTree.binsert tl key) :=
              ihl (F := F') (lo := lo) (hi := some k) (par := some a₀)
                (side := true) (hbst := hlB) (hlen := hlenL)
                (hC := hsubC) (hmem := hmemT)
            have hpresR : TreeSeg m5 r tr :=
              TreeSeg_surgery_preserved hr m1 m2 m3 m4 m5 a p halloc
                hmfresh ha key (linkWord none) (linkWord none)
                h0 h1 h2 _ _ _ hA
                (fun c hc hcon => by
                  subst hcon
                  exact absurd rfl (hdisj _ hmemT _ hc))
            have hne_a : a₀ ≠ p := by
              intro hcon
              have hm : TreeSegMem (m := m) l a₀ := by
                rw [hcon]; exact hmemT
              exact absurd rfl (hnl _ hm)
            have hnode5 := nodePost hnode m1 m2 m3 m4 m5 a p halloc
              hmfresh ha hne_a key (linkWord none) (linkWord none)
              h0 h1 h2 _ _ _ hA
            simp only [BTree.binsert, heqk, hslt, ite_true]
            exact TreeSeg.cons hnode5 hIHL hpresR
        · have hnslt : ¬((key.slt k) = true) := hslt
          have hmem2 : memLoad m a₀ t₀ 2 = .ok (linkWord r) :=
            nodeLoadRight hnode
          have hallocR : ∀ c', r = some c' →
              (memFind m c').isSome = true := by
            intro c' hc'
            cases hnxt : r with
            | none => rw [hnxt] at hc'; cases hc'
            | some c'' =>
              cases hc'
              exact TreeSeg_head_alloc hr
          have hdecR := nodeAt3_link_roundtrip hex hallocR
          have hlenR : tr.bsize ≤ F' := by omega
          simp only [hmem2, ite_eq_right hnslt] at hC
          have hsubC := hC
          have hpath := bstInsertChase_at_mem F' m hex
            (addrOfWord (linkWord r)) key (some a₀) false (some p) s
            tr hsubC (by rw [hdecR]; exact hr)
          rcases hpath with hpath | hpath
          · have hpa : p = a₀ := Option.some_inj.mp hpath.symm
            subst p
            have hrnone : r = none :=
              chase_stop_null hex hr hsubC hnr hlenR
            by_cases hs0 : s = false
            · have htrleaf : tr = .leaf := by
                rw [hrnone] at hr
                cases hr
                rfl
              have hnode4 := node_to_m4 hnode m1 m2 m3 m4 a halloc
                hmfresh ha key (linkWord none) (linkWord none)
                h0 h1 h2
              have hfind4' : memFind m4 a₀ = some _ := hnode4
              have htag0 : b.tag = t₀ := by
                rw [hfind4'] at hfind4
                simp only [Option.some.injEq] at hfind4
                exact congrArg Block.tag hfind4.symm
              simp only [htag0, hidx, hxA, hs0] at hA
              have hnode5 := nodeStoreRight_nodeAt3 hnode4 hA
              have hfresh := freshLeaf_init m key m1 a halloc m2 m3 m4
                h0 h1 h2
              have hne_af : a ≠ a₀ := by
                rw [ha]
                intro hcon
                have hfind0 : memFind m a₀ = some _ := hnode
                rw [← hcon] at hfind0
                rw [hmfresh] at hfind0
                cases hfind0
              have hfresh5 : nodeAt3 m5 a a key none none := by
                unfold nodeAt3 cellsAt at hfresh ⊢
                rw [memFind_memStore_other m4 m5 a₀ a _ _ _ hA hne_af]
                exact hfresh
              have hleafSeg : TreeSeg m5 (some a)
                  (BTree.node key .leaf .leaf) :=
                .cons hfresh5 .nil .nil
              have hpresL : TreeSeg m5 l tl :=
                TreeSeg_surgery_preserved hl m1 m2 m3 m4 m5 a a₀ halloc
                  hmfresh ha key (linkWord none) (linkWord none)
                  h0 h1 h2 _ _ _ hA hnl
              have hsltF : (key.slt k) = false := by
                cases h : (key.slt k) with
                | true => exact absurd h hslt
                | false => rfl
              simp only [BTree.binsert, heqk, hsltF, htrleaf]
              exact TreeSeg.cons hnode5 hpresL hleafSeg
            · rw [hrnone, addrOfWord_linkWord_none] at hsubC
              simp only [bstInsertChase] at hsubC
              simp only [Except.ok.injEq, BstInsertRes.attach.injEq] at hsubC
              obtain ⟨-, hs⟩ := hsubC
              exact absurd hs.symm hs0
          · obtain ⟨a', hpa', hmem⟩ := hpath
            have hpa2 : a' = p := Option.some_inj.mp hpa'.symm
            rw [hdecR] at hmem
            rw [hpa2] at hmem
            have hmemT : TreeSegMem (m := m) r p := hmem
            rw [hdecR] at hsubC
            have hIHR : TreeSeg m5 r (BTree.binsert tr key) :=
              ihr (F := F') (lo := some k) (hi := hi)
                (par := some a₀) (side := false)
                (hbst := hrB) (hlen := hlenR)
                (hC := hsubC) (hmem := hmemT)
            have hpresL : TreeSeg m5 l tl :=
              TreeSeg_surgery_preserved hl m1 m2 m3 m4 m5 a p halloc
                hmfresh ha key (linkWord none) (linkWord none)
                h0 h1 h2 _ _ _ hA
                (fun c hc hcon => by
                  subst hcon
                  exact absurd rfl (hdisj _ hc _ hmemT))
            have hne_a : a₀ ≠ p := by
              intro hcon
              have hm : TreeSegMem (m := m) r a₀ := by
                rw [hcon]; exact hmemT
              exact absurd rfl (hnr _ hm)
            have hnode5 := nodePost hnode m1 m2 m3 m4 m5 a p halloc
              hmfresh ha hne_a key (linkWord none) (linkWord none)
              h0 h1 h2 _ _ _ hA
            have hsltF : (key.slt k) = false := by
              cases h : (key.slt k) with
              | true => exact absurd h hslt
              | false => rfl
            simp only [BTree.binsert, heqk, hsltF]
            exact TreeSeg.cons hnode5 hpresL hIHR

/-! ## Forward contract (duplicate no-op, attach adds one leaf) -/

/-- Footprint membership exposes its node. -/
theorem TreeSegMem_nodeAt3' {m : Mem} {s : Option Addr}
    {a : Addr} (hmem : TreeSegMem (m := m) s a) :
    ∃ t k l r, nodeAt3 m a t k l r := by
  induction hmem with
  | here hnode => exact ⟨_, _, _, _, hnode⟩
  | left hnode _ ih => exact ih
  | right hnode _ ih => exact ih

/-- Functional insert is the identity on present keys (set
    semantics — the duplicate no-op, used by the forward
    duplicate case). -/
theorem BTree.binsert_dup_id {t : BTree} {x : BitVec 32}
    (h : BTree.contains t x = true) : BTree.binsert t x = t := by
  induction t with
  | leaf =>
    simp only [BTree.contains] at h
    cases h
  | node k l r ihl ihr =>
    simp only [BTree.contains] at h
    simp only [BTree.binsert]
    by_cases heq : (x == k) = true
    · simp only [heq, ite_true]
    · have heqF : (x == k) = false := by
        cases h' : (x == k) with
        | true => exact absurd h' heq
        | false => rfl
      simp only [heqF, Bool.false_eq_true, ite_false] at h ⊢
      by_cases hslt : (x.slt k) = true
      · simp only [hslt, ite_true] at h ⊢
        rw [ihl h]
      · have hsltF : (x.slt k) = false := by
          cases h' : (x.slt k) with
          | true => exact absurd h' hslt
          | false => rfl
        simp only [hsltF, Bool.false_eq_true, ite_false] at h ⊢
        rw [ihr h]

/-- A duplicate chase hit means the key is present. Induction on
    fuel, stepping through links with the roundtrip (as in the
    chase). -/
theorem bstInsertChase_dup_contains (F : Nat) (m : Mem)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (cur : Option Addr) (key : BitVec 32) (t : BTree)
    (par : Option Addr) (side : Bool)
    (hseg : TreeSeg m cur t) (hlen : t.bsize ≤ F)
    (hC : bstInsertChase F m cur key par side = .ok .dup) :
    BTree.contains t key = true := by
  induction F generalizing cur t hseg par side with
  | zero =>
    cases hseg with
    | nil =>
      simp only [bstInsertChase] at hC
      cases hC
    | cons _ _ _ =>
      simp only [BTree.bsize] at hlen
      omega
  | succ F' ih =>
    cases hseg with
    | nil =>
      simp only [bstInsertChase] at hC
      cases hC
    | @cons a₀ t₀ k l r tl tr hnode hl hr =>
      have hfb : memFind m a₀ = some _ := hnode
      have hmem0 : memLoad m a₀ t₀ 0 = .ok k := nodeLoadKey hnode
      have hmem1 : memLoad m a₀ t₀ 1 = .ok (linkWord l) :=
        nodeLoadLeft hnode
      have hmem2 : memLoad m a₀ t₀ 2 = .ok (linkWord r) :=
        nodeLoadRight hnode
      have hallocL : ∀ c', l = some c' →
          (memFind m c').isSome = true := by
        intro c' hc'
        cases hnxt : l with
        | none => rw [hnxt] at hc'; cases hc'
        | some c'' =>
          cases hc'
          exact TreeSeg_head_alloc hl
      have hdecL := nodeAt3_link_roundtrip hex hallocL
      have hl' : TreeSeg m (addrOfWord (linkWord l)) tl := by
        rw [hdecL]; exact hl
      have hlenL : tl.bsize ≤ F' := by
        simp only [BTree.bsize] at hlen
        omega
      have hallocR : ∀ c', r = some c' →
          (memFind m c').isSome = true := by
        intro c' hc'
        cases hnxt : r with
        | none => rw [hnxt] at hc'; cases hc'
        | some c'' =>
          cases hc'
          exact TreeSeg_head_alloc hr
      have hdecR := nodeAt3_link_roundtrip hex hallocR
      have hr' : TreeSeg m (addrOfWord (linkWord r)) tr := by
        rw [hdecR]; exact hr
      have hlenR : tr.bsize ≤ F' := by
        simp only [BTree.bsize] at hlen
        omega
      unfold bstInsertChase at hC
      simp only [hfb, hmem0] at hC
      by_cases heq : (k == key) = true
      · have hxk : key = k := (beq_iff_eq.mp heq).symm
        have hkk : (k == k) = true := beq_iff_eq.mpr rfl
        simp only [BTree.contains, hxk, hkk, ite_true]
      · rw [ite_eq_right heq] at hC
        have heqF : (k == key) = false := by
          cases h : (k == key) with
          | true => exact absurd h heq
          | false => rfl
        have heqk : (key == k) = false := beq_flip_false heqF
        by_cases hslt : (key.slt k) = true
        · simp only [hmem1, ite_eq_left hslt] at hC
          have hsub := ih (cur := addrOfWord (linkWord l))
            (par := some a₀) (side := true) (t := tl)
            (hseg := hl') (hlen := hlenL) (hC := hC)
          simp only [BTree.contains, heqk, hslt, ite_true]
          exact hsub
        · have hnslt : ¬((key.slt k) = true) := hslt
          simp only [hmem2, ite_eq_right hnslt] at hC
          have hsub := ih (cur := addrOfWord (linkWord r))
            (par := some a₀) (side := false) (t := tr)
            (hseg := hr') (hlen := hlenR) (hC := hC)
          simp only [BTree.contains, heqk]
          have hsltF : (key.slt k) = false := by
            cases h : (key.slt k) with
            | true => exact absurd h hslt
            | false => rfl
          simp only [hsltF]
          exact hsub

/-- The entry mirror is correct: duplicate keeps `(root, m)`
    with the key present; attach allocates, inits, and swings
    the recorded link, yielding the functional insertion. The
    forward match arms reduce by the store equations (supplied,
    not cased — every store succeeds on the framed blocks). -/
theorem bstInsertFwd_correct (F : Nat) (m : Mem)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (hmfresh : memFind m m.next = none)
    (root : Option Addr) (key : BitVec 32) (t : BTree)
    (hbst : Bst none none t) (hseg : TreeSeg m root t)
    (hd : SegDistinct m root t hseg)
    (hlen : t.bsize ≤ F)
    (r : Option Addr × Mem)
    (hfwd : bstInsertFwd F m root key = .ok r) :
    ∃ nr m', r = (nr, m') ∧
      ∃ t', t' = BTree.binsert t key ∧ TreeSeg m' nr t' ∧
        Bst none none t' ∧ key ∈ t'.flatten := by
  obtain ⟨cr, hC⟩ := bstInsertChase_ok F m hex key root t hseg hlen
    none false
  unfold bstInsertFwd at hfwd
  rw [hC] at hfwd
  cases cr with
  | dup =>
    simp only [] at hfwd
    simp only [Except.ok.injEq] at hfwd
    obtain rfl := hfwd
    have hcon := bstInsertChase_dup_contains F m hex root key t
      none false hseg hlen hC
    have hmem : key ∈ t.flatten := by
      have hiff := BTree.contains_iff_mem_flatten (t := t) (x := key)
        hbst True.intro True.intro
      rw [hiff] at hcon
      exact hcon
    have hdup : BTree.binsert t key = t :=
      BTree.binsert_dup_id hcon
    exact ⟨root, m, rfl, t, hdup.symm, hseg, hbst, hmem⟩
  | attach parent side =>
    simp only [] at hfwd
    obtain ⟨m1, a, hallock⟩ : ∃ m1 a, (m1, a) = memAlloc m 3 :=
      ⟨_, _, rfl⟩
    have ha : a = m.next := by
      have h2 := memAlloc_next m 3
      have h3 : a = (memAlloc m 3).2 := congrArg Prod.snd hallock
      rw [h3]; exact h2
    have hrep : List.replicate 3 (0 : BitVec 32) = [0, 0, 0] := rfl
    have hfind1 : memFind m1 a = some ⟨a, true, [0, 0, 0]⟩ := by
      have h := memFind_memAlloc m 3
      rw [hrep] at h
      have e1 : m1 = (memAlloc m 3).1 := congrArg Prod.fst hallock
      have e2 : a = (memAlloc m 3).2 := congrArg Prod.snd hallock
      rw [e1, e2]
      exact h
    have c0 : cellsAt m1 a a [0, 0, 0] := hfind1
    obtain ⟨m2, h0⟩ : ∃ m2, memStore m1 a a 0 key = .ok m2 :=
      ⟨_, memStore_cellsAt m1 a a 0 [0, 0, 0] key c0 (by simp)⟩
    have e0 : ([0, 0, 0].set 0 key) = [key, 0, 0] := by simp
    have c1 : cellsAt m2 a a [key, 0, 0] := by
      have hc := memFind_cellsAt_store m1 a a 0 [0, 0, 0] key m2
        c0 (by simp) h0
      rw [e0] at hc
      exact hc
    obtain ⟨m3, h1⟩ : ∃ m3,
        memStore m2 a a 1 (linkWord none) = .ok m3 :=
      ⟨_, memStore_cellsAt m2 a a 1 [key, 0, 0] (linkWord none)
        c1 (by simp)⟩
    have e1 : ([key, (0 : BitVec 32), 0].set 1 (linkWord none)) =
        [key, 0, 0] := by simp [linkWord_none]
    have c2 : cellsAt m3 a a [key, 0, 0] := by
      have hc := memFind_cellsAt_store m2 a a 1 [key, 0, 0]
        (linkWord none) m3 c1 (by simp) h1
      rw [e1] at hc
      exact hc
    obtain ⟨m4, h2⟩ : ∃ m4,
        memStore m3 a a 2 (linkWord none) = .ok m4 :=
      ⟨_, memStore_cellsAt m3 a a 2 [key, 0, 0] (linkWord none)
        c2 (by simp)⟩
    rw [← hallock] at hfwd
    dsimp only at hfwd
    simp only [h0, h1, h2] at hfwd
    cases parent with
    | none =>
      simp only [] at hfwd
      simp only [Except.ok.injEq] at hfwd
      obtain rfl := hfwd
      cases hseg with
      | nil =>
        have hfresh := freshLeaf_init m key m1 a hallock m2 m3 m4
          h0 h1 h2
        have hleaf : TreeSeg m4 (some a) (BTree.node key .leaf .leaf) :=
          .cons hfresh .nil .nil
        have hbin : BTree.binsert .leaf key =
            BTree.node key .leaf .leaf := rfl
        refine ⟨some a, m4, rfl, BTree.node key .leaf .leaf, ?_, ?_,
          ?_, ?_⟩
        · exact hbin.symm
        · exact hleaf
        · exact Bst.node True.intro True.intro (Bst.leaf _ _)
            (Bst.leaf _ _)
        · rw [show BTree.flatten (BTree.node key .leaf .leaf) = [key]
            from rfl]
          exact List.mem_cons_self
      | @cons a₀ t₀ k l r tl tr hnode hl hr =>
        cases F with
        | zero =>
          simp only [bstInsertChase] at hC
          cases hC
        | succ F' =>
          have hfb : memFind m a₀ = some _ := hnode
          have hmem0 : memLoad m a₀ t₀ 0 = .ok k :=
            nodeLoadKey hnode
          have hmem1 : memLoad m a₀ t₀ 1 = .ok (linkWord l) :=
            nodeLoadLeft hnode
          have hmem2 : memLoad m a₀ t₀ 2 = .ok (linkWord r) :=
            nodeLoadRight hnode
          have hallocL : ∀ c', l = some c' →
              (memFind m c').isSome = true := by
            intro c' hc'
            cases hnxt : l with
            | none => rw [hnxt] at hc'; cases hc'
            | some c'' =>
              cases hc'
              exact TreeSeg_head_alloc hl
          have hdecL := nodeAt3_link_roundtrip hex hallocL
          have hl' : TreeSeg m (addrOfWord (linkWord l)) tl := by
            rw [hdecL]; exact hl
          have hlenL : tl.bsize ≤ F' := by
            simp only [BTree.bsize] at hlen
            omega
          have hallocR : ∀ c', r = some c' →
              (memFind m c').isSome = true := by
            intro c' hc'
            cases hnxt : r with
            | none => rw [hnxt] at hc'; cases hc'
            | some c'' =>
              cases hc'
              exact TreeSeg_head_alloc hr
          have hdecR := nodeAt3_link_roundtrip hex hallocR
          have hr' : TreeSeg m (addrOfWord (linkWord r)) tr := by
            rw [hdecR]; exact hr
          have hlenR : tr.bsize ≤ F' := by
            simp only [BTree.bsize] at hlen
            omega
          unfold bstInsertChase at hC
          simp only [hfb, hmem0] at hC
          by_cases heq : (k == key) = true
          · rw [ite_eq_left heq] at hC
            cases hC
          · rw [ite_eq_right heq] at hC
            by_cases hslt : (key.slt k) = true
            · simp only [hmem1, ite_eq_left hslt] at hC
              have hpath := bstInsertChase_at_mem F' m hex
                (addrOfWord (linkWord l)) key (some a₀) true none
                side tl hC hl'
              rcases hpath with hpath | hpath
              · cases hpath
              · obtain ⟨a', hpa', -⟩ := hpath
                cases hpa'
            · have hnslt : ¬((key.slt k) = true) := hslt
              simp only [hmem2, ite_eq_right hnslt] at hC
              have hpath := bstInsertChase_at_mem F' m hex
                (addrOfWord (linkWord r)) key (some a₀) false none
                side tr hC hr'
              rcases hpath with hpath | hpath
              · cases hpath
              · obtain ⟨a', hpa', -⟩ := hpath
                cases hpa'
    | some p =>
      have hpath := bstInsertChase_at_mem F m hex root key none false
        (some p) side t hC hseg
      rcases hpath with hpath | hpath
      · cases hpath
      · obtain ⟨a', hpa', hmem'⟩ := hpath
        have hpa2 : a' = p := Option.some_inj.mp hpa'.symm
        subst a'
        obtain ⟨tp, kp, lp, rp, hpp⟩ := TreeSegMem_nodeAt3' hmem'
        have hnode4 := node_to_m4 hpp m1 m2 m3 m4 a hallock hmfresh
          ha key (linkWord none) (linkWord none) h0 h1 h2
        have hfind4 : memFind m4 p =
            some ⟨tp, true, [kp, linkWord lp, linkWord rp]⟩ := hnode4
        obtain ⟨b, hfind4b⟩ : ∃ b, memFind m4 p = some b :=
          ⟨_, hfind4⟩
        have htag : b.tag = tp := by
          rw [hfind4] at hfind4b
          simp only [Option.some.injEq] at hfind4b
          exact congrArg Block.tag hfind4b.symm
        obtain ⟨m5, hA⟩ : ∃ m5, memStore m4 p b.tag
            (if side then 1 else 2) (linkWord (some a)) = .ok m5 := by
          have hc4 : cellsAt m4 p b.tag
              [kp, linkWord lp, linkWord rp] := by
            rw [htag]; exact hnode4
          have hlt : (if side then 1 else 2) <
              [kp, linkWord lp, linkWord rp].length := by
            have h3 : [kp, linkWord lp, linkWord rp].length = 3 := rfl
            rw [h3]
            cases side <;> decide
          exact ⟨_, memStore_cellsAt m4 p b.tag
            (if side then 1 else 2) [kp, linkWord lp, linkWord rp]
            (linkWord (some a)) hc4 hlt⟩
        simp only [] at hfwd
        rw [hfind4b] at hfwd
        simp only [] at hfwd
        rw [hA] at hfwd
        simp only [] at hfwd
        simp only [Except.ok.injEq] at hfwd
        obtain rfl := hfwd
        have hseg5 := bstInsertAttach_seg (F := F) (m := m)
          (hex := hex) (hmfresh := hmfresh) (root := root)
          (key := key) (t := t) (lo := none) (hi := none)
          (hbst := hbst) (hseg := hseg) (hd := hd) (hlen := hlen)
          (p := p) (s := side) (par := none) (side := false)
          (hC := hC) (hmem := hmem')
          (m1 := m1) (m2 := m2) (m3 := m3) (m4 := m4) (m5 := m5)
          (a := a) (ha := ha) (halloc := hallock)
          (h0 := h0) (h1 := h1) (h2 := h2)
          (b := b) (hfind4 := hfind4b)
          (idxA := if side then 1 else 2)
          (xA := linkWord (some a)) (hA := hA)
          (hidx := rfl) (hxA := rfl)
        have hbst5 : Bst none none (BTree.binsert t key) :=
          BTree.binsert_bst hbst True.intro True.intro
        have hmem5 : key ∈ (BTree.binsert t key).flatten := by
          rw [BTree.mem_flatten_binsert]
          exact Or.inl rfl
        exact ⟨root, m5, rfl, _, rfl, hseg5, hbst5, hmem5⟩

/-! ## Loop agreement (evaluator follows the chase) -/

/-- Loop/evaluator agreement: the insert loop evaluates exactly
    as the chase directs — exhaustion falls through with the
    parent recorded, cursor null, and side flag matching the
    chase side; duplicate returns the old root early. The
    `went_left` flag (`wl`) tracks the chase side bit
    (`hwl`). Induction on fuel, reusing the chase-ok skeleton. -/
theorem bstInsertLoop_agree (F : Nat) :
    ∀ (m : Mem) (π : Layout)
      (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
      (root : Option Addr) (key : BitVec 32)
      (parent cur : Option Addr) (wl : BitVec 32)
      (t : BTree) (hseg : TreeSeg m cur t)
      (hlen : t.bsize ≤ F)
      (wentLeft : Bool) (hwl : wl = if wentLeft then 1 else 0)
      (r : BstInsertRes)
      (hC : bstInsertChase F m cur key parent wentLeft = .ok r),
    (∀ p s, r = .attach p s →
      memEvalStmtFuel F bstInsertLoop (mkBstInsertEnv root key parent cur wl)
        m π =
        .ok ((mkBstInsertEnv root key p none (if s then 1 else 0), m, π),
          .fellThrough)) ∧
    (r = .dup →
      ∃ ρ', memEvalStmtFuel F bstInsertLoop
        (mkBstInsertEnv root key parent cur wl) m π =
        .ok ((ρ', m, π), .returned (.ptrVal root))) := by
  induction F with
  | zero =>
    intro m π hex root key parent cur wl t hseg hlen wentLeft hwl r hC
    cases hseg with
    | nil =>
      have hC' : bstInsertChase 0 m none key parent wentLeft =
          .ok (.attach parent wentLeft) := by simp [bstInsertChase]
      rw [hC'] at hC
      simp only [Except.ok.injEq] at hC
      obtain rfl := hC
      refine ⟨?_, ?_⟩
      · intro p s hcon
        simp only [BstInsertRes.attach.injEq] at hcon
        obtain ⟨rfl, rfl⟩ := hcon
        have hcurE : memEvalExpr (.var "cur")
            (mkBstInsertEnv root key parent none wl) m π =
            .ok (.ptrVal none) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _
            (mkBstInsertEnv_cur _ _ _ _ _)
        have hnullE : memEvalExpr (.lit .nullptr)
            (mkBstInsertEnv root key parent none wl) m π =
            .ok (.ptrVal none) := by
          simp [memEvalExpr, litVal]
        have hgF : memEvalExpr (.une (.var "cur") (.lit .nullptr))
            (mkBstInsertEnv root key parent none wl) m π =
            .ok (.b false) := by
          have hg := memEvalExpr_une_ptrVal _ _ _ _ _ none none
            hcurE hnullE
          have hbe : ((none : Option Addr) != none) = false := by
            simp
          rw [hbe] at hg
          exact hg
        have hw : memEvalStmtFuel 0 bstInsertLoop
            (mkBstInsertEnv root key parent none wl) m π =
            .ok ((mkBstInsertEnv root key parent none wl, m, π),
              .fellThrough) :=
          memEvalStmtFuel_while_false _ _ _ _ _ _ hgF
        rw [← hwl]
        exact hw
      · intro hcon
        cases hcon
    | cons _ _ _ =>
      simp only [BTree.bsize] at hlen
      omega
  | succ F ih =>
    intro m π hex root key parent cur wl t hseg hlen wentLeft hwl r hC
    cases hseg with
    | nil =>
      have hC' : bstInsertChase (F + 1) m none key parent wentLeft =
          .ok (.attach parent wentLeft) := by simp [bstInsertChase]
      rw [hC'] at hC
      simp only [Except.ok.injEq] at hC
      obtain rfl := hC
      refine ⟨?_, ?_⟩
      · intro p s hcon
        simp only [BstInsertRes.attach.injEq] at hcon
        obtain ⟨rfl, rfl⟩ := hcon
        have hcurE : memEvalExpr (.var "cur")
            (mkBstInsertEnv root key parent none wl) m π =
            .ok (.ptrVal none) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _
            (mkBstInsertEnv_cur _ _ _ _ _)
        have hnullE : memEvalExpr (.lit .nullptr)
            (mkBstInsertEnv root key parent none wl) m π =
            .ok (.ptrVal none) := by
          simp [memEvalExpr, litVal]
        have hgF : memEvalExpr (.une (.var "cur") (.lit .nullptr))
            (mkBstInsertEnv root key parent none wl) m π =
            .ok (.b false) := by
          have hg := memEvalExpr_une_ptrVal _ _ _ _ _ none none
            hcurE hnullE
          have hbe : ((none : Option Addr) != none) = false := by
            simp
          rw [hbe] at hg
          exact hg
        have hw : memEvalStmtFuel (F + 1) bstInsertLoop
            (mkBstInsertEnv root key parent none wl) m π =
            .ok ((mkBstInsertEnv root key parent none wl, m, π),
              .fellThrough) :=
          memEvalStmtFuel_while_false _ _ _ _ _ _ hgF
        rw [← hwl]
        exact hw
      · intro hcon
        cases hcon
    | @cons a tg k l r_ tl tr hnode hl hr =>
      have hfb : memFind m a = some _ := hnode
      have hmem0 : memLoad m a tg 0 = .ok k := nodeLoadKey hnode
      have hmem1 : memLoad m a tg 1 = .ok (linkWord l) :=
        nodeLoadLeft hnode
      have hmem2 : memLoad m a tg 2 = .ok (linkWord r_) :=
        nodeLoadRight hnode
      have hlenL : tl.bsize ≤ F := by
        simp only [BTree.bsize] at hlen
        omega
      have hlenR : tr.bsize ≤ F := by
        simp only [BTree.bsize] at hlen
        omega
      have hcurE : memEvalExpr (.var "cur")
          (mkBstInsertEnv root key parent (some a) wl) m π =
          .ok (.ptrVal (some a)) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _
          (mkBstInsertEnv_cur _ _ _ _ _)
      have hnullE : memEvalExpr (.lit .nullptr)
          (mkBstInsertEnv root key parent (some a) wl) m π =
          .ok (.ptrVal none) := by
        simp [memEvalExpr, litVal]
      have hgT : memEvalExpr (.une (.var "cur") (.lit .nullptr))
          (mkBstInsertEnv root key parent (some a) wl) m π =
          .ok (.b true) := by
        have hg := memEvalExpr_une_ptrVal _ _ _ _ _ (some a) none
          hcurE hnullE
        have hbe : ((some a) != none) = true := by simp
        rw [hbe] at hg
        exact hg
      have hpget : memEvalExpr (.pgetVal (.var "cur"))
          (mkBstInsertEnv root key parent (some a) wl) m π =
          .ok (.i32 k) :=
        memEvalExpr_pgetVal_hit _ _ _ _ _ _ _ hcurE hfb hmem0
      have hkeyE : memEvalExpr (.var "key")
          (mkBstInsertEnv root key parent (some a) wl) m π =
          .ok (.i32 key) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ (mkBstInsertEnv_key _ _ _ _ _)
      have hueq : memEvalExpr (.ueq (.pgetVal (.var "cur")) (.var "key"))
          (mkBstInsertEnv root key parent (some a) wl) m π =
          .ok (.b (k == key)) := by
        unfold memEvalExpr
        simp only [hpget, hkeyE]
      by_cases heq : (k == key) = true
      · have hC' : bstInsertChase (F + 1) m (some a) key parent wentLeft =
          .ok .dup := by
          unfold bstInsertChase
          simp only [hfb, hmem0, ite_eq_left heq]
        rw [hC'] at hC
        simp only [Except.ok.injEq] at hC
        obtain rfl := hC
        refine ⟨?_, ?_⟩
        · intro p s hcon
          cases hcon
        · intro hcon
          cases hcon
          have hueqT : memEvalExpr
              (.ueq (.pgetVal (.var "cur")) (.var "key"))
              (mkBstInsertEnv root key parent (some a) wl) m π =
              .ok (.b true) := by
            rw [heq] at hueq
            exact hueq
          have hevR : memEvalExpr (.var "root")
              (mkBstInsertEnv root key parent (some a) wl) m π =
              evalExpr (.var "root")
                (mkBstInsertEnv root key parent (some a) wl) :=
            memEvalExpr_var _ _ _ _
          have hevRV : evalExpr (.var "root")
              (mkBstInsertEnv root key parent (some a) wl) =
              .ok (.ptrVal root) :=
            evalExpr_var_hit _ _ _
              (by simp [envLookup, mkBstInsertEnv])
          have hret := memEvalStmtFuel_return F (.var "root")
            (mkBstInsertEnv root key parent (some a) wl) m π _ hevR
            hevRV
          have hbodyEv : memEvalStmtFuel F bstInsertLoopBody
              (mkBstInsertEnv root key parent (some a) wl) m π =
              .ok (((mkBstInsertEnv root key parent (some a) wl, m, π)),
                .returned (.ptrVal root)) := by
            have hif : memEvalStmtFuel F bstInsertLoopBody
                (mkBstInsertEnv root key parent (some a) wl) m π =
                memEvalStmtFuel F (.return_ (.var "root"))
                (mkBstInsertEnv root key parent (some a) wl) m π :=
              memEvalStmtFuel_if_true F _ _ _ _ _ _ hueqT
            exact hif.trans hret
          have hW : memEvalStmtFuel (F + 1) bstInsertLoop
              (mkBstInsertEnv root key parent (some a) wl) m π =
              .ok (((mkBstInsertEnv root key parent (some a) wl, m, π)),
                .returned (.ptrVal root)) := by
            have h := memEvalStmtFuel_while_true F _
              bstInsertLoopBody _ _ _ hgT
            simp only [hbodyEv] at h
            exact h
          exact ⟨_, hW⟩
      · have heqF : (k == key) = false := by
          cases h : (k == key) with
          | true => exact absurd h heq
          | false => rfl
        have hueqF : memEvalExpr
            (.ueq (.pgetVal (.var "cur")) (.var "key"))
            (mkBstInsertEnv root key parent (some a) wl) m π =
            .ok (.b false) := by
          rw [heqF] at hueq
          exact hueq
        have hsltM : memEvalExpr
            (.slt (.var "key") (.pgetVal (.var "cur")))
            (mkBstInsertEnv root key parent (some a) wl) m π =
            .ok (.b (key.slt k)) := by
          unfold memEvalExpr
          simp only [hkeyE, hpget]
        by_cases hslt : (key.slt k) = true
        · have hallocL : ∀ c', l = some c' →
              (memFind m c').isSome = true := by
            intro c' hc'
            cases hnxt : l with
            | none => rw [hnxt] at hc'; cases hc'
            | some c'' =>
              cases hc'
              exact TreeSeg_head_alloc hl
          have hdecL := nodeAt3_link_roundtrip hex hallocL
          have hl' : TreeSeg m (addrOfWord (linkWord l)) tl := by
            rw [hdecL]; exact hl
          have hsltT : memEvalExpr
              (.slt (.var "key") (.pgetVal (.var "cur")))
              (mkBstInsertEnv root key parent (some a) wl) m π =
              .ok (.b true) := by
            rw [hslt] at hsltM
            exact hsltM
          have hlinkL : memEvalExpr (.pgetNext (.var "cur"))
              (mkBstInsertEnv root key parent (some a) wl) m π =
              .ok (.ptrVal (addrOfWord (linkWord l))) :=
            memEvalExpr_pgetNext_hit _ _ _ _ _ _ _ hcurE hfb hmem1
          have hpar : memEvalStmtFuel F
              (.assign "parent" (.var "cur"))
              (mkBstInsertEnv root key parent (some a) wl) m π =
              .ok (((mkBstInsertEnv root key (some a) (some a) wl, m, π)),
                .fellThrough) :=
            memEvalStmtFuel_assign_mem F "parent" (.var "cur")
              (mkBstInsertEnv root key parent (some a) wl) m π _ _
              hcurE (by simp [mkBstInsertEnv, envUpdate])
          have hcurE1 : envLookup
              (mkBstInsertEnv root key (some a) (some a) wl) "cur" =
              some (.ptrVal (some a)) :=
            mkBstInsertEnv_cur _ _ _ _ _
          have hevCur1 : memEvalExpr (.var "cur")
              (mkBstInsertEnv root key (some a) (some a) wl) m π =
              .ok (.ptrVal (some a)) := by
            rw [memEvalExpr_var]
            exact evalExpr_var_hit _ _ _ hcurE1
          have hlinkL' : memEvalExpr (.pgetNext (.var "cur"))
              (mkBstInsertEnv root key (some a) (some a) wl) m π =
              .ok (.ptrVal (addrOfWord (linkWord l))) :=
            memEvalExpr_pgetNext_hit _ _ _ _ _ _ _ hevCur1 hfb hmem1
          have hcur : memEvalStmtFuel F
              (.assign "cur" (.pgetNext (.var "cur")))
              (mkBstInsertEnv root key (some a) (some a) wl) m π =
              .ok (((mkBstInsertEnv root key (some a)
                (addrOfWord (linkWord l)) wl, m, π)), .fellThrough) :=
            memEvalStmtFuel_assign_mem F "cur" (.pgetNext (.var "cur"))
              (mkBstInsertEnv root key (some a) (some a) wl) m π _ _
              hlinkL' (by simp [mkBstInsertEnv, envUpdate])
          have hev1 : memEvalExpr (.lit (.i32 1))
              (mkBstInsertEnv root key (some a)
                (addrOfWord (linkWord l)) wl) m π =
              .ok (.i32 1) := by
            simp [memEvalExpr, evalExpr, litVal]
          have hwl : memEvalStmtFuel F
              (.assign "went_left" (.lit (.i32 1)))
              (mkBstInsertEnv root key (some a)
                (addrOfWord (linkWord l)) wl) m π =
              .ok (((mkBstInsertEnv root key (some a)
                (addrOfWord (linkWord l)) 1, m, π)), .fellThrough) :=
            memEvalStmtFuel_assign_mem F "went_left" (.lit (.i32 1))
              (mkBstInsertEnv root key (some a)
                (addrOfWord (linkWord l)) wl) m π _ _
              hev1 (by simp [mkBstInsertEnv, envUpdate])
          have hseq1 := memEvalStmtFuel_seq_fallthrough_trans F _ _
            (mkBstInsertEnv root key (some a) (some a) wl) m π
            (mkBstInsertEnv root key (some a)
              (addrOfWord (linkWord l)) wl) m π _ hcur hwl
          have hbodyEv : memEvalStmtFuel F bstInsertLoopBody
              (mkBstInsertEnv root key parent (some a) wl) m π =
              .ok (((mkBstInsertEnv root key (some a)
                (addrOfWord (linkWord l)) 1, m, π)), .fellThrough) := by
            have hifF : memEvalStmtFuel F bstInsertLoopBody
                (mkBstInsertEnv root key parent (some a) wl) m π =
                memEvalStmtFuel F
                  (.if_ (.slt (.var "key") (.pgetVal (.var "cur")))
                    (.seq (.assign "parent" (.var "cur"))
                    (.seq (.assign "cur" (.pgetNext (.var "cur")))
                      (.assign "went_left" (.lit (.i32 1)))))
                    (.seq (.assign "parent" (.var "cur"))
                    (.seq (.assign "cur" (.pgetRight (.var "cur")))
                      (.assign "went_left" (.lit (.i32 0))))))
                  (mkBstInsertEnv root key parent (some a) wl) m π :=
              memEvalStmtFuel_if_false F _ _ _ _ _ _ hueqF
            have hifT : memEvalStmtFuel F
                (.if_ (.slt (.var "key") (.pgetVal (.var "cur")))
                  (.seq (.assign "parent" (.var "cur"))
                  (.seq (.assign "cur" (.pgetNext (.var "cur")))
                    (.assign "went_left" (.lit (.i32 1)))))
                  (.seq (.assign "parent" (.var "cur"))
                  (.seq (.assign "cur" (.pgetRight (.var "cur")))
                    (.assign "went_left" (.lit (.i32 0))))))
                (mkBstInsertEnv root key parent (some a) wl) m π =
                memEvalStmtFuel F
                  (.seq (.assign "parent" (.var "cur"))
                  (.seq (.assign "cur" (.pgetNext (.var "cur")))
                    (.assign "went_left" (.lit (.i32 1)))))
                (mkBstInsertEnv root key parent (some a) wl) m π :=
              memEvalStmtFuel_if_true F _ _ _ _ _ _ hsltT
            have hseq0 := memEvalStmtFuel_seq_fallthrough_trans F _ _
              (mkBstInsertEnv root key parent (some a) wl) m π
              (mkBstInsertEnv root key (some a) (some a) wl) m π _
              hpar hseq1
            exact hifF.trans (hifT.trans hseq0)
          have hC'' : bstInsertChase F m (addrOfWord (linkWord l)) key
              (some a) true = .ok r := by
            have hch := hC
            unfold bstInsertChase at hch
            simp only [hfb, hmem0, hmem1] at hch
            rw [ite_eq_right heq, ite_eq_left hslt] at hch
            exact hch
          have hIH := ih m π hex root key (some a)
            (addrOfWord (linkWord l)) 1 tl hl' hlenL true rfl r hC''
          have hWh : memEvalStmtFuel (F + 1) bstInsertLoop
              (mkBstInsertEnv root key parent (some a) wl) m π =
              memEvalStmtFuel F bstInsertLoop
                (mkBstInsertEnv root key (some a)
                  (addrOfWord (linkWord l)) 1)
                m π := by
            have h := memEvalStmtFuel_while_true F _
              bstInsertLoopBody _ _ _ hgT
            simp only [hbodyEv] at h
            exact h
          refine ⟨fun p s hcon => ?_, fun hcon => ?_⟩
          · have hstep := hIH.1 p s hcon
            rw [hWh]
            exact hstep
          · obtain ⟨ρ'', hev⟩ := hIH.2 hcon
            rw [hWh]
            exact ⟨ρ'', hev⟩
        · have hnslt : ¬((key.slt k) = true) := hslt
          have hallocR : ∀ c', r_ = some c' →
              (memFind m c').isSome = true := by
            intro c' hc'
            cases hnxt : r_ with
            | none => rw [hnxt] at hc'; cases hc'
            | some c'' =>
              cases hc'
              exact TreeSeg_head_alloc hr
          have hdecR := nodeAt3_link_roundtrip hex hallocR
          have hr' : TreeSeg m (addrOfWord (linkWord r_)) tr := by
            rw [hdecR]; exact hr
          have hsltF : (key.slt k) = false := by
            cases h : (key.slt k) with
            | true => exact absurd h hslt
            | false => rfl
          have hsltF' : memEvalExpr
              (.slt (.var "key") (.pgetVal (.var "cur")))
              (mkBstInsertEnv root key parent (some a) wl) m π =
              .ok (.b false) := by
            rw [hsltF] at hsltM
            exact hsltM
          have hlinkR : memEvalExpr (.pgetRight (.var "cur"))
              (mkBstInsertEnv root key parent (some a) wl) m π =
              .ok (.ptrVal (addrOfWord (linkWord r_))) :=
            memEvalExpr_pgetRight_hit _ _ _ _ _ _ _ hcurE hfb hmem2
          have hpar : memEvalStmtFuel F
              (.assign "parent" (.var "cur"))
              (mkBstInsertEnv root key parent (some a) wl) m π =
              .ok (((mkBstInsertEnv root key (some a) (some a) wl, m, π)),
                .fellThrough) :=
            memEvalStmtFuel_assign_mem F "parent" (.var "cur")
              (mkBstInsertEnv root key parent (some a) wl) m π _ _
              hcurE (by simp [mkBstInsertEnv, envUpdate])
          have hcurE1 : envLookup
              (mkBstInsertEnv root key (some a) (some a) wl) "cur" =
              some (.ptrVal (some a)) :=
            mkBstInsertEnv_cur _ _ _ _ _
          have hevCur1 : memEvalExpr (.var "cur")
              (mkBstInsertEnv root key (some a) (some a) wl) m π =
              .ok (.ptrVal (some a)) := by
            rw [memEvalExpr_var]
            exact evalExpr_var_hit _ _ _ hcurE1
          have hlinkR' : memEvalExpr (.pgetRight (.var "cur"))
              (mkBstInsertEnv root key (some a) (some a) wl) m π =
              .ok (.ptrVal (addrOfWord (linkWord r_))) :=
            memEvalExpr_pgetRight_hit _ _ _ _ _ _ _ hevCur1 hfb hmem2
          have hcur : memEvalStmtFuel F
              (.assign "cur" (.pgetRight (.var "cur")))
              (mkBstInsertEnv root key (some a) (some a) wl) m π =
              .ok (((mkBstInsertEnv root key (some a)
                (addrOfWord (linkWord r_)) wl, m, π)), .fellThrough) :=
            memEvalStmtFuel_assign_mem F "cur" (.pgetRight (.var "cur"))
              (mkBstInsertEnv root key (some a) (some a) wl) m π _ _
              hlinkR' (by simp [mkBstInsertEnv, envUpdate])
          have hev0 : memEvalExpr (.lit (.i32 0))
              (mkBstInsertEnv root key (some a)
                (addrOfWord (linkWord r_)) wl) m π =
              .ok (.i32 0) := by
            simp [memEvalExpr, evalExpr, litVal]
          have hwl : memEvalStmtFuel F
              (.assign "went_left" (.lit (.i32 0)))
              (mkBstInsertEnv root key (some a)
                (addrOfWord (linkWord r_)) wl) m π =
              .ok (((mkBstInsertEnv root key (some a)
                (addrOfWord (linkWord r_)) 0, m, π)), .fellThrough) :=
            memEvalStmtFuel_assign_mem F "went_left" (.lit (.i32 0))
              (mkBstInsertEnv root key (some a)
                (addrOfWord (linkWord r_)) wl) m π _ _
              hev0 (by simp [mkBstInsertEnv, envUpdate])
          have hseq1 := memEvalStmtFuel_seq_fallthrough_trans F _ _
            (mkBstInsertEnv root key (some a) (some a) wl) m π
            (mkBstInsertEnv root key (some a)
              (addrOfWord (linkWord r_)) wl) m π _ hcur hwl
          have hbodyEv : memEvalStmtFuel F bstInsertLoopBody
              (mkBstInsertEnv root key parent (some a) wl) m π =
              .ok (((mkBstInsertEnv root key (some a)
                (addrOfWord (linkWord r_)) 0, m, π)), .fellThrough) := by
            have hifF : memEvalStmtFuel F bstInsertLoopBody
                (mkBstInsertEnv root key parent (some a) wl) m π =
                memEvalStmtFuel F
                  (.if_ (.slt (.var "key") (.pgetVal (.var "cur")))
                    (.seq (.assign "parent" (.var "cur"))
                    (.seq (.assign "cur" (.pgetNext (.var "cur")))
                      (.assign "went_left" (.lit (.i32 1)))))
                    (.seq (.assign "parent" (.var "cur"))
                    (.seq (.assign "cur" (.pgetRight (.var "cur")))
                      (.assign "went_left" (.lit (.i32 0))))))
                  (mkBstInsertEnv root key parent (some a) wl) m π :=
              memEvalStmtFuel_if_false F _ _ _ _ _ _ hueqF
            have hifF2 : memEvalStmtFuel F
                (.if_ (.slt (.var "key") (.pgetVal (.var "cur")))
                  (.seq (.assign "parent" (.var "cur"))
                  (.seq (.assign "cur" (.pgetNext (.var "cur")))
                    (.assign "went_left" (.lit (.i32 1)))))
                  (.seq (.assign "parent" (.var "cur"))
                  (.seq (.assign "cur" (.pgetRight (.var "cur")))
                    (.assign "went_left" (.lit (.i32 0))))))
                (mkBstInsertEnv root key parent (some a) wl) m π =
                memEvalStmtFuel F
                  (.seq (.assign "parent" (.var "cur"))
                  (.seq (.assign "cur" (.pgetRight (.var "cur")))
                    (.assign "went_left" (.lit (.i32 0)))))
                (mkBstInsertEnv root key parent (some a) wl) m π :=
              memEvalStmtFuel_if_false F _ _ _ _ _ _ hsltF'
            have hseq0 := memEvalStmtFuel_seq_fallthrough_trans F _ _
              (mkBstInsertEnv root key parent (some a) wl) m π
              (mkBstInsertEnv root key (some a) (some a) wl) m π _
              hpar hseq1
            exact hifF.trans (hifF2.trans hseq0)
          have hC'' : bstInsertChase F m (addrOfWord (linkWord r_)) key
              (some a) false = .ok r := by
            have hch := hC
            unfold bstInsertChase at hch
            simp only [hfb, hmem0, hmem2] at hch
            rw [ite_eq_right heq, ite_eq_right hnslt] at hch
            exact hch
          have hIHR := ih m π hex root key (some a)
            (addrOfWord (linkWord r_)) 0 tr hr' hlenR false rfl r hC''
          have hWh : memEvalStmtFuel (F + 1) bstInsertLoop
              (mkBstInsertEnv root key parent (some a) wl) m π =
              memEvalStmtFuel F bstInsertLoop
                (mkBstInsertEnv root key (some a)
                  (addrOfWord (linkWord r_)) 0)
                m π := by
            have h := memEvalStmtFuel_while_true F _
              bstInsertLoopBody _ _ _ hgT
            simp only [hbodyEv] at h
            exact h
          refine ⟨fun p s hcon => ?_, fun hcon => ?_⟩
          · have hstep := hIHR.1 p s hcon
            rw [hWh]
            exact hstep
          · obtain ⟨ρ'', hev⟩ := hIHR.2 hcon
            rw [hWh]
            exact ⟨ρ'', hev⟩

/-! ## Entry correctness (evaluator meets the mirror) -/

/-- The insert entry evaluates as the mirror and satisfies the
    set-semantics contract: duplicate keeps the old root,
    attach yields the functional insertion with the BST
    invariant preserved. Prelude seeds parent/cur/side, the
    loop agrees with the chase, the attach evaluates the
    stores, and the forward contract supplies the spec. -/
theorem bstInsertFunc_correct (F : Nat) (m : Mem) (π : Layout)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (hmfresh : memFind m m.next = none)
    (root : Option Addr) (key : BitVec 32) (t : BTree)
    (hbst : Bst none none t) (hseg : TreeSeg m root t)
    (hd : SegDistinct m root t hseg)
    (hlen : t.bsize ≤ F) :
    ∃ (ρ' : Env) (nr : Option Addr) (m' : Mem),
      memEvalStmtFuel F bstInsertFunc.body
        [("root", .ptrVal root), ("key", .i32 key)] m π =
        .ok ((ρ', m', π), .returned (.ptrVal nr)) ∧
      ∃ t', t' = BTree.binsert t key ∧ TreeSeg m' nr t' ∧
        Bst none none t' ∧ key ∈ t'.flatten := by
  have hevM0 : memEvalExpr (.lit .nullptr)
      [("root", .ptrVal root), ("key", .i32 key)] m π =
      evalExpr (.lit .nullptr)
        [("root", .ptrVal root), ("key", .i32 key)] :=
    memEvalExpr_lit _ _ _ _
  have hevV0 : evalExpr (.lit .nullptr)
      [("root", .ptrVal root), ("key", .i32 key)] =
      .ok (.ptrVal none) := by
    simp [evalExpr, litVal]
  have hpar := memEvalStmtFuel_let_pure F "parent" nodeTy
    (.lit .nullptr) _ _ _ (.ptrVal none)
    (by simp) (by simp) (by simp) (by simp) hevM0 hevV0
  have hevM1 : memEvalExpr (.var "root")
      (("parent", .ptrVal none) ::
        [("root", .ptrVal root), ("key", .i32 key)]) m π =
      evalExpr (.var "root")
        (("parent", .ptrVal none) ::
          [("root", .ptrVal root), ("key", .i32 key)]) :=
    memEvalExpr_var _ _ _ _
  have hevV1 : evalExpr (.var "root")
      (("parent", .ptrVal none) ::
        [("root", .ptrVal root), ("key", .i32 key)]) =
      .ok (.ptrVal root) := by
    simp [evalExpr, envLookup]
  have hcur := memEvalStmtFuel_let_pure F "cur" nodeTy (.var "root")
    _ _ _ (.ptrVal root)
    (by simp) (by simp) (by simp) (by simp) hevM1 hevV1
  have hevM2 : memEvalExpr (.lit (.i32 0))
      (("cur", .ptrVal root) :: ("parent", .ptrVal none) ::
        [("root", .ptrVal root), ("key", .i32 key)]) m π =
      evalExpr (.lit (.i32 0))
        (("cur", .ptrVal root) :: ("parent", .ptrVal none) ::
          [("root", .ptrVal root), ("key", .i32 key)]) :=
    memEvalExpr_lit _ _ _ _
  have hevV2 : evalExpr (.lit (.i32 0))
      (("cur", .ptrVal root) :: ("parent", .ptrVal none) ::
        [("root", .ptrVal root), ("key", .i32 key)]) =
      .ok (.i32 0) := by
    simp [evalExpr, litVal]
  have hwl := memEvalStmtFuel_let_pure F "went_left" (.i 32)
    (.lit (.i32 0)) _ _ _ (.i32 0)
    (by simp) (by simp) (by simp) (by simp) hevM2 hevV2
  obtain ⟨cr, hC⟩ := bstInsertChase_ok F m hex key root t hseg hlen
    none false
  have hloop := bstInsertLoop_agree F m π hex root key none root 0 t
    hseg hlen false rfl cr hC
  cases cr with
  | dup =>
    obtain ⟨ρ', hev⟩ := hloop.2 rfl
    have hRest := memEvalStmtFuel_seq_return F
      bstInsertLoop
      (.seq bstInsertAttach (.return_ (.var "root")))
      (mkBstInsertEnv root key none root 0) m π
      ρ' m π _ hev
    have h23 := memEvalStmtFuel_seq_fallthrough_trans F
      (.let_ "cur" nodeTy (.var "root"))
      (.seq (.let_ "went_left" (.i 32) (.lit (.i32 0)))
        (.seq bstInsertLoop
          (.seq bstInsertAttach (.return_ (.var "root")))))
      (("parent", .ptrVal none) ::
        [("root", .ptrVal root), ("key", .i32 key)]) m π
      (("cur", .ptrVal root) :: ("parent", .ptrVal none) ::
        [("root", .ptrVal root), ("key", .i32 key)]) m π _
      hcur
      (memEvalStmtFuel_seq_fallthrough_trans F _ _
        (("cur", .ptrVal root) :: ("parent", .ptrVal none) ::
          [("root", .ptrVal root), ("key", .i32 key)]) m π
        (mkBstInsertEnv root key none root 0) m π _ hwl hRest)
    have hTop := memEvalStmtFuel_seq_fallthrough_trans F
      (.let_ "parent" nodeTy (.lit .nullptr))
      (.seq (.let_ "cur" nodeTy (.var "root"))
        (.seq (.let_ "went_left" (.i 32) (.lit (.i32 0)))
          (.seq bstInsertLoop
            (.seq bstInsertAttach (.return_ (.var "root"))))))
      ([("root", .ptrVal root), ("key", .i32 key)]) m π
      (("parent", .ptrVal none) ::
        [("root", .ptrVal root), ("key", .i32 key)]) m π _ hpar h23
    have hfwd' : bstInsertFwd F m root key = .ok (root, m) := by
      simp only [bstInsertFwd, hC]
    obtain ⟨nr, m', hr, t', ht', hseg', hbst', hmem'⟩ :=
      bstInsertFwd_correct F m hex hmfresh root key t hbst hseg hd
        hlen (root, m) hfwd'
    simp only [Prod.mk.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    exact ⟨ρ', root, m, hTop, t', ht', hseg', hbst', hmem'⟩
  | attach parent side =>
    have hloopA := hloop.1 parent side rfl
    obtain ⟨m1, a, hallock⟩ : ∃ m1 a, (m1, a) = memAlloc m 3 :=
      ⟨_, _, rfl⟩
    have ha : a = m.next := by
      have h2 := memAlloc_next m 3
      have h3 : a = (memAlloc m 3).2 := congrArg Prod.snd hallock
      rw [h3]; exact h2
    have hrep : List.replicate 3 (0 : BitVec 32) = [0, 0, 0] := rfl
    have hfind1 : memFind m1 a = some ⟨a, true, [0, 0, 0]⟩ := by
      have h := memFind_memAlloc m 3
      rw [hrep] at h
      have e1 : m1 = (memAlloc m 3).1 := congrArg Prod.fst hallock
      have e2 : a = (memAlloc m 3).2 := congrArg Prod.snd hallock
      rw [e1, e2]
      exact h
    have c0 : cellsAt m1 a a [0, 0, 0] := hfind1
    obtain ⟨m2, h0⟩ : ∃ m2, memStore m1 a a 0 key = .ok m2 :=
      ⟨_, memStore_cellsAt m1 a a 0 [0, 0, 0] key c0 (by simp)⟩
    have e0 : ([0, 0, 0].set 0 key) = [key, 0, 0] := by simp
    have c1 : cellsAt m2 a a [key, 0, 0] := by
      have hc := memFind_cellsAt_store m1 a a 0 [0, 0, 0] key m2
        c0 (by simp) h0
      rw [e0] at hc
      exact hc
    obtain ⟨m3, h1⟩ : ∃ m3,
        memStore m2 a a 1 (linkWord none) = .ok m3 :=
      ⟨_, memStore_cellsAt m2 a a 1 [key, 0, 0] (linkWord none)
        c1 (by simp)⟩
    have e1 : ([key, (0 : BitVec 32), 0].set 1 (linkWord none)) =
        [key, 0, 0] := by simp [linkWord_none]
    have c2 : cellsAt m3 a a [key, 0, 0] := by
      have hc := memFind_cellsAt_store m2 a a 1 [key, 0, 0]
        (linkWord none) m3 c1 (by simp) h1
      rw [e1] at hc
      exact hc
    obtain ⟨m4, h2⟩ : ∃ m4,
        memStore m3 a a 2 (linkWord none) = .ok m4 :=
      ⟨_, memStore_cellsAt m3 a a 2 [key, 0, 0] (linkWord none)
        c2 (by simp)⟩
    have hpath := bstInsertChase_at_mem F m hex root key none false
      parent side t hC hseg
    rcases hpath with hpath | hpath
    · subst parent
      -- Empty tree: attach the fresh node as the new root.
      have hnd := memEvalStmtFuel_let_nnew3 F "nd" nodeTy
        (mkBstInsertEnv root key none none (if side then 1 else 0))
        m π
      rw [← hallock] at hnd
      dsimp only at hnd
      have hndE : envLookup
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key none none (if side then 1 else 0))
          "nd" = some (.ptrVal (some a)) := by
        simp [envLookup]
      have hndV : memEvalExpr (.var "nd")
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key none none (if side then 1 else 0))
          m1 π = .ok (.ptrVal (some a)) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ hndE
      have hkeyV : memEvalExpr (.var "key")
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key none none (if side then 1 else 0))
          m1 π = .ok (.i32 key) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _
          (by simp [envLookup, mkBstInsertEnv])
      have hpsV := memEvalStmtFuel_psetVal_ok F (.var "nd")
        (.var "key")
        (("nd", .ptrVal (some a)) ::
          mkBstInsertEnv root key none none (if side then 1 else 0))
        m1 π (a) (key) (⟨a, true, [0, 0, 0]⟩) (m2)
        hndV hkeyV hfind1 h0
      have hnullE1 : memEvalExpr (.lit .nullptr)
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key none none (if side then 1 else 0))
          m2 π = .ok (.ptrVal none) := by
        simp [memEvalExpr, litVal]
      have hndV2 : memEvalExpr (.var "nd")
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key none none (if side then 1 else 0))
          m2 π = .ok (.ptrVal (some a)) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ hndE
      have hfind2 : memFind m2 a = some ⟨a, true, [key, 0, 0]⟩ := c1
      have hpsN := memEvalStmtFuel_psetNext_ok F (.var "nd")
        (.lit .nullptr)
        (("nd", .ptrVal (some a)) ::
          mkBstInsertEnv root key none none (if side then 1 else 0))
        m2 π a none (⟨a, true, [key, 0, 0]⟩) (m3)
        hndV2 hnullE1 hfind2 h1
      have hfind3 : memFind m3 a = some ⟨a, true, [key, 0, 0]⟩ := c2
      have hndV3 : memEvalExpr (.var "nd")
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key none none (if side then 1 else 0))
          m3 π = .ok (.ptrVal (some a)) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ hndE
      have hnullE2 : memEvalExpr (.lit .nullptr)
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key none none (if side then 1 else 0))
          m3 π = .ok (.ptrVal none) := by
        simp [memEvalExpr, evalExpr, litVal]
      have hpsR := memEvalStmtFuel_psetRight_ok F (.var "nd")
        (.lit .nullptr)
        (("nd", .ptrVal (some a)) ::
          mkBstInsertEnv root key none none (if side then 1 else 0))
        m3 π a none (⟨a, true, [key, 0, 0]⟩) (m4)
        hndV3 hnullE2 hfind3 h2
      have hparE : memEvalExpr (.var "parent")
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key none none (if side then 1 else 0))
          m4 π = .ok (.ptrVal none) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _
          (by simp [envLookup, mkBstInsertEnv])
      have hnullE3 : memEvalExpr (.lit .nullptr)
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key none none (if side then 1 else 0))
          m4 π = .ok (.ptrVal none) := by
        simp [memEvalExpr, evalExpr, litVal]
      have hueqT : memEvalExpr
          (.ueq (.var "parent") (.lit .nullptr))
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key none none (if side then 1 else 0))
          m4 π = .ok (.b true) := by
        have h := memEvalExpr_ueq_ptrVal _ _ _ _ _ _ _ hparE hnullE3
        simpa using h
      have hndV4 : memEvalExpr (.var "nd")
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key none none (if side then 1 else 0))
          m4 π = .ok (.ptrVal (some a)) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ hndE
      have hevR0 : memEvalExpr (.var "nd")
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key none none (if side then 1 else 0))
          m4 π =
          evalExpr (.var "nd")
            (("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key none none
                (if side then 1 else 0)) :=
        memEvalExpr_var _ _ _ _
      have hevRV0 : evalExpr (.var "nd")
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key none none (if side then 1 else 0)) =
          .ok (.ptrVal (some a)) :=
        evalExpr_var_hit _ _ _ hndE
      have hret := memEvalStmtFuel_return F (.var "nd")
        (("nd", .ptrVal (some a)) ::
          mkBstInsertEnv root key none none (if side then 1 else 0))
        m4 π _ hevR0 hevRV0
      have hifT : memEvalStmtFuel F
          (.if_ (.ueq (.var "parent") (.lit .nullptr))
            (.return_ (.var "nd"))
            (.if_ (.une (.var "went_left") (.lit (.i32 0)))
              (.psetNext (.var "parent") (.var "nd"))
              (.psetRight (.var "parent") (.var "nd"))))
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key none none (if side then 1 else 0))
          m4 π =
          memEvalStmtFuel F (.return_ (.var "nd"))
            (("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key none none (if side then 1 else 0))
            m4 π :=
        memEvalStmtFuel_if_true _ _ _ _ _ _ _ hueqT
      have hbodyA := hifT.trans hret
      have hseqR := memEvalStmtFuel_seq_fallthrough_trans F _ _
        (("nd", .ptrVal (some a)) ::
          mkBstInsertEnv root key none none (if side then 1 else 0))
        m3 π
        (("nd", .ptrVal (some a)) ::
          mkBstInsertEnv root key none none (if side then 1 else 0))
        m4 π _ hpsR hbodyA
      have hseqN := memEvalStmtFuel_seq_fallthrough_trans F _ _
        (("nd", .ptrVal (some a)) ::
          mkBstInsertEnv root key none none (if side then 1 else 0))
        m2 π
        (("nd", .ptrVal (some a)) ::
          mkBstInsertEnv root key none none (if side then 1 else 0))
        m3 π _ hpsN hseqR
      have hseqV := memEvalStmtFuel_seq_fallthrough_trans F _ _
        (("nd", .ptrVal (some a)) ::
          mkBstInsertEnv root key none none (if side then 1 else 0))
        m1 π
        (("nd", .ptrVal (some a)) ::
          mkBstInsertEnv root key none none (if side then 1 else 0))
        m2 π _ hpsV hseqN
      have hattach := memEvalStmtFuel_seq_fallthrough_trans F _ _
        (mkBstInsertEnv root key none none (if side then 1 else 0))
        m π
        (("nd", .ptrVal (some a)) ::
          mkBstInsertEnv root key none none (if side then 1 else 0))
        m1 π _ hnd hseqV
      have hRestA := memEvalStmtFuel_seq_return F
        bstInsertAttach (.return_ (.var "root"))
        (mkBstInsertEnv root key none none (if side then 1 else 0)) m π
        (("nd", .ptrVal (some a)) ::
          mkBstInsertEnv root key none none (if side then 1 else 0))
        m4 π _ hattach
      have hLoopSeq := memEvalStmtFuel_seq_fallthrough_trans F _ _
        (mkBstInsertEnv root key none root 0) m π
        (mkBstInsertEnv root key none none (if side then 1 else 0)) m π _
        hloopA hRestA
      have hpre := memEvalStmtFuel_seq_fallthrough_trans F _ _
        ([("root", .ptrVal root), ("key", .i32 key)]) m π
        ([("parent", .ptrVal none)] ++
          [("root", .ptrVal root), ("key", .i32 key)]) m π _
        hpar
        (memEvalStmtFuel_seq_fallthrough_trans F _ _
          ([("parent", .ptrVal none)] ++
            [("root", .ptrVal root), ("key", .i32 key)]) m π
          (("cur", .ptrVal root) :: ("parent", .ptrVal none) ::
            [("root", .ptrVal root), ("key", .i32 key)]) m π _
          hcur
          (memEvalStmtFuel_seq_fallthrough_trans F _ _
            (("cur", .ptrVal root) :: ("parent", .ptrVal none) ::
              [("root", .ptrVal root), ("key", .i32 key)]) m π
            (mkBstInsertEnv root key none root 0) m π _
            hwl hLoopSeq))
      have hfwd' : bstInsertFwd F m root key = .ok (some a, m4) := by
        unfold bstInsertFwd
        rw [hC]
        simp only []
        rw [← hallock]
        dsimp only
        simp only [h0, h1, h2]
      obtain ⟨nr, m', hr, t', ht', hseg', hbst', hmem'⟩ :=
        bstInsertFwd_correct F m hex hmfresh root key t hbst hseg hd
          hlen (some a, m4) hfwd'
      simp only [Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨_, _, _, hpre, t', ht', hseg', hbst', hmem'⟩
    · obtain ⟨a', hpa', hmem⟩ := hpath
      subst parent
      -- (parent is now `some a'` everywhere)
      obtain ⟨tp, kp, lp, rp, hpp⟩ := TreeSegMem_nodeAt3' hmem
      have hnode4 := node_to_m4 hpp m1 m2 m3 m4 a hallock hmfresh
        ha key (linkWord none) (linkWord none) h0 h1 h2
      have hfind4 : memFind m4 a' =
          some ⟨tp, true, [kp, linkWord lp, linkWord rp]⟩ := hnode4
      obtain ⟨b, hfind4b⟩ : ∃ b, memFind m4 a' = some b :=
        ⟨_, hfind4⟩
      have htag : b.tag = tp := by
        rw [hfind4] at hfind4b
        simp only [Option.some.injEq] at hfind4b
        exact congrArg Block.tag hfind4b.symm
      have hnd := memEvalStmtFuel_let_nnew3 F "nd" nodeTy
        (mkBstInsertEnv root key (some a') none (if side then 1 else 0))
        m π
      rw [← hallock] at hnd
      dsimp only at hnd
      have hndE : envLookup
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none
              (if side then 1 else 0))
          "nd" = some (.ptrVal (some a)) := by
        simp [envLookup]
      have hndV : memEvalExpr (.var "nd")
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none
              (if side then 1 else 0))
          m1 π = .ok (.ptrVal (some a)) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ hndE
      have hkeyV : memEvalExpr (.var "key")
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none
              (if side then 1 else 0))
          m1 π = .ok (.i32 key) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _
          (by simp [envLookup, mkBstInsertEnv])
      have hpsV := memEvalStmtFuel_psetVal_ok F (.var "nd")
        (.var "key")
        (("nd", .ptrVal (some a)) ::
          mkBstInsertEnv root key (some a') none (if side then 1 else 0))
        m1 π (a) (key) (⟨a, true, [0, 0, 0]⟩) (m2)
        hndV hkeyV hfind1 h0
      have hnullE1 : memEvalExpr (.lit .nullptr)
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if side then 1 else 0))
          m2 π = .ok (.ptrVal none) := by
        simp [memEvalExpr, litVal]
      have hndV2 : memEvalExpr (.var "nd")
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if side then 1 else 0))
          m2 π = .ok (.ptrVal (some a)) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ hndE
      have hfind2 : memFind m2 a = some ⟨a, true, [key, 0, 0]⟩ := c1
      have hpsN := memEvalStmtFuel_psetNext_ok F (.var "nd")
        (.lit .nullptr)
        (("nd", .ptrVal (some a)) ::
          mkBstInsertEnv root key (some a') none (if side then 1 else 0))
        m2 π a none (⟨a, true, [key, 0, 0]⟩) (m3)
        hndV2 hnullE1 hfind2 h1
      have hfind3 : memFind m3 a = some ⟨a, true, [key, 0, 0]⟩ := c2
      have hndV3 : memEvalExpr (.var "nd")
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if side then 1 else 0))
          m3 π = .ok (.ptrVal (some a)) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ hndE
      have hnullE2 : memEvalExpr (.lit .nullptr)
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if side then 1 else 0))
          m3 π = .ok (.ptrVal none) := by
        simp [memEvalExpr, litVal]
      have hpsR := memEvalStmtFuel_psetRight_ok F (.var "nd")
        (.lit .nullptr)
        (("nd", .ptrVal (some a)) ::
          mkBstInsertEnv root key (some a') none (if side then 1 else 0))
        m3 π a none (⟨a, true, [key, 0, 0]⟩) (m4)
        hndV3 hnullE2 hfind3 h2
      have hparE : memEvalExpr (.var "parent")
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if side then 1 else 0))
          m4 π = .ok (.ptrVal (some a')) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _
          (by simp [envLookup, mkBstInsertEnv])
      have hnullE3 : memEvalExpr (.lit .nullptr)
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if side then 1 else 0))
          m4 π = .ok (.ptrVal none) := by
        simp [memEvalExpr, litVal]
      have hueqF : memEvalExpr
          (.ueq (.var "parent") (.lit .nullptr))
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if side then 1 else 0))
          m4 π = .ok (.b false) := by
        have h := memEvalExpr_ueq_ptrVal _ _ _ _ _ _ _ hparE hnullE3
        simpa using h
      have hifF : memEvalStmtFuel F
          (.if_ (.ueq (.var "parent") (.lit .nullptr))
            (.return_ (.var "nd"))
            (.if_ (.une (.var "went_left") (.lit (.i32 0)))
              (.psetNext (.var "parent") (.var "nd"))
              (.psetRight (.var "parent") (.var "nd"))))
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if side then 1 else 0))
          m4 π =
          memEvalStmtFuel F
            (.if_ (.une (.var "went_left") (.lit (.i32 0)))
              (.psetNext (.var "parent") (.var "nd"))
              (.psetRight (.var "parent") (.var "nd")))
            (("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if side then 1 else 0))
          m4 π :=
        memEvalStmtFuel_if_false _ _ _ _ _ _ _ hueqF
      cases side with
      | true =>
        have hwlE : memEvalExpr (.var "went_left")
            (("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if true then 1 else 0))
            m4 π = .ok (.i32 1) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _
            (by simp [envLookup, mkBstInsertEnv])
        have hzE : memEvalExpr (.lit (.i32 0))
            (("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if true then 1 else 0))
            m4 π = .ok (.i32 0) := by
          simp [memEvalExpr, evalExpr, litVal]
        have haA : memEvalExpr (.var "went_left")
            (("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if true then 1 else 0))
            m4 π =
            evalExpr (.var "went_left")
              (("nd", .ptrVal (some a)) ::
                mkBstInsertEnv root key (some a') none
                  (if true then 1 else 0)) :=
          memEvalExpr_var _ _ _ _
        have hbA : memEvalExpr (.lit (.i32 0))
            (("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if true then 1 else 0))
            m4 π =
            evalExpr (.lit (.i32 0))
              (("nd", .ptrVal (some a)) ::
                mkBstInsertEnv root key (some a') none
                  (if true then 1 else 0)) :=
          memEvalExpr_lit _ _ _ _
        have huneM := memEvalExpr_une_agree _ _ _ _ _ haA hbA
        have hwlV : evalExpr (.var "went_left")
            (("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if true then 1 else 0)) =
            .ok (.i32 1) := by
          rw [← haA]; exact hwlE
        have hzV : evalExpr (.lit (.i32 0))
            (("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if true then 1 else 0)) =
            .ok (.i32 0) := by
          rw [← hbA]; exact hzE
        have huneT : memEvalExpr
            (.une (.var "went_left") (.lit (.i32 0)))
            (("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if true then 1 else 0))
            m4 π = .ok (.b true) := by
          have h1ne : ((1 : BitVec 32) != 0) = true := by decide
          have hv := evalExpr_une_i32 _ _ _ _ _ hwlV hzV
          rw [huneM, hv, h1ne]
        have hifT2 : memEvalStmtFuel F
            (.if_ (.une (.var "went_left") (.lit (.i32 0)))
              (.psetNext (.var "parent") (.var "nd"))
              (.psetRight (.var "parent") (.var "nd")))
            (("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if true then 1 else 0))
            m4 π =
            memEvalStmtFuel F
              (.psetNext (.var "parent") (.var "nd"))
              (("nd", .ptrVal (some a)) ::
                mkBstInsertEnv root key (some a') none
                  (if true then 1 else 0))
              m4 π :=
          memEvalStmtFuel_if_true _ _ _ _ _ _ _ huneT
        have hc4 : cellsAt m4 a' b.tag [kp, linkWord lp, linkWord rp] := by
          rw [htag]; exact hnode4
        obtain ⟨m5L, hAlt⟩ : ∃ m5L, memStore m4 a' b.tag 1
            (linkWord (some a)) = .ok m5L := by
          have h3 : [kp, linkWord lp, linkWord rp].length = 3 := rfl
          have hlt1 : (1 : Nat) < [kp, linkWord lp, linkWord rp].length := by
            rw [h3]; decide
          exact ⟨_, memStore_cellsAt m4 a' b.tag 1
            [kp, linkWord lp, linkWord rp] (linkWord (some a)) hc4 hlt1⟩
        have hparE' : memEvalExpr (.var "parent")
            (("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if true then 1 else 0))
            m4 π = .ok (.ptrVal (some a')) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _
            (by simp [envLookup, mkBstInsertEnv])
        have hndV4' : memEvalExpr (.var "nd")
            (("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if true then 1 else 0))
            m4 π = .ok (.ptrVal (some a)) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _ hndE
        have hattachP := memEvalStmtFuel_psetNext_ok F (.var "parent")
          (.var "nd")
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if true then 1 else 0))
          m4 π a' (some a) (b) (m5L)
          hparE' hndV4' hfind4b hAlt
        have hRestL := hifF.trans (hifT2.trans hattachP)
        have hseqR := memEvalStmtFuel_seq_fallthrough_trans F _ _
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if true then 1 else 0))
          m3 π
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if true then 1 else 0))
          m4 π _ hpsR hRestL
        have hseqN := memEvalStmtFuel_seq_fallthrough_trans F _ _
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if true then 1 else 0))
          m2 π
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if true then 1 else 0))
          m3 π _ hpsN hseqR
        have hseqV := memEvalStmtFuel_seq_fallthrough_trans F _ _
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if true then 1 else 0))
          m1 π
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if true then 1 else 0))
          m2 π _ hpsV hseqN
        have hattach := memEvalStmtFuel_seq_fallthrough_trans F _ _
          (mkBstInsertEnv root key (some a') none (if true then 1 else 0))
          m π
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if true then 1 else 0))
          m1 π _ hnd hseqV
        have hretR : envLookup
            (("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if true then 1 else 0))
            "root" = some (.ptrVal root) := by
          simp [envLookup, mkBstInsertEnv]
        have hevR : memEvalExpr (.var "root")
            (("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if true then 1 else 0))
            m5L π =
            evalExpr (.var "root")
              (("nd", .ptrVal (some a)) ::
                mkBstInsertEnv root key (some a') none
                  (if true then 1 else 0)) :=
          memEvalExpr_var _ _ _ _
        have hevRV : evalExpr (.var "root")
            (("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if true then 1 else 0)) =
            .ok (.ptrVal root) := by
          exact evalExpr_var_hit _ _ _ hretR
        have htail := memEvalStmtFuel_return F (.var "root")
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if true then 1 else 0))
          m5L π _ hevR hevRV
        have hRestA := memEvalStmtFuel_seq_fallthrough_trans F _ _
          (mkBstInsertEnv root key (some a') none (if true then 1 else 0))
          m π
          (("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if true then 1 else 0))
          m5L π _ hattach htail
        have hLoopSeq := memEvalStmtFuel_seq_fallthrough_trans F _ _
          (mkBstInsertEnv root key none root 0) m π
          (mkBstInsertEnv root key (some a') none (if true then 1 else 0))
          m π _ hloopA hRestA
        have hLoopSeq2 : memEvalStmtFuel F
            (bstInsertLoop.seq (bstInsertAttach.seq (.return_ (.var "root"))))
            (mkBstInsertEnv root key none root 0) m π =
            .ok ((("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none
                (if true then 1 else 0), m5L, π),
              .returned (.ptrVal root)) := hLoopSeq
        have hseq3 := memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _
          hwl hLoopSeq2
        have hseq2 := memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _
          hcur hseq3
        have hTop : memEvalStmtFuel F bstInsertBody
            ([("root", .ptrVal root), ("key", .i32 key)]) m π =
            .ok ((("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none
                (if true then 1 else 0), m5L, π),
              .returned (.ptrVal root)) :=
          memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _ hpar hseq2
        have hfwd' : bstInsertFwd F m root key = .ok (root, m5L) := by
          unfold bstInsertFwd
          rw [hC]
          simp only []
          rw [← hallock]
          dsimp only
          rw [h0]
          simp only []
          rw [h1]
          simp only []
          rw [h2]
          simp only []
          rw [hfind4b]
          simp only []
          rw [show ((if True then (1 : Nat) else 2)) = 1 from rfl, hAlt]
        obtain ⟨nr, m', hr, t', ht', hseg', hbst', hmem'⟩ :=
          bstInsertFwd_correct F m hex hmfresh root key t hbst hseg hd
            hlen (root, m5L) hfwd'
        simp only [Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        have hTopBody : memEvalStmtFuel F bstInsertFunc.body
            ([("root", .ptrVal root), ("key", .i32 key)]) m π =
            .ok ((("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none
                (if true then 1 else 0), m5L, π),
              .returned (.ptrVal root)) := hTop
        exact ⟨_, _, _, hTopBody, t', ht', hseg', hbst', hmem'⟩
      | false =>
        have hwlE : memEvalExpr (.var "went_left")
            ((("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if false then 1 else 0)))
            m4 π = .ok (.i32 0) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _
            (by simp [envLookup, mkBstInsertEnv])
        have hzE : memEvalExpr (.lit (.i32 0))
            ((("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if false then 1 else 0)))
            m4 π = .ok (.i32 0) := by
          simp [memEvalExpr, evalExpr, litVal]
        have haA : memEvalExpr (.var "went_left")
            ((("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if false then 1 else 0)))
            m4 π =
            evalExpr (.var "went_left")
              ((("nd", .ptrVal (some a)) ::
                mkBstInsertEnv root key (some a') none
                  (if false then 1 else 0))) :=
          memEvalExpr_var _ _ _ _
        have hbA : memEvalExpr (.lit (.i32 0))
            ((("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if false then 1 else 0)))
            m4 π =
            evalExpr (.lit (.i32 0))
              ((("nd", .ptrVal (some a)) ::
                mkBstInsertEnv root key (some a') none
                  (if false then 1 else 0))) :=
          memEvalExpr_lit _ _ _ _
        have huneM := memEvalExpr_une_agree _ _ _ _ _ haA hbA
        have hwlV : evalExpr (.var "went_left")
            ((("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if false then 1 else 0))) =
            .ok (.i32 0) := by
          rw [← haA]; exact hwlE
        have hzV : evalExpr (.lit (.i32 0))
            ((("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if false then 1 else 0))) =
            .ok (.i32 0) := by
          rw [← hbA]; exact hzE
        have huneF : memEvalExpr
            (.une (.var "went_left") (.lit (.i32 0)))
            ((("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if false then 1 else 0)))
            m4 π = .ok (.b false) := by
          have h0ne : ((0 : BitVec 32) != 0) = false := by decide
          have hv := evalExpr_une_i32 _ _ _ _ _ hwlV hzV
          rw [huneM, hv, h0ne]
        have hifF2 : memEvalStmtFuel F
            (.if_ (.une (.var "went_left") (.lit (.i32 0)))
              (.psetNext (.var "parent") (.var "nd"))
              (.psetRight (.var "parent") (.var "nd")))
            ((("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if false then 1 else 0)))
            m4 π =
            memEvalStmtFuel F
              (.psetRight (.var "parent") (.var "nd"))
              ((("nd", .ptrVal (some a)) ::
                mkBstInsertEnv root key (some a') none
                  (if false then 1 else 0)))
              m4 π :=
          memEvalStmtFuel_if_false _ _ _ _ _ _ _ huneF
        have hc4 : cellsAt m4 a' b.tag [kp, linkWord lp, linkWord rp] := by
          rw [htag]; exact hnode4
        obtain ⟨m5R, hAltR⟩ : ∃ m5R, memStore m4 a' b.tag 2
            (linkWord (some a)) = .ok m5R := by
          have h3 : [kp, linkWord lp, linkWord rp].length = 3 := rfl
          have hlt2 : (2 : Nat) < [kp, linkWord lp, linkWord rp].length := by
            rw [h3]; decide
          exact ⟨_, memStore_cellsAt m4 a' b.tag 2
            [kp, linkWord lp, linkWord rp] (linkWord (some a)) hc4 hlt2⟩
        have hparE' : memEvalExpr (.var "parent")
            ((("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if false then 1 else 0)))
            m4 π = .ok (.ptrVal (some a')) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _
            (by simp [envLookup, mkBstInsertEnv])
        have hndV4' : memEvalExpr (.var "nd")
            ((("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if false then 1 else 0)))
            m4 π = .ok (.ptrVal (some a)) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _ hndE
        have hattachPR := memEvalStmtFuel_psetRight_ok F (.var "parent")
          (.var "nd")
          ((("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if false then 1 else 0)))
          m4 π a' (some a) (b) (m5R)
          hparE' hndV4' hfind4b hAltR
        have hRestR := hifF.trans (hifF2.trans hattachPR)
        have hseqR := memEvalStmtFuel_seq_fallthrough_trans F _ _
          ((("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if false then 1 else 0)))
          m3 π
          ((("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if false then 1 else 0)))
          m4 π _ hpsR hRestR
        have hseqN := memEvalStmtFuel_seq_fallthrough_trans F _ _
          ((("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if false then 1 else 0)))
          m2 π
          ((("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if false then 1 else 0)))
          m3 π _ hpsN hseqR
        have hseqV := memEvalStmtFuel_seq_fallthrough_trans F _ _
          ((("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if false then 1 else 0)))
          m1 π
          ((("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if false then 1 else 0)))
          m2 π _ hpsV hseqN
        have hattach := memEvalStmtFuel_seq_fallthrough_trans F _ _
          (mkBstInsertEnv root key (some a') none (if false then 1 else 0))
          m π
          ((("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if false then 1 else 0)))
          m1 π _ hnd hseqV
        have hretR : envLookup
            ((("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if false then 1 else 0)))
            "root" = some (.ptrVal root) := by
          simp [envLookup, mkBstInsertEnv]
        have hevR : memEvalExpr (.var "root")
            ((("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none (if false then 1 else 0)))
            m5R π =
            evalExpr (.var "root")
              ((("nd", .ptrVal (some a)) ::
                mkBstInsertEnv root key (some a') none
                  (if false then 1 else 0))) :=
          memEvalExpr_var _ _ _ _
        have hevRV : evalExpr (.var "root")
            ((("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none
                (if false then 1 else 0))) =
            .ok (.ptrVal root) := by
          exact evalExpr_var_hit _ _ _ hretR
        have htail := memEvalStmtFuel_return F (.var "root")
          ((("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if false then 1 else 0)))
          m5R π _ hevR hevRV
        have hRestA := memEvalStmtFuel_seq_fallthrough_trans F _ _
          (mkBstInsertEnv root key (some a') none (if false then 1 else 0))
          m π
          ((("nd", .ptrVal (some a)) ::
            mkBstInsertEnv root key (some a') none (if false then 1 else 0)))
          m5R π _ hattach htail
        have hLoopSeq := memEvalStmtFuel_seq_fallthrough_trans F _ _
          (mkBstInsertEnv root key none root 0) m π
          (mkBstInsertEnv root key (some a') none (if false then 1 else 0))
          m π _ hloopA hRestA
        have hLoopSeq2 : memEvalStmtFuel F
            (bstInsertLoop.seq (bstInsertAttach.seq (.return_ (.var "root"))))
            (mkBstInsertEnv root key none root 0) m π =
            .ok (((("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none
                (if false then 1 else 0), m5R, π)),
              .returned (.ptrVal root)) := hLoopSeq
        have hseq3 := memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _
          hwl hLoopSeq2
        have hseq2 := memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _
          hcur hseq3
        have hTop : memEvalStmtFuel F bstInsertBody
            ([("root", .ptrVal root), ("key", .i32 key)]) m π =
            .ok (((("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none
                (if false then 1 else 0), m5R, π)),
              .returned (.ptrVal root)) :=
          memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _ hpar hseq2
        have hfwd' : bstInsertFwd F m root key = .ok (root, m5R) := by
          unfold bstInsertFwd
          rw [hC]
          simp only []
          rw [← hallock]
          dsimp only
          rw [h0]
          simp only []
          rw [h1]
          simp only []
          rw [h2]
          simp only []
          rw [hfind4b]
          simp only []
          rw [show ((if false = true then (1 : Nat) else 2)) = 2 from rfl,
            hAltR]
        obtain ⟨nr, m', hr, t', ht', hseg', hbst', hmem'⟩ :=
          bstInsertFwd_correct F m hex hmfresh root key t hbst hseg hd
            hlen (root, m5R) hfwd'
        simp only [Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        have hTopBody : memEvalStmtFuel F bstInsertFunc.body
            ([("root", .ptrVal root), ("key", .i32 key)]) m π =
            .ok (((("nd", .ptrVal (some a)) ::
              mkBstInsertEnv root key (some a') none
                (if false then 1 else 0), m5R, π)),
              .returned (.ptrVal root)) := hTop
        exact ⟨_, _, _, hTopBody, t', ht', hseg', hbst', hmem'⟩
