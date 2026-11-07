import Circe.Emit.LinkedReverse
import Circe.Emit.ListSortedInsert
import Circe.Mem.LinkedList

/-- Pillar-1 proposed goal #1: sorted merge of two chains
    (`list_merge`, the first multi-input traversal).
    `Node *list_merge(Node * __restrict__ a, Node * __restrict__ b)`
    splices two ascending chains into one ascending chain by
    relinking: null-entry early returns, a head-seed pick on
    `a->val <= b->val`, a two-cursor chase swinging
    `tail->next` at the smaller head each iteration, and a
    remainder splice attaching the surviving suffix. No
    `malloc`/`free` (destructive relink only); `new` is not
    used. Both params carry `__restrict__` (two live pointers
    can always alias, so uniqueness is claimed in the text and
    corroborated by a `noalias` oracle verdict). Faults are
    loud (miss/tag/liveness checks); cycles and aliasing are
    out of scope (the contract assumes two acyclic,
    pairwise-disjoint input chains). -/
def listMergeName : String :=
  "_Z10list_mergeP4NodeS0_"

/-! ## Spec: two-chain merge oracle (pure) -/

/-- Pure oracle: stable merge of two ascending payload lists.
    Take from `a` unless `b` is strictly smaller (`b.slt a`) —
    the take-from-`a` tie rule matching `a->val <= b->val`. -/
def mergeChains : List (BitVec 32) → List (BitVec 32) → List (BitVec 32)
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs =>
    if b.slt a then b :: mergeChains (a :: as) bs
    else a :: mergeChains as (b :: bs)
termination_by as bs => as.length + bs.length

/-- Cons equations at a pick (stable take-from-`a` on ties):
    rewrite-only forms of the splitter arms. -/
theorem mergeChains_cons_takeB (a : BitVec 32) (as : List (BitVec 32))
    (b : BitVec 32) (bs : List (BitVec 32)) (h : (b.slt a) = true) :
    mergeChains (a :: as) (b :: bs) = b :: mergeChains (a :: as) bs := by
  simp [mergeChains, h]

/-- Nil arms as rewrite rules (the equation compiler keeps side
    conditions on the overlapping arms, so these are stated
    explicitly for variable inputs). -/
theorem mergeChains_nil_right (as : List (BitVec 32)) :
    mergeChains as [] = as := by
  cases as <;> simp [mergeChains]

theorem mergeChains_nil_left (bs : List (BitVec 32)) :
    mergeChains [] bs = bs := by
  simp [mergeChains]

theorem mergeChains_cons_takeA (a : BitVec 32) (as : List (BitVec 32))
    (b : BitVec 32) (bs : List (BitVec 32)) (h : (b.slt a) = false) :
    mergeChains (a :: as) (b :: bs) = a :: mergeChains as (b :: bs) := by
  have h' : ¬(b.slt a) = true := by simpa using h
  simp [mergeChains, h']

/-- The merge holds exactly the input payloads. -/
theorem mergeChains_length (as bs : List (BitVec 32)) :
    (mergeChains as bs).length = as.length + bs.length := by
  induction as, bs using mergeChains.induct
  · rename_i bs
    cases bs <;> simp [mergeChains]
  · rename_i as hne
    cases as with
    | nil => exact absurd rfl hne
    | cons a as => simp [mergeChains]
  · rename_i a as b bs h ih
    rw [mergeChains_cons_takeB a as b bs h]
    simp only [List.length_cons, ih]
    omega
  · rename_i a as b bs h ih
    have h' : (b.slt a) = false := Bool.eq_false_of_ne_true h
    rw [mergeChains_cons_takeA a as b bs h']
    simp only [List.length_cons, ih]
    omega

/-- A head cons permutes past an append (the pick-step
    commutation used at both merge picks). -/
theorem perm_cons_append_middle (x : BitVec 32) (l₁ l₂ : List (BitVec 32)) :
    List.Perm (x :: (l₁ ++ l₂)) (l₁ ++ (x :: l₂)) := by
  induction l₁ with
  | nil => exact List.Perm.rfl
  | cons y ys ih =>
    show List.Perm (x :: (y :: (ys ++ l₂))) (y :: (ys ++ (x :: l₂)))
    exact (List.Perm.swap x y _).symm.trans (List.Perm.cons y ih)

/-! ## CoreIR: two-cursor splice -/

/-- Seed pick: take `b` iff `b.val < a.val` (stable take-from-`a`
    on ties); the head and that cursor advance. -/
def listMergeSeed : CStmt :=
  (.if_ (.slt (.pgetVal (.var "b")) (.pgetVal (.var "a")))
    (.seq (.assign "head" (.var "b"))
      (.assign "b" (.pgetNext (.var "b"))))
    (.seq (.assign "head" (.var "a"))
      (.assign "a" (.pgetNext (.var "a")))))

/-- One chase iteration: swing `tail.next` at the smaller head,
    advance that cursor, follow the tail. -/
def listMergeIter : CStmt :=
  (.seq (.if_ (.slt (.pgetVal (.var "b")) (.pgetVal (.var "a")))
           (.seq (.psetNext (.var "tail") (.var "b"))
             (.assign "b" (.pgetNext (.var "b"))))
           (.seq (.psetNext (.var "tail") (.var "a"))
             (.assign "a" (.pgetNext (.var "a")))))
    (.assign "tail" (.pgetNext (.var "tail"))))

/-- The chase loop: both cursors non-null (short-circuit `&&`
    as nested `tif`, the sorted-insert idiom). -/
def listMergeLoop : CStmt :=
  (.while_ (.tif (.une (.var "a") (.lit .nullptr))
              (.tif (.une (.var "b") (.lit .nullptr))
                (.lit (.b true))
                (.lit (.b false)))
              (.lit (.b false)))
    listMergeIter)

/-- Canonical CoreIR for `list_merge`: null-entry early returns,
    head/tail slots, seed pick, tail init, chase, remainder
    splice (a null `a` splices the null link — chain end), and
    the head return. -/
def listMergeBody : CStmt :=
  (.seq (.if_ (.ueq (.var "a") (.lit .nullptr))
            (.return_ (.var "b"))
            .skip)
    (.seq (.if_ (.ueq (.var "b") (.lit .nullptr))
              (.return_ (.var "a"))
              .skip)
      (.seq (.let_ "head" nodeTy (.lit .nullptr))
        (.seq (.let_ "tail" nodeTy (.lit .nullptr))
          (.seq listMergeSeed
            (.seq (.assign "tail" (.var "head"))
              (.seq listMergeLoop
                (.seq (.if_ (.une (.var "a") (.lit .nullptr))
                        (.psetNext (.var "tail") (.var "a"))
                        (.psetNext (.var "tail") (.var "b")))
                  (.return_ (.var "head"))))))))))

/-- The merge entry: two `Node*` in, the merged `Node*` out. -/
def listMergeFunc : Func :=
  ⟨listMergeName,
   [{ name := "a", ty := nodeTy, role := .owned },
    { name := "b", ty := nodeTy, role := .owned }],
   nodeTy,
   listMergeBody⟩

/-- Merge environment: params `a`, `b` bound at entry, then the
    `head`/`tail` lets cons on the front. -/
def mkListMergeEnv (a b head tail : Option Addr) : Env :=
  [("tail", .ptrVal tail), ("head", .ptrVal head),
    ("b", .ptrVal b), ("a", .ptrVal a)]

theorem mkListMergeEnv_a (a b head tail : Option Addr) :
    envLookup (mkListMergeEnv a b head tail) "a" =
      some (.ptrVal a) := by
  simp [mkListMergeEnv, envLookup]

theorem mkListMergeEnv_b (a b head tail : Option Addr) :
    envLookup (mkListMergeEnv a b head tail) "b" =
      some (.ptrVal b) := by
  simp [mkListMergeEnv, envLookup]

theorem mkListMergeEnv_head (a b head tail : Option Addr) :
    envLookup (mkListMergeEnv a b head tail) "head" =
      some (.ptrVal head) := by
  simp [mkListMergeEnv, envLookup]

theorem mkListMergeEnv_tail (a b head tail : Option Addr) :
    envLookup (mkListMergeEnv a b head tail) "tail" =
      some (.ptrVal tail) := by
  simp [mkListMergeEnv, envLookup]

/-! ## Forward mirror (two-cursor chase with tail swing) -/

/-- Merge chase: while both cursors are live, read both payloads
    (loud on miss) and swing `tail.next` at the smaller head —
    take-from-`b` iff `b.val < a.val`, stable take-from-`a` on
    ties — advancing that cursor and following the tail. Fuel
    gates the pick (copy-style: the remaining length bounds
    fuel). Stops with one side exhausted; the entry splices the
    survivor. -/
def listMergeChase (F : Nat) (m : Mem) (a b : Option Addr)
    (tail : Addr) : Result (Mem × Addr × Option Addr × Option Addr) :=
  match a, b with
  | none, _ => .ok (m, tail, a, b)
  | _, none => .ok (m, tail, a, b)
  | some av, some bv =>
    match F with
    | 0 => .error .AssertFail
    | F + 1 =>
      match memFind m av, memFind m bv with
      | some ba, some bb =>
        match memLoad m av ba.tag 0, memLoad m bv bb.tag 0 with
        | .ok va, .ok vb =>
          if vb.slt va then
            match memLoad m bv bb.tag 1 with
            | .error e => .error e
            | .ok wb =>
              match memFind m tail with
              | none => .error .AssertFail
              | some bt =>
                match memStore m tail bt.tag 1 (linkWord (some bv)) with
                | .error e => .error e
                | .ok m' =>
                  listMergeChase F m' (some av) (addrOfWord wb) bv
          else
            match memLoad m av ba.tag 1 with
            | .error e => .error e
            | .ok wa =>
              match memFind m tail with
              | none => .error .AssertFail
              | some bt =>
                match memStore m tail bt.tag 1 (linkWord (some av)) with
                | .error e => .error e
                | .ok m' =>
                  listMergeChase F m' (addrOfWord wa) (some bv) av
        | _, _ => .error .AssertFail
      | _, _ => .error .AssertFail

/-- Entry mirror: null-entry early returns, seed pick (head and
    tail start at the smaller head), chase, remainder splice
    (a null `a` splices the null link — chain end), return the
    head. -/
def listMergeFwd (F : Nat) (m : Mem) (a b : Option Addr) :
    Result (Mem × Option Addr) :=
  match a, b with
  | none, _ => .ok (m, b)
  | _, none => .ok (m, a)
  | some av, some bv =>
    match memFind m av, memFind m bv with
    | some ba, some bb =>
      match memLoad m av ba.tag 0, memLoad m bv bb.tag 0 with
      | .ok va, .ok vb =>
        if vb.slt va then
          match memLoad m bv bb.tag 1 with
          | .error e => .error e
          | .ok wb =>
            match listMergeChase F m (some av) (addrOfWord wb) bv with
            | .error e => .error e
            | .ok (m', tail', a', b') =>
              match memFind m' tail' with
              | none => .error .AssertFail
              | some bt =>
                match a' with
                | some _ =>
                  match memStore m' tail' bt.tag 1 (linkWord a') with
                  | .error e => .error e
                  | .ok m'' => .ok (m'', some bv)
                | none =>
                  match memStore m' tail' bt.tag 1 (linkWord b') with
                  | .error e => .error e
                  | .ok m'' => .ok (m'', some bv)
        else
          match memLoad m av ba.tag 1 with
          | .error e => .error e
          | .ok wa =>
            match listMergeChase F m (addrOfWord wa) (some bv) av with
            | .error e => .error e
            | .ok (m', tail', a', b') =>
              match memFind m' tail' with
              | none => .error .AssertFail
              | some bt =>
                match a' with
                | some _ =>
                  match memStore m' tail' bt.tag 1 (linkWord a') with
                  | .error e => .error e
                  | .ok m'' => .ok (m'', some av)
                | none =>
                  match memStore m' tail' bt.tag 1 (linkWord b') with
                  | .error e => .error e
                  | .ok m'' => .ok (m'', some av)
      | _, _ => .error .AssertFail
    | _, _ => .error .AssertFail

/-! ## Address-spine segments (pure outsideness) -/

/-- A segment tracking its address spine alongside the payloads:
    `ListSeg` forgets addresses, but the merge's outsideness
    side-conditions are address facts — carrying both keeps
    every disjointness argument pure (stores never change
    addresses, so disjointness rides for free). -/
inductive ListSegAddrs (m : Mem) : Option Addr → List Addr →
    List (BitVec 32) → Prop
  | nil : ListSegAddrs m none [] []
  | cons {a t v n la vs} : nodeAt m a t v n →
      ListSegAddrs m n la vs → ListSegAddrs m (some a) (a :: la) (v :: vs)

/-- Forgetting addresses recovers `ListSeg` (final assembly,
    acyclicity via `ListSeg_head_notin_tail`). -/
theorem ListSegAddrs.toListSeg {m : Mem} {s : Option Addr}
    {la : List Addr} {vs : List (BitVec 32)}
    (h : ListSegAddrs m s la vs) : ListSeg m s vs := by
  induction h with
  | nil => exact .nil
  | cons hnode _ ih => exact .cons hnode ih

/-- A spine rides a store elsewhere: every spine address differs
    from the stored cell (pure side condition — no `SegMem`
    transport needed). -/
theorem ListSegAddrs.store_other {m m' : Mem} {s : Option Addr}
    {la : List Addr} {vs : List (BitVec 32)} {p : Addr}
    {t i : Nat} {x : BitVec 32}
    (h : ListSegAddrs m s la vs)
    (hout : ∀ c ∈ la, c ≠ p)
    (hstore : memStore m p t i x = .ok m') :
    ListSegAddrs m' s la vs := by
  induction h with
  | nil => exact .nil
  | cons hnode _ ih =>
    exact .cons (nodeAt_store_other_fwd hnode hstore
      (hout _ (List.mem_cons.mpr (Or.inl rfl))))
      (ih (fun c hc => hout _ (List.mem_cons.mpr (Or.inr hc))))

/-- Cons inversion: name the head cell, tag, value, link, and
    both tails at once. -/
theorem ListSegAddrs.cons_inv {m : Mem} {s : Option Addr}
    {la : List Addr} {vs : List (BitVec 32)}
    (h : ListSegAddrs m s la vs) (hne : vs ≠ []) :
    ∃ a t v n la' vs', s = some a ∧ la = a :: la' ∧ vs = v :: vs' ∧
      nodeAt m a t v n ∧ ListSegAddrs m n la' vs' := by
  cases h with
  | nil => exact False.elim (hne rfl)
  | cons hnode t =>
    exact ⟨_, _, _, _, _, _, rfl, rfl, rfl, hnode, t⟩

/-- Spine membership yields footprint membership (forward
    bridge into `SegMem` — the reverse direction never
    arises). -/
theorem ListSegAddrs.mem_segmem {m : Mem} {s : Option Addr}
    {la : List Addr} {vs : List (BitVec 32)}
    (h : ListSegAddrs m s la vs) :
    ∀ c ∈ la, SegMem (m := m) s c := by
  induction h with
  | nil =>
    intro c hc
    simp at hc
  | cons hnode _ ih =>
    intro c hc
    rw [List.mem_cons] at hc
    cases hc with
    | inl heq => subst heq; exact SegMem.here hnode
    | inr hmem => exact SegMem.there hnode (ih _ hmem)

/-- The head of a spine is outside its own tail (acyclicity,
    in spine form — used where one remainder advances past the
    other chain's head). -/
theorem ListSegAddrs.head_notin_tail {m : Mem} {a : Addr} {t : Nat}
    {v : BitVec 32} {n : Option Addr} {la : List Addr}
    {vs : List (BitVec 32)}
    (hnode : nodeAt m a t v n) (htail : ListSegAddrs m n la vs)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32) :
    ∀ b ∈ la, b ≠ a :=
  fun b hb => ListSeg_head_notin_tail hnode htail.toListSeg hex b
    (htail.mem_segmem b hb)

/-- An empty payload list starts at null (spine form). -/
theorem ListSegAddrs.nil_start {m : Mem} {s : Option Addr} {la : List Addr}
    (h : ListSegAddrs m s la []) : s = none := by
  cases h with
  | nil => rfl

/-- A visited prefix rides a store at an address outside it (the
    chase-step transport: the store hits the old tail, which the
    invariant keeps out of the prefix). -/
theorem PrefixChain.store_other {m m' : Mem} {s e : Option Addr}
    {nodes : List (Addr × Nat × BitVec 32)} {p : Addr}
    {tp i : Nat} {x : BitVec 32}
    (h : PrefixChain m s nodes e)
    (hout : ∀ a ∈ nodes.map (·.1), a ≠ p)
    (hstore : memStore m p tp i x = .ok m') :
    PrefixChain m' s nodes e := by
  induction h with
  | nil => exact .nil
  | cons hnode _ ih =>
    exact .cons (nodeAt_store_other_fwd hnode hstore
      (hout _ (List.mem_cons.mpr (Or.inl rfl))))
      (ih (fun c hc => hout _ (List.mem_cons.mpr (Or.inr hc))))

/-- Entry conversion: every `ListSeg` has an address spine. -/
theorem ListSeg.toAddrs {m : Mem} {s : Option Addr}
    {vs : List (BitVec 32)} (h : ListSeg m s vs) :
    ∃ la, ListSegAddrs m s la vs := by
  induction h with
  | nil => exact ⟨[], .nil⟩
  | cons hnode _ ih =>
    obtain ⟨la, hla⟩ := ih
    exact ⟨_ :: la, .cons hnode hla⟩

/-! ## Chase invariant: spine + equation through the chase -/

/-- Merge chase invariant: the output spine (`PrefixChain`
    ending at the tail, values `out`), the remaining suffix
    segments (with address spines, so outsideness is pure),
    the merge equation against the full inputs, input
    sortedness, the fuel bound, the exactness bound, and the
    outsideness facts the tail-link store needs (remaining
    spines avoid the tail and the output; the two remaining
    sides stay disjoint; the tail is fresh in the spine). -/
structure MergeInv (F : Nat) (m : Mem) (head : Option Addr)
    (a b : Option Addr) (tail : Addr) (tt : Nat) (wt : BitVec 32)
    (nt : Option Addr)
    (nodes : List (Addr × Nat × BitVec 32))
    (la lb : List Addr)
    (out sa sb as₀ bs₀ : List (BitVec 32)) : Prop where
  hchain : PrefixChain m head nodes (some tail)
  htailN : nodeAt m tail tt wt nt
  hvals : out = preVals nodes ++ [wt]
  hsegA : ListSegAddrs m a la sa
  hsegB : ListSegAddrs m b lb sb
  hmerge : mergeChains as₀ bs₀ = out ++ mergeChains sa sb
  hsortedA : SortedWindow as₀ 0 as₀.length
  hsortedB : SortedWindow bs₀ 0 bs₀.length
  hfuel : sa.length + sb.length ≤ F
  hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32
  hsepA : ∀ c ∈ la, c ≠ tail ∧ c ∉ nodes.map (·.1)
  hsepB : ∀ c ∈ lb, c ≠ tail ∧ c ∉ nodes.map (·.1)
  hdisjAB : ∀ x y, x ∈ la → y ∈ lb → x ≠ y
  hnodupT : tail ∉ nodes.map (·.1)

/-! ## Seed: establish the invariant at the first pick -/

/-- Seed step, take-`b`: both heads live with
    `b.val < a.val`. No store happens (nothing to swing yet) —
    head and tail start at `b`, the output is `[vb]`, and
    outsideness is the caller debt, bridged forward into pure
    spine facts (`mem_segmem` — the reverse bridge is never
    needed). -/
theorem merge_seedB (F : Nat) (m : Mem)
    (av bv : Addr) {ba bb : Block}
    (va vb wb : BitVec 32)
    (la₀ lb₀ : List Addr) (as₀ bs₀ : List (BitVec 32))
    (hfindA : memFind m av = some ba)
    (hfindB : memFind m bv = some bb)
    (hloadA : memLoad m av ba.tag 0 = .ok va)
    (hloadB : memLoad m bv bb.tag 0 = .ok vb)
    (hlinkB : memLoad m bv bb.tag 1 = .ok wb)
    (hlt : (vb.slt va) = true)
    (hsegA : ListSegAddrs m (some av) la₀ as₀)
    (hsegB : ListSegAddrs m (some bv) lb₀ bs₀)
    (hneA : as₀ ≠ []) (hneB : bs₀ ≠ [])
    (hsortedA : SortedWindow as₀ 0 as₀.length)
    (hsortedB : SortedWindow bs₀ 0 bs₀.length)
    (hfuel : as₀.length + bs₀.length ≤ F + 1)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (hdisj0 : ∀ q r, SegMem (m := m) (some av) q →
      SegMem (m := m) (some bv) r → q ≠ r) :
    ∃ (sb' : List (BitVec 32)) (lb' : List Addr),
      MergeInv F m (some bv) (some av) (addrOfWord wb) bv
        bb.tag vb (addrOfWord wb) [] la₀ lb' [vb] as₀ sb' as₀ bs₀ := by
  obtain ⟨_, ta, va', _, _, _, hsA, _, hvsA, hnodeA, _⟩ :=
    ListSegAddrs.cons_inv hsegA hneA
  obtain ⟨_, tb, vb', bnext', lb₂, sb₂, hsB, hlbB, hvsB, hnodeB, tB⟩ :=
    ListSegAddrs.cons_inv hsegB hneB
  cases hsA
  cases hsB
  have htagA : ba.tag = ta := by
    have h2 : memFind m av = some _ := hnodeA
    rw [hfindA] at h2
    injection h2 with hba
    rw [hba]
  have htagB : bb.tag = tb := by
    have h2 : memFind m bv = some _ := hnodeB
    rw [hfindB] at h2
    injection h2 with hbb
    rw [hbb]
  have eva : va = va' := by
    have h1 := hloadA
    rw [htagA] at h1
    have h2 := nodeLoadVal hnodeA
    rw [h1] at h2
    cases h2; rfl
  have evb : vb = vb' := by
    have h1 := hloadB
    rw [htagB] at h1
    have h2 := nodeLoadVal hnodeB
    rw [h1] at h2
    cases h2; rfl
  have ewb : wb = linkWord bnext' := by
    have h1 := hlinkB
    rw [htagB] at h1
    have h2 := nodeLoadNext hnodeB
    rw [h1] at h2
    cases h2; rfl
  have hdec : addrOfWord (linkWord bnext') = bnext' :=
    nodeAt_link_roundtrip hnodeB hex (by
      intro c' hc'
      cases hnxt : bnext' with
      | none => rw [hnxt] at hc'; cases hc'
      | some c'' =>
        cases hc'
        exact ListSeg_head_alloc tB.toListSeg)
  have hbw : addrOfWord wb = bnext' := by rw [ewb, hdec]
  rw [eva, evb] at hlt
  have htailN : nodeAt m bv tb vb (addrOfWord wb) := by
    rw [evb, ewb, hdec]
    exact hnodeB
  have hsegB' : ListSegAddrs m (addrOfWord wb) lb₂ sb₂ := by
    rw [hbw]; exact tB
  have hmerge : mergeChains as₀ bs₀ = [vb] ++ mergeChains as₀ sb₂ := by
    rw [hvsA, hvsB, mergeChains_cons_takeB _ _ _ _ hlt, ← evb]
    simp only [List.cons_append, List.nil_append]
  have hfuel' : as₀.length + sb₂.length ≤ F := by
    rw [hvsA, hvsB] at hfuel
    rw [hvsA] at ⊢
    simp only [List.length_cons] at hfuel ⊢
    omega
  have hmemBv : bv ∈ lb₀ := by
    rw [hlbB]; exact List.mem_cons.mpr (Or.inl rfl)
  refine ⟨sb₂, lb₂, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · exact PrefixChain.nil
  · rw [htagB]; exact htailN
  · exact hsegA
  · exact hsegB'
  · exact hmerge
  · exact hsortedA
  · exact hsortedB
  · exact hfuel'
  · exact hex
  · intro c hc
    refine ⟨?_, by simp⟩
    exact hdisj0 c bv (hsegA.mem_segmem c hc)
      (hsegB.mem_segmem bv hmemBv)
  · intro c hc
    refine ⟨ListSegAddrs.head_notin_tail hnodeB tB hex c hc, by simp⟩
  · intro x y hx hy
    have hy0 : y ∈ lb₀ := by
      rw [hlbB]; exact List.mem_cons.mpr (Or.inr hy)
    exact hdisj0 x y (hsegA.mem_segmem x hx)
      (hsegB.mem_segmem y hy0)
  · simp

/-- Seed step, take-`a`: both heads live with
    `¬(b.val < a.val)`. Symmetric mirror of `merge_seedB` —
    head and tail start at `a`, the output is `[va]`. -/
theorem merge_seedA (F : Nat) (m : Mem)
    (av bv : Addr) {ba bb : Block}
    (va vb wa : BitVec 32)
    (la₀ lb₀ : List Addr) (as₀ bs₀ : List (BitVec 32))
    (hfindA : memFind m av = some ba)
    (hfindB : memFind m bv = some bb)
    (hloadA : memLoad m av ba.tag 0 = .ok va)
    (hloadB : memLoad m bv bb.tag 0 = .ok vb)
    (hlinkA : memLoad m av ba.tag 1 = .ok wa)
    (hlt : (vb.slt va) = false)
    (hsegA : ListSegAddrs m (some av) la₀ as₀)
    (hsegB : ListSegAddrs m (some bv) lb₀ bs₀)
    (hneA : as₀ ≠ []) (hneB : bs₀ ≠ [])
    (hsortedA : SortedWindow as₀ 0 as₀.length)
    (hsortedB : SortedWindow bs₀ 0 bs₀.length)
    (hfuel : as₀.length + bs₀.length ≤ F + 1)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (hdisj0 : ∀ q r, SegMem (m := m) (some av) q →
      SegMem (m := m) (some bv) r → q ≠ r) :
    ∃ (sa' : List (BitVec 32)) (la' : List Addr),
      MergeInv F m (some av) (addrOfWord wa) (some bv) av
        ba.tag va (addrOfWord wa) [] la' lb₀ [va] sa' bs₀ as₀ bs₀ := by
  obtain ⟨_, ta, va', anext', la₂, sa₂, hsA, hlaA, hvsA, hnodeA, tA⟩ :=
    ListSegAddrs.cons_inv hsegA hneA
  obtain ⟨_, tb, vb', _, _, _, hsB, _, hvsB, hnodeB, _⟩ :=
    ListSegAddrs.cons_inv hsegB hneB
  cases hsA
  cases hsB
  have htagA : ba.tag = ta := by
    have h2 : memFind m av = some _ := hnodeA
    rw [hfindA] at h2
    injection h2 with hba
    rw [hba]
  have htagB : bb.tag = tb := by
    have h2 : memFind m bv = some _ := hnodeB
    rw [hfindB] at h2
    injection h2 with hbb
    rw [hbb]
  have eva : va = va' := by
    have h1 := hloadA
    rw [htagA] at h1
    have h2 := nodeLoadVal hnodeA
    rw [h1] at h2
    cases h2; rfl
  have evb : vb = vb' := by
    have h1 := hloadB
    rw [htagB] at h1
    have h2 := nodeLoadVal hnodeB
    rw [h1] at h2
    cases h2; rfl
  have ewa : wa = linkWord anext' := by
    have h1 := hlinkA
    rw [htagA] at h1
    have h2 := nodeLoadNext hnodeA
    rw [h1] at h2
    cases h2; rfl
  have hdec : addrOfWord (linkWord anext') = anext' :=
    nodeAt_link_roundtrip hnodeA hex (by
      intro c' hc'
      cases hnxt : anext' with
      | none => rw [hnxt] at hc'; cases hc'
      | some c'' =>
        cases hc'
        exact ListSeg_head_alloc tA.toListSeg)
  have haw : addrOfWord wa = anext' := by rw [ewa, hdec]
  rw [eva, evb] at hlt
  have htailN : nodeAt m av ta va (addrOfWord wa) := by
    rw [eva, ewa, hdec]
    exact hnodeA
  have hsegA' : ListSegAddrs m (addrOfWord wa) la₂ sa₂ := by
    rw [haw]; exact tA
  have hmerge : mergeChains as₀ bs₀ = [va] ++ mergeChains sa₂ bs₀ := by
    rw [hvsA, hvsB, mergeChains_cons_takeA _ _ _ _ hlt, ← eva]
    simp only [List.cons_append, List.nil_append]
  have hfuel' : sa₂.length + bs₀.length ≤ F := by
    rw [hvsA, hvsB] at hfuel
    rw [hvsB] at ⊢
    simp only [List.length_cons] at hfuel ⊢
    omega
  have hmemAv : av ∈ la₀ := by
    rw [hlaA]; exact List.mem_cons.mpr (Or.inl rfl)
  refine ⟨sa₂, la₂, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · exact PrefixChain.nil
  · rw [htagA]; exact htailN
  · exact hsegA'
  · exact hsegB
  · exact hmerge
  · exact hsortedA
  · exact hsortedB
  · exact hfuel'
  · exact hex
  · intro c hc
    refine ⟨ListSegAddrs.head_notin_tail hnodeA tA hex c hc, by simp⟩
  · intro c hc
    refine ⟨?_, by simp⟩
    exact (hdisj0 av c (hsegA.mem_segmem av hmemAv)
      (hsegB.mem_segmem c hc)).symm
  · intro x y hx hy
    have hx0 : x ∈ la₀ := by
      rw [hlaA]; exact List.mem_cons.mpr (Or.inr hx)
    exact hdisj0 x y (hsegA.mem_segmem x hx0)
      (hsegB.mem_segmem y hy)
  · simp

/-! ## Chase steps: invariant preservation across the tail swing -/

/-- Chase step, take-`b`: swinging `tail.next := b` preserves the
    invariant — the output spine snocs the old tail, the new tail
    is `b`, the `b` remainder advances, and outsideness is pure
    spine facts (stores never move addresses). -/
theorem merge_stepB (F : Nat) {m m' : Mem} {head : Option Addr}
    {av bv t : Addr} {tt : Nat} {wt : BitVec 32} {nt : Option Addr}
    {nodes : List (Addr × Nat × BitVec 32)}
    {la lb : List Addr} {out sa sb as₀ bs₀ : List (BitVec 32)}
    (hinv : MergeInv (F + 1) m head (some av) (some bv) t tt wt nt nodes
      la lb out sa sb as₀ bs₀)
    {ba bb : Block} (va vb wb : BitVec 32)
    (hfindA : memFind m av = some ba)
    (hfindB : memFind m bv = some bb)
    (hloadA : memLoad m av ba.tag 0 = .ok va)
    (hloadB : memLoad m bv bb.tag 0 = .ok vb)
    (hlinkB : memLoad m bv bb.tag 1 = .ok wb)
    (hlt : (vb.slt va) = true)
    (hstore : memStore m t tt 1 (linkWord (some bv)) = .ok m') :
    ∃ (sb' : List (BitVec 32)) (lb' : List Addr),
      MergeInv F m' head (some av) (addrOfWord wb) bv
        bb.tag vb (addrOfWord wb) (nodes ++ [(t, tt, wt)])
        la lb' (out ++ [vb]) sa sb' as₀ bs₀ := by
  have hfindT : memFind m t = some _ := hinv.htailN
  have hneA : sa ≠ [] := by
    intro h
    subst h
    exact absurd (ListSegAddrs.nil_start hinv.hsegA) (by simp)
  have hneB : sb ≠ [] := by
    intro h
    subst h
    exact absurd (ListSegAddrs.nil_start hinv.hsegB) (by simp)
  obtain ⟨_, ta, va', _, _, _, hsA, _, hvsA, hnodeA, _⟩ :=
    ListSegAddrs.cons_inv hinv.hsegA hneA
  obtain ⟨_, tb, vb', bnext', lb₂, sb₂, hsB, hlbB, hvsB, hnodeB, tB⟩ :=
    ListSegAddrs.cons_inv hinv.hsegB hneB
  cases hsA
  cases hsB
  have htagA : ba.tag = ta := by
    have h2 : memFind m av = some _ := hnodeA
    rw [hfindA] at h2
    injection h2 with hba
    rw [hba]
  have htagB : bb.tag = tb := by
    have h2 : memFind m bv = some _ := hnodeB
    rw [hfindB] at h2
    injection h2 with hbb
    rw [hbb]
  have eva : va = va' := by
    have h1 := hloadA
    rw [htagA] at h1
    have h2 := nodeLoadVal hnodeA
    rw [h1] at h2
    cases h2; rfl
  have evb : vb = vb' := by
    have h1 := hloadB
    rw [htagB] at h1
    have h2 := nodeLoadVal hnodeB
    rw [h1] at h2
    cases h2; rfl
  have ewb : wb = linkWord bnext' := by
    have h1 := hlinkB
    rw [htagB] at h1
    have h2 := nodeLoadNext hnodeB
    rw [h1] at h2
    cases h2; rfl
  have hdec : addrOfWord (linkWord bnext') = bnext' :=
    nodeAt_link_roundtrip hnodeB hinv.hex (by
      intro c' hc'
      cases hnxt : bnext' with
      | none => rw [hnxt] at hc'; cases hc'
      | some c'' =>
        cases hc'
        exact ListSeg_head_alloc tB.toListSeg)
  have hbw : addrOfWord wb = bnext' := by rw [ewb, hdec]
  rw [eva, evb] at hlt
  have hmemBv : bv ∈ lb := by
    rw [hlbB]; exact List.mem_cons.mpr (Or.inl rfl)
  -- new-memory facts: swung tail, transported chain and spines
  have hnodeT' : nodeAt m' t tt wt (some bv) :=
    nodeStoreNext_nodeAt hinv.htailN hstore
  have houtN : ∀ a ∈ nodes.map (·.1), a ≠ t := by
    intro a ha heq
    subst heq
    exact hinv.hnodupT ha
  have hchainT : PrefixChain m' head nodes (some t) :=
    PrefixChain.store_other hinv.hchain houtN hstore
  have hchain' : PrefixChain m' head (nodes ++ [(t, tt, wt)]) (some bv) :=
    PrefixChain.snoc_extend hchainT hnodeT' rfl rfl
  have houtB : ∀ c ∈ lb₂, c ≠ t := by
    intro c hc
    have hc0 : c ∈ lb := by
      rw [hlbB]; exact List.mem_cons.mpr (Or.inr hc)
    exact (hinv.hsepB c hc0).1
  have htailN' : nodeAt m' bv tb vb (addrOfWord wb) := by
    have hnb := nodeAt_store_other_fwd hnodeB hstore
      ((hinv.hsepB bv hmemBv).1)
    rw [evb, hbw]
    exact hnb
  have hsegA' : ListSegAddrs m' (some av) la sa :=
    ListSegAddrs.store_other hinv.hsegA
      (fun c hc => (hinv.hsepA c hc).1) hstore
  have hsegB' : ListSegAddrs m' (addrOfWord wb) lb₂ sb₂ := by
    rw [hbw]
    exact ListSegAddrs.store_other tB houtB hstore
  have hvals' : out ++ [vb] =
      preVals (nodes ++ [(t, tt, wt)]) ++ [vb] := by
    have happ : preVals (nodes ++ [(t, tt, wt)]) =
        preVals nodes ++ [wt] := by
      simp [preVals]
    rw [happ, ← hinv.hvals]
  have hmerge' : mergeChains as₀ bs₀ =
      (out ++ [vb]) ++ mergeChains sa sb₂ := by
    rw [hinv.hmerge, hvsA, hvsB, mergeChains_cons_takeB _ _ _ _ hlt, ← evb]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hfuel' : sa.length + sb₂.length ≤ F := by
    have hf := hinv.hfuel
    rw [hvsB] at hf
    simp only [List.length_cons] at hf ⊢
    omega
  have hex' : ∀ x, (memFind m' x).isSome = true → x + 1 < 2 ^ 32 := by
    intro x hx
    by_cases heq : x = t
    · rw [heq]
      exact hinv.hex t (by simp [hfindT])
    · have hfind := memFind_memStore_other m m' t x tt 1
        (linkWord (some bv)) hstore heq
      rw [hfind] at hx
      exact hinv.hex x hx
  refine ⟨sb₂, lb₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · exact hchain'
  · rw [htagB]; exact htailN'
  · exact hvals'
  · exact hsegA'
  · exact hsegB'
  · exact hmerge'
  · exact hinv.hsortedA
  · exact hinv.hsortedB
  · exact hfuel'
  · exact hex'
  · intro c hc
    refine ⟨hinv.hdisjAB c bv hc hmemBv, ?_⟩
    intro hcon
    rw [List.map_append, List.mem_append] at hcon
    cases hcon with
    | inl h => exact (hinv.hsepA c hc).2 h
    | inr h =>
      rw [List.map_cons, List.map_nil, List.mem_singleton] at h
      exact ((hinv.hsepA c hc).1 h).elim
  · intro c hc
    refine ⟨ListSegAddrs.head_notin_tail hnodeB tB hinv.hex c hc, ?_⟩
    intro hcon
    rw [List.map_append, List.mem_append] at hcon
    cases hcon with
    | inl h =>
      have hc0 : c ∈ lb := by
        rw [hlbB]; exact List.mem_cons.mpr (Or.inr hc)
      exact (hinv.hsepB c hc0).2 h
    | inr h =>
      rw [List.map_cons, List.map_nil, List.mem_singleton] at h
      have hc0 : c ∈ lb := by
        rw [hlbB]; exact List.mem_cons.mpr (Or.inr hc)
      exact ((hinv.hsepB c hc0).1 h).elim
  · intro x y hx hy
    have hy0 : y ∈ lb := by
      rw [hlbB]; exact List.mem_cons.mpr (Or.inr hy)
    exact hinv.hdisjAB x y hx hy0
  · intro hcon
    rw [List.map_append, List.mem_append] at hcon
    cases hcon with
    | inl h => exact (hinv.hsepB bv hmemBv).2 h
    | inr h =>
      rw [List.map_cons, List.map_nil, List.mem_singleton] at h
      exact ((hinv.hsepB bv hmemBv).1 h).elim

/-- Chase step, take-`a`: swinging `tail.next := a` preserves the
    invariant — symmetric mirror of `merge_stepB`. -/
theorem merge_stepA (F : Nat) {m m' : Mem} {head : Option Addr}
    {av bv t : Addr} {tt : Nat} {wt : BitVec 32} {nt : Option Addr}
    {nodes : List (Addr × Nat × BitVec 32)}
    {la lb : List Addr} {out sa sb as₀ bs₀ : List (BitVec 32)}
    (hinv : MergeInv (F + 1) m head (some av) (some bv) t tt wt nt nodes
      la lb out sa sb as₀ bs₀)
    {ba bb : Block} (va vb wa : BitVec 32)
    (hfindA : memFind m av = some ba)
    (hfindB : memFind m bv = some bb)
    (hloadA : memLoad m av ba.tag 0 = .ok va)
    (hloadB : memLoad m bv bb.tag 0 = .ok vb)
    (hlinkA : memLoad m av ba.tag 1 = .ok wa)
    (hlt : (vb.slt va) = false)
    (hstore : memStore m t tt 1 (linkWord (some av)) = .ok m') :
    ∃ (sa' : List (BitVec 32)) (la' : List Addr),
      MergeInv F m' head (addrOfWord wa) (some bv) av
        ba.tag va (addrOfWord wa) (nodes ++ [(t, tt, wt)])
        la' lb (out ++ [va]) sa' sb as₀ bs₀ := by
  have hfindT : memFind m t = some _ := hinv.htailN
  have hneA : sa ≠ [] := by
    intro h
    subst h
    exact absurd (ListSegAddrs.nil_start hinv.hsegA) (by simp)
  have hneB : sb ≠ [] := by
    intro h
    subst h
    exact absurd (ListSegAddrs.nil_start hinv.hsegB) (by simp)
  obtain ⟨_, ta, va', anext', la₂, sa₂, hsA, hlaA, hvsA, hnodeA, tA⟩ :=
    ListSegAddrs.cons_inv hinv.hsegA hneA
  obtain ⟨_, tb, vb', _, _, _, hsB, _, hvsB, hnodeB, _⟩ :=
    ListSegAddrs.cons_inv hinv.hsegB hneB
  cases hsA
  cases hsB
  have htagA : ba.tag = ta := by
    have h2 : memFind m av = some _ := hnodeA
    rw [hfindA] at h2
    injection h2 with hba
    rw [hba]
  have htagB : bb.tag = tb := by
    have h2 : memFind m bv = some _ := hnodeB
    rw [hfindB] at h2
    injection h2 with hbb
    rw [hbb]
  have eva : va = va' := by
    have h1 := hloadA
    rw [htagA] at h1
    have h2 := nodeLoadVal hnodeA
    rw [h1] at h2
    cases h2; rfl
  have evb : vb = vb' := by
    have h1 := hloadB
    rw [htagB] at h1
    have h2 := nodeLoadVal hnodeB
    rw [h1] at h2
    cases h2; rfl
  have ewa : wa = linkWord anext' := by
    have h1 := hlinkA
    rw [htagA] at h1
    have h2 := nodeLoadNext hnodeA
    rw [h1] at h2
    cases h2; rfl
  have hdec : addrOfWord (linkWord anext') = anext' :=
    nodeAt_link_roundtrip hnodeA hinv.hex (by
      intro c' hc'
      cases hnxt : anext' with
      | none => rw [hnxt] at hc'; cases hc'
      | some c'' =>
        cases hc'
        exact ListSeg_head_alloc tA.toListSeg)
  have haw : addrOfWord wa = anext' := by rw [ewa, hdec]
  rw [eva, evb] at hlt
  have hmemAv : av ∈ la := by
    rw [hlaA]; exact List.mem_cons.mpr (Or.inl rfl)
  -- new-memory facts: swung tail, transported chain and spines
  have hnodeT' : nodeAt m' t tt wt (some av) :=
    nodeStoreNext_nodeAt hinv.htailN hstore
  have houtN : ∀ a ∈ nodes.map (·.1), a ≠ t := by
    intro a ha heq
    subst heq
    exact hinv.hnodupT ha
  have hchainT : PrefixChain m' head nodes (some t) :=
    PrefixChain.store_other hinv.hchain houtN hstore
  have hchain' : PrefixChain m' head (nodes ++ [(t, tt, wt)]) (some av) :=
    PrefixChain.snoc_extend hchainT hnodeT' rfl rfl
  have houtA : ∀ c ∈ la₂, c ≠ t := by
    intro c hc
    have hc0 : c ∈ la := by
      rw [hlaA]; exact List.mem_cons.mpr (Or.inr hc)
    exact (hinv.hsepA c hc0).1
  have htailN' : nodeAt m' av ta va (addrOfWord wa) := by
    have hna := nodeAt_store_other_fwd hnodeA hstore
      ((hinv.hsepA av hmemAv).1)
    rw [eva, haw]
    exact hna
  have hsegA' : ListSegAddrs m' (addrOfWord wa) la₂ sa₂ := by
    rw [haw]
    exact ListSegAddrs.store_other tA houtA hstore
  have hsegB' : ListSegAddrs m' (some bv) lb sb :=
    ListSegAddrs.store_other hinv.hsegB
      (fun c hc => (hinv.hsepB c hc).1) hstore
  have hvals' : out ++ [va] =
      preVals (nodes ++ [(t, tt, wt)]) ++ [va] := by
    have happ : preVals (nodes ++ [(t, tt, wt)]) =
        preVals nodes ++ [wt] := by
      simp [preVals]
    rw [happ, ← hinv.hvals]
  have hmerge' : mergeChains as₀ bs₀ =
      (out ++ [va]) ++ mergeChains sa₂ sb := by
    rw [hinv.hmerge, hvsA, hvsB, mergeChains_cons_takeA _ _ _ _ hlt, ← eva]
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hfuel' : sa₂.length + sb.length ≤ F := by
    have hf := hinv.hfuel
    rw [hvsA, hvsB] at hf
    rw [hvsB] at ⊢
    simp only [List.length_cons] at hf ⊢
    omega
  have hex' : ∀ x, (memFind m' x).isSome = true → x + 1 < 2 ^ 32 := by
    intro x hx
    by_cases heq : x = t
    · rw [heq]
      exact hinv.hex t (by simp [hfindT])
    · have hfind := memFind_memStore_other m m' t x tt 1
        (linkWord (some av)) hstore heq
      rw [hfind] at hx
      exact hinv.hex x hx
  refine ⟨sa₂, la₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_⟩
  · exact hchain'
  · rw [htagA]; exact htailN'
  · exact hvals'
  · exact hsegA'
  · exact hsegB'
  · exact hmerge'
  · exact hinv.hsortedA
  · exact hinv.hsortedB
  · exact hfuel'
  · exact hex'
  · intro c hc
    refine ⟨ListSegAddrs.head_notin_tail hnodeA tA hinv.hex c hc, ?_⟩
    intro hcon
    rw [List.map_append, List.mem_append] at hcon
    cases hcon with
    | inl h =>
      have hc0 : c ∈ la := by
        rw [hlaA]; exact List.mem_cons.mpr (Or.inr hc)
      exact (hinv.hsepA c hc0).2 h
    | inr h =>
      rw [List.map_cons, List.map_nil, List.mem_singleton] at h
      have hc0 : c ∈ la := by
        rw [hlaA]; exact List.mem_cons.mpr (Or.inr hc)
      exact ((hinv.hsepA c hc0).1 h).elim
  · intro c hc
    refine ⟨(hinv.hdisjAB av c hmemAv hc).symm, ?_⟩
    intro hcon
    rw [List.map_append, List.mem_append] at hcon
    cases hcon with
    | inl h => exact (hinv.hsepB c hc).2 h
    | inr h =>
      rw [List.map_cons, List.map_nil, List.mem_singleton] at h
      exact ((hinv.hsepB c hc).1 h).elim
  · intro x y hx hy
    have hx0 : x ∈ la := by
      rw [hlaA]; exact List.mem_cons.mpr (Or.inr hx)
    exact hinv.hdisjAB x y hx0 hy
  · intro hcon
    rw [List.map_append, List.mem_append] at hcon
    cases hcon with
    | inl h => exact (hinv.hsepA av hmemAv).2 h
    | inr h =>
      rw [List.map_cons, List.map_nil, List.mem_singleton] at h
      exact ((hinv.hsepA av hmemAv).1 h).elim

/-! ## Remainder splice: attach the live remainder whole -/

/-- Remainder splice, `a` exhausted: swinging `tail.next := b`
    attaches the whole live `b` remainder — the output spine plus
    the transported remainder assemble the merged segment. -/
theorem merge_spliceB (F : Nat) {m m' : Mem} {head : Option Addr}
    {bv t : Addr} {tt : Nat} {wt : BitVec 32} {nt : Option Addr}
    {nodes : List (Addr × Nat × BitVec 32)}
    {lb : List Addr} {out sb as₀ bs₀ : List (BitVec 32)}
    (hinv : MergeInv F m head none (some bv) t tt wt nt nodes
      [] lb out [] sb as₀ bs₀)
    (hstore : memStore m t tt 1 (linkWord (some bv)) = .ok m') :
    ListSeg m' head (out ++ sb) := by
  have hnodeT' : nodeAt m' t tt wt (some bv) :=
    nodeStoreNext_nodeAt hinv.htailN hstore
  have houtN : ∀ a ∈ nodes.map (·.1), a ≠ t := by
    intro a ha heq
    subst heq
    exact hinv.hnodupT ha
  have hchain' : PrefixChain m' head (nodes ++ [(t, tt, wt)]) (some bv) :=
    PrefixChain.snoc_extend
      (PrefixChain.store_other hinv.hchain houtN hstore) hnodeT' rfl rfl
  have hsegB' : ListSeg m' (some bv) sb :=
    (ListSegAddrs.store_other hinv.hsegB
      (fun c hc => (hinv.hsepB c hc).1) hstore).toListSeg
  have happ : preVals (nodes ++ [(t, tt, wt)]) = out := by
    have h0 : preVals (nodes ++ [(t, tt, wt)]) =
        preVals nodes ++ [wt] := by
      simp [preVals]
    rw [h0, ← hinv.hvals]
  have hfin : ListSeg m' head
      (preVals (nodes ++ [(t, tt, wt)]) ++ sb) :=
    PrefixChain.appendSeg hchain' hsegB'
  rw [happ] at hfin
  exact hfin

/-- Remainder splice, `b` exhausted: symmetric mirror — swinging
    `tail.next := a` attaches the whole live `a` remainder. -/
theorem merge_spliceA (F : Nat) {m m' : Mem} {head : Option Addr}
    {av t : Addr} {tt : Nat} {wt : BitVec 32} {nt : Option Addr}
    {nodes : List (Addr × Nat × BitVec 32)}
    {la : List Addr} {out sa as₀ bs₀ : List (BitVec 32)}
    (hinv : MergeInv F m head (some av) none t tt wt nt nodes
      la [] out sa [] as₀ bs₀)
    (hstore : memStore m t tt 1 (linkWord (some av)) = .ok m') :
    ListSeg m' head (out ++ sa) := by
  have hnodeT' : nodeAt m' t tt wt (some av) :=
    nodeStoreNext_nodeAt hinv.htailN hstore
  have houtN : ∀ a ∈ nodes.map (·.1), a ≠ t := by
    intro a ha heq
    subst heq
    exact hinv.hnodupT ha
  have hchain' : PrefixChain m' head (nodes ++ [(t, tt, wt)]) (some av) :=
    PrefixChain.snoc_extend
      (PrefixChain.store_other hinv.hchain houtN hstore) hnodeT' rfl rfl
  have hsegA' : ListSeg m' (some av) sa :=
    (ListSegAddrs.store_other hinv.hsegA
      (fun c hc => (hinv.hsepA c hc).1) hstore).toListSeg
  have happ : preVals (nodes ++ [(t, tt, wt)]) = out := by
    have h0 : preVals (nodes ++ [(t, tt, wt)]) =
        preVals nodes ++ [wt] := by
      simp [preVals]
    rw [h0, ← hinv.hvals]
  have hfin : ListSeg m' head
      (preVals (nodes ++ [(t, tt, wt)]) ++ sa) :=
    PrefixChain.appendSeg hchain' hsegA'
  rw [happ] at hfin
  exact hfin

/-! ## Chase correctness: fuel induction over the mirror -/

/-- A successful chase stops with a dead cursor: the only `ok`
    arms are the stop arms; recursion needs both live. -/
theorem listMergeChase_stop : ∀ (F : Nat) {m m' : Mem} {a b : Option Addr}
    {tail tail' : Addr} {a' b' : Option Addr},
    listMergeChase F m a b tail = .ok (m', tail', a', b') →
    a' = none ∨ b' = none := by
  intro F
  induction F with
  | zero =>
    intro m m' a b tail tail' a' b' hfwd
    cases a with
    | none =>
      simp only [listMergeChase] at hfwd
      cases hfwd
      exact Or.inl rfl
    | some av =>
      cases b with
      | none =>
        simp only [listMergeChase] at hfwd
        cases hfwd
        exact Or.inr rfl
      | some bv =>
        simp only [listMergeChase] at hfwd
        cases hfwd
  | succ F ih =>
    intro m m' a b tail tail' a' b' hfwd
    cases a with
    | none =>
      simp only [listMergeChase] at hfwd
      cases hfwd
      exact Or.inl rfl
    | some av =>
      cases b with
      | none =>
        simp only [listMergeChase] at hfwd
        cases hfwd
        exact Or.inr rfl
      | some bv =>
        simp only [listMergeChase] at hfwd
        cases hfa : memFind m av with
        | none =>
          simp only [hfa] at hfwd
          cases hfwd
        | some ba =>
          simp only [hfa] at hfwd
          cases hfb : memFind m bv with
          | none =>
            simp only [hfb] at hfwd
            cases hfwd
          | some bb =>
            simp only [hfb] at hfwd
            cases hla : memLoad m av ba.tag 0 with
            | error e =>
              simp only [hla] at hfwd
              cases hfwd
            | ok va =>
              simp only [hla] at hfwd
              cases hlb : memLoad m bv bb.tag 0 with
              | error e =>
                simp only [hlb] at hfwd
                cases hfwd
              | ok vb =>
                simp only [hlb] at hfwd
                by_cases hlt : (vb.slt va) = true
                · rw [if_pos hlt] at hfwd
                  cases hwb : memLoad m bv bb.tag 1 with
                  | error e =>
                    simp only [hwb] at hfwd
                    cases hfwd
                  | ok wb =>
                    simp only [hwb] at hfwd
                    cases hft : memFind m tail with
                    | none =>
                      simp only [hft] at hfwd
                      cases hfwd
                    | some bt =>
                      simp only [hft] at hfwd
                      cases hst : memStore m tail bt.tag 1
                          (linkWord (some bv)) with
                      | error e =>
                        simp only [hst] at hfwd
                        cases hfwd
                      | ok m'' =>
                        simp only [hst] at hfwd
                        exact ih hfwd
                · rw [if_neg hlt] at hfwd
                  cases hwa : memLoad m av ba.tag 1 with
                  | error e =>
                    simp only [hwa] at hfwd
                    cases hfwd
                  | ok wa =>
                    simp only [hwa] at hfwd
                    cases hft : memFind m tail with
                    | none =>
                      simp only [hft] at hfwd
                      cases hfwd
                    | some bt =>
                      simp only [hft] at hfwd
                      cases hst : memStore m tail bt.tag 1
                          (linkWord (some av)) with
                      | error e =>
                        simp only [hst] at hfwd
                        cases hfwd
                      | ok m'' =>
                        simp only [hst] at hfwd
                        exact ih hfwd

/-- Chase correctness: an invariant at the chase entry
    becomes an invariant at the chase exit — stop arms carry it
    over; live iterations swing the tail link (`merge_stepA/B`)
    and recurse on the remaining fuel. -/
theorem listMergeChase_correct : ∀ (F : Nat) {m m' : Mem}
    {head : Option Addr} {a b : Option Addr}
    {tail tail' : Addr} {a' b' : Option Addr}
    {tt : Nat} {wt : BitVec 32} {nt : Option Addr}
    {nodes : List (Addr × Nat × BitVec 32)}
    {la lb : List Addr} {out sa sb as₀ bs₀ : List (BitVec 32)}
    (hinv : MergeInv F m head a b tail tt wt nt nodes la lb out sa sb
      as₀ bs₀),
    listMergeChase F m a b tail = .ok (m', tail', a', b') →
    ∃ (tt' : Nat) (wt' : BitVec 32) (nt' : Option Addr)
      (nodes' : List (Addr × Nat × BitVec 32))
      (la' lb' : List Addr) (out' sa' sb' : List (BitVec 32)),
      MergeInv F m' head a' b' tail' tt' wt' nt' nodes' la' lb'
        out' sa' sb' as₀ bs₀ := by
  intro F
  induction F with
  | zero =>
    intro m m' head a b tail tail' a' b' tt wt nt nodes la lb out sa sb
      as₀ bs₀ hinv hfwd
    cases a with
    | none =>
      simp only [listMergeChase] at hfwd
      cases hfwd
      exact ⟨tt, wt, nt, nodes, la, lb, out, sa, sb, hinv⟩
    | some av =>
      cases b with
      | none =>
        simp only [listMergeChase] at hfwd
        cases hfwd
        exact ⟨tt, wt, nt, nodes, la, lb, out, sa, sb, hinv⟩
      | some bv =>
        simp only [listMergeChase] at hfwd
        cases hfwd
  | succ F ih =>
    intro m m' head a b tail tail' a' b' tt wt nt nodes la lb out sa sb
      as₀ bs₀ hinv hfwd
    cases a with
    | none =>
      simp only [listMergeChase] at hfwd
      cases hfwd
      exact ⟨tt, wt, nt, nodes, la, lb, out, sa, sb, hinv⟩
    | some av =>
      cases b with
      | none =>
        simp only [listMergeChase] at hfwd
        cases hfwd
        exact ⟨tt, wt, nt, nodes, la, lb, out, sa, sb, hinv⟩
      | some bv =>
        have hneA : sa ≠ [] := by
          intro h
          subst h
          exact absurd (ListSegAddrs.nil_start hinv.hsegA) (by simp)
        have hneB : sb ≠ [] := by
          intro h
          subst h
          exact absurd (ListSegAddrs.nil_start hinv.hsegB) (by simp)
        obtain ⟨_, ta, va', anext', _, _, hsA, _, _, hnodeA, _⟩ :=
          ListSegAddrs.cons_inv hinv.hsegA hneA
        obtain ⟨_, tb, vb', bnext', _, _, hsB, _, _, hnodeB, _⟩ :=
          ListSegAddrs.cons_inv hinv.hsegB hneB
        cases hsA
        cases hsB
        have hfindA : memFind m av = some _ := hnodeA
        have hfindB : memFind m bv = some _ := hnodeB
        have hloadA : memLoad m av ta 0 = .ok va' := nodeLoadVal hnodeA
        have hloadB : memLoad m bv tb 0 = .ok vb' := nodeLoadVal hnodeB
        have hlinkA : memLoad m av ta 1 = .ok (linkWord anext') :=
          nodeLoadNext hnodeA
        have hlinkB : memLoad m bv tb 1 = .ok (linkWord bnext') :=
          nodeLoadNext hnodeB
        have hfindT : memFind m tail = some _ := hinv.htailN
        unfold listMergeChase at hfwd
        simp only [hfindA, hfindB, hloadA, hloadB] at hfwd
        by_cases hlt : (vb'.slt va') = true
        · rw [if_pos hlt] at hfwd
          simp only [hlinkB, hfindT] at hfwd
          cases hst : memStore m tail tt 1 (linkWord (some bv)) with
          | error e =>
            simp only [hst] at hfwd
            cases hfwd
          | ok m'' =>
            simp only [hst] at hfwd
            obtain ⟨sb₂, lb₂, hinvS⟩ := merge_stepB F hinv va' vb'
              (linkWord bnext') hfindA hfindB hloadA hloadB hlinkB
              hlt hst
            obtain ⟨tt', wt', nt', nodes', la', lb', out', sa', sb', hinvI⟩ :=
              ih hinvS hfwd
            exact ⟨tt', wt', nt', nodes', la', lb', out', sa', sb',
              { hinvI with hfuel := Nat.le_step hinvI.hfuel }⟩
        · have hltF : (vb'.slt va') = false :=
            Bool.eq_false_of_ne_true hlt
          rw [if_neg (by simp [hltF])] at hfwd
          simp only [hlinkA, hfindT] at hfwd
          cases hst : memStore m tail tt 1 (linkWord (some av)) with
          | error e =>
            simp only [hst] at hfwd
            cases hfwd
          | ok m'' =>
            simp only [hst] at hfwd
            obtain ⟨sa₂, la₂, hinvS⟩ := merge_stepA F hinv va' vb'
              (linkWord anext') hfindA hfindB hloadA hloadB hlinkA
              hltF hst
            obtain ⟨tt', wt', nt', nodes', la', lb', out', sa', sb', hinvI⟩ :=
              ih hinvS hfwd
            exact ⟨tt', wt', nt', nodes', la', lb', out', sa', sb',
              { hinvI with hfuel := Nat.le_step hinvI.hfuel }⟩

/-- Entry correctness: the seed pick, the chase, and the remainder
    splice assemble the merged segment — null entries return the
    live side; both-live picks the smaller head, chases, and
    attaches the survivor (`merge_spliceA/B`, null-terminating
    when both cursors die together). -/
theorem listMergeFwd_correct (F : Nat) {m m'' : Mem} {a b : Option Addr}
    {hret : Option Addr} {as₀ bs₀ : List (BitVec 32)}
    (hsegA0 : ListSeg m a as₀) (hsegB0 : ListSeg m b bs₀)
    (hsortedA : SortedWindow as₀ 0 as₀.length)
    (hsortedB : SortedWindow bs₀ 0 bs₀.length)
    (hfuel : as₀.length + bs₀.length ≤ F + 1)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (hdisj0 : ∀ q r, SegMem (m := m) a q → SegMem (m := m) b r → q ≠ r)
    (hfwd : listMergeFwd F m a b = .ok (m'', hret)) :
    ListSeg m'' hret (mergeChains as₀ bs₀) := by
  cases a with
  | none =>
    simp only [listMergeFwd] at hfwd
    cases hfwd
    cases hsegA0 with
    | nil =>
      have hnil : mergeChains [] bs₀ = bs₀ := by simp [mergeChains]
      rw [hnil]
      exact hsegB0
  | some av =>
    cases b with
    | none =>
      simp only [listMergeFwd] at hfwd
      cases hfwd
      cases hsegB0 with
      | nil =>
        have hnil : mergeChains as₀ [] = as₀ := mergeChains_nil_right as₀
        rw [hnil]
        exact hsegA0
    | some bv =>
      obtain ⟨la₀, hsegA⟩ := ListSeg.toAddrs hsegA0
      obtain ⟨lb₀, hsegB⟩ := ListSeg.toAddrs hsegB0
      have hneA : as₀ ≠ [] := by
        intro h
        subst h
        exact absurd (ListSeg_nil_start hsegA0) (by simp)
      have hneB : bs₀ ≠ [] := by
        intro h
        subst h
        exact absurd (ListSeg_nil_start hsegB0) (by simp)
      obtain ⟨_, ta, va', anext', _, _, hsA, _, _, hnodeA, _⟩ :=
        ListSegAddrs.cons_inv hsegA hneA
      obtain ⟨_, tb, vb', bnext', _, _, hsB, _, _, hnodeB, _⟩ :=
        ListSegAddrs.cons_inv hsegB hneB
      cases hsA
      cases hsB
      have hfindA : memFind m av = some _ := hnodeA
      have hfindB : memFind m bv = some _ := hnodeB
      have hloadA : memLoad m av ta 0 = .ok va' := nodeLoadVal hnodeA
      have hloadB : memLoad m bv tb 0 = .ok vb' := nodeLoadVal hnodeB
      have hlinkA : memLoad m av ta 1 = .ok (linkWord anext') :=
        nodeLoadNext hnodeA
      have hlinkB : memLoad m bv tb 1 = .ok (linkWord bnext') :=
        nodeLoadNext hnodeB
      unfold listMergeFwd at hfwd
      simp only [hfindA, hfindB, hloadA, hloadB] at hfwd
      by_cases hlt : (vb'.slt va') = true
      · rw [if_pos hlt] at hfwd
        simp only [hlinkB] at hfwd
        obtain ⟨sb₂, lb₂, hseed⟩ := merge_seedB F m av bv va' vb'
          (linkWord bnext') la₀ lb₀ as₀ bs₀ hfindA hfindB hloadA hloadB
          hlinkB hlt hsegA hsegB hneA hneB hsortedA hsortedB hfuel hex
          hdisj0
        cases hch : listMergeChase F m (some av)
            (addrOfWord (linkWord bnext')) bv with
        | error e =>
          simp only [hch] at hfwd
          cases hfwd
        | ok res =>
          obtain ⟨m', tail', a', b'⟩ := res
          simp only [hch] at hfwd
          obtain ⟨tt', wt', nt', nodes', la', lb', out', sa', sb', hinv'⟩ :=
            listMergeChase_correct F hseed hch
          have hstop := listMergeChase_stop F hch
          have hfindT : memFind m' tail' = some _ := hinv'.htailN
          simp only [hfindT] at hfwd
          cases ha0 : a' with
          | some x =>
            subst ha0
            cases hsw : memStore m' tail' tt' 1 (linkWord (some x)) with
            | error e =>
              simp only [hsw] at hfwd
              cases hfwd
            | ok m2 =>
              simp only [hsw] at hfwd
              cases hfwd
              have hb' : b' = none := by
                cases hstop with
                | inl h => cases h
                | inr h => exact h
              subst hb'
              have hB0 := hinv'.hsegB
              cases hB0 with
              | nil =>
                have hfin := merge_spliceA F hinv' hsw
                have hnil : mergeChains sa' [] = sa' := mergeChains_nil_right sa'
                rw [hinv'.hmerge, hnil]
                exact hfin
          | none =>
            subst ha0
            cases hsw : memStore m' tail' tt' 1 (linkWord b') with
            | error e =>
              simp only [hsw] at hfwd
              cases hfwd
            | ok m2 =>
              simp only [hsw] at hfwd
              cases hfwd
              cases hb0 : b' with
              | some y =>
                subst hb0
                have hA0 := hinv'.hsegA
                cases hA0 with
                | nil =>
                  have hfin := merge_spliceB F hinv' hsw
                  have hnil : mergeChains [] sb' = sb' := mergeChains_nil_left sb'
                  rw [hinv'.hmerge, hnil]
                  exact hfin
              | none =>
                subst hb0
                have hA0 := hinv'.hsegA
                cases hA0 with
                | nil =>
                  have hB0 := hinv'.hsegB
                  cases hB0 with
                  | nil =>
                    have houtN : ∀ a ∈ nodes'.map (·.1), a ≠ tail' := by
                      intro a ha heq
                      subst heq
                      exact hinv'.hnodupT ha
                    have hchainT : PrefixChain m'' _ nodes'
                        (some tail') :=
                      PrefixChain.store_other hinv'.hchain houtN hsw
                    have htailN0 : nodeAt m'' tail' tt' wt' none :=
                      nodeStoreNext_nodeAt hinv'.htailN hsw
                    have hfin : ListSeg m'' _
                        (preVals nodes' ++ [wt']) :=
                      PrefixChain.appendSeg hchainT
                        (ListSeg.cons htailN0 .nil)
                    rw [← hinv'.hvals] at hfin
                    have hnil : mergeChains ([] : List (BitVec 32)) [] = [] :=
                      mergeChains_nil_left []
                    rw [hinv'.hmerge, hnil, List.append_nil]
                    exact hfin
      · have hltF : (vb'.slt va') = false :=
          Bool.eq_false_of_ne_true hlt
        rw [if_neg (by simp [hltF])] at hfwd
        simp only [hlinkA] at hfwd
        obtain ⟨sa₂, la₂, hseed⟩ := merge_seedA F m av bv va' vb'
          (linkWord anext') la₀ lb₀ as₀ bs₀ hfindA hfindB hloadA hloadB
          hlinkA hltF hsegA hsegB hneA hneB hsortedA hsortedB hfuel hex
          hdisj0
        cases hch : listMergeChase F m
            (addrOfWord (linkWord anext')) (some bv) av with
        | error e =>
          simp only [hch] at hfwd
          cases hfwd
        | ok res =>
          obtain ⟨m', tail', a', b'⟩ := res
          simp only [hch] at hfwd
          obtain ⟨tt', wt', nt', nodes', la', lb', out', sa', sb', hinv'⟩ :=
            listMergeChase_correct F hseed hch
          have hstop := listMergeChase_stop F hch
          have hfindT : memFind m' tail' = some _ := hinv'.htailN
          simp only [hfindT] at hfwd
          cases ha0 : a' with
          | some x =>
            subst ha0
            cases hsw : memStore m' tail' tt' 1 (linkWord (some x)) with
            | error e =>
              simp only [hsw] at hfwd
              cases hfwd
            | ok m2 =>
              simp only [hsw] at hfwd
              cases hfwd
              have hb' : b' = none := by
                cases hstop with
                | inl h => cases h
                | inr h => exact h
              subst hb'
              have hB0 := hinv'.hsegB
              cases hB0 with
              | nil =>
                have hfin := merge_spliceA F hinv' hsw
                have hnil : mergeChains sa' [] = sa' := mergeChains_nil_right sa'
                rw [hinv'.hmerge, hnil]
                exact hfin
          | none =>
            subst ha0
            cases hsw : memStore m' tail' tt' 1 (linkWord b') with
            | error e =>
              simp only [hsw] at hfwd
              cases hfwd
            | ok m2 =>
              simp only [hsw] at hfwd
              cases hfwd
              cases hb0 : b' with
              | some y =>
                subst hb0
                have hA0 := hinv'.hsegA
                cases hA0 with
                | nil =>
                  have hfin := merge_spliceB F hinv' hsw
                  have hnil : mergeChains [] sb' = sb' := mergeChains_nil_left sb'
                  rw [hinv'.hmerge, hnil]
                  exact hfin
              | none =>
                subst hb0
                have hA0 := hinv'.hsegA
                cases hA0 with
                | nil =>
                  have hB0 := hinv'.hsegB
                  cases hB0 with
                  | nil =>
                    have houtN : ∀ a ∈ nodes'.map (·.1), a ≠ tail' := by
                      intro a ha heq
                      subst heq
                      exact hinv'.hnodupT ha
                    have hchainT : PrefixChain m'' _ nodes'
                        (some tail') :=
                      PrefixChain.store_other hinv'.hchain houtN hsw
                    have htailN0 : nodeAt m'' tail' tt' wt' none :=
                      nodeStoreNext_nodeAt hinv'.htailN hsw
                    have hfin : ListSeg m'' _
                        (preVals nodes' ++ [wt']) :=
                      PrefixChain.appendSeg hchainT
                        (ListSeg.cons htailN0 .nil)
                    rw [← hinv'.hvals] at hfin
                    have hnil : mergeChains ([] : List (BitVec 32)) [] = [] :=
                      mergeChains_nil_left []
                    rw [hinv'.hmerge, hnil, List.append_nil]
                    exact hfin

/-- The merge is a permutation of the concatenation. -/
theorem mergeChains_perm (as bs : List (BitVec 32)) :
    List.Perm (mergeChains as bs) (as ++ bs) := by
  induction as, bs using mergeChains.induct
  · rename_i bs
    cases bs <;> simp [mergeChains]
  · rename_i as hne
    cases as with
    | nil => exact absurd rfl hne
    | cons a as => simp [mergeChains]
  · rename_i a as b bs h ih
    rw [mergeChains_cons_takeB a as b bs h]
    exact (List.Perm.cons b ih).trans
      (perm_cons_append_middle b (a :: as) bs)
  · rename_i a as b bs h ih
    have h' : (b.slt a) = false := Bool.eq_false_of_ne_true h
    rw [mergeChains_cons_takeA a as b bs h']
    exact List.Perm.cons a ih

/-- Tail of a sorted window is sorted (index shift by one). -/
theorem SortedWindow_cons_tail (x : BitVec 32) (xs : List (BitVec 32))
    (h : SortedWindow (x :: xs) 0 (x :: xs).length) :
    SortedWindow xs 0 xs.length := by
  intro p q hlo hpq hqk a b ha hb
  have hlen : ((x :: xs).length) = xs.length + 1 := rfl
  have ha' : ((x :: xs)[p + 1]?) = some a := by
    rw [List.getElem?_cons_succ]; exact ha
  have hb' : ((x :: xs)[q + 1]?) = some b := by
    rw [List.getElem?_cons_succ]; exact hb
  have h2 := h (p + 1) (q + 1) (by omega) (by omega) (by omega)
    a b ha' hb'
  exact h2

/-- `slt` antisymmetry: no strict order either way means equal
    (via `toInt` + `omega`). -/
theorem slt_antisymm_eq (x y : BitVec 32)
    (h1 : (x.slt y) = false) (h2 : (y.slt x) = false) : x = y := by
  rw [BitVec.slt_eq_decide] at h1 h2
  simp only [decide_eq_false_iff_not] at h1 h2
  have h3 : x.toInt = y.toInt := by omega
  exact BitVec.eq_of_toInt_eq h3

/-- Membership yields a `getElem?` position (index form for the
    positional `SortedWindow` facts). -/
private theorem mem_index_some (x : BitVec 32) (l : List (BitVec 32))
    (h : x ∈ l) : ∃ k, l[k]? = some x ∧ k < l.length := by
  induction l with
  | nil => simp at h
  | cons y ys ih =>
    rw [List.mem_cons] at h
    cases h with
    | inl heq =>
      refine ⟨0, by simp [heq], ?_⟩
      show (0 : Nat) < ys.length + 1
      omega
    | inr hmem =>
      obtain ⟨k, hk, hlt⟩ := ih hmem
      refine ⟨k + 1, by rw [List.getElem?_cons_succ]; exact hk, ?_⟩
      show k + 1 < ys.length + 1
      omega

/-- The merge of sorted inputs is sorted: every cross pair
    rides sortedness of one side plus one `slt` transitivity
    step through the picked head (ties take from `a`, so the
    take-`a` side needs the antisymmetry case split). -/
theorem mergeChains_sorted (as bs : List (BitVec 32))
    (ha : SortedWindow as 0 as.length)
    (hb : SortedWindow bs 0 bs.length) :
    SortedWindow (mergeChains as bs) 0 (mergeChains as bs).length := by
  induction as, bs using mergeChains.induct
  · rename_i bs
    cases bs with
    | nil => simpa [mergeChains] using ha
    | cons b bs => simpa [mergeChains] using hb
  · rename_i as hne
    cases as with
    | nil => exact absurd rfl hne
    | cons a as =>
      have e : mergeChains (a :: as) [] = (a :: as) := by
        simp [mergeChains]
      rw [e]; exact ha
  · rename_i a as b bs h ih
    have hrest : SortedWindow (mergeChains (a :: as) bs) 0
        (mergeChains (a :: as) bs).length :=
      ih ha (SortedWindow_cons_tail b bs hb)
    have e : mergeChains (a :: as) (b :: bs) =
        b :: mergeChains (a :: as) bs :=
      mergeChains_cons_takeB a as b bs h
    rw [e]
    have hperm : List.Perm (mergeChains (a :: as) bs) ((a :: as) ++ bs) :=
      mergeChains_perm (a :: as) bs
    have hlenA : ((a :: as).length) = as.length + 1 := rfl
    have hlenB : ((b :: bs).length) = bs.length + 1 := rfl
    have hlenM : ((b :: mergeChains (a :: as) bs).length) =
        (mergeChains (a :: as) bs).length + 1 := rfl
    intro p q hlo hpq hqk x y hx hy
    cases p with
    | zero =>
      have h0 : (((b :: mergeChains (a :: as) bs))[0]?) = some b := rfl
      rw [h0] at hx
      have hxb : x = b := by cases hx; rfl
      rw [hxb]
      cases q with
      | zero => omega
      | succ r =>
      have hy' : ((mergeChains (a :: as) bs)[r]?) = some y := by
        simpa using hy
      have hmem : y ∈ mergeChains (a :: as) bs :=
        List.mem_of_getElem? hy'
      have hmem' : y ∈ (a :: as) ++ bs :=
        (List.Perm.mem_iff hperm).mp hmem
      rw [List.mem_append] at hmem'
      cases hmem' with
      | inl hleft =>
        rw [List.mem_cons] at hleft
        cases hleft with
        | inl heq =>
          rw [heq]
          exact sortedInsert_slt_asymm h
        | inr hmemAs =>
          obtain ⟨k, hk, hlt⟩ := mem_index_some y as hmemAs
          have hya : ((a :: as)[k + 1]?) = some y := by
            rw [List.getElem?_cons_succ]; exact hk
          have ha0 : ((a :: as)[0]?) = some a := rfl
          have hyaF : (y.slt a) = false :=
            ha 0 (k + 1) (by omega) (by omega) (by omega) a y ha0 hya
          rw [BitVec.slt_eq_decide] at hyaF h ⊢
          simp only [decide_eq_true_eq, decide_eq_false_iff_not]
            at hyaF h ⊢
          omega
      | inr hmemBs =>
        obtain ⟨k, hk, hlt⟩ := mem_index_some y bs hmemBs
        have hbk : ((b :: bs)[k + 1]?) = some y := by
          rw [List.getElem?_cons_succ]; exact hk
        have hb0 : ((b :: bs)[0]?) = some b := rfl
        exact hb 0 (k + 1) (by omega) (by omega) (by omega) b y hb0 hbk
    | succ r =>
      have hx' : ((mergeChains (a :: as) bs)[r]?) = some x := by
        simpa using hx
      cases q with
      | zero => omega
      | succ s =>
      have hy' : ((mergeChains (a :: as) bs)[s]?) = some y := by
        simpa using hy
      have h2 := hrest r s (by omega) (by omega) (by omega) x y hx' hy'
      exact h2
  · rename_i a as b bs h ih
    have h' : (b.slt a) = false := Bool.eq_false_of_ne_true h
    have hrest : SortedWindow (mergeChains as (b :: bs)) 0
        (mergeChains as (b :: bs)).length :=
      ih (SortedWindow_cons_tail a as ha) hb
    have e : mergeChains (a :: as) (b :: bs) =
        a :: mergeChains as (b :: bs) :=
      mergeChains_cons_takeA a as b bs h'
    rw [e]
    have hperm : List.Perm (mergeChains as (b :: bs)) (as ++ (b :: bs)) :=
      mergeChains_perm as (b :: bs)
    have hlenA : ((a :: as).length) = as.length + 1 := rfl
    have hlenB : ((b :: bs).length) = bs.length + 1 := rfl
    have hlenM : ((a :: mergeChains as (b :: bs)).length) =
        (mergeChains as (b :: bs)).length + 1 := rfl
    intro p q hlo hpq hqk x y hx hy
    cases p with
    | zero =>
      have h0 : (((a :: mergeChains as (b :: bs)))[0]?) = some a := rfl
      rw [h0] at hx
      have hxa : x = a := by cases hx; rfl
      rw [hxa]
      cases q with
      | zero => omega
      | succ r =>
      have hy' : ((mergeChains as (b :: bs))[r]?) = some y := by
        simpa using hy
      have hmem : y ∈ mergeChains as (b :: bs) :=
        List.mem_of_getElem? hy'
      have hmem' : y ∈ as ++ (b :: bs) :=
        (List.Perm.mem_iff hperm).mp hmem
      rw [List.mem_append] at hmem'
      cases hmem' with
      | inl hmemAs =>
        obtain ⟨k, hk, hlt⟩ := mem_index_some y as hmemAs
        have hya : ((a :: as)[k + 1]?) = some y := by
          rw [List.getElem?_cons_succ]; exact hk
        have ha0 : ((a :: as)[0]?) = some a := rfl
        exact ha 0 (k + 1) (by omega) (by omega) (by omega) a y ha0 hya
      | inr hmemBs =>
        rw [List.mem_cons] at hmemBs
        cases hmemBs with
        | inl heq =>
          rw [heq]
          exact h'
        | inr hmemBsTail =>
          obtain ⟨k, hk, hlt⟩ := mem_index_some y bs hmemBsTail
          have hyb : ((b :: bs)[k + 1]?) = some y := by
            rw [List.getElem?_cons_succ]; exact hk
          have hb0 : ((b :: bs)[0]?) = some b := rfl
          have hybF : (y.slt b) = false :=
            hb 0 (k + 1) (by omega) (by omega) (by omega) b y hb0 hyb
          by_cases hab : (a.slt b) = true
          · rw [BitVec.slt_eq_decide] at hybF hab ⊢
            simp only [decide_eq_true_eq, decide_eq_false_iff_not]
              at hybF hab ⊢
            omega
          · have habF : (a.slt b) = false := Bool.eq_false_of_ne_true hab
            have heq : a = b := slt_antisymm_eq a b habF h'
            rw [heq]
            exact hybF
    | succ r =>
      have hx' : ((mergeChains as (b :: bs))[r]?) = some x := by
        simpa using hx
      cases q with
      | zero => omega
      | succ s =>
      have hy' : ((mergeChains as (b :: bs))[s]?) = some y := by
        simpa using hy
      have h2 := hrest r s (by omega) (by omega) (by omega) x y hx' hy'
      exact h2
