/-
Circe.Emit.ListAppend — L-ptr second-shape writer leg: tail
insertion (`list_append`) over caller-owned `Node { val, next }`.

The corpus (`tests/cpp/list_append.cpp`, entry
`Node *list_append(Node * __restrict__ head, Node * __restrict__ nd)`)
takes the head and the new node — both caller-owned — and returns
the new head (`nd` for the empty list). Both params carry
`__restrict__`: two live pointers can always alias, so uniqueness
is claimed in the text and corroborated by a `noalias` oracle
verdict (the single-pointer exemption does not apply; the shape is
listed with the blessed multi-pointer shapes in the gate).

The entry normalizes the node link (`nd->next = nullptr` — loud
on a null `nd`), returns `nd` early on a null head, otherwise
chases `cur` while `cur->next != nullptr`, swings the tail link
to the node, and returns the head. The entry itself never
allocates. Dangling cursors and short blocks abort loudly;
cyclic input exhausts fuel (no visited set — the chase is purely
structural on fuel). Payloads ride along untouched.

The tail chase is read-only; only the two link stores change
memory, so the frame reasoning is one `ListSeg.store_other`
(for the normalize store) plus a single tail-swing snoc
(`ListSeg_swing_snoc` below). Termination is by fuel lockstep.
-/
import Circe.Emit.LinkedReverse

/-! ## L: `list_append` entry -/

/-- Mangled name of the append entry. -/
def listAppendName : String :=
  "_Z11list_appendP4NodeS0_"

/-- The chase seed: head cursor (the G5a init-all-loop-vars
    convention; `nd` stays bound from the entry). -/
def listAppendSeed : CStmt :=
  .let_ "cur" nodeTy (.var "head")

/-- One tail-chase iteration: cursor advance. -/
def listAppendBody : CStmt :=
  .assign "cur" (.pgetNext (.var "cur"))

/-- The tail chase: `cur->next != nullptr`. -/
def listAppendOuter : CStmt :=
  .while_ (.une (.pgetNext (.var "cur")) (.lit .nullptr)) listAppendBody

/-- Canonical CoreIR for `list_append`: normalize the node link,
    early-return the node on a null head, otherwise seed the
    chase, swing the tail link to the node, and return the
    head. -/
def listAppendFunc : Func :=
  ⟨listAppendName,
   [{ name := "head", ty := nodeTy, role := .owned },
    { name := "nd", ty := nodeTy, role := .owned }],
   nodeTy,
   (.seq (.psetNext (.var "nd") (.lit .nullptr))
     (.seq (.if_ (.ueq (.var "head") (.lit .nullptr))
               (.return_ (.var "nd"))
               .skip)
       (.seq listAppendSeed
         (.seq listAppendOuter
           (.seq (.psetNext (.var "cur") (.var "nd"))
             (.return_ (.var "head")))))))⟩

/-- Append environment: cursor, head, then node slots (the layout
    stays empty — link ops resolve through the block's own tag).
    The order matches the entry evaluation: the entry binds `head`
    and `nd` first, then the seed `let` conses `cur` on the front. -/
def mkListAppendEnv (head nd cur : Option Addr) : Env :=
  [("cur", .ptrVal cur), ("head", .ptrVal head),
    ("nd", .ptrVal nd)]

theorem mkListAppendEnv_cur (head nd cur : Option Addr) :
    envLookup (mkListAppendEnv head nd cur) "cur" =
      some (.ptrVal cur) := by
  simp [mkListAppendEnv, envLookup]

theorem mkListAppendEnv_nd (head nd cur : Option Addr) :
    envLookup (mkListAppendEnv head nd cur) "nd" =
      some (.ptrVal nd) := by
  simp [mkListAppendEnv, envLookup]

theorem mkListAppendEnv_head (head nd cur : Option Addr) :
    envLookup (mkListAppendEnv head nd cur) "head" =
      some (.ptrVal head) := by
  simp [mkListAppendEnv, envLookup]

/-! ## Fuel-threaded tail forward -/

/-- Tail chase: mirrors `listAppendOuter` iteration for iteration
    (same fuel, same memory ops — reads only, so the memory is
    threaded unchanged). The guard reads the link, so it is
    evaluated at every fuel level (a dangling cursor or short
    block aborts loudly even at zero fuel); a null link stops
    cleanly and a live link consumes one fuel for the advance —
    the S3a fuel contract for a dereferencing guard. -/
def listAppendTailFwd (F : Nat) (m : Mem) (cur : Option Addr) :
    Result (Mem × Option Addr) :=
  match cur with
  | none => .error .AssertFail
  | some a =>
    match memFind m a with
    | none => .error .AssertFail
    | some b =>
      match memLoad m a b.tag 1 with
      | .error e => .error e
      | .ok w =>
        match addrOfWord w with
        | none => .ok (m, some a)
        | some n =>
          match F with
          | 0 => .error .AssertFail
          | F + 1 => listAppendTailFwd F m (some n)

/-- Entry mirror: normalize the node link, early-return on a null
    head, otherwise chase to the tail, swing the tail link to the
    node, and return the head. -/
def listAppendFwd (F : Nat) (m : Mem) (head nd : Option Addr) :
    Result (Mem × Option Addr) :=
  match nd with
  | none => .error .AssertFail
  | some d =>
    match memFind m d with
    | none => .error .AssertFail
    | some bd =>
      match memStore m d bd.tag 1 (linkWord none) with
      | .error e => .error e
      | .ok m1 =>
        match head with
        | none => .ok (m1, nd)
        | some _ =>
          match listAppendTailFwd F m1 head with
          | .error e => .error e
          | .ok (m2, tail) =>
            match tail with
            | none => .error .AssertFail
            | some t =>
              match memFind m2 t with
              | none => .error .AssertFail
              | some bt =>
                match memStore m2 t bt.tag 1 (linkWord nd) with
                | .error e => .error e
                | .ok m3 => .ok (m3, head)

/-! ## Tail-chase agreement -/

/-- One tail iteration with a live cursor: advance (any fuel). -/
theorem listAppendBody_ok (F : Nat) (m : Mem) (π : Layout)
    (head nd : Option Addr) (a : Addr) (nxt : Option Addr)
    (b : Block) (w : BitVec 32)
    (hfind : memFind m a = some b)
    (hmem : memLoad m a b.tag 1 = .ok w)
    (hdec : addrOfWord w = nxt) :
    memEvalStmtFuel F listAppendBody
      (mkListAppendEnv head nd (some a)) m π =
      .ok (((mkListAppendEnv head nd nxt, m, π)),
        .fellThrough) := by
  have hbody : listAppendBody =
      .assign "cur" (.pgetNext (.var "cur")) := rfl
  have hcur : memEvalExpr (.var "cur")
      (mkListAppendEnv head nd (some a)) m π =
      .ok (.ptrVal (some a)) := by
    rw [memEvalExpr_var]
    exact evalExpr_var_hit _ _ _
      (mkListAppendEnv_cur head nd (some a))
  have hget : memEvalExpr (.pgetNext (.var "cur"))
      (mkListAppendEnv head nd (some a)) m π =
      .ok (.ptrVal nxt) := by
    have h := memEvalExpr_pgetNext_hit (.var "cur")
      (mkListAppendEnv head nd (some a)) m π a w b
      hcur hfind hmem
    rw [hdec] at h
    exact h
  have huC : envUpdate
      (mkListAppendEnv head nd (some a)) "cur" (.ptrVal nxt) =
      some (mkListAppendEnv head nd nxt) := by
    simp [mkListAppendEnv, envUpdate]
  have hassignC := memEvalStmtFuel_assign_mem F "cur"
    (.pgetNext (.var "cur"))
    (mkListAppendEnv head nd (some a)) m π _ _ hget huC
  rw [hbody]
  exact hassignC

/-- One tail iteration with a dangling cursor aborts loudly. -/
theorem listAppendBody_miss (F : Nat) (m : Mem) (π : Layout)
    (head nd : Option Addr) (a : Addr)
    (hfind : memFind m a = none) :
    memEvalStmtFuel F listAppendBody
      (mkListAppendEnv head nd (some a)) m π =
      .error .AssertFail := by
  have hbody : listAppendBody =
      .assign "cur" (.pgetNext (.var "cur")) := rfl
  have hcur : memEvalExpr (.var "cur")
      (mkListAppendEnv head nd (some a)) m π =
      .ok (.ptrVal (some a)) := by
    rw [memEvalExpr_var]
    exact evalExpr_var_hit _ _ _
      (mkListAppendEnv_cur head nd (some a))
  have hpg := memEvalExpr_pgetNext_miss (.var "cur")
    (mkListAppendEnv head nd (some a)) m π a hcur hfind
  have hassign := memEvalStmtFuel_assign_err F "cur"
    (.pgetNext (.var "cur"))
    (mkListAppendEnv head nd (some a)) m π .AssertFail hpg
  rw [hbody]
  exact hassign

/-! ## Tail-chase contract -/

/-- Tail-chase invariant: chasing a nonempty segment returns its
    last cell (memory untouched — read-only), with the last
    payload and footprint membership. Induction on fuel; the
    length bound rules out fuel exhaustion on acyclic input;
    a live link recurses, a null link stops. -/
theorem listAppendTailFwd_invariant (F : Nat) :
    ∀ (m : Mem)
      (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
      (cur : Option Addr) (vs : List (BitVec 32))
      (m' : Mem) (t : Option Addr),
    ListSeg m cur vs →
    vs ≠ [] →
    vs.length ≤ F →
    listAppendTailFwd F m cur = .ok (m', t) →
    m' = m ∧ ∃ a ta lv, t = some a ∧ nodeAt m a ta lv none ∧
      vs.getLast? = some lv ∧ SegMem (m := m) cur a := by
  induction F with
  | zero =>
    intro m hex cur vs m' t hseg hne hlen hf
    have hvs0 : vs = [] := by
      cases vs with
      | nil => rfl
      | cons w ws =>
        simp only [List.length_cons] at hlen
        omega
    exact False.elim (hne hvs0)
  | succ F ih =>
    intro m hex cur vs m' t hseg hne hlen hf
    cases cur with
    | none =>
      simp only [listAppendTailFwd] at hf
      cases hf
    | some a =>
      cases hseg with
      | cons hnode t2 =>
        obtain ⟨v, nxt, rfl, rfl⟩ := nodeAt_parts hnode
        obtain ⟨vs', rfl⟩ := listSegVals t2
        obtain ⟨t', heq⟩ := nodeAt_tag hnode
        rw [← heq] at hnode
        have hfb : memFind m a = some _ := hnode
        have hmem : memLoad m a t' 1 = .ok _ := nodeLoadNext hnode
        unfold listAppendTailFwd at hf
        simp only [hfb, hmem] at hf
        have hdec : addrOfWord (linkWord nxt) = nxt :=
          nodeAt_link_roundtrip hnode hex (by
            intro c' hc'
            cases hnxt : nxt with
            | none => rw [hnxt] at hc'; cases hc'
            | some c'' =>
              cases hc'
              exact ListSeg_head_alloc t2)
        rw [hdec] at hf
        revert hf
        cases hnxt : nxt with
        | none =>
          intro hf
          dsimp only at hf
          have hvs' : vs' = [] := by
            rw [hnxt] at t2
            cases t2 <;> rfl
          subst hvs'
          cases hf
          refine ⟨rfl, a, t', v, rfl, ?_, ?_, ?_⟩
          · rw [hnxt] at hnode
            exact hnode
          · rfl
          · exact SegMem.here hnode
        | some c =>
          intro hf
          dsimp only at hf
          rw [hnxt] at t2
          have hne' : vs' ≠ [] := by
            intro h
            subst h
            have hnn := ListSeg_nil_start t2
            simp at hnn
          have hlen' : vs'.length ≤ F := by
            simp only [List.length_cons] at hlen
            omega
          have hIH := ih m hex (some c) vs' m' t t2 hne' hlen' hf
          obtain ⟨rfl, a', ta, lv, rfl, hnodeT, hlast, hmemT⟩ := hIH
          refine ⟨rfl, a', ta, lv, rfl, hnodeT, ?_, ?_⟩
          · cases vs' with
            | nil => exact False.elim (hne' rfl)
            | cons w ws => simpa using hlast
          · rw [← hnxt] at hmemT
            exact SegMem.there hnode hmemT

/-! ## Tail-swing snoc -/

/-- Swinging the last cell's link to a fresh node extends the
    segment: if `ListSeg m s vs` is nonempty, its last cell `t`
    (null-linked) swings to `d`, and `d` holds `ndv`
    null-linked post-store, then `ListSeg m' s (vs ++ [ndv])`.
    Induction on the segment; the head case identifies the tail
    via link uniqueness, the step case frames the head through
    the elsewhere-store and recurses. -/
theorem ListSeg_swing_snoc {m m' : Mem} {s : Option Addr}
    {vs : List (BitVec 32)}
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (h : ListSeg m s vs) (hne : vs ≠ [])
    {t : Addr} {tt : Nat} {lv : BitVec 32}
    (htail : nodeAt m t tt lv none)
    (hmem : SegMem (m := m) s t)
    {d : Addr} {td : Nat} {ndv : BitVec 32}
    (hnd : nodeAt m' d td ndv none)
    (hstore : memStore m t tt 1 (linkWord (some d)) = .ok m') :
    ListSeg m' s (vs ++ [ndv]) := by
  induction h with
  | nil =>
    cases hmem
  | @cons a _ _ _ _ hnode t2 ih =>
    obtain ⟨v, nxt, rfl, rfl⟩ := nodeAt_parts hnode
    obtain ⟨vs', rfl⟩ := listSegVals t2
    obtain ⟨t'', heq⟩ := nodeAt_tag hnode
    rw [← heq] at hnode
    by_cases hta : t = a
    · subst hta
      have hlink : nxt = none := by
        have h := nodeAt_link_unique htail hnode hex
          (by intro c hc; simp at hc)
          (by
            intro c hc
            cases hnxt : nxt with
            | none => rw [hnxt] at hc; simp at hc
            | some c' =>
              rw [hnxt] at hc
              have heq' : c' = c := by simpa using hc
              subst heq'
              have t2' : ListSeg m (some c') vs' := by
                rw [← hnxt]
                exact t2
              exact ListSeg_head_alloc t2')
        exact h.symm
      subst hlink
      have htag : t'' = tt := by
        have hconj : tt = t'' ∧ lv = v := by
          unfold nodeAt cellsAt at htail hnode
          rw [htail] at hnode
          simpa using hnode
        exact hconj.1.symm
      subst htag
      have hnil : vs' = [] := by
        cases t2 <;> rfl
      subst hnil
      exact ListSeg.cons (nodeStoreNext_nodeAt hnode hstore)
        (ListSeg.cons hnd ListSeg.nil)
    · have hmem' : SegMem (m := m) nxt t := by
        cases hmem with
        | here _ => exact False.elim (hta rfl)
        | @there _ _ _ _ nN hN hm =>
          have hlinkN : nN = nxt :=
            nodeAt_link_unique hN hnode hex
              (by
                intro c hc
                exact SegMem_head_alloc (by rw [hc] at hm; exact hm) c rfl)
              (by
                intro c hc
                cases hnxt : nxt with
                | none => rw [hnxt] at hc; simp at hc
                | some c' =>
                  rw [hnxt] at hc
                  have heq' : c' = c := by simpa using hc
                  subst heq'
                  have t2' : ListSeg m (some c') vs' := by
                    rw [← hnxt]
                    exact t2
                  exact ListSeg_head_alloc t2')
          rw [hlinkN] at hm
          exact hm
      have hne' : vs' ≠ [] := by
        intro h
        subst h
        have hnn := ListSeg_nil_start t2
        rw [hnn] at hmem'
        cases hmem'
      have hnodeF : nodeAt m' a t'' v nxt :=
        nodeAt_store_other_fwd hnode hstore (fun h => hta h.symm)
      exact ListSeg.cons hnodeF (ih hne' hmem')

/-! ## Append contract -/

/-- Top-level append contract: normalizing the node link, chasing
    a whole segment to its tail, and swinging the tail link to the
    node yields the snoc segment (the head is returned, or the
    node for the empty list). The caller-debt disjointness (`d`
    outside the head footprint) frames the normalize store; the
    tail swing is the snoc lemma. -/
theorem listAppendFwd_correct (F : Nat) (m : Mem)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (head : Option Addr) (d : Addr) (vs : List (BitVec 32))
    (ndv : BitVec 32) (td : Nat) (n0 : Option Addr)
    (m' : Mem) (hd' : Option Addr)
    (hseg : ListSeg m head vs)
    (hnd : nodeAt m d td ndv n0)
    (hout : ∀ b, SegMem (m := m) head b → b ≠ d)
    (hlen : vs.length ≤ F)
    (hfwd : listAppendFwd F m head (some d) = .ok (m', hd')) :
    ListSeg m' hd' (vs ++ [ndv]) := by
  simp only [listAppendFwd] at hfwd
  cases hF : memFind m d with
  | none =>
    have hcon : memFind m d = some _ := hnd
    rw [hF] at hcon
    simp at hcon
  | some bd =>
    simp only [hF] at hfwd
    cases hS : memStore m d bd.tag 1 (linkWord none) with
    | error e =>
      simp only [hS] at hfwd
      cases hfwd
    | ok m1 =>
      simp only [hS] at hfwd
      have htd : bd.tag = td := by
        have h2 : memFind m d = some _ := hnd
        rw [hF] at h2
        cases h2
        rfl
      rw [htd] at hS
      have hndN : nodeAt m1 d td ndv none :=
        nodeStoreNext_nodeAt hnd hS
      have hsegF : ListSeg m1 head vs :=
        ListSeg.store_other hseg hS hout
      have hhex1 : ∀ y, (memFind m1 y).isSome = true → y + 1 < 2 ^ 32 :=
        hex_store hex hS (by
          have hfd : memFind m d = some _ := hnd
          simp [hfd])
      cases hhead : head with
      | none =>
        simp only [hhead] at hfwd
        cases hfwd
        have hvsnil : vs = [] := by
          rw [hhead] at hseg
          cases hseg with
          | nil => rfl
        subst hvsnil
        exact ListSeg.cons hndN ListSeg.nil
      | some a =>
        simp only [hhead] at hfwd
        rw [hhead] at hseg hsegF hout
        have hne : vs ≠ [] := by
          intro h
          subst h
          have hnn := ListSeg_nil_start hseg
          simp at hnn
        -- The appended node stays outside the normalized footprint:
        -- re-establish outsideness through the normalize store
        -- (first-arrival argument, `SegMem_store_avoid`).
        have hheadA : ∀ y, (some a) = some y → y ≠ d := by
          intro y hy h
          have hay : a = d := by simpa using hy.trans (congrArg some h)
          have hsegD : ListSeg m (some d) vs := by
            rw [← hay]
            exact hseg
          have houtD : ∀ b, SegMem (m := m) (some d) b → b ≠ d := by
            intro b hb
            rw [← hay] at hb
            exact hout b hb
          cases hsegD with
          | cons hN _ => exact houtD d (SegMem.here hN) rfl
        have hout1 : ∀ b, SegMem (m := m1) (some a) b → b ≠ d :=
          SegMem_store_avoid hS hseg hex hhex1 hheadA hout
        cases hT : listAppendTailFwd F m1 (some a) with
        | error e =>
          simp only [hT] at hfwd
          cases hfwd
        | ok p =>
          obtain ⟨m2, tail⟩ := p
          simp only [hT] at hfwd
          have hInv := listAppendTailFwd_invariant F m1 hhex1 (some a) vs
            m2 tail hsegF hne hlen hT
          obtain ⟨hm2, t', tt', lv, htailEq, hnodeT, hlast, hmemT⟩ := hInv
          subst m2
          simp only [htailEq] at hfwd
          cases hF2 : memFind m1 t' with
          | none =>
            have hcon : memFind m1 t' = some _ := hnodeT
            rw [hF2] at hcon
            simp at hcon
          | some bt =>
            simp only [hF2] at hfwd
            cases hS2 : memStore m1 t' bt.tag 1 (linkWord (some d)) with
            | error e =>
              simp only [hS2] at hfwd
              cases hfwd
            | ok m3 =>
              simp only [hS2] at hfwd
              have hm3 : m3 = m' := by cases hfwd; rfl
              have hhd : hd' = some a := by cases hfwd; rfl
              have htt : bt.tag = tt' := by
                have h2 : memFind m1 t' = some _ := hnodeT
                rw [hF2] at h2
                cases h2
                rfl
              rw [htt] at hS2
              have hdout : t' ≠ d := hout1 t' hmemT
              have hndS : nodeAt m3 d td ndv none :=
                nodeAt_store_other_fwd hndN hS2 (fun h => hdout h.symm)
              rw [← hm3, hhd]
              exact ListSeg_swing_snoc hhex1 hsegF hne hnodeT hmemT hndS hS2

/-! ## Tail-chase/evaluator agreement -/

/-- Tail-chase/evaluator agreement: `listAppendOuter` at any fuel
    agrees with the tail forward (same fuel, same memory ops,
    same order). The guard reads the link, so memory is cased
    first and fuel afterwards. -/
theorem listAppendTail_agree (F : Nat) :
    ∀ (m : Mem) (π : Layout) (head nd cur : Option Addr),
    memEvalStmtFuel F listAppendOuter
      (mkListAppendEnv head nd cur) m π =
      match listAppendTailFwd F m cur with
      | .ok (m', t) =>
        .ok (((mkListAppendEnv head nd t, m', π)), .fellThrough)
      | .error e => .error e := by
  induction F with
  | zero =>
    intro m π head nd cur
    cases cur with
    | none =>
      have hcur : memEvalExpr (.var "cur")
          (mkListAppendEnv head nd none) m π =
          .ok (.ptrVal none) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ (mkListAppendEnv_cur _ _ _)
      have hpg := memEvalExpr_pgetNext_null (.var "cur")
        (mkListAppendEnv head nd none) m π hcur
      have hnull : memEvalExpr (.lit .nullptr)
          (mkListAppendEnv head nd none) m π =
          .ok (.ptrVal none) := by
        simp [memEvalExpr, litVal]
      have hg : memEvalExpr (.une (.pgetNext (.var "cur")) (.lit .nullptr))
          (mkListAppendEnv head nd none) m π = .error .AssertFail := by
        unfold memEvalExpr
        rw [hpg, hnull]
      have hw : memEvalStmtFuel 0 listAppendOuter
          (mkListAppendEnv head nd none) m π = .error .AssertFail := by
        simp only [listAppendOuter, memEvalStmtFuel, memEvalStmtZero,
          memEvalStmtWith, memEvalStmtZeroHandler, hg]
      rw [hw]
      simp only [listAppendTailFwd]
    | some a =>
      have hcur : memEvalExpr (.var "cur")
          (mkListAppendEnv head nd (some a)) m π =
          .ok (.ptrVal (some a)) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ (mkListAppendEnv_cur _ _ _)
      have hnull : memEvalExpr (.lit .nullptr)
          (mkListAppendEnv head nd (some a)) m π =
          .ok (.ptrVal none) := by
        simp [memEvalExpr, litVal]
      cases hF : memFind m a with
      | none =>
        have hpg := memEvalExpr_pgetNext_miss (.var "cur")
          (mkListAppendEnv head nd (some a)) m π a hcur hF
        have hg : memEvalExpr (.une (.pgetNext (.var "cur")) (.lit .nullptr))
            (mkListAppendEnv head nd (some a)) m π =
            .error .AssertFail := by
          unfold memEvalExpr
          rw [hpg, hnull]
        have hw : memEvalStmtFuel 0 listAppendOuter
            (mkListAppendEnv head nd (some a)) m π =
            .error .AssertFail := by
          simp only [listAppendOuter, memEvalStmtFuel, memEvalStmtZero,
            memEvalStmtWith, memEvalStmtZeroHandler, hg]
        rw [hw]
        simp only [listAppendTailFwd, hF]
      | some b =>
        cases hL : memLoad m a b.tag 1 with
        | error werr =>
          have hpg := memEvalExpr_pgetNext_err (.var "cur")
            (mkListAppendEnv head nd (some a)) m π a b werr
            hcur hF hL
          have hg : memEvalExpr (.une (.pgetNext (.var "cur")) (.lit .nullptr))
              (mkListAppendEnv head nd (some a)) m π =
              .error werr := by
            unfold memEvalExpr
            rw [hpg, hnull]
          have hw : memEvalStmtFuel 0 listAppendOuter
              (mkListAppendEnv head nd (some a)) m π =
              .error werr := by
            simp only [listAppendOuter, memEvalStmtFuel, memEvalStmtZero,
              memEvalStmtWith, memEvalStmtZeroHandler, hg]
          rw [hw]
          simp only [listAppendTailFwd, hF, hL]
        | ok w =>
          have hpg := memEvalExpr_pgetNext_hit (.var "cur")
            (mkListAppendEnv head nd (some a)) m π a w b
            hcur hF hL
          have hg : memEvalExpr (.une (.pgetNext (.var "cur")) (.lit .nullptr))
              (mkListAppendEnv head nd (some a)) m π =
              .ok (.b (addrOfWord w != none)) :=
            memEvalExpr_une_ptrVal _ _ _ _ _
              (addrOfWord w) none hpg hnull
          cases haw : addrOfWord w with
          | none =>
            rw [haw] at hg
            have hbe : ((none : Option Addr) != none) = false := by simp
            rw [hbe] at hg
            have hw : memEvalStmtFuel 0 listAppendOuter
                (mkListAppendEnv head nd (some a)) m π =
                .ok (((mkListAppendEnv head nd (some a), m, π)),
                  .fellThrough) :=
              memEvalStmtFuel_while_false _ _ listAppendBody _ _ _ hg
            rw [hw]
            simp only [listAppendTailFwd, hF, hL, haw]
          | some n =>
            rw [haw] at hg
            have hbe : ((some n != none)) = true := by simp
            rw [hbe] at hg
            have hw : memEvalStmtFuel 0 listAppendOuter
                (mkListAppendEnv head nd (some a)) m π =
                .error .AssertFail := by
              simp only [listAppendOuter, memEvalStmtFuel, memEvalStmtZero,
                memEvalStmtWith, memEvalStmtZeroHandler, hg]
            rw [hw]
            simp only [listAppendTailFwd, hF, hL, haw]
  | succ F ih =>
    intro m π head nd cur
    cases cur with
    | none =>
      have hcur : memEvalExpr (.var "cur")
          (mkListAppendEnv head nd none) m π =
          .ok (.ptrVal none) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ (mkListAppendEnv_cur _ _ _)
      have hpg := memEvalExpr_pgetNext_null (.var "cur")
        (mkListAppendEnv head nd none) m π hcur
      have hnull : memEvalExpr (.lit .nullptr)
          (mkListAppendEnv head nd none) m π =
          .ok (.ptrVal none) := by
        simp [memEvalExpr, litVal]
      have hg : memEvalExpr (.une (.pgetNext (.var "cur")) (.lit .nullptr))
          (mkListAppendEnv head nd none) m π = .error .AssertFail := by
        unfold memEvalExpr
        rw [hpg, hnull]
      have hw : memEvalStmtFuel (F + 1) listAppendOuter
          (mkListAppendEnv head nd none) m π = .error .AssertFail := by
        simp only [listAppendOuter, memEvalStmtFuel, memEvalStmtWith,
          memEvalSuccHandler, hg]
      rw [hw]
      simp only [listAppendTailFwd]
    | some a =>
      have hcur : memEvalExpr (.var "cur")
          (mkListAppendEnv head nd (some a)) m π =
          .ok (.ptrVal (some a)) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ (mkListAppendEnv_cur _ _ _)
      have hnull : memEvalExpr (.lit .nullptr)
          (mkListAppendEnv head nd (some a)) m π =
          .ok (.ptrVal none) := by
        simp [memEvalExpr, litVal]
      cases hF : memFind m a with
      | none =>
        have hpg := memEvalExpr_pgetNext_miss (.var "cur")
          (mkListAppendEnv head nd (some a)) m π a hcur hF
        have hg : memEvalExpr (.une (.pgetNext (.var "cur")) (.lit .nullptr))
            (mkListAppendEnv head nd (some a)) m π =
            .error .AssertFail := by
          unfold memEvalExpr
          rw [hpg, hnull]
        have hw : memEvalStmtFuel (F + 1) listAppendOuter
            (mkListAppendEnv head nd (some a)) m π =
            .error .AssertFail := by
          simp only [listAppendOuter, memEvalStmtFuel, memEvalStmtWith,
            memEvalSuccHandler, hg]
        rw [hw]
        simp only [listAppendTailFwd, hF]
      | some b =>
        cases hL : memLoad m a b.tag 1 with
        | error werr =>
          have hpg := memEvalExpr_pgetNext_err (.var "cur")
            (mkListAppendEnv head nd (some a)) m π a b werr
            hcur hF hL
          have hg : memEvalExpr (.une (.pgetNext (.var "cur")) (.lit .nullptr))
              (mkListAppendEnv head nd (some a)) m π =
              .error werr := by
            unfold memEvalExpr
            rw [hpg, hnull]
          have hw : memEvalStmtFuel (F + 1) listAppendOuter
              (mkListAppendEnv head nd (some a)) m π =
              .error werr := by
            simp only [listAppendOuter, memEvalStmtFuel, memEvalStmtWith,
              memEvalSuccHandler, hg]
          rw [hw]
          simp only [listAppendTailFwd, hF, hL]
        | ok w =>
          have hpg := memEvalExpr_pgetNext_hit (.var "cur")
            (mkListAppendEnv head nd (some a)) m π a w b
            hcur hF hL
          have hg : memEvalExpr (.une (.pgetNext (.var "cur")) (.lit .nullptr))
              (mkListAppendEnv head nd (some a)) m π =
              .ok (.b (addrOfWord w != none)) :=
            memEvalExpr_une_ptrVal _ _ _ _ _
              (addrOfWord w) none hpg hnull
          cases haw : addrOfWord w with
          | none =>
            rw [haw] at hg
            have hbe : ((none : Option Addr) != none) = false := by simp
            rw [hbe] at hg
            have hw : memEvalStmtFuel (F + 1) listAppendOuter
                (mkListAppendEnv head nd (some a)) m π =
                .ok (((mkListAppendEnv head nd (some a), m, π)),
                  .fellThrough) :=
              memEvalStmtFuel_while_false _ _ listAppendBody _ _ _ hg
            rw [hw]
            simp only [listAppendTailFwd, hF, hL, haw]
          | some n =>
            rw [haw] at hg hpg
            have hbe : ((some n != none)) = true := by simp
            rw [hbe] at hg
            have hw := memEvalStmtFuel_while_true F
              (.une (.pgetNext (.var "cur")) (.lit .nullptr))
              listAppendBody _ _ _ hg
            simp only [listAppendOuter] at hw ⊢
            rw [hw]
            have huN : envUpdate (mkListAppendEnv head nd (some a)) "cur"
                (.ptrVal (some n)) =
                some (mkListAppendEnv head nd (some n)) := by
              simp [mkListAppendEnv, envUpdate]
            have hbody : memEvalStmtFuel F listAppendBody
                (mkListAppendEnv head nd (some a)) m π =
                .ok (((mkListAppendEnv head nd (some n), m, π)),
                  .fellThrough) := by
              have ha := memEvalStmtFuel_assign_mem F "cur"
                (.pgetNext (.var "cur"))
                (mkListAppendEnv head nd (some a)) m π
                (.ptrVal (some n)) (mkListAppendEnv head nd (some n))
                hpg huN
              simpa [listAppendBody] using ha
            rw [hbody]
            dsimp only
            have hIH := ih m π head nd (some n)
            unfold listAppendTailFwd at ⊢
            simp only [hF, hL, haw] at ⊢
            exact hIH

/-! ## Entry Hoare triple -/

/-- Entry Hoare triple (thin sugar): normalize, early-return on a
    null head, otherwise seed, chase (bridge), swing, and return
    the head — then the pure contract. -/
theorem listAppendFunc_correct (F : Nat) (m : Mem) (π : Layout)
    (hex : ∀ x, (memFind m x).isSome = true → x + 1 < 2 ^ 32)
    (head : Option Addr) (d : Addr) (vs : List (BitVec 32))
    (ndv : BitVec 32) (td : Nat) (n0 : Option Addr)
    (m' : Mem) (hd' : Option Addr)
    (hseg : ListSeg m head vs)
    (hnd : nodeAt m d td ndv n0)
    (hout : ∀ b, SegMem (m := m) head b → b ≠ d)
    (hlen : vs.length ≤ F)
    (hfwd : listAppendFwd F m head (some d) = .ok (m', hd')) :
    ∃ ρ', memEvalStmtFuel F listAppendFunc.body
      [("head", .ptrVal head), ("nd", .ptrVal (some d))] m π =
      .ok ((ρ', m', π), .returned (.ptrVal hd')) ∧
      ListSeg m' hd' (vs ++ [ndv]) := by
  have hseg' := listAppendFwd_correct F m hex head d vs ndv td n0 m' hd'
    hseg hnd hout hlen hfwd
  simp only [listAppendFwd] at hfwd
  cases hF : memFind m d with
  | none =>
    have hcon : memFind m d = some _ := hnd
    rw [hF] at hcon
    simp at hcon
  | some bd =>
    simp only [hF] at hfwd
    cases hS : memStore m d bd.tag 1 (linkWord none) with
    | error e =>
      simp only [hS] at hfwd
      cases hfwd
    | ok m1 =>
      simp only [hS] at hfwd
      -- Normalize: `nd->next = nullptr` (env and layout untouched).
      have hndE : memEvalExpr (.var "nd")
          [("head", .ptrVal head), ("nd", .ptrVal (some d))] m π =
          .ok (.ptrVal (some d)) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ (by simp [envLookup])
      have hnullE : memEvalExpr (.lit .nullptr)
          [("head", .ptrVal head), ("nd", .ptrVal (some d))] m π =
          .ok (.ptrVal none) := by
        simp [memEvalExpr, litVal]
      have hnorm := memEvalStmtFuel_psetNext_ok F (.var "nd")
        (.lit .nullptr)
        [("head", .ptrVal head), ("nd", .ptrVal (some d))] m π
        d none bd m1 hndE hnullE hF hS
      have hnullE1 : memEvalExpr (.lit .nullptr)
          [("head", .ptrVal head), ("nd", .ptrVal (some d))] m1 π =
          .ok (.ptrVal none) := by
        simp [memEvalExpr, litVal]
      cases hhead : head with
      | none =>
        simp only [hhead] at hfwd
        rw [hhead] at hnorm hnullE1
        have hm1 : m1 = m' := by cases hfwd; rfl
        have hhd : hd' = some d := by cases hfwd; rfl
        -- Null head: the guard is true, return the node.
        have hheadE : memEvalExpr (.var "head")
            [("head", .ptrVal none), ("nd", .ptrVal (some d))] m1 π =
            .ok (.ptrVal none) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _ (by simp [envLookup])
        have hif : memEvalExpr
            (.ueq (.var "head") (.lit .nullptr))
            [("head", .ptrVal none), ("nd", .ptrVal (some d))] m1 π =
            .ok (.b true) := by
          have hg := memEvalExpr_ueq_ptrVal _ _ _ _ _ none none
            hheadE hnullE1
          have hbe : ((none : Option Addr) == none) = true := by simp
          rw [hbe] at hg
          exact hg
        have hretNdE : memEvalExpr (.var "nd")
            [("head", .ptrVal none), ("nd", .ptrVal (some d))] m1 π =
            evalExpr (.var "nd")
              [("head", .ptrVal none), ("nd", .ptrVal (some d))] :=
          memEvalExpr_var _ _ _ _
        have hretNdV : evalExpr (.var "nd")
            [("head", .ptrVal none), ("nd", .ptrVal (some d))] =
            .ok (.ptrVal (some d)) :=
          evalExpr_var_hit _ _ _ (by simp [envLookup])
        have hret := memEvalStmtFuel_return F (.var "nd")
          [("head", .ptrVal none), ("nd", .ptrVal (some d))] m1 π _
          hretNdE hretNdV
        have hifT := memEvalStmtFuel_if_true F
          (.ueq (.var "head") (.lit .nullptr))
          (.return_ (.var "nd")) .skip _ _ _ hif
        have hbody : listAppendFunc.body =
            (.seq (.psetNext (.var "nd") (.lit .nullptr))
              (.seq (.if_ (.ueq (.var "head") (.lit .nullptr))
                      (.return_ (.var "nd")) .skip)
                (.seq listAppendSeed
                  (.seq listAppendOuter
                    (.seq (.psetNext (.var "cur") (.var "nd"))
                      (.return_ (.var "head"))))))) := rfl
        have heval : memEvalStmtFuel F listAppendFunc.body
            [("head", .ptrVal none), ("nd", .ptrVal (some d))] m π =
            .ok ((([("head", .ptrVal none),
              ("nd", .ptrVal (some d))], m1, π)),
              .returned (.ptrVal (some d))) := by
          rw [hbody]
          have c1 := memEvalStmtFuel_seq_fallthrough F
            (.psetNext (.var "nd") (.lit .nullptr))
            (.seq (.if_ (.ueq (.var "head") (.lit .nullptr))
                    (.return_ (.var "nd")) .skip)
              (.seq listAppendSeed
                (.seq listAppendOuter
                  (.seq (.psetNext (.var "cur") (.var "nd"))
                    (.return_ (.var "head"))))))
            _ _ _ _ _ _ hnorm
          rw [c1]
          exact memEvalStmtFuel_seq_return F _ _ _ _ _ _ _ _ _
            (hifT.trans hret)
        rw [← hm1, hhd] at hseg' ⊢
        exact ⟨_, heval, hseg'⟩
      | some a =>
        simp only [hhead] at hfwd
        rw [hhead] at hnorm hnullE1
        -- Non-null head: the guard is false, take the skip leg.
        have hheadE : memEvalExpr (.var "head")
            [("head", .ptrVal (some a)), ("nd", .ptrVal (some d))] m1 π =
            .ok (.ptrVal (some a)) := by
          rw [memEvalExpr_var]
          exact evalExpr_var_hit _ _ _ (by simp [envLookup])
        have hif : memEvalExpr
            (.ueq (.var "head") (.lit .nullptr))
            [("head", .ptrVal (some a)), ("nd", .ptrVal (some d))] m1 π =
            .ok (.b false) := by
          have hg := memEvalExpr_ueq_ptrVal _ _ _ _ _ (some a) none
            hheadE hnullE1
          have hbe : ((some a : Option Addr) == none) = false := by simp
          rw [hbe] at hg
          exact hg
        have hskip : memEvalStmtFuel F .skip
            [("head", .ptrVal (some a)), ("nd", .ptrVal (some d))] m1 π =
            .ok ((([("head", .ptrVal (some a)),
              ("nd", .ptrVal (some d))], m1, π)), .fellThrough) := by
          cases F <;> rfl
        have hifF := memEvalStmtFuel_if_false F
          (.ueq (.var "head") (.lit .nullptr))
          (.return_ (.var "nd")) .skip _ _ _ hif
        -- Seed: cursor `let` conses the canonical environment.
        have hseedE : memEvalExpr (.var "head")
            [("head", .ptrVal (some a)), ("nd", .ptrVal (some d))] m1 π =
            evalExpr (.var "head")
              [("head", .ptrVal (some a)), ("nd", .ptrVal (some d))] :=
          memEvalExpr_var _ _ _ _
        have hseedV : evalExpr (.var "head")
            [("head", .ptrVal (some a)), ("nd", .ptrVal (some d))] =
            .ok (.ptrVal (some a)) :=
          evalExpr_var_hit _ _ _ (by simp [envLookup])
        have hseed : memEvalStmtFuel F listAppendSeed
            [("head", .ptrVal (some a)), ("nd", .ptrVal (some d))] m1 π =
            .ok ((mkListAppendEnv (some a) (some d) (some a), m1, π),
              .fellThrough) := by
          have hL := memEvalStmtFuel_let_pure F "cur" nodeTy
            (.var "head")
            [("head", .ptrVal (some a)), ("nd", .ptrVal (some d))] m1 π
            (.ptrVal (some a)) (by simp) (by simp) (by simp) (by simp)
            hseedE hseedV
          simpa [listAppendSeed, mkListAppendEnv] using hL
        -- Chase: the bridge fires the tail forward.
        cases hT : listAppendTailFwd F m1 (some a) with
        | error e =>
          simp only [hT] at hfwd
          cases hfwd
        | ok p =>
          obtain ⟨m2, tail⟩ := p
          simp only [hT] at hfwd
          have hloop := listAppendTail_agree F m1 π (some a) (some d)
            (some a)
          simp only [hT] at hloop
          -- Swing: the tail link takes the node.
          cases htail : tail with
          | none =>
            simp only [htail] at hfwd
            cases hfwd
          | some t =>
            simp only [htail] at hfwd
            cases hF2 : memFind m2 t with
            | none =>
              simp only [hF2] at hfwd
              cases hfwd
            | some bt =>
              simp only [hF2] at hfwd
              cases hS2 : memStore m2 t bt.tag 1 (linkWord (some d)) with
              | error e =>
                simp only [hS2] at hfwd
                cases hfwd
              | ok m3 =>
                simp only [hS2] at hfwd
                have hm3 : m3 = m' := by cases hfwd; rfl
                have hhd : hd' = some a := by cases hfwd; rfl
                have hcurE : memEvalExpr (.var "cur")
                    (mkListAppendEnv (some a) (some d) tail) m2 π =
                    .ok (.ptrVal (some t)) := by
                  rw [htail]
                  rw [memEvalExpr_var]
                  exact evalExpr_var_hit _ _ _
                    (by simp [mkListAppendEnv, envLookup])
                have hndE2 : memEvalExpr (.var "nd")
                    (mkListAppendEnv (some a) (some d) tail) m2 π =
                    .ok (.ptrVal (some d)) := by
                  rw [htail]
                  rw [memEvalExpr_var]
                  exact evalExpr_var_hit _ _ _
                    (by simp [mkListAppendEnv, envLookup])
                have hswing := memEvalStmtFuel_psetNext_ok F
                  (.var "cur") (.var "nd")
                  (mkListAppendEnv (some a) (some d) tail) m2 π
                  t (some d) bt m3 hcurE hndE2 hF2 hS2
                have hretE : memEvalExpr (.var "head")
                    (mkListAppendEnv (some a) (some d) tail) m3 π =
                    evalExpr (.var "head")
                      (mkListAppendEnv (some a) (some d) tail) :=
                  memEvalExpr_var _ _ _ _
                have hretV : evalExpr (.var "head")
                    (mkListAppendEnv (some a) (some d) tail) =
                    .ok (.ptrVal (some a)) := by
                  rw [htail]
                  exact evalExpr_var_hit _ _ _
                    (by simp [mkListAppendEnv, envLookup])
                have hret := memEvalStmtFuel_return F (.var "head")
                  (mkListAppendEnv (some a) (some d) tail) m3 π _
                  hretE hretV
                have hbody : listAppendFunc.body =
            (.seq (.psetNext (.var "nd") (.lit .nullptr))
                      (.seq (.if_ (.ueq (.var "head") (.lit .nullptr))
                              (.return_ (.var "nd")) .skip)
                        (.seq listAppendSeed
                          (.seq listAppendOuter
                            (.seq (.psetNext (.var "cur") (.var "nd"))
                              (.return_ (.var "head"))))))) := rfl
                have heval : memEvalStmtFuel F listAppendFunc.body
                    [("head", .ptrVal (some a)),
                      ("nd", .ptrVal (some d))] m π =
                    .ok (((mkListAppendEnv (some a) (some d) tail, m3,
                      π)), .returned (.ptrVal (some a))) := by
                  rw [hbody]
                  have c1 := memEvalStmtFuel_seq_fallthrough F
                    (.psetNext (.var "nd") (.lit .nullptr))
                    (.seq (.if_ (.ueq (.var "head") (.lit .nullptr))
                            (.return_ (.var "nd")) .skip)
                      (.seq listAppendSeed
                        (.seq listAppendOuter
                          (.seq (.psetNext (.var "cur") (.var "nd"))
                            (.return_ (.var "head"))))))
                    _ _ _ _ _ _ hnorm
                  rw [c1]
                  have c2 := memEvalStmtFuel_seq_fallthrough F
                    (.if_ (.ueq (.var "head") (.lit .nullptr))
                      (.return_ (.var "nd")) .skip)
                    (.seq listAppendSeed
                      (.seq listAppendOuter
                        (.seq (.psetNext (.var "cur") (.var "nd"))
                          (.return_ (.var "head")))))
                    _ _ _ _ _ _
                    (hifF.trans hskip)
                  rw [c2]
                  have c3 := memEvalStmtFuel_seq_fallthrough F
                    listAppendSeed
                    (.seq listAppendOuter
                      (.seq (.psetNext (.var "cur") (.var "nd"))
                        (.return_ (.var "head"))))
                    _ _ _ _ _ _ hseed
                  rw [c3]
                  have c4 := memEvalStmtFuel_seq_fallthrough F
                    listAppendOuter
                    (.seq (.psetNext (.var "cur") (.var "nd"))
                      (.return_ (.var "head")))
                    _ _ _ _ _ _ hloop
                  rw [c4]
                  have c5 := memEvalStmtFuel_seq_fallthrough F
                    (.psetNext (.var "cur") (.var "nd"))
                    (.return_ (.var "head")) _ _ _ _ _ _ hswing
                  rw [c5]
                  rw [htail] at hret ⊢
                  exact hret
                rw [← hm3, hhd] at hseg' ⊢
                exact ⟨_, heval, hseg'⟩
