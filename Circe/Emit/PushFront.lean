/-
Circe.Emit.PushFront — pillar-1 goal #1: caller-allocated node
construction (`push_front`) over caller-owned `Node { val, next }`.

The corpus (`tests/cpp/push_front.cpp`, entry
`Node *push_front(Node *head, int val)`) takes the list head and a
payload — the list stays caller-owned — allocates one fresh 2-word
cell (`malloc`, infallible by the unbounded convention: no
null-check arm, OOM is out of scope like fuel exhaustion), writes
the payload at `[0]` and the head link at `[1]`, and returns the
fresh cell. The entry never reads the old list: the input head
value is copied blind, so even a dangling head cannot fault (the
fresh cell is disjoint by construction — the bump allocator hands
out an address the pre-state never looked up).

The mirror allocates with the new `.nnew` constructor (the
statement-level `memAlloc m 2` arm), stores the payload with the
new `.psetVal` statement (offset-0 twin of `.psetNext`), swings
the link with `.psetNext`, and returns the cell. The entry is
total: allocation and both stores into the fresh live block always
succeed, so there are no error legs (unlike the append writer leg,
whose caller-provided node needs loud miss legs). The contract is
a cons: `ListSeg m' hd' (v :: vs)` with `hd'` the fresh address.
Freshness is a pre-state hypothesis (`memFind m m.next = none` —
the allocator invariant the runtime maintains); each old node
carries its own lookup, so every old node differs from the fresh
address and the tail rides the allocation plus both stores by
`ListSeg.alloc_stores_other`, node by node.
-/
import Circe.Emit.LinkedReverse

/-! ## P3: `push_front` entry -/

/-- Mangled name of the push-front entry. -/
def pushFrontName : String :=
  "_Z10push_frontP4Nodei"

/-- Canonical CoreIR for `push_front`: allocate the node, write the
    payload, link the head, return the cell. -/
def pushFrontBody : CStmt :=
  (.seq (.let_ "nd" nodeTy .nnew)
    (.seq (.psetVal (.var "nd") (.var "val"))
      (.seq (.psetNext (.var "nd") (.var "head"))
        (.return_ (.var "nd")))))

/-- The push-front entry: `Node*` + `i32` in, `Node*` out. -/
def pushFrontFunc : Func :=
  ⟨pushFrontName,
   [{ name := "head", ty := nodeTy, role := .owned },
    { name := "val", ty := (.i 32), role := .owned }],
   nodeTy,
   pushFrontBody⟩

/-- Push-front environment: head and payload slots, then the
    allocated-cell slot (the entry binds `head` and `val` first,
    then the `let` conses `nd` on the front). -/
def mkPushFrontEnv (head : Option Addr) (v : BitVec 32)
    (nd : Option Addr) : Env :=
  [("nd", .ptrVal nd), ("head", .ptrVal head),
    ("val", .i32 v)]

theorem mkPushFrontEnv_nd (head : Option Addr) (v : BitVec 32)
    (nd : Option Addr) :
    envLookup (mkPushFrontEnv head v nd) "nd" =
      some (.ptrVal nd) := by
  simp [mkPushFrontEnv, envLookup]

theorem mkPushFrontEnv_head (head : Option Addr) (v : BitVec 32)
    (nd : Option Addr) :
    envLookup (mkPushFrontEnv head v nd) "head" =
      some (.ptrVal head) := by
  simp [mkPushFrontEnv, envLookup]

theorem mkPushFrontEnv_val (head : Option Addr) (v : BitVec 32)
    (nd : Option Addr) :
    envLookup (mkPushFrontEnv head v nd) "val" =
      some (.i32 v) := by
  simp [mkPushFrontEnv, envLookup]

/-! ## Forward mirror (total: allocation + two fresh stores) -/

/-- Entry mirror: allocate the 2-word cell, store the payload at
    `[0]`, store the head link at `[1]`, return the fresh address.
    Total — every step succeeds on the fresh live block (the error
    arms are structurally present but unreachable). -/
def pushFrontFwd (m : Mem) (head : Option Addr) (v : BitVec 32) :
    Result (Mem × Option Addr) :=
  match memStore (memAlloc m 2).1 (memAlloc m 2).2
      (memAlloc m 2).2 0 v with
  | .error e => .error e
  | .ok m2 =>
    match memStore m2 (memAlloc m 2).2 (memAlloc m 2).2 1
        (linkWord head) with
    | .error e => .error e
    | .ok m3 => .ok (m3, some (memAlloc m 2).2)

/-! ## Forward contract: allocation conses the cell -/

/-- Pushing conses: the fresh cell holds the payload linked at the
    old head, and the old segment rides the allocation plus both
    fresh-cell stores untouched (`ListSeg.alloc_stores_other`). -/
theorem pushFrontFwd_correct (m : Mem)
    (head : Option Addr) (v : BitVec 32) (vs : List (BitVec 32))
    (m' : Mem) (hd' : Option Addr)
    (hseg : ListSeg m head vs)
    (hmfresh : memFind m m.next = none)
    (hfwd : pushFrontFwd m head v = .ok (m', hd')) :
    ListSeg m' hd' (v :: vs) := by
  simp only [pushFrontFwd] at hfwd
  cases hS1 : memStore (memAlloc m 2).1 (memAlloc m 2).2
      (memAlloc m 2).2 0 v with
  | error e =>
      simp only [hS1] at hfwd
      cases hfwd
  | ok m2 =>
      simp only [hS1] at hfwd
      cases hS2 : memStore m2 (memAlloc m 2).2
          (memAlloc m 2).2 1 (linkWord head) with
      | error e =>
          simp only [hS2] at hfwd
          cases hfwd
      | ok m3 =>
          simp only [hS2] at hfwd
          have hm3 : m3 = m' := by cases hfwd; rfl
          have hhd : some (memAlloc m 2).2 = hd' := by
            cases hfwd; rfl
          have ha : (memAlloc m 2).2 = m.next := memAlloc_next m 2
          have hcell0 : cellsAt (memAlloc m 2).1 (memAlloc m 2).2
              (memAlloc m 2).2 (List.replicate 2 0) := by
            unfold cellsAt
            exact memFind_memAlloc m 2
          have hcell1 := memFind_cellsAt_store _ _ _ _ _ _ _
            hcell0 (by decide) hS1
          have hcell2 := memFind_cellsAt_store _ _ _ _ _ _ _
            hcell1 (by simp) hS2
          have hset : ((List.replicate 2 (0 : BitVec 32)).set 0 v).set 1
              (linkWord head) = [v, linkWord head] := by simp
          rw [hset] at hcell2
          have hnode : nodeAt m3 (memAlloc m 2).2
              (memAlloc m 2).2 v head := hcell2
          have htail : ListSeg m3 head vs :=
            ListSeg.alloc_stores_other hseg hmfresh ha rfl hS1 hS2
          rw [← hm3, ← hhd]
          exact ListSeg.cons hnode htail

/-! ## Evaluator agreement -/

/-- The body evaluates exactly as the forward mirror: allocation,
    payload store, link store, return — each step's agree lemma
    composed by `seq_fallthrough_trans` (error legs propagate by
    `seq_err`, mirroring the forward's match arms). -/
theorem pushFront_body_agree (F : Nat) (m : Mem) (π : Layout)
    (head : Option Addr) (v : BitVec 32) :
    memEvalStmtFuel F pushFrontBody
      [("head", .ptrVal head), ("val", .i32 v)] m π =
      match pushFrontFwd m head v with
      | .ok (m', r) =>
        .ok ((mkPushFrontEnv head v r, m', π), .returned (.ptrVal r))
      | .error e => .error e := by
  simp only [pushFrontBody, mkPushFrontEnv, pushFrontFwd]
  cases hS1 : memStore (memAlloc m 2).1 (memAlloc m 2).2
      (memAlloc m 2).2 0 v with
  | error e =>
      have hlet : memEvalStmtFuel F (.let_ "nd" nodeTy .nnew)
          [("head", .ptrVal head), ("val", .i32 v)] m π =
          .ok ((("nd", .ptrVal (some (memAlloc m 2).2)) ::
            [("head", .ptrVal head), ("val", .i32 v)],
            (memAlloc m 2).1, π), .fellThrough) :=
        memEvalStmtFuel_let_nnew F "nd" nodeTy _ _ _
      have hnd : memEvalExpr (.var "nd")
          ((("nd", .ptrVal (some (memAlloc m 2).2)) ::
            [("head", .ptrVal head), ("val", .i32 v)]))
          (memAlloc m 2).1 π =
          .ok (.ptrVal (some (memAlloc m 2).2)) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ (by simp [envLookup])
      have hval : memEvalExpr (.var "val")
          ((("nd", .ptrVal (some (memAlloc m 2).2)) ::
            [("head", .ptrVal head), ("val", .i32 v)]))
          (memAlloc m 2).1 π =
          .ok (.i32 v) := by
        rw [memEvalExpr_var]
        exact evalExpr_var_hit _ _ _ (by simp [envLookup])
      have hfind : memFind (memAlloc m 2).1 (memAlloc m 2).2 =
          some ⟨(memAlloc m 2).2, true, List.replicate 2 0⟩ :=
        memFind_memAlloc m 2
      have herr := memEvalStmtFuel_psetVal_err F (.var "nd")
        (.var "val") (("nd", .ptrVal (some (memAlloc m 2).2)) ::
        [("head", .ptrVal head), ("val", .i32 v)]) (memAlloc m 2).1 π (memAlloc m 2).2 v ⟨(memAlloc m 2).2, true, List.replicate 2 0⟩ e hnd hval hfind hS1
      rw [memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _
        hlet (memEvalStmtFuel_seq_err F _ _ _ _ _ _ herr)]
  | ok m2 =>
      simp only [hS1]
      cases hS2 : memStore m2 (memAlloc m 2).2
          (memAlloc m 2).2 1 (linkWord head) with
      | error e =>
          simp only [hS2]
          have hlet : memEvalStmtFuel F (.let_ "nd" nodeTy .nnew)
              [("head", .ptrVal head), ("val", .i32 v)] m π =
              .ok ((("nd", .ptrVal (some (memAlloc m 2).2)) ::
                [("head", .ptrVal head), ("val", .i32 v)],
                (memAlloc m 2).1, π), .fellThrough) :=
            memEvalStmtFuel_let_nnew F "nd" nodeTy _ _ _
          have hnd : memEvalExpr (.var "nd")
              ((("nd", .ptrVal (some (memAlloc m 2).2)) ::
                [("head", .ptrVal head), ("val", .i32 v)]))
              (memAlloc m 2).1 π =
              .ok (.ptrVal (some (memAlloc m 2).2)) := by
            rw [memEvalExpr_var]
            exact evalExpr_var_hit _ _ _ (by simp [envLookup])
          have hval : memEvalExpr (.var "val")
              ((("nd", .ptrVal (some (memAlloc m 2).2)) ::
                [("head", .ptrVal head), ("val", .i32 v)]))
              (memAlloc m 2).1 π =
              .ok (.i32 v) := by
            rw [memEvalExpr_var]
            exact evalExpr_var_hit _ _ _ (by simp [envLookup])
          have hfind : memFind (memAlloc m 2).1 (memAlloc m 2).2 =
              some ⟨(memAlloc m 2).2, true, List.replicate 2 0⟩ :=
            memFind_memAlloc m 2
          have hokV := memEvalStmtFuel_psetVal_ok F (.var "nd")
            (.var "val") (("nd", .ptrVal (some (memAlloc m 2).2)) ::
            [("head", .ptrVal head), ("val", .i32 v)]) (memAlloc m 2).1 π (memAlloc m 2).2 v ⟨(memAlloc m 2).2, true, List.replicate 2 0⟩ m2 hnd hval hfind hS1
          have hcell1 : cellsAt m2 (memAlloc m 2).2
              (memAlloc m 2).2
              ((List.replicate 2 (0 : BitVec 32)).set 0 v) :=
            memFind_cellsAt_store _ _ _ _ _ _ _
              (by unfold cellsAt; exact memFind_memAlloc m 2)
              (by decide) hS1
          have hfind2 : memFind m2 (memAlloc m 2).2 =
              some ⟨(memAlloc m 2).2, true,
                (List.replicate 2 (0 : BitVec 32)).set 0 v⟩ := by
            unfold cellsAt at hcell1
            exact hcell1
          have hnd2 : memEvalExpr (.var "nd")
              ((("nd", .ptrVal (some (memAlloc m 2).2)) ::
                [("head", .ptrVal head), ("val", .i32 v)]))
              m2 π =
              .ok (.ptrVal (some (memAlloc m 2).2)) := hnd
          have hlink : memEvalExpr (.var "head")
              ((("nd", .ptrVal (some (memAlloc m 2).2)) ::
                [("head", .ptrVal head), ("val", .i32 v)]))
              m2 π =
              .ok (.ptrVal head) := by
            rw [memEvalExpr_var]
            exact evalExpr_var_hit _ _ _ (by simp [envLookup])
          have herr := memEvalStmtFuel_psetNext_err F (.var "nd")
            (.var "head")
              ((("nd", .ptrVal (some (memAlloc m 2).2)) ::
                [("head", .ptrVal head), ("val", .i32 v)]))
              m2 π (memAlloc m 2).2 head
              ⟨(memAlloc m 2).2, true,
                (List.replicate 2 (0 : BitVec 32)).set 0 v⟩ e
              hnd2 hlink hfind2 hS2
          rw [memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _
            hlet (memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _
              hokV (memEvalStmtFuel_seq_err F _ _ _ _ _ _ herr))]
      | ok m3 =>
          simp only [hS2]
          have hlet : memEvalStmtFuel F (.let_ "nd" nodeTy .nnew)
              [("head", .ptrVal head), ("val", .i32 v)] m π =
              .ok ((("nd", .ptrVal (some (memAlloc m 2).2)) ::
                [("head", .ptrVal head), ("val", .i32 v)],
                (memAlloc m 2).1, π), .fellThrough) :=
            memEvalStmtFuel_let_nnew F "nd" nodeTy _ _ _
          have hnd : memEvalExpr (.var "nd")
              ((("nd", .ptrVal (some (memAlloc m 2).2)) ::
                [("head", .ptrVal head), ("val", .i32 v)]))
              (memAlloc m 2).1 π =
              .ok (.ptrVal (some (memAlloc m 2).2)) := by
            rw [memEvalExpr_var]
            exact evalExpr_var_hit _ _ _ (by simp [envLookup])
          have hval : memEvalExpr (.var "val")
              ((("nd", .ptrVal (some (memAlloc m 2).2)) ::
                [("head", .ptrVal head), ("val", .i32 v)]))
              (memAlloc m 2).1 π =
              .ok (.i32 v) := by
            rw [memEvalExpr_var]
            exact evalExpr_var_hit _ _ _ (by simp [envLookup])
          have hfind : memFind (memAlloc m 2).1 (memAlloc m 2).2 =
              some ⟨(memAlloc m 2).2, true, List.replicate 2 0⟩ :=
            memFind_memAlloc m 2
          have hokV := memEvalStmtFuel_psetVal_ok F (.var "nd")
            (.var "val") (("nd", .ptrVal (some (memAlloc m 2).2)) ::
            [("head", .ptrVal head), ("val", .i32 v)]) (memAlloc m 2).1 π (memAlloc m 2).2 v ⟨(memAlloc m 2).2, true, List.replicate 2 0⟩ m2 hnd hval hfind hS1
          have hcell1 : cellsAt m2 (memAlloc m 2).2
              (memAlloc m 2).2
              ((List.replicate 2 (0 : BitVec 32)).set 0 v) :=
            memFind_cellsAt_store _ _ _ _ _ _ _
              (by unfold cellsAt; exact memFind_memAlloc m 2)
              (by decide) hS1
          have hfind2 : memFind m2 (memAlloc m 2).2 =
              some ⟨(memAlloc m 2).2, true,
                (List.replicate 2 (0 : BitVec 32)).set 0 v⟩ := by
            unfold cellsAt at hcell1
            exact hcell1
          have hnd2 : memEvalExpr (.var "nd")
              ((("nd", .ptrVal (some (memAlloc m 2).2)) ::
                [("head", .ptrVal head), ("val", .i32 v)]))
              m2 π =
              .ok (.ptrVal (some (memAlloc m 2).2)) := hnd
          have hlink : memEvalExpr (.var "head")
              ((("nd", .ptrVal (some (memAlloc m 2).2)) ::
                [("head", .ptrVal head), ("val", .i32 v)]))
              m2 π =
              .ok (.ptrVal head) := by
            rw [memEvalExpr_var]
            exact evalExpr_var_hit _ _ _ (by simp [envLookup])
          have hokN := memEvalStmtFuel_psetNext_ok F (.var "nd")
            (.var "head")
              ((("nd", .ptrVal (some (memAlloc m 2).2)) ::
                [("head", .ptrVal head), ("val", .i32 v)]))
              m2 π (memAlloc m 2).2 head
              ⟨(memAlloc m 2).2, true,
                (List.replicate 2 (0 : BitVec 32)).set 0 v⟩ m3
              hnd2 hlink hfind2 hS2
          have hretE : memEvalExpr (.var "nd")
              ((("nd", .ptrVal (some (memAlloc m 2).2)) ::
                [("head", .ptrVal head), ("val", .i32 v)]))
              m3 π =
              evalExpr (.var "nd")
                ((("nd", .ptrVal (some (memAlloc m 2).2)) ::
                  [("head", .ptrVal head), ("val", .i32 v)])) :=
            memEvalExpr_var _ _ _ _
          have hretV : evalExpr (.var "nd")
              ((("nd", .ptrVal (some (memAlloc m 2).2)) ::
                [("head", .ptrVal head), ("val", .i32 v)])) =
              .ok (.ptrVal (some (memAlloc m 2).2)) :=
            evalExpr_var_hit _ _ _ (by simp [envLookup])
          have hret := memEvalStmtFuel_return F (.var "nd") _ _ _
            _ hretE hretV
          rw [memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _
            hlet (memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _
              hokV (memEvalStmtFuel_seq_fallthrough_trans F _ _ _ _ _ _ _ _ _
                hokN hret))]

/-! ## Entry triple -/

/-- The push-front entry evaluates as the mirror and returns the
    fresh cell holding the payload consed onto the old segment.
    No fuel hypothesis (straight-line, no loops), no exactness
    hypothesis (no link is ever decoded): only the allocator
    freshness the runtime maintains. -/
theorem pushFrontFunc_correct (F : Nat) (m : Mem) (π : Layout)
    (head : Option Addr) (v : BitVec 32) (vs : List (BitVec 32))
    (m' : Mem) (hd' : Option Addr)
    (hseg : ListSeg m head vs)
    (hmfresh : memFind m m.next = none)
    (hfwd : pushFrontFwd m head v = .ok (m', hd')) :
    ∃ ρ', memEvalStmtFuel F pushFrontFunc.body
      [("head", .ptrVal head), ("val", .i32 v)] m π =
      .ok ((ρ', m', π), .returned (.ptrVal hd')) ∧
      ListSeg m' hd' (v :: vs) := by
  have hag := pushFront_body_agree F m π head v
  rw [hfwd] at hag
  have hag2 : memEvalStmtFuel F pushFrontBody
      [("head", .ptrVal head), ("val", .i32 v)] m π =
      .ok ((mkPushFrontEnv head v hd', m', π),
        .returned (.ptrVal hd')) := hag
  have hseg' := pushFrontFwd_correct m head v vs m' hd'
    hseg hmfresh hfwd
  have hbody : pushFrontFunc.body = pushFrontBody := rfl
  rw [hbody]
  exact ⟨_, hag2, hseg'⟩
