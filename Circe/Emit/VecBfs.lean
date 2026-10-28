/-
Circe.Emit.VecBfs — B-slice breadth-first traversal over a flat
row-major matrix: the `bfs_order` entry.

The corpus (`tests/cpp/bfs_order.cpp`: const-matrix `m`,
mut-visited `vis`, mut caller queue `q`, mut visit-order record
`order`, `u64` dimension `n` and source `src`, `u64`
reachable-count out) captures the entry + the const/mut `at()`
composers + `_M_range_check` + both `operator[]` + `size`. The
entry functionalizes to a fused seed (visited mark plus queue
enqueue of the source through the mut-`at()` checked writes
behind their `ult` guards, the `at()`-throw precedent) plus the
outer queue-drain `while_` (`head != tail`) around the inner
row-scan `while_` (`u < n`, the G1 loop shape): each dequeue
records the visit in `order[head]` (`head` already counts drained
vertices, so no extra cursor), then each row scans
`m.at(v * n + u)` (the G2 index computation) and enqueues every
unvisited non-zero neighbor (gate one `m.at(v*n+u) != 0`, gate
two `vis.at(u) == 0`), counting each first visit. Every vector
op sits behind its own fused `ult` guard (seed-visited,
seed-queue, dequeue-read, visit-record, matrix-read,
visited-read, queue-store); each miss is the `at()`-throw
`AssertFail`, including wrapping index computations that land
out of range. The cursor and count advances are pure wrapping
`uadd` (no `usub` — the head cursor only advances); the
dequeue-read widens through `u64ofI32` (C integer promotion),
the three stores narrow through `i32ofU64` (the V2 cast
precedent), and the visit record relies on the
narrow-after-widen roundtrip.

Termination is by fuel lockstep, not by measure: the forwards
thread the same fuel as the evaluator (`while_` is the only
consumer, one per iteration; zero fuel exits cleanly on a false
condition and aborts loudly on a live one — the S3a fuel
contract), and the entry theorem holds for every fuel by
induction. A fuel-free traversal would need the visited-freshness
measure up front; lockstep keeps the graph argument out of the
proof — the forward mirrors the loop nest exactly (the G1
`markFold` precedent), and agreement with native is pinned by
spec edges plus the Diff fuzz.
-/
import Circe.Emit.VecStackPush

/-! ## B: `bfs_order` entry -/

/-- Mangled name of the BFS entry. -/
def bfsName : String :=
  "_Z9bfs_orderRKSt6vectorIiSaIiEERS1_S4_S4_mm"

/-- The G2 row index (`v * n + u`, CIR order). -/
def bfsRowIdx : CExpr :=
  .uadd (.umul (.var "v") (.var "n")) (.var "u")

/-- The fused entry seed: guarded visited mark plus guarded queue
    enqueue of the source (each miss is the `at()`-throw). -/
def bfsSeed : CStmt :=
  .seq (.if_ (.ult (.var "src") (.stdVecLen "vis"))
          (.vecSet "vis" (.var "src") (.lit (.i32 1)))
          .fail)
  (.seq (.if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "q"))
          (.vecSet "q" (.lit (.u64 (BitVec.ofNat 64 0)))
            (.i32ofU64 (.var "src")))
          .fail)
  (.seq (.let_ "head" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
  (.seq (.let_ "tail" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
  (.seq (.let_ "count" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
  (.seq (.let_ "v" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
  (.let_ "u" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0)))))))))

/-- One inner enqueue: guarded queue store plus the wrapping tail
    and count advances. -/
def bfsPush : CStmt :=
  .seq (.if_ (.ult (.var "tail") (.stdVecLen "q"))
          (.vecSet "q" (.var "tail") (.i32ofU64 (.var "u")))
          .fail)
  (.seq (.assign "tail" (.uadd (.var "tail")
            (.lit (.u64 (BitVec.ofNat 64 1)))))
    (.assign "count" (.uadd (.var "count")
      (.lit (.u64 (BitVec.ofNat 64 1))))))

/-- One row-scan iteration: the matrix guard, the two gates, the
    enqueue, and the `u` advance (which always runs). -/
def bfsInnerBody : CStmt :=
  .seq (.if_ (.ult bfsRowIdx (.stdVecLen "m"))
          (.if_ (.une (.stdVecAt "m" bfsRowIdx)
                  (.lit (.i32 (BitVec.ofNat 32 0))))
            (.if_ (.ult (.var "u") (.stdVecLen "vis"))
              (.if_ (.ueq (.stdVecAt "vis" (.var "u"))
                      (.lit (.i32 (BitVec.ofNat 32 0))))
                (.seq (.vecSet "vis" (.var "u")
                         (.lit (.i32 (BitVec.ofNat 32 1))))
                  bfsPush)
                .skip)
              .fail)
            .skip)
          .fail)
       (.assign "u" (.uadd (.var "u")
         (.lit (.u64 (BitVec.ofNat 64 1)))))

/-- The row scan: `u` runs `0..n`. -/
def bfsInner : CStmt :=
  .while_ (.ult (.var "u") (.var "n")) bfsInnerBody

/-- One drain iteration: guarded widening dequeue read, guarded
    visit record at the same head, head advance, `u` reset, then
    the row scan. -/
def bfsOuterBody : CStmt :=
  .seq (.if_ (.ult (.var "head") (.stdVecLen "q"))
          (.assign "v" (.u64ofI32 (.stdVecAt "q" (.var "head"))))
          .fail)
  (.seq (.if_ (.ult (.var "head") (.stdVecLen "order"))
          (.vecSet "order" (.var "head") (.i32ofU64 (.var "v")))
          .fail)
  (.seq (.assign "head" (.uadd (.var "head")
            (.lit (.u64 (BitVec.ofNat 64 1)))))
  (.seq (.assign "u" (.lit (.u64 (BitVec.ofNat 64 0))))
    bfsInner)))

/-- The queue drain: `head != tail`. -/
def bfsOuter : CStmt :=
  .while_ (.une (.var "head") (.var "tail"))
    bfsOuterBody

/-- Canonical CoreIR for `bfs_order`: the fused seed, the nested
    drain, and the count return. -/
def bfsOrderFunc : Func :=
  ⟨bfsName,
   [{ name := "m", ty := stdVecObjTy, role := .sharedBorrow },
    { name := "vis", ty := stdVecObjTy, role := .mutBorrow 0 },
    { name := "q", ty := stdVecObjTy, role := .mutBorrow 0 },
    { name := "order", ty := stdVecObjTy, role := .mutBorrow 0 },
    { name := "n", ty := .u 64, role := .owned },
    { name := "src", ty := .u 64, role := .owned }],
   .u 64,
   (.seq bfsSeed (.seq bfsOuter (.return_ (.var "count"))))⟩

/-- Drain environment: four word lists, dimension, source, and the
    five cursor words. -/
def mkBfsEnv (mL visL qL orderL : List (BitVec 32))
    (n src head tail count v u : BitVec 64) : Env :=
  [("u", .u64 u), ("v", .u64 v),
   ("count", .u64 count), ("tail", .u64 tail),
   ("head", .u64 head),
   ("m", .stdVecVal mL), ("vis", .stdVecVal visL),
   ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
   ("n", .u64 n), ("src", .u64 src)]

theorem mkBfsEnv_m (mL visL qL orderL : List (BitVec 32))
    (n src head tail count v u : BitVec 64) :
    envLookup (mkBfsEnv mL visL qL orderL n src head tail count v u) "m" =
      some (.stdVecVal mL) := by
  simp [mkBfsEnv, envLookup,
    show ("u" : String) ≠ "m" by decide,
    show ("v" : String) ≠ "m" by decide,
    show ("count" : String) ≠ "m" by decide,
    show ("tail" : String) ≠ "m" by decide,
    show ("head" : String) ≠ "m" by decide]

theorem mkBfsEnv_vis (mL visL qL orderL : List (BitVec 32))
    (n src head tail count v u : BitVec 64) :
    envLookup (mkBfsEnv mL visL qL orderL n src head tail count v u) "vis" =
      some (.stdVecVal visL) := by
  simp [mkBfsEnv, envLookup,
    show ("u" : String) ≠ "vis" by decide,
    show ("v" : String) ≠ "vis" by decide,
    show ("count" : String) ≠ "vis" by decide,
    show ("tail" : String) ≠ "vis" by decide,
    show ("head" : String) ≠ "vis" by decide,
    show ("m" : String) ≠ "vis" by decide]

theorem mkBfsEnv_q (mL visL qL orderL : List (BitVec 32))
    (n src head tail count v u : BitVec 64) :
    envLookup (mkBfsEnv mL visL qL orderL n src head tail count v u) "q" =
      some (.stdVecVal qL) := by
  simp [mkBfsEnv, envLookup,
    show ("u" : String) ≠ "q" by decide,
    show ("v" : String) ≠ "q" by decide,
    show ("count" : String) ≠ "q" by decide,
    show ("tail" : String) ≠ "q" by decide,
    show ("head" : String) ≠ "q" by decide,
    show ("m" : String) ≠ "q" by decide,
    show ("vis" : String) ≠ "q" by decide]

theorem mkBfsEnv_order (mL visL qL orderL : List (BitVec 32))
    (n src head tail count v u : BitVec 64) :
    envLookup (mkBfsEnv mL visL qL orderL n src head tail count v u) "order" =
      some (.stdVecVal orderL) := by
  simp [mkBfsEnv, envLookup,
    show ("u" : String) ≠ "order" by decide,
    show ("v" : String) ≠ "order" by decide,
    show ("count" : String) ≠ "order" by decide,
    show ("tail" : String) ≠ "order" by decide,
    show ("head" : String) ≠ "order" by decide,
    show ("m" : String) ≠ "order" by decide,
    show ("vis" : String) ≠ "order" by decide,
    show ("q" : String) ≠ "order" by decide]

theorem mkBfsEnv_n (mL visL qL orderL : List (BitVec 32))
    (n src head tail count v u : BitVec 64) :
    envLookup (mkBfsEnv mL visL qL orderL n src head tail count v u) "n" =
      some (.u64 n) := by
  simp [mkBfsEnv, envLookup,
    show ("u" : String) ≠ "n" by decide,
    show ("v" : String) ≠ "n" by decide,
    show ("count" : String) ≠ "n" by decide,
    show ("tail" : String) ≠ "n" by decide,
    show ("head" : String) ≠ "n" by decide,
    show ("m" : String) ≠ "n" by decide,
    show ("vis" : String) ≠ "n" by decide,
    show ("q" : String) ≠ "n" by decide,
    show ("order" : String) ≠ "n" by decide]

theorem mkBfsEnv_src (mL visL qL orderL : List (BitVec 32))
    (n src head tail count v u : BitVec 64) :
    envLookup (mkBfsEnv mL visL qL orderL n src head tail count v u) "src" =
      some (.u64 src) := by
  simp [mkBfsEnv, envLookup,
    show ("u" : String) ≠ "src" by decide,
    show ("v" : String) ≠ "src" by decide,
    show ("count" : String) ≠ "src" by decide,
    show ("tail" : String) ≠ "src" by decide,
    show ("head" : String) ≠ "src" by decide,
    show ("m" : String) ≠ "src" by decide,
    show ("vis" : String) ≠ "src" by decide,
    show ("q" : String) ≠ "src" by decide,
    show ("order" : String) ≠ "src" by decide,
    show ("n" : String) ≠ "src" by decide]

theorem mkBfsEnv_head (mL visL qL orderL : List (BitVec 32))
    (n src head tail count v u : BitVec 64) :
    envLookup (mkBfsEnv mL visL qL orderL n src head tail count v u) "head" =
      some (.u64 head) := by
  simp [mkBfsEnv, envLookup,
    show ("u" : String) ≠ "head" by decide,
    show ("v" : String) ≠ "head" by decide,
    show ("count" : String) ≠ "head" by decide,
    show ("tail" : String) ≠ "head" by decide]

theorem mkBfsEnv_tail (mL visL qL orderL : List (BitVec 32))
    (n src head tail count v u : BitVec 64) :
    envLookup (mkBfsEnv mL visL qL orderL n src head tail count v u) "tail" =
      some (.u64 tail) := by
  simp [mkBfsEnv, envLookup,
    show ("u" : String) ≠ "tail" by decide,
    show ("v" : String) ≠ "tail" by decide,
    show ("count" : String) ≠ "tail" by decide]

theorem mkBfsEnv_count (mL visL qL orderL : List (BitVec 32))
    (n src head tail count v u : BitVec 64) :
    envLookup (mkBfsEnv mL visL qL orderL n src head tail count v u) "count" =
      some (.u64 count) := by
  simp [mkBfsEnv, envLookup,
    show ("u" : String) ≠ "count" by decide,
    show ("v" : String) ≠ "count" by decide]

theorem mkBfsEnv_v (mL visL qL orderL : List (BitVec 32))
    (n src head tail count v u : BitVec 64) :
    envLookup (mkBfsEnv mL visL qL orderL n src head tail count v u) "v" =
      some (.u64 v) := by
  simp [mkBfsEnv, envLookup]

theorem mkBfsEnv_u (mL visL qL orderL : List (BitVec 32))
    (n src head tail count v u : BitVec 64) :
    envLookup (mkBfsEnv mL visL qL orderL n src head tail count v u) "u" =
      some (.u64 u) := by
  simp [mkBfsEnv, envLookup]

/-- Fuel-threaded row-scan forward: mirrors `bfsInner` iteration for
    iteration (same fuel, same guard order). Zero fuel exits cleanly
    on a spent bound and aborts loudly on a live one — the S3a fuel
    contract. -/
def bfsRowFwd (F : Nat) (mL visL qL : List (BitVec 32))
    (n v tail count u : BitVec 64) :
    Result (List (BitVec 32) × List (BitVec 32) × BitVec 64 × BitVec 64 ×
      BitVec 64) :=
  match F with
  | 0 =>
    if u.ult n then .error .AssertFail
    else .ok (visL, qL, tail, count, u)
  | F + 1 =>
    if u.ult n then
      match mL[(v * n + u).toNat]? with
      | none => .error .AssertFail
      | some g =>
        if g != (BitVec.ofNat 32 0) then
          match visL[u.toNat]? with
          | none => .error .AssertFail
          | some w =>
            if w == (BitVec.ofNat 32 0) then
              match qL[tail.toNat]? with
              | none => .error .AssertFail
              | some _ =>
                bfsRowFwd F mL (visL.set u.toNat 1)
                  (qL.set tail.toNat (BitVec.ofNat 32 u.toNat))
                  n v (tail + 1) (count + 1) (u + 1)
            else bfsRowFwd F mL visL qL n v tail count (u + 1)
        else bfsRowFwd F mL visL qL n v tail count (u + 1)
    else .ok (visL, qL, tail, count, u)

/-- Fuel-threaded drain forward: mirrors `bfsOuter` (same fuel;
    the row scan runs at predecessor fuel, exactly as the
    successor handler threads it). Each dequeue records the
    visit in `order[head]` before the head advance. -/
def bfsOuterFwd (F : Nat) (mL visL qL orderL : List (BitVec 32))
    (n head tail count v u : BitVec 64) :
    Result (List (BitVec 32) × List (BitVec 32) × List (BitVec 32) ×
      BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) :=
  match F with
  | 0 =>
    if head != tail then .error .AssertFail
    else .ok (visL, qL, orderL, head, tail, count, v, u)
  | F + 1 =>
    if head != tail then
      match qL[head.toNat]? with
      | none => .error .AssertFail
      | some w =>
        match orderL[head.toNat]? with
        | none => .error .AssertFail
        | some _ =>
          match bfsRowFwd F mL visL qL n (w.signExtend 64) tail count 0 with
          | .error e => .error e
          | .ok (vis', q', tail', count', u') =>
            bfsOuterFwd F mL vis' q' (orderL.set head.toNat w)
              n (head + 1) tail' count' (w.signExtend 64) u'
    else .ok (visL, qL, orderL, head, tail, count, v, u)

/-- Seed mirror: the two guarded stores (each miss is loud). -/
def bfsSeedFwd (visL qL : List (BitVec 32)) (src : BitVec 64) :
    Result (List (BitVec 32) × List (BitVec 32)) :=
  match visL[src.toNat]? with
  | none => .error .AssertFail
  | some _ =>
    match qL[(BitVec.ofNat 64 0).toNat]? with
    | none => .error .AssertFail
    | some _ =>
      .ok (visL.set src.toNat 1,
        qL.set 0 (BitVec.ofNat 32 src.toNat))

/-- Entry mirror: seed, then the drain; the count is the return. -/
def bfsFwd (F : Nat) (mL visL qL orderL : List (BitVec 32))
    (n src : BitVec 64) : Result Value :=
  match bfsSeedFwd visL qL src with
  | .error e => .error e
  | .ok (vis1, q1) =>
    match bfsOuterFwd F mL vis1 q1 orderL n 0 1 1 0 0 with
    | .error e => .error e
    | .ok (_, _, _, _, _, count, _, _) => .ok (.u64 count)

/-- The row index evaluates to the wrapped `u64` (G2 pattern). -/
theorem bfsRowIdx_eval (mL visL qL orderL : List (BitVec 32))
    (n src head tail count v u : BitVec 64) :
    evalExpr bfsRowIdx (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.u64 (v * n + u)) := by
  have hn := mkBfsEnv_n mL visL qL orderL n src head tail count v u
  have hv := mkBfsEnv_v mL visL qL orderL n src head tail count v u
  have hu := mkBfsEnv_u mL visL qL orderL n src head tail count v u
  have hvv : evalExpr (.var "v")
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.u64 v) :=
    evalExpr_var_hit _ _ _ hv
  have hvn : evalExpr (.var "n")
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.u64 n) :=
    evalExpr_var_hit _ _ _ hn
  have hvu : evalExpr (.var "u")
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.u64 u) :=
    evalExpr_var_hit _ _ _ hu
  have hmul : evalExpr (.umul (.var "v") (.var "n"))
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.u64 (v * n)) :=
    evalExpr_umul_u64 _ _ _ _ _ hvv hvn
  have := evalExpr_uadd_u64 _ _ _ _ _ hmul hvu
  simpa [bfsRowIdx] using this

/-- Seed visited guard: `src < vis.length`. -/
theorem bfsSeedVisGuard_eval (mL visL qL orderL : List (BitVec 32))
    (n src head tail count v u : BitVec 64)
    (hlen64 : visL.length < 2 ^ 64) :
    evalExpr (.ult (.var "src") (.stdVecLen "vis"))
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.b (src.ult (BitVec.ofNat 64 visL.length))) := by
  have hsrc : evalExpr (.var "src")
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.u64 src) :=
    evalExpr_var_hit _ _ _
      (mkBfsEnv_src mL visL qL orderL n src head tail count v u)
  have hlen : evalExpr (.stdVecLen "vis")
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.u64 (BitVec.ofNat 64 visL.length)) :=
    evalExpr_stdVecLen_some "vis" _ visL
      (mkBfsEnv_vis mL visL qL orderL n src head tail count v u)
  exact evalExpr_ult_u64 _ _ _ _ _ hsrc hlen

/-- Seed queue guard: `0 < q.length`. -/
theorem bfsSeedQGuard_eval (mL visL qL orderL : List (BitVec 32))
    (n src head tail count v u : BitVec 64) :
    evalExpr (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "q"))
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.b ((BitVec.ofNat 64 0).ult (BitVec.ofNat 64 qL.length))) := by
  have hlen : evalExpr (.stdVecLen "q")
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.u64 (BitVec.ofNat 64 qL.length)) :=
    evalExpr_stdVecLen_some "q" _ qL
      (mkBfsEnv_q mL visL qL orderL n src head tail count v u)
  have hlit : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  exact evalExpr_ult_u64 _ _ _ _ _ hlit hlen

/-- Bridge: a true `ult` guard gives an in-bounds `getElem?`
    (slice-local copy of the G5a bridge — each slice file stays
    self-contained, the push-lemma precedent). -/
theorem bfsUltGuard_inBounds {x : BitVec 64} {l : List (BitVec 32)}
    (hlen : l.length < 2 ^ 64)
    (h : x.ult (BitVec.ofNat 64 l.length) = true) :
    x.toNat < l.length := by
  have h1 : decide (x.toNat < (BitVec.ofNat 64 l.length).toNat) = true := by
    rw [← BitVec.ult_eq_decide]; exact h
  have h2 := of_decide_eq_true h1
  rw [ofNat64_toNat _ hlen] at h2
  exact h2

/-- One inner enqueue at any fuel: guarded store plus the two
    wrapping advances (miss aborts loudly). -/
theorem bfsPush_ok (F : Nat) (mL visL qL orderL : List (BitVec 32))
    (n src head tail count v u : BitVec 64)
    (hqllen : qL.length < 2 ^ 64)
    (hguard : tail.ult (BitVec.ofNat 64 qL.length) = true) :
    evalStmtFuel F bfsPush
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (mkBfsEnv mL visL
        (qL.set tail.toNat (BitVec.ofNat 32 u.toNat)) orderL
        n src head (tail + 1) (count + 1) v u, .fellThrough) := by
  have hbody : bfsPush =
      .seq (.if_ (.ult (.var "tail") (.stdVecLen "q"))
              (.vecSet "q" (.var "tail") (.i32ofU64 (.var "u")))
              .fail)
      (.seq (.assign "tail" (.uadd (.var "tail")
                (.lit (.u64 (BitVec.ofNat 64 1)))))
        (.assign "count" (.uadd (.var "count")
          (.lit (.u64 (BitVec.ofNat 64 1)))))) := rfl
  have hq := mkBfsEnv_q mL visL qL orderL n src head tail count v u
  have htail : evalExpr (.var "tail")
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.u64 tail) :=
    evalExpr_var_hit _ _ _
      (mkBfsEnv_tail mL visL qL orderL n src head tail count v u)
  have hlen : evalExpr (.stdVecLen "q")
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.u64 (BitVec.ofNat 64 qL.length)) :=
    evalExpr_stdVecLen_some "q" _ qL hq
  have hg := evalExpr_ult_u64 _ _ _ _ _ htail hlen
  rw [hguard] at hg
  have hc : evalExpr (.ult (.var "tail") (.stdVecLen "q"))
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.b true) := hg
  have hlt : tail.toNat < qL.length :=
    bfsUltGuard_inBounds hqllen hguard
  have hne : qL[tail.toNat]? ≠ none := by
    rw [ne_eq, List.getElem?_eq_none_iff]
    omega
  obtain ⟨w, hget'⟩ := Option.ne_none_iff_exists.mp hne
  have hget : qL[tail.toNat]? = some w := hget'.symm
  have huvar : evalExpr (.var "u")
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.u64 u) :=
    evalExpr_var_hit _ _ _
      (mkBfsEnv_u mL visL qL orderL n src head tail count v u)
  have hval : evalExpr (.i32ofU64 (.var "u"))
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.i32 (BitVec.ofNat 32 u.toNat)) :=
    evalExpr_i32ofU64_ok _ _ _ huvar
  have hu : envUpdate
      (mkBfsEnv mL visL qL orderL n src head tail count v u) "q"
      (.stdVecVal (qL.set tail.toNat (BitVec.ofNat 32 u.toNat))) =
      some (mkBfsEnv mL visL
        (qL.set tail.toNat (BitVec.ofNat 32 u.toNat)) orderL
        n src head tail count v u) := by
    simp [mkBfsEnv, envUpdate,
      show ("u" : String) ≠ "q" by decide,
      show ("v" : String) ≠ "q" by decide,
      show ("count" : String) ≠ "q" by decide,
      show ("tail" : String) ≠ "q" by decide,
      show ("head" : String) ≠ "q" by decide,
      show ("m" : String) ≠ "q" by decide,
      show ("vis" : String) ≠ "q" by decide]
  have hset := evalStmtFuel_vecSet F "q" (.var "tail")
    (.i32ofU64 (.var "u"))
    (mkBfsEnv mL visL qL orderL n src head tail count v u) tail
    (BitVec.ofNat 32 u.toNat) qL w _ htail hval hq hget hu
  have hone : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      (mkBfsEnv mL visL
        (qL.set tail.toNat (BitVec.ofNat 32 u.toNat)) orderL
        n src head tail count v u) =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have htail2 : evalExpr (.var "tail")
      (mkBfsEnv mL visL
        (qL.set tail.toNat (BitVec.ofNat 32 u.toNat)) orderL
        n src head tail count v u) = .ok (.u64 tail) :=
    evalExpr_var_hit _ _ _ (by
      simp [envLookup, mkBfsEnv,
        show ("tail" : String) ≠ "m" by decide,
        show ("tail" : String) ≠ "vis" by decide,
        show ("tail" : String) ≠ "q" by decide,
        show ("tail" : String) ≠ "order" by decide])
  have hu2 : envUpdate
      (mkBfsEnv mL visL
        (qL.set tail.toNat (BitVec.ofNat 32 u.toNat)) orderL
        n src head tail count v u) "tail" (.u64 (tail + 1)) =
      some (mkBfsEnv mL visL
        (qL.set tail.toNat (BitVec.ofNat 32 u.toNat)) orderL
        n src head (tail + 1) count v u) := by
    simp [mkBfsEnv, envUpdate,
      show ("u" : String) ≠ "tail" by decide,
      show ("v" : String) ≠ "tail" by decide,
      show ("count" : String) ≠ "tail" by decide]
  have hadd1 := evalExpr_uadd_u64 _ _ _ _ _ htail2 hone
  have hassign1 := evalStmtFuel_assign F "tail"
    (.uadd (.var "tail") (.lit (.u64 (BitVec.ofNat 64 1))))
    (mkBfsEnv mL visL
      (qL.set tail.toNat (BitVec.ofNat 32 u.toNat)) orderL
      n src head tail count v u) _ _ hadd1 hu2
  have hcount : evalExpr (.var "count")
      (mkBfsEnv mL visL
        (qL.set tail.toNat (BitVec.ofNat 32 u.toNat)) orderL
        n src head (tail + 1) count v u) = .ok (.u64 count) :=
    evalExpr_var_hit _ _ _ (by
      simp [envLookup, mkBfsEnv,
        show ("count" : String) ≠ "m" by decide,
        show ("count" : String) ≠ "vis" by decide,
        show ("count" : String) ≠ "q" by decide,
        show ("count" : String) ≠ "order" by decide,
        show ("count" : String) ≠ "n" by decide,
        show ("count" : String) ≠ "src" by decide,
        show ("count" : String) ≠ "head" by decide,
        show ("count" : String) ≠ "tail" by decide])
  have hone2 : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      (mkBfsEnv mL visL
        (qL.set tail.toNat (BitVec.ofNat 32 u.toNat)) orderL
        n src head (tail + 1) count v u) =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have hu3 : envUpdate
      (mkBfsEnv mL visL
        (qL.set tail.toNat (BitVec.ofNat 32 u.toNat)) orderL
        n src head (tail + 1) count v u) "count" (.u64 (count + 1)) =
      some (mkBfsEnv mL visL
        (qL.set tail.toNat (BitVec.ofNat 32 u.toNat)) orderL
        n src head (tail + 1) (count + 1) v u) := by
    simp [mkBfsEnv, envUpdate,
      show ("u" : String) ≠ "count" by decide]
  have hadd2 := evalExpr_uadd_u64 _ _ _ _ _ hcount hone2
  have hassign2 := evalStmtFuel_assign F "count"
    (.uadd (.var "count") (.lit (.u64 (BitVec.ofNat 64 1))))
    (mkBfsEnv mL visL
      (qL.set tail.toNat (BitVec.ofNat 32 u.toNat)) orderL
      n src head (tail + 1) count v u) _ _ hadd2 hu3
  have hseq2 := evalStmtFuel_seq_fallthrough F
    (.assign "tail" (.uadd (.var "tail")
      (.lit (.u64 (BitVec.ofNat 64 1)))))
    (.assign "count" (.uadd (.var "count")
      (.lit (.u64 (BitVec.ofNat 64 1)))))
    _ _ hassign1
  have hif := (evalStmtFuel_if_true F _
    (.vecSet "q" (.var "tail") (.i32ofU64 (.var "u"))) .fail _ hc).trans hset
  have houter := evalStmtFuel_seq_fallthrough F _
    (.seq (.assign "tail" (.uadd (.var "tail")
      (.lit (.u64 (BitVec.ofNat 64 1)))))
      (.assign "count" (.uadd (.var "count")
        (.lit (.u64 (BitVec.ofNat 64 1)))))) _ _ hif
  rw [hbody]
  exact houter.trans (hseq2.trans hassign2)

/-- An enqueue past the reserved length aborts loudly (any fuel). -/
theorem bfsPush_miss (F : Nat) (mL visL qL orderL : List (BitVec 32))
    (n src head tail count v u : BitVec 64)
    (hguard : tail.ult (BitVec.ofNat 64 qL.length) = false) :
    evalStmtFuel F bfsPush
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .error .AssertFail := by
  have hbody : bfsPush =
      .seq (.if_ (.ult (.var "tail") (.stdVecLen "q"))
              (.vecSet "q" (.var "tail") (.i32ofU64 (.var "u")))
              .fail)
      (.seq (.assign "tail" (.uadd (.var "tail")
                (.lit (.u64 (BitVec.ofNat 64 1)))))
        (.assign "count" (.uadd (.var "count")
          (.lit (.u64 (BitVec.ofNat 64 1)))))) := rfl
  have hq := mkBfsEnv_q mL visL qL orderL n src head tail count v u
  have htail : evalExpr (.var "tail")
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.u64 tail) :=
    evalExpr_var_hit _ _ _
      (mkBfsEnv_tail mL visL qL orderL n src head tail count v u)
  have hlen : evalExpr (.stdVecLen "q")
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.u64 (BitVec.ofNat 64 qL.length)) :=
    evalExpr_stdVecLen_some "q" _ qL hq
  have hg : evalExpr (.ult (.var "tail") (.stdVecLen "q"))
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.b false) := by
    have h := evalExpr_ult_u64 _ _ _ _ _ htail hlen
    rw [hguard] at h
    exact h
  rw [hbody]
  exact evalStmtFuel_seq_err F _
    (.seq (.assign "tail" (.uadd (.var "tail")
      (.lit (.u64 (BitVec.ofNat 64 1)))))
      (.assign "count" (.uadd (.var "count")
        (.lit (.u64 (BitVec.ofNat 64 1)))))) _ _
    ((evalStmtFuel_if_false F _ _ _ _ hg).trans
      (evalStmtFuel_fail F _))

/-- Bridge: a `some` read gives a strict bound (slice-local copy
    of the G5a bridge). -/
theorem bfsGetElem_some_lt {α : Type} {l : List α} {i : Nat} {x : α}
    (h : l[i]? = some x) : i < l.length := by
  have hne : l[i]? ≠ none := by simp [h]
  rw [ne_eq, List.getElem?_eq_none_iff] at hne
  omega

/-- One row-scan iteration at any fuel: the matrix guard, the two
    gates, the enqueue, and the `u` advance — mirroring the
    forward's branch order exactly. -/
theorem bfsInnerBody_eval (F : Nat) (mL visL qL orderL : List (BitVec 32))
    (n src head tail count v u : BitVec 64)
    (hmen : mL.length < 2 ^ 64) (hvislen : visL.length < 2 ^ 64)
    (hqllen : qL.length < 2 ^ 64) :
    evalStmtFuel F bfsInnerBody
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      match mL[(v * n + u).toNat]? with
      | none => .error .AssertFail
      | some g =>
        if g != (BitVec.ofNat 32 0) then
          match visL[u.toNat]? with
          | none => .error .AssertFail
          | some w =>
            if w == (BitVec.ofNat 32 0) then
              match qL[tail.toNat]? with
              | none => .error .AssertFail
              | some _ => .ok (mkBfsEnv mL (visL.set u.toNat 1)
                  (qL.set tail.toNat (BitVec.ofNat 32 u.toNat)) orderL
                  n src head (tail + 1) (count + 1) v (u + 1),
                  .fellThrough)
            else .ok (mkBfsEnv mL visL qL orderL n src head tail count
              v (u + 1), .fellThrough)
        else .ok (mkBfsEnv mL visL qL orderL n src head tail count
          v (u + 1), .fellThrough) := by
  have hbody : bfsInnerBody =
      .seq (.if_ (.ult bfsRowIdx (.stdVecLen "m"))
              (.if_ (.une (.stdVecAt "m" bfsRowIdx)
                      (.lit (.i32 (BitVec.ofNat 32 0))))
                (.if_ (.ult (.var "u") (.stdVecLen "vis"))
                  (.if_ (.ueq (.stdVecAt "vis" (.var "u"))
                          (.lit (.i32 (BitVec.ofNat 32 0))))
                    (.seq (.vecSet "vis" (.var "u")
                             (.lit (.i32 (BitVec.ofNat 32 1))))
                      bfsPush)
                    .skip)
                  .fail)
                .skip)
              .fail)
           (.assign "u" (.uadd (.var "u")
             (.lit (.u64 (BitVec.ofNat 64 1))))) := rfl
  have hidx := bfsRowIdx_eval mL visL qL orderL
    n src head tail count v u
  have hm := mkBfsEnv_m mL visL qL orderL n src head tail count v u
  have hmlen : evalExpr (.stdVecLen "m")
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.u64 (BitVec.ofNat 64 mL.length)) :=
    evalExpr_stdVecLen_some "m" _ mL hm
  have hmguard := evalExpr_ult_u64 _ _ _ _ _ hidx hmlen
  -- The `u` advance shared by every fall-through leg.
  have hadv : ∀ (vis' qL' : List (BitVec 32)) (tail' count' : BitVec 64),
      evalStmtFuel F (.assign "u" (.uadd (.var "u")
        (.lit (.u64 (BitVec.ofNat 64 1)))))
        (mkBfsEnv mL vis' qL' orderL n src head tail' count' v u) =
        .ok (mkBfsEnv mL vis' qL' orderL n src head tail' count'
          v (u + 1), .fellThrough) := by
    intro vis' qL' tail' count'
    have hvar : evalExpr (.var "u")
        (mkBfsEnv mL vis' qL' orderL n src head tail' count' v u) =
        .ok (.u64 u) :=
      evalExpr_var_hit _ _ _ (by
        simp [envLookup, mkBfsEnv,
          show ("u" : String) ≠ "m" by decide,
          show ("u" : String) ≠ "vis" by decide,
          show ("u" : String) ≠ "q" by decide,
          show ("u" : String) ≠ "order" by decide,
          show ("u" : String) ≠ "n" by decide,
          show ("u" : String) ≠ "src" by decide,
          show ("u" : String) ≠ "head" by decide,
          show ("u" : String) ≠ "tail" by decide,
          show ("u" : String) ≠ "count" by decide,
          show ("u" : String) ≠ "v" by decide])
    have hone : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        (mkBfsEnv mL vis' qL' orderL n src head tail' count' v u) =
        .ok (.u64 (BitVec.ofNat 64 1)) := by
      simp [evalExpr, litVal]
    have hadd := evalExpr_uadd_u64 _ _ _ _ _ hvar hone
    have hu : envUpdate
        (mkBfsEnv mL vis' qL' orderL n src head tail' count' v u) "u"
        (.u64 (u + 1)) =
        some (mkBfsEnv mL vis' qL' orderL n src head tail' count'
          v (u + 1)) := by
      simp [mkBfsEnv, envUpdate]
    exact evalStmtFuel_assign F "u" _ _ _ _ hadd hu
  match hgetm : mL[(v * n + u).toNat]? with
  | none =>
    have hnot : ¬ (v * n + u).toNat < mL.length := by
      intro hcon
      have hne : mL[(v * n + u).toNat]? ≠ none := by
        rw [ne_eq, List.getElem?_eq_none_iff]
        omega
      exact hne hgetm
    have hult : (v * n + u).ult (BitVec.ofNat 64 mL.length) = false := by
      have h1 : ¬ (v * n + u).toNat <
          (BitVec.ofNat 64 mL.length).toNat := by
        rw [ofNat64_toNat _ hmen]
        exact hnot
      have h2 : decide ((v * n + u).toNat <
          (BitVec.ofNat 64 mL.length).toNat) = false :=
        decide_eq_false h1
      rwa [← BitVec.ult_eq_decide] at h2
    have hc : evalExpr (.ult bfsRowIdx (.stdVecLen "m"))
        (mkBfsEnv mL visL qL orderL n src head tail count v u) =
        .ok (.b false) := by
      have h1 := evalExpr_ult_u64 _ _ _ _ _ hidx hmlen
      rw [hult] at h1
      exact h1
    rw [hbody]
    simp only [hgetm]
    exact evalStmtFuel_seq_err F _
      (.assign "u" (.uadd (.var "u")
        (.lit (.u64 (BitVec.ofNat 64 1))))) _ _
      ((evalStmtFuel_if_false F _ _ _ _ hc).trans
        (evalStmtFuel_fail F _))
  | some g =>
    have hlt : (v * n + u).toNat < mL.length :=
      bfsGetElem_some_lt hgetm
    have hult : (v * n + u).ult (BitVec.ofNat 64 mL.length) = true := by
      have h1 : (v * n + u).toNat <
          (BitVec.ofNat 64 mL.length).toNat := by
        rw [ofNat64_toNat _ hmen]
        exact hlt
      have h2 : decide ((v * n + u).toNat <
          (BitVec.ofNat 64 mL.length).toNat) = true :=
        decide_eq_true h1
      rwa [← BitVec.ult_eq_decide] at h2
    have hc : evalExpr (.ult bfsRowIdx (.stdVecLen "m"))
        (mkBfsEnv mL visL qL orderL n src head tail count v u) =
        .ok (.b true) := by
      have h1 := evalExpr_ult_u64 _ _ _ _ _ hidx hmlen
      rw [hult] at h1
      exact h1
    have hread : evalExpr (.stdVecAt "m" bfsRowIdx)
        (mkBfsEnv mL visL qL orderL n src head tail count v u) =
        .ok (.i32 g) := by
      have hi := bfsRowIdx_eval mL visL qL orderL
        n src head tail count v u
      exact evalExpr_stdVecAt_some "m" _ _ _ _ _ hm hi hgetm
    have hzero : evalExpr (.lit (.i32 (BitVec.ofNat 32 0)))
        (mkBfsEnv mL visL qL orderL n src head tail count v u) =
        .ok (.i32 (BitVec.ofNat 32 0)) := by
      simp [evalExpr, litVal]
    have hgateM := evalExpr_une_i32 _ _ _ _ _ hread hzero
    by_cases hgm : g != (BitVec.ofNat 32 0)
    · have hcm : evalExpr (.une (.stdVecAt "m" bfsRowIdx)
            (.lit (.i32 (BitVec.ofNat 32 0))))
            (mkBfsEnv mL visL qL orderL n src head tail count v u) =
            .ok (.b true) := by
        simp only [hgm] at hgateM
        exact hgateM
      have hvis := mkBfsEnv_vis mL visL qL orderL
        n src head tail count v u
      have huvar : evalExpr (.var "u")
          (mkBfsEnv mL visL qL orderL n src head tail count v u) =
          .ok (.u64 u) :=
        evalExpr_var_hit _ _ _
          (mkBfsEnv_u mL visL qL orderL n src head tail count v u)
      have hvlen : evalExpr (.stdVecLen "vis")
          (mkBfsEnv mL visL qL orderL n src head tail count v u) =
          .ok (.u64 (BitVec.ofNat 64 visL.length)) :=
        evalExpr_stdVecLen_some "vis" _ visL hvis
      have hvguard := evalExpr_ult_u64 _ _ _ _ _ huvar hvlen
      match hgetv : visL[u.toNat]? with
      | none =>
        have hnot : ¬ u.toNat < visL.length := by
          intro hcon
          have hne : visL[u.toNat]? ≠ none := by
            rw [ne_eq, List.getElem?_eq_none_iff]
            omega
          exact hne hgetv
        have hult : u.ult (BitVec.ofNat 64 visL.length) = false := by
          have h1 : ¬ u.toNat <
              (BitVec.ofNat 64 visL.length).toNat := by
            rw [ofNat64_toNat _ hvislen]
            exact hnot
          have h2 : decide (u.toNat <
              (BitVec.ofNat 64 visL.length).toNat) = false :=
            decide_eq_false h1
          rwa [← BitVec.ult_eq_decide] at h2
        have hcv : evalExpr (.ult (.var "u") (.stdVecLen "vis"))
            (mkBfsEnv mL visL qL orderL n src head tail count v u) =
            .ok (.b false) := by
          rw [hult] at hvguard
          exact hvguard
        rw [hbody]
        simp only [hgetm, hgm, hgetv]
        exact evalStmtFuel_seq_err F _
          (.assign "u" (.uadd (.var "u")
            (.lit (.u64 (BitVec.ofNat 64 1))))) _ _
          (((evalStmtFuel_if_true F _ _ _ _ hc).trans
            (evalStmtFuel_if_true F _ _ _ _ hcm)).trans
            ((evalStmtFuel_if_false F _ _ _ _ hcv).trans
              (evalStmtFuel_fail F _)))
      | some w =>
        have hltv : u.toNat < visL.length :=
          bfsGetElem_some_lt hgetv
        have hult : u.ult (BitVec.ofNat 64 visL.length) = true := by
          have h1 : u.toNat <
              (BitVec.ofNat 64 visL.length).toNat := by
            rw [ofNat64_toNat _ hvislen]
            exact hltv
          have h2 : decide (u.toNat <
              (BitVec.ofNat 64 visL.length).toNat) = true :=
            decide_eq_true h1
          rwa [← BitVec.ult_eq_decide] at h2
        have hcv : evalExpr (.ult (.var "u") (.stdVecLen "vis"))
            (mkBfsEnv mL visL qL orderL n src head tail count v u) =
            .ok (.b true) := by
          rw [hult] at hvguard
          exact hvguard
        have hreadv : evalExpr (.stdVecAt "vis" (.var "u"))
            (mkBfsEnv mL visL qL orderL n src head tail count v u) =
            .ok (.i32 w) :=
          evalExpr_stdVecAt_some "vis" _ _ _ _ _ hvis huvar hgetv
        have hgateV := evalExpr_ueq_i32 _ _ _ _ _ hreadv hzero
        by_cases hgv : w == (BitVec.ofNat 32 0)
        · have hcv2 : evalExpr
              (.ueq (.stdVecAt "vis" (.var "u"))
                (.lit (.i32 (BitVec.ofNat 32 0))))
                (mkBfsEnv mL visL qL orderL n src head tail count v u) =
                .ok (.b true) := by
            simp only [hgv] at hgateV
            exact hgateV
          -- enqueue leg: vis-store, guarded enqueue, shared advance.
          match hgetq : qL[tail.toNat]? with
          | none =>
            have hnot : ¬ tail.toNat < qL.length := by
              intro hcon
              have hne : qL[tail.toNat]? ≠ none := by
                rw [ne_eq, List.getElem?_eq_none_iff]
                omega
              exact hne hgetq
            have hqgF : tail.ult (BitVec.ofNat 64 qL.length) = false := by
              have h1 : ¬ tail.toNat <
                  (BitVec.ofNat 64 qL.length).toNat := by
                rw [ofNat64_toNat _ hqllen]
                exact hnot
              have h2 : decide (tail.toNat <
                  (BitVec.ofNat 64 qL.length).toNat) = false :=
                decide_eq_false h1
              rwa [← BitVec.ult_eq_decide] at h2
            have hvis : envLookup
                (mkBfsEnv mL visL qL orderL n src head tail count v u)
                "vis" = some (.stdVecVal visL) :=
              mkBfsEnv_vis mL visL qL orderL n src head tail count v u
            have huvar : evalExpr (.var "u")
                (mkBfsEnv mL visL qL orderL n src head tail count v u) =
                .ok (.u64 u) :=
              evalExpr_var_hit _ _ _
                (mkBfsEnv_u mL visL qL orderL n src head tail count v u)
            have hx1 : evalExpr (.lit (.i32 (1 : BitVec 32)))
                (mkBfsEnv mL visL qL orderL n src head tail count v u) =
                .ok (.i32 1) := by
              simp [evalExpr, litVal]
            have hu : envUpdate
                (mkBfsEnv mL visL qL orderL n src head tail count v u)
                "vis" (.stdVecVal (visL.set u.toNat 1)) =
                some (mkBfsEnv mL (visL.set u.toNat 1) qL orderL
                  n src head tail count v u) := by
              simp [mkBfsEnv, envUpdate,
                show ("u" : String) ≠ "vis" by decide,
                show ("v" : String) ≠ "vis" by decide,
                show ("count" : String) ≠ "vis" by decide,
                show ("tail" : String) ≠ "vis" by decide,
                show ("head" : String) ≠ "vis" by decide,
                show ("m" : String) ≠ "vis" by decide]
            have hsetv := evalStmtFuel_vecSet F "vis" (.var "u")
              (.lit (.i32 (1 : BitVec 32)))
              (mkBfsEnv mL visL qL orderL n src head tail count v u)
              u 1 visL w _ huvar hx1 hvis hgetv hu
            have hpushF := bfsPush_miss F mL (visL.set u.toNat 1) qL
              orderL n src head tail count v u hqgF
            have hdone := (evalStmtFuel_seq_fallthrough F _ bfsPush _ _
              hsetv).trans hpushF
            rw [hbody]
            simp only [hgetm, hgm, hgetv, hgv, hgetq]
            exact evalStmtFuel_seq_err F _
              (.assign "u" (.uadd (.var "u")
                (.lit (.u64 (BitVec.ofNat 64 1))))) _ _
              (((((evalStmtFuel_if_true F _ _ _ _ hc).trans
                (evalStmtFuel_if_true F _ _ _ _ hcm)).trans
                (evalStmtFuel_if_true F _ _ _ _ hcv)).trans
                (evalStmtFuel_if_true F _ _ _ _ hcv2)).trans (hdone))
          | some _ =>
              have hvis : envLookup
                (mkBfsEnv mL visL qL orderL n src head tail count v u)
                "vis" = some (.stdVecVal visL) :=
              mkBfsEnv_vis mL visL qL orderL n src head tail count v u
              have huvar : evalExpr (.var "u")
                  (mkBfsEnv mL visL qL orderL n src head tail count v u) =
                  .ok (.u64 u) :=
                evalExpr_var_hit _ _ _
                  (mkBfsEnv_u mL visL qL orderL
                    n src head tail count v u)
              have hx1 : evalExpr (.lit (.i32 (1 : BitVec 32)))
                  (mkBfsEnv mL visL qL orderL n src head tail count v u) =
                  .ok (.i32 1) := by
                simp [evalExpr, litVal]
              have hu : envUpdate
                  (mkBfsEnv mL visL qL orderL n src head tail count v u)
                  "vis" (.stdVecVal (visL.set u.toNat 1)) =
                  some (mkBfsEnv mL (visL.set u.toNat 1) qL orderL
                    n src head tail count v u) := by
                simp [mkBfsEnv, envUpdate,
                  show ("u" : String) ≠ "vis" by decide,
                  show ("v" : String) ≠ "vis" by decide,
                  show ("count" : String) ≠ "vis" by decide,
                  show ("tail" : String) ≠ "vis" by decide,
                  show ("head" : String) ≠ "vis" by decide,
                  show ("m" : String) ≠ "vis" by decide]
              have hsetv := evalStmtFuel_vecSet F "vis" (.var "u")
                (.lit (.i32 (1 : BitVec 32)))
                (mkBfsEnv mL visL qL orderL n src head tail count v u)
                u 1 visL w _ huvar hx1 hvis hgetv hu
              have hqg : tail.ult (BitVec.ofNat 64 qL.length) = true := by
                have hltq : tail.toNat < qL.length :=
                  bfsGetElem_some_lt hgetq
                have h2 : decide (tail.toNat <
                    (BitVec.ofNat 64 qL.length).toNat) = true := by
                  rw [ofNat64_toNat _ hqllen]
                  exact decide_eq_true hltq
                rwa [← BitVec.ult_eq_decide] at h2
              have hpush := bfsPush_ok F mL (visL.set u.toNat 1) qL
                orderL n src head tail count v u hqllen hqg
              have hdone := (evalStmtFuel_seq_fallthrough F _ bfsPush _ _
                hsetv).trans hpush
              have hadv1 := hadv (visL.set u.toNat 1)
                (qL.set tail.toNat (BitVec.ofNat 32 u.toNat))
                (tail + 1) (count + 1)
              rw [hbody]
              simp only [hgetm, hgm, hgetv, hgv, hgetq]
              exact ((evalStmtFuel_seq_fallthrough F _
                  (.assign "u" (.uadd (.var "u")
                    (.lit (.u64 (BitVec.ofNat 64 1))))) _ _
                  (((((evalStmtFuel_if_true F _ _ _ _ hc).trans
                    (evalStmtFuel_if_true F _ _ _ _ hcm)).trans
                    (evalStmtFuel_if_true F _ _ _ _ hcv)).trans
                    (evalStmtFuel_if_true F _ _ _ _ hcv2)).trans
                    (hdone))).trans hadv1)
        · -- visited leg: skip the enqueue, still advance `u`.
          have hfalse : (w == (BitVec.ofNat 32 0)) = false :=
            Bool.eq_false_of_ne_true hgv
          have hcv2 : evalExpr (.ueq (.stdVecAt "vis" (.var "u"))
                  (.lit (.i32 (BitVec.ofNat 32 0))))
                  (mkBfsEnv mL visL qL orderL n src head tail count v u) =
                  .ok (.b false) := by
            rw [hfalse] at hgateV
            exact hgateV
          have hskip : evalStmtFuel F .skip
              (mkBfsEnv mL visL qL orderL n src head tail count v u) =
              .ok (mkBfsEnv mL visL qL orderL n src head tail count v u,
                .fellThrough) := by
            cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith]
          have hadv1 := hadv visL qL tail count
          rw [hbody]
          simp only [hgetm, hgm, hgetv, hfalse]
          exact ((evalStmtFuel_seq_fallthrough F _
              (.assign "u" (.uadd (.var "u")
                (.lit (.u64 (BitVec.ofNat 64 1))))) _ _
              (((((evalStmtFuel_if_true F _ _ _ _ hc).trans
                (evalStmtFuel_if_true F _ _ _ _ hcm)).trans
                (evalStmtFuel_if_true F _ _ _ _ hcv)).trans
                (evalStmtFuel_if_false F _ _ _ _ hcv2)).trans
                (hskip))).trans hadv1)
    · -- no-edge leg: skip the visit test, still advance `u`.
      have hfalseM : (g != (BitVec.ofNat 32 0)) = false :=
        Bool.eq_false_of_ne_true hgm
      have hcm : evalExpr (.une (.stdVecAt "m" bfsRowIdx)
              (.lit (.i32 (BitVec.ofNat 32 0))))
              (mkBfsEnv mL visL qL orderL n src head tail count v u) =
              .ok (.b false) := by
        rw [hfalseM] at hgateM
        exact hgateM
      have hskip : evalStmtFuel F .skip
          (mkBfsEnv mL visL qL orderL n src head tail count v u) =
          .ok (mkBfsEnv mL visL qL orderL n src head tail count v u,
            .fellThrough) := by
        cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith]
      have hadv1 := hadv visL qL tail count
      rw [hbody]
      simp only [hgetm, hfalseM]
      exact ((evalStmtFuel_seq_fallthrough F _
          (.assign "u" (.uadd (.var "u")
            (.lit (.u64 (BitVec.ofNat 64 1))))) _ _
          (((evalStmtFuel_if_true F _ _ _ _ hc).trans
            (evalStmtFuel_if_false F _ _ _ _ hcm)).trans
            (hskip))).trans hadv1)

/-- Row scan at fuel `F`: the evaluator agrees with the forward on
    every `.ok` run (fuel induction; the error legs contradict `hfwd`). -/
theorem bfsRow_ok (F : Nat) (mL visL qL orderL : List (BitVec 32))
    (n src head tail count v u : BitVec 64)
    (hmen : mL.length < 2 ^ 64) (hvislen : visL.length < 2 ^ 64)
    (hqllen : qL.length < 2 ^ 64)
    (vis' qL' : List (BitVec 32)) (tail' count' u' : BitVec 64)
    (hfwd : bfsRowFwd F mL visL qL n v tail count u =
      .ok (vis', qL', tail', count', u')) :
    evalStmtFuel F bfsInner
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (mkBfsEnv mL vis' qL' orderL n src head tail' count' v u',
        .fellThrough) := by
  induction F generalizing visL qL tail count u vis' qL'
    tail' count' u' with
  | zero =>
    by_cases hult : u.ult n = true
    · have hcon : bfsRowFwd 0 mL visL qL n v tail count u =
          .error .AssertFail := by
        simp only [bfsRowFwd, hult, Bool.false_eq_true, ite_true, ite_false]
      rw [hcon] at hfwd
      cases hfwd
    · have hultF : (u.ult n) = false := Bool.eq_false_of_ne_true hult
      have huvar : evalExpr (.var "u")
          (mkBfsEnv mL visL qL orderL n src head tail count v u) =
          .ok (.u64 u) :=
        evalExpr_var_hit _ _ _
          (mkBfsEnv_u mL visL qL orderL n src head tail count v u)
      have hnvar : evalExpr (.var "n")
          (mkBfsEnv mL visL qL orderL n src head tail count v u) =
          .ok (.u64 n) :=
        evalExpr_var_hit _ _ _
          (mkBfsEnv_n mL visL qL orderL n src head tail count v u)
      have hcond : evalExpr (.ult (.var "u") (.var "n"))
          (mkBfsEnv mL visL qL orderL n src head tail count v u) =
          .ok (.b false) := by
        have h := evalExpr_ult_u64 _ _ _ _ _ huvar hnvar
        rw [hultF] at h
        exact h
      have hev : evalStmtFuel 0 bfsInner
          (mkBfsEnv mL visL qL orderL n src head tail count v u) =
          .ok (mkBfsEnv mL visL qL orderL n src head tail count v u,
            .fellThrough) :=
        evalStmtFuel_zero_while_exit _ _ _ hcond
      have hfw : bfsRowFwd 0 mL visL qL n v tail count u =
          .ok (visL, qL, tail, count, u) := by
        simp only [bfsRowFwd, hult, Bool.false_eq_true, ite_true, ite_false]
      rw [hfw] at hfwd
      have h5 : (visL, qL, tail, count, u) =
          (vis', qL', tail', count', u') := by
        injection hfwd
      simp only [Prod.mk.injEq] at h5
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h5
      exact hev
  | succ F ih =>
    have huvar : evalExpr (.var "u")
        (mkBfsEnv mL visL qL orderL n src head tail count v u) =
        .ok (.u64 u) :=
      evalExpr_var_hit _ _ _
        (mkBfsEnv_u mL visL qL orderL n src head tail count v u)
    have hnvar : evalExpr (.var "n")
        (mkBfsEnv mL visL qL orderL n src head tail count v u) =
        .ok (.u64 n) :=
      evalExpr_var_hit _ _ _
        (mkBfsEnv_n mL visL qL orderL n src head tail count v u)
    by_cases hult : u.ult n = true
    · have hcondT : evalExpr (.ult (.var "u") (.var "n"))
          (mkBfsEnv mL visL qL orderL n src head tail count v u) =
          .ok (.b true) := by
        have h := evalExpr_ult_u64 _ _ _ _ _ huvar hnvar
        rw [hult] at h
        exact h
      match hgetm : mL[(v * n + u).toNat]? with
      | none =>
        have hcon : bfsRowFwd (F + 1) mL visL qL n v tail count u =
            .error .AssertFail := by
          simp only [bfsRowFwd, hult, hgetm, ite_true, ite_false]
        rw [hcon] at hfwd
        cases hfwd
      | some g =>
        by_cases hgm : g != (BitVec.ofNat 32 0)
        · match hgetv : visL[u.toNat]? with
          | none =>
            have hcon : bfsRowFwd (F + 1) mL visL qL n v tail count u =
                .error .AssertFail := by
              simp only [bfsRowFwd, hult, hgetm, hgm, hgetv,
                ite_true, ite_false]
            rw [hcon] at hfwd
            cases hfwd
          | some w =>
            by_cases hgv : w == (BitVec.ofNat 32 0)
            · match hgetq : qL[tail.toNat]? with
              | none =>
                have hcon : bfsRowFwd (F + 1) mL visL qL n v tail count u =
                    .error .AssertFail := by
                  simp only [bfsRowFwd, hult, hgetm, hgm, hgetv, hgv,
                    hgetq, ite_true, ite_false]
                rw [hcon] at hfwd
                cases hfwd
              | some _ =>
                have hvislen1 : (visL.set u.toNat 1).length < 2 ^ 64 := by
                  rw [List.length_set]
                  exact hvislen
                have hltq : tail.toNat < qL.length :=
                  bfsGetElem_some_lt hgetq
                have hqllen1 : (qL.set tail.toNat
                    (BitVec.ofNat 32 u.toNat)).length < 2 ^ 64 := by
                  rw [List.length_set]
                  exact hqllen
                have hb : evalStmtFuel F bfsInnerBody
                    (mkBfsEnv mL visL qL orderL
                      n src head tail count v u) =
                    .ok (mkBfsEnv mL (visL.set u.toNat 1)
                      (qL.set tail.toNat (BitVec.ofNat 32 u.toNat))
                      orderL n src head (tail + 1) (count + 1) v (u + 1),
                      .fellThrough) := by
                  have h := bfsInnerBody_eval F mL visL qL orderL
                    n src head tail count v u hmen hvislen hqllen
                  simp only [hgetm, hgm, hgetv, hgv, hgetq] at h
                  exact h
                have hloop : evalStmtFuel (F + 1) bfsInner
                    (mkBfsEnv mL visL qL orderL
                      n src head tail count v u) =
                    evalStmtFuel F bfsInner (mkBfsEnv mL
                      (visL.set u.toNat 1)
                      (qL.set tail.toNat (BitVec.ofNat 32 u.toNat))
                      orderL n src head (tail + 1) (count + 1)
                      v (u + 1)) := by
                  simp only [bfsInner, evalStmtFuel, evalStmtSuccHandler,
                    evalStmtWith, hcondT, hb]
                have hfwd1 : bfsRowFwd (F + 1) mL visL qL n v tail count u =
                    bfsRowFwd F mL (visL.set u.toNat 1)
                      (qL.set tail.toNat (BitVec.ofNat 32 u.toNat))
                      n v (tail + 1) (count + 1) (u + 1) := by
                  simp only [bfsRowFwd, hult, hgetm, hgm, hgetv, hgv,
                    hgetq, ite_true, ite_false]
                rw [hfwd1] at hfwd
                rw [hloop]
                exact ih _ _ _ _ _ hvislen1 hqllen1 _ _ _ _ _ hfwd
            · have hfalse : (w == (BitVec.ofNat 32 0)) = false :=
                Bool.eq_false_of_ne_true hgv
              have hb : evalStmtFuel F bfsInnerBody
                  (mkBfsEnv mL visL qL orderL n src head tail count v u) =
                  .ok (mkBfsEnv mL visL qL orderL n src head tail count
                    v (u + 1), .fellThrough) := by
                have h := bfsInnerBody_eval F mL visL qL orderL
                  n src head tail count v u hmen hvislen hqllen
                simp only [hgetm, hgm, hgetv, hfalse] at h
                exact h
              have hloop : evalStmtFuel (F + 1) bfsInner
                  (mkBfsEnv mL visL qL orderL n src head tail count v u) =
                  evalStmtFuel F bfsInner
                    (mkBfsEnv mL visL qL orderL n src head tail count
                      v (u + 1)) := by
                simp only [bfsInner, evalStmtFuel, evalStmtSuccHandler,
                  evalStmtWith, hcondT, hb]
              have hfwd1 : bfsRowFwd (F + 1) mL visL qL n v tail count u =
                  bfsRowFwd F mL visL qL n v tail count (u + 1) := by
                simp only [bfsRowFwd, hult, hgetm, hgm, hgetv, hgv,
                  Bool.false_eq_true, ite_true, ite_false]
              rw [hfwd1] at hfwd
              rw [hloop]
              exact ih _ _ _ _ _ hvislen hqllen _ _ _ _ _ hfwd
        · have hfalseM : (g != (BitVec.ofNat 32 0)) = false :=
            Bool.eq_false_of_ne_true hgm
          have hb : evalStmtFuel F bfsInnerBody
              (mkBfsEnv mL visL qL orderL n src head tail count v u) =
              .ok (mkBfsEnv mL visL qL orderL n src head tail count
                v (u + 1), .fellThrough) := by
            have h := bfsInnerBody_eval F mL visL qL orderL
              n src head tail count v u hmen hvislen hqllen
            simp only [hgetm, hfalseM] at h
            exact h
          have hloop : evalStmtFuel (F + 1) bfsInner
              (mkBfsEnv mL visL qL orderL n src head tail count v u) =
              evalStmtFuel F bfsInner
                (mkBfsEnv mL visL qL orderL n src head tail count v (u + 1)) := by
            simp only [bfsInner, evalStmtFuel, evalStmtSuccHandler,
              evalStmtWith, hcondT, hb]
          have hfwd1 : bfsRowFwd (F + 1) mL visL qL n v tail count u =
              bfsRowFwd F mL visL qL n v tail count (u + 1) := by
            simp only [bfsRowFwd, hult, hgetm, hgm, Bool.false_eq_true,
              ite_true, ite_false]
          rw [hfwd1] at hfwd
          rw [hloop]
          exact ih _ _ _ _ _ hvislen hqllen _ _ _ _ _ hfwd
    · have hultF : (u.ult n) = false := Bool.eq_false_of_ne_true hult
      have hcond : evalExpr (.ult (.var "u") (.var "n"))
          (mkBfsEnv mL visL qL orderL n src head tail count v u) =
          .ok (.b false) := by
        have h := evalExpr_ult_u64 _ _ _ _ _ huvar hnvar
        rw [hultF] at h
        exact h
      have hev : evalStmtFuel (F + 1) bfsInner
          (mkBfsEnv mL visL qL orderL n src head tail count v u) =
          .ok (mkBfsEnv mL visL qL orderL n src head tail count v u,
            .fellThrough) := by
        simp [bfsInner, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond]
      have hfw : bfsRowFwd (F + 1) mL visL qL n v tail count u =
          .ok (visL, qL, tail, count, u) := by
        simp only [bfsRowFwd, hult, Bool.false_eq_true, ite_true, ite_false]
      rw [hfw] at hfwd
      have h5 : (visL, qL, tail, count, u) =
          (vis', qL', tail', count', u') := by
        injection hfwd
      simp only [Prod.mk.injEq] at h5
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h5
      exact hev

/-- Row scan at fuel `F`: the evaluator agrees with the forward on
    every `.error` run (fuel induction; the ok legs step the loop and
    apply the IH). -/
theorem bfsRow_err (F : Nat) (mL visL qL orderL : List (BitVec 32))
    (n src head tail count v u : BitVec 64)
    (hmen : mL.length < 2 ^ 64) (hvislen : visL.length < 2 ^ 64)
    (hqllen : qL.length < 2 ^ 64)
    (e : Panic)
    (hfwd : bfsRowFwd F mL visL qL n v tail count u = .error e) :
    evalStmtFuel F bfsInner
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .error e := by
  induction F generalizing visL qL tail count u with
  | zero =>
    by_cases hult : u.ult n = true
    · have hultT : (u.ult n) = true := hult
      have huvar : evalExpr (.var "u")
          (mkBfsEnv mL visL qL orderL n src head tail count v u) =
          .ok (.u64 u) :=
        evalExpr_var_hit _ _ _
          (mkBfsEnv_u mL visL qL orderL n src head tail count v u)
      have hnvar : evalExpr (.var "n")
          (mkBfsEnv mL visL qL orderL n src head tail count v u) =
          .ok (.u64 n) :=
        evalExpr_var_hit _ _ _
          (mkBfsEnv_n mL visL qL orderL n src head tail count v u)
      have hcond : evalExpr (.ult (.var "u") (.var "n"))
          (mkBfsEnv mL visL qL orderL n src head tail count v u) =
          .ok (.b true) := by
        have h := evalExpr_ult_u64 _ _ _ _ _ huvar hnvar
        rw [hultT] at h
        exact h
      have hev : evalStmtFuel 0 bfsInner
          (mkBfsEnv mL visL qL orderL n src head tail count v u) =
          .error .AssertFail :=
        evalStmtFuel_zero_while_enter _ _ _ hcond
      have hcon : bfsRowFwd 0 mL visL qL n v tail count u =
          .error .AssertFail := by
        simp only [bfsRowFwd, hultT, ite_true, ite_false]
      rw [hcon] at hfwd
      cases hfwd
      exact hev
    · have hfw : bfsRowFwd 0 mL visL qL n v tail count u =
          .ok (visL, qL, tail, count, u) := by
        simp only [bfsRowFwd, hult, Bool.false_eq_true, ite_true, ite_false]
      rw [hfw] at hfwd
      cases hfwd
  | succ F ih =>
    have huvar : evalExpr (.var "u")
        (mkBfsEnv mL visL qL orderL n src head tail count v u) =
        .ok (.u64 u) :=
      evalExpr_var_hit _ _ _
        (mkBfsEnv_u mL visL qL orderL n src head tail count v u)
    have hnvar : evalExpr (.var "n")
        (mkBfsEnv mL visL qL orderL n src head tail count v u) =
        .ok (.u64 n) :=
      evalExpr_var_hit _ _ _
        (mkBfsEnv_n mL visL qL orderL n src head tail count v u)
    by_cases hult : u.ult n = true
    · have hcondT : evalExpr (.ult (.var "u") (.var "n"))
          (mkBfsEnv mL visL qL orderL n src head tail count v u) =
          .ok (.b true) := by
        have h := evalExpr_ult_u64 _ _ _ _ _ huvar hnvar
        rw [hult] at h
        exact h
      -- Body-error legs reuse the single-step theorem, then the loop
      -- replays the error through the successor handler.
      match hgetm : mL[(v * n + u).toNat]? with
      | none =>
        have hcon : bfsRowFwd (F + 1) mL visL qL n v tail count u =
            .error .AssertFail := by
          simp only [bfsRowFwd, hult, hgetm, ite_true, ite_false]
        have hb : evalStmtFuel F bfsInnerBody
            (mkBfsEnv mL visL qL orderL n src head tail count v u) =
            .error .AssertFail := by
          have h := bfsInnerBody_eval F mL visL qL orderL
            n src head tail count v u hmen hvislen hqllen
          simp only [hgetm] at h
          exact h
        have hev : evalStmtFuel (F + 1) bfsInner
            (mkBfsEnv mL visL qL orderL n src head tail count v u) =
            .error .AssertFail := by
          simp only [bfsInner, evalStmtFuel, evalStmtSuccHandler,
            evalStmtWith, hcondT, hb]
        rw [hcon] at hfwd
        cases hfwd
        exact hev
      | some g =>
        by_cases hgm : g != (BitVec.ofNat 32 0)
        · match hgetv : visL[u.toNat]? with
          | none =>
            have hcon : bfsRowFwd (F + 1) mL visL qL n v tail count u =
                .error .AssertFail := by
              simp only [bfsRowFwd, hult, hgetm, hgm, hgetv, ite_true,
                ite_false]
            have hb : evalStmtFuel F bfsInnerBody
                (mkBfsEnv mL visL qL orderL n src head tail count v u) =
                .error .AssertFail := by
              have h := bfsInnerBody_eval F mL visL qL orderL
                n src head tail count v u hmen hvislen hqllen
              simp only [hgetm, hgm, hgetv] at h
              exact h
            have hev : evalStmtFuel (F + 1) bfsInner
                (mkBfsEnv mL visL qL orderL n src head tail count v u) =
                .error .AssertFail := by
              simp only [bfsInner, evalStmtFuel, evalStmtSuccHandler,
                evalStmtWith, hcondT, hb]
            rw [hcon] at hfwd
            cases hfwd
            exact hev
          | some w =>
            by_cases hgv : w == (BitVec.ofNat 32 0)
            · match hgetq : qL[tail.toNat]? with
              | none =>
                have hcon : bfsRowFwd (F + 1) mL visL qL n v tail count u =
                    .error .AssertFail := by
                  simp only [bfsRowFwd, hult, hgetm, hgm, hgetv, hgv,
                    hgetq, ite_true, ite_false]
                have hb : evalStmtFuel F bfsInnerBody
                    (mkBfsEnv mL visL qL orderL
                      n src head tail count v u) =
                    .error .AssertFail := by
                  have h := bfsInnerBody_eval F mL visL qL orderL
                    n src head tail count v u hmen hvislen hqllen
                  simp only [hgetm, hgm, hgetv, hgv, hgetq] at h
                  exact h
                have hev : evalStmtFuel (F + 1) bfsInner
                    (mkBfsEnv mL visL qL orderL
                      n src head tail count v u) =
                    .error .AssertFail := by
                  simp only [bfsInner, evalStmtFuel, evalStmtSuccHandler,
                    evalStmtWith, hcondT, hb]
                rw [hcon] at hfwd
                cases hfwd
                exact hev
              | some _ =>
                have hvislen1 : (visL.set u.toNat 1).length < 2 ^ 64 := by
                  rw [List.length_set]
                  exact hvislen
                have hltq : tail.toNat < qL.length :=
                  bfsGetElem_some_lt hgetq
                have hqllen1 : (qL.set tail.toNat
                    (BitVec.ofNat 32 u.toNat)).length < 2 ^ 64 := by
                  rw [List.length_set]
                  exact hqllen
                have hb : evalStmtFuel F bfsInnerBody
                    (mkBfsEnv mL visL qL orderL
                      n src head tail count v u) =
                    .ok (mkBfsEnv mL (visL.set u.toNat 1)
                      (qL.set tail.toNat (BitVec.ofNat 32 u.toNat))
                      orderL n src head (tail + 1) (count + 1) v (u + 1),
                      .fellThrough) := by
                  have h := bfsInnerBody_eval F mL visL qL orderL
                    n src head tail count v u hmen hvislen hqllen
                  simp only [hgetm, hgm, hgetv, hgv, hgetq] at h
                  exact h
                have hloop : evalStmtFuel (F + 1) bfsInner
                    (mkBfsEnv mL visL qL orderL
                      n src head tail count v u) =
                    evalStmtFuel F bfsInner (mkBfsEnv mL
                      (visL.set u.toNat 1)
                      (qL.set tail.toNat (BitVec.ofNat 32 u.toNat))
                      orderL n src head (tail + 1) (count + 1)
                      v (u + 1)) := by
                  simp only [bfsInner, evalStmtFuel, evalStmtSuccHandler,
                    evalStmtWith, hcondT, hb]
                have hfwd1 : bfsRowFwd (F + 1) mL visL qL n v tail count u =
                    bfsRowFwd F mL (visL.set u.toNat 1)
                      (qL.set tail.toNat (BitVec.ofNat 32 u.toNat))
                      n v (tail + 1) (count + 1) (u + 1) := by
                  simp only [bfsRowFwd, hult, hgetm, hgm, hgetv, hgv,
                    hgetq, ite_true, ite_false]
                rw [hfwd1] at hfwd
                rw [hloop]
                exact ih _ _ _ _ _ hvislen1 hqllen1 hfwd
            · have hfalse : (w == (BitVec.ofNat 32 0)) = false :=
                Bool.eq_false_of_ne_true hgv
              have hb : evalStmtFuel F bfsInnerBody
                  (mkBfsEnv mL visL qL orderL n src head tail count v u) =
                  .ok (mkBfsEnv mL visL qL orderL n src head tail count
                    v (u + 1), .fellThrough) := by
                have h := bfsInnerBody_eval F mL visL qL orderL
                  n src head tail count v u hmen hvislen hqllen
                simp only [hgetm, hgm, hgetv, hfalse] at h
                exact h
              have hloop : evalStmtFuel (F + 1) bfsInner
                  (mkBfsEnv mL visL qL orderL n src head tail count v u) =
                  evalStmtFuel F bfsInner
                    (mkBfsEnv mL visL qL orderL n src head tail count
                      v (u + 1)) := by
                simp only [bfsInner, evalStmtFuel, evalStmtSuccHandler,
                  evalStmtWith, hcondT, hb]
              have hfwd1 : bfsRowFwd (F + 1) mL visL qL n v tail count u =
                  bfsRowFwd F mL visL qL n v tail count (u + 1) := by
                simp only [bfsRowFwd, hult, hgetm, hgm, hgetv, hgv,
                  Bool.false_eq_true, ite_true, ite_false]
              rw [hfwd1] at hfwd
              rw [hloop]
              exact ih _ _ _ _ _ hvislen hqllen hfwd
        · have hfalseM : (g != (BitVec.ofNat 32 0)) = false :=
            Bool.eq_false_of_ne_true hgm
          have hb : evalStmtFuel F bfsInnerBody
              (mkBfsEnv mL visL qL orderL n src head tail count v u) =
              .ok (mkBfsEnv mL visL qL orderL n src head tail count
                v (u + 1), .fellThrough) := by
            have h := bfsInnerBody_eval F mL visL qL orderL
              n src head tail count v u hmen hvislen hqllen
            simp only [hgetm, hfalseM] at h
            exact h
          have hloop : evalStmtFuel (F + 1) bfsInner
              (mkBfsEnv mL visL qL orderL n src head tail count v u) =
              evalStmtFuel F bfsInner
                (mkBfsEnv mL visL qL orderL n src head tail count v (u + 1)) := by
            simp only [bfsInner, evalStmtFuel, evalStmtSuccHandler,
              evalStmtWith, hcondT, hb]
          have hfwd1 : bfsRowFwd (F + 1) mL visL qL n v tail count u =
              bfsRowFwd F mL visL qL n v tail count (u + 1) := by
            simp only [bfsRowFwd, hult, hgetm, hgm, Bool.false_eq_true,
              ite_true, ite_false]
          rw [hfwd1] at hfwd
          rw [hloop]
          exact ih _ _ _ _ _ hvislen hqllen hfwd
    · have hultF : (u.ult n) = false := Bool.eq_false_of_ne_true hult
      have hcond : evalExpr (.ult (.var "u") (.var "n"))
          (mkBfsEnv mL visL qL orderL n src head tail count v u) =
          .ok (.b false) := by
        have h := evalExpr_ult_u64 _ _ _ _ _ huvar hnvar
        rw [hultF] at h
        exact h
      have hev : evalStmtFuel (F + 1) bfsInner
          (mkBfsEnv mL visL qL orderL n src head tail count v u) =
          .ok (mkBfsEnv mL visL qL orderL n src head tail count v u,
            .fellThrough) := by
        simp [bfsInner, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond]
      have hfw : bfsRowFwd (F + 1) mL visL qL n v tail count u =
          .ok (visL, qL, tail, count, u) := by
        simp only [bfsRowFwd, hult, Bool.false_eq_true, ite_true, ite_false]
      rw [hfw] at hfwd
      cases hfwd

/-- Narrow-after-widen is the identity on 32-bit words: the visit
    record `(int)v` stores back the dequeued word. -/
theorem bfsNarrowWiden (w : BitVec 32) :
    BitVec.ofNat 32 (w.signExtend 64).toNat = w := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  rw [BitVec.toNat_signExtend]
  have hzw : (w.setWidth 64).toNat = w.toNat := by
    rw [BitVec.toNat_setWidth]
    have hlt : w.toNat < 2 ^ 64 :=
      Nat.lt_of_lt_of_le w.isLt (by decide)
    exact Nat.mod_eq_of_lt hlt
  rw [hzw]
  by_cases hmsb : w.msb = true
  · rw [if_pos hmsb]
    have hlt : w.toNat < 2 ^ 32 := w.isLt
    omega
  · rw [if_neg hmsb]
    exact Nat.mod_eq_of_lt w.isLt

/-- An ok row scan only ever stores through `vecSet`: both list
    lengths are preserved (feeds the outer loop's bound refresh). -/
theorem bfsRow_ok_len (F : Nat) (mL visL qL : List (BitVec 32))
    (n v tail count u : BitVec 64)
    (vis' qL' : List (BitVec 32)) (tail' count' u' : BitVec 64)
    (hfwd : bfsRowFwd F mL visL qL n v tail count u =
      .ok (vis', qL', tail', count', u')) :
    vis'.length = visL.length ∧ qL'.length = qL.length := by
  induction F generalizing visL qL tail count u with
  | zero =>
    by_cases hult : u.ult n = true
    · have hcon : bfsRowFwd 0 mL visL qL n v tail count u =
          .error .AssertFail := by
        simp only [bfsRowFwd, hult, ite_true, ite_false]
      rw [hcon] at hfwd
      cases hfwd
    · have hfw : bfsRowFwd 0 mL visL qL n v tail count u =
          .ok (visL, qL, tail, count, u) := by
        simp only [bfsRowFwd, hult, Bool.false_eq_true, ite_true, ite_false]
      rw [hfw] at hfwd
      cases hfwd
      exact ⟨rfl, rfl⟩
  | succ F ih =>
    by_cases hult : u.ult n = true
    · match hgetm : mL[(v * n + u).toNat]? with
      | none =>
        have hcon : bfsRowFwd (F + 1) mL visL qL n v tail count u =
            .error .AssertFail := by
          simp only [bfsRowFwd, hult, hgetm, ite_true, ite_false]
        rw [hcon] at hfwd
        cases hfwd
      | some g =>
        by_cases hgm : g != (BitVec.ofNat 32 0)
        · match hgetv : visL[u.toNat]? with
          | none =>
            have hcon : bfsRowFwd (F + 1) mL visL qL n v tail count u =
                .error .AssertFail := by
              simp only [bfsRowFwd, hult, hgetm, hgm, hgetv, ite_true,
                ite_false]
            rw [hcon] at hfwd
            cases hfwd
          | some w =>
            by_cases hgv : w == (BitVec.ofNat 32 0)
            · match hgetq : qL[tail.toNat]? with
              | none =>
                have hcon : bfsRowFwd (F + 1) mL visL qL n v tail count u =
                    .error .AssertFail := by
                  simp only [bfsRowFwd, hult, hgetm, hgm, hgetv, hgv,
                    hgetq, ite_true, ite_false]
                rw [hcon] at hfwd
                cases hfwd
              | some _ =>
                have hfwd1 : bfsRowFwd (F + 1) mL visL qL n v tail count u =
                    bfsRowFwd F mL (visL.set u.toNat 1)
                      (qL.set tail.toNat (BitVec.ofNat 32 u.toNat))
                      n v (tail + 1) (count + 1) (u + 1) := by
                  simp only [bfsRowFwd, hult, hgetm, hgm, hgetv, hgv,
                    hgetq, ite_true, ite_false]
                rw [hfwd1] at hfwd
                have hih := ih _ _ _ _ _ hfwd
                simp only [List.length_set] at hih
                exact hih
            · have hfwd1 : bfsRowFwd (F + 1) mL visL qL n v tail count u =
                  bfsRowFwd F mL visL qL n v tail count (u + 1) := by
                simp only [bfsRowFwd, hult, hgetm, hgm, hgetv, hgv,
                  Bool.false_eq_true, ite_true, ite_false]
              rw [hfwd1] at hfwd
              exact ih _ _ _ _ _ hfwd
        · have hfwd1 : bfsRowFwd (F + 1) mL visL qL n v tail count u =
              bfsRowFwd F mL visL qL n v tail count (u + 1) := by
            simp only [bfsRowFwd, hult, hgetm, hgm, Bool.false_eq_true,
              ite_true, ite_false]
          rw [hfwd1] at hfwd
          exact ih _ _ _ _ _ hfwd
    · have hfw : bfsRowFwd (F + 1) mL visL qL n v tail count u =
          .ok (visL, qL, tail, count, u) := by
        simp only [bfsRowFwd, hult, Bool.false_eq_true, ite_true, ite_false]
      rw [hfw] at hfwd
      cases hfwd
      exact ⟨rfl, rfl⟩

/-- One drain iteration with the guard holding: guarded widening
    dequeue read, guarded visit record, head advance, `u` reset,
    then hand off to the row scan (any fuel). -/
theorem bfsOuterBody_ok (F : Nat) (mL visL qL orderL : List (BitVec 32))
    (n src head tail count v u : BitVec 64)
    (w : BitVec 32) (hget : qL[head.toNat]? = some w)
    (hg : (head.ult (BitVec.ofNat 64 qL.length)) = true)
    (wO : BitVec 32) (hgetO : orderL[head.toNat]? = some wO)
    (hgO : (head.ult (BitVec.ofNat 64 orderL.length)) = true) :
    evalStmtFuel F bfsOuterBody
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      evalStmtFuel F bfsInner
        (mkBfsEnv mL visL qL (orderL.set head.toNat w)
          n src (head + 1) tail count (w.signExtend 64) 0) := by
  have hbody : bfsOuterBody =
      .seq (.if_ (.ult (.var "head") (.stdVecLen "q"))
              (.assign "v" (.u64ofI32 (.stdVecAt "q" (.var "head"))))
              .fail)
      (.seq (.if_ (.ult (.var "head") (.stdVecLen "order"))
              (.vecSet "order" (.var "head") (.i32ofU64 (.var "v")))
              .fail)
      (.seq (.assign "head" (.uadd (.var "head")
                (.lit (.u64 (BitVec.ofNat 64 1)))))
      (.seq (.assign "u" (.lit (.u64 (BitVec.ofNat 64 0))))
        bfsInner))) := rfl
  have hhead : evalExpr (.var "head")
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.u64 head) :=
    evalExpr_var_hit _ _ _
      (mkBfsEnv_head mL visL qL orderL n src head tail count v u)
  have hlen : evalExpr (.stdVecLen "q")
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.u64 (BitVec.ofNat 64 qL.length)) :=
    evalExpr_stdVecLen_some "q" _ qL
      (mkBfsEnv_q mL visL qL orderL n src head tail count v u)
  have hguard : evalExpr (.ult (.var "head") (.stdVecLen "q"))
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.b true) := by
    have h := evalExpr_ult_u64 _ _ _ _ _ hhead hlen
    rw [hg] at h
    exact h
  have hq := mkBfsEnv_q mL visL qL orderL n src head tail count v u
  have hread : evalExpr (.stdVecAt "q" (.var "head"))
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.i32 w) :=
    evalExpr_stdVecAt_some "q" _ _ _ _ _ hq hhead hget
  have hwide := evalExpr_u64ofI32_ok _ _ _ hread
  have huv : envUpdate
      (mkBfsEnv mL visL qL orderL n src head tail count v u) "v"
      (.u64 (w.signExtend 64)) =
      some (mkBfsEnv mL visL qL orderL n src head tail count
        (w.signExtend 64) u) := by
    simp [mkBfsEnv, envUpdate,
      show ("u" : String) ≠ "v" by decide]
  have hassignV := evalStmtFuel_assign F "v"
    (.u64ofI32 (.stdVecAt "q" (.var "head")))
    (mkBfsEnv mL visL qL orderL n src head tail count v u) _ _ hwide huv
  have hheadV : evalExpr (.var "head")
      (mkBfsEnv mL visL qL orderL n src head tail count
        (w.signExtend 64) u) = .ok (.u64 head) :=
    evalExpr_var_hit _ _ _ (by
      simp [envLookup, mkBfsEnv,
        show ("u" : String) ≠ "head" by decide,
        show ("v" : String) ≠ "head" by decide,
        show ("count" : String) ≠ "head" by decide,
        show ("tail" : String) ≠ "head" by decide])
  have hlenO : evalExpr (.stdVecLen "order")
      (mkBfsEnv mL visL qL orderL n src head tail count
        (w.signExtend 64) u) =
      .ok (.u64 (BitVec.ofNat 64 orderL.length)) :=
    evalExpr_stdVecLen_some "order" _ orderL
      (mkBfsEnv_order mL visL qL orderL n src head tail count
        (w.signExtend 64) u)
  have hguardO : evalExpr (.ult (.var "head") (.stdVecLen "order"))
      (mkBfsEnv mL visL qL orderL n src head tail count
        (w.signExtend 64) u) = .ok (.b true) := by
    have h := evalExpr_ult_u64 _ _ _ _ _ hheadV hlenO
    rw [hgO] at h
    exact h
  have hvarV : evalExpr (.var "v")
      (mkBfsEnv mL visL qL orderL n src head tail count
        (w.signExtend 64) u) = .ok (.u64 (w.signExtend 64)) :=
    evalExpr_var_hit _ _ _ (by
      simp [envLookup, mkBfsEnv,
        show ("u" : String) ≠ "v" by decide])
  have hvalO : evalExpr (.i32ofU64 (.var "v"))
      (mkBfsEnv mL visL qL orderL n src head tail count
        (w.signExtend 64) u) = .ok (.i32 w) := by
    have h := evalExpr_i32ofU64_ok _ _ _ hvarV
    rw [bfsNarrowWiden] at h
    exact h
  have horder := mkBfsEnv_order mL visL qL orderL n src head tail count
    (w.signExtend 64) u
  have huO : envUpdate
      (mkBfsEnv mL visL qL orderL n src head tail count
        (w.signExtend 64) u) "order"
      (.stdVecVal (orderL.set head.toNat w)) =
      some (mkBfsEnv mL visL qL (orderL.set head.toNat w)
        n src head tail count (w.signExtend 64) u) := by
    simp [mkBfsEnv, envUpdate,
      show ("u" : String) ≠ "order" by decide,
      show ("v" : String) ≠ "order" by decide,
      show ("count" : String) ≠ "order" by decide,
      show ("tail" : String) ≠ "order" by decide,
      show ("head" : String) ≠ "order" by decide,
      show ("m" : String) ≠ "order" by decide,
      show ("vis" : String) ≠ "order" by decide,
      show ("q" : String) ≠ "order" by decide]
  have hsetO := evalStmtFuel_vecSet F "order" (.var "head")
    (.i32ofU64 (.var "v"))
    (mkBfsEnv mL visL qL orderL n src head tail count
      (w.signExtend 64) u) head w orderL wO _ hheadV hvalO horder hgetO huO
  have hhead2 : evalExpr (.var "head")
      (mkBfsEnv mL visL qL (orderL.set head.toNat w)
        n src head tail count (w.signExtend 64) u) =
      .ok (.u64 head) :=
    evalExpr_var_hit _ _ _ (by
      simp [envLookup, mkBfsEnv,
        show ("u" : String) ≠ "head" by decide,
        show ("v" : String) ≠ "head" by decide,
        show ("count" : String) ≠ "head" by decide,
        show ("tail" : String) ≠ "head" by decide])
  have hone : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      (mkBfsEnv mL visL qL (orderL.set head.toNat w)
        n src head tail count (w.signExtend 64) u) =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have huH : envUpdate
      (mkBfsEnv mL visL qL (orderL.set head.toNat w)
        n src head tail count (w.signExtend 64) u) "head"
      (.u64 (head + 1)) =
      some (mkBfsEnv mL visL qL (orderL.set head.toNat w)
        n src (head + 1) tail count (w.signExtend 64) u) := by
    simp [mkBfsEnv, envUpdate,
      show ("u" : String) ≠ "head" by decide,
      show ("v" : String) ≠ "head" by decide,
      show ("count" : String) ≠ "head" by decide,
      show ("tail" : String) ≠ "head" by decide]
  have hadd1 := evalExpr_uadd_u64 _ _ _ _ _ hhead2 hone
  have hassignH := evalStmtFuel_assign F "head"
    (.uadd (.var "head") (.lit (.u64 (BitVec.ofNat 64 1))))
    (mkBfsEnv mL visL qL (orderL.set head.toNat w)
      n src head tail count (w.signExtend 64) u) _ _ hadd1 huH
  have hzero : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (mkBfsEnv mL visL qL (orderL.set head.toNat w)
        n src (head + 1) tail count (w.signExtend 64) u) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  have huU : envUpdate
      (mkBfsEnv mL visL qL (orderL.set head.toNat w)
        n src (head + 1) tail count (w.signExtend 64) u) "u"
      (.u64 (BitVec.ofNat 64 0)) =
      some (mkBfsEnv mL visL qL (orderL.set head.toNat w)
        n src (head + 1) tail count (w.signExtend 64) 0) := by
    simp [mkBfsEnv, envUpdate]
  have hassignU := evalStmtFuel_assign F "u"
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (mkBfsEnv mL visL qL (orderL.set head.toNat w)
      n src (head + 1) tail count (w.signExtend 64) u)
    _ _ hzero huU
  have hifV := (evalStmtFuel_if_true F _
    (.assign "v" (.u64ofI32 (.stdVecAt "q" (.var "head")))) .fail _
    hguard).trans hassignV
  have hifO := (evalStmtFuel_if_true F _
    (.vecSet "order" (.var "head") (.i32ofU64 (.var "v"))) .fail _
    hguardO).trans hsetO
  have hheadSeq := evalStmtFuel_seq_fallthrough F _
    (.seq (.assign "u" (.lit (.u64 (BitVec.ofNat 64 0)))) bfsInner) _ _
    hassignH
  have huseq := evalStmtFuel_seq_fallthrough F _ bfsInner _ _ hassignU
  have htailSeq := hheadSeq.trans huseq
  have hmid := (evalStmtFuel_seq_fallthrough F _ _ _ _ hifO).trans htailSeq
  rw [hbody]
  exact (evalStmtFuel_seq_fallthrough F _ _ _ _ hifV).trans hmid

/-- One drain iteration with a dead queue slot aborts loudly. -/
theorem bfsOuterBody_missQ (F : Nat) (mL visL qL orderL : List (BitVec 32))
    (n src head tail count v u : BitVec 64)
    (hg : ((head.ult (BitVec.ofNat 64 qL.length))) = false) :
    evalStmtFuel F bfsOuterBody
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .error .AssertFail := by
  have hbody : bfsOuterBody =
      .seq (.if_ (.ult (.var "head") (.stdVecLen "q"))
              (.assign "v" (.u64ofI32 (.stdVecAt "q" (.var "head"))))
              .fail)
      (.seq (.if_ (.ult (.var "head") (.stdVecLen "order"))
              (.vecSet "order" (.var "head") (.i32ofU64 (.var "v")))
              .fail)
      (.seq (.assign "head" (.uadd (.var "head")
                (.lit (.u64 (BitVec.ofNat 64 1)))))
      (.seq (.assign "u" (.lit (.u64 (BitVec.ofNat 64 0))))
        bfsInner))) := rfl
  have hhead : evalExpr (.var "head")
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.u64 head) :=
    evalExpr_var_hit _ _ _
      (mkBfsEnv_head mL visL qL orderL n src head tail count v u)
  have hlen : evalExpr (.stdVecLen "q")
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.u64 (BitVec.ofNat 64 qL.length)) :=
    evalExpr_stdVecLen_some "q" _ qL
      (mkBfsEnv_q mL visL qL orderL n src head tail count v u)
  have hguard : evalExpr (.ult (.var "head") (.stdVecLen "q"))
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.b false) := by
    have h := evalExpr_ult_u64 _ _ _ _ _ hhead hlen
    rw [hg] at h
    exact h
  have hif := (evalStmtFuel_if_false F _
    (.assign "v" (.u64ofI32 (.stdVecAt "q" (.var "head")))) .fail _
    hguard).trans (evalStmtFuel_fail F _)
  rw [hbody]
  exact evalStmtFuel_seq_err F _ _ _ _ hif

/-- One drain iteration with a dead order slot aborts loudly (the
    dequeue read succeeded, the visit record misses). -/
theorem bfsOuterBody_missO (F : Nat) (mL visL qL orderL : List (BitVec 32))
    (n src head tail count v u : BitVec 64)
    (w : BitVec 32) (hget : qL[head.toNat]? = some w)
    (hg : (head.ult (BitVec.ofNat 64 qL.length)) = true)
    (hgetO : orderL[head.toNat]? = none)
    (hordlen : orderL.length < 2 ^ 64) :
    evalStmtFuel F bfsOuterBody
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .error .AssertFail := by
  have hbody : bfsOuterBody =
      .seq (.if_ (.ult (.var "head") (.stdVecLen "q"))
              (.assign "v" (.u64ofI32 (.stdVecAt "q" (.var "head"))))
              .fail)
      (.seq (.if_ (.ult (.var "head") (.stdVecLen "order"))
              (.vecSet "order" (.var "head") (.i32ofU64 (.var "v")))
              .fail)
      (.seq (.assign "head" (.uadd (.var "head")
                (.lit (.u64 (BitVec.ofNat 64 1)))))
      (.seq (.assign "u" (.lit (.u64 (BitVec.ofNat 64 0))))
        bfsInner))) := rfl
  have hhead : evalExpr (.var "head")
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.u64 head) :=
    evalExpr_var_hit _ _ _
      (mkBfsEnv_head mL visL qL orderL n src head tail count v u)
  have hlen : evalExpr (.stdVecLen "q")
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.u64 (BitVec.ofNat 64 qL.length)) :=
    evalExpr_stdVecLen_some "q" _ qL
      (mkBfsEnv_q mL visL qL orderL n src head tail count v u)
  have hguard : evalExpr (.ult (.var "head") (.stdVecLen "q"))
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.b true) := by
    have h := evalExpr_ult_u64 _ _ _ _ _ hhead hlen
    rw [hg] at h
    exact h
  have hq := mkBfsEnv_q mL visL qL orderL n src head tail count v u
  have hread : evalExpr (.stdVecAt "q" (.var "head"))
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (.i32 w) :=
    evalExpr_stdVecAt_some "q" _ _ _ _ _ hq hhead hget
  have hwide := evalExpr_u64ofI32_ok _ _ _ hread
  have huv : envUpdate
      (mkBfsEnv mL visL qL orderL n src head tail count v u) "v"
      (.u64 (w.signExtend 64)) =
      some (mkBfsEnv mL visL qL orderL n src head tail count
        (w.signExtend 64) u) := by
    simp [mkBfsEnv, envUpdate,
      show ("u" : String) ≠ "v" by decide]
  have hassignV := evalStmtFuel_assign F "v"
    (.u64ofI32 (.stdVecAt "q" (.var "head")))
    (mkBfsEnv mL visL qL orderL n src head tail count v u) _ _ hwide huv
  have hheadV : evalExpr (.var "head")
      (mkBfsEnv mL visL qL orderL n src head tail count
        (w.signExtend 64) u) = .ok (.u64 head) :=
    evalExpr_var_hit _ _ _ (by
      simp [envLookup, mkBfsEnv,
        show ("u" : String) ≠ "head" by decide,
        show ("v" : String) ≠ "head" by decide,
        show ("count" : String) ≠ "head" by decide,
        show ("tail" : String) ≠ "head" by decide])
  have hlenO : evalExpr (.stdVecLen "order")
      (mkBfsEnv mL visL qL orderL n src head tail count
        (w.signExtend 64) u) =
      .ok (.u64 (BitVec.ofNat 64 orderL.length)) :=
    evalExpr_stdVecLen_some "order" _ orderL
      (mkBfsEnv_order mL visL qL orderL n src head tail count
        (w.signExtend 64) u)
  have hifV := (evalStmtFuel_if_true F _
    (.assign "v" (.u64ofI32 (.stdVecAt "q" (.var "head")))) .fail _
    hguard).trans hassignV
  have hnot : ¬ head.toNat < orderL.length := by
    intro hcon
    have hne : orderL[head.toNat]? ≠ none := by
      rw [ne_eq, List.getElem?_eq_none_iff]
      omega
    exact hne hgetO
  have hgO : (head.ult (BitVec.ofNat 64 orderL.length)) = false := by
    have h1 : ¬ head.toNat <
        (BitVec.ofNat 64 orderL.length).toNat := by
      rw [ofNat64_toNat _ hordlen]
      exact hnot
    have h2 : decide (head.toNat <
        (BitVec.ofNat 64 orderL.length).toNat) = false :=
      decide_eq_false h1
    rwa [← BitVec.ult_eq_decide] at h2
  have hguardO : evalExpr (.ult (.var "head") (.stdVecLen "order"))
      (mkBfsEnv mL visL qL orderL n src head tail count
        (w.signExtend 64) u) = .ok (.b false) := by
    have h := evalExpr_ult_u64 _ _ _ _ _ hheadV hlenO
    rw [hgO] at h
    exact h
  have htailErr : evalStmtFuel F
      (.seq (.if_ (.ult (.var "head") (.stdVecLen "order"))
              (.vecSet "order" (.var "head") (.i32ofU64 (.var "v")))
              .fail)
      (.seq (.assign "head" (.uadd (.var "head")
                (.lit (.u64 (BitVec.ofNat 64 1)))))
      (.seq (.assign "u" (.lit (.u64 (BitVec.ofNat 64 0))))
        bfsInner)))
      (mkBfsEnv mL visL qL orderL n src head tail count
        (w.signExtend 64) u) =
      .error .AssertFail := by
    exact evalStmtFuel_seq_err F _ _ _ _
      ((evalStmtFuel_if_false F _ _ _ _ hguardO).trans
        (evalStmtFuel_fail F _))
  rw [hbody]
  exact (evalStmtFuel_seq_fallthrough F _ _ _ _ hifV).trans htailErr

/-- The queue drain at fuel `F`: evaluator agrees with the forward on
    every `.ok` run. -/
theorem bfsOuter_ok (F : Nat) (mL visL qL orderL : List (BitVec 32))
    (n src head tail count v u : BitVec 64)
    (hmen : mL.length < 2 ^ 64) (hvislen : visL.length < 2 ^ 64)
    (hqllen : qL.length < 2 ^ 64) (hordlen : orderL.length < 2 ^ 64)
    (vis' qL' orderL' : List (BitVec 32))
    (head' tail' count' v' u' : BitVec 64)
    (hfwd : bfsOuterFwd F mL visL qL orderL n head tail count v u =
      .ok (vis', qL', orderL', head', tail', count', v', u')) :
    evalStmtFuel F bfsOuter
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .ok (mkBfsEnv mL vis' qL' orderL' n src head' tail' count' v' u',
        .fellThrough) := by
  induction F generalizing visL qL orderL head tail count v u
    vis' qL' orderL' head' tail' count' v' u' with
  | zero =>
    have hheadvar : evalExpr (.var "head")
        (mkBfsEnv mL visL qL orderL n src head tail count v u) =
        .ok (.u64 head) :=
      evalExpr_var_hit _ _ _
        (mkBfsEnv_head mL visL qL orderL n src head tail count v u)
    have htailvar : evalExpr (.var "tail")
        (mkBfsEnv mL visL qL orderL n src head tail count v u) =
        .ok (.u64 tail) :=
      evalExpr_var_hit _ _ _
        (mkBfsEnv_tail mL visL qL orderL n src head tail count v u)
    by_cases hcond : head != tail
    · have hcon : bfsOuterFwd 0 mL visL qL orderL n head tail count v u =
          .error .AssertFail := by
        simp only [bfsOuterFwd, hcond, ite_true, ite_false]
      rw [hcon] at hfwd
      cases hfwd
    · have hfalse : (head != tail) = false :=
        Bool.eq_false_of_ne_true hcond
      have hcondE : evalExpr (.une (.var "head") (.var "tail"))
          (mkBfsEnv mL visL qL orderL n src head tail count v u) =
          .ok (.b false) := by
        have h := evalExpr_une_u64 _ _ _ _ _ hheadvar htailvar
        rw [hfalse] at h
        exact h
      have hev : evalStmtFuel 0 bfsOuter
          (mkBfsEnv mL visL qL orderL n src head tail count v u) =
          .ok (mkBfsEnv mL visL qL orderL n src head tail count v u,
            .fellThrough) :=
        evalStmtFuel_zero_while_exit _ _ _ hcondE
      have hfw : bfsOuterFwd 0 mL visL qL orderL n head tail count v u =
          .ok (visL, qL, orderL, head, tail, count, v, u) := by
        simp only [bfsOuterFwd, hcond, Bool.false_eq_true, ite_true,
          ite_false]
      rw [hfw] at hfwd
      have h8 : (visL, qL, orderL, head, tail, count, v, u) =
          (vis', qL', orderL', head', tail', count', v', u') := by
        injection hfwd
      simp only [Prod.mk.injEq] at h8
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h8
      exact hev
  | succ F ih =>
    have hheadvar : evalExpr (.var "head")
        (mkBfsEnv mL visL qL orderL n src head tail count v u) =
        .ok (.u64 head) :=
      evalExpr_var_hit _ _ _
        (mkBfsEnv_head mL visL qL orderL n src head tail count v u)
    have htailvar : evalExpr (.var "tail")
        (mkBfsEnv mL visL qL orderL n src head tail count v u) =
        .ok (.u64 tail) :=
      evalExpr_var_hit _ _ _
        (mkBfsEnv_tail mL visL qL orderL n src head tail count v u)
    by_cases hcond : head != tail
    · have hcondT : evalExpr (.une (.var "head") (.var "tail"))
          (mkBfsEnv mL visL qL orderL n src head tail count v u) =
          .ok (.b true) := by
        have h := evalExpr_une_u64 _ _ _ _ _ hheadvar htailvar
        rw [hcond] at h
        exact h
      match hget : qL[head.toNat]? with
      | none =>
        have hnot : ¬ head.toNat < qL.length := by
          intro hcon
          have hne : qL[head.toNat]? ≠ none := by
            rw [ne_eq, List.getElem?_eq_none_iff]
            omega
          exact hne hget
        have hgF : (head.ult (BitVec.ofNat 64 qL.length)) = false := by
          have h1 : ¬ head.toNat <
              (BitVec.ofNat 64 qL.length).toNat := by
            rw [ofNat64_toNat _ hqllen]
            exact hnot
          have h2 : decide (head.toNat <
              (BitVec.ofNat 64 qL.length).toNat) = false :=
            decide_eq_false h1
          rwa [← BitVec.ult_eq_decide] at h2
        have hcon : bfsOuterFwd (F + 1) mL visL qL orderL
            n head tail count v u = .error .AssertFail := by
          simp only [bfsOuterFwd, hcond, hget, ite_true, ite_false]
        have hbev : evalStmtFuel F bfsOuterBody
            (mkBfsEnv mL visL qL orderL n src head tail count v u) =
            .error .AssertFail :=
          bfsOuterBody_missQ F mL visL qL orderL
            n src head tail count v u hgF
        have hev : evalStmtFuel (F + 1) bfsOuter
            (mkBfsEnv mL visL qL orderL n src head tail count v u) =
            .error .AssertFail := by
          simp only [bfsOuter, evalStmtFuel, evalStmtSuccHandler,
            evalStmtWith, hcondT, hbev]
        rw [hcon] at hfwd
        cases hfwd
      | some w =>
        have hlt : head.toNat < qL.length :=
          bfsGetElem_some_lt hget
        have hgT : (head.ult (BitVec.ofNat 64 qL.length)) = true := by
          have h2 : decide (head.toNat <
              (BitVec.ofNat 64 qL.length).toNat) = true := by
            rw [ofNat64_toNat _ hqllen]
            exact decide_eq_true hlt
          rwa [← BitVec.ult_eq_decide] at h2
        match hgetO : orderL[head.toNat]? with
        | none =>
          have hcon : bfsOuterFwd (F + 1) mL visL qL orderL
              n head tail count v u = .error .AssertFail := by
            simp only [bfsOuterFwd, hcond, hget, hgetO, ite_true, ite_false]
          have hbev : evalStmtFuel F bfsOuterBody
              (mkBfsEnv mL visL qL orderL n src head tail count v u) =
              .error .AssertFail :=
            bfsOuterBody_missO F mL visL qL orderL
              n src head tail count v u w hget hgT hgetO hordlen
          have hev : evalStmtFuel (F + 1) bfsOuter
              (mkBfsEnv mL visL qL orderL n src head tail count v u) =
              .error .AssertFail := by
            simp only [bfsOuter, evalStmtFuel, evalStmtSuccHandler,
              evalStmtWith, hcondT, hbev]
          rw [hcon] at hfwd
          cases hfwd
        | some wO =>
          have hltO : head.toNat < orderL.length :=
            bfsGetElem_some_lt hgetO
          have hgOT : (head.ult
              (BitVec.ofNat 64 orderL.length)) = true := by
            have h2 : decide (head.toNat <
                (BitVec.ofNat 64 orderL.length).toNat) = true := by
              rw [ofNat64_toNat _ hordlen]
              exact decide_eq_true hltO
            rwa [← BitVec.ult_eq_decide] at h2
          have hbody := bfsOuterBody_ok F mL visL qL orderL
            n src head tail count v u w hget hgT wO hgetO hgOT
          match hrow : bfsRowFwd F mL visL qL n (w.signExtend 64)
              tail count 0 with
          | .error e =>
            have hcon : bfsOuterFwd (F + 1) mL visL qL orderL
                n head tail count v u = .error e := by
              simp only [bfsOuterFwd, hcond, hget, hgetO, hrow,
                ite_true, ite_false]
            rw [hcon] at hfwd
            cases hfwd
          | .ok (vis1, qL1, tail1, count1, u1) =>
            have hrowO := bfsRow_ok F mL visL qL (orderL.set head.toNat w)
              n src (head + 1) tail count (w.signExtend 64) 0 hmen hvislen
              hqllen _ _ _ _ _ hrow
            have hbev : evalStmtFuel F bfsOuterBody
                (mkBfsEnv mL visL qL orderL n src head tail count v u) =
                .ok (mkBfsEnv mL vis1 qL1 (orderL.set head.toNat w)
                  n src (head + 1) tail1 count1 (w.signExtend 64) u1,
                  .fellThrough) :=
              hbody.trans hrowO
            have hloop : evalStmtFuel (F + 1) bfsOuter
                (mkBfsEnv mL visL qL orderL n src head tail count v u) =
                evalStmtFuel F bfsOuter
                  (mkBfsEnv mL vis1 qL1 (orderL.set head.toNat w)
                    n src (head + 1) tail1 count1 (w.signExtend 64) u1) := by
              simp only [bfsOuter, evalStmtFuel, evalStmtSuccHandler,
                evalStmtWith, hcondT, hbev]
            have hfwd1 : bfsOuterFwd (F + 1) mL visL qL orderL
                n head tail count v u =
                bfsOuterFwd F mL vis1 qL1 (orderL.set head.toNat w)
                  n (head + 1) tail1 count1 (w.signExtend 64) u1 := by
              simp only [bfsOuterFwd, hcond, hget, hgetO, hrow,
                ite_true, ite_false]
            rw [hfwd1] at hfwd
            rw [hloop]
            have hlen := bfsRow_ok_len F mL visL qL n (w.signExtend 64)
              tail count 0 _ _ _ _ _ hrow
            have hvislen1 : vis1.length < 2 ^ 64 := by
              rw [hlen.1]; exact hvislen
            have hqllen1 : qL1.length < 2 ^ 64 := by
              rw [hlen.2]; exact hqllen
            have hordlen1 : (orderL.set head.toNat w).length < 2 ^ 64 := by
              rw [List.length_set]; exact hordlen
            exact ih vis1 qL1 (orderL.set head.toNat w) (head + 1) tail1
              count1 (w.signExtend 64) u1 hvislen1 hqllen1 hordlen1 vis' qL'
              orderL' head' tail' count' v' u' hfwd
    · have hfalse : (head != tail) = false :=
        Bool.eq_false_of_ne_true hcond
      have hcondE : evalExpr (.une (.var "head") (.var "tail"))
          (mkBfsEnv mL visL qL orderL n src head tail count v u) =
          .ok (.b false) := by
        have h := evalExpr_une_u64 _ _ _ _ _ hheadvar htailvar
        rw [hfalse] at h
        exact h
      have hev : evalStmtFuel (F + 1) bfsOuter
          (mkBfsEnv mL visL qL orderL n src head tail count v u) =
          .ok (mkBfsEnv mL visL qL orderL n src head tail count v u,
            .fellThrough) := by
        simp [bfsOuter, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcondE]
      have hfw : bfsOuterFwd (F + 1) mL visL qL orderL n head tail count v u =
          .ok (visL, qL, orderL, head, tail, count, v, u) := by
        simp only [bfsOuterFwd, hcond, Bool.false_eq_true, ite_true,
          ite_false]
      rw [hfw] at hfwd
      cases hfwd
      exact hev

/-- The queue drain at fuel `F`: evaluator agrees with the forward on
    every `.error` run. -/
theorem bfsOuter_err (F : Nat) (mL visL qL orderL : List (BitVec 32))
    (n src head tail count v u : BitVec 64)
    (hmen : mL.length < 2 ^ 64) (hvislen : visL.length < 2 ^ 64)
    (hqllen : qL.length < 2 ^ 64) (hordlen : orderL.length < 2 ^ 64)
    (e : Panic)
    (hfwd : bfsOuterFwd F mL visL qL orderL n head tail count v u =
      .error e) :
    evalStmtFuel F bfsOuter
      (mkBfsEnv mL visL qL orderL n src head tail count v u) =
      .error e := by
  induction F generalizing visL qL orderL head tail count v u with
  | zero =>
    have hheadvar : evalExpr (.var "head")
        (mkBfsEnv mL visL qL orderL n src head tail count v u) =
        .ok (.u64 head) :=
      evalExpr_var_hit _ _ _
        (mkBfsEnv_head mL visL qL orderL n src head tail count v u)
    have htailvar : evalExpr (.var "tail")
        (mkBfsEnv mL visL qL orderL n src head tail count v u) =
        .ok (.u64 tail) :=
      evalExpr_var_hit _ _ _
        (mkBfsEnv_tail mL visL qL orderL n src head tail count v u)
    by_cases hcond : head != tail
    · have hcondE : evalExpr (.une (.var "head") (.var "tail"))
          (mkBfsEnv mL visL qL orderL n src head tail count v u) =
          .ok (.b true) := by
        have h := evalExpr_une_u64 _ _ _ _ _ hheadvar htailvar
        rw [hcond] at h
        exact h
      have hev : evalStmtFuel 0 bfsOuter
          (mkBfsEnv mL visL qL orderL n src head tail count v u) =
          .error .AssertFail :=
        evalStmtFuel_zero_while_enter _ _ _ hcondE
      have hcon : bfsOuterFwd 0 mL visL qL orderL n head tail count v u =
          .error .AssertFail := by
        simp only [bfsOuterFwd, hcond, ite_true, ite_false]
      rw [hcon] at hfwd
      cases hfwd
      exact hev
    · have hfw : bfsOuterFwd 0 mL visL qL orderL n head tail count v u =
          .ok (visL, qL, orderL, head, tail, count, v, u) := by
        simp only [bfsOuterFwd, hcond, Bool.false_eq_true, ite_true,
          ite_false]
      rw [hfw] at hfwd
      cases hfwd
  | succ F ih =>
    have hheadvar : evalExpr (.var "head")
        (mkBfsEnv mL visL qL orderL n src head tail count v u) =
        .ok (.u64 head) :=
      evalExpr_var_hit _ _ _
        (mkBfsEnv_head mL visL qL orderL n src head tail count v u)
    have htailvar : evalExpr (.var "tail")
        (mkBfsEnv mL visL qL orderL n src head tail count v u) =
        .ok (.u64 tail) :=
      evalExpr_var_hit _ _ _
        (mkBfsEnv_tail mL visL qL orderL n src head tail count v u)
    by_cases hcond : head != tail
    · have hcondT : evalExpr (.une (.var "head") (.var "tail"))
          (mkBfsEnv mL visL qL orderL n src head tail count v u) =
          .ok (.b true) := by
        have h := evalExpr_une_u64 _ _ _ _ _ hheadvar htailvar
        rw [hcond] at h
        exact h
      match hget : qL[head.toNat]? with
      | none =>
        have hnot : ¬ head.toNat < qL.length := by
          intro hcon
          have hne : qL[head.toNat]? ≠ none := by
            rw [ne_eq, List.getElem?_eq_none_iff]
            omega
          exact hne hget
        have hgF : (head.ult (BitVec.ofNat 64 qL.length)) = false := by
          have h1 : ¬ head.toNat <
              (BitVec.ofNat 64 qL.length).toNat := by
            rw [ofNat64_toNat _ hqllen]
            exact hnot
          have h2 : decide (head.toNat <
              (BitVec.ofNat 64 qL.length).toNat) = false :=
            decide_eq_false h1
          rwa [← BitVec.ult_eq_decide] at h2
        have hcon : bfsOuterFwd (F + 1) mL visL qL orderL
            n head tail count v u = .error .AssertFail := by
          simp only [bfsOuterFwd, hcond, hget, ite_true, ite_false]
        have hbev : evalStmtFuel F bfsOuterBody
            (mkBfsEnv mL visL qL orderL n src head tail count v u) =
            .error .AssertFail :=
          bfsOuterBody_missQ F mL visL qL orderL
            n src head tail count v u hgF
        have hev : evalStmtFuel (F + 1) bfsOuter
            (mkBfsEnv mL visL qL orderL n src head tail count v u) =
            .error .AssertFail := by
          simp only [bfsOuter, evalStmtFuel, evalStmtSuccHandler,
            evalStmtWith, hcondT, hbev]
        rw [hcon] at hfwd
        cases hfwd
        exact hev
      | some w =>
        have hlt : head.toNat < qL.length :=
          bfsGetElem_some_lt hget
        have hgT : (head.ult (BitVec.ofNat 64 qL.length)) = true := by
          have h2 : decide (head.toNat <
              (BitVec.ofNat 64 qL.length).toNat) = true := by
            rw [ofNat64_toNat _ hqllen]
            exact decide_eq_true hlt
          rwa [← BitVec.ult_eq_decide] at h2
        match hgetO : orderL[head.toNat]? with
        | none =>
          have hcon : bfsOuterFwd (F + 1) mL visL qL orderL
              n head tail count v u = .error .AssertFail := by
            simp only [bfsOuterFwd, hcond, hget, hgetO, ite_true, ite_false]
          have hbev : evalStmtFuel F bfsOuterBody
              (mkBfsEnv mL visL qL orderL n src head tail count v u) =
              .error .AssertFail :=
            bfsOuterBody_missO F mL visL qL orderL
              n src head tail count v u w hget hgT hgetO hordlen
          have hev : evalStmtFuel (F + 1) bfsOuter
              (mkBfsEnv mL visL qL orderL n src head tail count v u) =
              .error .AssertFail := by
            simp only [bfsOuter, evalStmtFuel, evalStmtSuccHandler,
              evalStmtWith, hcondT, hbev]
          rw [hcon] at hfwd
          cases hfwd
          exact hev
        | some wO =>
          have hltO : head.toNat < orderL.length :=
            bfsGetElem_some_lt hgetO
          have hgOT : (head.ult
              (BitVec.ofNat 64 orderL.length)) = true := by
            have h2 : decide (head.toNat <
                (BitVec.ofNat 64 orderL.length).toNat) = true := by
              rw [ofNat64_toNat _ hordlen]
              exact decide_eq_true hltO
            rwa [← BitVec.ult_eq_decide] at h2
          have hbody := bfsOuterBody_ok F mL visL qL orderL
            n src head tail count v u w hget hgT wO hgetO hgOT
          match hrow : bfsRowFwd F mL visL qL n (w.signExtend 64)
              tail count 0 with
          | .error e' =>
            have hcon : bfsOuterFwd (F + 1) mL visL qL orderL
                n head tail count v u = .error e' := by
              simp only [bfsOuterFwd, hcond, hget, hgetO, hrow,
                ite_true, ite_false]
            have hrowE := bfsRow_err F mL visL qL (orderL.set head.toNat w)
              n src (head + 1) tail count (w.signExtend 64) 0 hmen hvislen
              hqllen _ hrow
            have hbev : evalStmtFuel F bfsOuterBody
                (mkBfsEnv mL visL qL orderL n src head tail count v u) =
                .error e' :=
              hbody.trans hrowE
            have hev : evalStmtFuel (F + 1) bfsOuter
                (mkBfsEnv mL visL qL orderL n src head tail count v u) =
                .error e' := by
              simp only [bfsOuter, evalStmtFuel, evalStmtSuccHandler,
                evalStmtWith, hcondT, hbev]
            rw [hcon] at hfwd
            cases hfwd
            exact hev
          | .ok (vis1, qL1, tail1, count1, u1) =>
            have hrowO := bfsRow_ok F mL visL qL (orderL.set head.toNat w)
              n src (head + 1) tail count (w.signExtend 64) 0 hmen hvislen
              hqllen _ _ _ _ _ hrow
            have hbev : evalStmtFuel F bfsOuterBody
                (mkBfsEnv mL visL qL orderL n src head tail count v u) =
                .ok (mkBfsEnv mL vis1 qL1 (orderL.set head.toNat w)
                  n src (head + 1) tail1 count1 (w.signExtend 64) u1,
                  .fellThrough) :=
              hbody.trans hrowO
            have hloop : evalStmtFuel (F + 1) bfsOuter
                (mkBfsEnv mL visL qL orderL n src head tail count v u) =
                evalStmtFuel F bfsOuter
                  (mkBfsEnv mL vis1 qL1 (orderL.set head.toNat w)
                    n src (head + 1) tail1 count1 (w.signExtend 64) u1) := by
              simp only [bfsOuter, evalStmtFuel, evalStmtSuccHandler,
                evalStmtWith, hcondT, hbev]
            have hfwd1 : bfsOuterFwd (F + 1) mL visL qL orderL
                n head tail count v u =
                bfsOuterFwd F mL vis1 qL1 (orderL.set head.toNat w)
                  n (head + 1) tail1 count1 (w.signExtend 64) u1 := by
              simp only [bfsOuterFwd, hcond, hget, hgetO, hrow,
                ite_true, ite_false]
            rw [hfwd1] at hfwd
            rw [hloop]
            have hlen := bfsRow_ok_len F mL visL qL n (w.signExtend 64)
              tail count 0 _ _ _ _ _ hrow
            have hvislen1 : vis1.length < 2 ^ 64 := by
              rw [hlen.1]; exact hvislen
            have hqllen1 : qL1.length < 2 ^ 64 := by
              rw [hlen.2]; exact hqllen
            have hordlen1 : (orderL.set head.toNat w).length < 2 ^ 64 := by
              rw [List.length_set]; exact hordlen
            exact ih vis1 qL1 (orderL.set head.toNat w) (head + 1) tail1
              count1 (w.signExtend 64) u1 hvislen1 hqllen1 hordlen1 hfwd
    · have hfw : bfsOuterFwd (F + 1) mL visL qL orderL n head tail count v u =
          .ok (visL, qL, orderL, head, tail, count, v, u) := by
        simp only [bfsOuterFwd, hcond, Bool.false_eq_true, ite_true,
          ite_false]
      rw [hfw] at hfwd
      cases hfwd

/-- Seed with both slots live: the two guarded stores plus the five
    cursor bindings (any fuel). -/
theorem bfsSeed_ok (F : Nat) (mL visL qL orderL : List (BitVec 32))
    (n src : BitVec 64)
    (hvislen : visL.length < 2 ^ 64) (hqllen : qL.length < 2 ^ 64)
    (vis1 qL1 : List (BitVec 32))
    (hfwd : bfsSeedFwd visL qL src = .ok (vis1, qL1)) :
    evalStmtFuel F bfsSeed
      [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
        ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
        ("n", .u64 n), ("src", .u64 src)] =
      .ok (mkBfsEnv mL vis1 qL1 orderL n src 0 1 1 0 0, .fellThrough) := by
  have hseed : bfsSeed =
      .seq (.if_ (.ult (.var "src") (.stdVecLen "vis"))
              (.vecSet "vis" (.var "src") (.lit (.i32 1)))
              .fail)
      (.seq (.if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "q"))
              (.vecSet "q" (.lit (.u64 (BitVec.ofNat 64 0)))
                (.i32ofU64 (.var "src")))
              .fail)
      (.seq (.let_ "head" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.seq (.let_ "tail" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      (.seq (.let_ "count" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      (.seq (.let_ "v" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.let_ "u" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))))))) := rfl
  match hvis : visL[src.toNat]? with
  | none =>
    have hcon : bfsSeedFwd visL qL src = .error .AssertFail := by
      simp only [bfsSeedFwd, hvis, ite_true, ite_false]
    rw [hcon] at hfwd
    cases hfwd
  | some w =>
    match hq : qL[(BitVec.ofNat 64 0).toNat]? with
    | none =>
      have hcon : bfsSeedFwd visL qL src = .error .AssertFail := by
        simp only [bfsSeedFwd, hvis, hq, ite_true, ite_false]
      rw [hcon] at hfwd
      cases hfwd
    | some wq =>
      have hcon : bfsSeedFwd visL qL src =
          .ok (visL.set src.toNat 1,
            qL.set 0 (BitVec.ofNat 32 src.toNat)) := by
        simp only [bfsSeedFwd, hvis, hq, ite_true, ite_false]
      rw [hcon] at hfwd
      cases hfwd
      have hsrc : evalExpr (.var "src")
          [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
            ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)] =
          .ok (.u64 src) :=
        evalExpr_var_hit _ _ _
          (by simp [envLookup,
            show ("src" : String) ≠ "m" by decide,
            show ("src" : String) ≠ "vis" by decide,
            show ("src" : String) ≠ "q" by decide,
            show ("src" : String) ≠ "order" by decide,
            show ("src" : String) ≠ "n" by decide])
      have hvislen0 : evalExpr (.stdVecLen "vis")
          [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
            ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)] =
          .ok (.u64 (BitVec.ofNat 64 visL.length)) :=
        evalExpr_stdVecLen_some "vis" _ _
          (by simp [envLookup,
            show ("vis" : String) ≠ "m" by decide])
      have hltv : src.toNat < visL.length := bfsGetElem_some_lt hvis
      have hguardV : evalExpr (.ult (.var "src") (.stdVecLen "vis"))
          [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
            ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)] =
          .ok (.b true) := by
        have h := evalExpr_ult_u64 _ _ _ _ _ hsrc hvislen0
        have h2 : decide (src.toNat <
            (BitVec.ofNat 64 visL.length).toNat) = true := by
          rw [ofNat64_toNat _ hvislen]
          exact decide_eq_true hltv
        have h3 : src.ult (BitVec.ofNat 64 visL.length) = true := by
          rwa [← BitVec.ult_eq_decide] at h2
        rw [h3] at h
        exact h
      have hx1 : evalExpr (.lit (.i32 (1 : BitVec 32)))
          [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
            ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)] =
          .ok (.i32 1) := by
        simp [evalExpr, litVal]
      have hstoreV := evalStmtFuel_vecSet F "vis" (.var "src")
        (.lit (.i32 (1 : BitVec 32)))
        [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
          ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
          ("n", .u64 n), ("src", .u64 src)]
        src 1 visL w
        [("m", .stdVecVal mL), ("vis", .stdVecVal (visL.set src.toNat 1)),
          ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
          ("n", .u64 n), ("src", .u64 src)]
        hsrc hx1
        (by simp [envLookup,
          show ("vis" : String) ≠ "m" by decide])
        hvis
        (by simp [envUpdate,
          show ("vis" : String) ≠ "m" by decide])
      have hqllen1 : evalExpr (.stdVecLen "q")
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)] =
          .ok (.u64 (BitVec.ofNat 64 qL.length)) :=
        evalExpr_stdVecLen_some "q" _ _
          (by simp [envLookup,
            show ("q" : String) ≠ "m" by decide,
            show ("q" : String) ≠ "vis" by decide])
      have hltq : (BitVec.ofNat 64 0).toNat < qL.length :=
        bfsGetElem_some_lt hq
      have hguardQ : evalExpr
          (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "q"))
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)] =
          .ok (.b true) := by
        have hlitz : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
            [("m", .stdVecVal mL),
              ("vis", .stdVecVal (visL.set src.toNat 1)),
              ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
              ("n", .u64 n), ("src", .u64 src)] =
            .ok (.u64 (BitVec.ofNat 64 0)) := by
          simp [evalExpr, litVal]
        have h := evalExpr_ult_u64 _ _ _ _ _ hlitz hqllen1
        have h2 : decide ((BitVec.ofNat 64 0).toNat <
            (BitVec.ofNat 64 qL.length).toNat) = true := by
          rw [ofNat64_toNat _ hqllen]
          exact decide_eq_true hltq
        have h3 : (BitVec.ofNat 64 0).ult
            (BitVec.ofNat 64 qL.length) = true := by
          rwa [← BitVec.ult_eq_decide] at h2
        rw [h3] at h
        exact h
      have hsrc1 : evalExpr (.var "src")
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)] =
          .ok (.u64 src) :=
        evalExpr_var_hit _ _ _
          (by simp [envLookup,
            show ("src" : String) ≠ "m" by decide,
            show ("src" : String) ≠ "vis" by decide,
            show ("src" : String) ≠ "q" by decide,
            show ("src" : String) ≠ "order" by decide,
            show ("src" : String) ≠ "n" by decide])
      have hwide := evalExpr_i32ofU64_ok _ _ _ hsrc1
      have hstoreQ := evalStmtFuel_vecSet F "q"
        (.lit (.u64 (BitVec.ofNat 64 0))) (.i32ofU64 (.var "src"))
        [("m", .stdVecVal mL),
          ("vis", .stdVecVal (visL.set src.toNat 1)),
          ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
          ("n", .u64 n), ("src", .u64 src)]
        (BitVec.ofNat 64 0) (BitVec.ofNat 32 src.toNat) qL wq
        [("m", .stdVecVal mL),
          ("vis", .stdVecVal (visL.set src.toNat 1)),
          ("q", .stdVecVal (qL.set (BitVec.ofNat 64 0).toNat
            (BitVec.ofNat 32 src.toNat))),
          ("order", .stdVecVal orderL),
          ("n", .u64 n), ("src", .u64 src)]
        (by simp [evalExpr, litVal]) hwide
        (by simp [envLookup,
          show ("q" : String) ≠ "m" by decide,
          show ("q" : String) ≠ "vis" by decide])
        hq
        (by simp [envUpdate,
          show ("q" : String) ≠ "m" by decide,
          show ("q" : String) ≠ "vis" by decide])
      have hlit1 : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("q", .stdVecVal (qL.set (BitVec.ofNat 64 0).toNat
              (BitVec.ofNat 32 src.toNat))),
            ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)] =
          .ok (.u64 (BitVec.ofNat 64 1)) := by
        simp [evalExpr, litVal]
      have hlit0 : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("q", .stdVecVal (qL.set (BitVec.ofNat 64 0).toNat
              (BitVec.ofNat 32 src.toNat))),
            ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)] =
          .ok (.u64 (BitVec.ofNat 64 0)) := by
        simp [evalExpr, litVal]
      have hletH := evalStmtFuel_let_ F "head" (.u 64)
        (.lit (.u64 (BitVec.ofNat 64 0)))
        [("m", .stdVecVal mL),
          ("vis", .stdVecVal (visL.set src.toNat 1)),
          ("q", .stdVecVal (qL.set (BitVec.ofNat 64 0).toNat
            (BitVec.ofNat 32 src.toNat))),
          ("order", .stdVecVal orderL),
          ("n", .u64 n), ("src", .u64 src)]
        _ hlit0
      have hletT := evalStmtFuel_let_ F "tail" (.u 64)
        (.lit (.u64 (BitVec.ofNat 64 1)))
        (envExtend
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("q", .stdVecVal (qL.set (BitVec.ofNat 64 0).toNat
              (BitVec.ofNat 32 src.toNat))),
            ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)]
          "head" (.u64 (BitVec.ofNat 64 0)))
        _ hlit1
      have hletC := evalStmtFuel_let_ F "count" (.u 64)
        (.lit (.u64 (BitVec.ofNat 64 1)))
        (envExtend (envExtend
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("q", .stdVecVal (qL.set (BitVec.ofNat 64 0).toNat
              (BitVec.ofNat 32 src.toNat))),
            ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)]
          "head" (.u64 (BitVec.ofNat 64 0)))
          "tail" (.u64 (BitVec.ofNat 64 1)))
        _ hlit1
      have hletV := evalStmtFuel_let_ F "v" (.u 64)
        (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend (envExtend (envExtend
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("q", .stdVecVal (qL.set (BitVec.ofNat 64 0).toNat
              (BitVec.ofNat 32 src.toNat))),
            ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)]
          "head" (.u64 (BitVec.ofNat 64 0)))
          "tail" (.u64 (BitVec.ofNat 64 1)))
          "count" (.u64 (BitVec.ofNat 64 1)))
        _ hlit0
      have hletU := evalStmtFuel_let_ F "u" (.u 64)
        (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend (envExtend (envExtend (envExtend
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("q", .stdVecVal (qL.set (BitVec.ofNat 64 0).toNat
              (BitVec.ofNat 32 src.toNat))),
            ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)]
          "head" (.u64 (BitVec.ofNat 64 0)))
          "tail" (.u64 (BitVec.ofNat 64 1)))
          "count" (.u64 (BitVec.ofNat 64 1)))
          "v" (.u64 (BitVec.ofNat 64 0)))
        _ hlit0
      have hfin : envExtend (envExtend (envExtend (envExtend (envExtend
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("q", .stdVecVal (qL.set (BitVec.ofNat 64 0).toNat
              (BitVec.ofNat 32 src.toNat))),
            ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)]
          "head" (.u64 (BitVec.ofNat 64 0)))
          "tail" (.u64 (BitVec.ofNat 64 1)))
          "count" (.u64 (BitVec.ofNat 64 1)))
          "v" (.u64 (BitVec.ofNat 64 0)))
          "u" (.u64 (BitVec.ofNat 64 0)) =
          mkBfsEnv mL (visL.set src.toNat 1)
            (qL.set (BitVec.ofNat 64 0).toNat
              (BitVec.ofNat 32 src.toNat)) orderL n src 0 1 1 0 0 := rfl
      have hgateV : evalStmtFuel F
          (.if_ (.ult (.var "src") (.stdVecLen "vis"))
            (.vecSet "vis" (.var "src") (.lit (.i32 1)))
            .fail)
          [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
            ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)] =
          .ok ([("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)],
            .fellThrough) :=
        (evalStmtFuel_if_true F _ _ _ _ hguardV).trans hstoreV
      have hgateQ : evalStmtFuel F
          (.if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "q"))
            (.vecSet "q" (.lit (.u64 (BitVec.ofNat 64 0)))
              (.i32ofU64 (.var "src")))
            .fail)
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)] =
          .ok ([("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("q", .stdVecVal (qL.set (BitVec.ofNat 64 0).toNat
              (BitVec.ofNat 32 src.toNat))),
            ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)], .fellThrough) :=
        (evalStmtFuel_if_true F _ _ _ _ hguardQ).trans hstoreQ
      have hletU' : evalStmtFuel F
          (.let_ "u" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
          (envExtend (envExtend (envExtend (envExtend
            [("m", .stdVecVal mL),
              ("vis", .stdVecVal (visL.set src.toNat 1)),
              ("q", .stdVecVal (qL.set (BitVec.ofNat 64 0).toNat
                (BitVec.ofNat 32 src.toNat))),
              ("order", .stdVecVal orderL),
              ("n", .u64 n), ("src", .u64 src)]
            "head" (.u64 (BitVec.ofNat 64 0)))
            "tail" (.u64 (BitVec.ofNat 64 1)))
            "count" (.u64 (BitVec.ofNat 64 1)))
            "v" (.u64 (BitVec.ofNat 64 0))) =
          .ok (mkBfsEnv mL (visL.set src.toNat 1)
            (qL.set (BitVec.ofNat 64 0).toNat
              (BitVec.ofNat 32 src.toNat)) orderL n src 0 1 1 0 0,
            .fellThrough) := by
        rw [← hfin]
        exact hletU
      rw [hseed]
      exact (evalStmtFuel_seq_fallthrough F _ _ _ _ hgateV).trans
        ((evalStmtFuel_seq_fallthrough F _ _ _ _ hgateQ).trans
        ((evalStmtFuel_seq_fallthrough F _ _ _ _ hletH).trans
        ((evalStmtFuel_seq_fallthrough F _ _ _ _ hletT).trans
        ((evalStmtFuel_seq_fallthrough F _ _ _ _ hletC).trans
        ((evalStmtFuel_seq_fallthrough F _ _ _ _ hletV).trans
          hletU')))))

/-- Seed with a dead slot aborts loudly (any fuel). -/
theorem bfsSeed_err (F : Nat) (mL visL qL orderL : List (BitVec 32))
    (n src : BitVec 64)
    (hvislen : visL.length < 2 ^ 64) (hqllen : qL.length < 2 ^ 64)
    (e : Panic)
    (hfwd : bfsSeedFwd visL qL src = .error e) :
    evalStmtFuel F bfsSeed
      [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
        ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
        ("n", .u64 n), ("src", .u64 src)] =
      .error e := by
  have hseed : bfsSeed =
      .seq (.if_ (.ult (.var "src") (.stdVecLen "vis"))
              (.vecSet "vis" (.var "src") (.lit (.i32 1)))
              .fail)
      (.seq (.if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "q"))
              (.vecSet "q" (.lit (.u64 (BitVec.ofNat 64 0)))
                (.i32ofU64 (.var "src")))
              .fail)
      (.seq (.let_ "head" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.seq (.let_ "tail" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      (.seq (.let_ "count" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      (.seq (.let_ "v" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.let_ "u" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))))))) := rfl
  have hsrc : evalExpr (.var "src")
      [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
        ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
        ("n", .u64 n), ("src", .u64 src)] =
      .ok (.u64 src) :=
    evalExpr_var_hit _ _ _
      (by simp [envLookup,
        show ("src" : String) ≠ "m" by decide,
        show ("src" : String) ≠ "vis" by decide,
        show ("src" : String) ≠ "q" by decide,
        show ("src" : String) ≠ "order" by decide,
        show ("src" : String) ≠ "n" by decide])
  have hvislen0 : evalExpr (.stdVecLen "vis")
      [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
        ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
        ("n", .u64 n), ("src", .u64 src)] =
      .ok (.u64 (BitVec.ofNat 64 visL.length)) :=
    evalExpr_stdVecLen_some "vis" _ _
      (by simp [envLookup,
        show ("vis" : String) ≠ "m" by decide])
  match hvis : visL[src.toNat]? with
  | none =>
    have hnot : ¬ src.toNat < visL.length := by
      intro hcon
      have hne : visL[src.toNat]? ≠ none := by
        rw [ne_eq, List.getElem?_eq_none_iff]
        omega
      exact hne hvis
    have hultF : src.ult (BitVec.ofNat 64 visL.length) = false := by
      have h1 : ¬ src.toNat <
          (BitVec.ofNat 64 visL.length).toNat := by
        rw [ofNat64_toNat _ hvislen]
        exact hnot
      have h2 : decide (src.toNat <
          (BitVec.ofNat 64 visL.length).toNat) = false :=
        decide_eq_false h1
      rwa [← BitVec.ult_eq_decide] at h2
    have hguardV : evalExpr (.ult (.var "src") (.stdVecLen "vis"))
        [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
          ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
          ("n", .u64 n), ("src", .u64 src)] =
        .ok (.b false) := by
      have h := evalExpr_ult_u64 _ _ _ _ _ hsrc hvislen0
      rw [hultF] at h
      exact h
    have hcon : bfsSeedFwd visL qL src = .error .AssertFail := by
      simp only [bfsSeedFwd, hvis, ite_true, ite_false]
    have hev : evalStmtFuel F bfsSeed
        [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
          ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
          ("n", .u64 n), ("src", .u64 src)] =
        .error .AssertFail := by
      rw [hseed]
      exact evalStmtFuel_seq_err F _
        (.seq (.if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0)))
                (.stdVecLen "q"))
                (.vecSet "q" (.lit (.u64 (BitVec.ofNat 64 0)))
                  (.i32ofU64 (.var "src")))
                .fail)
        (.seq (.let_ "head" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.seq (.let_ "tail" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
        (.seq (.let_ "count" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
        (.seq (.let_ "v" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.let_ "u" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))))))) _ _
        ((evalStmtFuel_if_false F _ _ _ _ hguardV).trans
          (evalStmtFuel_fail F _))
    rw [hcon] at hfwd
    cases hfwd
    exact hev
  | some w =>
    match hq : qL[(BitVec.ofNat 64 0).toNat]? with
    | none =>
      have hcon : bfsSeedFwd visL qL src = .error .AssertFail := by
        simp only [bfsSeedFwd, hvis, hq, ite_true, ite_false]
      have hguardV : evalExpr (.ult (.var "src") (.stdVecLen "vis"))
          [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
            ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)] =
          .ok (.b true) := by
        have hltv : src.toNat < visL.length := bfsGetElem_some_lt hvis
        have h := evalExpr_ult_u64 _ _ _ _ _ hsrc hvislen0
        have h2 : decide (src.toNat <
            (BitVec.ofNat 64 visL.length).toNat) = true := by
          rw [ofNat64_toNat _ hvislen]
          exact decide_eq_true hltv
        have h3 : src.ult (BitVec.ofNat 64 visL.length) = true := by
          rwa [← BitVec.ult_eq_decide] at h2
        rw [h3] at h
        exact h
      have hx1 : evalExpr (.lit (.i32 (1 : BitVec 32)))
          [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
            ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)] =
          .ok (.i32 1) := by
        simp [evalExpr, litVal]
      have hstoreV := evalStmtFuel_vecSet F "vis" (.var "src")
        (.lit (.i32 (1 : BitVec 32)))
        [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
          ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
          ("n", .u64 n), ("src", .u64 src)]
        src 1 visL w
        [("m", .stdVecVal mL), ("vis", .stdVecVal (visL.set src.toNat 1)),
          ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
          ("n", .u64 n), ("src", .u64 src)]
        hsrc hx1
        (by simp [envLookup,
          show ("vis" : String) ≠ "m" by decide])
        hvis
        (by simp [envUpdate,
          show ("vis" : String) ≠ "m" by decide])
      have hnot : ¬ (BitVec.ofNat 64 0).toNat < qL.length := by
        intro hcon
        have hne : qL[(BitVec.ofNat 64 0).toNat]? ≠ none := by
          rw [ne_eq, List.getElem?_eq_none_iff]
          omega
        exact hne hq
      have hultF : (BitVec.ofNat 64 0).ult
          (BitVec.ofNat 64 qL.length) = false := by
        have h1 : ¬ (BitVec.ofNat 64 0).toNat <
            (BitVec.ofNat 64 qL.length).toNat := by
          rw [ofNat64_toNat _ hqllen]
          exact hnot
        have h2 : decide ((BitVec.ofNat 64 0).toNat <
            (BitVec.ofNat 64 qL.length).toNat) = false :=
          decide_eq_false h1
        rwa [← BitVec.ult_eq_decide] at h2
      have hqllen1 : evalExpr (.stdVecLen "q")
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)] =
          .ok (.u64 (BitVec.ofNat 64 qL.length)) :=
        evalExpr_stdVecLen_some "q" _ _
          (by simp [envLookup,
            show ("q" : String) ≠ "m" by decide,
            show ("q" : String) ≠ "vis" by decide])
      have hlitz : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)] =
          .ok (.u64 (BitVec.ofNat 64 0)) := by
        simp [evalExpr, litVal]
      have hguardQ : evalExpr
          (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "q"))
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)] =
          .ok (.b false) := by
        have h := evalExpr_ult_u64 _ _ _ _ _ hlitz hqllen1
        rw [hultF] at h
        exact h
      have hgateV : evalStmtFuel F
          (.if_ (.ult (.var "src") (.stdVecLen "vis"))
            (.vecSet "vis" (.var "src") (.lit (.i32 1)))
            .fail)
          [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
            ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)] =
          .ok ([("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)],
            .fellThrough) :=
        (evalStmtFuel_if_true F _ _ _ _ hguardV).trans hstoreV
      have hev : evalStmtFuel F bfsSeed
          [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
            ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)] =
          .error .AssertFail := by
        rw [hseed]
        exact (evalStmtFuel_seq_fallthrough F _ _ _ _ hgateV).trans
          (evalStmtFuel_seq_err F _
            (.seq (.let_ "head" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
            (.seq (.let_ "tail" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
            (.seq (.let_ "count" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
            (.seq (.let_ "v" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
            (.let_ "u" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0)))))))) _ _
            ((evalStmtFuel_if_false F _ _ _ _ hguardQ).trans
              (evalStmtFuel_fail F _)))
      rw [hcon] at hfwd
      cases hfwd
      exact hev
    | some wq =>
      have hcon : bfsSeedFwd visL qL src =
          .ok (visL.set src.toNat 1,
            qL.set 0 (BitVec.ofNat 32 src.toNat)) := by
        simp only [bfsSeedFwd, hvis, hq, ite_true, ite_false]
      rw [hcon] at hfwd
      cases hfwd

/-- Seed length preservation (the stores are `vecSet`s). -/
theorem bfsSeed_ok_len (visL qL : List (BitVec 32)) (src : BitVec 64)
    (vis1 qL1 : List (BitVec 32))
    (hfwd : bfsSeedFwd visL qL src = .ok (vis1, qL1)) :
    vis1.length = visL.length ∧ qL1.length = qL.length := by
  match hvis : visL[src.toNat]? with
  | none =>
    have hcon : bfsSeedFwd visL qL src = .error .AssertFail := by
      simp only [bfsSeedFwd, hvis, ite_true, ite_false]
    rw [hcon] at hfwd
    cases hfwd
  | some _ =>
    match hq : qL[(BitVec.ofNat 64 0).toNat]? with
    | none =>
      have hcon : bfsSeedFwd visL qL src = .error .AssertFail := by
        simp only [bfsSeedFwd, hvis, hq, ite_true, ite_false]
      rw [hcon] at hfwd
      cases hfwd
    | some _ =>
      have hcon : bfsSeedFwd visL qL src =
          .ok (visL.set src.toNat 1,
            qL.set 0 (BitVec.ofNat 32 src.toNat)) := by
        simp only [bfsSeedFwd, hvis, hq, ite_true, ite_false]
      rw [hcon] at hfwd
      cases hfwd
      simp [List.length_set]

/-- Whole-function correctness: the evaluator agrees with the forward
    mirror on every input (seed, drain, return). -/
theorem evalFuncFuel_bfs (F : Nat) (mL visL qL orderL : List (BitVec 32))
    (n src : BitVec 64)
    (hmen : mL.length < 2 ^ 64) (hvislen : visL.length < 2 ^ 64)
    (hqllen : qL.length < 2 ^ 64) (hordlen : orderL.length < 2 ^ 64) :
    evalFuncFuel F bfsOrderFunc
      [.stdVecVal mL, .stdVecVal visL, .stdVecVal qL,
        .stdVecVal orderL, .u64 n, .u64 src] =
      bfsFwd F mL visL qL orderL n src := by
  have hbind : bindArgs bfsOrderFunc.args
      [.stdVecVal mL, .stdVecVal visL, .stdVecVal qL,
        .stdVecVal orderL, .u64 n, .u64 src] =
      some [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
        ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
        ("n", .u64 n), ("src", .u64 src)] := rfl
  have hfunc : bfsOrderFunc.body =
      .seq bfsSeed
        (.seq bfsOuter (.return_ (.var "count"))) := rfl
  match hseed : bfsSeedFwd visL qL src with
  | .error e =>
    have hseedE := bfsSeed_err F mL visL qL orderL n src hvislen hqllen
      _ hseed
    have hstmt : evalStmtFuel F bfsOrderFunc.body
        [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
          ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
          ("n", .u64 n), ("src", .u64 src)] =
        .error e := by
      rw [hfunc]
      exact evalStmtFuel_seq_err F _
        (.seq bfsOuter (.return_ (.var "count"))) _ _ hseedE
    simp only [evalFuncFuel, hbind, hstmt, bfsFwd, hseed]
  | .ok (vis1, qL1) =>
    have hseedO := bfsSeed_ok F mL visL qL orderL n src hvislen hqllen
      _ _ hseed
    have hlen := bfsSeed_ok_len visL qL src _ _ hseed
    have hvislen1 : vis1.length < 2 ^ 64 := by
      rw [hlen.1]; exact hvislen
    have hqllen1 : qL1.length < 2 ^ 64 := by
      rw [hlen.2]; exact hqllen
    match houter : bfsOuterFwd F mL vis1 qL1 orderL n 0 1 1 0 0 with
    | .error e =>
      have houterE := bfsOuter_err F mL vis1 qL1 orderL n src 0 1 1 0 0
        hmen hvislen1 hqllen1 hordlen _ houter
      have hstmt : evalStmtFuel F bfsOrderFunc.body
          [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
            ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)] =
          .error e := by
        rw [hfunc]
        exact (evalStmtFuel_seq_fallthrough F _ _ _ _ hseedO).trans
          (evalStmtFuel_seq_err F _ (.return_ (.var "count")) _ _ houterE)
      simp only [evalFuncFuel, hbind, hstmt, bfsFwd, hseed, houter]
    | .ok (vis2, qL2, order2, head2, tail2, count2, v2, u2) =>
      have houterO := bfsOuter_ok F mL vis1 qL1 orderL n src 0 1 1 0 0
        hmen hvislen1 hqllen1 hordlen _ _ _ _ _ _ _ _ houter
      have hcount : evalExpr (.var "count")
          (mkBfsEnv mL vis2 qL2 order2 n src head2 tail2 count2 v2 u2) =
          .ok (.u64 count2) :=
        evalExpr_var_hit _ _ _
          (mkBfsEnv_count mL vis2 qL2 order2
            n src head2 tail2 count2 v2 u2)
      have hret := evalStmtFuel_return F _ _ _ hcount
      have hstmt : evalStmtFuel F bfsOrderFunc.body
          [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
            ("q", .stdVecVal qL), ("order", .stdVecVal orderL),
            ("n", .u64 n), ("src", .u64 src)] =
          .ok (mkBfsEnv mL vis2 qL2 order2 n src head2 tail2 count2 v2 u2,
            .returned (.u64 count2)) := by
        rw [hfunc]
        exact (evalStmtFuel_seq_fallthrough F _ _ _ _ hseedO).trans
          ((evalStmtFuel_seq_fallthrough F _ _ _ _ houterO).trans hret)
      simp only [evalFuncFuel, hbind, hstmt, bfsFwd, hseed, houter]
