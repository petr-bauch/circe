/-
Circe.Emit.VecDfs — G5a iterative DFS over a flat row-major matrix:
the `dfs_reachable` entry.

The corpus (`tests/cpp/dfs_reachable.cpp`: const-matrix `m`,
mut-visited `vis`, mut caller stack `st`, `u64` dimension `n` and
source `src`, `u64` reachable-count out) captures the entry + the
const/mut `at()` composers + `_M_range_check` + both `operator[]`
+ `size`. The entry functionalizes to a fused seed (visited mark
plus stack push through the mut-`at()` checked writes behind
their `ult` guards, the `at()`-throw precedent) plus the outer
stack-drain `while_` (`top != 0`) around the inner row-scan
`while_` (`u < n`, the G1 loop shape): each row scans
`m.at(v * n + u)` (the G2 index computation) and pushes every
unvisited non-zero neighbor (gate one `m.at(v*n+u) != 0`, gate
two `vis.at(u) == 0`), counting each first visit. Every vector op
sits behind its own fused `ult` guard (seed-visited, seed-stack,
pop-read, matrix-read, visited-read, stack-store); each miss is
the `at()`-throw `AssertFail`, including wrapping index
computations that land out of range. The cursor and count
advances are pure wrapping `uadd`/`usub`; the pop-read widens
through `u64ofI32` (C integer promotion) and the two stores
narrow through `i32ofU64` (the V2 cast precedent).

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

/-! ## G5a: `dfs_reachable` entry -/

/-- Mangled name of the DFS entry. -/
def dfsName : String :=
  "_Z13dfs_reachableRKSt6vectorIiSaIiEERS1_S4_mm"

/-- The G2 row index (`v * n + u`, CIR order). -/
def dfsRowIdx : CExpr :=
  .uadd (.umul (.var "v") (.var "n")) (.var "u")

/-- The fused entry seed: guarded visited mark plus guarded stack
    push of the source (each miss is the `at()`-throw). -/
def dfsSeed : CStmt :=
  .seq (.if_ (.ult (.var "src") (.stdVecLen "vis"))
          (.vecSet "vis" (.var "src") (.lit (.i32 1)))
          .fail)
  (.seq (.if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "st"))
          (.vecSet "st" (.lit (.u64 (BitVec.ofNat 64 0)))
            (.i32ofU64 (.var "src")))
          .fail)
  (.seq (.let_ "top" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
  (.seq (.let_ "count" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
  (.seq (.let_ "v" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
  (.let_ "u" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))))))

/-- One inner push: guarded stack store plus the wrapping cursor
    and count advances. -/
def dfsPush : CStmt :=
  .seq (.if_ (.ult (.var "top") (.stdVecLen "st"))
          (.vecSet "st" (.var "top") (.i32ofU64 (.var "u")))
          .fail)
  (.seq (.assign "top" (.uadd (.var "top")
            (.lit (.u64 (BitVec.ofNat 64 1)))))
    (.assign "count" (.uadd (.var "count")
      (.lit (.u64 (BitVec.ofNat 64 1))))))

/-- One row-scan iteration: the matrix guard, the two gates, the
    push, and the `u` advance (which always runs). -/
def dfsInnerBody : CStmt :=
  .seq (.if_ (.ult dfsRowIdx (.stdVecLen "m"))
          (.if_ (.une (.stdVecAt "m" dfsRowIdx)
                  (.lit (.i32 (BitVec.ofNat 32 0))))
            (.if_ (.ult (.var "u") (.stdVecLen "vis"))
              (.if_ (.ueq (.stdVecAt "vis" (.var "u"))
                      (.lit (.i32 (BitVec.ofNat 32 0))))
                (.seq (.vecSet "vis" (.var "u")
                         (.lit (.i32 (BitVec.ofNat 32 1))))
                  dfsPush)
                .skip)
              .fail)
            .skip)
          .fail)
       (.assign "u" (.uadd (.var "u")
         (.lit (.u64 (BitVec.ofNat 64 1)))))

/-- The row scan: `u` runs `0..n`. -/
def dfsInner : CStmt :=
  .while_ (.ult (.var "u") (.var "n")) dfsInnerBody

/-- One drain iteration: pop, guarded widening read, `u` reset,
    then the row scan. -/
def dfsOuterBody : CStmt :=
  .seq (.assign "top" (.usub (.var "top")
          (.lit (.u64 (BitVec.ofNat 64 1)))))
  (.seq (.if_ (.ult (.var "top") (.stdVecLen "st"))
          (.assign "v" (.u64ofI32 (.stdVecAt "st" (.var "top"))))
          .fail)
  (.seq (.assign "u" (.lit (.u64 (BitVec.ofNat 64 0))))
    dfsInner))

/-- The stack drain: `top != 0`. -/
def dfsOuter : CStmt :=
  .while_ (.une (.var "top") (.lit (.u64 (BitVec.ofNat 64 0))))
    dfsOuterBody

/-- Canonical CoreIR for `dfs_reachable`: the fused seed, the
    nested drain, and the count return. -/
def dfsFunc : Func :=
  ⟨dfsName,
   [{ name := "m", ty := stdVecObjTy, role := .sharedBorrow },
    { name := "vis", ty := stdVecObjTy, role := .mutBorrow 0 },
    { name := "st", ty := stdVecObjTy, role := .mutBorrow 0 },
    { name := "n", ty := .u 64, role := .owned },
    { name := "src", ty := .u 64, role := .owned }],
   .u 64,
   (.seq dfsSeed (.seq dfsOuter (.return_ (.var "count"))))⟩

/-- Drain environment: three word lists, dimension, source, and the
    four cursor words. -/
def mkDfsEnv (mL visL stL : List (BitVec 32))
    (n src top count v u : BitVec 64) : Env :=
  [("u", .u64 u), ("v", .u64 v),
   ("count", .u64 count), ("top", .u64 top),
   ("m", .stdVecVal mL), ("vis", .stdVecVal visL),
   ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)]

theorem mkDfsEnv_m (mL visL stL : List (BitVec 32))
    (n src top count v u : BitVec 64) :
    envLookup (mkDfsEnv mL visL stL n src top count v u) "m" =
      some (.stdVecVal mL) := by
  simp [mkDfsEnv, envLookup,
    show ("u" : String) ≠ "m" by decide,
    show ("v" : String) ≠ "m" by decide,
    show ("count" : String) ≠ "m" by decide,
    show ("top" : String) ≠ "m" by decide]

theorem mkDfsEnv_vis (mL visL stL : List (BitVec 32))
    (n src top count v u : BitVec 64) :
    envLookup (mkDfsEnv mL visL stL n src top count v u) "vis" =
      some (.stdVecVal visL) := by
  simp [mkDfsEnv, envLookup,
    show ("u" : String) ≠ "vis" by decide,
    show ("v" : String) ≠ "vis" by decide,
    show ("count" : String) ≠ "vis" by decide,
    show ("top" : String) ≠ "vis" by decide,
    show ("m" : String) ≠ "vis" by decide]

theorem mkDfsEnv_st (mL visL stL : List (BitVec 32))
    (n src top count v u : BitVec 64) :
    envLookup (mkDfsEnv mL visL stL n src top count v u) "st" =
      some (.stdVecVal stL) := by
  simp [mkDfsEnv, envLookup,
    show ("u" : String) ≠ "st" by decide,
    show ("v" : String) ≠ "st" by decide,
    show ("count" : String) ≠ "st" by decide,
    show ("top" : String) ≠ "st" by decide,
    show ("m" : String) ≠ "st" by decide,
    show ("vis" : String) ≠ "st" by decide]

theorem mkDfsEnv_n (mL visL stL : List (BitVec 32))
    (n src top count v u : BitVec 64) :
    envLookup (mkDfsEnv mL visL stL n src top count v u) "n" =
      some (.u64 n) := by
  simp [mkDfsEnv, envLookup,
    show ("u" : String) ≠ "n" by decide,
    show ("v" : String) ≠ "n" by decide,
    show ("count" : String) ≠ "n" by decide,
    show ("top" : String) ≠ "n" by decide,
    show ("m" : String) ≠ "n" by decide,
    show ("vis" : String) ≠ "n" by decide,
    show ("st" : String) ≠ "n" by decide]

theorem mkDfsEnv_src (mL visL stL : List (BitVec 32))
    (n src top count v u : BitVec 64) :
    envLookup (mkDfsEnv mL visL stL n src top count v u) "src" =
      some (.u64 src) := by
  simp [mkDfsEnv, envLookup,
    show ("u" : String) ≠ "src" by decide,
    show ("v" : String) ≠ "src" by decide,
    show ("count" : String) ≠ "src" by decide,
    show ("top" : String) ≠ "src" by decide,
    show ("m" : String) ≠ "src" by decide,
    show ("vis" : String) ≠ "src" by decide,
    show ("st" : String) ≠ "src" by decide,
    show ("n" : String) ≠ "src" by decide]

theorem mkDfsEnv_top (mL visL stL : List (BitVec 32))
    (n src top count v u : BitVec 64) :
    envLookup (mkDfsEnv mL visL stL n src top count v u) "top" =
      some (.u64 top) := by
  simp [mkDfsEnv, envLookup,
    show ("u" : String) ≠ "top" by decide,
    show ("v" : String) ≠ "top" by decide,
    show ("count" : String) ≠ "top" by decide]

theorem mkDfsEnv_count (mL visL stL : List (BitVec 32))
    (n src top count v u : BitVec 64) :
    envLookup (mkDfsEnv mL visL stL n src top count v u) "count" =
      some (.u64 count) := by
  simp [mkDfsEnv, envLookup,
    show ("u" : String) ≠ "count" by decide,
    show ("v" : String) ≠ "count" by decide]

theorem mkDfsEnv_v (mL visL stL : List (BitVec 32))
    (n src top count v u : BitVec 64) :
    envLookup (mkDfsEnv mL visL stL n src top count v u) "v" =
      some (.u64 v) := by
  simp [mkDfsEnv, envLookup,
    show ("u" : String) ≠ "v" by decide]

theorem mkDfsEnv_u (mL visL stL : List (BitVec 32))
    (n src top count v u : BitVec 64) :
    envLookup (mkDfsEnv mL visL stL n src top count v u) "u" =
      some (.u64 u) := by
  simp [mkDfsEnv, envLookup]

/-- Fuel-threaded row-scan forward: mirrors `dfsInner` iteration for
    iteration (same fuel, same guard order). Zero fuel exits cleanly
    on a spent bound and aborts loudly on a live one — the S3a fuel
    contract. -/
def dfsRowFwd (F : Nat) (mL visL stL : List (BitVec 32))
    (n v top count u : BitVec 64) :
    Result (List (BitVec 32) × List (BitVec 32) × BitVec 64 × BitVec 64 ×
      BitVec 64) :=
  match F with
  | 0 =>
    if u.ult n then .error .AssertFail
    else .ok (visL, stL, top, count, u)
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
              match stL[top.toNat]? with
              | none => .error .AssertFail
              | some _ =>
                dfsRowFwd F mL (visL.set u.toNat 1)
                  (stL.set top.toNat (BitVec.ofNat 32 u.toNat))
                  n v (top + 1) (count + 1) (u + 1)
            else dfsRowFwd F mL visL stL n v top count (u + 1)
        else dfsRowFwd F mL visL stL n v top count (u + 1)
    else .ok (visL, stL, top, count, u)

/-- Fuel-threaded drain forward: mirrors `dfsOuter` (same fuel;
    the row scan runs at predecessor fuel, exactly as the
    successor handler threads it). -/
def dfsOuterFwd (F : Nat) (mL visL stL : List (BitVec 32))
    (n top count v u : BitVec 64) :
    Result (List (BitVec 32) × List (BitVec 32) × BitVec 64 × BitVec 64 ×
      BitVec 64 × BitVec 64) :=
  match F with
  | 0 =>
    if top != (BitVec.ofNat 64 0) then .error .AssertFail
    else .ok (visL, stL, top, count, v, u)
  | F + 1 =>
    if top != (BitVec.ofNat 64 0) then
      let top1 := top - 1
      match stL[top1.toNat]? with
      | none => .error .AssertFail
      | some w =>
        match dfsRowFwd F mL visL stL n (w.signExtend 64) top1 count 0 with
        | .error e => .error e
        | .ok (vis', st', top', count', u') =>
          dfsOuterFwd F mL vis' st' n top' count' (w.signExtend 64) u'
    else .ok (visL, stL, top, count, v, u)

/-- Seed mirror: the two guarded stores (each miss is loud). -/
def dfsSeedFwd (visL stL : List (BitVec 32)) (src : BitVec 64) :
    Result (List (BitVec 32) × List (BitVec 32)) :=
  match visL[src.toNat]? with
  | none => .error .AssertFail
  | some _ =>
    match stL[(BitVec.ofNat 64 0).toNat]? with
    | none => .error .AssertFail
    | some _ =>
      .ok (visL.set src.toNat 1,
        stL.set 0 (BitVec.ofNat 32 src.toNat))

/-- Entry mirror: seed, then the drain; the count is the return. -/
def dfsFwd (F : Nat) (mL visL stL : List (BitVec 32))
    (n src : BitVec 64) : Result Value :=
  match dfsSeedFwd visL stL src with
  | .error e => .error e
  | .ok (vis1, st1) =>
    match dfsOuterFwd F mL vis1 st1 n 1 1 0 0 with
    | .error e => .error e
    | .ok (_, _, _, count, _, _) => .ok (.u64 count)

/-- The row index evaluates to the wrapped `u64` (G2 pattern). -/
theorem dfsRowIdx_eval (mL visL stL : List (BitVec 32))
    (n src top count v u : BitVec 64) :
    evalExpr dfsRowIdx (mkDfsEnv mL visL stL n src top count v u) =
      .ok (.u64 (v * n + u)) := by
  have hn := mkDfsEnv_n mL visL stL n src top count v u
  have hv := mkDfsEnv_v mL visL stL n src top count v u
  have hu := mkDfsEnv_u mL visL stL n src top count v u
  have hvv : evalExpr (.var "v") (mkDfsEnv mL visL stL n src top count v u) =
      .ok (.u64 v) :=
    evalExpr_var_hit _ _ _ hv
  have hvn : evalExpr (.var "n") (mkDfsEnv mL visL stL n src top count v u) =
      .ok (.u64 n) :=
    evalExpr_var_hit _ _ _ hn
  have hvu : evalExpr (.var "u") (mkDfsEnv mL visL stL n src top count v u) =
      .ok (.u64 u) :=
    evalExpr_var_hit _ _ _ hu
  have hmul : evalExpr (.umul (.var "v") (.var "n"))
      (mkDfsEnv mL visL stL n src top count v u) = .ok (.u64 (v * n)) :=
    evalExpr_umul_u64 _ _ _ _ _ hvv hvn
  have := evalExpr_uadd_u64 _ _ _ _ _ hmul hvu
  simpa [dfsRowIdx] using this

/-- Seed visited guard: `src < vis.length`. -/
theorem dfsSeedVisGuard_eval (mL visL stL : List (BitVec 32))
    (n src top count v u : BitVec 64) (hlen64 : visL.length < 2 ^ 64) :
    evalExpr (.ult (.var "src") (.stdVecLen "vis"))
      (mkDfsEnv mL visL stL n src top count v u) =
      .ok (.b (src.ult (BitVec.ofNat 64 visL.length))) := by
  have hsrc : evalExpr (.var "src") (mkDfsEnv mL visL stL n src top count v u) =
      .ok (.u64 src) :=
    evalExpr_var_hit _ _ _ (mkDfsEnv_src mL visL stL n src top count v u)
  have hlen : evalExpr (.stdVecLen "vis")
      (mkDfsEnv mL visL stL n src top count v u) =
      .ok (.u64 (BitVec.ofNat 64 visL.length)) :=
    evalExpr_stdVecLen_some "vis" _ visL
      (mkDfsEnv_vis mL visL stL n src top count v u)
  exact evalExpr_ult_u64 _ _ _ _ _ hsrc hlen

/-- Seed stack guard: `0 < st.length`. -/
theorem dfsSeedStGuard_eval (mL visL stL : List (BitVec 32))
    (n src top count v u : BitVec 64) :
    evalExpr (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "st"))
      (mkDfsEnv mL visL stL n src top count v u) =
      .ok (.b ((BitVec.ofNat 64 0).ult (BitVec.ofNat 64 stL.length))) := by
  have hlen : evalExpr (.stdVecLen "st")
      (mkDfsEnv mL visL stL n src top count v u) =
      .ok (.u64 (BitVec.ofNat 64 stL.length)) :=
    evalExpr_stdVecLen_some "st" _ stL
      (mkDfsEnv_st mL visL stL n src top count v u)
  have hlit : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (mkDfsEnv mL visL stL n src top count v u) =
      .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  exact evalExpr_ult_u64 _ _ _ _ _ hlit hlen

/-- Bridge: a true `ult` guard gives an in-bounds `getElem?`. -/
theorem ultGuard_inBounds {x : BitVec 64} {l : List (BitVec 32)}
    (hlen : l.length < 2 ^ 64)
    (h : x.ult (BitVec.ofNat 64 l.length) = true) :
    x.toNat < l.length := by
  have h1 : decide (x.toNat < (BitVec.ofNat 64 l.length).toNat) = true := by
    rw [← BitVec.ult_eq_decide]; exact h
  have h2 := of_decide_eq_true h1
  rw [ofNat64_toNat _ hlen] at h2
  exact h2

/-- One inner push at any fuel: guarded store plus the two wrapping
    advances (miss aborts loudly). -/
theorem dfsPush_ok (F : Nat) (mL visL stL : List (BitVec 32))
    (n src top count v u : BitVec 64)
    (hstlen : stL.length < 2 ^ 64)
    (hguard : top.ult (BitVec.ofNat 64 stL.length) = true) :
    evalStmtFuel F dfsPush (mkDfsEnv mL visL stL n src top count v u) =
      .ok (mkDfsEnv mL visL (stL.set top.toNat (BitVec.ofNat 32 u.toNat))
        n src (top + 1) (count + 1) v u, .fellThrough) := by
  have hbody : dfsPush =
      .seq (.if_ (.ult (.var "top") (.stdVecLen "st"))
              (.vecSet "st" (.var "top") (.i32ofU64 (.var "u")))
              .fail)
      (.seq (.assign "top" (.uadd (.var "top")
                (.lit (.u64 (BitVec.ofNat 64 1)))))
        (.assign "count" (.uadd (.var "count")
          (.lit (.u64 (BitVec.ofNat 64 1)))))) := rfl
  have hst := mkDfsEnv_st mL visL stL n src top count v u
  have htop : evalExpr (.var "top")
      (mkDfsEnv mL visL stL n src top count v u) = .ok (.u64 top) :=
    evalExpr_var_hit _ _ _ (mkDfsEnv_top mL visL stL n src top count v u)
  have hlen : evalExpr (.stdVecLen "st")
      (mkDfsEnv mL visL stL n src top count v u) =
      .ok (.u64 (BitVec.ofNat 64 stL.length)) :=
    evalExpr_stdVecLen_some "st" _ stL hst
  have hg := evalExpr_ult_u64 _ _ _ _ _ htop hlen
  rw [hguard] at hg
  have hc : evalExpr (.ult (.var "top") (.stdVecLen "st"))
      (mkDfsEnv mL visL stL n src top count v u) = .ok (.b true) := hg
  have hlt : top.toNat < stL.length :=
    ultGuard_inBounds hstlen hguard
  have hne : stL[top.toNat]? ≠ none := by
    rw [ne_eq, List.getElem?_eq_none_iff]
    omega
  obtain ⟨w, hget'⟩ := Option.ne_none_iff_exists.mp hne
  have hget : stL[top.toNat]? = some w := hget'.symm
  have huvar : evalExpr (.var "u") (mkDfsEnv mL visL stL n src top count v u) =
      .ok (.u64 u) :=
    evalExpr_var_hit _ _ _ (mkDfsEnv_u mL visL stL n src top count v u)
  have hval : evalExpr (.i32ofU64 (.var "u"))
      (mkDfsEnv mL visL stL n src top count v u) =
      .ok (.i32 (BitVec.ofNat 32 u.toNat)) :=
    evalExpr_i32ofU64_ok _ _ _ huvar
  have hu : envUpdate (mkDfsEnv mL visL stL n src top count v u) "st"
      (.stdVecVal (stL.set top.toNat (BitVec.ofNat 32 u.toNat))) =
      some (mkDfsEnv mL visL (stL.set top.toNat (BitVec.ofNat 32 u.toNat))
        n src top count v u) := by
    simp [mkDfsEnv, envUpdate,
      show ("u" : String) ≠ "st" by decide,
      show ("v" : String) ≠ "st" by decide,
      show ("count" : String) ≠ "st" by decide,
      show ("top" : String) ≠ "st" by decide,
      show ("m" : String) ≠ "st" by decide,
      show ("vis" : String) ≠ "st" by decide]
  have hset := evalStmtFuel_vecSet F "st" (.var "top") (.i32ofU64 (.var "u"))
    (mkDfsEnv mL visL stL n src top count v u) top
    (BitVec.ofNat 32 u.toNat) stL w _ htop hval hst hget hu
  have hone : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      (mkDfsEnv mL visL (stL.set top.toNat (BitVec.ofNat 32 u.toNat))
        n src top count v u) =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have htop2 : evalExpr (.var "top")
      (mkDfsEnv mL visL (stL.set top.toNat (BitVec.ofNat 32 u.toNat))
        n src top count v u) = .ok (.u64 top) :=
    evalExpr_var_hit _ _ _ (by
      simp [envLookup, mkDfsEnv,
        show ("top" : String) ≠ "m" by decide,
        show ("top" : String) ≠ "vis" by decide,
        show ("top" : String) ≠ "st" by decide])
  have hu2 : envUpdate
      (mkDfsEnv mL visL (stL.set top.toNat (BitVec.ofNat 32 u.toNat))
        n src top count v u) "top" (.u64 (top + 1)) =
      some (mkDfsEnv mL visL (stL.set top.toNat (BitVec.ofNat 32 u.toNat))
        n src (top + 1) count v u) := by
    simp [mkDfsEnv, envUpdate,
      show ("u" : String) ≠ "top" by decide,
      show ("v" : String) ≠ "top" by decide,
      show ("count" : String) ≠ "top" by decide]
  have hadd1 := evalExpr_uadd_u64 _ _ _ _ _ htop2 hone
  have hassign1 := evalStmtFuel_assign F "top"
    (.uadd (.var "top") (.lit (.u64 (BitVec.ofNat 64 1))))
    (mkDfsEnv mL visL (stL.set top.toNat (BitVec.ofNat 32 u.toNat))
      n src top count v u) _ _ hadd1 hu2
  have hcount : evalExpr (.var "count")
      (mkDfsEnv mL visL (stL.set top.toNat (BitVec.ofNat 32 u.toNat))
        n src (top + 1) count v u) = .ok (.u64 count) :=
    evalExpr_var_hit _ _ _ (by
      simp [envLookup, mkDfsEnv,
        show ("count" : String) ≠ "m" by decide,
        show ("count" : String) ≠ "vis" by decide,
        show ("count" : String) ≠ "st" by decide,
        show ("count" : String) ≠ "n" by decide,
        show ("count" : String) ≠ "src" by decide,
        show ("count" : String) ≠ "top" by decide])
  have hone2 : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      (mkDfsEnv mL visL (stL.set top.toNat (BitVec.ofNat 32 u.toNat))
        n src (top + 1) count v u) =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have hu3 : envUpdate
      (mkDfsEnv mL visL (stL.set top.toNat (BitVec.ofNat 32 u.toNat))
        n src (top + 1) count v u) "count" (.u64 (count + 1)) =
      some (mkDfsEnv mL visL (stL.set top.toNat (BitVec.ofNat 32 u.toNat))
        n src (top + 1) (count + 1) v u) := by
    simp [mkDfsEnv, envUpdate,
      show ("u" : String) ≠ "count" by decide,
      show ("v" : String) ≠ "count" by decide]
  have hadd2 := evalExpr_uadd_u64 _ _ _ _ _ hcount hone2
  have hassign2 := evalStmtFuel_assign F "count"
    (.uadd (.var "count") (.lit (.u64 (BitVec.ofNat 64 1))))
    (mkDfsEnv mL visL (stL.set top.toNat (BitVec.ofNat 32 u.toNat))
      n src (top + 1) count v u) _ _ hadd2 hu3
  have hseq2 := evalStmtFuel_seq_fallthrough F
    (.assign "top" (.uadd (.var "top") (.lit (.u64 (BitVec.ofNat 64 1)))))
    (.assign "count" (.uadd (.var "count") (.lit (.u64 (BitVec.ofNat 64 1)))))
    _ _ hassign1
  have hif := (evalStmtFuel_if_true F _
    (.vecSet "st" (.var "top") (.i32ofU64 (.var "u"))) .fail _ hc).trans hset
  have houter := evalStmtFuel_seq_fallthrough F _
    (.seq (.assign "top" (.uadd (.var "top")
      (.lit (.u64 (BitVec.ofNat 64 1)))))
      (.assign "count" (.uadd (.var "count")
        (.lit (.u64 (BitVec.ofNat 64 1)))))) _ _ hif
  rw [hbody]
  exact houter.trans (hseq2.trans hassign2)

/-- A push past the reserved length aborts loudly (any fuel). -/
theorem dfsPush_miss (F : Nat) (mL visL stL : List (BitVec 32))
    (n src top count v u : BitVec 64)
    (hguard : top.ult (BitVec.ofNat 64 stL.length) = false) :
    evalStmtFuel F dfsPush (mkDfsEnv mL visL stL n src top count v u) =
      .error .AssertFail := by
  have hbody : dfsPush =
      .seq (.if_ (.ult (.var "top") (.stdVecLen "st"))
              (.vecSet "st" (.var "top") (.i32ofU64 (.var "u")))
              .fail)
      (.seq (.assign "top" (.uadd (.var "top")
                (.lit (.u64 (BitVec.ofNat 64 1)))))
        (.assign "count" (.uadd (.var "count")
          (.lit (.u64 (BitVec.ofNat 64 1)))))) := rfl
  have hst := mkDfsEnv_st mL visL stL n src top count v u
  have htop : evalExpr (.var "top")
      (mkDfsEnv mL visL stL n src top count v u) = .ok (.u64 top) :=
    evalExpr_var_hit _ _ _ (mkDfsEnv_top mL visL stL n src top count v u)
  have hlen : evalExpr (.stdVecLen "st")
      (mkDfsEnv mL visL stL n src top count v u) =
      .ok (.u64 (BitVec.ofNat 64 stL.length)) :=
    evalExpr_stdVecLen_some "st" _ stL hst
  have hg : evalExpr (.ult (.var "top") (.stdVecLen "st"))
      (mkDfsEnv mL visL stL n src top count v u) = .ok (.b false) := by
    have h := evalExpr_ult_u64 _ _ _ _ _ htop hlen
    rw [hguard] at h
    exact h
  rw [hbody]
  exact evalStmtFuel_seq_err F _
    (.seq (.assign "top" (.uadd (.var "top")
      (.lit (.u64 (BitVec.ofNat 64 1)))))
      (.assign "count" (.uadd (.var "count")
        (.lit (.u64 (BitVec.ofNat 64 1)))))) _ _
    ((evalStmtFuel_if_false F _ _ _ _ hg).trans
      (evalStmtFuel_fail F _))

/-- Bridge: a `some` read gives a strict bound. -/
theorem getElem_some_lt {α : Type} {l : List α} {i : Nat} {x : α}
    (h : l[i]? = some x) : i < l.length := by
  have hne : l[i]? ≠ none := by simp [h]
  rw [ne_eq, List.getElem?_eq_none_iff] at hne
  omega

/-- One row-scan iteration at any fuel: the matrix guard, the two
    gates, the push, and the `u` advance — mirroring the forward's
    branch order exactly. -/
theorem dfsInnerBody_eval (F : Nat) (mL visL stL : List (BitVec 32))
    (n src top count v u : BitVec 64)
    (hmen : mL.length < 2 ^ 64) (hvislen : visL.length < 2 ^ 64)
    (hstlen : stL.length < 2 ^ 64) :
    evalStmtFuel F dfsInnerBody
      (mkDfsEnv mL visL stL n src top count v u) =
      match mL[(v * n + u).toNat]? with
      | none => .error .AssertFail
      | some g =>
        if g != (BitVec.ofNat 32 0) then
          match visL[u.toNat]? with
          | none => .error .AssertFail
          | some w =>
            if w == (BitVec.ofNat 32 0) then
              match stL[top.toNat]? with
              | none => .error .AssertFail
              | some _ => .ok (mkDfsEnv mL (visL.set u.toNat 1)
                  (stL.set top.toNat (BitVec.ofNat 32 u.toNat))
                  n src (top + 1) (count + 1) v (u + 1), .fellThrough)
            else .ok (mkDfsEnv mL visL stL n src top count v (u + 1),
              .fellThrough)
        else .ok (mkDfsEnv mL visL stL n src top count v (u + 1),
          .fellThrough) := by
  have hbody : dfsInnerBody =
      .seq (.if_ (.ult dfsRowIdx (.stdVecLen "m"))
              (.if_ (.une (.stdVecAt "m" dfsRowIdx)
                      (.lit (.i32 (BitVec.ofNat 32 0))))
                (.if_ (.ult (.var "u") (.stdVecLen "vis"))
                  (.if_ (.ueq (.stdVecAt "vis" (.var "u"))
                          (.lit (.i32 (BitVec.ofNat 32 0))))
                    (.seq (.vecSet "vis" (.var "u")
                             (.lit (.i32 (BitVec.ofNat 32 1))))
                      dfsPush)
                    .skip)
                  .fail)
                .skip)
              .fail)
           (.assign "u" (.uadd (.var "u")
             (.lit (.u64 (BitVec.ofNat 64 1))))) := rfl
  have hidx := dfsRowIdx_eval mL visL stL n src top count v u
  have hm := mkDfsEnv_m mL visL stL n src top count v u
  have hmlen : evalExpr (.stdVecLen "m")
      (mkDfsEnv mL visL stL n src top count v u) =
      .ok (.u64 (BitVec.ofNat 64 mL.length)) :=
    evalExpr_stdVecLen_some "m" _ mL hm
  have hmguard := evalExpr_ult_u64 _ _ _ _ _ hidx hmlen
  -- The `u` advance shared by every fall-through leg.
  have hadv : ∀ (vis' stL' : List (BitVec 32)) (top' count' : BitVec 64),
      evalStmtFuel F (.assign "u" (.uadd (.var "u")
        (.lit (.u64 (BitVec.ofNat 64 1)))))
        (mkDfsEnv mL vis' stL' n src top' count' v u) =
        .ok (mkDfsEnv mL vis' stL' n src top' count' v (u + 1),
          .fellThrough) := by
    intro vis' stL' top' count'
    have hvar : evalExpr (.var "u")
        (mkDfsEnv mL vis' stL' n src top' count' v u) = .ok (.u64 u) :=
      evalExpr_var_hit _ _ _ (by
        simp [envLookup, mkDfsEnv,
          show ("u" : String) ≠ "m" by decide,
          show ("u" : String) ≠ "vis" by decide,
          show ("u" : String) ≠ "st" by decide,
          show ("u" : String) ≠ "n" by decide,
          show ("u" : String) ≠ "src" by decide,
          show ("u" : String) ≠ "top" by decide,
          show ("u" : String) ≠ "count" by decide,
          show ("u" : String) ≠ "v" by decide])
    have hone : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
        (mkDfsEnv mL vis' stL' n src top' count' v u) =
        .ok (.u64 (BitVec.ofNat 64 1)) := by
      simp [evalExpr, litVal]
    have hadd := evalExpr_uadd_u64 _ _ _ _ _ hvar hone
    have hu : envUpdate (mkDfsEnv mL vis' stL' n src top' count' v u) "u"
        (.u64 (u + 1)) =
        some (mkDfsEnv mL vis' stL' n src top' count' v (u + 1)) := by
      simp [mkDfsEnv, envUpdate]
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
    have hc : evalExpr (.ult dfsRowIdx (.stdVecLen "m"))
        (mkDfsEnv mL visL stL n src top count v u) = .ok (.b false) := by
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
    have hlt : (v * n + u).toNat < mL.length := getElem_some_lt hgetm
    have hult : (v * n + u).ult (BitVec.ofNat 64 mL.length) = true := by
      have h1 : (v * n + u).toNat <
          (BitVec.ofNat 64 mL.length).toNat := by
        rw [ofNat64_toNat _ hmen]
        exact hlt
      have h2 : decide ((v * n + u).toNat <
          (BitVec.ofNat 64 mL.length).toNat) = true :=
        decide_eq_true h1
      rwa [← BitVec.ult_eq_decide] at h2
    have hc : evalExpr (.ult dfsRowIdx (.stdVecLen "m"))
        (mkDfsEnv mL visL stL n src top count v u) = .ok (.b true) := by
      have h1 := evalExpr_ult_u64 _ _ _ _ _ hidx hmlen
      rw [hult] at h1
      exact h1
    have hread : evalExpr (.stdVecAt "m" dfsRowIdx)
        (mkDfsEnv mL visL stL n src top count v u) = .ok (.i32 g) := by
      have hi := dfsRowIdx_eval mL visL stL n src top count v u
      exact evalExpr_stdVecAt_some "m" _ _ _ _ _ hm hi hgetm
    have hzero : evalExpr (.lit (.i32 (BitVec.ofNat 32 0)))
        (mkDfsEnv mL visL stL n src top count v u) =
        .ok (.i32 (BitVec.ofNat 32 0)) := by
      simp [evalExpr, litVal]
    have hgateM := evalExpr_une_i32 _ _ _ _ _ hread hzero
    by_cases hgm : g != (BitVec.ofNat 32 0)
    · have hcm : evalExpr (.une (.stdVecAt "m" dfsRowIdx)
            (.lit (.i32 (BitVec.ofNat 32 0))))
            (mkDfsEnv mL visL stL n src top count v u) =
            .ok (.b true) := by
        simp only [hgm] at hgateM
        exact hgateM
      have hvis := mkDfsEnv_vis mL visL stL n src top count v u
      have huvar : evalExpr (.var "u")
          (mkDfsEnv mL visL stL n src top count v u) = .ok (.u64 u) :=
        evalExpr_var_hit _ _ _ (mkDfsEnv_u mL visL stL n src top count v u)
      have hvlen : evalExpr (.stdVecLen "vis")
          (mkDfsEnv mL visL stL n src top count v u) =
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
            (mkDfsEnv mL visL stL n src top count v u) =
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
        have hltv : u.toNat < visL.length := getElem_some_lt hgetv
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
            (mkDfsEnv mL visL stL n src top count v u) =
            .ok (.b true) := by
          rw [hult] at hvguard
          exact hvguard
        have hreadv : evalExpr (.stdVecAt "vis" (.var "u"))
            (mkDfsEnv mL visL stL n src top count v u) = .ok (.i32 w) :=
          evalExpr_stdVecAt_some "vis" _ _ _ _ _ hvis huvar hgetv
        have hgateV := evalExpr_ueq_i32 _ _ _ _ _ hreadv hzero
        by_cases hgv : w == (BitVec.ofNat 32 0)
        · have hcv2 : evalExpr (.ueq (.stdVecAt "vis" (.var "u"))
                (.lit (.i32 (BitVec.ofNat 32 0))))
                (mkDfsEnv mL visL stL n src top count v u) =
                .ok (.b true) := by
            simp only [hgv] at hgateV
            exact hgateV
          -- push leg: vis-store, guarded push, shared advance.
          match hgetst : stL[top.toNat]? with
          | none =>
            have hnot : ¬ top.toNat < stL.length := by
              intro hcon
              have hne : stL[top.toNat]? ≠ none := by
                rw [ne_eq, List.getElem?_eq_none_iff]
                omega
              exact hne hgetst
            have hstgF : top.ult (BitVec.ofNat 64 stL.length) = false := by
              have h1 : ¬ top.toNat <
                  (BitVec.ofNat 64 stL.length).toNat := by
                rw [ofNat64_toNat _ hstlen]
                exact hnot
              have h2 : decide (top.toNat <
                  (BitVec.ofNat 64 stL.length).toNat) = false :=
                decide_eq_false h1
              rwa [← BitVec.ult_eq_decide] at h2
            have hvis : envLookup (mkDfsEnv mL visL stL n src top count v u)
                "vis" = some (.stdVecVal visL) :=
              mkDfsEnv_vis mL visL stL n src top count v u
            have huvar : evalExpr (.var "u")
                (mkDfsEnv mL visL stL n src top count v u) = .ok (.u64 u) :=
              evalExpr_var_hit _ _ _ (mkDfsEnv_u mL visL stL n src top count v u)
            have hx1 : evalExpr (.lit (.i32 (1 : BitVec 32)))
                (mkDfsEnv mL visL stL n src top count v u) =
                .ok (.i32 1) := by
              simp [evalExpr, litVal]
            have hu : envUpdate (mkDfsEnv mL visL stL n src top count v u) "vis"
                (.stdVecVal (visL.set u.toNat 1)) =
                some (mkDfsEnv mL (visL.set u.toNat 1) stL
                  n src top count v u) := by
              simp [mkDfsEnv, envUpdate,
                show ("u" : String) ≠ "vis" by decide,
                show ("v" : String) ≠ "vis" by decide,
                show ("count" : String) ≠ "vis" by decide,
                show ("top" : String) ≠ "vis" by decide,
                show ("m" : String) ≠ "vis" by decide]
            have hsetv := evalStmtFuel_vecSet F "vis" (.var "u")
              (.lit (.i32 (1 : BitVec 32)))
              (mkDfsEnv mL visL stL n src top count v u) u 1 visL w _
              huvar hx1 hvis hgetv hu
            have hpushF := dfsPush_miss F mL (visL.set u.toNat 1) stL
              n src top count v u hstgF
            have hdone := (evalStmtFuel_seq_fallthrough F _ dfsPush _ _
              hsetv).trans hpushF
            rw [hbody]
            simp only [hgetm, hgm, hgetv, hgv, hgetst]
            exact evalStmtFuel_seq_err F _
                                  (.assign "u" (.uadd (.var "u")
                                    (.lit (.u64 (BitVec.ofNat 64 1))))) _ _
                                  (((((evalStmtFuel_if_true F _ _ _ _ hc).trans (evalStmtFuel_if_true F _ _ _ _ hcm)).trans (evalStmtFuel_if_true F _ _ _ _ hcv)).trans (evalStmtFuel_if_true F _ _ _ _ hcv2)).trans (hdone))
          | some _ =>
              have hvis : envLookup (mkDfsEnv mL visL stL n src top count v u)
                "vis" = some (.stdVecVal visL) :=
              mkDfsEnv_vis mL visL stL n src top count v u
              have huvar : evalExpr (.var "u")
                  (mkDfsEnv mL visL stL n src top count v u) = .ok (.u64 u) :=
                evalExpr_var_hit _ _ _ (mkDfsEnv_u mL visL stL n src top count v u)
              have hx1 : evalExpr (.lit (.i32 (1 : BitVec 32)))
                  (mkDfsEnv mL visL stL n src top count v u) =
                  .ok (.i32 1) := by
                simp [evalExpr, litVal]
              have hu : envUpdate (mkDfsEnv mL visL stL n src top count v u) "vis"
                  (.stdVecVal (visL.set u.toNat 1)) =
                  some (mkDfsEnv mL (visL.set u.toNat 1) stL
                    n src top count v u) := by
                simp [mkDfsEnv, envUpdate,
                  show ("u" : String) ≠ "vis" by decide,
                  show ("v" : String) ≠ "vis" by decide,
                  show ("count" : String) ≠ "vis" by decide,
                  show ("top" : String) ≠ "vis" by decide,
                  show ("m" : String) ≠ "vis" by decide]
              have hsetv := evalStmtFuel_vecSet F "vis" (.var "u")
                (.lit (.i32 (1 : BitVec 32)))
                (mkDfsEnv mL visL stL n src top count v u) u 1 visL w _
                huvar hx1 hvis hgetv hu
              have hstg : top.ult (BitVec.ofNat 64 stL.length) = true := by
                have hltst : top.toNat < stL.length := getElem_some_lt hgetst
                have h2 : decide (top.toNat <
                    (BitVec.ofNat 64 stL.length).toNat) = true := by
                  rw [ofNat64_toNat _ hstlen]
                  exact decide_eq_true hltst
                rwa [← BitVec.ult_eq_decide] at h2
              have hpush := dfsPush_ok F mL (visL.set u.toNat 1) stL
                n src top count v u hstlen hstg
              have hdone := (evalStmtFuel_seq_fallthrough F _ dfsPush _ _
                hsetv).trans hpush
              have hadv1 := hadv (visL.set u.toNat 1)
                (stL.set top.toNat (BitVec.ofNat 32 u.toNat)) (top + 1) (count + 1)
              rw [hbody]
              simp only [hgetm, hgm, hgetv, hgv, hgetst]
              exact ((evalStmtFuel_seq_fallthrough F _
                  (.assign "u" (.uadd (.var "u")
                    (.lit (.u64 (BitVec.ofNat 64 1))))) _ _
                  (((((evalStmtFuel_if_true F _ _ _ _ hc).trans (evalStmtFuel_if_true F _ _ _ _ hcm)).trans (evalStmtFuel_if_true F _ _ _ _ hcv)).trans (evalStmtFuel_if_true F _ _ _ _ hcv2)).trans (hdone))).trans hadv1)
        · -- visited leg: skip the push, still advance `u`.
          have hfalse : (w == (BitVec.ofNat 32 0)) = false :=
            Bool.eq_false_of_ne_true hgv
          have hcv2 : evalExpr (.ueq (.stdVecAt "vis" (.var "u"))
                  (.lit (.i32 (BitVec.ofNat 32 0))))
                  (mkDfsEnv mL visL stL n src top count v u) =
                  .ok (.b false) := by
            rw [hfalse] at hgateV
            exact hgateV
          have hskip : evalStmtFuel F .skip
              (mkDfsEnv mL visL stL n src top count v u) =
              .ok (mkDfsEnv mL visL stL n src top count v u,
                .fellThrough) := by
            cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith]
          have hadv1 := hadv visL stL top count
          rw [hbody]
          simp only [hgetm, hgm, hgetv, hfalse]
          exact ((evalStmtFuel_seq_fallthrough F _
              (.assign "u" (.uadd (.var "u")
                (.lit (.u64 (BitVec.ofNat 64 1))))) _ _
              (((((evalStmtFuel_if_true F _ _ _ _ hc).trans (evalStmtFuel_if_true F _ _ _ _ hcm)).trans (evalStmtFuel_if_true F _ _ _ _ hcv)).trans (evalStmtFuel_if_false F _ _ _ _ hcv2)).trans (hskip))).trans hadv1)
    · -- no-edge leg: skip the visit test, still advance `u`.
      have hfalseM : (g != (BitVec.ofNat 32 0)) = false :=
        Bool.eq_false_of_ne_true hgm
      have hcm : evalExpr (.une (.stdVecAt "m" dfsRowIdx)
              (.lit (.i32 (BitVec.ofNat 32 0))))
              (mkDfsEnv mL visL stL n src top count v u) =
              .ok (.b false) := by
        rw [hfalseM] at hgateM
        exact hgateM
      have hskip : evalStmtFuel F .skip
          (mkDfsEnv mL visL stL n src top count v u) =
          .ok (mkDfsEnv mL visL stL n src top count v u,
            .fellThrough) := by
        cases F <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith]
      have hadv1 := hadv visL stL top count
      rw [hbody]
      simp only [hgetm, hfalseM]
      exact ((evalStmtFuel_seq_fallthrough F _
              (.assign "u" (.uadd (.var "u")
                (.lit (.u64 (BitVec.ofNat 64 1))))) _ _
              (((evalStmtFuel_if_true F _ _ _ _ hc).trans (evalStmtFuel_if_false F _ _ _ _ hcm)).trans (hskip))).trans hadv1)

/-- Row scan at fuel `F`: the evaluator agrees with the forward on
    every `.ok` run (fuel induction; the error legs contradict `hfwd`). -/
theorem dfsRow_ok (F : Nat) (mL visL stL : List (BitVec 32))
    (n src top count v u : BitVec 64)
    (hmen : mL.length < 2 ^ 64) (hvislen : visL.length < 2 ^ 64)
    (hstlen : stL.length < 2 ^ 64)
    (vis' stL' : List (BitVec 32)) (top' count' u' : BitVec 64)
    (hfwd : dfsRowFwd F mL visL stL n v top count u =
      .ok (vis', stL', top', count', u')) :
    evalStmtFuel F dfsInner (mkDfsEnv mL visL stL n src top count v u) =
      .ok (mkDfsEnv mL vis' stL' n src top' count' v u', .fellThrough) := by
  induction F generalizing visL stL top count u vis' stL' top' count' u' with
  | zero =>
    by_cases hult : u.ult n = true
    · have hcon : dfsRowFwd 0 mL visL stL n v top count u =
          .error .AssertFail := by
        simp only [dfsRowFwd, hult, Bool.false_eq_true, ite_true, ite_false]
      rw [hcon] at hfwd
      cases hfwd
    · have hultF : (u.ult n) = false := Bool.eq_false_of_ne_true hult
      have huvar : evalExpr (.var "u")
          (mkDfsEnv mL visL stL n src top count v u) = .ok (.u64 u) :=
        evalExpr_var_hit _ _ _ (mkDfsEnv_u mL visL stL n src top count v u)
      have hnvar : evalExpr (.var "n")
          (mkDfsEnv mL visL stL n src top count v u) = .ok (.u64 n) :=
        evalExpr_var_hit _ _ _ (mkDfsEnv_n mL visL stL n src top count v u)
      have hcond : evalExpr (.ult (.var "u") (.var "n"))
          (mkDfsEnv mL visL stL n src top count v u) = .ok (.b false) := by
        have h := evalExpr_ult_u64 _ _ _ _ _ huvar hnvar
        rw [hultF] at h
        exact h
      have hev : evalStmtFuel 0 dfsInner
          (mkDfsEnv mL visL stL n src top count v u) =
          .ok (mkDfsEnv mL visL stL n src top count v u, .fellThrough) :=
        evalStmtFuel_zero_while_exit _ _ _ hcond
      have hfw : dfsRowFwd 0 mL visL stL n v top count u =
          .ok (visL, stL, top, count, u) := by
        simp only [dfsRowFwd, hult, Bool.false_eq_true, ite_true, ite_false]
      rw [hfw] at hfwd
      have h5 : (visL, stL, top, count, u) =
          (vis', stL', top', count', u') := by
        injection hfwd
      simp only [Prod.mk.injEq] at h5
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h5
      exact hev
  | succ F ih =>
    have huvar : evalExpr (.var "u")
        (mkDfsEnv mL visL stL n src top count v u) = .ok (.u64 u) :=
      evalExpr_var_hit _ _ _ (mkDfsEnv_u mL visL stL n src top count v u)
    have hnvar : evalExpr (.var "n")
        (mkDfsEnv mL visL stL n src top count v u) = .ok (.u64 n) :=
      evalExpr_var_hit _ _ _ (mkDfsEnv_n mL visL stL n src top count v u)
    by_cases hult : u.ult n = true
    · have hcondT : evalExpr (.ult (.var "u") (.var "n"))
          (mkDfsEnv mL visL stL n src top count v u) = .ok (.b true) := by
        have h := evalExpr_ult_u64 _ _ _ _ _ huvar hnvar
        rw [hult] at h
        exact h
      match hgetm : mL[(v * n + u).toNat]? with
      | none =>
        have hcon : dfsRowFwd (F + 1) mL visL stL n v top count u =
            .error .AssertFail := by
          simp only [dfsRowFwd, hult, hgetm, ite_true, ite_false]
        rw [hcon] at hfwd
        cases hfwd
      | some g =>
        by_cases hgm : g != (BitVec.ofNat 32 0)
        · match hgetv : visL[u.toNat]? with
          | none =>
            have hcon : dfsRowFwd (F + 1) mL visL stL n v top count u =
                .error .AssertFail := by
              simp only [dfsRowFwd, hult, hgetm, hgm, hgetv, ite_true, ite_false]
            rw [hcon] at hfwd
            cases hfwd
          | some w =>
            by_cases hgv : w == (BitVec.ofNat 32 0)
            · match hgetst : stL[top.toNat]? with
              | none =>
                have hcon : dfsRowFwd (F + 1) mL visL stL n v top count u =
                    .error .AssertFail := by
                  simp only [dfsRowFwd, hult, hgetm, hgm, hgetv, hgv, hgetst, ite_true, ite_false]
                rw [hcon] at hfwd
                cases hfwd
              | some _ =>
                have hltv : u.toNat < visL.length := getElem_some_lt hgetv
                have hvislen1 : (visL.set u.toNat 1).length < 2 ^ 64 := by
                  rw [List.length_set]
                  exact hvislen
                have hltst : top.toNat < stL.length :=
                  getElem_some_lt hgetst
                have hstlen1 : (stL.set top.toNat
                    (BitVec.ofNat 32 u.toNat)).length < 2 ^ 64 := by
                  rw [List.length_set]
                  exact hstlen
                have hb : evalStmtFuel F dfsInnerBody
                    (mkDfsEnv mL visL stL n src top count v u) =
                    .ok (mkDfsEnv mL (visL.set u.toNat 1)
                      (stL.set top.toNat (BitVec.ofNat 32 u.toNat))
                      n src (top + 1) (count + 1) v (u + 1),
                      .fellThrough) := by
                  have h := dfsInnerBody_eval F mL visL stL n src top count
                    v u hmen hvislen hstlen
                  simp only [hgetm, hgm, hgetv, hgv, hgetst] at h
                  exact h
                have hloop : evalStmtFuel (F + 1) dfsInner
                    (mkDfsEnv mL visL stL n src top count v u) =
                    evalStmtFuel F dfsInner (mkDfsEnv mL (visL.set u.toNat 1)
                      (stL.set top.toNat (BitVec.ofNat 32 u.toNat))
                      n src (top + 1) (count + 1) v (u + 1)) := by
                  simp only [dfsInner, evalStmtFuel, evalStmtSuccHandler,
                    evalStmtWith, hcondT, hb]
                have hfwd1 : dfsRowFwd (F + 1) mL visL stL n v top count u =
                    dfsRowFwd F mL (visL.set u.toNat 1)
                      (stL.set top.toNat (BitVec.ofNat 32 u.toNat))
                      n v (top + 1) (count + 1) (u + 1) := by
                  simp only [dfsRowFwd, hult, hgetm, hgm, hgetv, hgv, hgetst, ite_true, ite_false]
                rw [hfwd1] at hfwd
                rw [hloop]
                exact ih _ _ _ _ _ hvislen1 hstlen1 _ _ _ _ _ hfwd
            · have hfalse : (w == (BitVec.ofNat 32 0)) = false :=
                Bool.eq_false_of_ne_true hgv
              have hb : evalStmtFuel F dfsInnerBody
                  (mkDfsEnv mL visL stL n src top count v u) =
                  .ok (mkDfsEnv mL visL stL n src top count v (u + 1),
                    .fellThrough) := by
                have h := dfsInnerBody_eval F mL visL stL n src top count
                  v u hmen hvislen hstlen
                simp only [hgetm, hgm, hgetv, hfalse] at h
                exact h
              have hloop : evalStmtFuel (F + 1) dfsInner
                  (mkDfsEnv mL visL stL n src top count v u) =
                  evalStmtFuel F dfsInner
                    (mkDfsEnv mL visL stL n src top count v (u + 1)) := by
                simp only [dfsInner, evalStmtFuel, evalStmtSuccHandler,
                  evalStmtWith, hcondT, hb]
              have hfwd1 : dfsRowFwd (F + 1) mL visL stL n v top count u =
                  dfsRowFwd F mL visL stL n v top count (u + 1) := by
                simp only [dfsRowFwd, hult, hgetm, hgm, hgetv, hgv,
                  Bool.false_eq_true, ite_true, ite_false]
              rw [hfwd1] at hfwd
              rw [hloop]
              exact ih _ _ _ _ _ hvislen hstlen _ _ _ _ _ hfwd
        · have hfalseM : (g != (BitVec.ofNat 32 0)) = false :=
            Bool.eq_false_of_ne_true hgm
          have hb : evalStmtFuel F dfsInnerBody
              (mkDfsEnv mL visL stL n src top count v u) =
              .ok (mkDfsEnv mL visL stL n src top count v (u + 1),
                .fellThrough) := by
            have h := dfsInnerBody_eval F mL visL stL n src top count
              v u hmen hvislen hstlen
            simp only [hgetm, hfalseM] at h
            exact h
          have hloop : evalStmtFuel (F + 1) dfsInner
              (mkDfsEnv mL visL stL n src top count v u) =
              evalStmtFuel F dfsInner
                (mkDfsEnv mL visL stL n src top count v (u + 1)) := by
            simp only [dfsInner, evalStmtFuel, evalStmtSuccHandler,
              evalStmtWith, hcondT, hb]
          have hfwd1 : dfsRowFwd (F + 1) mL visL stL n v top count u =
              dfsRowFwd F mL visL stL n v top count (u + 1) := by
            simp only [dfsRowFwd, hult, hgetm, hgm, Bool.false_eq_true,
              ite_true, ite_false]
          rw [hfwd1] at hfwd
          rw [hloop]
          exact ih _ _ _ _ _ hvislen hstlen _ _ _ _ _ hfwd
    · have hultF : (u.ult n) = false := Bool.eq_false_of_ne_true hult
      have hcond : evalExpr (.ult (.var "u") (.var "n"))
          (mkDfsEnv mL visL stL n src top count v u) = .ok (.b false) := by
        have h := evalExpr_ult_u64 _ _ _ _ _ huvar hnvar
        rw [hultF] at h
        exact h
      have hev : evalStmtFuel (F + 1) dfsInner
          (mkDfsEnv mL visL stL n src top count v u) =
          .ok (mkDfsEnv mL visL stL n src top count v u, .fellThrough) := by
        simp [dfsInner, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond]
      have hfw : dfsRowFwd (F + 1) mL visL stL n v top count u =
          .ok (visL, stL, top, count, u) := by
        simp only [dfsRowFwd, hult, Bool.false_eq_true, ite_true, ite_false]
      rw [hfw] at hfwd
      have h5 : (visL, stL, top, count, u) =
          (vis', stL', top', count', u') := by
        injection hfwd
      simp only [Prod.mk.injEq] at h5
      obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h5
      exact hev

/-- Row scan at fuel `F`: the evaluator agrees with the forward on
    every `.error` run (fuel induction; the ok legs step the loop and
    apply the IH). -/
theorem dfsRow_err (F : Nat) (mL visL stL : List (BitVec 32))
    (n src top count v u : BitVec 64)
    (hmen : mL.length < 2 ^ 64) (hvislen : visL.length < 2 ^ 64)
    (hstlen : stL.length < 2 ^ 64)
    (e : Panic)
    (hfwd : dfsRowFwd F mL visL stL n v top count u = .error e) :
    evalStmtFuel F dfsInner (mkDfsEnv mL visL stL n src top count v u) =
      .error e := by
  induction F generalizing visL stL top count u with
  | zero =>
    by_cases hult : u.ult n = true
    · have hultT : (u.ult n) = true := hult
      have huvar : evalExpr (.var "u")
          (mkDfsEnv mL visL stL n src top count v u) = .ok (.u64 u) :=
        evalExpr_var_hit _ _ _ (mkDfsEnv_u mL visL stL n src top count v u)
      have hnvar : evalExpr (.var "n")
          (mkDfsEnv mL visL stL n src top count v u) = .ok (.u64 n) :=
        evalExpr_var_hit _ _ _ (mkDfsEnv_n mL visL stL n src top count v u)
      have hcond : evalExpr (.ult (.var "u") (.var "n"))
          (mkDfsEnv mL visL stL n src top count v u) = .ok (.b true) := by
        have h := evalExpr_ult_u64 _ _ _ _ _ huvar hnvar
        rw [hultT] at h
        exact h
      have hev : evalStmtFuel 0 dfsInner
          (mkDfsEnv mL visL stL n src top count v u) =
          .error .AssertFail :=
        evalStmtFuel_zero_while_enter _ _ _ hcond
      have hcon : dfsRowFwd 0 mL visL stL n v top count u =
          .error .AssertFail := by
        simp only [dfsRowFwd, hultT, ite_true, ite_false]
      rw [hcon] at hfwd
      cases hfwd
      exact hev
    · have hfw : dfsRowFwd 0 mL visL stL n v top count u =
          .ok (visL, stL, top, count, u) := by
        simp only [dfsRowFwd, hult, Bool.false_eq_true, ite_true, ite_false]
      rw [hfw] at hfwd
      cases hfwd
  | succ F ih =>
    have huvar : evalExpr (.var "u")
        (mkDfsEnv mL visL stL n src top count v u) = .ok (.u64 u) :=
      evalExpr_var_hit _ _ _ (mkDfsEnv_u mL visL stL n src top count v u)
    have hnvar : evalExpr (.var "n")
        (mkDfsEnv mL visL stL n src top count v u) = .ok (.u64 n) :=
      evalExpr_var_hit _ _ _ (mkDfsEnv_n mL visL stL n src top count v u)
    by_cases hult : u.ult n = true
    · have hcondT : evalExpr (.ult (.var "u") (.var "n"))
          (mkDfsEnv mL visL stL n src top count v u) = .ok (.b true) := by
        have h := evalExpr_ult_u64 _ _ _ _ _ huvar hnvar
        rw [hult] at h
        exact h
      -- Body-error legs reuse the single-step theorem, then the loop
      -- replays the error through the successor handler.
      match hgetm : mL[(v * n + u).toNat]? with
      | none =>
        have hcon : dfsRowFwd (F + 1) mL visL stL n v top count u =
            .error .AssertFail := by
          simp only [dfsRowFwd, hult, hgetm, ite_true, ite_false]
        have hb : evalStmtFuel F dfsInnerBody
            (mkDfsEnv mL visL stL n src top count v u) =
            .error .AssertFail := by
          have h := dfsInnerBody_eval F mL visL stL n src top count
            v u hmen hvislen hstlen
          simp only [hgetm] at h
          exact h
        have hev : evalStmtFuel (F + 1) dfsInner
            (mkDfsEnv mL visL stL n src top count v u) =
            .error .AssertFail := by
          simp only [dfsInner, evalStmtFuel, evalStmtSuccHandler,
            evalStmtWith, hcondT, hb]
        rw [hcon] at hfwd
        cases hfwd
        exact hev
      | some g =>
        by_cases hgm : g != (BitVec.ofNat 32 0)
        · match hgetv : visL[u.toNat]? with
          | none =>
            have hcon : dfsRowFwd (F + 1) mL visL stL n v top count u =
                .error .AssertFail := by
              simp only [dfsRowFwd, hult, hgetm, hgm, hgetv, ite_true,
                ite_false]
            have hb : evalStmtFuel F dfsInnerBody
                (mkDfsEnv mL visL stL n src top count v u) =
                .error .AssertFail := by
              have h := dfsInnerBody_eval F mL visL stL n src top count
                v u hmen hvislen hstlen
              simp only [hgetm, hgm, hgetv] at h
              exact h
            have hev : evalStmtFuel (F + 1) dfsInner
                (mkDfsEnv mL visL stL n src top count v u) =
                .error .AssertFail := by
              simp only [dfsInner, evalStmtFuel, evalStmtSuccHandler,
                evalStmtWith, hcondT, hb]
            rw [hcon] at hfwd
            cases hfwd
            exact hev
          | some w =>
            by_cases hgv : w == (BitVec.ofNat 32 0)
            · match hgetst : stL[top.toNat]? with
              | none =>
                have hcon : dfsRowFwd (F + 1) mL visL stL n v top count u =
                    .error .AssertFail := by
                  simp only [dfsRowFwd, hult, hgetm, hgm, hgetv, hgv,
                    hgetst, ite_true, ite_false]
                have hb : evalStmtFuel F dfsInnerBody
                    (mkDfsEnv mL visL stL n src top count v u) =
                    .error .AssertFail := by
                  have h := dfsInnerBody_eval F mL visL stL n src top count
                    v u hmen hvislen hstlen
                  simp only [hgetm, hgm, hgetv, hgv, hgetst] at h
                  exact h
                have hev : evalStmtFuel (F + 1) dfsInner
                    (mkDfsEnv mL visL stL n src top count v u) =
                    .error .AssertFail := by
                  simp only [dfsInner, evalStmtFuel, evalStmtSuccHandler,
                    evalStmtWith, hcondT, hb]
                rw [hcon] at hfwd
                cases hfwd
                exact hev
              | some _ =>
                have hltv : u.toNat < visL.length := getElem_some_lt hgetv
                have hvislen1 : (visL.set u.toNat 1).length < 2 ^ 64 := by
                  rw [List.length_set]
                  exact hvislen
                have hltst : top.toNat < stL.length :=
                  getElem_some_lt hgetst
                have hstlen1 : (stL.set top.toNat
                    (BitVec.ofNat 32 u.toNat)).length < 2 ^ 64 := by
                  rw [List.length_set]
                  exact hstlen
                have hb : evalStmtFuel F dfsInnerBody
                    (mkDfsEnv mL visL stL n src top count v u) =
                    .ok (mkDfsEnv mL (visL.set u.toNat 1)
                      (stL.set top.toNat (BitVec.ofNat 32 u.toNat))
                      n src (top + 1) (count + 1) v (u + 1),
                      .fellThrough) := by
                  have h := dfsInnerBody_eval F mL visL stL n src top count
                    v u hmen hvislen hstlen
                  simp only [hgetm, hgm, hgetv, hgv, hgetst] at h
                  exact h
                have hloop : evalStmtFuel (F + 1) dfsInner
                    (mkDfsEnv mL visL stL n src top count v u) =
                    evalStmtFuel F dfsInner (mkDfsEnv mL (visL.set u.toNat 1)
                      (stL.set top.toNat (BitVec.ofNat 32 u.toNat))
                      n src (top + 1) (count + 1) v (u + 1)) := by
                  simp only [dfsInner, evalStmtFuel, evalStmtSuccHandler,
                    evalStmtWith, hcondT, hb]
                have hfwd1 : dfsRowFwd (F + 1) mL visL stL n v top count u =
                    dfsRowFwd F mL (visL.set u.toNat 1)
                      (stL.set top.toNat (BitVec.ofNat 32 u.toNat))
                      n v (top + 1) (count + 1) (u + 1) := by
                  simp only [dfsRowFwd, hult, hgetm, hgm, hgetv, hgv,
                    hgetst, ite_true, ite_false]
                rw [hfwd1] at hfwd
                rw [hloop]
                exact ih _ _ _ _ _ hvislen1 hstlen1 hfwd
            · have hfalse : (w == (BitVec.ofNat 32 0)) = false :=
                Bool.eq_false_of_ne_true hgv
              have hb : evalStmtFuel F dfsInnerBody
                  (mkDfsEnv mL visL stL n src top count v u) =
                  .ok (mkDfsEnv mL visL stL n src top count v (u + 1),
                    .fellThrough) := by
                have h := dfsInnerBody_eval F mL visL stL n src top count
                  v u hmen hvislen hstlen
                simp only [hgetm, hgm, hgetv, hfalse] at h
                exact h
              have hloop : evalStmtFuel (F + 1) dfsInner
                  (mkDfsEnv mL visL stL n src top count v u) =
                  evalStmtFuel F dfsInner
                    (mkDfsEnv mL visL stL n src top count v (u + 1)) := by
                simp only [dfsInner, evalStmtFuel, evalStmtSuccHandler,
                  evalStmtWith, hcondT, hb]
              have hfwd1 : dfsRowFwd (F + 1) mL visL stL n v top count u =
                  dfsRowFwd F mL visL stL n v top count (u + 1) := by
                simp only [dfsRowFwd, hult, hgetm, hgm, hgetv, hgv,
                  Bool.false_eq_true, ite_true, ite_false]
              rw [hfwd1] at hfwd
              rw [hloop]
              exact ih _ _ _ _ _ hvislen hstlen hfwd
        · have hfalseM : (g != (BitVec.ofNat 32 0)) = false :=
            Bool.eq_false_of_ne_true hgm
          have hb : evalStmtFuel F dfsInnerBody
              (mkDfsEnv mL visL stL n src top count v u) =
              .ok (mkDfsEnv mL visL stL n src top count v (u + 1),
                .fellThrough) := by
            have h := dfsInnerBody_eval F mL visL stL n src top count
              v u hmen hvislen hstlen
            simp only [hgetm, hfalseM] at h
            exact h
          have hloop : evalStmtFuel (F + 1) dfsInner
              (mkDfsEnv mL visL stL n src top count v u) =
              evalStmtFuel F dfsInner
                (mkDfsEnv mL visL stL n src top count v (u + 1)) := by
            simp only [dfsInner, evalStmtFuel, evalStmtSuccHandler,
              evalStmtWith, hcondT, hb]
          have hfwd1 : dfsRowFwd (F + 1) mL visL stL n v top count u =
              dfsRowFwd F mL visL stL n v top count (u + 1) := by
            simp only [dfsRowFwd, hult, hgetm, hgm, Bool.false_eq_true,
              ite_true, ite_false]
          rw [hfwd1] at hfwd
          rw [hloop]
          exact ih _ _ _ _ _ hvislen hstlen hfwd
    · have hultF : (u.ult n) = false := Bool.eq_false_of_ne_true hult
      have hcond : evalExpr (.ult (.var "u") (.var "n"))
          (mkDfsEnv mL visL stL n src top count v u) = .ok (.b false) := by
        have h := evalExpr_ult_u64 _ _ _ _ _ huvar hnvar
        rw [hultF] at h
        exact h
      have hev : evalStmtFuel (F + 1) dfsInner
          (mkDfsEnv mL visL stL n src top count v u) =
          .ok (mkDfsEnv mL visL stL n src top count v u, .fellThrough) := by
        simp [dfsInner, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond]
      have hfw : dfsRowFwd (F + 1) mL visL stL n v top count u =
          .ok (visL, stL, top, count, u) := by
        simp only [dfsRowFwd, hult, Bool.false_eq_true, ite_true, ite_false]
      rw [hfw] at hfwd
      cases hfwd

/-- One drain iteration with the guard holding: pop, widen, reset `u`,
    then hand off to the row scan (any fuel). -/
theorem dfsOuterBody_ok (F : Nat) (mL visL stL : List (BitVec 32))
    (n src top count v u : BitVec 64)
    (w : BitVec 32) (hget : stL[(top - 1).toNat]? = some w)
    (hg : ((top - 1).ult (BitVec.ofNat 64 stL.length)) = true) :
    evalStmtFuel F dfsOuterBody
      (mkDfsEnv mL visL stL n src top count v u) =
      evalStmtFuel F dfsInner
        (mkDfsEnv mL visL stL n src (top - 1) count (w.signExtend 64) 0) := by
  have hbody : dfsOuterBody =
      .seq (.assign "top" (.usub (.var "top")
              (.lit (.u64 (BitVec.ofNat 64 1)))))
      (.seq (.if_ (.ult (.var "top") (.stdVecLen "st"))
              (.assign "v" (.u64ofI32 (.stdVecAt "st" (.var "top"))))
              .fail)
      (.seq (.assign "u" (.lit (.u64 (BitVec.ofNat 64 0))))
        dfsInner)) := rfl
  have htop : evalExpr (.var "top")
      (mkDfsEnv mL visL stL n src top count v u) = .ok (.u64 top) :=
    evalExpr_var_hit _ _ _ (mkDfsEnv_top mL visL stL n src top count v u)
  have hone : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
      (mkDfsEnv mL visL stL n src top count v u) =
      .ok (.u64 (BitVec.ofNat 64 1)) := by
    simp [evalExpr, litVal]
  have hsub := evalExpr_u64_usub top 1 (.var "top")
    (mkDfsEnv mL visL stL n src top count v u) htop
  have hupop : envUpdate (mkDfsEnv mL visL stL n src top count v u) "top"
      (.u64 (top - 1)) =
      some (mkDfsEnv mL visL stL n src (top - 1) count v u) := by
    simp [mkDfsEnv, envUpdate,
      show ("u" : String) ≠ "top" by decide,
      show ("v" : String) ≠ "top" by decide,
      show ("count" : String) ≠ "top" by decide]
  have hpop := evalStmtFuel_assign F "top"
    (.usub (.var "top") (.lit (.u64 (BitVec.ofNat 64 1))))
    (mkDfsEnv mL visL stL n src top count v u) _ _ hsub hupop
  have htop1 : evalExpr (.var "top")
      (mkDfsEnv mL visL stL n src (top - 1) count v u) =
      .ok (.u64 (top - 1)) :=
    evalExpr_var_hit _ _ _
      (mkDfsEnv_top mL visL stL n src (top - 1) count v u)
  have hlen : evalExpr (.stdVecLen "st")
      (mkDfsEnv mL visL stL n src (top - 1) count v u) =
      .ok (.u64 (BitVec.ofNat 64 stL.length)) :=
    evalExpr_stdVecLen_some "st" _
      stL (mkDfsEnv_st mL visL stL n src (top - 1) count v u)
  have hguard : evalExpr (.ult (.var "top") (.stdVecLen "st"))
      (mkDfsEnv mL visL stL n src (top - 1) count v u) =
      .ok (.b true) := by
    have h := evalExpr_ult_u64 _ _ _ _ _ htop1 hlen
    rw [hg] at h
    exact h
  have hvec := mkDfsEnv_st mL visL stL n src (top - 1) count v u
  have hread : evalExpr (.stdVecAt "st" (.var "top"))
      (mkDfsEnv mL visL stL n src (top - 1) count v u) = .ok (.i32 w) :=
    evalExpr_stdVecAt_some "st" _ _ _ _ _ hvec htop1 hget
  have hwide := evalExpr_u64ofI32_ok _ _ _ hread
  have huv : envUpdate
      (mkDfsEnv mL visL stL n src (top - 1) count v u) "v"
      (.u64 (w.signExtend 64)) =
      some (mkDfsEnv mL visL stL n src (top - 1) count
        (w.signExtend 64) u) := by
    simp [mkDfsEnv, envUpdate,
      show ("u" : String) ≠ "v" by decide]
  have hassignV := evalStmtFuel_assign F "v"
    (.u64ofI32 (.stdVecAt "st" (.var "top")))
    (mkDfsEnv mL visL stL n src (top - 1) count v u) _ _ hwide huv
  have hzero : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
      (mkDfsEnv mL visL stL n src (top - 1) count
        (w.signExtend 64) u) = .ok (.u64 (BitVec.ofNat 64 0)) := by
    simp [evalExpr, litVal]
  have huu : envUpdate
      (mkDfsEnv mL visL stL n src (top - 1) count (w.signExtend 64) u) "u"
      (.u64 (BitVec.ofNat 64 0)) =
      some (mkDfsEnv mL visL stL n src (top - 1) count
        (w.signExtend 64) 0) := by
    simp [mkDfsEnv, envUpdate]
  have hassignU := evalStmtFuel_assign F "u"
    (.lit (.u64 (BitVec.ofNat 64 0)))
    (mkDfsEnv mL visL stL n src (top - 1) count (w.signExtend 64) u)
    _ _ hzero huu
  have hifV := (evalStmtFuel_if_true F _
    (.assign "v" (.u64ofI32 (.stdVecAt "st" (.var "top")))) .fail _
    hguard).trans hassignV
  have hseqU := evalStmtFuel_seq_fallthrough F _ dfsInner _ _ hassignU
  have htail : evalStmtFuel F
      (.seq (.assign "u" (.lit (.u64 (BitVec.ofNat 64 0)))) dfsInner)
      (mkDfsEnv mL visL stL n src (top - 1) count
        (w.signExtend 64) u) =
      evalStmtFuel F dfsInner
        (mkDfsEnv mL visL stL n src (top - 1) count
          (w.signExtend 64) 0) :=
    hseqU
  have hmid : evalStmtFuel F
      (.seq (.if_ (.ult (.var "top") (.stdVecLen "st"))
              (.assign "v" (.u64ofI32 (.stdVecAt "st" (.var "top"))))
              .fail)
        (.seq (.assign "u" (.lit (.u64 (BitVec.ofNat 64 0)))) dfsInner))
      (mkDfsEnv mL visL stL n src (top - 1) count v u) =
      evalStmtFuel F dfsInner
        (mkDfsEnv mL visL stL n src (top - 1) count
          (w.signExtend 64) 0) :=
    (evalStmtFuel_seq_fallthrough F _ _ _ _ hifV).trans htail
  rw [hbody]
  exact (evalStmtFuel_seq_fallthrough F _ _ _ _ hpop).trans hmid

/-- One drain iteration with a dead stack slot aborts loudly. -/
theorem dfsOuterBody_miss (F : Nat) (mL visL stL : List (BitVec 32))
    (n src top count v u : BitVec 64)
    (hg : ((top - 1).ult (BitVec.ofNat 64 stL.length)) = false) :
    evalStmtFuel F dfsOuterBody
      (mkDfsEnv mL visL stL n src top count v u) =
      .error .AssertFail := by
  have hbody : dfsOuterBody =
      .seq (.assign "top" (.usub (.var "top")
              (.lit (.u64 (BitVec.ofNat 64 1)))))
      (.seq (.if_ (.ult (.var "top") (.stdVecLen "st"))
              (.assign "v" (.u64ofI32 (.stdVecAt "st" (.var "top"))))
              .fail)
      (.seq (.assign "u" (.lit (.u64 (BitVec.ofNat 64 0))))
        dfsInner)) := rfl
  have htop : evalExpr (.var "top")
      (mkDfsEnv mL visL stL n src top count v u) = .ok (.u64 top) :=
    evalExpr_var_hit _ _ _ (mkDfsEnv_top mL visL stL n src top count v u)
  have hsub := evalExpr_u64_usub top 1 (.var "top")
    (mkDfsEnv mL visL stL n src top count v u) htop
  have hupop : envUpdate (mkDfsEnv mL visL stL n src top count v u) "top"
      (.u64 (top - 1)) =
      some (mkDfsEnv mL visL stL n src (top - 1) count v u) := by
    simp [mkDfsEnv, envUpdate,
      show ("u" : String) ≠ "top" by decide,
      show ("v" : String) ≠ "top" by decide,
      show ("count" : String) ≠ "top" by decide]
  have hpop := evalStmtFuel_assign F "top"
    (.usub (.var "top") (.lit (.u64 (BitVec.ofNat 64 1))))
    (mkDfsEnv mL visL stL n src top count v u) _ _ hsub hupop
  have htop1 : evalExpr (.var "top")
      (mkDfsEnv mL visL stL n src (top - 1) count v u) =
      .ok (.u64 (top - 1)) :=
    evalExpr_var_hit _ _ _
      (mkDfsEnv_top mL visL stL n src (top - 1) count v u)
  have hlen : evalExpr (.stdVecLen "st")
      (mkDfsEnv mL visL stL n src (top - 1) count v u) =
      .ok (.u64 (BitVec.ofNat 64 stL.length)) :=
    evalExpr_stdVecLen_some "st" _
      stL (mkDfsEnv_st mL visL stL n src (top - 1) count v u)
  have hguard : evalExpr (.ult (.var "top") (.stdVecLen "st"))
      (mkDfsEnv mL visL stL n src (top - 1) count v u) =
      .ok (.b false) := by
    have h := evalExpr_ult_u64 _ _ _ _ _ htop1 hlen
    rw [hg] at h
    exact h
  have hif := (evalStmtFuel_if_false F _
    (.assign "v" (.u64ofI32 (.stdVecAt "st" (.var "top")))) .fail _
    hguard).trans (evalStmtFuel_fail F _)
  have hmid : evalStmtFuel F
      (.seq (.if_ (.ult (.var "top") (.stdVecLen "st"))
              (.assign "v" (.u64ofI32 (.stdVecAt "st" (.var "top"))))
              .fail)
        (.seq (.assign "u" (.lit (.u64 (BitVec.ofNat 64 0)))) dfsInner))
      (mkDfsEnv mL visL stL n src (top - 1) count v u) =
      .error .AssertFail := by
    exact evalStmtFuel_seq_err F _ _ _ _ hif
  rw [hbody]
  exact (evalStmtFuel_seq_fallthrough F _ _ _ _ hpop).trans hmid

/-- An ok row scan only ever stores through `vecSet`: both list
    lengths are preserved (feeds the outer loop's bound refresh). -/
theorem dfsRow_ok_len (F : Nat) (mL visL stL : List (BitVec 32))
    (n v top count u : BitVec 64)
    (vis' stL' : List (BitVec 32)) (top' count' u' : BitVec 64)
    (hfwd : dfsRowFwd F mL visL stL n v top count u =
      .ok (vis', stL', top', count', u')) :
    vis'.length = visL.length ∧ stL'.length = stL.length := by
  induction F generalizing visL stL top count u with
  | zero =>
    by_cases hult : u.ult n = true
    · have hcon : dfsRowFwd 0 mL visL stL n v top count u =
          .error .AssertFail := by
        simp only [dfsRowFwd, hult, ite_true, ite_false]
      rw [hcon] at hfwd
      cases hfwd
    · have hfw : dfsRowFwd 0 mL visL stL n v top count u =
          .ok (visL, stL, top, count, u) := by
        simp only [dfsRowFwd, hult, Bool.false_eq_true, ite_true, ite_false]
      rw [hfw] at hfwd
      cases hfwd
      exact ⟨rfl, rfl⟩
  | succ F ih =>
    by_cases hult : u.ult n = true
    · match hgetm : mL[(v * n + u).toNat]? with
      | none =>
        have hcon : dfsRowFwd (F + 1) mL visL stL n v top count u =
            .error .AssertFail := by
          simp only [dfsRowFwd, hult, hgetm, ite_true, ite_false]
        rw [hcon] at hfwd
        cases hfwd
      | some g =>
        by_cases hgm : g != (BitVec.ofNat 32 0)
        · match hgetv : visL[u.toNat]? with
          | none =>
            have hcon : dfsRowFwd (F + 1) mL visL stL n v top count u =
                .error .AssertFail := by
              simp only [dfsRowFwd, hult, hgetm, hgm, hgetv, ite_true,
                ite_false]
            rw [hcon] at hfwd
            cases hfwd
          | some w =>
            by_cases hgv : w == (BitVec.ofNat 32 0)
            · match hgetst : stL[top.toNat]? with
              | none =>
                have hcon : dfsRowFwd (F + 1) mL visL stL n v top count u =
                    .error .AssertFail := by
                  simp only [dfsRowFwd, hult, hgetm, hgm, hgetv, hgv,
                    hgetst, ite_true, ite_false]
                rw [hcon] at hfwd
                cases hfwd
              | some _ =>
                have hfwd1 : dfsRowFwd (F + 1) mL visL stL n v top count u =
                    dfsRowFwd F mL (visL.set u.toNat 1)
                      (stL.set top.toNat (BitVec.ofNat 32 u.toNat))
                      n v (top + 1) (count + 1) (u + 1) := by
                  simp only [dfsRowFwd, hult, hgetm, hgm, hgetv, hgv,
                    hgetst, ite_true, ite_false]
                rw [hfwd1] at hfwd
                have hih := ih _ _ _ _ _ hfwd
                simp only [List.length_set] at hih
                exact hih
            · have hfwd1 : dfsRowFwd (F + 1) mL visL stL n v top count u =
                  dfsRowFwd F mL visL stL n v top count (u + 1) := by
                simp only [dfsRowFwd, hult, hgetm, hgm, hgetv, hgv,
                  Bool.false_eq_true, ite_true, ite_false]
              rw [hfwd1] at hfwd
              exact ih _ _ _ _ _ hfwd
        · have hfwd1 : dfsRowFwd (F + 1) mL visL stL n v top count u =
              dfsRowFwd F mL visL stL n v top count (u + 1) := by
            simp only [dfsRowFwd, hult, hgetm, hgm, Bool.false_eq_true,
              ite_true, ite_false]
          rw [hfwd1] at hfwd
          exact ih _ _ _ _ _ hfwd
    · have hfw : dfsRowFwd (F + 1) mL visL stL n v top count u =
          .ok (visL, stL, top, count, u) := by
        simp only [dfsRowFwd, hult, Bool.false_eq_true, ite_true, ite_false]
      rw [hfw] at hfwd
      cases hfwd
      exact ⟨rfl, rfl⟩

/-- The stack drain at fuel `F`: evaluator agrees with the forward on
    every `.ok` run. -/
theorem dfsOuter_ok (F : Nat) (mL visL stL : List (BitVec 32))
    (n src top count v u : BitVec 64)
    (hmen : mL.length < 2 ^ 64) (hvislen : visL.length < 2 ^ 64)
    (hstlen : stL.length < 2 ^ 64)
    (vis' stL' : List (BitVec 32)) (top' count' v' u' : BitVec 64)
    (hfwd : dfsOuterFwd F mL visL stL n top count v u =
      .ok (vis', stL', top', count', v', u')) :
    evalStmtFuel F dfsOuter (mkDfsEnv mL visL stL n src top count v u) =
      .ok (mkDfsEnv mL vis' stL' n src top' count' v' u', .fellThrough) := by
  induction F generalizing visL stL top count v u vis' stL' top' count' v' u' with
  | zero =>
    have htopvar : evalExpr (.var "top")
        (mkDfsEnv mL visL stL n src top count v u) = .ok (.u64 top) :=
      evalExpr_var_hit _ _ _ (mkDfsEnv_top mL visL stL n src top count v u)
    have hzero0 : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (mkDfsEnv mL visL stL n src top count v u) =
        .ok (.u64 (BitVec.ofNat 64 0)) := by
      simp [evalExpr, litVal]
    by_cases htopne : top != (BitVec.ofNat 64 0)
    · have hcon : dfsOuterFwd 0 mL visL stL n top count v u =
          .error .AssertFail := by
        simp only [dfsOuterFwd, htopne, ite_true, ite_false]
      rw [hcon] at hfwd
      cases hfwd
    · have hfalse : (top != (BitVec.ofNat 64 0)) = false :=
        Bool.eq_false_of_ne_true htopne
      have hcond : evalExpr (.une (.var "top")
          (.lit (.u64 (BitVec.ofNat 64 0))))
          (mkDfsEnv mL visL stL n src top count v u) =
          .ok (.b false) := by
        have h := evalExpr_une_u64 _ _ _ _ _ htopvar hzero0
        rw [hfalse] at h
        exact h
      have hev : evalStmtFuel 0 dfsOuter
          (mkDfsEnv mL visL stL n src top count v u) =
          .ok (mkDfsEnv mL visL stL n src top count v u, .fellThrough) :=
        evalStmtFuel_zero_while_exit _ _ _ hcond
      have hfw : dfsOuterFwd 0 mL visL stL n top count v u =
          .ok (visL, stL, top, count, v, u) := by
        simp only [dfsOuterFwd, htopne, Bool.false_eq_true, ite_true,
          ite_false]
      rw [hfw] at hfwd
      cases hfwd
      exact hev
  | succ F ih =>
    have htopvar : evalExpr (.var "top")
        (mkDfsEnv mL visL stL n src top count v u) = .ok (.u64 top) :=
      evalExpr_var_hit _ _ _ (mkDfsEnv_top mL visL stL n src top count v u)
    have hzero0 : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (mkDfsEnv mL visL stL n src top count v u) =
        .ok (.u64 (BitVec.ofNat 64 0)) := by
      simp [evalExpr, litVal]
    by_cases htopne : top != (BitVec.ofNat 64 0)
    · have hcondT : evalExpr (.une (.var "top")
          (.lit (.u64 (BitVec.ofNat 64 0))))
          (mkDfsEnv mL visL stL n src top count v u) =
          .ok (.b true) := by
        have h := evalExpr_une_u64 _ _ _ _ _ htopvar hzero0
        rw [htopne] at h
        exact h
      match hget : stL[(top - 1).toNat]? with
      | none =>
        have hcon : dfsOuterFwd (F + 1) mL visL stL n top count v u =
            .error .AssertFail := by
          simp only [dfsOuterFwd, htopne, hget, ite_true, ite_false]
        rw [hcon] at hfwd
        cases hfwd
      | some w =>
        have hlt : (top - 1).toNat < stL.length := getElem_some_lt hget
        have hgT : ((top - 1).ult
            (BitVec.ofNat 64 stL.length)) = true := by
          have h2 : decide ((top - 1).toNat <
              (BitVec.ofNat 64 stL.length).toNat) = true := by
            rw [ofNat64_toNat _ hstlen]
            exact decide_eq_true hlt
          rwa [← BitVec.ult_eq_decide] at h2
        have hbody := dfsOuterBody_ok F mL visL stL n src top count v u
          w hget hgT
        match hrow : dfsRowFwd F mL visL stL n (w.signExtend 64)
            (top - 1) count 0 with
        | .error e =>
          have hcon : dfsOuterFwd (F + 1) mL visL stL n top count v u =
              .error e := by
            simp only [dfsOuterFwd, htopne, hget, hrow, ite_true, ite_false]
          rw [hcon] at hfwd
          cases hfwd
        | .ok (vis1, st1, top1, count1, u1) =>
          have hrowO := dfsRow_ok F mL visL stL n src (top - 1) count
            (w.signExtend 64) 0 hmen hvislen hstlen _ _ _ _ _ hrow
          have hbev : evalStmtFuel F dfsOuterBody
              (mkDfsEnv mL visL stL n src top count v u) =
              .ok (mkDfsEnv mL vis1 st1 n src top1 count1
                (w.signExtend 64) u1, .fellThrough) :=
            hbody.trans hrowO
          have hloop : evalStmtFuel (F + 1) dfsOuter
              (mkDfsEnv mL visL stL n src top count v u) =
              evalStmtFuel F dfsOuter
                (mkDfsEnv mL vis1 st1 n src top1 count1
                  (w.signExtend 64) u1) := by
            simp only [dfsOuter, evalStmtFuel, evalStmtSuccHandler,
              evalStmtWith, hcondT, hbev]
          have hfwd1 : dfsOuterFwd (F + 1) mL visL stL n top count v u =
              dfsOuterFwd F mL vis1 st1 n top1 count1
                (w.signExtend 64) u1 := by
            simp only [dfsOuterFwd, htopne, hget, hrow, ite_true, ite_false]
          rw [hfwd1] at hfwd
          rw [hloop]
          have hlen := dfsRow_ok_len F mL visL stL n (w.signExtend 64)
            (top - 1) count 0 _ _ _ _ _ hrow
          have hvislen1 : vis1.length < 2 ^ 64 := by
            rw [hlen.1]; exact hvislen
          have hstlen1 : st1.length < 2 ^ 64 := by
            rw [hlen.2]; exact hstlen
          exact ih _ _ _ _ _ _ hvislen1 hstlen1 _ _ _ _ _ _ hfwd
    · have hfalse : (top != (BitVec.ofNat 64 0)) = false :=
        Bool.eq_false_of_ne_true htopne
      have hcond : evalExpr (.une (.var "top")
          (.lit (.u64 (BitVec.ofNat 64 0))))
          (mkDfsEnv mL visL stL n src top count v u) =
          .ok (.b false) := by
        have h := evalExpr_une_u64 _ _ _ _ _ htopvar hzero0
        rw [hfalse] at h
        exact h
      have hev : evalStmtFuel (F + 1) dfsOuter
          (mkDfsEnv mL visL stL n src top count v u) =
          .ok (mkDfsEnv mL visL stL n src top count v u, .fellThrough) := by
        simp [dfsOuter, evalStmtFuel, evalStmtSuccHandler, evalStmtWith,
          hcond]
      have hfw : dfsOuterFwd (F + 1) mL visL stL n top count v u =
          .ok (visL, stL, top, count, v, u) := by
        simp only [dfsOuterFwd, htopne, Bool.false_eq_true, ite_true,
          ite_false]
      rw [hfw] at hfwd
      cases hfwd
      exact hev

/-- The stack drain at fuel `F`: evaluator agrees with the forward on
    every `.error` run. -/
theorem dfsOuter_err (F : Nat) (mL visL stL : List (BitVec 32))
    (n src top count v u : BitVec 64)
    (hmen : mL.length < 2 ^ 64) (hvislen : visL.length < 2 ^ 64)
    (hstlen : stL.length < 2 ^ 64)
    (e : Panic)
    (hfwd : dfsOuterFwd F mL visL stL n top count v u = .error e) :
    evalStmtFuel F dfsOuter (mkDfsEnv mL visL stL n src top count v u) =
      .error e := by
  induction F generalizing visL stL top count v u with
  | zero =>
    have htopvar : evalExpr (.var "top")
        (mkDfsEnv mL visL stL n src top count v u) = .ok (.u64 top) :=
      evalExpr_var_hit _ _ _ (mkDfsEnv_top mL visL stL n src top count v u)
    have hzero0 : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (mkDfsEnv mL visL stL n src top count v u) =
        .ok (.u64 (BitVec.ofNat 64 0)) := by
      simp [evalExpr, litVal]
    by_cases htopne : top != (BitVec.ofNat 64 0)
    · have hcond : evalExpr (.une (.var "top")
          (.lit (.u64 (BitVec.ofNat 64 0))))
          (mkDfsEnv mL visL stL n src top count v u) =
          .ok (.b true) := by
        have h := evalExpr_une_u64 _ _ _ _ _ htopvar hzero0
        rw [htopne] at h
        exact h
      have hev : evalStmtFuel 0 dfsOuter
          (mkDfsEnv mL visL stL n src top count v u) =
          .error .AssertFail :=
        evalStmtFuel_zero_while_enter _ _ _ hcond
      have hcon : dfsOuterFwd 0 mL visL stL n top count v u =
          .error .AssertFail := by
        simp only [dfsOuterFwd, htopne, ite_true, ite_false]
      rw [hcon] at hfwd
      cases hfwd
      exact hev
    · have hfw : dfsOuterFwd 0 mL visL stL n top count v u =
          .ok (visL, stL, top, count, v, u) := by
        simp only [dfsOuterFwd, htopne, Bool.false_eq_true, ite_true,
          ite_false]
      rw [hfw] at hfwd
      cases hfwd
  | succ F ih =>
    have htopvar : evalExpr (.var "top")
        (mkDfsEnv mL visL stL n src top count v u) = .ok (.u64 top) :=
      evalExpr_var_hit _ _ _ (mkDfsEnv_top mL visL stL n src top count v u)
    have hzero0 : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
        (mkDfsEnv mL visL stL n src top count v u) =
        .ok (.u64 (BitVec.ofNat 64 0)) := by
      simp [evalExpr, litVal]
    by_cases htopne : top != (BitVec.ofNat 64 0)
    · have hcondT : evalExpr (.une (.var "top")
          (.lit (.u64 (BitVec.ofNat 64 0))))
          (mkDfsEnv mL visL stL n src top count v u) =
          .ok (.b true) := by
        have h := evalExpr_une_u64 _ _ _ _ _ htopvar hzero0
        rw [htopne] at h
        exact h
      match hget : stL[(top - 1).toNat]? with
      | none =>
        have hnot : ¬ (top - 1).toNat < stL.length := by
          intro hcon
          have hne : stL[(top - 1).toNat]? ≠ none := by
            rw [ne_eq, List.getElem?_eq_none_iff]
            omega
          exact hne hget
        have hgF : ((top - 1).ult
            (BitVec.ofNat 64 stL.length)) = false := by
          have h1 : ¬ (top - 1).toNat <
              (BitVec.ofNat 64 stL.length).toNat := by
            rw [ofNat64_toNat _ hstlen]
            exact hnot
          have h2 : decide ((top - 1).toNat <
              (BitVec.ofNat 64 stL.length).toNat) = false :=
            decide_eq_false h1
          rwa [← BitVec.ult_eq_decide] at h2
        have hcon : dfsOuterFwd (F + 1) mL visL stL n top count v u =
            .error .AssertFail := by
          simp only [dfsOuterFwd, htopne, hget, ite_true, ite_false]
        have hbev : evalStmtFuel F dfsOuterBody
            (mkDfsEnv mL visL stL n src top count v u) =
            .error .AssertFail :=
          dfsOuterBody_miss F mL visL stL n src top count v u hgF
        have hev : evalStmtFuel (F + 1) dfsOuter
            (mkDfsEnv mL visL stL n src top count v u) =
            .error .AssertFail := by
          simp only [dfsOuter, evalStmtFuel, evalStmtSuccHandler,
            evalStmtWith, hcondT, hbev]
        rw [hcon] at hfwd
        cases hfwd
        exact hev
      | some w =>
        have hlt : (top - 1).toNat < stL.length := getElem_some_lt hget
        have hgT : ((top - 1).ult
            (BitVec.ofNat 64 stL.length)) = true := by
          have h2 : decide ((top - 1).toNat <
              (BitVec.ofNat 64 stL.length).toNat) = true := by
            rw [ofNat64_toNat _ hstlen]
            exact decide_eq_true hlt
          rwa [← BitVec.ult_eq_decide] at h2
        have hbody := dfsOuterBody_ok F mL visL stL n src top count v u
          w hget hgT
        match hrow : dfsRowFwd F mL visL stL n (w.signExtend 64)
            (top - 1) count 0 with
        | .error e' =>
          have hcon : dfsOuterFwd (F + 1) mL visL stL n top count v u =
              .error e' := by
            simp only [dfsOuterFwd, htopne, hget, hrow, ite_true, ite_false]
          have hrowE := dfsRow_err F mL visL stL n src (top - 1) count
            (w.signExtend 64) 0 hmen hvislen hstlen _ hrow
          have hbev : evalStmtFuel F dfsOuterBody
              (mkDfsEnv mL visL stL n src top count v u) = .error e' :=
            hbody.trans hrowE
          have hev : evalStmtFuel (F + 1) dfsOuter
              (mkDfsEnv mL visL stL n src top count v u) = .error e' := by
            simp only [dfsOuter, evalStmtFuel, evalStmtSuccHandler,
              evalStmtWith, hcondT, hbev]
          rw [hcon] at hfwd
          cases hfwd
          exact hev
        | .ok (vis1, st1, top1, count1, u1) =>
          have hrowO := dfsRow_ok F mL visL stL n src (top - 1) count
            (w.signExtend 64) 0 hmen hvislen hstlen _ _ _ _ _ hrow
          have hbev : evalStmtFuel F dfsOuterBody
              (mkDfsEnv mL visL stL n src top count v u) =
              .ok (mkDfsEnv mL vis1 st1 n src top1 count1
                (w.signExtend 64) u1, .fellThrough) :=
            hbody.trans hrowO
          have hloop : evalStmtFuel (F + 1) dfsOuter
              (mkDfsEnv mL visL stL n src top count v u) =
              evalStmtFuel F dfsOuter
                (mkDfsEnv mL vis1 st1 n src top1 count1
                  (w.signExtend 64) u1) := by
            simp only [dfsOuter, evalStmtFuel, evalStmtSuccHandler,
              evalStmtWith, hcondT, hbev]
          have hfwd1 : dfsOuterFwd (F + 1) mL visL stL n top count v u =
              dfsOuterFwd F mL vis1 st1 n top1 count1
                (w.signExtend 64) u1 := by
            simp only [dfsOuterFwd, htopne, hget, hrow, ite_true, ite_false]
          rw [hfwd1] at hfwd
          rw [hloop]
          have hlen := dfsRow_ok_len F mL visL stL n (w.signExtend 64)
            (top - 1) count 0 _ _ _ _ _ hrow
          have hvislen1 : vis1.length < 2 ^ 64 := by
            rw [hlen.1]; exact hvislen
          have hstlen1 : st1.length < 2 ^ 64 := by
            rw [hlen.2]; exact hstlen
          exact ih _ _ _ _ _ _ hvislen1 hstlen1 hfwd
    · have hfw : dfsOuterFwd (F + 1) mL visL stL n top count v u =
          .ok (visL, stL, top, count, v, u) := by
        simp only [dfsOuterFwd, htopne, Bool.false_eq_true, ite_true,
          ite_false]
      rw [hfw] at hfwd
      cases hfwd

/-- Seed with both slots live: the two guarded stores plus the four
    cursor bindings (any fuel). -/
theorem dfsSeed_ok (F : Nat) (mL visL stL : List (BitVec 32))
    (n src : BitVec 64)
    (hvislen : visL.length < 2 ^ 64) (hstlen : stL.length < 2 ^ 64)
    (vis1 st1 : List (BitVec 32))
    (hfwd : dfsSeedFwd visL stL src = .ok (vis1, st1)) :
    evalStmtFuel F dfsSeed
      [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
        ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
      .ok (mkDfsEnv mL vis1 st1 n src 1 1 0 0, .fellThrough) := by
  have hseed : dfsSeed =
      .seq (.if_ (.ult (.var "src") (.stdVecLen "vis"))
              (.vecSet "vis" (.var "src") (.lit (.i32 1)))
              .fail)
      (.seq (.if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "st"))
              (.vecSet "st" (.lit (.u64 (BitVec.ofNat 64 0)))
                (.i32ofU64 (.var "src")))
              .fail)
      (.seq (.let_ "top" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      (.seq (.let_ "count" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      (.seq (.let_ "v" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.let_ "u" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0)))))))) := rfl
  match hvis : visL[src.toNat]? with
  | none =>
    have hcon : dfsSeedFwd visL stL src = .error .AssertFail := by
      simp only [dfsSeedFwd, hvis, ite_true, ite_false]
    rw [hcon] at hfwd
    cases hfwd
  | some w =>
    match hst : stL[(BitVec.ofNat 64 0).toNat]? with
    | none =>
      have hcon : dfsSeedFwd visL stL src = .error .AssertFail := by
        simp only [dfsSeedFwd, hvis, hst, ite_true, ite_false]
      rw [hcon] at hfwd
      cases hfwd
    | some wst =>
      have hcon : dfsSeedFwd visL stL src =
          .ok (visL.set src.toNat 1,
            stL.set 0 (BitVec.ofNat 32 src.toNat)) := by
        simp only [dfsSeedFwd, hvis, hst, ite_true, ite_false]
      rw [hcon] at hfwd
      cases hfwd
      have hsrc : evalExpr (.var "src")
          [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
            ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
          .ok (.u64 src) :=
        evalExpr_var_hit _ _ _
          (by simp [envLookup,
            show ("src" : String) ≠ "m" by decide,
            show ("src" : String) ≠ "vis" by decide,
            show ("src" : String) ≠ "st" by decide,
            show ("src" : String) ≠ "n" by decide])
      have hvislen0 : evalExpr (.stdVecLen "vis")
          [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
            ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
          .ok (.u64 (BitVec.ofNat 64 visL.length)) :=
        evalExpr_stdVecLen_some "vis" _ _
          (by simp [envLookup,
            show ("vis" : String) ≠ "m" by decide])
      have hltv : src.toNat < visL.length := getElem_some_lt hvis
      have hguardV : evalExpr (.ult (.var "src") (.stdVecLen "vis"))
          [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
            ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
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
            ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
          .ok (.i32 1) := by
        simp [evalExpr, litVal]
      have hstoreV := evalStmtFuel_vecSet F "vis" (.var "src")
        (.lit (.i32 (1 : BitVec 32)))
        [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
          ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)]
        src 1 visL w
        [("m", .stdVecVal mL), ("vis", .stdVecVal (visL.set src.toNat 1)),
          ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)]
        hsrc hx1
        (by simp [envLookup,
          show ("vis" : String) ≠ "m" by decide])
        hvis
        (by simp [envUpdate,
          show ("vis" : String) ≠ "m" by decide])
      have hstlen1 : evalExpr (.stdVecLen "st")
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
          .ok (.u64 (BitVec.ofNat 64 stL.length)) :=
        evalExpr_stdVecLen_some "st" _ _
          (by simp [envLookup,
            show ("st" : String) ≠ "m" by decide,
            show ("st" : String) ≠ "vis" by decide])
      have hltst : (BitVec.ofNat 64 0).toNat < stL.length :=
        getElem_some_lt hst
      have hguardS : evalExpr
          (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "st"))
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
          .ok (.b true) := by
        have hlitz : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
            [("m", .stdVecVal mL),
              ("vis", .stdVecVal (visL.set src.toNat 1)),
              ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
            .ok (.u64 (BitVec.ofNat 64 0)) := by
          simp [evalExpr, litVal]
        have h := evalExpr_ult_u64 _ _ _ _ _ hlitz hstlen1
        have h2 : decide ((BitVec.ofNat 64 0).toNat <
            (BitVec.ofNat 64 stL.length).toNat) = true := by
          rw [ofNat64_toNat _ hstlen]
          exact decide_eq_true hltst
        have h3 : (BitVec.ofNat 64 0).ult
            (BitVec.ofNat 64 stL.length) = true := by
          rwa [← BitVec.ult_eq_decide] at h2
        rw [h3] at h
        exact h
      have hsrc1 : evalExpr (.var "src")
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
          .ok (.u64 src) :=
        evalExpr_var_hit _ _ _
          (by simp [envLookup,
            show ("src" : String) ≠ "m" by decide,
            show ("src" : String) ≠ "vis" by decide,
            show ("src" : String) ≠ "st" by decide,
            show ("src" : String) ≠ "n" by decide])
      have hwide := evalExpr_i32ofU64_ok _ _ _ hsrc1
      have hstoreS := evalStmtFuel_vecSet F "st"
        (.lit (.u64 (BitVec.ofNat 64 0))) (.i32ofU64 (.var "src"))
        [("m", .stdVecVal mL),
          ("vis", .stdVecVal (visL.set src.toNat 1)),
          ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)]
        (BitVec.ofNat 64 0) (BitVec.ofNat 32 src.toNat) stL wst
        [("m", .stdVecVal mL),
          ("vis", .stdVecVal (visL.set src.toNat 1)),
          ("st", .stdVecVal (stL.set (BitVec.ofNat 64 0).toNat
            (BitVec.ofNat 32 src.toNat))), ("n", .u64 n),
          ("src", .u64 src)]
        (by simp [evalExpr, litVal]) hwide
        (by simp [envLookup,
          show ("st" : String) ≠ "m" by decide,
          show ("st" : String) ≠ "vis" by decide])
        hst
        (by simp [envUpdate,
          show ("st" : String) ≠ "m" by decide,
          show ("st" : String) ≠ "vis" by decide])
      have hlit1 : evalExpr (.lit (.u64 (BitVec.ofNat 64 1)))
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("st", .stdVecVal (stL.set (BitVec.ofNat 64 0).toNat
              (BitVec.ofNat 32 src.toNat))), ("n", .u64 n),
            ("src", .u64 src)] =
          .ok (.u64 (BitVec.ofNat 64 1)) := by
        simp [evalExpr, litVal]
      have hlit0 : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("st", .stdVecVal (stL.set (BitVec.ofNat 64 0).toNat
              (BitVec.ofNat 32 src.toNat))), ("n", .u64 n),
            ("src", .u64 src)] =
          .ok (.u64 (BitVec.ofNat 64 0)) := by
        simp [evalExpr, litVal]
      have hletT := evalStmtFuel_let_ F "top" (.u 64)
        (.lit (.u64 (BitVec.ofNat 64 1)))
        [("m", .stdVecVal mL),
          ("vis", .stdVecVal (visL.set src.toNat 1)),
          ("st", .stdVecVal (stL.set (BitVec.ofNat 64 0).toNat
            (BitVec.ofNat 32 src.toNat))), ("n", .u64 n),
          ("src", .u64 src)]
        _ hlit1
      have hletC := evalStmtFuel_let_ F "count" (.u 64)
        (.lit (.u64 (BitVec.ofNat 64 1)))
        (envExtend
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("st", .stdVecVal (stL.set (BitVec.ofNat 64 0).toNat
              (BitVec.ofNat 32 src.toNat))), ("n", .u64 n),
            ("src", .u64 src)]
          "top" (.u64 (BitVec.ofNat 64 1)))
        _ hlit1
      have hletV := evalStmtFuel_let_ F "v" (.u 64)
        (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend (envExtend
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("st", .stdVecVal (stL.set (BitVec.ofNat 64 0).toNat
              (BitVec.ofNat 32 src.toNat))), ("n", .u64 n),
            ("src", .u64 src)]
          "top" (.u64 (BitVec.ofNat 64 1)))
          "count" (.u64 (BitVec.ofNat 64 1)))
        _ hlit0
      have hletU := evalStmtFuel_let_ F "u" (.u 64)
        (.lit (.u64 (BitVec.ofNat 64 0)))
        (envExtend (envExtend (envExtend
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("st", .stdVecVal (stL.set (BitVec.ofNat 64 0).toNat
              (BitVec.ofNat 32 src.toNat))), ("n", .u64 n),
            ("src", .u64 src)]
          "top" (.u64 (BitVec.ofNat 64 1)))
          "count" (.u64 (BitVec.ofNat 64 1)))
          "v" (.u64 (BitVec.ofNat 64 0)))
        _ hlit0
      have hfin : envExtend (envExtend (envExtend (envExtend
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("st", .stdVecVal (stL.set (BitVec.ofNat 64 0).toNat
              (BitVec.ofNat 32 src.toNat))), ("n", .u64 n),
            ("src", .u64 src)]
          "top" (.u64 (BitVec.ofNat 64 1)))
          "count" (.u64 (BitVec.ofNat 64 1)))
          "v" (.u64 (BitVec.ofNat 64 0)))
          "u" (.u64 (BitVec.ofNat 64 0)) =
          mkDfsEnv mL (visL.set src.toNat 1)
            (stL.set (BitVec.ofNat 64 0).toNat
              (BitVec.ofNat 32 src.toNat)) n src 1 1 0 0 := rfl
      have hgateV : evalStmtFuel F
          (.if_ (.ult (.var "src") (.stdVecLen "vis"))
            (.vecSet "vis" (.var "src") (.lit (.i32 1)))
            .fail)
          [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
            ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
          .ok ([("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)],
            .fellThrough) :=
        (evalStmtFuel_if_true F _ _ _ _ hguardV).trans hstoreV
      have hgateS : evalStmtFuel F
          (.if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "st"))
            (.vecSet "st" (.lit (.u64 (BitVec.ofNat 64 0)))
              (.i32ofU64 (.var "src")))
            .fail)
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
          .ok ([("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("st", .stdVecVal (stL.set (BitVec.ofNat 64 0).toNat
              (BitVec.ofNat 32 src.toNat))), ("n", .u64 n),
            ("src", .u64 src)], .fellThrough) :=
        (evalStmtFuel_if_true F _ _ _ _ hguardS).trans hstoreS
      have hletU' : evalStmtFuel F
          (.let_ "u" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
          (envExtend (envExtend (envExtend
            [("m", .stdVecVal mL),
              ("vis", .stdVecVal (visL.set src.toNat 1)),
              ("st", .stdVecVal (stL.set (BitVec.ofNat 64 0).toNat
                (BitVec.ofNat 32 src.toNat))), ("n", .u64 n),
              ("src", .u64 src)]
            "top" (.u64 (BitVec.ofNat 64 1)))
            "count" (.u64 (BitVec.ofNat 64 1)))
            "v" (.u64 (BitVec.ofNat 64 0))) =
          .ok (mkDfsEnv mL (visL.set src.toNat 1)
            (stL.set (BitVec.ofNat 64 0).toNat
              (BitVec.ofNat 32 src.toNat)) n src 1 1 0 0,
            .fellThrough) := by
        rw [← hfin]
        exact hletU
      rw [hseed]
      exact (evalStmtFuel_seq_fallthrough F _ _ _ _ hgateV).trans
        ((evalStmtFuel_seq_fallthrough F _ _ _ _ hgateS).trans
        ((evalStmtFuel_seq_fallthrough F _ _ _ _ hletT).trans
        ((evalStmtFuel_seq_fallthrough F _ _ _ _ hletC).trans
        ((evalStmtFuel_seq_fallthrough F _ _ _ _ hletV).trans
          hletU'))))

/-- Seed with a dead slot aborts loudly (any fuel). -/
theorem dfsSeed_err (F : Nat) (mL visL stL : List (BitVec 32))
    (n src : BitVec 64)
    (hvislen : visL.length < 2 ^ 64) (hstlen : stL.length < 2 ^ 64)
    (e : Panic)
    (hfwd : dfsSeedFwd visL stL src = .error e) :
    evalStmtFuel F dfsSeed
      [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
        ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
      .error e := by
  have hseed : dfsSeed =
      .seq (.if_ (.ult (.var "src") (.stdVecLen "vis"))
              (.vecSet "vis" (.var "src") (.lit (.i32 1)))
              .fail)
      (.seq (.if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "st"))
              (.vecSet "st" (.lit (.u64 (BitVec.ofNat 64 0)))
                (.i32ofU64 (.var "src")))
              .fail)
      (.seq (.let_ "top" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      (.seq (.let_ "count" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
      (.seq (.let_ "v" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
      (.let_ "u" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0)))))))) := rfl
  have hsrc : evalExpr (.var "src")
      [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
        ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
      .ok (.u64 src) :=
    evalExpr_var_hit _ _ _
      (by simp [envLookup,
        show ("src" : String) ≠ "m" by decide,
        show ("src" : String) ≠ "vis" by decide,
        show ("src" : String) ≠ "st" by decide,
        show ("src" : String) ≠ "n" by decide])
  have hvislen0 : evalExpr (.stdVecLen "vis")
      [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
        ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
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
          ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
        .ok (.b false) := by
      have h := evalExpr_ult_u64 _ _ _ _ _ hsrc hvislen0
      rw [hultF] at h
      exact h
    have hcon : dfsSeedFwd visL stL src = .error .AssertFail := by
      simp only [dfsSeedFwd, hvis, ite_true, ite_false]
    have hev : evalStmtFuel F dfsSeed
        [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
          ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
        .error .AssertFail := by
      rw [hseed]
      exact evalStmtFuel_seq_err F _
        (.seq (.if_ (.ult (.lit (.u64 (BitVec.ofNat 64 0)))
                (.stdVecLen "st"))
                (.vecSet "st" (.lit (.u64 (BitVec.ofNat 64 0)))
                  (.i32ofU64 (.var "src")))
                .fail)
        (.seq (.let_ "top" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
        (.seq (.let_ "count" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
        (.seq (.let_ "v" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
        (.let_ "u" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0)))))))) _ _
        ((evalStmtFuel_if_false F _ _ _ _ hguardV).trans
          (evalStmtFuel_fail F _))
    rw [hcon] at hfwd
    cases hfwd
    exact hev
  | some w =>
    match hst : stL[(BitVec.ofNat 64 0).toNat]? with
    | none =>
      have hcon : dfsSeedFwd visL stL src = .error .AssertFail := by
        simp only [dfsSeedFwd, hvis, hst, ite_true, ite_false]
      have hguardV : evalExpr (.ult (.var "src") (.stdVecLen "vis"))
          [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
            ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
          .ok (.b true) := by
        have hltv : src.toNat < visL.length := getElem_some_lt hvis
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
            ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
          .ok (.i32 1) := by
        simp [evalExpr, litVal]
      have hstoreV := evalStmtFuel_vecSet F "vis" (.var "src")
        (.lit (.i32 (1 : BitVec 32)))
        [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
          ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)]
        src 1 visL w
        [("m", .stdVecVal mL), ("vis", .stdVecVal (visL.set src.toNat 1)),
          ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)]
        hsrc hx1
        (by simp [envLookup,
          show ("vis" : String) ≠ "m" by decide])
        hvis
        (by simp [envUpdate,
          show ("vis" : String) ≠ "m" by decide])
      have hnot : ¬ (BitVec.ofNat 64 0).toNat < stL.length := by
        intro hcon
        have hne : stL[(BitVec.ofNat 64 0).toNat]? ≠ none := by
          rw [ne_eq, List.getElem?_eq_none_iff]
          omega
        exact hne hst
      have hultF : (BitVec.ofNat 64 0).ult
          (BitVec.ofNat 64 stL.length) = false := by
        have h1 : ¬ (BitVec.ofNat 64 0).toNat <
            (BitVec.ofNat 64 stL.length).toNat := by
          rw [ofNat64_toNat _ hstlen]
          exact hnot
        have h2 : decide ((BitVec.ofNat 64 0).toNat <
            (BitVec.ofNat 64 stL.length).toNat) = false :=
          decide_eq_false h1
        rwa [← BitVec.ult_eq_decide] at h2
      have hstlen1 : evalExpr (.stdVecLen "st")
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
          .ok (.u64 (BitVec.ofNat 64 stL.length)) :=
        evalExpr_stdVecLen_some "st" _ _
          (by simp [envLookup,
            show ("st" : String) ≠ "m" by decide,
            show ("st" : String) ≠ "vis" by decide])
      have hlitz : evalExpr (.lit (.u64 (BitVec.ofNat 64 0)))
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
          .ok (.u64 (BitVec.ofNat 64 0)) := by
        simp [evalExpr, litVal]
      have hguardS : evalExpr
          (.ult (.lit (.u64 (BitVec.ofNat 64 0))) (.stdVecLen "st"))
          [("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
          .ok (.b false) := by
        have h := evalExpr_ult_u64 _ _ _ _ _ hlitz hstlen1
        rw [hultF] at h
        exact h
      have hgateV : evalStmtFuel F
          (.if_ (.ult (.var "src") (.stdVecLen "vis"))
            (.vecSet "vis" (.var "src") (.lit (.i32 1)))
            .fail)
          [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
            ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
          .ok ([("m", .stdVecVal mL),
            ("vis", .stdVecVal (visL.set src.toNat 1)),
            ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)],
            .fellThrough) :=
        (evalStmtFuel_if_true F _ _ _ _ hguardV).trans hstoreV
      have hev : evalStmtFuel F dfsSeed
          [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
            ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
          .error .AssertFail := by
        rw [hseed]
        exact (evalStmtFuel_seq_fallthrough F _ _ _ _ hgateV).trans
          (evalStmtFuel_seq_err F _
            (.seq (.let_ "top" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
            (.seq (.let_ "count" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
            (.seq (.let_ "v" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
            (.let_ "u" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))))) _ _
            ((evalStmtFuel_if_false F _ _ _ _ hguardS).trans
              (evalStmtFuel_fail F _)))
      rw [hcon] at hfwd
      cases hfwd
      exact hev
    | some wst =>
      have hcon : dfsSeedFwd visL stL src =
          .ok (visL.set src.toNat 1,
            stL.set 0 (BitVec.ofNat 32 src.toNat)) := by
        simp only [dfsSeedFwd, hvis, hst, ite_true, ite_false]
      rw [hcon] at hfwd
      cases hfwd

/-- Seed length preservation (the stores are `vecSet`s). -/
theorem dfsSeed_ok_len (visL stL : List (BitVec 32)) (src : BitVec 64)
    (vis1 st1 : List (BitVec 32))
    (hfwd : dfsSeedFwd visL stL src = .ok (vis1, st1)) :
    vis1.length = visL.length ∧ st1.length = stL.length := by
  match hvis : visL[src.toNat]? with
  | none =>
    have hcon : dfsSeedFwd visL stL src = .error .AssertFail := by
      simp only [dfsSeedFwd, hvis, ite_true, ite_false]
    rw [hcon] at hfwd
    cases hfwd
  | some _ =>
    match hst : stL[(BitVec.ofNat 64 0).toNat]? with
    | none =>
      have hcon : dfsSeedFwd visL stL src = .error .AssertFail := by
        simp only [dfsSeedFwd, hvis, hst, ite_true, ite_false]
      rw [hcon] at hfwd
      cases hfwd
    | some _ =>
      have hcon : dfsSeedFwd visL stL src =
          .ok (visL.set src.toNat 1,
            stL.set 0 (BitVec.ofNat 32 src.toNat)) := by
        simp only [dfsSeedFwd, hvis, hst, ite_true, ite_false]
      rw [hcon] at hfwd
      cases hfwd
      simp [List.length_set]

/-- Whole-function correctness: the evaluator agrees with the forward
    mirror on every input (seed, drain, return). -/
theorem evalFuncFuel_dfs (F : Nat) (mL visL stL : List (BitVec 32))
    (n src : BitVec 64)
    (hmen : mL.length < 2 ^ 64) (hvislen : visL.length < 2 ^ 64)
    (hstlen : stL.length < 2 ^ 64) :
    evalFuncFuel F dfsFunc
      [.stdVecVal mL, .stdVecVal visL, .stdVecVal stL, .u64 n, .u64 src] =
      dfsFwd F mL visL stL n src := by
  have hbind : bindArgs dfsFunc.args
      [.stdVecVal mL, .stdVecVal visL, .stdVecVal stL, .u64 n, .u64 src] =
      some [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
        ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] := rfl
  have hfunc : dfsFunc.body =
      .seq dfsSeed
        (.seq dfsOuter (.return_ (.var "count"))) := rfl
  match hseed : dfsSeedFwd visL stL src with
  | .error e =>
    have hseedE := dfsSeed_err F mL visL stL n src hvislen hstlen _ hseed
    have hstmt : evalStmtFuel F dfsFunc.body
        [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
          ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
        .error e := by
      rw [hfunc]
      exact evalStmtFuel_seq_err F _
        (.seq dfsOuter (.return_ (.var "count"))) _ _ hseedE
    simp only [evalFuncFuel, hbind, hstmt, dfsFwd, hseed]
  | .ok (vis1, st1) =>
    have hseedO := dfsSeed_ok F mL visL stL n src hvislen hstlen _ _ hseed
    have hlen := dfsSeed_ok_len visL stL src _ _ hseed
    have hvislen1 : vis1.length < 2 ^ 64 := by
      rw [hlen.1]; exact hvislen
    have hstlen1 : st1.length < 2 ^ 64 := by
      rw [hlen.2]; exact hstlen
    match houter : dfsOuterFwd F mL vis1 st1 n 1 1 0 0 with
    | .error e =>
      have houterE := dfsOuter_err F mL vis1 st1 n src 1 1 0 0
        hmen hvislen1 hstlen1 _ houter
      have hstmt : evalStmtFuel F dfsFunc.body
          [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
            ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
          .error e := by
        rw [hfunc]
        exact (evalStmtFuel_seq_fallthrough F _ _ _ _ hseedO).trans
          (evalStmtFuel_seq_err F _ (.return_ (.var "count")) _ _ houterE)
      simp only [evalFuncFuel, hbind, hstmt, dfsFwd, hseed, houter]
    | .ok (vis2, st2, top2, count2, v2, u2) =>
      have houterO := dfsOuter_ok F mL vis1 st1 n src 1 1 0 0
        hmen hvislen1 hstlen1 _ _ _ _ _ _ houter
      have hcount : evalExpr (.var "count")
          (mkDfsEnv mL vis2 st2 n src top2 count2 v2 u2) =
          .ok (.u64 count2) :=
        evalExpr_var_hit _ _ _ (mkDfsEnv_count mL vis2 st2 n src top2 count2 v2 u2)
      have hret := evalStmtFuel_return F _ _ _ hcount
      have hstmt : evalStmtFuel F dfsFunc.body
          [("m", .stdVecVal mL), ("vis", .stdVecVal visL),
            ("st", .stdVecVal stL), ("n", .u64 n), ("src", .u64 src)] =
          .ok (mkDfsEnv mL vis2 st2 n src top2 count2 v2 u2,
            .returned (.u64 count2)) := by
        rw [hfunc]
        exact (evalStmtFuel_seq_fallthrough F _ _ _ _ hseedO).trans
          ((evalStmtFuel_seq_fallthrough F _ _ _ _ houterO).trans hret)
      simp only [evalFuncFuel, hbind, hstmt, dfsFwd, hseed, houter]
