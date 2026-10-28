/-
Circe.Emit.VecDfsGrow — G4 iterative DFS over a growing stack:
the `dfs_grow` entry.

The corpus (`tests/cpp/dfs_grow.cpp`: const-matrix `m`,
mut-visited `vis`, mut caller stack `st` (passed empty),
`u64` dimension `n` and source `src`, `u64` reachable-count out)
captures the entry + the const/mut `at()` composers +
`_M_range_check` + both `operator[]` + `size` + the N4d-iv-b2
growth closure (`push_back` / `emplace_back` /
`_M_realloc_insert` + the b1 leaves). The entry functionalizes
to a fused seed (visited mark through the mut-`at()` checked
write behind its `ult` guard, then the source pushed through the
`push_back` composer) plus the outer stack-drain `while_`
(`top != 0`) around the inner row-scan `while_` (`u < n`):
each row scans `m[v * n + u]` (the G2 index computation) and
pushes every unvisited non-zero neighbor through `push_back`
(gate one `m[v*n+u] != 0`, gate two `vis[u] == 0`), counting
each first visit. The `top` cursor is kept (the keep-top
spelling — `top == st.length` holds by construction, no size
arithmetic in the guard), so the loop skeleton is exactly G5a's;
only the two pushes change representation: Eval-world reified
lists cannot call the `push_back` composer (`callProg` is loud
outside the program evaluator), so the entry lives in
Prog-world over owned triples (the `stdVecShiftDownFunc`
precedent: `.vecBlock` params, `.vgrowLen` guards, `.vgrowAt`
reads, `.vgrowSet` stores, `.callProg` pushes), evaluated by
`evalProgFunc vecGrowProg`. Every `at()`-style op sits behind
its own fused `ult` guard; each miss is loud (`AssertFail` from
the guard `.fail`, `.OOB` from an unguarded triple read —
both exit 4 natively). The cursor and count advances are pure
wrapping `uadd`/`usub`; the pop-read widens through `u64ofI32`
and the pushed values narrow through `i32ofU64` (the V2 cast
precedent). Capacities are model-internal (reallocation is
invisible in the return count); the entry theorem holds for
every initial `st` capacity, and the Diff fuzzer pins native
agreement including repeated `_M_realloc_insert` relocations.

Termination is by fuel lockstep, not by measure: the forwards
thread the same fuel as the evaluator (`while_` and `callProg`
are the consumers — one fuel per iteration and per composer
call depth; zero fuel exits cleanly on a false condition and
aborts loudly on a live one), and the entry theorem holds for
every fuel by induction. Fuel splits go through `fuel_step_down`
(the N5a gate).
-/
import Circe.Emit.VecStackPush
import Circe.Emit.VecCompose.Emplace

/-! ## G4: `dfs_grow` entry -/

/-- Mangled name of the growing-stack DFS entry. -/
def dfsGrowName : String :=
  "_Z8dfs_growRKSt6vectorIiSaIiEERS1_S4_mm"

/-- The G2 row index (`v * n + u`, CIR order). -/
def dfsGrowRowIdx : CExpr :=
  .uadd (.umul (.var "v") (.var "n")) (.var "u")

/-- The fused entry seed: guarded visited mark plus the source
    pushed through the `push_back` composer (each miss is loud). -/
def dfsGrowSeed : CStmt :=
  .seq (.if_ (.ult (.var "src") (.vgrowLen "vis"))
          (.vgrowSet "vis" (.var "src") (.lit (.i32 1)))
          .fail)
  (.seq (.let_ "x0" (.i 32) (.i32ofU64 (.var "src")))
  (.seq (.callProg "st" stdVecPushBackName ["st", "x0"])
  (.seq (.let_ "top" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
  (.seq (.let_ "count" (.u 64) (.lit (.u64 (BitVec.ofNat 64 1))))
  (.seq (.let_ "v" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0))))
  (.let_ "u" (.u 64) (.lit (.u64 (BitVec.ofNat 64 0)))))))))

/-- One inner push: the discovery value reuses the popped slot
    when one is free (`top < len`, a guarded `at()` store) and grows
    through the `push_back` composer past the high-water mark; the
    live count and visit count advance by exactly one either way
    (the termination potential is unchanged by a push). -/
def dfsGrowPush : CStmt :=
  .seq (.let_ "x" (.i 32) (.i32ofU64 (.var "u")))
  (.seq (.if_ (.ult (.var "top") (.vgrowLen "st"))
          (.vgrowSet "st" (.var "top") (.var "x"))
          (.callProg "st" stdVecPushBackName ["st", "x"]))
  (.seq (.assign "top" (.uadd (.var "top")
            (.lit (.u64 (BitVec.ofNat 64 1)))))
    (.assign "count" (.uadd (.var "count")
      (.lit (.u64 (BitVec.ofNat 64 1)))))))

/-- One row-scan iteration: the matrix guard, the two gates, the
    push, and the `u` advance (which always runs). -/
def dfsGrowInnerBody : CStmt :=
  .seq (.if_ (.ult dfsGrowRowIdx (.vgrowLen "m"))
          (.if_ (.une (.vgrowAt "m" dfsGrowRowIdx)
                  (.lit (.i32 (BitVec.ofNat 32 0))))
            (.if_ (.ult (.var "u") (.vgrowLen "vis"))
              (.if_ (.ueq (.vgrowAt "vis" (.var "u"))
                      (.lit (.i32 (BitVec.ofNat 32 0))))
                (.seq (.vgrowSet "vis" (.var "u")
                         (.lit (.i32 (BitVec.ofNat 32 1))))
                  dfsGrowPush)
                .skip)
              .fail)
            .skip)
          .fail)
       (.assign "u" (.uadd (.var "u")
         (.lit (.u64 (BitVec.ofNat 64 1)))))

/-- The row scan: `u` runs `0..n`. -/
def dfsGrowInner : CStmt :=
  .while_ (.ult (.var "u") (.var "n")) dfsGrowInnerBody

/-- One drain iteration: pop, guarded widening read, `u` reset,
    then the row scan. -/
def dfsGrowOuterBody : CStmt :=
  .seq (.assign "top" (.usub (.var "top")
          (.lit (.u64 (BitVec.ofNat 64 1)))))
  (.seq (.if_ (.ult (.var "top") (.vgrowLen "st"))
          (.assign "v" (.u64ofI32 (.vgrowAt "st" (.var "top"))))
          .fail)
  (.seq (.assign "u" (.lit (.u64 (BitVec.ofNat 64 0))))
    dfsGrowInner))

/-- The stack drain: `top != 0`. -/
def dfsGrowOuter : CStmt :=
  .while_ (.une (.var "top") (.lit (.u64 (BitVec.ofNat 64 0))))
    dfsGrowOuterBody

/-- Canonical CoreIR for `dfs_grow`: the fused seed, the nested
    drain, and the count return. Prog-world over owned triples
    (the `push_back` composer calls need `evalProgFunc`). -/
def dfsGrowFunc : Func :=
  ⟨dfsGrowName,
   [{ name := "m", ty := .vecBlock, role := .owned },
    { name := "vis", ty := .vecBlock, role := .owned },
    { name := "st", ty := .vecBlock, role := .owned },
    { name := "n", ty := .u 64, role := .owned },
    { name := "src", ty := .u 64, role := .owned }],
   .u 64,
   (.seq dfsGrowSeed (.seq dfsGrowOuter (.return_ (.var "count"))))⟩

/-! ## Composer characterization (the G4 proof work) -/

/-- `max_size` round-trips (`2^61 - 1 < 2^64`). -/
theorem stdVecMaxDiffBV_toNat :
    stdVecMaxDiffBV.toNat = stdVecMaxDiff := by
  simp [stdVecMaxDiffBV, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by decide : stdVecMaxDiff < 2 ^ 64)]

/-- Check-length success delivers headroom: the new length covers
    `len + 1` and stays below `max_size` (the error branch is dead
    under `len ≤ maxdiff - 1`). -/
theorem stdVecCheckLenFwd_ok_len (len : Nat) (w : BitVec 64)
    (h64 : len < 2 ^ 64)
    (hmax : len ≤ stdVecMaxDiffBV.toNat - 1)
    (h : stdVecCheckLenFwd len (BitVec.ofNat 64 1) = .ok (.u64 w)) :
    len + 1 ≤ w.toNat ∧ w.toNat ≤ stdVecMaxDiffBV.toNat := by
  have hmaxv := stdVecMaxDiffBV_toNat
  have hmax64 : stdVecMaxDiff < 2 ^ 64 := by decide
  have hlen64 : (BitVec.ofNat 64 len).toNat = len := by
    rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt h64
  have h1 : (BitVec.ofNat 64 1).toNat = 1 := rfl
  have hmaxT : stdVecMaxDiffBV.toNat = stdVecMaxDiff := hmaxv
  unfold stdVecCheckLenFwd at h
  by_cases hc1 : (stdVecMaxDiffBV - BitVec.ofNat 64 len).ult
      (BitVec.ofNat 64 1) = true
  · simp [hc1] at h
  · simp only [hc1] at h
    by_cases hc2 : (BitVec.ofNat 64 len +
        (if (BitVec.ofNat 64 len).ult (BitVec.ofNat 64 1) then
          (BitVec.ofNat 64 1)
        else BitVec.ofNat 64 len)).ult (BitVec.ofNat 64 len) = true
    · simp only [hc2] at h
      cases h
      rw [hmaxT] at hmax ⊢
      simp only [stdVecMaxDiff] at hmax ⊢
      omega
    · simp only [hc2] at h
      by_cases hc3 : stdVecMaxDiffBV.ult (BitVec.ofNat 64 len +
          (if (BitVec.ofNat 64 len).ult (BitVec.ofNat 64 1) then
            (BitVec.ofNat 64 1)
          else BitVec.ofNat 64 len)) = true
      · simp only [hc3] at h
        cases h
        rw [hmaxT] at hmax ⊢
        simp only [stdVecMaxDiff] at hmax ⊢
        omega
      · simp only [hc3] at h
        cases h
        by_cases hx : (BitVec.ofNat 64 len).ult
            (BitVec.ofNat 64 1) = true
        · have hX : (if (BitVec.ofNat 64 len).ult (BitVec.ofNat 64 1)
              then (BitVec.ofNat 64 1)
              else BitVec.ofNat 64 len) = BitVec.ofNat 64 1 := by
            rw [ite_eq_left hx]
          have hsum : (BitVec.ofNat 64 len + BitVec.ofNat 64 1).toNat =
              len + 1 := by
            rw [BitVec.toNat_add, hlen64, h1]
            have hno : ¬ (len + 1) % 2 ^ 64 < len := by
              have h2 := hc2
              rw [hX] at h2
              rw [BitVec.ult_eq_decide, BitVec.toNat_add, hlen64, h1,
                decide_eq_true_eq] at h2
              exact h2
            have h2 : (2:Nat) ^ 64 = 18446744073709551616 := rfl
            have hlt : len + 1 < 2 ^ 64 := by omega
            exact Nat.mod_eq_of_lt hlt
          rw [hX]
          rw [hsum]
          have hle : (BitVec.ofNat 64 len + BitVec.ofNat 64 1).toNat ≤
              stdVecMaxDiffBV.toNat := by
            have h2 := hc3
            rw [hX] at h2
            rw [BitVec.ult_eq_decide, decide_eq_true_eq] at h2
            omega
          rw [hmaxT] at hmax ⊢
          omega
        · have hX : (if (BitVec.ofNat 64 len).ult (BitVec.ofNat 64 1)
              then (BitVec.ofNat 64 1)
              else BitVec.ofNat 64 len) = BitVec.ofNat 64 len := by
            rw [ite_eq_right hx]
          have hsum : (BitVec.ofNat 64 len + BitVec.ofNat 64 len).toNat =
              len + len := by
            rw [BitVec.toNat_add, hlen64]
            have hno : ¬ (len + len) % 2 ^ 64 < len := by
              have h2 := hc2
              rw [hX] at h2
              rw [BitVec.ult_eq_decide, BitVec.toNat_add, hlen64,
                decide_eq_true_eq] at h2
              exact h2
            have h2 : (2:Nat) ^ 64 = 18446744073709551616 := rfl
            have hlt : len + len < 2 ^ 64 := by omega
            exact Nat.mod_eq_of_lt hlt
          rw [hX]
          rw [hsum]
          have hle : (BitVec.ofNat 64 len + BitVec.ofNat 64 len).toNat ≤
              stdVecMaxDiffBV.toNat := by
            have h2 := hc3
            rw [hX] at h2
            rw [BitVec.ult_eq_decide, decide_eq_true_eq] at h2
            omega
          have hlen1 : 1 ≤ len := by
            have := hx
            rw [BitVec.ult_eq_decide, hlen64, h1] at this
            simp at this
            omega
          rw [hmaxT] at hmax ⊢
          omega

/-- Projectors are injective on success (case the value once,
    reuse everywhere a composer bind is cased). -/
theorem vecGrowU64_ok {v : Value} {w : BitVec 64}
    (h : vecGrowU64 v = .ok w) : v = .u64 w := by
  cases v <;> simp_all [vecGrowU64]

theorem vecGrowI64_ok {v : Value} {w : BitVec 64}
    (h : vecGrowI64 v = .ok w) : v = .i64 w := by
  cases v <;> simp_all [vecGrowI64]

theorem vecGrowOwned_ok {v : Value} {t : Vec32 × Nat × Nat}
    (h : vecGrowOwned v = .ok t) :
    v = .stdVecOwned t.1 t.2.1 t.2.2 := by
  cases v <;> simp_all [vecGrowOwned]
  obtain rfl := h
  exact ⟨rfl, rfl, rfl⟩

/-- A successful push keeps the triple well-formed: live,
    length covered by words, both counters below `2^64`, and the
    length pinned to `len + 1` (both paths bump by exactly one;
    the slow-path equation is `hmod` below).
    (Fast path: `construct` stores into spare words; slow path:
    fresh `newlen` words, relocate, length `len + 1`.) -/
theorem stdVecPushBackFwd_ok (b : Vec32) (len cap : Nat)
    (x : BitVec 32) (v : Value)
    (hlive : b.freed = false)
    (hlen : len ≤ b.val.length)
    (hbuflen : b.val.length < 2 ^ 64)
    (h64 : len < 2 ^ 64)
    (hcap64 : cap < 2 ^ 64)
    (hmax : len ≤ stdVecMaxDiffBV.toNat - 1)
    (h : stdVecPushBackFwd b len cap x = .ok v) :
    ∃ b' l' c', v = .stdVecOwned b' l' c' ∧ b'.freed = false ∧
      l' ≤ b'.val.length ∧ b'.val.length < 2 ^ 64 ∧ l' < 2 ^ 64 ∧
      c' < 2 ^ 64 ∧ l' = len + 1 := by
  have hmaxT := stdVecMaxDiffBV_toNat
  have hmax64 : stdVecMaxDiff < 2 ^ 64 := by decide
  have hpush : stdVecPushBackFwd b len cap x =
      stdVecEmplaceBackFwd b len cap x := rfl
  rw [hpush] at h
  unfold stdVecEmplaceBackFwd at h
  split at h
  · -- Slow path: `_M_realloc_insert` at `pos = len`.
    unfold stdVecGrowReallocFwd at h
    cases hck : stdVecCheckLenFwd len (BitVec.ofNat 64 1) with
    | error e =>
      simp only [hck, vecGrow_bind_err] at h
      cases h
    | ok w =>
      simp only [hck, vecGrow_bind_ok] at h
      cases hpr : vecGrowU64 w with
      | error e =>
        simp only [hpr, vecGrow_bind_err] at h
        cases h
      | ok newlenW =>
        have hw : w = .u64 newlenW := vecGrowU64_ok hpr
        rw [hw] at hck
        simp only [hpr, vecGrow_bind_ok] at h
        obtain ⟨hnew1, hnew2⟩ :=
          stdVecCheckLenFwd_ok_len len newlenW h64 hmax hck
        have hg0 : (BitVec.ofNat 64 0).toNat = 0 := rfl
        have hpos : (BitVec.ofNat 64 0).ult newlenW = true := by
          rw [BitVec.ult_eq_decide, hg0]
          exact decide_eq_true (by omega)
        have hbg : stdVecBeginFwd =
            .ok (.u64 (BitVec.ofNat 64 0)) := rfl
        have hbgv : vecGrowU64 (.u64 (BitVec.ofNat 64 0)) =
            .ok (BitVec.ofNat 64 0) := rfl
        have hmi : stdVecMinusFwd (BitVec.ofNat 64 len)
            (BitVec.ofNat 64 0) =
            .ok (.i64 (BitVec.ofNat 64 len - BitVec.ofNat 64 0)) := rfl
        have hkd : vecGrowI64
            (.i64 (BitVec.ofNat 64 len - BitVec.ofNat 64 0)) =
            .ok (BitVec.ofNat 64 len - BitVec.ofNat 64 0) := rfl
        simp only [hbg, vecGrow_bind_ok] at h
        simp only [hbgv, vecGrow_bind_ok] at h
        simp only [hmi, vecGrow_bind_ok] at h
        simp only [hkd, vecGrow_bind_ok] at h
        cases hal : stdVecAllocFwd newlenW with
        | error e =>
          simp only [hal, vecGrow_bind_err] at h
          cases h
        | ok alv =>
          obtain ⟨bNew, halv, hNlive, hNlen⟩ :=
            stdVecAllocFwd_ok newlenW alv hpos hal
          have hownedA : vecGrowOwned
              (.stdVecOwned bNew 0 newlenW.toNat) =
              .ok (bNew, 0, newlenW.toNat) := rfl
          simp only [hal, vecGrow_bind_ok] at h
          simp only [halv] at h
          simp only [hownedA, vecGrow_bind_ok] at h
          cases hcon : stdVecConstructFwd bNew 0 newlenW.toNat
              (BitVec.ofNat 64 len - BitVec.ofNat 64 0) x with
          | error e =>
            simp only [hcon, vecGrow_bind_err] at h
            cases h
          | ok conv =>
            obtain ⟨bC, hconv, hClive, hClen⟩ :=
              stdVecConstructFwd_ok bNew 0 newlenW.toNat
                (BitVec.ofNat 64 len - BitVec.ofNat 64 0) x conv hcon
            have hownedC : vecGrowOwned
                (.stdVecOwned bC 0 newlenW.toNat) =
                .ok (bC, 0, newlenW.toNat) := rfl
            simp only [hcon, vecGrow_bind_ok] at h
            simp only [hconv] at h
            simp only [hownedC, vecGrow_bind_ok] at h
            cases hr1 : stdVecRelocFwd b len cap bC 0 newlenW.toNat
                (BitVec.ofNat 64 0)
                (BitVec.ofNat 64 len - BitVec.ofNat 64 0)
                (BitVec.ofNat 64 0) with
            | error e =>
              simp only [hr1, vecGrow_bind_err] at h
              cases h
            | ok r1v =>
              obtain ⟨bR1, hr1v, hR1live, hR1len⟩ :=
                stdVecRelocFwd_ok b len cap bC 0 newlenW.toNat
                  (BitVec.ofNat 64 0)
                  (BitVec.ofNat 64 len - BitVec.ofNat 64 0)
                  (BitVec.ofNat 64 0) r1v hClive hr1
              have hownedR1 : vecGrowOwned
                  (.stdVecOwned bR1 0 newlenW.toNat) =
                  .ok (bR1, 0, newlenW.toNat) := rfl
              simp only [hr1, vecGrow_bind_ok] at h
              simp only [hr1v] at h
              simp only [hownedR1, vecGrow_bind_ok] at h
              cases hr2 : stdVecRelocFwd b len cap bR1 0
                  newlenW.toNat
                  (BitVec.ofNat 64 len - BitVec.ofNat 64 0)
                  (BitVec.ofNat 64 len)
                  (BitVec.ofNat 64 len - BitVec.ofNat 64 0 +
                    BitVec.ofNat 64 1) with
              | error e =>
                simp only [hr2, vecGrow_bind_err] at h
                cases h
              | ok r2v =>
                obtain ⟨bR2, hr2v, hR2live, hR2len⟩ :=
                  stdVecRelocFwd_ok b len cap bR1 0 newlenW.toNat
                    (BitVec.ofNat 64 len - BitVec.ofNat 64 0)
                    (BitVec.ofNat 64 len)
                    (BitVec.ofNat 64 len - BitVec.ofNat 64 0 +
                      BitVec.ofNat 64 1) r2v hR1live hr2
                have hownedR2 : vecGrowOwned
                    (.stdVecOwned bR2 0 newlenW.toNat) =
                    .ok (bR2, 0, newlenW.toNat) := rfl
                simp only [hr2, vecGrow_bind_ok] at h
                simp only [hr2v] at h
                simp only [hownedR2, vecGrow_bind_ok] at h
                cases hdg : stdVecDeallocGuardFwd b len cap
                    (BitVec.ofNat 64 cap) with
                | error e =>
                  simp only [hdg, vecGrow_bind_err] at h
                  cases h
                | ok _ =>
                  simp only [hdg, vecGrow_bind_ok] at h
                  cases h
                  have hlenR : bR2.val.length = newlenW.toNat := by
                    rw [hR2len, hR1len, hClen, hNlen]
                  have hlt : len + 1 < 2 ^ 64 := by
                    have h2 : (2:Nat) ^ 64 =
                        18446744073709551616 := rfl
                    rw [hmaxT] at hmax
                    simp only [stdVecMaxDiff] at hmax
                    omega
                  have hmod : (BitVec.ofNat 64 len +
                      BitVec.ofNat 64 1).toNat = len + 1 := by
                    rw [BitVec.toNat_add]
                    have hlen64 : (BitVec.ofNat 64 len).toNat = len := by
                      rw [BitVec.toNat_ofNat]
                      exact Nat.mod_eq_of_lt h64
                    have h1 : (BitVec.ofNat 64 1).toNat = 1 := rfl
                    rw [hlen64, h1]
                    exact Nat.mod_eq_of_lt hlt
                  have hle : (BitVec.ofNat 64 len +
                      BitVec.ofNat 64 1).toNat ≤ newlenW.toNat := by
                    omega
                  have h64' : newlenW.toNat < 2 ^ 64 := by
                    have h2 : (2:Nat) ^ 64 =
                        18446744073709551616 := rfl
                    rw [hmaxT] at hnew2
                    simp only [stdVecMaxDiff] at hnew2
                    omega
                  refine ⟨bR2, (BitVec.ofNat 64 len +
                    BitVec.ofNat 64 1).toNat, newlenW.toNat,
                    rfl, hR2live, ?_, ?_, ?_, ?_, hmod⟩ <;>
                    omega
  · -- Fast path: `construct` at `len`, bump to `len + 1`.
    cases hcon : stdVecConstructFwd b len cap
        (BitVec.ofNat 64 len) x with
    | error e =>
      simp only [hcon, vecGrow_bind_err] at h
      cases h
    | ok conv =>
      obtain ⟨bC, hconv, hClive, hClen⟩ :=
        stdVecConstructFwd_ok b len cap (BitVec.ofNat 64 len) x conv
          hcon
      simp only [hcon, hconv, vecGrow_bind_ok, vecGrowOwned] at h
      cases h
      have hlt : len < b.val.length := by
        by_cases hlt : len < b.val.length
        · exact hlt
        · have hlen64 : (BitVec.ofNat 64 len).toNat = len := by
            rw [BitVec.toNat_ofNat]
            exact Nat.mod_eq_of_lt h64
          have herr := vecSet_oob b ((BitVec.ofNat 64 len).toNat) x
            hlive (by omega)
          unfold stdVecConstructFwd at hcon
          rw [herr] at hcon
          cases hcon
      refine ⟨bC, len + 1, cap, rfl, hClive, ?_, ?_, ?_, hcap64, rfl⟩
      · rw [hClen]
        omega
      · rw [hClen]
        omega
      · have h2 : (2:Nat) ^ 64 = 18446744073709551616 := rfl
        rw [hmaxT] at hmax
        simp only [stdVecMaxDiff] at hmax
        omega

/-! ## Visited-mark counting (fuel-adequacy measure)

    Fuel adequacy cannot be threaded as a `len`-vs-`F` hypothesis:
    pushes grow `len` while same-fuel loop recursion holds `F`, so
    no such relation survives a push arm. Instead adequacy is
    absolute: the entry supplies fuel covering the worst case, and
    every push site discharges its composer premise from the
    absolute length bound `len ≤ L0 + ones`, where `ones` counts
    marked cells and `L0` is the entry length. Marks only ever go
    `0 → 1` (the seed marks a fresh source cell, the discovery arm
    marks behind its `w == 0` gate), so the bound is preserved by
    every arm; `ones_le_length` caps it by the visited length. -/

/-- Number of nonzero (marked) visited cells. -/
def ones : List (BitVec 32) → Nat
  | [] => 0
  | x :: xs => (if x = 0 then 0 else 1) + ones xs

/-- Marking a fresh (zero) cell bumps the count by exactly one. -/
theorem ones_set_one (l : List (BitVec 32)) (i : Nat)
    (h : l[i]? = some (0 : BitVec 32)) :
    ones (l.set i 1) = ones l + 1 := by
  induction l generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero =>
      have hx : x = 0 := by simpa using h
      subst hx
      simp only [List.set, ones, ↓reduceIte]
      rw [ite_eq_right (by decide : ¬((1 : BitVec 32) = 0))]
      omega
    | succ n =>
      have h' : xs[n]? = some (0 : BitVec 32) := h
      have ihr := ih n h'
      simp only [List.set, ones] at ⊢
      rw [ihr]
      omega

/-- The mark count never exceeds the visited length. -/
theorem ones_le_length (l : List (BitVec 32)) : ones l ≤ l.length := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons x xs ih =>
    simp only [ones, List.length_cons]
    have hcell : (if x = (0 : BitVec 32) then 0 else 1) ≤ 1 := by
      split <;> omega
    omega

/-! ## Forwards (Prog-world: lists for `m`/`vis`, full triple for `st`)

    `m` never changes, so its triple is fixed by the entry
    premises; `vis` keeps `len = words.length` (marks preserve
    length). Only the stack threads its full triple (spare
    capacity is real state after a realloc). The push legs check
    capacity one stricter than the composer's precondition
    (`len ≤ maxdiff - 1` is exactly the success condition, and a
    successful forward discharges the exact `hmax` by `omega`);
    fuel adequacy is an S3a-style theorem hypothesis, since a
    forward fuel check would be stricter than the evaluator on
    the fast path. -/

/-- Seed mirror: the guarded visited mark, then the source through
    the `push_back` forward (the composer forward is shared with
    the evaluator side, so pushes agree by rewriting). The capacity
    check is one stricter than the composer's `max_size` contract
    (`len ≤ maxdiff - 1` is exactly the success condition, since
    `check_len` fails at `len = maxdiff`; a successful forward
    discharges the composer's exact precondition by `omega`).
    Fuel adequacy is a theorem hypothesis (S3a side condition),
    not a forward check. -/
def dfsGrowSeedFwd (F : Nat) (visL : List (BitVec 32))
    (b : Vec32) (len cap : Nat) (src : BitVec 64) :
    Result (List (BitVec 32) × Vec32 × Nat × Nat) :=
  if src.ult (BitVec.ofNat 64 visL.length) then
    match visL[src.toNat]? with
    | none => .error .OOB
    | some _ =>
      if src.toNat < visL.length then
        if len ≤ stdVecMaxDiffBV.toNat - 1 then
          (stdVecPushBackFwd b len cap
            (BitVec.ofNat 32 src.toNat)).bind fun v =>
          (vecGrowOwned v).bind fun t =>
            .ok (visL.set src.toNat 1, t.1, t.2.1, t.2.2)
        else .error .AssertFail
      else .error .OOB
  else .error .AssertFail

/-- Fuel-threaded row-scan forward: mirrors `dfsGrowInner`
    iteration for iteration (same fuel, same guard order). -/
def dfsGrowRowFwd (F : Nat) (mL visL : List (BitVec 32))
    (b : Vec32) (len cap : Nat) (n v top count u : BitVec 64) :
    Result (List (BitVec 32) × Vec32 × Nat × Nat ×
      BitVec 64 × BitVec 64 × BitVec 64) :=
  match F with
  | 0 =>
    if u.ult n then .error .AssertFail
    else .ok (visL, b, len, cap, top, count, u)
  | F + 1 =>
    if u.ult n then
      if (v * n + u).ult (BitVec.ofNat 64 mL.length) then
        match mL[(v * n + u).toNat]? with
        | none => .error .OOB
        | some g =>
          if (v * n + u).toNat < mL.length then
            if g != (BitVec.ofNat 32 0) then
              if u.ult (BitVec.ofNat 64 visL.length) then
                match visL[u.toNat]? with
                | none => .error .OOB
                | some w =>
                  if u.toNat < visL.length then
                    if w == (BitVec.ofNat 32 0) then
                      if top.ult (BitVec.ofNat 64 len) then
                        match vecSet b top.toNat
                            (BitVec.ofNat 32 u.toNat) with
                        | .error e => .error e
                        | .ok b2 =>
                          dfsGrowRowFwd F mL
                            (visL.set u.toNat 1)
                            b2 len cap
                            n v (top + 1) (count + 1) (u + 1)
                      else
                        if len ≤ stdVecMaxDiffBV.toNat - 1 then
                          (stdVecPushBackFwd b len cap
                            (BitVec.ofNat 32 u.toNat)).bind fun pv =>
                          (vecGrowOwned pv).bind fun pt =>
                            dfsGrowRowFwd F mL
                              (visL.set u.toNat 1)
                              pt.1 pt.2.1 pt.2.2
                              n v (top + 1) (count + 1) (u + 1)
                        else .error .AssertFail
                    else dfsGrowRowFwd F mL visL b len cap n v
                      top count (u + 1)
                  else .error .OOB
              else .error .AssertFail
            else dfsGrowRowFwd F mL visL b len cap n v top
              count (u + 1)
          else .error .OOB
      else .error .AssertFail
    else .ok (visL, b, len, cap, top, count, u)

/-- Fuel-threaded drain forward: mirrors `dfsGrowOuter` (same
    fuel; the row scan runs at predecessor fuel, exactly as the
    successor handler threads it). -/
def dfsGrowOuterFwd (F : Nat) (mL visL : List (BitVec 32))
    (b : Vec32) (len cap : Nat) (n top count v u : BitVec 64) :
    Result (List (BitVec 32) × Vec32 × Nat × Nat ×
      BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) :=
  match F with
  | 0 =>
    if top != (BitVec.ofNat 64 0) then .error .AssertFail
    else .ok (visL, b, len, cap, top, count, v, u)
  | F + 1 =>
    if top != (BitVec.ofNat 64 0) then
      if (top - 1).ult (BitVec.ofNat 64 len) then
        match b.val[(top - 1).toNat]? with
        | none => .error .OOB
        | some w =>
          if (top - 1).toNat < len then
            match dfsGrowRowFwd F mL visL b len cap n
                (w.signExtend 64) (top - 1) count 0 with
            | .error e => .error e
            | .ok (vis', b', l', c', top', count', u') =>
              dfsGrowOuterFwd F mL vis' b' l' c' n top'
                count' (w.signExtend 64) u'
          else .error .OOB
      else .error .AssertFail
    else .ok (visL, b, len, cap, top, count, v, u)

/-- Entry mirror: seed, then the drain; the count is the return. -/
def dfsGrowFwd (F : Nat) (mL visL : List (BitVec 32))
    (b : Vec32) (len cap : Nat) (n src : BitVec 64) :
    Result Value :=
  match dfsGrowSeedFwd F visL b len cap src with
  | .error e => .error e
  | .ok (vis1, b1, l1, c1) =>
    match dfsGrowOuterFwd F mL vis1 b1 l1 c1 n 1 1 0 0 with
    | .error e => .error e
    | .ok (_, _, _, _, _, count, _, _) => .ok (.u64 count)

/-! ## Seed agreement -/

/-- Seed agreement (ok leg): the guarded mark plus the source push
    evaluate exactly as the seed forward says, threading the post
    lookups. -/
theorem dfsGrowSeed_ok (F : Nat) (mL visL : List (BitVec 32))
    (b : Vec32) (len cap : Nat) (n src : BitVec 64) (ρ : Env)
    (hm : envLookup ρ "m" =
      some (.stdVecOwned ⟨mL, false⟩ mL.length mL.length))
    (hmen : mL.length < 2 ^ 64)
    (hvis : envLookup ρ "vis" =
      some (.stdVecOwned ⟨visL, false⟩ visL.length visL.length))
    (hvislen : visL.length < 2 ^ 64)
    (hst : envLookup ρ "st" = some (.stdVecOwned b len cap))
    (hlive : b.freed = false)
    (hlen : len ≤ b.val.length)
    (hbuflen : b.val.length < 2 ^ 64)
    (hlen64 : len < 2 ^ 64)
    (hcap64 : cap < 2 ^ 64)
    (hF : len + 4 ≤ F)
    (hn : envLookup ρ "n" = some (.u64 n))
    (hsrc : envLookup ρ "src" = some (.u64 src))
    (hvis0 : visL[src.toNat]? = some (0 : BitVec 32))
    (vis1 : List (BitVec 32)) (b1 : Vec32) (l1 c1 : Nat)
    (hseed : dfsGrowSeedFwd F visL b len cap src =
      .ok (vis1, b1, l1, c1)) :
    ∃ ρ', evalProgStmt vecGrowProg F dfsGrowSeed ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "m" =
        some (.stdVecOwned ⟨mL, false⟩ mL.length mL.length) ∧
      envLookup ρ' "vis" =
        some (.stdVecOwned ⟨vis1, false⟩ visL.length visL.length) ∧
      envLookup ρ' "st" = some (.stdVecOwned b1 l1 c1) ∧
      envLookup ρ' "n" = some (.u64 n) ∧
      envLookup ρ' "src" = some (.u64 src) ∧
      envLookup ρ' "top" = some (.u64 (BitVec.ofNat 64 1)) ∧
      envLookup ρ' "count" = some (.u64 (BitVec.ofNat 64 1)) ∧
      envLookup ρ' "v" = some (.u64 (BitVec.ofNat 64 0)) ∧
      envLookup ρ' "u" = some (.u64 (BitVec.ofNat 64 0)) ∧
      b1.freed = false ∧ l1 ≤ b1.val.length ∧
      b1.val.length < 2 ^ 64 ∧ l1 < 2 ^ 64 ∧ c1 < 2 ^ 64 ∧
      l1 = len + 1 ∧ ones vis1 = ones visL + 1 ∧
      l1 ≤ len + ones vis1 ∧ 1 ≤ l1 := by
  simp only [dfsGrowSeed]
  unfold dfsGrowSeedFwd at hseed
  by_cases hg : src.ult (BitVec.ofNat 64 visL.length) = true
  · simp only [hg] at hseed
    cases hget : visL[src.toNat]? with
    | none =>
      simp only [hget] at hseed
      cases hseed
    | some w =>
      simp only [hget] at hseed
      by_cases hltN : src.toNat < visL.length
      · simp only [hltN, ↓reduceIte] at hseed
        by_cases hmaxC : len ≤ stdVecMaxDiffBV.toNat - 1
        · simp only [hmaxC, ↓reduceIte] at hseed
          cases hpush : stdVecPushBackFwd b len cap (BitVec.ofNat 32 src.toNat) with
          | error e =>
            simp only [hpush, vecGrow_bind_err] at hseed
            cases hseed
          | ok v =>
            simp only [hpush, vecGrow_bind_ok] at hseed
            cases hown : vecGrowOwned v with
            | error e =>
              simp only [hown, vecGrow_bind_err] at hseed
              cases hseed
            | ok t =>
              simp only [hown, vecGrow_bind_ok] at hseed
              cases hseed
              have hv0 := vecGrowOwned_ok hown
              obtain ⟨b', l', c', hv2, hfr, hlen', hbuflen', h64',
                  hcap', hlen1⟩ :=
                stdVecPushBackFwd_ok b len cap
                  (BitVec.ofNat 32 src.toNat) v hlive hlen
                  hbuflen hlen64 hcap64 hmaxC hpush
              have hones1 : ones (visL.set src.toNat 1) =
                  ones visL + 1 :=
                ones_set_one visL src.toNat hvis0
              have hconn : Value.stdVecOwned b' l' c' =
                  Value.stdVecOwned t.1 t.2.1 t.2.2 := by
                rw [← hv2, hv0]
              simp only [Value.stdVecOwned.injEq] at hconn
              obtain ⟨e1, e2, e3⟩ := hconn
              rw [← e1, ← e2, ← e3] at ⊢
              -- Eval side: guard, mark, x0, push, cursor lets.
              have hguard : evalExpr
                  (.ult (.var "src") (.vgrowLen "vis")) ρ =
                  .ok (.b true) := by
                have h1 := evalExpr_var_hit ρ "src" (.u64 src) hsrc
                have h2 := evalExpr_vgrowLen_some "vis" ρ
                  ⟨visL, false⟩ visL.length visL.length hvis
                have h3 := evalExpr_ult_u64 _ _ _ _ _ h1 h2
                rwa [hg] at h3
              have hstepIf : evalProgStmt vecGrowProg F
                  (.if_ (.ult (.var "src") (.vgrowLen "vis"))
                    (.vgrowSet "vis" (.var "src")
                      (.lit (.i32 1)))
                    .fail) ρ =
                  evalProgStmt vecGrowProg F
                    (.vgrowSet "vis" (.var "src")
                      (.lit (.i32 1))) ρ :=
                evalProgStmt_if_true vecGrowProg F _ _ _ _ hguard
              have hset : vecSet ⟨visL, false⟩ src.toNat 1 =
                  .ok ⟨visL.set src.toNat 1, false⟩ := by
                unfold vecSet
                simp [hltN]
              obtain ⟨ρ1, hu⟩ := envUpdate_some_of_lookup ρ "vis"
                (.stdVecOwned ⟨visL, false⟩ visL.length visL.length)
                (.stdVecOwned ⟨visL.set src.toNat 1, false⟩
                  visL.length visL.length) hvis
              have hmark := evalStmtFuel_vgrowSet F "vis"
                (.var "src") (.lit (.i32 1)) ρ src
                (BitVec.ofNat 32 1) ⟨visL, false⟩
                ⟨visL.set src.toNat 1, false⟩
                visL.length visL.length ρ1
                (evalExpr_var_hit ρ "src" (.u64 src) hsrc) rfl
                hvis hset hu
              have hfbMark : evalProgStmt vecGrowProg F
                  (.vgrowSet "vis" (.var "src")
                    (.lit (.i32 1))) ρ =
                  evalStmtFuel F (.vgrowSet "vis" (.var "src")
                    (.lit (.i32 1))) ρ := by
                simp only [evalProgStmt]
              have hstepMark : evalProgStmt vecGrowProg F
                  (.vgrowSet "vis" (.var "src")
                    (.lit (.i32 1))) ρ =
                  .ok (ρ1, .fellThrough) := by
                rw [hfbMark]
                exact hmark
              -- `x0` and the push.
              have hsrc1 : envLookup ρ1 "src" = some (.u64 src) := by
                have hmiss := envLookup_update_miss ρ "src" "vis"
                  (.stdVecOwned ⟨visL.set src.toNat 1, false⟩
                    visL.length visL.length) ρ1 (by decide) hu
                rwa [hsrc] at hmiss
              have hx0eval : evalExpr (.i32ofU64 (.var "src")) ρ1 =
                  .ok (.i32 (BitVec.ofNat 32 src.toNat)) :=
                evalExpr_i32ofU64_ok _ _ _
                  (evalExpr_var_hit ρ1 "src" (.u64 src) hsrc1)
              have hstepX0 := evalProgStmt_let_fb vecGrowProg F
                "x0" (.i 32) (.i32ofU64 (.var "src")) ρ1
              have hletX0 : evalStmtFuel F
                  (.let_ "x0" (.i 32) (.i32ofU64 (.var "src")))
                  ρ1 =
                  .ok (envExtend ρ1 "x0"
                    (.i32 (BitVec.ofNat 32 src.toNat)),
                    .fellThrough) :=
                evalStmtFuel_let_ F "x0" (.i 32)
                  (.i32ofU64 (.var "src")) ρ1 _ hx0eval
              obtain ⟨F', rfl, hF'⟩ : ∃ F', F = F' + 1 ∧
                  len + 3 ≤ F' := ⟨F - 1, by omega, by omega⟩
              have hstepX0' : evalProgStmt vecGrowProg (F' + 1)
                  (.let_ "x0" (.i 32) (.i32ofU64 (.var "src")))
                  ρ1 =
                  .ok (envExtend ρ1 "x0"
                    (.i32 (BitVec.ofNat 32 src.toNat)),
                    .fellThrough) := by
                rw [evalProgStmt_let_fb]
                exact hletX0
              have hargs : lookupArgs
                  (envExtend ρ1 "x0"
                    (.i32 (BitVec.ofNat 32 src.toNat)))
                  ["st", "x0"] = some [.stdVecOwned b len cap,
                    .i32 (BitVec.ofNat 32 src.toNat)] := by
                have hst2 : envLookup
                    (envExtend ρ1 "x0"
                      (.i32 (BitVec.ofNat 32 src.toNat))) "st" =
                    some (.stdVecOwned b len cap) := by
                  simp only [envLookup, envExtend,
                    show ("st" : String) ≠ "x0" by decide]
                  have hmiss := envLookup_update_miss ρ "st" "vis"
                    (.stdVecOwned ⟨visL.set src.toNat 1, false⟩
                      visL.length visL.length) ρ1 (by decide) hu
                  rwa [hst] at hmiss
                have hx02 : envLookup
                    (envExtend ρ1 "x0"
                      (.i32 (BitVec.ofNat 32 src.toNat))) "x0" =
                    some (.i32 (BitVec.ofNat 32 src.toNat)) := by
                  simp [envLookup, envExtend]
                exact lookupArgs_cons_hit _ "st"
                  (.stdVecOwned b len cap) ["x0"]
                  [.i32 (BitVec.ofNat 32 src.toNat)] hst2
                  (lookupArgs_cons_hit _ "x0"
                    (.i32 (BitVec.ofNat 32 src.toNat)) [] [] hx02
                    (lookupArgs_nil _))
              have hmax' : len ≤ stdVecMaxDiffBV.toNat := by omega
              have hcall := evalProgFunc_stdVecPushBack F' b len
                cap (BitVec.ofNat 32 src.toNat) hlive hmax'
                hlen hbuflen hcap64 hF'
              rw [hpush, hv0, ← e1, ← e2, ← e3] at hcall
              have hstepPush := evalProgStmt_callProg_ok vecGrowProg
                F' "st" stdVecPushBackName ["st", "x0"]
                (envExtend ρ1 "x0"
                  (.i32 (BitVec.ofNat 32 src.toNat)))
                [.stdVecOwned b len cap,
                  .i32 (BitVec.ofNat 32 src.toNat)]
                stdVecPushBackFunc (.stdVecOwned b' l' c')
                hargs findFunc_stdVecPushBack hcall
              -- Cursor lets.
              have hstepTop : evalProgStmt vecGrowProg (F' + 1)
                  (.let_ "top" (.u 64)
                    (.lit (.u64 (BitVec.ofNat 64 1))))
                  (envExtend (envExtend ρ1 "x0"
                    (.i32 (BitVec.ofNat 32 src.toNat))) "st"
                    (.stdVecOwned b' l' c')) =
                  .ok (envExtend (envExtend (envExtend ρ1 "x0"
                    (.i32 (BitVec.ofNat 32 src.toNat))) "st"
                    (.stdVecOwned b' l' c'))
                    "top" (.u64 (BitVec.ofNat 64 1)),
                    .fellThrough) := by
                rw [evalProgStmt_let_fb]
                exact evalStmtFuel_let_ _ _ _ _ _ _
                  (by simp [evalExpr, litVal])
              have hstepCount : evalProgStmt vecGrowProg (F' + 1)
                  (.let_ "count" (.u 64)
                    (.lit (.u64 (BitVec.ofNat 64 1))))
                  (envExtend (envExtend (envExtend ρ1 "x0"
                    (.i32 (BitVec.ofNat 32 src.toNat))) "st"
                    (.stdVecOwned b' l' c'))
                    "top" (.u64 (BitVec.ofNat 64 1))) =
                  .ok (envExtend (envExtend (envExtend (envExtend ρ1
                    "x0" (.i32 (BitVec.ofNat 32 src.toNat))) "st"
                    (.stdVecOwned b' l' c'))
                    "top" (.u64 (BitVec.ofNat 64 1)))
                    "count" (.u64 (BitVec.ofNat 64 1)),
                    .fellThrough) := by
                rw [evalProgStmt_let_fb]
                exact evalStmtFuel_let_ _ _ _ _ _ _
                  (by simp [evalExpr, litVal])
              have hstepV : evalProgStmt vecGrowProg (F' + 1)
                  (.let_ "v" (.u 64)
                    (.lit (.u64 (BitVec.ofNat 64 0))))
                  (envExtend (envExtend (envExtend (envExtend ρ1
                    "x0" (.i32 (BitVec.ofNat 32 src.toNat))) "st"
                    (.stdVecOwned b' l' c'))
                    "top" (.u64 (BitVec.ofNat 64 1)))
                    "count" (.u64 (BitVec.ofNat 64 1))) =
                  .ok (envExtend (envExtend (envExtend (envExtend
                    (envExtend ρ1 "x0"
                    (.i32 (BitVec.ofNat 32 src.toNat))) "st"
                    (.stdVecOwned b' l' c'))
                    "top" (.u64 (BitVec.ofNat 64 1)))
                    "count" (.u64 (BitVec.ofNat 64 1)))
                    "v" (.u64 (BitVec.ofNat 64 0)),
                    .fellThrough) := by
                rw [evalProgStmt_let_fb]
                exact evalStmtFuel_let_ _ _ _ _ _ _
                  (by simp [evalExpr, litVal])
              have hstepU : evalProgStmt vecGrowProg (F' + 1)
                  (.let_ "u" (.u 64)
                    (.lit (.u64 (BitVec.ofNat 64 0))))
                  (envExtend (envExtend (envExtend (envExtend
                    (envExtend ρ1 "x0"
                    (.i32 (BitVec.ofNat 32 src.toNat))) "st"
                    (.stdVecOwned b' l' c'))
                    "top" (.u64 (BitVec.ofNat 64 1)))
                    "count" (.u64 (BitVec.ofNat 64 1)))
                    "v" (.u64 (BitVec.ofNat 64 0))) =
                  .ok (envExtend (envExtend (envExtend (envExtend
                    (envExtend (envExtend ρ1 "x0"
                    (.i32 (BitVec.ofNat 32 src.toNat))) "st"
                    (.stdVecOwned b' l' c'))
                    "top" (.u64 (BitVec.ofNat 64 1)))
                    "count" (.u64 (BitVec.ofNat 64 1)))
                    "v" (.u64 (BitVec.ofNat 64 0)))
                    "u" (.u64 (BitVec.ofNat 64 0)),
                    .fellThrough) := by
                rw [evalProgStmt_let_fb]
                exact evalStmtFuel_let_ _ _ _ _ _ _
                  (by simp [evalExpr, litVal])
              have hIfOk : evalProgStmt vecGrowProg (F' + 1)
                  (.if_ (.ult (.var "src") (.vgrowLen "vis"))
                    (.vgrowSet "vis" (.var "src")
                      (.lit (.i32 1)))
                    .fail) ρ = .ok (ρ1, .fellThrough) := by
                rw [hstepIf]
                exact hstepMark
              have hRest : evalProgStmt vecGrowProg (F' + 1)
                  (.seq (.let_ "x0" (.i 32)
                    (.i32ofU64 (.var "src")))
                  (.seq (.callProg "st" stdVecPushBackName
                    ["st", "x0"])
                  (.seq (.let_ "top" (.u 64)
                    (.lit (.u64 (BitVec.ofNat 64 1))))
                  (.seq (.let_ "count" (.u 64)
                    (.lit (.u64 (BitVec.ofNat 64 1))))
                  (.seq (.let_ "v" (.u 64)
                    (.lit (.u64 (BitVec.ofNat 64 0))))
                  (.let_ "u" (.u 64)
                    (.lit (.u64 (BitVec.ofNat 64 0))))))))) ρ1 =
                  .ok (envExtend (envExtend (envExtend (envExtend
                    (envExtend (envExtend ρ1 "x0"
                    (.i32 (BitVec.ofNat 32 src.toNat))) "st"
                    (.stdVecOwned b' l' c'))
                    "top" (.u64 (BitVec.ofNat 64 1)))
                    "count" (.u64 (BitVec.ofNat 64 1)))
                    "v" (.u64 (BitVec.ofNat 64 0)))
                    "u" (.u64 (BitVec.ofNat 64 0)),
                    .fellThrough) := by
                rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _
                  hstepX0']
                rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _
                  hstepPush]
                rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _
                  hstepTop]
                rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _
                  hstepCount]
                rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _
                  hstepV]
                exact hstepU
              have hstmt : evalProgStmt vecGrowProg (F' + 1)
                  (.seq (.if_ (.ult (.var "src")
                    (.vgrowLen "vis"))
                    (.vgrowSet "vis" (.var "src")
                      (.lit (.i32 1)))
                    .fail)
                  (.seq (.let_ "x0" (.i 32)
                    (.i32ofU64 (.var "src")))
                  (.seq (.callProg "st" stdVecPushBackName
                    ["st", "x0"])
                  (.seq (.let_ "top" (.u 64)
                    (.lit (.u64 (BitVec.ofNat 64 1))))
                  (.seq (.let_ "count" (.u 64)
                    (.lit (.u64 (BitVec.ofNat 64 1))))
                  (.seq (.let_ "v" (.u 64)
                    (.lit (.u64 (BitVec.ofNat 64 0))))
                  (.let_ "u" (.u 64)
                    (.lit (.u64 (BitVec.ofNat 64 0)))))))))) ρ =
                  .ok (envExtend (envExtend (envExtend (envExtend
                    (envExtend (envExtend ρ1 "x0"
                    (.i32 (BitVec.ofNat 32 src.toNat))) "st"
                    (.stdVecOwned b' l' c'))
                    "top" (.u64 (BitVec.ofNat 64 1)))
                    "count" (.u64 (BitVec.ofNat 64 1)))
                    "v" (.u64 (BitVec.ofNat 64 0)))
                    "u" (.u64 (BitVec.ofNat 64 0)),
                    .fellThrough) := by
                rw [evalProgStmt_seq_fallthrough _ _ _ _ _ _ hIfOk]
                exact hRest
              refine ⟨_, hstmt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
                ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
                try simp only [envLookup, envExtend, ↓reduceIte,
                  show ("m" : String) ≠ "u" by decide,
                  show ("m" : String) ≠ "v" by decide,
                  show ("m" : String) ≠ "count" by decide,
                  show ("m" : String) ≠ "top" by decide,
                  show ("m" : String) ≠ "st" by decide,
                  show ("m" : String) ≠ "x0" by decide,
                  show ("vis" : String) ≠ "u" by decide,
                  show ("vis" : String) ≠ "v" by decide,
                  show ("vis" : String) ≠ "count" by decide,
                  show ("vis" : String) ≠ "top" by decide,
                  show ("vis" : String) ≠ "st" by decide,
                  show ("vis" : String) ≠ "x0" by decide,
                  show ("st" : String) ≠ "u" by decide,
                  show ("st" : String) ≠ "v" by decide,
                  show ("st" : String) ≠ "count" by decide,
                  show ("st" : String) ≠ "top" by decide,
                  show ("n" : String) ≠ "u" by decide,
                  show ("n" : String) ≠ "v" by decide,
                  show ("n" : String) ≠ "count" by decide,
                  show ("n" : String) ≠ "top" by decide,
                  show ("n" : String) ≠ "st" by decide,
                  show ("n" : String) ≠ "x0" by decide,
                  show ("src" : String) ≠ "u" by decide,
                  show ("src" : String) ≠ "v" by decide,
                  show ("src" : String) ≠ "count" by decide,
                  show ("src" : String) ≠ "top" by decide,
                  show ("src" : String) ≠ "st" by decide,
                  show ("src" : String) ≠ "x0" by decide,
                  show ("top" : String) ≠ "u" by decide,
                  show ("top" : String) ≠ "v" by decide,
                  show ("top" : String) ≠ "count" by decide,
                  show ("count" : String) ≠ "u" by decide,
                  show ("count" : String) ≠ "v" by decide,
                  show ("v" : String) ≠ "u" by decide]
              · exact (envLookup_update_miss ρ "m" "vis"
                  (.stdVecOwned ⟨visL.set src.toNat 1, false⟩
                    visL.length visL.length) ρ1 (by decide) hu).trans hm
              · exact envLookup_update_hit ρ "vis"
                  (.stdVecOwned ⟨visL.set src.toNat 1, false⟩
                    visL.length visL.length) ρ1 hu
              · exact (envLookup_update_miss ρ "n" "vis"
                  (.stdVecOwned ⟨visL.set src.toNat 1, false⟩
                    visL.length visL.length) ρ1 (by decide) hu).trans hn
              · exact (envLookup_update_miss ρ "src" "vis"
                  (.stdVecOwned ⟨visL.set src.toNat 1, false⟩
                    visL.length visL.length) ρ1 (by decide) hu).trans hsrc
              · exact hfr
              · exact hlen'
              · exact hbuflen'
              · exact h64'
              · exact hcap'
              · exact hlen1
              · exact hones1
              · omega
              · omega
        · simp only [hmaxC, ↓reduceIte] at hseed
          cases hseed
      · simp only [hltN, ↓reduceIte] at hseed
        cases hseed
  · simp only [hg] at hseed
    cases hseed

/-- `skip` under a program is a no-op (catch-all delegates to the
    call-free evaluator; both fuel cases are `skip`). -/
theorem evalProgStmt_skip (prog : Prog) (f : Nat) (ρ : Env) :
    evalProgStmt prog f .skip ρ = .ok (ρ, .fellThrough) := by
  have hfb : evalProgStmt prog f .skip ρ = evalStmtFuel f .skip ρ := by
    simp only [evalProgStmt]
  rw [hfb]
  cases f <;> simp [evalStmtFuel, evalStmtZero, evalStmtWith]

/-- Lookup of a freshly extended binding. -/
theorem envLookup_extend_hit (ρ : Env) (x : String) (v : Value) :
    envLookup (envExtend ρ x v) x = some v := by
  simp [envLookup, envExtend]

/-- Lookup of any other variable through an extension. -/
theorem envLookup_extend_miss (ρ : Env) (x y : String) (v w : Value)
    (h : envLookup ρ x = some v) (hne : x ≠ y) :
    envLookup (envExtend ρ y w) x = some v := by
  simp only [envLookup, envExtend, hne]
  exact h

/-- The `u`-advance assignment evaluates (any fuel): value fact,
    update, and the program-level bridge. Callers thread the other
    lookups through the returned update equation. -/
theorem evalProgUAdv (F : Nat) (ρ : Env) (u : BitVec 64)
    (hu : envLookup ρ "u" = some (.u64 u)) (ρU : Env)
    (hup : envUpdate ρ "u" (.u64 (u + 1)) = some ρU) :
    evalProgStmt vecGrowProg F
        (.assign "u" (.uadd (.var "u")
          (.lit (.u64 (BitVec.ofNat 64 1))))) ρ =
        .ok (ρU, .fellThrough) ∧
      envLookup ρU "u" = some (.u64 (u + 1)) := by
  have huAdvE : evalExpr (.uadd (.var "u")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρ =
      .ok (.u64 (u + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit ρ "u" (.u64 u) hu) (evalExpr_lit _ _)
  have hfb : evalProgStmt vecGrowProg F
      (.assign "u" (.uadd (.var "u")
        (.lit (.u64 (BitVec.ofNat 64 1))))) ρ =
      evalStmtFuel F
        (.assign "u" (.uadd (.var "u")
          (.lit (.u64 (BitVec.ofNat 64 1))))) ρ := by
    simp only [evalProgStmt]
  have hev : evalProgStmt vecGrowProg F
      (.assign "u" (.uadd (.var "u")
        (.lit (.u64 (BitVec.ofNat 64 1))))) ρ =
      .ok (ρU, .fellThrough) := by
    rw [hfb]
    exact evalStmtFuel_assign _ _ _ _ _ _ huAdvE hup
  exact ⟨hev, envLookup_update_hit ρ "u" _ ρU hup⟩

/-- Row skip (guard-false leg): at any fuel, a fully-reduced
    guard-false forward agrees with `while`-false. Callers case
    fuel and the forward first (reducing `hrow` to the skip shape),
    then close by this lemma. -/
theorem dfsGrowRow_skip (F : Nat) (mL visL : List (BitVec 32))
    (b : Vec32) (len cap : Nat) (n v top count u : BitVec 64) (ρ : Env)
    (L0 : Nat)
    (hm : envLookup ρ "m" =
      some (.stdVecOwned ⟨mL, false⟩ mL.length mL.length))
    (hvis : envLookup ρ "vis" =
      some (.stdVecOwned ⟨visL, false⟩ visL.length visL.length))
    (hvislen : visL.length < 2 ^ 64)
    (hst : envLookup ρ "st" = some (.stdVecOwned b len cap))
    (hlive : b.freed = false)
    (hlen : len ≤ b.val.length)
    (hbuflen : b.val.length < 2 ^ 64)
    (hlen64 : len < 2 ^ 64)
    (hcap64 : cap < 2 ^ 64)
    (hcnt : len ≤ L0 + ones visL)
    (htopLe : top.toNat ≤ len)
    (hn : envLookup ρ "n" = some (.u64 n))
    (hv : envLookup ρ "v" = some (.u64 v))
    (htop : envLookup ρ "top" = some (.u64 top))
    (hcount : envLookup ρ "count" = some (.u64 count))
    (hu : envLookup ρ "u" = some (.u64 u))
    (huLT : u.ult n = false) :
    ∃ ρ', evalProgStmt vecGrowProg F dfsGrowInner ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "m" =
        some (.stdVecOwned ⟨mL, false⟩ mL.length mL.length) ∧
      envLookup ρ' "vis" =
        some (.stdVecOwned ⟨visL, false⟩ visL.length visL.length) ∧
      envLookup ρ' "st" = some (.stdVecOwned b len cap) ∧
      envLookup ρ' "n" = some (.u64 n) ∧
      envLookup ρ' "v" = some (.u64 v) ∧
      envLookup ρ' "top" = some (.u64 top) ∧
      envLookup ρ' "count" = some (.u64 count) ∧
      envLookup ρ' "u" = some (.u64 u) ∧
      b.freed = false ∧ len ≤ b.val.length ∧
      b.val.length < 2 ^ 64 ∧ len < 2 ^ 64 ∧ cap < 2 ^ 64 ∧
      len ≤ L0 + ones visL ∧ ones visL ≤ ones visL ∧
      top.toNat + ones visL = top.toNat + ones visL ∧
      top.toNat ≤ len := by
  have hguard : evalExpr (.ult (.var "u") (.var "n")) ρ =
      .ok (.b false) := by
    have h1 := evalExpr_var_hit ρ "u" (.u64 u) hu
    have h2 := evalExpr_var_hit ρ "n" (.u64 n) hn
    have h3 := evalExpr_ult_u64 _ _ _ _ _ h1 h2
    rw [huLT] at h3
    exact h3
  have hwhile := evalProgStmt_while_false vecGrowProg F
    (.ult (.var "u") (.var "n")) dfsGrowInnerBody ρ hguard
  simp only [dfsGrowInner] at hwhile ⊢
  exact ⟨ρ, hwhile, hm, hvis, hst, hn, hv, htop, hcount, hu,
    hlive, hlen, hbuflen, hlen64, hcap64, hcnt, Nat.le_refl _,
    trivial, htopLe⟩

/-- Push-sequence agreement, slot-reuse leg: with the reuse guard
    true and the guarded store succeeding, `dfsGrowPush` runs the
    `x` let, takes the store branch, and advances `top`/`count`,
    leaving every other binding untouched. (Extracted from the
    row-ok discovery branch; cf. `dfsPush_ok` in `VecDfs`.) -/
theorem dfsGrowPushSlot_ok (F : Nat) (b b2 : Vec32) (len cap : Nat)
    (top count u : BitVec 64) (ρ : Env)
    (vv : Vec32) (vl vc : Nat)
    (mv : Vec32) (ml mc : Nat) (nn v0 : BitVec 64)
    (hvis : envLookup ρ "vis" = some (.stdVecOwned vv vl vc))
    (hm : envLookup ρ "m" = some (.stdVecOwned mv ml mc))
    (hn : envLookup ρ "n" = some (.u64 nn))
    (hv : envLookup ρ "v" = some (.u64 v0))
    (hst : envLookup ρ "st" = some (.stdVecOwned b len cap))
    (htop : envLookup ρ "top" = some (.u64 top))
    (hcount : envLookup ρ "count" = some (.u64 count))
    (hu : envLookup ρ "u" = some (.u64 u))
    (hlen : len ≤ b.val.length)
    (hbuflen : b.val.length < 2 ^ 64)
    (hlen64 : len < 2 ^ 64)
    (hguard : top.ult (BitVec.ofNat 64 len) = true)
    (hsetB : vecSet b top.toNat (BitVec.ofNat 32 u.toNat) = .ok b2) :
    ∃ ρC, evalProgStmt vecGrowProg F dfsGrowPush ρ =
        .ok (ρC, .fellThrough) ∧
      envLookup ρC "m" = some (.stdVecOwned mv ml mc) ∧
      envLookup ρC "vis" = some (.stdVecOwned vv vl vc) ∧
      envLookup ρC "st" = some (.stdVecOwned b2 len cap) ∧
      envLookup ρC "n" = some (.u64 nn) ∧
      envLookup ρC "v" = some (.u64 v0) ∧
      envLookup ρC "top" = some (.u64 (top + 1)) ∧
      envLookup ρC "count" = some (.u64 (count + 1)) ∧
      envLookup ρC "u" = some (.u64 u) ∧
      len ≤ b2.val.length ∧ b2.val.length < 2 ^ 64 ∧
      b2.freed = false := by
  -- The `x` let.
  have hxE : evalExpr (.i32ofU64 (.var "u")) ρ =
      .ok (.i32 (BitVec.ofNat 32 u.toNat)) :=
    evalExpr_i32ofU64_ok _ _ _
      (evalExpr_var_hit ρ "u" (.u64 u) hu)
  have hletX : evalStmtFuel F (.let_ "x" (.i 32)
      (.i32ofU64 (.var "u"))) ρ =
      .ok (envExtend ρ "x" (.i32 (BitVec.ofNat 32 u.toNat)),
        .fellThrough) :=
    evalStmtFuel_let_ F "x" (.i 32) (.i32ofU64 (.var "u")) ρ _ hxE
  have hstepX : evalProgStmt vecGrowProg F (.let_ "x" (.i 32)
      (.i32ofU64 (.var "u"))) ρ =
      .ok (envExtend ρ "x" (.i32 (BitVec.ofNat 32 u.toNat)),
        .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact hletX
  -- The reuse-guard evaluation.
  have hstX : envLookup (envExtend ρ "x"
      (.i32 (BitVec.ofNat 32 u.toNat))) "st" =
      some (.stdVecOwned b len cap) :=
    envLookup_extend_miss _ _ _ _ _ hst (by decide)
  have hxX : envLookup (envExtend ρ "x"
      (.i32 (BitVec.ofNat 32 u.toNat))) "x" =
      some (.i32 (BitVec.ofNat 32 u.toNat)) :=
    envLookup_extend_hit _ _ _
  have htopX : envLookup (envExtend ρ "x"
      (.i32 (BitVec.ofNat 32 u.toNat))) "top" =
      some (.u64 top) :=
    envLookup_extend_miss _ _ _ _ _ htop (by decide)
  have hstLenX : evalExpr (.vgrowLen "st") (envExtend ρ "x"
      (.i32 (BitVec.ofNat 32 u.toNat))) =
      .ok (.u64 (BitVec.ofNat 64 len)) :=
    evalExpr_vgrowLen_some "st" _ b len cap hstX
  have hguardP : evalExpr (.ult (.var "top") (.vgrowLen "st"))
      (envExtend ρ "x" (.i32 (BitVec.ofNat 32 u.toNat))) =
      .ok (.b (top.ult (BitVec.ofNat 64 len))) :=
    evalExpr_ult_u64 _ _ _ _ _
      (evalExpr_var_hit _ "top" (.u64 top) htopX) hstLenX
  rw [hguard] at hguardP
  -- Slot reuse: the guarded store hits; length and capacity
  -- are unchanged.
  have htlN : top.toNat < len := by
    have h := hguard
    rw [BitVec.ult_eq_decide, decide_eq_true_eq] at h
    have ho : (BitVec.ofNat 64 len).toNat = len := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hlen64
    omega
  have hlenB : b2.val.length = b.val.length :=
    vecSet_length _ _ _ _ hsetB
  have hfrB : b2.freed = false :=
    vecSet_live _ _ _ _ hsetB
  have hlen2 : len ≤ b2.val.length := by
    rw [hlenB]; exact hlen
  have hbuflen2 : b2.val.length < 2 ^ 64 := by
    rw [hlenB]; exact hbuflen
  have hvisX : envLookup (envExtend ρ "x"
      (.i32 (BitVec.ofNat 32 u.toNat))) "vis" =
      some (.stdVecOwned vv vl vc) :=
    envLookup_extend_miss _ _ _ _ _ hvis (by decide)
  have hnX : envLookup (envExtend ρ "x"
      (.i32 (BitVec.ofNat 32 u.toNat))) "n" =
      some (.u64 nn) :=
    envLookup_extend_miss _ _ _ _ _ hn (by decide)
  have hvX : envLookup (envExtend ρ "x"
      (.i32 (BitVec.ofNat 32 u.toNat))) "v" =
      some (.u64 v0) :=
    envLookup_extend_miss _ _ _ _ _ hv (by decide)
  have huX : envLookup (envExtend ρ "x"
      (.i32 (BitVec.ofNat 32 u.toNat))) "u" =
      some (.u64 u) :=
    envLookup_extend_miss _ _ _ _ _ hu (by decide)
  have hcountX : envLookup (envExtend ρ "x"
      (.i32 (BitVec.ofNat 32 u.toNat))) "count" =
      some (.u64 count) :=
    envLookup_extend_miss _ _ _ _ _ hcount (by decide)
  obtain ⟨ρS, hupS⟩ := envUpdate_some_of_lookup (envExtend ρ "x"
      (.i32 (BitVec.ofNat 32 u.toNat))) "st"
      (.stdVecOwned b len cap) (.stdVecOwned b2 len cap) hstX
  have hstepSet : evalStmtFuel F (.vgrowSet "st" (.var "top")
      (.var "x")) (envExtend ρ "x"
      (.i32 (BitVec.ofNat 32 u.toNat))) =
      .ok (ρS, .fellThrough) :=
    evalStmtFuel_vgrowSet F "st" (.var "top") (.var "x")
      (envExtend ρ "x" (.i32 (BitVec.ofNat 32 u.toNat)))
      top (BitVec.ofNat 32 u.toNat) b b2 len cap ρS
      (evalExpr_var_hit _ "top" (.u64 top) htopX)
      (evalExpr_var_hit _ "x" (.i32 (BitVec.ofNat 32 u.toNat))
        hxX)
      hstX hsetB hupS
  have hifS : evalProgStmt vecGrowProg F
      (.if_ (.ult (.var "top") (.vgrowLen "st"))
        (.vgrowSet "st" (.var "top") (.var "x"))
        (.callProg "st" stdVecPushBackName ["st", "x"]))
      (envExtend ρ "x" (.i32 (BitVec.ofNat 32 u.toNat))) =
      evalProgStmt vecGrowProg F
        (.vgrowSet "st" (.var "top") (.var "x"))
        (envExtend ρ "x" (.i32 (BitVec.ofNat 32 u.toNat))) := by
    rw [evalProgStmt_if_true _ _ _ _ _ _ hguardP]
  have hstepSetP : evalProgStmt vecGrowProg F
      (.vgrowSet "st" (.var "top") (.var "x"))
      (envExtend ρ "x" (.i32 (BitVec.ofNat 32 u.toNat))) =
      .ok (ρS, .fellThrough) := by
    have hfb : evalProgStmt vecGrowProg F
        (.vgrowSet "st" (.var "top") (.var "x"))
        (envExtend ρ "x" (.i32 (BitVec.ofNat 32 u.toNat))) =
        evalStmtFuel F (.vgrowSet "st" (.var "top") (.var "x"))
          (envExtend ρ "x" (.i32 (BitVec.ofNat 32 u.toNat))) := by
      simp only [evalProgStmt]
    rw [hfb]
    exact hstepSet
  have hifEv : evalProgStmt vecGrowProg F
      (.if_ (.ult (.var "top") (.vgrowLen "st"))
        (.vgrowSet "st" (.var "top") (.var "x"))
        (.callProg "st" stdVecPushBackName ["st", "x"]))
      (envExtend ρ "x" (.i32 (BitVec.ofNat 32 u.toNat))) =
      .ok (ρS, .fellThrough) :=
    hifS.trans hstepSetP
  -- Post-store lookups.
  have hvisS : envLookup ρS "vis" = some (.stdVecOwned vv vl vc) :=
    (envLookup_update_miss _ "vis" "st" (.stdVecOwned b2 len cap)
      ρS (by decide) hupS).trans hvisX
  have hnS : envLookup ρS "n" = some (.u64 nn) :=
    (envLookup_update_miss _ "n" "st" (.stdVecOwned b2 len cap)
      ρS (by decide) hupS).trans hnX
  have hvS : envLookup ρS "v" = some (.u64 v0) :=
    (envLookup_update_miss _ "v" "st" (.stdVecOwned b2 len cap)
      ρS (by decide) hupS).trans hvX
  have huS : envLookup ρS "u" = some (.u64 u) :=
    (envLookup_update_miss _ "u" "st" (.stdVecOwned b2 len cap)
      ρS (by decide) hupS).trans huX
  have hcountS : envLookup ρS "count" = some (.u64 count) :=
    (envLookup_update_miss _ "count" "st" (.stdVecOwned b2 len cap)
      ρS (by decide) hupS).trans hcountX
  have htopS : envLookup ρS "top" = some (.u64 top) :=
    (envLookup_update_miss _ "top" "st" (.stdVecOwned b2 len cap)
      ρS (by decide) hupS).trans htopX
  have hstS : envLookup ρS "st" = some (.stdVecOwned b2 len cap) :=
    envLookup_update_hit _ "st" _ ρS hupS
  -- The `top` advance.
  have htopE : evalExpr (.uadd (.var "top")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρS =
      .ok (.u64 (top + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ "top" (.u64 top) htopS)
      (evalExpr_lit _ _)
  obtain ⟨ρT, hupT⟩ := envUpdate_some_of_lookup ρS "top"
      (.u64 top) (.u64 (top + 1)) htopS
  have htopA : evalProgStmt vecGrowProg F (.assign "top"
      (.uadd (.var "top") (.lit (.u64 (BitVec.ofNat 64 1)))))
      ρS = .ok (ρT, .fellThrough) := by
    have hfb : evalProgStmt vecGrowProg F (.assign "top"
        (.uadd (.var "top") (.lit (.u64 (BitVec.ofNat 64 1)))))
        ρS =
        evalStmtFuel F (.assign "top" (.uadd (.var "top")
          (.lit (.u64 (BitVec.ofNat 64 1))))) ρS := by
      simp only [evalProgStmt]
    rw [hfb]
    exact evalStmtFuel_assign _ _ _ _ _ _ htopE hupT
  have hvisT : envLookup ρT "vis" = some (.stdVecOwned vv vl vc) :=
    (envLookup_update_miss _ "vis" "top" (.u64 (top + 1)) ρT
      (by decide) hupT).trans hvisS
  have hstT : envLookup ρT "st" = some (.stdVecOwned b2 len cap) :=
    (envLookup_update_miss _ "st" "top" (.u64 (top + 1)) ρT
      (by decide) hupT).trans hstS
  have htopT : envLookup ρT "top" = some (.u64 (top + 1)) :=
    envLookup_update_hit _ "top" _ ρT hupT
  have hnT : envLookup ρT "n" = some (.u64 nn) :=
    (envLookup_update_miss _ "n" "top" (.u64 (top + 1)) ρT
      (by decide) hupT).trans hnS
  have hvT : envLookup ρT "v" = some (.u64 v0) :=
    (envLookup_update_miss _ "v" "top" (.u64 (top + 1)) ρT
      (by decide) hupT).trans hvS
  have hcountT : envLookup ρT "count" = some (.u64 count) :=
    (envLookup_update_miss _ "count" "top" (.u64 (top + 1)) ρT
      (by decide) hupT).trans hcountS
  -- The `count` advance.
  have hcountE : evalExpr (.uadd (.var "count")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρT =
      .ok (.u64 (count + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit ρT "count" (.u64 count) hcountT)
      (evalExpr_lit _ _)
  obtain ⟨ρC, hupC⟩ := envUpdate_some_of_lookup ρT "count"
      (.u64 count) (.u64 (count + 1)) hcountT
  have hcountA : evalProgStmt vecGrowProg F (.assign "count"
      (.uadd (.var "count") (.lit (.u64 (BitVec.ofNat 64 1)))))
      ρT = .ok (ρC, .fellThrough) := by
    have hfb : evalProgStmt vecGrowProg F (.assign "count"
        (.uadd (.var "count") (.lit (.u64 (BitVec.ofNat 64 1)))))
        ρT =
        evalStmtFuel F (.assign "count" (.uadd (.var "count")
          (.lit (.u64 (BitVec.ofNat 64 1))))) ρT := by
      simp only [evalProgStmt]
    rw [hfb]
    exact evalStmtFuel_assign _ _ _ _ _ _ hcountE hupC
  -- Post-count lookups.
  have hvisC : envLookup ρC "vis" = some (.stdVecOwned vv vl vc) :=
    (envLookup_update_miss ρT "vis" "count" (.u64 (count + 1)) ρC
      (by decide) hupC).trans hvisT
  have hstC : envLookup ρC "st" = some (.stdVecOwned b2 len cap) :=
    (envLookup_update_miss ρT "st" "count" (.u64 (count + 1)) ρC
      (by decide) hupC).trans hstT
  have htopC : envLookup ρC "top" = some (.u64 (top + 1)) :=
    (envLookup_update_miss ρT "top" "count" (.u64 (count + 1))
      ρC (by decide) hupC).trans htopT
  have hnC : envLookup ρC "n" = some (.u64 nn) :=
    (envLookup_update_miss ρT "n" "count" (.u64 (count + 1)) ρC
      (by decide) hupC).trans hnT
  have hvC : envLookup ρC "v" = some (.u64 v0) :=
    (envLookup_update_miss ρT "v" "count" (.u64 (count + 1)) ρC
      (by decide) hupC).trans hvT
  have hmC : envLookup ρC "m" = some (.stdVecOwned mv ml mc) :=
    (envLookup_update_miss ρT "m" "count" (.u64 (count + 1)) ρC
      (by decide) hupC).trans
      ((envLookup_update_miss _ "m" "top" (.u64 (top + 1)) ρT
        (by decide) hupT).trans
        ((envLookup_update_miss _ "m" "st" (.stdVecOwned b2 len cap)
          ρS (by decide) hupS).trans
          (envLookup_extend_miss _ _ _ _ _ hm (by decide))))
  have huC : envLookup ρC "u" = some (.u64 u) :=
    (envLookup_update_miss ρT "u" "count" (.u64 (count + 1)) ρC
      (by decide) hupC).trans
      ((envLookup_update_miss _ "u" "top" (.u64 (top + 1)) ρT
        (by decide) hupT).trans huS)
  have hcountC : envLookup ρC "count" = some (.u64 (count + 1)) :=
    envLookup_update_hit _ "count" _ ρC hupC
  -- Whole-push assembly.
  have hPushS : evalProgStmt vecGrowProg F dfsGrowPush ρ =
      .ok (ρC, .fellThrough) := by
    simp only [dfsGrowPush]
    exact (evalProgStmt_seq_fallthrough vecGrowProg F _ _ _ _
      hstepX).trans
      ((evalProgStmt_seq_fallthrough vecGrowProg F _ _ _ _
        hifEv).trans
        ((evalProgStmt_seq_fallthrough vecGrowProg F _ _ _ _
          htopA).trans hcountA))
  exact ⟨ρC, hPushS, hmC, hvisC, hstC, hnC, hvC, htopC, hcountC,
    huC, hlen2, hbuflen2, hfrB⟩

/-- Push-sequence agreement, growth leg: with the reuse guard false
    and the composer push succeeding through the check-length and
    relocation machinery, `dfsGrowPush` runs the `x` let, takes the
    `push_back` branch, and advances `top`/`count`, leaving every
    other binding untouched. (Extracted from the row-ok discovery
    branch; the fuel premise dominates the composer call.) -/
theorem dfsGrowPushGrow_ok (F : Nat) (b : Vec32) (len cap : Nat)
    (top count u : BitVec 64) (ρ : Env)
    (vv : Vec32) (vl vc : Nat)
    (mv : Vec32) (ml mc : Nat) (nn v0 : BitVec 64)
    (pv : Value) (pt : Vec32 × Nat × Nat)
    (hvis : envLookup ρ "vis" = some (.stdVecOwned vv vl vc))
    (hm : envLookup ρ "m" = some (.stdVecOwned mv ml mc))
    (hn : envLookup ρ "n" = some (.u64 nn))
    (hv : envLookup ρ "v" = some (.u64 v0))
    (hst : envLookup ρ "st" = some (.stdVecOwned b len cap))
    (htop : envLookup ρ "top" = some (.u64 top))
    (hcount : envLookup ρ "count" = some (.u64 count))
    (hu : envLookup ρ "u" = some (.u64 u))
    (hlive : b.freed = false)
    (hlen : len ≤ b.val.length)
    (hbuflen : b.val.length < 2 ^ 64)
    (hlen64 : len < 2 ^ 64)
    (hcap64 : cap < 2 ^ 64)
    (hguard : top.ult (BitVec.ofNat 64 len) = false)
    (hmaxC : len ≤ stdVecMaxDiffBV.toNat - 1)
    (hadq : len + 4 ≤ F)
    (hpush : stdVecPushBackFwd b len cap
      (BitVec.ofNat 32 u.toNat) = .ok pv)
    (hown : vecGrowOwned pv = .ok pt) :
    ∃ ρC b2 l2 c2, evalProgStmt vecGrowProg F dfsGrowPush ρ =
        .ok (ρC, .fellThrough) ∧
      envLookup ρC "m" = some (.stdVecOwned mv ml mc) ∧
      envLookup ρC "vis" = some (.stdVecOwned vv vl vc) ∧
      envLookup ρC "st" = some (.stdVecOwned b2 l2 c2) ∧
      envLookup ρC "n" = some (.u64 nn) ∧
      envLookup ρC "v" = some (.u64 v0) ∧
      envLookup ρC "top" = some (.u64 (top + 1)) ∧
      envLookup ρC "count" = some (.u64 (count + 1)) ∧
      envLookup ρC "u" = some (.u64 u) ∧
      b2.freed = false ∧ l2 ≤ b2.val.length ∧
      b2.val.length < 2 ^ 64 ∧ l2 < 2 ^ 64 ∧ c2 < 2 ^ 64 ∧
      l2 = len + 1 ∧ b2 = pt.1 ∧ l2 = pt.2.1 ∧
      c2 = pt.2.2 := by
  -- The `x` let.
  have hxE : evalExpr (.i32ofU64 (.var "u")) ρ =
      .ok (.i32 (BitVec.ofNat 32 u.toNat)) :=
    evalExpr_i32ofU64_ok _ _ _
      (evalExpr_var_hit ρ "u" (.u64 u) hu)
  have hletX : evalStmtFuel F (.let_ "x" (.i 32)
      (.i32ofU64 (.var "u"))) ρ =
      .ok (envExtend ρ "x" (.i32 (BitVec.ofNat 32 u.toNat)),
        .fellThrough) :=
    evalStmtFuel_let_ F "x" (.i 32) (.i32ofU64 (.var "u")) ρ _ hxE
  have hstepX : evalProgStmt vecGrowProg F (.let_ "x" (.i 32)
      (.i32ofU64 (.var "u"))) ρ =
      .ok (envExtend ρ "x" (.i32 (BitVec.ofNat 32 u.toNat)),
        .fellThrough) := by
    rw [evalProgStmt_let_fb]
    exact hletX
  -- The reuse-guard evaluation (false on the growth leg).
  have hstX : envLookup (envExtend ρ "x"
      (.i32 (BitVec.ofNat 32 u.toNat))) "st" =
      some (.stdVecOwned b len cap) :=
    envLookup_extend_miss _ _ _ _ _ hst (by decide)
  have hxX : envLookup (envExtend ρ "x"
      (.i32 (BitVec.ofNat 32 u.toNat))) "x" =
      some (.i32 (BitVec.ofNat 32 u.toNat)) :=
    envLookup_extend_hit _ _ _
  have htopX : envLookup (envExtend ρ "x"
      (.i32 (BitVec.ofNat 32 u.toNat))) "top" =
      some (.u64 top) :=
    envLookup_extend_miss _ _ _ _ _ htop (by decide)
  have hstLenX : evalExpr (.vgrowLen "st") (envExtend ρ "x"
      (.i32 (BitVec.ofNat 32 u.toNat))) =
      .ok (.u64 (BitVec.ofNat 64 len)) :=
    evalExpr_vgrowLen_some "st" _ b len cap hstX
  have hguardP : evalExpr (.ult (.var "top") (.vgrowLen "st"))
      (envExtend ρ "x" (.i32 (BitVec.ofNat 32 u.toNat))) =
      .ok (.b (top.ult (BitVec.ofNat 64 len))) :=
    evalExpr_ult_u64 _ _ _ _ _
      (evalExpr_var_hit _ "top" (.u64 top) htopX) hstLenX
  rw [hguard] at hguardP
  -- The composer push: check-length, fresh storage, relocation.
  have hv0 := vecGrowOwned_ok hown
  obtain ⟨b2, l2, c2, hv2, hfr, hlen2, hbuflen2, h64_2, hcap2,
      hlen1⟩ :=
    stdVecPushBackFwd_ok b len cap (BitVec.ofNat 32 u.toNat) pv
      hlive hlen hbuflen hlen64 hcap64 hmaxC hpush
  obtain ⟨Fp, hFeq, hFp⟩ := fuel_step_down (len + 3) hadq
  have hmaxC' : len ≤ stdVecMaxDiffBV.toNat := by
    omega
  have hcall := evalProgFunc_stdVecPushBack Fp b len cap
      (BitVec.ofNat 32 u.toNat) hlive hmaxC' hlen hbuflen hcap64 hFp
  rw [hpush, hv2] at hcall
  have hargs : lookupArgs (envExtend ρ "x"
      (.i32 (BitVec.ofNat 32 u.toNat))) ["st", "x"] =
      some [.stdVecOwned b len cap,
        .i32 (BitVec.ofNat 32 u.toNat)] :=
    lookupArgs_cons_hit _ _ _ _ _ hstX
      (lookupArgs_cons_hit _ _ _ [] [] hxX (lookupArgs_nil _))
  have hstepPushF : evalProgStmt vecGrowProg (Fp + 1)
      (.callProg "st" stdVecPushBackName ["st", "x"])
      (envExtend ρ "x" (.i32 (BitVec.ofNat 32 u.toNat))) =
      .ok (envExtend (envExtend ρ "x"
        (.i32 (BitVec.ofNat 32 u.toNat)))
        "st" (.stdVecOwned b2 l2 c2), .fellThrough) :=
    evalProgStmt_callProg_ok vecGrowProg Fp "st"
      stdVecPushBackName ["st", "x"]
      (envExtend ρ "x" (.i32 (BitVec.ofNat 32 u.toNat)))
      [.stdVecOwned b len cap, .i32 (BitVec.ofNat 32 u.toNat)]
      stdVecPushBackFunc (.stdVecOwned b2 l2 c2) hargs
      findFunc_stdVecPushBack hcall
  rw [← hFeq] at hstepPushF
  -- The branch: guard false takes the composer call.
  have hifG : evalProgStmt vecGrowProg F
      (.if_ (.ult (.var "top") (.vgrowLen "st"))
        (.vgrowSet "st" (.var "top") (.var "x"))
        (.callProg "st" stdVecPushBackName ["st", "x"]))
      (envExtend ρ "x" (.i32 (BitVec.ofNat 32 u.toNat))) =
      evalProgStmt vecGrowProg F
        (.callProg "st" stdVecPushBackName ["st", "x"])
        (envExtend ρ "x" (.i32 (BitVec.ofNat 32 u.toNat))) := by
    rw [evalProgStmt_if_false _ _ _ _ _ _ hguardP]
  have hifEvG : evalProgStmt vecGrowProg F
      (.if_ (.ult (.var "top") (.vgrowLen "st"))
        (.vgrowSet "st" (.var "top") (.var "x"))
        (.callProg "st" stdVecPushBackName ["st", "x"]))
      (envExtend ρ "x" (.i32 (BitVec.ofNat 32 u.toNat))) =
      .ok (envExtend (envExtend ρ "x"
        (.i32 (BitVec.ofNat 32 u.toNat)))
        "st" (.stdVecOwned b2 l2 c2), .fellThrough) :=
    hifG.trans hstepPushF
  -- Double-extended lookups (post-call env).
  have hvisVxS : envLookup (envExtend (envExtend ρ "x"
      (.i32 (BitVec.ofNat 32 u.toNat)))
      "st" (.stdVecOwned b2 l2 c2)) "vis" =
      some (.stdVecOwned vv vl vc) :=
    envLookup_extend_miss _ _ _ _ _
      (envLookup_extend_miss _ _ _ _ _ hvis (by decide))
      (by decide)
  have hnVxS : envLookup (envExtend (envExtend ρ "x"
      (.i32 (BitVec.ofNat 32 u.toNat)))
      "st" (.stdVecOwned b2 l2 c2)) "n" =
      some (.u64 nn) :=
    envLookup_extend_miss _ _ _ _ _
      (envLookup_extend_miss _ _ _ _ _ hn (by decide))
      (by decide)
  have hvVxS : envLookup (envExtend (envExtend ρ "x"
      (.i32 (BitVec.ofNat 32 u.toNat)))
      "st" (.stdVecOwned b2 l2 c2)) "v" =
      some (.u64 v0) :=
    envLookup_extend_miss _ _ _ _ _
      (envLookup_extend_miss _ _ _ _ _ hv (by decide))
      (by decide)
  have huVxS : envLookup (envExtend (envExtend ρ "x"
      (.i32 (BitVec.ofNat 32 u.toNat)))
      "st" (.stdVecOwned b2 l2 c2)) "u" =
      some (.u64 u) :=
    envLookup_extend_miss _ _ _ _ _
      (envLookup_extend_miss _ _ _ _ _ hu (by decide))
      (by decide)
  have hcountVxS : envLookup (envExtend (envExtend ρ "x"
      (.i32 (BitVec.ofNat 32 u.toNat)))
      "st" (.stdVecOwned b2 l2 c2)) "count" =
      some (.u64 count) :=
    envLookup_extend_miss _ _ _ _ _
      (envLookup_extend_miss _ _ _ _ _ hcount (by decide))
      (by decide)
  have htopVxS : envLookup (envExtend (envExtend ρ "x"
      (.i32 (BitVec.ofNat 32 u.toNat)))
      "st" (.stdVecOwned b2 l2 c2)) "top" =
      some (.u64 top) :=
    envLookup_extend_miss _ _ _ _ _
      (envLookup_extend_miss _ _ _ _ _ htop (by decide))
      (by decide)
  have hmVxS : envLookup (envExtend (envExtend ρ "x"
      (.i32 (BitVec.ofNat 32 u.toNat)))
      "st" (.stdVecOwned b2 l2 c2)) "m" =
      some (.stdVecOwned mv ml mc) :=
    envLookup_extend_miss _ _ _ _ _
      (envLookup_extend_miss _ _ _ _ _ hm (by decide))
      (by decide)
  -- The `top` advance.
  have htopE : evalExpr (.uadd (.var "top")
      (.lit (.u64 (BitVec.ofNat 64 1))))
      (envExtend (envExtend ρ "x"
        (.i32 (BitVec.ofNat 32 u.toNat)))
        "st" (.stdVecOwned b2 l2 c2)) =
      .ok (.u64 (top + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit _ "top" (.u64 top) htopVxS)
      (evalExpr_lit _ _)
  obtain ⟨ρT, hupT⟩ := envUpdate_some_of_lookup
      (envExtend (envExtend ρ "x"
        (.i32 (BitVec.ofNat 32 u.toNat)))
        "st" (.stdVecOwned b2 l2 c2)) "top"
      (.u64 top) (.u64 (top + 1)) htopVxS
  have htopA : evalProgStmt vecGrowProg F (.assign "top"
      (.uadd (.var "top") (.lit (.u64 (BitVec.ofNat 64 1)))))
      (envExtend (envExtend ρ "x"
        (.i32 (BitVec.ofNat 32 u.toNat)))
        "st" (.stdVecOwned b2 l2 c2)) =
      .ok (ρT, .fellThrough) := by
    have hfb : evalProgStmt vecGrowProg F (.assign "top"
        (.uadd (.var "top") (.lit (.u64 (BitVec.ofNat 64 1)))))
        (envExtend (envExtend ρ "x"
          (.i32 (BitVec.ofNat 32 u.toNat)))
          "st" (.stdVecOwned b2 l2 c2)) =
        evalStmtFuel F (.assign "top" (.uadd (.var "top")
          (.lit (.u64 (BitVec.ofNat 64 1)))))
          (envExtend (envExtend ρ "x"
            (.i32 (BitVec.ofNat 32 u.toNat)))
            "st" (.stdVecOwned b2 l2 c2)) := by
      simp only [evalProgStmt]
    rw [hfb]
    exact evalStmtFuel_assign _ _ _ _ _ _ htopE hupT
  have hvisT : envLookup ρT "vis" = some (.stdVecOwned vv vl vc) :=
    (envLookup_update_miss _ "vis" "top" (.u64 (top + 1)) ρT
      (by decide) hupT).trans hvisVxS
  have hstX2 : envLookup (envExtend (envExtend ρ "x"
      (.i32 (BitVec.ofNat 32 u.toNat)))
      "st" (.stdVecOwned b2 l2 c2)) "st" =
      some (.stdVecOwned b2 l2 c2) :=
    envLookup_extend_hit _ _ _
  have hstT : envLookup ρT "st" = some (.stdVecOwned b2 l2 c2) :=
    (envLookup_update_miss _ "st" "top" (.u64 (top + 1)) ρT
      (by decide) hupT).trans hstX2
  have htopT : envLookup ρT "top" = some (.u64 (top + 1)) :=
    envLookup_update_hit _ "top" _ ρT hupT
  have hnT : envLookup ρT "n" = some (.u64 nn) :=
    (envLookup_update_miss _ "n" "top" (.u64 (top + 1)) ρT
      (by decide) hupT).trans hnVxS
  have hvT : envLookup ρT "v" = some (.u64 v0) :=
    (envLookup_update_miss _ "v" "top" (.u64 (top + 1)) ρT
      (by decide) hupT).trans hvVxS
  have hcountT : envLookup ρT "count" = some (.u64 count) :=
    (envLookup_update_miss _ "count" "top" (.u64 (top + 1)) ρT
      (by decide) hupT).trans hcountVxS
  -- The `count` advance.
  have hcountE : evalExpr (.uadd (.var "count")
      (.lit (.u64 (BitVec.ofNat 64 1)))) ρT =
      .ok (.u64 (count + 1)) :=
    evalExpr_uadd_u64 _ _ _ _ _
      (evalExpr_var_hit ρT "count" (.u64 count) hcountT)
      (evalExpr_lit _ _)
  obtain ⟨ρC, hupC⟩ := envUpdate_some_of_lookup ρT "count"
      (.u64 count) (.u64 (count + 1)) hcountT
  have hcountA : evalProgStmt vecGrowProg F (.assign "count"
      (.uadd (.var "count") (.lit (.u64 (BitVec.ofNat 64 1)))))
      ρT = .ok (ρC, .fellThrough) := by
    have hfb : evalProgStmt vecGrowProg F (.assign "count"
        (.uadd (.var "count") (.lit (.u64 (BitVec.ofNat 64 1)))))
        ρT =
        evalStmtFuel F (.assign "count" (.uadd (.var "count")
          (.lit (.u64 (BitVec.ofNat 64 1))))) ρT := by
      simp only [evalProgStmt]
    rw [hfb]
    exact evalStmtFuel_assign _ _ _ _ _ _ hcountE hupC
  -- Post-count lookups.
  have hvisC : envLookup ρC "vis" = some (.stdVecOwned vv vl vc) :=
    (envLookup_update_miss ρT "vis" "count" (.u64 (count + 1)) ρC
      (by decide) hupC).trans hvisT
  have hstC : envLookup ρC "st" = some (.stdVecOwned b2 l2 c2) :=
    (envLookup_update_miss ρT "st" "count" (.u64 (count + 1)) ρC
      (by decide) hupC).trans hstT
  have htopC : envLookup ρC "top" = some (.u64 (top + 1)) :=
    (envLookup_update_miss ρT "top" "count" (.u64 (count + 1))
      ρC (by decide) hupC).trans htopT
  have hnC : envLookup ρC "n" = some (.u64 nn) :=
    (envLookup_update_miss ρT "n" "count" (.u64 (count + 1)) ρC
      (by decide) hupC).trans hnT
  have hvC : envLookup ρC "v" = some (.u64 v0) :=
    (envLookup_update_miss ρT "v" "count" (.u64 (count + 1)) ρC
      (by decide) hupC).trans hvT
  have hmC : envLookup ρC "m" = some (.stdVecOwned mv ml mc) :=
    (envLookup_update_miss ρT "m" "count" (.u64 (count + 1)) ρC
      (by decide) hupC).trans
      ((envLookup_update_miss _ "m" "top" (.u64 (top + 1)) ρT
        (by decide) hupT).trans hmVxS)
  have huC : envLookup ρC "u" = some (.u64 u) :=
    (envLookup_update_miss ρT "u" "count" (.u64 (count + 1)) ρC
      (by decide) hupC).trans
      ((envLookup_update_miss _ "u" "top" (.u64 (top + 1)) ρT
        (by decide) hupT).trans huVxS)
  have hcountC : envLookup ρC "count" = some (.u64 (count + 1)) :=
    envLookup_update_hit _ "count" _ ρC hupC
  -- The composer's triple is the forward's `pt`.
  have hconnV : (Value.stdVecOwned b2 l2 c2 : Value) =
      Value.stdVecOwned pt.1 pt.2.1 pt.2.2 := hv2.symm.trans hv0
  simp only [Value.stdVecOwned.injEq] at hconnV
  obtain ⟨e1, e2, e3⟩ := hconnV
  -- Whole-push assembly.
  have hPushG : evalProgStmt vecGrowProg F dfsGrowPush ρ =
      .ok (ρC, .fellThrough) := by
    simp only [dfsGrowPush]
    exact (evalProgStmt_seq_fallthrough vecGrowProg F _ _ _ _
      hstepX).trans
      ((evalProgStmt_seq_fallthrough vecGrowProg F _ _ _ _
        hifEvG).trans
        ((evalProgStmt_seq_fallthrough vecGrowProg F _ _ _ _
          htopA).trans hcountA))
  exact ⟨ρC, b2, l2, c2, hPushG, hmC, hvisC, hstC, hnC, hvC,
    htopC, hcountC, huC, hfr, hlen2, hbuflen2, h64_2, hcap2,
    hlen1, e1, e2, e3⟩

/-! ## Row-scan agreement -/

/-- Row-scan agreement (ok leg): the `u` loop evaluates exactly as
    the row forward says, threading the post lookups. Induction on
    fuel; each taken arm mirrors its evaluator steps, the loop
    recurses through the IH at predecessor fuel. -/
theorem dfsGrowRow_ok (F : Nat) (mL visL : List (BitVec 32))
    (b : Vec32) (len cap : Nat) (n v top count u : BitVec 64) (ρ : Env)
    (L0 : Nat)
    (hm : envLookup ρ "m" =
      some (.stdVecOwned ⟨mL, false⟩ mL.length mL.length))
    (hmen : mL.length < 2 ^ 64)
    (hvis : envLookup ρ "vis" =
      some (.stdVecOwned ⟨visL, false⟩ visL.length visL.length))
    (hvislen : visL.length < 2 ^ 64)
    (hst : envLookup ρ "st" = some (.stdVecOwned b len cap))
    (hlive : b.freed = false)
    (hlen : len ≤ b.val.length)
    (hbuflen : b.val.length < 2 ^ 64)
    (hlen64 : len < 2 ^ 64)
    (hcap64 : cap < 2 ^ 64)
    (hP : L0 + visL.length + 8 + (n.toNat - u.toNat) ≤ F)
    (hLV : L0 + visL.length + 1 < 2 ^ 64)
    (hcnt : len ≤ L0 + ones visL)
    (htopLe : top.toNat ≤ len)
    (hn : envLookup ρ "n" = some (.u64 n))
    (hv : envLookup ρ "v" = some (.u64 v))
    (htop : envLookup ρ "top" = some (.u64 top))
    (hcount : envLookup ρ "count" = some (.u64 count))
    (hu : envLookup ρ "u" = some (.u64 u))
    (vis' : List (BitVec 32)) (b' : Vec32) (l' c' : Nat)
    (top' count' u' : BitVec 64)
    (hrow : dfsGrowRowFwd F mL visL b len cap n v top count u =
      .ok (vis', b', l', c', top', count', u')) :
    ∃ ρ', evalProgStmt vecGrowProg F dfsGrowInner ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "m" =
        some (.stdVecOwned ⟨mL, false⟩ mL.length mL.length) ∧
      envLookup ρ' "vis" =
        some (.stdVecOwned ⟨vis', false⟩ visL.length visL.length) ∧
      envLookup ρ' "st" = some (.stdVecOwned b' l' c') ∧
      envLookup ρ' "n" = some (.u64 n) ∧
      envLookup ρ' "v" = some (.u64 v) ∧
      envLookup ρ' "top" = some (.u64 top') ∧
      envLookup ρ' "count" = some (.u64 count') ∧
      envLookup ρ' "u" = some (.u64 u') ∧
      b'.freed = false ∧ l' ≤ b'.val.length ∧
      b'.val.length < 2 ^ 64 ∧ l' < 2 ^ 64 ∧ c' < 2 ^ 64 ∧
      l' ≤ L0 + ones vis' ∧ ones visL ≤ ones vis' ∧
      top'.toNat + ones visL = top.toNat + ones vis' ∧
      top'.toNat ≤ l' := by
  -- Measure induction on the remaining scan `n.toNat - u.toNat`.
  -- Fuel `F` is generalized (it drops through `while_` entry) while
  -- the absolute adequacy premise `hP` is preserved exactly: each
  -- iteration consumes one fuel and advances `u` by one, so both
  -- sides drop by one. `L0`/`n`/`v`/`m` never change.
  obtain ⟨k, hk⟩ : ∃ k, n.toNat - u.toNat = k := ⟨_, rfl⟩
  induction k generalizing u visL b len cap F top count ρ with
  | zero =>
    cases huLT : u.ult n with
    | false =>
      cases F with
      | zero =>
        -- `cases hrow` substitutes the forward equation backward
        -- (unprimed state vars are replaced by the primed witnesses),
        -- so the skip lemma is applied at the primed state.
        simp only [dfsGrowRowFwd, huLT, ↓reduceIte] at hrow
        cases hrow
        exact dfsGrowRow_skip 0 mL vis' b' l' c' n v top' count' u' ρ
          L0 hm hvis hvislen hst hlive hlen hbuflen hlen64 hcap64
          hcnt htopLe hn hv htop hcount hu huLT
      | succ G =>
        simp only [dfsGrowRowFwd, huLT, ↓reduceIte] at hrow
        cases hrow
        exact dfsGrowRow_skip (G + 1) mL vis' b' l' c' n v top' count'
          u' ρ L0 hm hvis hvislen hst hlive hlen hbuflen hlen64
          hcap64 hcnt htopLe hn hv htop hcount hu huLT
    | true =>
      have huN : u.toNat < n.toNat := by
        have h := huLT
        rw [BitVec.ult_eq_decide, decide_eq_true_eq] at h
        exact h
      omega
  | succ k ih =>
    cases huLT : u.ult n with
    | false =>
      cases F with
      | zero =>
        simp only [dfsGrowRowFwd, huLT, ↓reduceIte] at hrow
        cases hrow
        exact dfsGrowRow_skip 0 mL vis' b' l' c' n v top' count' u' ρ
          L0 hm hvis hvislen hst hlive hlen hbuflen hlen64 hcap64
          hcnt htopLe hn hv htop hcount hu huLT
      | succ G =>
        simp only [dfsGrowRowFwd, huLT, ↓reduceIte] at hrow
        cases hrow
        exact dfsGrowRow_skip (G + 1) mL vis' b' l' c' n v top' count'
          u' ρ L0 hm hvis hvislen hst hlive hlen hbuflen hlen64
          hcap64 hcnt htopLe hn hv htop hcount hu huLT
    | true =>
      -- `u < n` as naturals (for the measure equation and wrap-freedom).
      have huN : u.toNat < n.toNat := by
        have h := huLT
        rw [BitVec.ult_eq_decide, decide_eq_true_eq] at h
        exact h
      -- `u + 1` does not wrap (`u < n < 2^64`).
      have hwrapU : (u + 1).toNat = u.toNat + 1 := by
        have h1 : ((1 : BitVec 64)).toNat = 1 := rfl
        have hn64 : n.toNat < 2 ^ 64 := BitVec.isLt n
        have hmod : (u.toNat + 1) % 2 ^ 64 = u.toNat + 1 := by
          apply Nat.mod_eq_of_lt
          omega
        calc (u + 1).toNat
            = (u.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 :=
              BitVec.toNat_add _ _
          _ = u.toNat + 1 := by rw [h1]; exact hmod
      -- Fuel casing: at zero fuel the forward errors (vacuous); at
      -- successor fuel the body runs at the predecessor. The `succ`
      -- predecessor shadows `F`, so the body below is verbatim.
      cases F with
      | zero =>
        simp only [dfsGrowRowFwd, huLT, ↓reduceIte] at hrow
        cases hrow
      | succ F =>
        simp only [dfsGrowRowFwd, huLT, ↓reduceIte] at hrow
        -- Shared guard facts: the flat index and its matrix bound.
        have hguardU : evalExpr (.ult (.var "u") (.var "n")) ρ =
            .ok (.b true) := by
          have h1 := evalExpr_var_hit ρ "u" (.u64 u) hu
          have h2 := evalExpr_var_hit ρ "n" (.u64 n) hn
          have h3 := evalExpr_ult_u64 _ _ _ _ _ h1 h2
          rw [huLT] at h3
          exact h3
        have hvn : evalExpr (.umul (.var "v") (.var "n")) ρ =
            .ok (.u64 (v * n)) :=
          evalExpr_umul_u64 _ _ _ _ _
            (evalExpr_var_hit ρ "v" (.u64 v) hv)
            (evalExpr_var_hit ρ "n" (.u64 n) hn)
        have huV : evalExpr (.var "u") ρ = .ok (.u64 u) :=
          evalExpr_var_hit ρ "u" (.u64 u) hu
        have hidx : evalExpr dfsGrowRowIdx ρ = .ok (.u64 (v * n + u)) := by
          simp only [dfsGrowRowIdx]
          exact evalExpr_uadd_u64 _ _ _ _ _ hvn huV
        have hmLen : evalExpr (.vgrowLen "m") ρ =
            .ok (.u64 (BitVec.ofNat 64 mL.length)) :=
          evalExpr_vgrowLen_some "m" ρ ⟨mL, false⟩ mL.length mL.length hm
        have hgIdx : evalExpr (.ult dfsGrowRowIdx (.vgrowLen "m")) ρ =
            .ok (.b ((v * n + u).ult (BitVec.ofNat 64 mL.length))) :=
          evalExpr_ult_u64 _ _ _ _ _ hidx hmLen
        by_cases hidxB :
            (v * n + u).ult (BitVec.ofNat 64 mL.length) = true
        · rw [hidxB] at hgIdx
          simp only [hidxB] at hrow
          cases hgetM : mL[(v * n + u).toNat]? with
          | none =>
            simp only [hgetM, ↓reduceIte] at hrow
            cases hrow
          | some g =>
            simp only [hgetM, ↓reduceIte] at hrow
            by_cases hltM : (v * n + u).toNat < mL.length
            · simp only [hltM, ↓reduceIte] at hrow
              have hmv : evalExpr (.vgrowAt "m" dfsGrowRowIdx) ρ =
                  .ok (.i32 g) :=
                evalExpr_vgrowAt_some "m" _ ρ ⟨mL, false⟩ mL.length
                  mL.length (v * n + u) g hm hidx rfl hgetM hltM
              have hgNe : evalExpr (.une (.vgrowAt "m" dfsGrowRowIdx)
                  (.lit (.i32 (BitVec.ofNat 32 0)))) ρ =
                  .ok (.b (g != (BitVec.ofNat 32 0))) :=
                evalExpr_une_i32 (.vgrowAt "m" dfsGrowRowIdx)
                  (.lit (.i32 (BitVec.ofNat 32 0))) ρ g
                  (BitVec.ofNat 32 0) hmv (evalExpr_lit _ _)
              by_cases hg0 : (g != (BitVec.ofNat 32 0)) = true
              · rw [hg0] at hgNe
                simp only [hg0] at hrow
                have hvisLenE : evalExpr (.vgrowLen "vis") ρ =
                    .ok (.u64 (BitVec.ofNat 64 visL.length)) :=
                  evalExpr_vgrowLen_some "vis" ρ ⟨visL, false⟩
                    visL.length visL.length hvis
                have hgU : evalExpr (.ult (.var "u")
                    (.vgrowLen "vis")) ρ =
                    .ok (.b (u.ult (BitVec.ofNat 64 visL.length))) :=
                  evalExpr_ult_u64 _ _ _ _ _ huV hvisLenE
                by_cases huVlen :
                    u.ult (BitVec.ofNat 64 visL.length) = true
                · rw [huVlen] at hgU
                  simp only [huVlen] at hrow
                  cases hgetV : visL[u.toNat]? with
                  | none =>
                    simp only [hgetV, ↓reduceIte] at hrow
                    cases hrow
                  | some w =>
                    simp only [hgetV, ↓reduceIte] at hrow
                    by_cases hltV : u.toNat < visL.length
                    · simp only [hltV, ↓reduceIte] at hrow
                      have hwv : evalExpr (.vgrowAt "vis" (.var "u")) ρ =
                          .ok (.i32 w) :=
                        evalExpr_vgrowAt_some "vis" _ ρ ⟨visL, false⟩
                          visL.length visL.length u w hvis huV rfl
                          hgetV hltV
                      have hwEq : evalExpr (.ueq
                          (.vgrowAt "vis" (.var "u"))
                          (.lit (.i32 (BitVec.ofNat 32 0)))) ρ =
                          .ok (.b (w == (BitVec.ofNat 32 0))) :=
                        evalExpr_ueq_i32 (.vgrowAt "vis" (.var "u"))
                          (.lit (.i32 (BitVec.ofNat 32 0))) ρ w
                          (BitVec.ofNat 32 0) hwv (evalExpr_lit _ _)
                      by_cases hw0 :
                          (w == (BitVec.ofNat 32 0)) = true
                      · rw [hw0] at hwEq
                        simp only [hw0] at hrow
                        have hL1 : evalProgStmt vecGrowProg F
                            (.if_ (.ult dfsGrowRowIdx
                              (.vgrowLen "m"))
                              (.if_ (.une
                                (.vgrowAt "m" dfsGrowRowIdx)
                                (.lit (.i32
                                  (BitVec.ofNat 32 0))))
                                (.if_ (.ult (.var "u")
                                  (.vgrowLen "vis"))
                                  (.if_ (.ueq
                                    (.vgrowAt "vis" (.var "u"))
                                    (.lit (.i32
                                      (BitVec.ofNat 32 0))))
                                    (.seq (.vgrowSet "vis"
                                      (.var "u")
                                      (.lit (.i32
                                        (BitVec.ofNat 32 1))))
                                      dfsGrowPush)
                                    .skip)
                                  .fail)
                                .skip)
                              .fail) ρ =
                            evalProgStmt vecGrowProg F
                              (.seq (.vgrowSet "vis" (.var "u")
                                (.lit (.i32
                                  (BitVec.ofNat 32 1))))
                                dfsGrowPush) ρ := by
                          rw [evalProgStmt_if_true _ _ _ _ _ _
                            hgIdx,
                            evalProgStmt_if_true _ _ _ _ _ _
                            hgNe,
                            evalProgStmt_if_true _ _ _ _ _ _
                            hgU,
                            evalProgStmt_if_true _ _ _ _ _ _
                            hwEq]

                        have hset : vecSet ⟨visL, false⟩
                            u.toNat 1 =
                            .ok ⟨visL.set u.toNat 1,
                              false⟩ := by
                          unfold vecSet
                          simp [hltV]
                        obtain ⟨ρV, huv⟩ :=
                          envUpdate_some_of_lookup ρ "vis"
                            (.stdVecOwned ⟨visL, false⟩
                              visL.length visL.length)
                            (.stdVecOwned
                              ⟨visL.set u.toNat 1, false⟩
                              visL.length visL.length) hvis
                        have hmark := evalStmtFuel_vgrowSet F
                          "vis" (.var "u")
                          (.lit (.i32 (BitVec.ofNat 32 1))) ρ u
                          (BitVec.ofNat 32 1) ⟨visL, false⟩
                          ⟨visL.set u.toNat 1, false⟩
                          visL.length visL.length ρV
                          (evalExpr_var_hit ρ "u" (.u64 u) hu)
                          rfl hvis hset huv
                        have hfbMark : evalProgStmt vecGrowProg F
                            (.vgrowSet "vis" (.var "u")
                              (.lit (.i32
                                (BitVec.ofNat 32 1)))) ρ =
                            evalStmtFuel F
                              (.vgrowSet "vis" (.var "u")
                                (.lit (.i32
                                  (BitVec.ofNat 32 1)))) ρ := by
                          simp only [evalProgStmt]
                        have hstepMark : evalProgStmt vecGrowProg F
                            (.vgrowSet "vis" (.var "u")
                              (.lit (.i32
                                (BitVec.ofNat 32 1)))) ρ =
                            .ok (ρV, .fellThrough) := by
                          rw [hfbMark]
                          exact hmark
                        have hsetlen : (visL.set u.toNat 1).length =
                            visL.length := by
                          simp
                        have hmV : envLookup ρV "m" =
                            some (.stdVecOwned ⟨mL, false⟩
                              mL.length mL.length) :=
                          (envLookup_update_miss ρ "m" "vis"
                            (.stdVecOwned
                              ⟨visL.set u.toNat 1, false⟩
                              visL.length visL.length) ρV
                            (by decide) huv).trans hm
                        have hnV : envLookup ρV "n" =
                            some (.u64 n) :=
                          (envLookup_update_miss ρ "n" "vis"
                            (.stdVecOwned
                              ⟨visL.set u.toNat 1, false⟩
                              visL.length visL.length) ρV
                            (by decide) huv).trans hn
                        have hvV : envLookup ρV "v" =
                            some (.u64 v) :=
                          (envLookup_update_miss ρ "v" "vis"
                            (.stdVecOwned
                              ⟨visL.set u.toNat 1, false⟩
                              visL.length visL.length) ρV
                            (by decide) huv).trans hv
                        have htopV : envLookup ρV "top" =
                            some (.u64 top) :=
                          (envLookup_update_miss ρ "top" "vis"
                            (.stdVecOwned
                              ⟨visL.set u.toNat 1, false⟩
                              visL.length visL.length) ρV
                            (by decide) huv).trans htop
                        have hcountV : envLookup ρV "count" =
                            some (.u64 count) :=
                          (envLookup_update_miss ρ "count" "vis"
                            (.stdVecOwned
                              ⟨visL.set u.toNat 1, false⟩
                              visL.length visL.length) ρV
                            (by decide) huv).trans hcount
                        have huV2 : envLookup ρV "u" =
                            some (.u64 u) :=
                          (envLookup_update_miss ρ "u" "vis"
                            (.stdVecOwned
                              ⟨visL.set u.toNat 1, false⟩
                              visL.length visL.length) ρV
                            (by decide) huv).trans hu
                        have hvisV : envLookup ρV "vis" =
                            some (.stdVecOwned
                              ⟨visL.set u.toNat 1, false⟩
                              visL.length visL.length) :=
                          envLookup_update_hit ρ "vis" _ ρV huv
                        have hstV : envLookup ρV "st" =
                            some (.stdVecOwned b len cap) :=
                          (envLookup_update_miss ρ "st" "vis"
                            (.stdVecOwned
                              ⟨visL.set u.toNat 1, false⟩
                              visL.length visL.length) ρV
                            (by decide) huv).trans hst
                        by_cases htl :
                            top.ult (BitVec.ofNat 64 len) = true
                        · simp only [htl, ↓reduceIte] at hrow
                          -- Slot reuse (`top < len`): the guarded store
                          -- hits; length and capacity are unchanged.
                          have hw00 : w = 0 := by simpa using hw0
                          have hvis0 : visL[u.toNat]? =
                              some (0 : BitVec 32) := by
                            simpa [hw00] using hgetV
                          have honesU : ones (visL.set u.toNat 1) =
                              ones visL + 1 :=
                            ones_set_one visL u.toNat hvis0
                          have htlN : top.toNat < len := by
                            have h := htl
                            rw [BitVec.ult_eq_decide,
                              decide_eq_true_eq] at h
                            have ho : (BitVec.ofNat 64 len).toNat =
                                len := by
                              rw [BitVec.toNat_ofNat]
                              exact Nat.mod_eq_of_lt hlen64
                            omega
                          cases hsetB : vecSet b top.toNat
                              (BitVec.ofNat 32 u.toNat) with
                          | error e =>
                            simp only [hsetB] at hrow
                            cases hrow
                          | ok b2 =>
                            simp only [hsetB] at hrow
                            -- The push sequence (slot leg): factored
                            -- into `dfsGrowPushSlot_ok`.
                            obtain ⟨ρC, hPushS, hmC, hvisC, hstC,
                                hnC, hvC, htopC, hcountC, huC,
                                hlen2, hbuflen2, hfrB⟩ :=
                              dfsGrowPushSlot_ok F b b2 len cap top
                                count u ρV
                                ⟨visL.set u.toNat 1, false⟩
                                visL.length visL.length
                                ⟨mL, false⟩ mL.length mL.length n v
                                hvisV hmV hnV hvV hstV htopV hcountV
                                huV2 hlen hbuflen hlen64 htl hsetB
                            obtain ⟨ρU, hupU⟩ :=
                              envUpdate_some_of_lookup ρC "u"
                                (.u64 u) (.u64 (u + 1)) huC
                            obtain ⟨huA, huU⟩ :=
                              evalProgUAdv F ρC u huC ρU hupU
                            have hmB : envLookup ρU "m" =
                                some (.stdVecOwned ⟨mL, false⟩
                                  mL.length mL.length) :=
                              (envLookup_update_miss ρC "m" "u"
                                (.u64 (u + 1)) ρU
                                (by decide) hupU).trans hmC
                            have hnB : envLookup ρU "n" =
                                some (.u64 n) :=
                              (envLookup_update_miss ρC "n" "u"
                                (.u64 (u + 1)) ρU
                                (by decide) hupU).trans hnC
                            have hvB : envLookup ρU "v" =
                                some (.u64 v) :=
                              (envLookup_update_miss ρC "v" "u"
                                (.u64 (u + 1)) ρU
                                (by decide) hupU).trans hvC
                            have htopB : envLookup ρU "top" =
                                some (.u64 (top + 1)) :=
                              (envLookup_update_miss ρC "top" "u"
                                (.u64 (u + 1)) ρU
                                (by decide) hupU).trans htopC
                            have hcountB : envLookup ρU "count" =
                                some (.u64 (count + 1)) :=
                              (envLookup_update_miss ρC "count" "u"
                                (.u64 (u + 1)) ρU
                                (by decide) hupU).trans hcountC
                            have hvisB : envLookup ρU "vis" =
                                some (.stdVecOwned
                                  ⟨visL.set u.toNat 1, false⟩
                                  (visL.set u.toNat 1).length
                                  (visL.set u.toNat 1).length) := by
                              rw [hsetlen]
                              exact (envLookup_update_miss ρC "vis"
                                "u" (.u64 (u + 1)) ρU
                                (by decide) hupU).trans hvisC
                            have hvislenB :
                                (visL.set u.toNat 1).length <
                                2 ^ 64 := by
                              rw [hsetlen]
                              exact hvislen
                            have hstB : envLookup ρU "st" =
                                some (.stdVecOwned b2 len cap) :=
                              (envLookup_update_miss ρC "st" "u"
                                (.u64 (u + 1)) ρU
                                (by decide) hupU).trans hstC
                            have hwrapTop : (top + 1).toNat =
                                top.toNat + 1 := by
                              have h1 : ((1 : BitVec 64)).toNat = 1 :=
                                rfl
                              have hmod : (top.toNat + 1) % 2 ^ 64 =
                                  top.toNat + 1 := by
                                apply Nat.mod_eq_of_lt
                                omega
                              calc (top + 1).toNat
                                  = (top.toNat +
                                    (1 : BitVec 64).toNat) % 2 ^ 64 :=
                                    BitVec.toNat_add _ _
                                _ = top.toNat + 1 := by
                                  rw [h1]; exact hmod
                            have hP' : L0 +
                                (visL.set u.toNat 1).length + 8 +
                                (n.toNat - (u + 1).toNat) ≤ F := by
                              rw [hsetlen, hwrapU]
                              omega
                            have hLV' : L0 +
                                (visL.set u.toNat 1).length + 1 <
                                2 ^ 64 := by
                              rw [hsetlen]
                              exact hLV
                            have hcnt' : len ≤
                                L0 + ones (visL.set u.toNat 1) := by
                              rw [honesU]
                              omega
                            have htopLe' : (top + 1).toNat ≤ len := by
                              rw [hwrapTop]
                              omega
                            have hmono' : ones visL ≤
                                ones (visL.set u.toNat 1) := by
                              rw [honesU]
                              omega
                            have hlock' : (top + 1).toNat + ones visL =
                                top.toNat +
                                  ones (visL.set u.toNat 1) := by
                              rw [hwrapTop, honesU]
                              omega
                            have hNu : n.toNat - (u + 1).toNat = k := by
                              rw [hwrapU]
                              omega
                            have hmonoStep : ones visL ≤
                                ones (visL.set u.toNat 1) := by
                              rw [honesU]
                              exact Nat.le_succ _
                            obtain ⟨ρ', ihEval, ihM, ihVis, ihSt, ihN,
                                ihV, ihTop, ihCount, ihU, ihFr, ihLe,
                                ihBuflen, ih64, ihCap, ihCnt, ihMono,
                                ihLock, ihTopLe⟩ :=
                              ih F (visL.set u.toNat 1) b2 len cap
                                (top + 1) (count + 1) (u + 1) ρU
                                hmB hvisB hvislenB hstB hfrB hlen2
                                hbuflen2 hlen64 hcap64 hP' hLV' hcnt'
                                htopLe' hnB hvB htopB
                                hcountB huU hrow hNu
                            have hmono : ones visL ≤ ones vis' :=
                              Nat.le_trans hmonoStep ihMono
                            have eLock : top'.toNat + (ones visL + 1) =
                                (top.toNat + 1) + ones vis' := by
                              have e := ihLock
                              rw [hwrapTop, honesU] at e
                              exact e
                            have hlock : top'.toNat + ones visL =
                                top.toNat + ones vis' := by
                              omega
                            have hL4S : evalProgStmt vecGrowProg F
                                (.seq (.vgrowSet "vis" (.var "u")
                                  (.lit (.i32
                                    (BitVec.ofNat 32 1))))
                                  dfsGrowPush) ρ =
                                .ok (ρC, .fellThrough) :=
                              (evalProgStmt_seq_fallthrough vecGrowProg
                                F _ _ _ _ hstepMark).trans hPushS
                            have hL1evS : evalProgStmt vecGrowProg F
                                (.if_ (.ult dfsGrowRowIdx
                                  (.vgrowLen "m"))
                                  (.if_ (.une
                                    (.vgrowAt "m" dfsGrowRowIdx)
                                    (.lit (.i32
                                      (BitVec.ofNat 32 0))))
                                    (.if_ (.ult (.var "u")
                                      (.vgrowLen "vis"))
                                      (.if_ (.ueq
                                        (.vgrowAt "vis" (.var "u"))
                                        (.lit (.i32
                                          (BitVec.ofNat 32 0))))
                                        (.seq (.vgrowSet "vis"
                                          (.var "u")
                                          (.lit (.i32
                                            (BitVec.ofNat 32 1))))
                                          dfsGrowPush)
                                        .skip)
                                      .fail)
                                    .skip)
                                  .fail) ρ =
                                .ok (ρC, .fellThrough) :=
                              hL1.trans hL4S
                            have hBodyS : evalProgStmt vecGrowProg F
                                (.seq (.if_
                                  (.ult dfsGrowRowIdx (.vgrowLen "m"))
                                  (.if_ (.une
                                    (.vgrowAt "m" dfsGrowRowIdx)
                                    (.lit (.i32
                                      (BitVec.ofNat 32 0))))
                                    (.if_ (.ult (.var "u")
                                      (.vgrowLen "vis"))
                                      (.if_ (.ueq
                                        (.vgrowAt "vis" (.var "u"))
                                        (.lit (.i32
                                          (BitVec.ofNat 32 0))))
                                        (.seq (.vgrowSet "vis"
                                          (.var "u")
                                          (.lit (.i32
                                            (BitVec.ofNat 32 1))))
                                          dfsGrowPush)
                                        .skip)
                                      .fail)
                                    .skip)
                                  .fail)
                                (.assign "u" (.uadd (.var "u")
                                  (.lit (.u64
                                    (BitVec.ofNat 64 1)))))) ρ =
                                .ok (ρU, .fellThrough) :=
                              (evalProgStmt_seq_fallthrough vecGrowProg
                                F _ _ _ _ hL1evS).trans huA
                            simp only [dfsGrowInner, dfsGrowInnerBody] at ⊢ ihEval
                            rw [hsetlen] at ihVis
                            refine ⟨ρ', ?_, ihM, ihVis, ihSt, ihN,
                              ihV, ihTop, ihCount, ihU, ihFr, ihLe,
                              ihBuflen, ih64, ihCap, ihCnt, hmono,
                              hlock, ihTopLe⟩
                            rw [evalProgStmt_while_true _ _ _ _ _
                              hguardU, hBodyS]
                            exact ihEval
                        · have htlF : top.ult
                              (BitVec.ofNat 64 len) = false :=
                            Bool.eq_false_of_ne_true htl
                          simp only [htlF, ↓reduceIte] at hrow
                          by_cases hmaxC :
                              len ≤ stdVecMaxDiffBV.toNat - 1
                          · simp only [hmaxC, ↓reduceIte] at hrow
                            -- Discovery: the forward pushes and recurses;
                            -- the evaluator marks, pushes, advances all
                            -- three cursors, and recurses.
                            cases hpush : stdVecPushBackFwd b len cap
                                (BitVec.ofNat 32 u.toNat) with
                            | error e =>
                              simp only [hpush, vecGrow_bind_err] at hrow
                              cases hrow
                            | ok pv =>
                              simp only [hpush, vecGrow_bind_ok] at hrow
                              cases hown : vecGrowOwned pv with
                              | error e =>
                                simp only [hown, vecGrow_bind_err] at hrow
                                cases hrow
                              | ok pt =>
                                simp only [hown, vecGrow_bind_ok] at hrow
                                -- Push adequacy from the absolute bound:
                                -- `len ≤ L0 + ones ≤ L0 + V` and `hP`.
                                have hadq : len + 4 ≤ F := by
                                  have hle : ones visL ≤ visL.length :=
                                    ones_le_length visL
                                  omega
                                -- The push sequence (growth leg):
                                -- factored into `dfsGrowPushGrow_ok`.
                                obtain ⟨ρC, b2, l2, c2, hPush,
                                    hmC, hvisC, hstC, hnC, hvC,
                                    htopC, hcountC, huC, hfr, hlen2,
                                    hbuflen2, h64_2, hcap2, hlen1,
                                    e1, e2, e3⟩ :=
                                  dfsGrowPushGrow_ok F b len cap top
                                    count u ρV
                                    ⟨visL.set u.toNat 1, false⟩
                                    visL.length visL.length
                                    ⟨mL, false⟩ mL.length mL.length
                                    n v pv pt hvisV hmV hnV hvV hstV
                                    htopV hcountV huV2 hlive hlen
                                    hbuflen hlen64 hcap64 htlF hmaxC
                                    hadq hpush hown
                                -- (composer call now in lemma)
                                -- The `u` advance (helper).
                                obtain ⟨ρU, hupU⟩ :=
                                  envUpdate_some_of_lookup ρC "u"
                                    (.u64 u) (.u64 (u + 1)) huC
                                obtain ⟨huA, huU⟩ :=
                                  evalProgUAdv F ρC u huC ρU hupU
                                have hL4 : evalProgStmt vecGrowProg F
                                    (.seq (.vgrowSet "vis" (.var "u")
                                      (.lit (.i32
                                        (BitVec.ofNat 32 1))))
                                      dfsGrowPush) ρ =
                                    .ok (ρC, .fellThrough) :=
                                  (evalProgStmt_seq_fallthrough vecGrowProg
                                    F _ _ _ _ hstepMark).trans hPush
                                have hL1ev : evalProgStmt vecGrowProg F
                                    (.if_ (.ult dfsGrowRowIdx
                                      (.vgrowLen "m"))
                                      (.if_ (.une
                                        (.vgrowAt "m" dfsGrowRowIdx)
                                        (.lit (.i32
                                          (BitVec.ofNat 32 0))))
                                        (.if_ (.ult (.var "u")
                                          (.vgrowLen "vis"))
                                          (.if_ (.ueq
                                            (.vgrowAt "vis" (.var "u"))
                                            (.lit (.i32
                                              (BitVec.ofNat 32 0))))
                                            (.seq (.vgrowSet "vis"
                                              (.var "u")
                                              (.lit (.i32
                                                (BitVec.ofNat 32 1))))
                                              dfsGrowPush)
                                            .skip)
                                          .fail)
                                        .skip)
                                      .fail) ρ =
                                    .ok (ρC, .fellThrough) :=
                                  hL1.trans hL4
                                have hBody : evalProgStmt vecGrowProg F
                                    (.seq (.if_
                                      (.ult dfsGrowRowIdx (.vgrowLen "m"))
                                      (.if_ (.une
                                        (.vgrowAt "m" dfsGrowRowIdx)
                                        (.lit (.i32
                                          (BitVec.ofNat 32 0))))
                                        (.if_ (.ult (.var "u")
                                          (.vgrowLen "vis"))
                                          (.if_ (.ueq
                                            (.vgrowAt "vis" (.var "u"))
                                            (.lit (.i32
                                              (BitVec.ofNat 32 0))))
                                            (.seq (.vgrowSet "vis"
                                              (.var "u")
                                              (.lit (.i32
                                                (BitVec.ofNat 32 1))))
                                              dfsGrowPush)
                                            .skip)
                                          .fail)
                                        .skip)
                                      .fail)
                                    (.assign "u" (.uadd (.var "u")
                                      (.lit (.u64
                                        (BitVec.ofNat 64 1)))))) ρ =
                                    .ok (ρU, .fellThrough) :=
                                  (evalProgStmt_seq_fallthrough vecGrowProg
                                    F _ _ _ _ hL1ev).trans huA
                                -- Thread the post-body lookups (all from
                                -- the lemma conclusions).
                                have hmB : envLookup ρU "m" =
                                    some (.stdVecOwned ⟨mL, false⟩
                                      mL.length mL.length) :=
                                  (envLookup_update_miss ρC "m" "u"
                                    (.u64 (u + 1)) ρU (by decide)
                                    hupU).trans hmC
                                have hnB : envLookup ρU "n" =
                                    some (.u64 n) :=
                                  (envLookup_update_miss ρC "n" "u"
                                    (.u64 (u + 1)) ρU (by decide)
                                    hupU).trans hnC
                                have hvB : envLookup ρU "v" =
                                    some (.u64 v) :=
                                  (envLookup_update_miss ρC "v" "u"
                                    (.u64 (u + 1)) ρU (by decide)
                                    hupU).trans hvC
                                have hvisU : envLookup ρU "vis" =
                                    some (.stdVecOwned
                                      ⟨visL.set u.toNat 1, false⟩
                                      visL.length visL.length) :=
                                  (envLookup_update_miss ρC "vis" "u"
                                    (.u64 (u + 1)) ρU (by decide)
                                    hupU).trans hvisC
                                have hvisB : envLookup ρU "vis" =
                                    some (.stdVecOwned
                                      ⟨visL.set u.toNat 1, false⟩
                                      (visL.set u.toNat 1).length
                                      (visL.set u.toNat 1).length) := by
                                  rw [hsetlen]
                                  exact hvisU
                                have hvislenB :
                                    (visL.set u.toNat 1).length <
                                    2 ^ 64 := by
                                  rw [hsetlen]
                                  exact hvislen
                                have hstB : envLookup ρU "st" =
                                    some (.stdVecOwned b2 l2 c2) :=
                                  (envLookup_update_miss ρC "st" "u"
                                    (.u64 (u + 1)) ρU (by decide)
                                    hupU).trans hstC
                                have htopB : envLookup ρU "top" =
                                    some (.u64 (top + 1)) :=
                                  (envLookup_update_miss ρC "top" "u"
                                    (.u64 (u + 1)) ρU (by decide)
                                    hupU).trans htopC
                                have hcountB : envLookup ρU "count" =
                                    some (.u64 (count + 1)) :=
                                  (envLookup_update_miss ρC "count" "u"
                                    (.u64 (u + 1)) ρU (by decide)
                                    hupU).trans hcountC
                                rw [← e1, ← e2, ← e3] at hrow
                                -- Measure facts for the row IH: the mark
                                -- is fresh, so `ones` and `len` advance in
                                -- lockstep; fuel drops exactly as `u` rises.
                                have hw00 : w = 0 := by simpa using hw0
                                have hvis0 : visL[u.toNat]? =
                                    some (0 : BitVec 32) := by
                                  simpa [hw00] using hgetV
                                have honesU : ones (visL.set u.toNat 1) =
                                    ones visL + 1 :=
                                  ones_set_one visL u.toNat hvis0
                                have hwrapTop : (top + 1).toNat =
                                    top.toNat + 1 := by
                                  have h1 : ((1 : BitVec 64)).toNat = 1 :=
                                    rfl
                                  have hle : ones visL ≤ visL.length :=
                                    ones_le_length visL
                                  have hmod : (top.toNat + 1) % 2 ^ 64 =
                                      top.toNat + 1 := by
                                    apply Nat.mod_eq_of_lt
                                    omega
                                  calc (top + 1).toNat
                                      = (top.toNat +
                                        (1 : BitVec 64).toNat) % 2 ^ 64 :=
                                        BitVec.toNat_add _ _
                                    _ = top.toNat + 1 := by
                                      rw [h1]; exact hmod
                                have hP' : L0 +
                                    (visL.set u.toNat 1).length + 8 +
                                    (n.toNat - (u + 1).toNat) ≤ F := by
                                  rw [hsetlen, hwrapU]
                                  omega
                                have hLV' : L0 +
                                    (visL.set u.toNat 1).length + 1 <
                                    2 ^ 64 := by
                                  rw [hsetlen]
                                  exact hLV
                                have hcnt' : l2 ≤
                                    L0 + ones (visL.set u.toNat 1) := by
                                  rw [hlen1, honesU]
                                  omega
                                have htopLe' : (top + 1).toNat ≤ l2 := by
                                  rw [hwrapTop, hlen1]
                                  omega
                                have hmono' : ones visL ≤
                                    ones (visL.set u.toNat 1) := by
                                  rw [honesU]
                                  omega
                                have hlock' : (top + 1).toNat + ones visL =
                                    top.toNat +
                                      ones (visL.set u.toNat 1) := by
                                  rw [hwrapTop, honesU]
                                  omega
                                have hNu : n.toNat - (u + 1).toNat = k := by
                                  rw [hwrapU]
                                  omega
                                -- The outer `MONO`/`LOCK` speak about the
                                -- pre-mark `visL`; the IH's speak about the
                                -- marked list. Bridge via `honesU`.
                                have hmonoStep : ones visL ≤
                                    ones (visL.set u.toNat 1) := by
                                  rw [honesU]
                                  exact Nat.le_succ _
                                obtain ⟨ρ', ihEval, ihM, ihVis, ihSt, ihN,
                                    ihV, ihTop, ihCount, ihU, ihFr, ihLe,
                                    ihBuflen, ih64, ihCap, ihCnt, ihMono,
                                    ihLock, ihTopLe⟩ :=
                                  ih F (visL.set u.toNat 1) b2 l2 c2
                                    (top + 1) (count + 1) (u + 1) ρU
                                    hmB hvisB hvislenB hstB hfr hlen2
                                    hbuflen2 h64_2 hcap2 hP' hLV' hcnt'
                                    htopLe' hnB hvB htopB
                                    hcountB huU hrow hNu
                                have hmono : ones visL ≤ ones vis' :=
                                  Nat.le_trans hmonoStep ihMono
                                have eLock : top'.toNat + (ones visL + 1) =
                                    (top.toNat + 1) + ones vis' := by
                                  have e := ihLock
                                  rw [hwrapTop, honesU] at e
                                  exact e
                                have hlock : top'.toNat + ones visL =
                                    top.toNat + ones vis' := by
                                  omega
                                simp only [dfsGrowInner, dfsGrowInnerBody] at ⊢ ihEval
                                rw [hsetlen] at ihVis
                                refine ⟨ρ', ?_, ihM, ihVis, ihSt, ihN,
                                  ihV, ihTop, ihCount, ihU, ihFr, ihLe,
                                  ihBuflen, ih64, ihCap, ihCnt, hmono,
                                  hlock, ihTopLe⟩
                                rw [evalProgStmt_while_true _ _ _ _ _
                                  hguardU, hBody]
                                exact ihEval
                          · simp only [hmaxC, ↓reduceIte] at hrow
                            cases hrow
                      · simp only [hw0] at hrow
                        -- `w ≠ 0`: already visited; skip, advance, recurse.
                        have hw0F : (w == (BitVec.ofNat 32 0)) =
                            false :=
                          Bool.eq_false_of_ne_true hw0
                        have hwEqF : evalExpr (.ueq
                            (.vgrowAt "vis" (.var "u"))
                            (.lit (.i32 (BitVec.ofNat 32 0)))) ρ =
                            .ok (.b false) := by
                          rw [hw0F] at hwEq
                          exact hwEq
                        have hskip : evalProgStmt vecGrowProg F .skip ρ =
                            .ok (ρ, .fellThrough) :=
                          evalProgStmt_skip _ _ _
                        obtain ⟨ρU, hupU⟩ := envUpdate_some_of_lookup ρ
                          "u" (.u64 u) (.u64 (u + 1)) hu
                        obtain ⟨huA, huU⟩ := evalProgUAdv F ρ u hu ρU
                          hupU
                        have hL1 : evalProgStmt vecGrowProg F
                            (.if_ (.ult dfsGrowRowIdx (.vgrowLen "m"))
                              (.if_ (.une
                                (.vgrowAt "m" dfsGrowRowIdx)
                                (.lit (.i32 (BitVec.ofNat 32 0))))
                                (.if_ (.ult (.var "u")
                                  (.vgrowLen "vis"))
                                  (.if_ (.ueq
                                    (.vgrowAt "vis" (.var "u"))
                                    (.lit (.i32
                                      (BitVec.ofNat 32 0))))
                                    (.seq (.vgrowSet "vis"
                                      (.var "u")
                                      (.lit (.i32
                                        (BitVec.ofNat 32 1))))
                                      dfsGrowPush)
                                    .skip)
                                  .fail)
                                .skip)
                              .fail) ρ =
                            evalProgStmt vecGrowProg F .skip ρ := by
                          rw [evalProgStmt_if_true _ _ _ _ _ _ hgIdx,
                            evalProgStmt_if_true _ _ _ _ _ _ hgNe,
                            evalProgStmt_if_true _ _ _ _ _ _ hgU,
                            evalProgStmt_if_false _ _ _ _ _ _ hwEqF]
                        have hL1ev : evalProgStmt vecGrowProg F
                            (.if_ (.ult dfsGrowRowIdx (.vgrowLen "m"))
                              (.if_ (.une
                                (.vgrowAt "m" dfsGrowRowIdx)
                                (.lit (.i32 (BitVec.ofNat 32 0))))
                                (.if_ (.ult (.var "u")
                                  (.vgrowLen "vis"))
                                  (.if_ (.ueq
                                    (.vgrowAt "vis" (.var "u"))
                                    (.lit (.i32
                                      (BitVec.ofNat 32 0))))
                                    (.seq (.vgrowSet "vis"
                                      (.var "u")
                                      (.lit (.i32
                                        (BitVec.ofNat 32 1))))
                                      dfsGrowPush)
                                    .skip)
                                  .fail)
                                .skip)
                              .fail) ρ =
                            .ok (ρ, .fellThrough) :=
                          hL1.trans hskip
                        have hBody : evalProgStmt vecGrowProg F
                            (.seq (.if_
                              (.ult dfsGrowRowIdx (.vgrowLen "m"))
                              (.if_ (.une
                                (.vgrowAt "m" dfsGrowRowIdx)
                                (.lit (.i32 (BitVec.ofNat 32 0))))
                                (.if_ (.ult (.var "u")
                                  (.vgrowLen "vis"))
                                  (.if_ (.ueq
                                    (.vgrowAt "vis" (.var "u"))
                                    (.lit (.i32
                                      (BitVec.ofNat 32 0))))
                                    (.seq (.vgrowSet "vis"
                                      (.var "u")
                                      (.lit (.i32
                                        (BitVec.ofNat 32 1))))
                                      dfsGrowPush)
                                    .skip)
                                  .fail)
                                .skip)
                              .fail)
                            (.assign "u" (.uadd (.var "u")
                              (.lit (.u64
                                (BitVec.ofNat 64 1)))))) ρ =
                            .ok (ρU, .fellThrough) :=
                          (evalProgStmt_seq_fallthrough vecGrowProg F _ _
                            _ _ hL1ev).trans huA
                        have hmU : envLookup ρU "m" =
                            some (.stdVecOwned ⟨mL, false⟩
                              mL.length mL.length) :=
                          (envLookup_update_miss ρ "m" "u"
                            (.u64 (u + 1)) ρU (by decide)
                            hupU).trans hm
                        have hnU : envLookup ρU "n" = some (.u64 n) :=
                          (envLookup_update_miss ρ "n" "u"
                            (.u64 (u + 1)) ρU (by decide)
                            hupU).trans hn
                        have hvU : envLookup ρU "v" = some (.u64 v) :=
                          (envLookup_update_miss ρ "v" "u"
                            (.u64 (u + 1)) ρU (by decide)
                            hupU).trans hv
                        have htopU : envLookup ρU "top" =
                            some (.u64 top) :=
                          (envLookup_update_miss ρ "top" "u"
                            (.u64 (u + 1)) ρU (by decide)
                            hupU).trans htop
                        have hcountU : envLookup ρU "count" =
                            some (.u64 count) :=
                          (envLookup_update_miss ρ "count" "u"
                            (.u64 (u + 1)) ρU (by decide)
                            hupU).trans hcount
                        have hvisU : envLookup ρU "vis" =
                            some (.stdVecOwned ⟨visL, false⟩
                              visL.length visL.length) :=
                          (envLookup_update_miss ρ "vis" "u"
                            (.u64 (u + 1)) ρU (by decide)
                            hupU).trans hvis
                        have hstU : envLookup ρU "st" =
                            some (.stdVecOwned b len cap) :=
                          (envLookup_update_miss ρ "st" "u"
                            (.u64 (u + 1)) ρU (by decide)
                            hupU).trans hst
                        have hPs : L0 + visL.length + 8 +
                            (n.toNat - (u + 1).toNat) ≤ F := by
                          rw [hwrapU]
                          omega
                        have hNus : n.toNat - (u + 1).toNat = k := by
                          rw [hwrapU]
                          omega
                        obtain ⟨ρ', ihEval, ihM, ihVis, ihSt, ihN, ihV,
                            ihTop, ihCount, ihU, ihFr, ihLe, ihBuflen,
                            ih64, ihCap, ihCnt, ihMono, ihLock,
                            ihTopLe⟩ :=
                          ih F visL b len cap top count (u + 1) ρU
                            hmU hvisU hvislen hstU hlive hlen hbuflen
                            hlen64 hcap64 hPs hLV hcnt htopLe hnU hvU
                            htopU hcountU huU hrow hNus
                        simp only [dfsGrowInner, dfsGrowInnerBody] at ⊢ ihEval
                        refine ⟨ρ', ?_, ihM, ihVis, ihSt, ihN, ihV,
                          ihTop, ihCount, ihU, ihFr, ihLe, ihBuflen,
                          ih64, ihCap, ihCnt, ihMono, ihLock, ihTopLe⟩
                        rw [evalProgStmt_while_true _ _ _ _ _ hguardU,
                          hBody]
                        exact ihEval
                    · simp only [hltV, ↓reduceIte] at hrow
                      cases hrow
                · simp only [huVlen] at hrow
                  cases hrow
              · simp only [hg0] at hrow
                -- `g == 0`: the row recurses with `u + 1`; the evaluator
                -- takes the `skip` arm, advances `u`, and recurses.
                have hg0F : (g != (BitVec.ofNat 32 0)) = false := by
                  cases h : (g != (BitVec.ofNat 32 0)) <;> simp_all
                have hgNeF : evalExpr (.une
                    (.vgrowAt "m" dfsGrowRowIdx)
                    (.lit (.i32 (BitVec.ofNat 32 0)))) ρ =
                    .ok (.b false) := by
                  rw [hg0F] at hgNe
                  exact hgNe
                have hskip : evalProgStmt vecGrowProg F .skip ρ =
                    .ok (ρ, .fellThrough) :=
                  evalProgStmt_skip _ _ _
                obtain ⟨ρU, hupU⟩ := envUpdate_some_of_lookup ρ "u"
                  (.u64 u) (.u64 (u + 1)) hu
                obtain ⟨huA, huU⟩ := evalProgUAdv F ρ u hu ρU hupU
                have hL1 : evalProgStmt vecGrowProg F
                    (.if_ (.ult dfsGrowRowIdx (.vgrowLen "m"))
                      (.if_ (.une (.vgrowAt "m" dfsGrowRowIdx)
                        (.lit (.i32 (BitVec.ofNat 32 0))))
                        (.if_ (.ult (.var "u") (.vgrowLen "vis"))
                          (.if_ (.ueq (.vgrowAt "vis" (.var "u"))
                            (.lit (.i32 (BitVec.ofNat 32 0))))
                            (.seq (.vgrowSet "vis" (.var "u")
                              (.lit (.i32 (BitVec.ofNat 32 1))))
                              dfsGrowPush)
                            .skip)
                          .fail)
                        .skip)
                      .fail) ρ =
                    evalProgStmt vecGrowProg F .skip ρ := by
                  rw [evalProgStmt_if_true _ _ _ _ _ _ hgIdx,
                    evalProgStmt_if_false _ _ _ _ _ _ hgNeF]
                have hL1ev : evalProgStmt vecGrowProg F
                    (.if_ (.ult dfsGrowRowIdx (.vgrowLen "m"))
                      (.if_ (.une (.vgrowAt "m" dfsGrowRowIdx)
                        (.lit (.i32 (BitVec.ofNat 32 0))))
                        (.if_ (.ult (.var "u") (.vgrowLen "vis"))
                          (.if_ (.ueq (.vgrowAt "vis" (.var "u"))
                            (.lit (.i32 (BitVec.ofNat 32 0))))
                            (.seq (.vgrowSet "vis" (.var "u")
                              (.lit (.i32 (BitVec.ofNat 32 1))))
                              dfsGrowPush)
                            .skip)
                          .fail)
                        .skip)
                      .fail) ρ =
                    .ok (ρ, .fellThrough) :=
                  hL1.trans hskip
                have hBody : evalProgStmt vecGrowProg F
                    (.seq (.if_ (.ult dfsGrowRowIdx (.vgrowLen "m"))
                      (.if_ (.une (.vgrowAt "m" dfsGrowRowIdx)
                        (.lit (.i32 (BitVec.ofNat 32 0))))
                        (.if_ (.ult (.var "u") (.vgrowLen "vis"))
                          (.if_ (.ueq (.vgrowAt "vis" (.var "u"))
                            (.lit (.i32 (BitVec.ofNat 32 0))))
                            (.seq (.vgrowSet "vis" (.var "u")
                              (.lit (.i32 (BitVec.ofNat 32 1))))
                              dfsGrowPush)
                            .skip)
                          .fail)
                        .skip)
                      .fail)
                    (.assign "u" (.uadd (.var "u")
                      (.lit (.u64 (BitVec.ofNat 64 1)))))) ρ =
                    .ok (ρU, .fellThrough) :=
                  (evalProgStmt_seq_fallthrough vecGrowProg F _ _ _ _
                    hL1ev).trans huA
                have hmU : envLookup ρU "m" =
                    some (.stdVecOwned ⟨mL, false⟩
                      mL.length mL.length) :=
                  (envLookup_update_miss ρ "m" "u" (.u64 (u + 1)) ρU
                    (by decide) hupU).trans hm
                have hnU : envLookup ρU "n" = some (.u64 n) :=
                  (envLookup_update_miss ρ "n" "u" (.u64 (u + 1)) ρU
                    (by decide) hupU).trans hn
                have hvU : envLookup ρU "v" = some (.u64 v) :=
                  (envLookup_update_miss ρ "v" "u" (.u64 (u + 1)) ρU
                    (by decide) hupU).trans hv
                have htopU : envLookup ρU "top" = some (.u64 top) :=
                  (envLookup_update_miss ρ "top" "u" (.u64 (u + 1)) ρU
                    (by decide) hupU).trans htop
                have hcountU : envLookup ρU "count" =
                    some (.u64 count) :=
                  (envLookup_update_miss ρ "count" "u" (.u64 (u + 1))
                    ρU (by decide) hupU).trans hcount
                have hvisU : envLookup ρU "vis" =
                    some (.stdVecOwned ⟨visL, false⟩
                      visL.length visL.length) :=
                  (envLookup_update_miss ρ "vis" "u" (.u64 (u + 1))
                    ρU (by decide) hupU).trans hvis
                have hstU : envLookup ρU "st" =
                    some (.stdVecOwned b len cap) :=
                  (envLookup_update_miss ρ "st" "u" (.u64 (u + 1)) ρU
                    (by decide) hupU).trans hst
                have hPg : L0 + visL.length + 8 +
                    (n.toNat - (u + 1).toNat) ≤ F := by
                  rw [hwrapU]
                  omega
                have hNug : n.toNat - (u + 1).toNat = k := by
                  rw [hwrapU]
                  omega
                obtain ⟨ρ', ihEval, ihM, ihVis, ihSt, ihN, ihV, ihTop,
                    ihCount, ihU, ihFr, ihLe, ihBuflen, ih64,
                    ihCap, ihCnt, ihMono, ihLock, ihTopLe⟩ :=
                  ih F visL b len cap top count (u + 1) ρU
                    hmU hvisU hvislen hstU hlive hlen hbuflen
                    hlen64 hcap64 hPg hLV hcnt htopLe hnU hvU
                    htopU hcountU huU hrow hNug
                simp only [dfsGrowInner, dfsGrowInnerBody] at ⊢ ihEval
                refine ⟨ρ', ?_, ihM, ihVis, ihSt, ihN, ihV, ihTop,
                  ihCount, ihU, ihFr, ihLe, ihBuflen, ih64, ihCap,
                  ihCnt, ihMono, ihLock, ihTopLe⟩
                rw [evalProgStmt_while_true _ _ _ _ _ hguardU, hBody]
                exact ihEval
            · simp only [hltM, ↓reduceIte] at hrow
              cases hrow
        · simp only [hidxB] at hrow
          cases hrow

/-- Row-scan error agreement: the `u` loop evaluates exactly as
    the row forward says on the error legs. Fuel induction (no measure
    needed: each taken arm strips one fuel). Besides the ok-leg lookups
    it takes the fuel premise `hP` (the discovery push needs callee
    fuel), the count invariant `hcnt` (push fuel + IH threading), and a
    maxdiff budget `hmaxL0` (threaded unchanged; it excludes the
    over-strict gate case `len ≥ maxdiff`, where the forward errors but
    a fast-path push could still succeed — executions past `2^61`
    pushes are outside the proven scope and the entry maintains the
    budget). Miss arms with contradictory case facts (`get? = none`
    against a `true` bound guard) close by `getElem?_eq_getElem`. -/
theorem dfsGrowRow_err (F : Nat) (mL visL : List (BitVec 32))
    (b : Vec32) (len cap : Nat) (n v top count u : BitVec 64) (ρ : Env)
    (hm : envLookup ρ "m" =
      some (.stdVecOwned ⟨mL, false⟩ mL.length mL.length))
    (hmen : mL.length < 2 ^ 64)
    (hvis : envLookup ρ "vis" =
      some (.stdVecOwned ⟨visL, false⟩ visL.length visL.length))
    (hvislen : visL.length < 2 ^ 64)
    (hst : envLookup ρ "st" = some (.stdVecOwned b len cap))
    (hlive : b.freed = false)
    (hlen : len ≤ b.val.length)
    (hbuflen : b.val.length < 2 ^ 64)
    (hlen64 : len < 2 ^ 64)
    (hcap64 : cap < 2 ^ 64)
    (hP : L0 + visL.length + 8 + (n.toNat - u.toNat) ≤ F)
    (hcnt : len ≤ L0 + ones visL)
    (hmaxL0 : L0 + visL.length + n.toNat ≤ stdVecMaxDiffBV.toNat - 1)
    (hn : envLookup ρ "n" = some (.u64 n))
    (hv : envLookup ρ "v" = some (.u64 v))
    (htop : envLookup ρ "top" = some (.u64 top))
    (hcount : envLookup ρ "count" = some (.u64 count))
    (hu : envLookup ρ "u" = some (.u64 u))
    (e : Panic)
    (herr : dfsGrowRowFwd F mL visL b len cap n v top count u = .error e) :
    evalProgStmt vecGrowProg F dfsGrowInner ρ = .error e := by
  -- `L0` never changes, so it stays fixed (like `mL`/`n`/`v`).
  induction F generalizing visL b len cap top count u ρ with
  | zero =>
    cases huLT : u.ult n with
    | false =>
      simp only [dfsGrowRowFwd, huLT, ↓reduceIte] at herr
      cases herr
    | true =>
      simp only [dfsGrowRowFwd, huLT, ↓reduceIte] at herr
      cases herr
      have hguardU : evalExpr (.ult (.var "u") (.var "n")) ρ =
          .ok (.b true) := by
        have h1 := evalExpr_var_hit ρ "u" (.u64 u) hu
        have h2 := evalExpr_var_hit ρ "n" (.u64 n) hn
        have h3 := evalExpr_ult_u64 _ _ _ _ _ h1 h2
        rw [huLT] at h3
        exact h3
      have hfb : evalProgStmt vecGrowProg 0 dfsGrowInner ρ =
          evalStmtFuel 0 dfsGrowInner ρ := by
        simp only [dfsGrowInner, evalProgStmt]
      rw [hfb]
      simp only [dfsGrowInner]
      exact evalStmtFuel_zero_while_enter _ _ _ hguardU
  | succ F ih =>
    cases huLT : u.ult n with
    | false =>
      simp only [dfsGrowRowFwd, huLT, ↓reduceIte] at herr
      cases herr
    | true =>
      simp only [dfsGrowRowFwd, huLT, ↓reduceIte] at herr
      -- `u + 1` does not wrap (`u < n < 2^64`).
      have huN : u.toNat < n.toNat := by
        have h := huLT
        rw [BitVec.ult_eq_decide, decide_eq_true_eq] at h
        exact h
      have hn64 : n.toNat < 2 ^ 64 := BitVec.isLt n
      have hwrapU : (u + 1).toNat = u.toNat + 1 := by
        have h1 : ((1 : BitVec 64)).toNat = 1 := rfl
        have hmod : (u.toNat + 1) % 2 ^ 64 = u.toNat + 1 := by
          apply Nat.mod_eq_of_lt
          omega
        calc (u + 1).toNat
            = (u.toNat + (1 : BitVec 64).toNat) % 2 ^ 64 :=
              BitVec.toNat_add _ _
          _ = u.toNat + 1 := by rw [h1]; exact hmod
      -- Shared guard facts: the flat index and its matrix bound.
      have hguardU : evalExpr (.ult (.var "u") (.var "n")) ρ =
          .ok (.b true) := by
        have h1 := evalExpr_var_hit ρ "u" (.u64 u) hu
        have h2 := evalExpr_var_hit ρ "n" (.u64 n) hn
        have h3 := evalExpr_ult_u64 _ _ _ _ _ h1 h2
        rw [huLT] at h3
        exact h3
      have hvn : evalExpr (.umul (.var "v") (.var "n")) ρ =
          .ok (.u64 (v * n)) :=
        evalExpr_umul_u64 _ _ _ _ _
          (evalExpr_var_hit ρ "v" (.u64 v) hv)
          (evalExpr_var_hit ρ "n" (.u64 n) hn)
      have huV : evalExpr (.var "u") ρ = .ok (.u64 u) :=
        evalExpr_var_hit ρ "u" (.u64 u) hu
      have hidx : evalExpr dfsGrowRowIdx ρ = .ok (.u64 (v * n + u)) := by
        simp only [dfsGrowRowIdx]
        exact evalExpr_uadd_u64 _ _ _ _ _ hvn huV
      have hmLen : evalExpr (.vgrowLen "m") ρ =
          .ok (.u64 (BitVec.ofNat 64 mL.length)) :=
        evalExpr_vgrowLen_some "m" ρ ⟨mL, false⟩ mL.length mL.length hm
      have hgIdx : evalExpr (.ult dfsGrowRowIdx (.vgrowLen "m")) ρ =
          .ok (.b ((v * n + u).ult (BitVec.ofNat 64 mL.length))) :=
        evalExpr_ult_u64 _ _ _ _ _ hidx hmLen
      -- Matrix-bound miss: the forward errors before any state change,
      -- so only the guard value matters.
      have hml : (BitVec.ofNat 64 mL.length).toNat = mL.length := by
        rw [BitVec.toNat_ofNat]
        exact Nat.mod_eq_of_lt hmen
      have hltM_of : (v * n + u).ult (BitVec.ofNat 64 mL.length) = true →
          (v * n + u).toNat < mL.length := by
        intro h
        rw [BitVec.ult_eq_decide, decide_eq_true_eq, hml] at h
        exact h
      by_cases hidxB :
          (v * n + u).ult (BitVec.ofNat 64 mL.length) = true
      · rw [hidxB] at hgIdx
        simp only [hidxB] at herr
        cases hgetM : mL[(v * n + u).toNat]? with
        | none =>
          simp only [hgetM, ↓reduceIte] at herr
          -- Vacuous: the `ult` guard gives `idx < length`, so `get?`
          -- must hit.
          have hsome :=
            List.getElem?_eq_getElem (hltM_of hidxB)
          rw [hsome] at hgetM
          cases hgetM
        | some g =>
          simp only [hgetM, ↓reduceIte] at herr
          by_cases hltM : (v * n + u).toNat < mL.length
          · simp only [hltM, ↓reduceIte] at herr
            have hmv : evalExpr (.vgrowAt "m" dfsGrowRowIdx) ρ =
                .ok (.i32 g) :=
              evalExpr_vgrowAt_some "m" _ ρ ⟨mL, false⟩ mL.length
                mL.length (v * n + u) g hm hidx rfl hgetM hltM
            have hgNe : evalExpr (.une (.vgrowAt "m" dfsGrowRowIdx)
                (.lit (.i32 (BitVec.ofNat 32 0)))) ρ =
                .ok (.b (g != (BitVec.ofNat 32 0))) :=
              evalExpr_une_i32 (.vgrowAt "m" dfsGrowRowIdx)
                (.lit (.i32 (BitVec.ofNat 32 0))) ρ g
                (BitVec.ofNat 32 0) hmv (evalExpr_lit _ _)
            by_cases hg0 : (g != (BitVec.ofNat 32 0)) = true
            · rw [hg0] at hgNe
              simp only [hg0] at herr
              have hvisLenE : evalExpr (.vgrowLen "vis") ρ =
                  .ok (.u64 (BitVec.ofNat 64 visL.length)) :=
                evalExpr_vgrowLen_some "vis" ρ ⟨visL, false⟩
                  visL.length visL.length hvis
              have hgU : evalExpr (.ult (.var "u")
                  (.vgrowLen "vis")) ρ =
                  .ok (.b (u.ult (BitVec.ofNat 64 visL.length))) :=
                evalExpr_ult_u64 _ _ _ _ _ huV hvisLenE
              have hvl : (BitVec.ofNat 64 visL.length).toNat =
                  visL.length := by
                rw [BitVec.toNat_ofNat]
                exact Nat.mod_eq_of_lt hvislen
              have hltV_of : u.ult (BitVec.ofNat 64 visL.length) = true →
                  u.toNat < visL.length := by
                intro h
                rw [BitVec.ult_eq_decide, decide_eq_true_eq, hvl] at h
                exact h
              by_cases huVlen :
                  u.ult (BitVec.ofNat 64 visL.length) = true
              · rw [huVlen] at hgU
                simp only [huVlen] at herr
                cases hgetV : visL[u.toNat]? with
                | none =>
                  simp only [hgetV, ↓reduceIte] at herr
                  -- Vacuous: the `ult` guard gives `u < length`, so
                  -- `get?` must hit.
                  have hsome :=
                    List.getElem?_eq_getElem (hltV_of huVlen)
                  rw [hsome] at hgetV
                  cases hgetV
                | some w =>
                  simp only [hgetV, ↓reduceIte] at herr
                  by_cases hltV : u.toNat < visL.length
                  · simp only [hltV, ↓reduceIte] at herr
                    have hwv : evalExpr (.vgrowAt "vis" (.var "u")) ρ =
                        .ok (.i32 w) :=
                      evalExpr_vgrowAt_some "vis" _ ρ ⟨visL, false⟩
                        visL.length visL.length u w hvis huV rfl
                        hgetV hltV
                    have hwEq : evalExpr (.ueq
                        (.vgrowAt "vis" (.var "u"))
                        (.lit (.i32 (BitVec.ofNat 32 0)))) ρ =
                        .ok (.b (w == (BitVec.ofNat 32 0))) :=
                      evalExpr_ueq_i32 (.vgrowAt "vis" (.var "u"))
                        (.lit (.i32 (BitVec.ofNat 32 0))) ρ w
                        (BitVec.ofNat 32 0) hwv (evalExpr_lit _ _)
                    by_cases hw0 :
                        (w == (BitVec.ofNat 32 0)) = true
                    · rw [hw0] at hwEq
                      simp only [hw0] at herr
                      by_cases hmaxC :
                          len ≤ stdVecMaxDiffBV.toNat - 1
                      · simp only [hmaxC, ↓reduceIte] at herr
                        -- Push adequacy from the absolute bound (as in
                        -- the ok leg): `len ≤ L0 + ones ≤ L0 + V` with
                        -- `hP`. The `hmaxC` case fact feeds the callee
                        -- agreement.
                        have hadq : len + 4 ≤ F := by
                          have hle : ones visL ≤ visL.length :=
                            ones_le_length visL
                          omega
                        obtain ⟨Fp, hFeq, hFp⟩ :=
                          fuel_step_down (len + 3) hadq
                        have hmaxC' :
                            len ≤ stdVecMaxDiffBV.toNat := by omega
                        have hcall := evalProgFunc_stdVecPushBack
                          Fp b len cap
                          (BitVec.ofNat 32 u.toNat) hlive hmaxC'
                          hlen hbuflen hcap64 hFp
                        -- The visited mark.
                        have hset : vecSet ⟨visL, false⟩
                            u.toNat 1 =
                            .ok ⟨visL.set u.toNat 1,
                              false⟩ := by
                          unfold vecSet
                          simp [hltV]
                        obtain ⟨ρV, huv⟩ :=
                          envUpdate_some_of_lookup ρ "vis"
                            (.stdVecOwned ⟨visL, false⟩
                              visL.length visL.length)
                            (.stdVecOwned
                              ⟨visL.set u.toNat 1, false⟩
                              visL.length visL.length) hvis
                        have hmark := evalStmtFuel_vgrowSet F
                          "vis" (.var "u")
                          (.lit (.i32 (BitVec.ofNat 32 1))) ρ u
                          (BitVec.ofNat 32 1) ⟨visL, false⟩
                          ⟨visL.set u.toNat 1, false⟩
                          visL.length visL.length ρV
                          (evalExpr_var_hit ρ "u" (.u64 u) hu)
                          rfl hvis hset huv
                        have hfbMark : evalProgStmt vecGrowProg F
                            (.vgrowSet "vis" (.var "u")
                              (.lit (.i32
                                (BitVec.ofNat 32 1)))) ρ =
                            evalStmtFuel F
                              (.vgrowSet "vis" (.var "u")
                                (.lit (.i32
                                  (BitVec.ofNat 32 1)))) ρ := by
                          simp only [evalProgStmt]
                        have hstepMark : evalProgStmt vecGrowProg F
                            (.vgrowSet "vis" (.var "u")
                              (.lit (.i32
                                (BitVec.ofNat 32 1)))) ρ =
                            .ok (ρV, .fellThrough) := by
                          rw [hfbMark]
                          exact hmark
                        have hsetlen : (visL.set u.toNat 1).length =
                            visL.length := by
                          simp
                        have huV2 : envLookup ρV "u" =
                            some (.u64 u) :=
                          (envLookup_update_miss ρ "u" "vis"
                            (.stdVecOwned
                              ⟨visL.set u.toNat 1, false⟩
                              visL.length visL.length) ρV
                            (by decide) huv).trans hu
                        have hstV : envLookup ρV "st" =
                            some (.stdVecOwned b len cap) :=
                          (envLookup_update_miss ρ "st" "vis"
                            (.stdVecOwned
                              ⟨visL.set u.toNat 1, false⟩
                              visL.length visL.length) ρV
                            (by decide) huv).trans hst
                        have hmV : envLookup ρV "m" =
                            some (.stdVecOwned ⟨mL, false⟩
                              mL.length mL.length) :=
                          (envLookup_update_miss ρ "m" "vis"
                            (.stdVecOwned
                              ⟨visL.set u.toNat 1, false⟩
                              visL.length visL.length) ρV
                            (by decide) huv).trans hm
                        have hnV : envLookup ρV "n" =
                            some (.u64 n) :=
                          (envLookup_update_miss ρ "n" "vis"
                            (.stdVecOwned
                              ⟨visL.set u.toNat 1, false⟩
                              visL.length visL.length) ρV
                            (by decide) huv).trans hn
                        have hvV : envLookup ρV "v" =
                            some (.u64 v) :=
                          (envLookup_update_miss ρ "v" "vis"
                            (.stdVecOwned
                              ⟨visL.set u.toNat 1, false⟩
                              visL.length visL.length) ρV
                            (by decide) huv).trans hv
                        have htopV : envLookup ρV "top" =
                            some (.u64 top) :=
                          (envLookup_update_miss ρ "top" "vis"
                            (.stdVecOwned
                              ⟨visL.set u.toNat 1, false⟩
                              visL.length visL.length) ρV
                            (by decide) huv).trans htop
                        have hcountV : envLookup ρV "count" =
                            some (.u64 count) :=
                          (envLookup_update_miss ρ "count" "vis"
                            (.stdVecOwned
                              ⟨visL.set u.toNat 1, false⟩
                              visL.length visL.length) ρV
                            (by decide) huv).trans hcount
                        have hvisV : envLookup ρV "vis" =
                            some (.stdVecOwned
                              ⟨visL.set u.toNat 1, false⟩
                              visL.length visL.length) :=
                          envLookup_update_hit ρ "vis" _ ρV huv
                        -- The `x` let.
                        have hxE : evalExpr
                            (.i32ofU64 (.var "u")) ρV =
                            .ok (.i32
                              (BitVec.ofNat 32 u.toNat)) :=
                          evalExpr_i32ofU64_ok _ _ _
                            (evalExpr_var_hit ρV "u" (.u64 u)
                              huV2)
                        have hletX : evalStmtFuel F
                            (.let_ "x" (.i 32)
                              (.i32ofU64 (.var "u"))) ρV =
                            .ok (envExtend ρV "x"
                              (.i32 (BitVec.ofNat 32 u.toNat)),
                              .fellThrough) :=
                          evalStmtFuel_let_ F "x" (.i 32)
                            (.i32ofU64 (.var "u")) ρV _ hxE
                        have hstepX : evalProgStmt vecGrowProg F
                            (.let_ "x" (.i 32)
                              (.i32ofU64 (.var "u"))) ρV =
                            .ok (envExtend ρV "x"
                              (.i32 (BitVec.ofNat 32 u.toNat)),
                              .fellThrough) := by
                          rw [evalProgStmt_let_fb]
                          exact hletX
                        have hstVx : envLookup (envExtend ρV "x"
                            (.i32 (BitVec.ofNat 32 u.toNat)))
                            "st" =
                            some (.stdVecOwned b len cap) :=
                          envLookup_extend_miss _ _ _ _ _ hstV
                            (by decide)
                        have hL1 : evalProgStmt vecGrowProg F
                            (.if_ (.ult dfsGrowRowIdx
                              (.vgrowLen "m"))
                              (.if_ (.une
                                (.vgrowAt "m" dfsGrowRowIdx)
                                (.lit (.i32
                                  (BitVec.ofNat 32 0))))
                                (.if_ (.ult (.var "u")
                                  (.vgrowLen "vis"))
                                  (.if_ (.ueq
                                    (.vgrowAt "vis" (.var "u"))
                                    (.lit (.i32
                                      (BitVec.ofNat 32 0))))
                                    (.seq (.vgrowSet "vis"
                                      (.var "u")
                                      (.lit (.i32
                                        (BitVec.ofNat 32 1))))
                                      dfsGrowPush)
                                    .skip)
                                  .fail)
                                .skip)
                              .fail) ρ =
                            evalProgStmt vecGrowProg F
                              (.seq (.vgrowSet "vis" (.var "u")
                                (.lit (.i32
                                  (BitVec.ofNat 32 1))))
                                dfsGrowPush) ρ := by
                          rw [evalProgStmt_if_true _ _ _ _ _ _
                            hgIdx,
                            evalProgStmt_if_true _ _ _ _ _ _
                            hgNe,
                            evalProgStmt_if_true _ _ _ _ _ _
                            hgU,
                            evalProgStmt_if_true _ _ _ _ _ _
                            hwEq]

                        have hxVx : envLookup (envExtend ρV "x"
                            (.i32 (BitVec.ofNat 32 u.toNat)))
                            "x" =
                            some (.i32
                              (BitVec.ofNat 32 u.toNat)) :=
                          envLookup_extend_hit _ _ _
                        have htopVx : envLookup (envExtend ρV "x"
                            (.i32 (BitVec.ofNat 32 u.toNat)))
                            "top" =
                            some (.u64 top) :=
                          envLookup_extend_miss _ _ _ _ _ htopV
                            (by decide)
                        have hstLenX : evalExpr (.vgrowLen "st")
                            (envExtend ρV "x"
                              (.i32
                                (BitVec.ofNat 32 u.toNat))) =
                            .ok (.u64
                              (BitVec.ofNat 64 len)) :=
                          evalExpr_vgrowLen_some "st" _ b len cap
                            hstVx
                        have hguardP : evalExpr
                            (.ult (.var "top")
                              (.vgrowLen "st"))
                            (envExtend ρV "x"
                              (.i32
                                (BitVec.ofNat 32 u.toNat))) =
                            .ok (.b (top.ult
                              (BitVec.ofNat 64 len))) :=
                          evalExpr_ult_u64 _ _ _ _ _
                            (evalExpr_var_hit _
                              "top" (.u64 top) htopVx)
                            hstLenX
                        by_cases htl :
                            top.ult (BitVec.ofNat 64 len) = true
                        · rw [htl] at hguardP
                          simp only [htl, ↓reduceIte] at herr
                          have hw00 : w = 0 := by simpa using hw0
                          have hvis0 : visL[u.toNat]? =
                              some (0 : BitVec 32) := by
                            simpa [hw00] using hgetV
                          have honesU : ones (visL.set u.toNat 1) =
                              ones visL + 1 :=
                            ones_set_one visL u.toNat hvis0
                          have htlN : top.toNat < len := by
                            have h := htl
                            rw [BitVec.ult_eq_decide,
                              decide_eq_true_eq] at h
                            have ho : (BitVec.ofNat 64 len).toNat =
                                len := by
                              rw [BitVec.toNat_ofNat]
                              exact Nat.mod_eq_of_lt hlen64
                            omega
                          cases hsetB : vecSet b top.toNat
                              (BitVec.ofNat 32 u.toNat) with
                          | error e1 =>
                            simp only [hsetB] at herr
                            cases herr
                            have hstepSetE : evalStmtFuel F
                                (.vgrowSet "st" (.var "top")
                                  (.var "x"))
                                (envExtend ρV "x"
                                  (.i32
                                    (BitVec.ofNat 32 u.toNat))) =
                                .error e :=
                              evalStmtFuel_vgrowSet_err F "st"
                                (.var "top") (.var "x")
                                (envExtend ρV "x"
                                  (.i32
                                    (BitVec.ofNat 32 u.toNat)))
                                top
                                (BitVec.ofNat 32 u.toNat) b len
                                cap e
                                (evalExpr_var_hit _
                                  "top" (.u64 top) htopVx)
                                (evalExpr_var_hit _
                                  "x"
                                  (.i32
                                    (BitVec.ofNat 32 u.toNat))
                                  hxVx)
                                hstVx hsetB
                            have hifS : evalProgStmt vecGrowProg F
                                (.if_ (.ult (.var "top")
                                  (.vgrowLen "st"))
                                  (.vgrowSet "st" (.var "top")
                                    (.var "x"))
                                  (.callProg "st"
                                    stdVecPushBackName ["st", "x"]))
                                (envExtend ρV "x"
                                  (.i32
                                    (BitVec.ofNat 32 u.toNat))) =
                                evalProgStmt vecGrowProg F
                                  (.vgrowSet "st" (.var "top")
                                    (.var "x"))
                                  (envExtend ρV "x"
                                    (.i32
                                      (BitVec.ofNat 32 u.toNat))) := by
                              rw [evalProgStmt_if_true _ _ _ _ _ _
                                hguardP]
                            have hfbS : evalProgStmt vecGrowProg F
                                (.vgrowSet "st" (.var "top")
                                  (.var "x"))
                                (envExtend ρV "x"
                                  (.i32
                                    (BitVec.ofNat 32 u.toNat))) =
                                evalStmtFuel F
                                  (.vgrowSet "st" (.var "top")
                                    (.var "x"))
                                  (envExtend ρV "x"
                                    (.i32
                                      (BitVec.ofNat 32 u.toNat))) := by
                              simp only [evalProgStmt]
                            have hPushTailS : evalProgStmt vecGrowProg F
                                dfsGrowPush ρV = .error e := by
                              simp only [dfsGrowPush]
                              exact (evalProgStmt_seq_fallthrough
                                vecGrowProg F _ _ _ _
                                hstepX).trans
                                (evalProgStmt_seq_err _ _ _ _ _ _
                                  ((hifS.trans hfbS).trans hstepSetE))
                            have hL4S : evalProgStmt vecGrowProg F
                                (.seq (.vgrowSet "vis" (.var "u")
                                  (.lit (.i32
                                    (BitVec.ofNat 32 1))))
                                  dfsGrowPush) ρ = .error e :=
                              (evalProgStmt_seq_fallthrough vecGrowProg
                                F _ _ _ _ hstepMark).trans hPushTailS
                            have hBodyS : evalProgStmt vecGrowProg F
                                dfsGrowInnerBody ρ = .error e := by
                              simp only [dfsGrowInnerBody]
                              exact evalProgStmt_seq_err _ _ _ _ _ _
                                (hL1.trans hL4S)
                            have hevS : evalProgStmt vecGrowProg (F + 1)
                                dfsGrowInner ρ = .error e := by
                              simp only [dfsGrowInner]
                              rw [evalProgStmt_while_true _ _ _ _ _
                                hguardU, hBodyS]
                            exact hevS
                          | ok b2 =>
                            simp only [hsetB] at herr
                            -- The push sequence (slot leg): factored
                            -- into `dfsGrowPushSlot_ok`.
                            obtain ⟨ρC, hPushS, hmC, hvisC, hstC,
                                hnC, hvC, htopC, hcountC, huC,
                                hlen2, hbuflen2, hfrB⟩ :=
                              dfsGrowPushSlot_ok F b b2 len cap top
                                count u ρV
                                ⟨visL.set u.toNat 1, false⟩
                                visL.length visL.length
                                ⟨mL, false⟩ mL.length mL.length n v
                                hvisV hmV hnV hvV hstV htopV hcountV
                                huV2 hlen hbuflen hlen64 htl hsetB
                            -- (push tail now in lemma; u advance below
                            -- threads the lemma post-state)
                            obtain ⟨ρU, hupU⟩ :=
                              envUpdate_some_of_lookup ρC "u"
                                (.u64 u) (.u64 (u + 1)) huC
                            obtain ⟨huA, huU⟩ :=
                              evalProgUAdv F ρC u huC ρU hupU
                            have hmB : envLookup ρU "m" =
                                some (.stdVecOwned ⟨mL, false⟩
                                  mL.length mL.length) :=
                              (envLookup_update_miss ρC "m" "u"
                                (.u64 (u + 1)) ρU
                                (by decide) hupU).trans hmC
                            have hnB : envLookup ρU "n" =
                                some (.u64 n) :=
                              (envLookup_update_miss ρC "n" "u"
                                (.u64 (u + 1)) ρU
                                (by decide) hupU).trans hnC
                            have hvB : envLookup ρU "v" =
                                some (.u64 v) :=
                              (envLookup_update_miss ρC "v" "u"
                                (.u64 (u + 1)) ρU
                                (by decide) hupU).trans hvC
                            have htopB : envLookup ρU "top" =
                                some (.u64 (top + 1)) :=
                              (envLookup_update_miss ρC "top" "u"
                                (.u64 (u + 1)) ρU
                                (by decide) hupU).trans htopC
                            have hcountB : envLookup ρU "count" =
                                some (.u64 (count + 1)) :=
                              (envLookup_update_miss ρC "count" "u"
                                (.u64 (u + 1)) ρU
                                (by decide) hupU).trans hcountC
                            have hvisB : envLookup ρU "vis" =
                                some (.stdVecOwned
                                  ⟨visL.set u.toNat 1, false⟩
                                  (visL.set u.toNat 1).length
                                  (visL.set u.toNat 1).length) := by
                              rw [hsetlen]
                              exact (envLookup_update_miss ρC "vis"
                                "u" (.u64 (u + 1)) ρU
                                (by decide) hupU).trans hvisC
                            have hvislenB :
                                (visL.set u.toNat 1).length <
                                2 ^ 64 := by
                              rw [hsetlen]
                              exact hvislen
                            have hstB : envLookup ρU "st" =
                                some (.stdVecOwned b2 len cap) :=
                              (envLookup_update_miss ρC "st" "u"
                                (.u64 (u + 1)) ρU
                                (by decide) hupU).trans hstC
                            have hL4S : evalProgStmt vecGrowProg F
                                (.seq (.vgrowSet "vis" (.var "u")
                                  (.lit (.i32
                                    (BitVec.ofNat 32 1))))
                                  dfsGrowPush) ρ =
                                .ok (ρC, .fellThrough) :=
                              (evalProgStmt_seq_fallthrough vecGrowProg
                                F _ _ _ _ hstepMark).trans hPushS
                            have hL1evS : evalProgStmt vecGrowProg F
                                (.if_ (.ult dfsGrowRowIdx
                                  (.vgrowLen "m"))
                                  (.if_ (.une
                                    (.vgrowAt "m" dfsGrowRowIdx)
                                    (.lit (.i32
                                      (BitVec.ofNat 32 0))))
                                    (.if_ (.ult (.var "u")
                                      (.vgrowLen "vis"))
                                      (.if_ (.ueq
                                        (.vgrowAt "vis" (.var "u"))
                                        (.lit (.i32
                                          (BitVec.ofNat 32 0))))
                                        (.seq (.vgrowSet "vis"
                                          (.var "u")
                                          (.lit (.i32
                                            (BitVec.ofNat 32 1))))
                                          dfsGrowPush)
                                        .skip)
                                      .fail)
                                    .skip)
                                  .fail) ρ =
                                .ok (ρC, .fellThrough) :=
                              hL1.trans hL4S
                            have hBodyS : evalProgStmt vecGrowProg F
                                dfsGrowInnerBody ρ =
                                .ok (ρU, .fellThrough) := by
                              simp only [dfsGrowInnerBody]
                              exact (evalProgStmt_seq_fallthrough
                                vecGrowProg F _ _ _ _ hL1evS).trans huA
                            have hPgB : L0 +
                                (visL.set u.toNat 1).length + 8 +
                                (n.toNat - (u + 1).toNat) ≤ F := by
                              rw [hsetlen, hwrapU]
                              omega
                            have hcntB : len ≤
                                L0 + ones (visL.set u.toNat 1) := by
                              rw [honesU]
                              omega
                            have hmaxB : L0 +
                                (visL.set u.toNat 1).length +
                                n.toNat ≤
                                stdVecMaxDiffBV.toNat - 1 := by
                              rw [hsetlen]
                              exact hmaxL0
                            have hev : evalProgStmt vecGrowProg F
                                dfsGrowInner ρU = .error e :=
                              ih (visL.set u.toNat 1) b2 len cap
                                (top + 1) (count + 1) (u + 1) ρU
                                hmB hvisB hvislenB hstB hfrB hlen2
                                hbuflen2 hlen64 hcap64 hPgB hcntB
                                hmaxB hnB hvB htopB hcountB huU herr
                            simp only [dfsGrowInner]
                            rw [evalProgStmt_while_true _ _ _ _ _
                              hguardU, hBodyS]
                            exact hev
                        · have htlF : top.ult
                              (BitVec.ofNat 64 len) = false :=
                            Bool.eq_false_of_ne_true htl
                          rw [htlF] at hguardP
                          simp only [htlF, ↓reduceIte] at herr
                          have hargs : lookupArgs (envExtend ρV "x"
                              (.i32 (BitVec.ofNat 32 u.toNat)))
                              ["st", "x"] =
                              some [.stdVecOwned b len cap,
                                .i32
                                  (BitVec.ofNat 32 u.toNat)] :=
                            lookupArgs_cons_hit _ _ _ _ _ hstVx
                              (lookupArgs_cons_hit _ _ _ [] []
                                hxVx (lookupArgs_nil _))
                          cases hpush : stdVecPushBackFwd b len cap
                              (BitVec.ofNat 32 u.toNat)
                          case error e1 =>
                            simp only [hpush, vecGrow_bind_err] at herr
                            cases herr
                            rw [hpush] at hcall
                            -- The failing `push_back` call.
                            have hstepPushE : evalProgStmt vecGrowProg
                                (Fp + 1)
                                (.callProg "st" stdVecPushBackName
                                  ["st", "x"])
                                (envExtend ρV "x"
                                  (.i32 (BitVec.ofNat 32 u.toNat))) =
                                .error e :=
                              evalProgStmt_callProg_err vecGrowProg Fp
                                "st" stdVecPushBackName ["st", "x"]
                                (envExtend ρV "x"
                                  (.i32 (BitVec.ofNat 32 u.toNat)))
                                [.stdVecOwned b len cap,
                                  .i32 (BitVec.ofNat 32 u.toNat)]
                                stdVecPushBackFunc e hargs
                                findFunc_stdVecPushBack hcall
                            rw [← hFeq] at hstepPushE
                            have hifG : evalProgStmt vecGrowProg F
                                (.if_ (.ult (.var "top")
                                  (.vgrowLen "st"))
                                  (.vgrowSet "st" (.var "top")
                                    (.var "x"))
                                  (.callProg "st"
                                    stdVecPushBackName ["st", "x"]))
                                (envExtend ρV "x"
                                  (.i32
                                    (BitVec.ofNat 32 u.toNat))) =
                                evalProgStmt vecGrowProg F
                                  (.callProg "st"
                                    stdVecPushBackName ["st", "x"])
                                  (envExtend ρV "x"
                                    (.i32
                                      (BitVec.ofNat 32
                                        u.toNat))) := by
                              rw [evalProgStmt_if_false _ _ _ _ _ _
                                hguardP]
                            have hPushTail : evalProgStmt vecGrowProg F
                                dfsGrowPush ρV = .error e := by
                              simp only [dfsGrowPush]
                              exact (evalProgStmt_seq_fallthrough
                                vecGrowProg F _ _ _ _
                                hstepX).trans
                                (evalProgStmt_seq_err _ _ _ _ _ _
                                  (hifG.trans hstepPushE))
                            have hL4 : evalProgStmt vecGrowProg F
                                (.seq (.vgrowSet "vis" (.var "u")
                                  (.lit (.i32
                                    (BitVec.ofNat 32 1))))
                                  dfsGrowPush) ρ = .error e :=
                              (evalProgStmt_seq_fallthrough vecGrowProg
                                F _ _ _ _ hstepMark).trans hPushTail
                            have hBody : evalProgStmt vecGrowProg F
                                dfsGrowInnerBody ρ = .error e := by
                              simp only [dfsGrowInnerBody]
                              exact evalProgStmt_seq_err _ _ _ _ _ _
                                (hL1.trans hL4)
                            have hev : evalProgStmt vecGrowProg (F + 1)
                                dfsGrowInner ρ = .error e := by
                              simp only [dfsGrowInner]
                              rw [evalProgStmt_while_true _ _ _ _ _
                                hguardU, hBody]
                            exact hev
                          case ok pv =>
                            simp only [hpush, vecGrow_bind_ok] at herr
                            cases hown : vecGrowOwned pv with
                          | error e2 =>
                            simp only [hown, vecGrow_bind_err] at herr
                            -- Vacuous: a successful push always yields
                            -- an owned triple, so `vecGrowOwned` on it
                            -- cannot fail.
                            have hshape := stdVecPushBackFwd_ok b len
                              cap (BitVec.ofNat 32 u.toNat) pv hlive
                              hlen hbuflen hlen64 hcap64 hmaxC hpush
                            obtain ⟨b2, l2, c2, hv2, -, -, -, -, -,
                                -⟩ := hshape
                            rw [hv2] at hown
                            simp only [vecGrowOwned] at hown
                            cases hown
                          | ok pt =>
                            simp only [hown, vecGrow_bind_ok] at herr
                            -- Push adequacy from the absolute bound.
                            have hadq : len + 4 ≤ F := by
                              have hle : ones visL ≤ visL.length :=
                                ones_le_length visL
                              omega
                            -- The push sequence (growth leg): factored.
                            obtain ⟨ρC, b2, l2, c2, hPush,
                                hmC, hvisC, hstC, hnC, hvC,
                                htopC, hcountC, huC, hfr, hlen2,
                                hbuflen2, h64_2, hcap2, hlen1,
                                e1, e2, e3⟩ :=
                              dfsGrowPushGrow_ok F b len cap top
                                count u ρV
                                ⟨visL.set u.toNat 1, false⟩
                                visL.length visL.length
                                ⟨mL, false⟩ mL.length mL.length
                                n v pv pt hvisV hmV hnV hvV hstV
                                htopV hcountV huV2 hlive hlen
                                hbuflen hlen64 hcap64 htlF hmaxC
                                hadq hpush hown
                            obtain ⟨ρU, hupU⟩ :=
                              envUpdate_some_of_lookup ρC "u"
                                (.u64 u) (.u64 (u + 1)) huC
                            obtain ⟨huA, huU⟩ :=
                              evalProgUAdv F ρC u huC ρU hupU
                            have hL4 : evalProgStmt vecGrowProg F
                                (.seq (.vgrowSet "vis" (.var "u")
                                  (.lit (.i32
                                    (BitVec.ofNat 32 1))))
                                  dfsGrowPush) ρ =
                                .ok (ρC, .fellThrough) :=
                              (evalProgStmt_seq_fallthrough vecGrowProg
                                F _ _ _ _ hstepMark).trans hPush
                            have hL1 : evalProgStmt vecGrowProg F
                                (.if_ (.ult dfsGrowRowIdx
                                  (.vgrowLen "m"))
                                  (.if_ (.une
                                    (.vgrowAt "m" dfsGrowRowIdx)
                                    (.lit (.i32
                                      (BitVec.ofNat 32 0))))
                                    (.if_ (.ult (.var "u")
                                      (.vgrowLen "vis"))
                                      (.if_ (.ueq
                                        (.vgrowAt "vis" (.var "u"))
                                        (.lit (.i32
                                          (BitVec.ofNat 32 0))))
                                        (.seq (.vgrowSet "vis"
                                          (.var "u")
                                          (.lit (.i32
                                            (BitVec.ofNat 32 1))))
                                          dfsGrowPush)
                                        .skip)
                                      .fail)
                                    .skip)
                                  .fail) ρ =
                                evalProgStmt vecGrowProg F
                                  (.seq (.vgrowSet "vis" (.var "u")
                                    (.lit (.i32
                                      (BitVec.ofNat 32 1))))
                                    dfsGrowPush) ρ := by
                              rw [evalProgStmt_if_true _ _ _ _ _ _
                                hgIdx,
                                evalProgStmt_if_true _ _ _ _ _ _
                                hgNe,
                                evalProgStmt_if_true _ _ _ _ _ _
                                hgU,
                                evalProgStmt_if_true _ _ _ _ _ _
                                hwEq]
                            have hL1ev : evalProgStmt vecGrowProg F
                                (.if_ (.ult dfsGrowRowIdx
                                  (.vgrowLen "m"))
                                  (.if_ (.une
                                    (.vgrowAt "m" dfsGrowRowIdx)
                                    (.lit (.i32
                                      (BitVec.ofNat 32 0))))
                                    (.if_ (.ult (.var "u")
                                      (.vgrowLen "vis"))
                                      (.if_ (.ueq
                                        (.vgrowAt "vis" (.var "u"))
                                        (.lit (.i32
                                          (BitVec.ofNat 32 0))))
                                        (.seq (.vgrowSet "vis"
                                          (.var "u")
                                          (.lit (.i32
                                            (BitVec.ofNat 32 1))))
                                          dfsGrowPush)
                                        .skip)
                                      .fail)
                                    .skip)
                                  .fail) ρ =
                                .ok (ρC, .fellThrough) :=
                              hL1.trans hL4
                            have hBody : evalProgStmt vecGrowProg F
                                dfsGrowInnerBody ρ =
                                .ok (ρU, .fellThrough) := by
                              simp only [dfsGrowInnerBody]
                              exact (evalProgStmt_seq_fallthrough
                                vecGrowProg F _ _ _ _ hL1ev).trans huA
                            -- Thread the post-body lookups (all from
                            -- the lemma conclusions).
                            have hmB : envLookup ρU "m" =
                                some (.stdVecOwned ⟨mL, false⟩
                                  mL.length mL.length) :=
                              (envLookup_update_miss ρC "m" "u"
                                (.u64 (u + 1)) ρU (by decide)
                                hupU).trans hmC
                            have hnB : envLookup ρU "n" =
                                some (.u64 n) :=
                              (envLookup_update_miss ρC "n" "u"
                                (.u64 (u + 1)) ρU (by decide)
                                hupU).trans hnC
                            have hvB : envLookup ρU "v" =
                                some (.u64 v) :=
                              (envLookup_update_miss ρC "v" "u"
                                (.u64 (u + 1)) ρU (by decide)
                                hupU).trans hvC
                            have hvisU : envLookup ρU "vis" =
                                some (.stdVecOwned
                                  ⟨visL.set u.toNat 1, false⟩
                                  visL.length visL.length) :=
                              (envLookup_update_miss ρC "vis" "u"
                                (.u64 (u + 1)) ρU (by decide)
                                hupU).trans hvisC
                            have hvisB : envLookup ρU "vis" =
                                some (.stdVecOwned
                                  ⟨visL.set u.toNat 1, false⟩
                                  (visL.set u.toNat 1).length
                                  (visL.set u.toNat 1).length) := by
                              rw [hsetlen]
                              exact hvisU
                            have hvislenB :
                                (visL.set u.toNat 1).length <
                                2 ^ 64 := by
                              rw [hsetlen]
                              exact hvislen
                            have hstB : envLookup ρU "st" =
                                some (.stdVecOwned b2 l2 c2) :=
                              (envLookup_update_miss ρC "st" "u"
                                (.u64 (u + 1)) ρU (by decide)
                                hupU).trans hstC
                            have htopB : envLookup ρU "top" =
                                some (.u64 (top + 1)) :=
                              (envLookup_update_miss ρC "top" "u"
                                (.u64 (u + 1)) ρU (by decide)
                                hupU).trans htopC
                            have hcountB : envLookup ρU "count" =
                                some (.u64 (count + 1)) :=
                              (envLookup_update_miss ρC "count" "u"
                                (.u64 (u + 1)) ρU (by decide)
                                hupU).trans hcountC
                            rw [← e1, ← e2, ← e3] at herr
                            -- Budget premises after the push: fuel and
                            -- maxdiff track the marked list; the count
                            -- invariant advances with the fresh mark.
                            have hw00 : w = 0 := by simpa using hw0
                            have hvis0 : visL[u.toNat]? =
                                some (0 : BitVec 32) := by
                              simpa [hw00] using hgetV
                            have honesU : ones (visL.set u.toNat 1) =
                                ones visL + 1 :=
                              ones_set_one visL u.toNat hvis0
                            have hPgB : L0 +
                                (visL.set u.toNat 1).length + 8 +
                                (n.toNat - (u + 1).toNat) ≤ F := by
                              rw [hsetlen, hwrapU]
                              omega
                            have hcntB : l2 ≤
                                L0 + ones (visL.set u.toNat 1) := by
                              rw [hlen1, honesU]
                              omega
                            have hmaxB : L0 +
                                (visL.set u.toNat 1).length +
                                n.toNat ≤
                                stdVecMaxDiffBV.toNat - 1 := by
                              rw [hsetlen]
                              exact hmaxL0
                            have hev : evalProgStmt vecGrowProg F
                                dfsGrowInner ρU = .error e :=
                              ih (visL.set u.toNat 1) b2 l2 c2
                                (top + 1) (count + 1) (u + 1) ρU
                                hmB hvisB hvislenB hstB hfr hlen2
                                hbuflen2 h64_2 hcap2 hPgB hcntB
                                hmaxB hnB hvB htopB hcountB huU herr
                            simp only [dfsGrowInner]
                            rw [evalProgStmt_while_true _ _ _ _ _
                              hguardU, hBody]
                            exact hev
                      · -- Excluded by the maxdiff budget: `len ≤
                        -- maxdiff - 1` follows from `hcnt`, `ones ≤
                        -- length`, and `hmaxL0`.
                        have h1o := ones_le_length visL
                        have hle :
                            len ≤ stdVecMaxDiffBV.toNat - 1 := by
                          omega
                        exact absurd hle hmaxC
                    · -- `w ≠ 0`: already visited; skip, advance, recurse.
                      have hw0F : (w == (BitVec.ofNat 32 0)) =
                          false :=
                        Bool.eq_false_of_ne_true hw0
                      have hwEqF : evalExpr (.ueq
                          (.vgrowAt "vis" (.var "u"))
                          (.lit (.i32 (BitVec.ofNat 32 0)))) ρ =
                          .ok (.b false) := by
                        rw [hw0F] at hwEq
                        exact hwEq
                      simp only [hw0] at herr
                      have hskip : evalProgStmt vecGrowProg F .skip ρ =
                          .ok (ρ, .fellThrough) :=
                        evalProgStmt_skip _ _ _
                      have hL1 : evalProgStmt vecGrowProg F
                          (.if_ (.ult dfsGrowRowIdx (.vgrowLen "m"))
                            (.if_ (.une
                              (.vgrowAt "m" dfsGrowRowIdx)
                              (.lit (.i32 (BitVec.ofNat 32 0))))
                              (.if_ (.ult (.var "u")
                                (.vgrowLen "vis"))
                                (.if_ (.ueq
                                  (.vgrowAt "vis" (.var "u"))
                                  (.lit (.i32
                                    (BitVec.ofNat 32 0))))
                                  (.seq (.vgrowSet "vis"
                                    (.var "u")
                                    (.lit (.i32
                                      (BitVec.ofNat 32 1))))
                                    dfsGrowPush)
                                  .skip)
                                .fail)
                              .skip)
                            .fail) ρ =
                          evalProgStmt vecGrowProg F .skip ρ := by
                        rw [evalProgStmt_if_true _ _ _ _ _ _ hgIdx,
                          evalProgStmt_if_true _ _ _ _ _ _ hgNe,
                          evalProgStmt_if_true _ _ _ _ _ _ hgU,
                          evalProgStmt_if_false _ _ _ _ _ _ hwEqF]
                      have hL1ev : evalProgStmt vecGrowProg F
                          (.if_ (.ult dfsGrowRowIdx (.vgrowLen "m"))
                            (.if_ (.une
                              (.vgrowAt "m" dfsGrowRowIdx)
                              (.lit (.i32 (BitVec.ofNat 32 0))))
                              (.if_ (.ult (.var "u")
                                (.vgrowLen "vis"))
                                (.if_ (.ueq
                                  (.vgrowAt "vis" (.var "u"))
                                  (.lit (.i32
                                    (BitVec.ofNat 32 0))))
                                  (.seq (.vgrowSet "vis"
                                    (.var "u")
                                    (.lit (.i32
                                      (BitVec.ofNat 32 1))))
                                    dfsGrowPush)
                                  .skip)
                                .fail)
                              .skip)
                            .fail) ρ =
                          .ok (ρ, .fellThrough) :=
                        hL1.trans hskip
                      obtain ⟨ρU, hupU⟩ := envUpdate_some_of_lookup ρ
                        "u" (.u64 u) (.u64 (u + 1)) hu
                      obtain ⟨huA, huU⟩ := evalProgUAdv F ρ u hu ρU hupU
                      have hBody : evalProgStmt vecGrowProg F
                          dfsGrowInnerBody ρ =
                          .ok (ρU, .fellThrough) := by
                        simp only [dfsGrowInnerBody]
                        exact (evalProgStmt_seq_fallthrough vecGrowProg
                          F _ _ _ _ hL1ev).trans huA
                      have hmU : envLookup ρU "m" =
                          some (.stdVecOwned ⟨mL, false⟩
                            mL.length mL.length) :=
                        (envLookup_update_miss ρ "m" "u"
                          (.u64 (u + 1)) ρU (by decide)
                          hupU).trans hm
                      have hnU : envLookup ρU "n" = some (.u64 n) :=
                        (envLookup_update_miss ρ "n" "u"
                          (.u64 (u + 1)) ρU (by decide)
                          hupU).trans hn
                      have hvU : envLookup ρU "v" = some (.u64 v) :=
                        (envLookup_update_miss ρ "v" "u"
                          (.u64 (u + 1)) ρU (by decide)
                          hupU).trans hv
                      have htopU : envLookup ρU "top" =
                          some (.u64 top) :=
                        (envLookup_update_miss ρ "top" "u"
                          (.u64 (u + 1)) ρU (by decide)
                          hupU).trans htop
                      have hcountU : envLookup ρU "count" =
                          some (.u64 count) :=
                        (envLookup_update_miss ρ "count" "u"
                          (.u64 (u + 1)) ρU (by decide)
                          hupU).trans hcount
                      have hvisU : envLookup ρU "vis" =
                          some (.stdVecOwned ⟨visL, false⟩
                            visL.length visL.length) :=
                        (envLookup_update_miss ρ "vis" "u"
                          (.u64 (u + 1)) ρU (by decide)
                          hupU).trans hvis
                      have hstU : envLookup ρU "st" =
                          some (.stdVecOwned b len cap) :=
                        (envLookup_update_miss ρ "st" "u"
                          (.u64 (u + 1)) ρU (by decide)
                          hupU).trans hst
                      have hPgU : L0 + visL.length + 8 +
                          (n.toNat - (u + 1).toNat) ≤ F := by
                        rw [hwrapU]
                        omega
                      have hmaxU : len + (n.toNat - (u + 1).toNat) ≤
                          stdVecMaxDiffBV.toNat - 1 := by
                        rw [hwrapU]
                        have h1o := ones_le_length visL
                        omega
                      have hev : evalProgStmt vecGrowProg F dfsGrowInner
                          ρU = .error e :=
                        ih visL b len cap top count (u + 1) ρU
                          hmU hvisU hvislen hstU hlive hlen hbuflen
                          hlen64 hcap64 hPgU hcnt hmaxL0 hnU hvU
                          htopU hcountU huU herr
                      simp only [dfsGrowInner]
                      rw [evalProgStmt_while_true _ _ _ _ _ hguardU,
                        hBody]
                      exact hev
                  · -- Vacuous: contradicts the `ult` guard fact.
                    exact absurd (hltV_of huVlen) hltV
              · simp only [huVlen] at herr
                cases herr
                -- Visited-bound miss: the `if_` chain fails at the
                -- `vis` guard, then `.fail`.
                have hgUF : evalExpr (.ult (.var "u")
                    (.vgrowLen "vis")) ρ = .ok (.b false) := by
                  have hgUF' : (u.ult
                      (BitVec.ofNat 64 visL.length)) = false :=
                    Bool.eq_false_of_ne_true huVlen
                  rw [hgUF'] at hgU
                  exact hgU
                have hIf : evalProgStmt vecGrowProg F
                    (.if_ (.ult dfsGrowRowIdx (.vgrowLen "m"))
                      (.if_ (.une
                        (.vgrowAt "m" dfsGrowRowIdx)
                        (.lit (.i32 (BitVec.ofNat 32 0))))
                        (.if_ (.ult (.var "u")
                          (.vgrowLen "vis"))
                          (.if_ (.ueq
                            (.vgrowAt "vis" (.var "u"))
                            (.lit (.i32
                              (BitVec.ofNat 32 0))))
                            (.seq (.vgrowSet "vis"
                              (.var "u")
                              (.lit (.i32
                                (BitVec.ofNat 32 1))))
                              dfsGrowPush)
                            .skip)
                          .fail)
                        .skip)
                      .fail) ρ =
                    evalProgStmt vecGrowProg F .fail ρ := by
                  rw [evalProgStmt_if_true _ _ _ _ _ _ hgIdx,
                    evalProgStmt_if_true _ _ _ _ _ _ hgNe,
                    evalProgStmt_if_false _ _ _ _ _ _ hgUF]
                have hfail : evalProgStmt vecGrowProg F .fail ρ =
                    .error .AssertFail := by
                  have hfb : evalProgStmt vecGrowProg F .fail ρ =
                      evalStmtFuel F .fail ρ := by
                    simp only [evalProgStmt]
                  rw [hfb]
                  exact evalStmtFuel_fail _ _
                have hBody : evalProgStmt vecGrowProg F
                    dfsGrowInnerBody ρ = .error .AssertFail := by
                  simp only [dfsGrowInnerBody]
                  exact evalProgStmt_seq_err _ _ _ _ _ _
                    (hIf.trans hfail)
                have hev : evalProgStmt vecGrowProg (F + 1) dfsGrowInner
                    ρ = .error .AssertFail := by
                  simp only [dfsGrowInner]
                  rw [evalProgStmt_while_true _ _ _ _ _ hguardU, hBody]
                exact hev
            · -- `g = 0`: skip, advance, recurse.
              have hg0F : (g != (BitVec.ofNat 32 0)) = false :=
                Bool.eq_false_of_ne_true hg0
              have hgNeF : evalExpr (.une
                  (.vgrowAt "m" dfsGrowRowIdx)
                  (.lit (.i32 (BitVec.ofNat 32 0)))) ρ =
                  .ok (.b false) := by
                rw [hg0F] at hgNe
                exact hgNe
              simp only [hg0] at herr
              have hskip : evalProgStmt vecGrowProg F .skip ρ =
                  .ok (ρ, .fellThrough) :=
                evalProgStmt_skip _ _ _
              have hL1 : evalProgStmt vecGrowProg F
                  (.if_ (.ult dfsGrowRowIdx (.vgrowLen "m"))
                    (.if_ (.une
                      (.vgrowAt "m" dfsGrowRowIdx)
                      (.lit (.i32 (BitVec.ofNat 32 0))))
                      (.if_ (.ult (.var "u")
                        (.vgrowLen "vis"))
                        (.if_ (.ueq
                          (.vgrowAt "vis" (.var "u"))
                          (.lit (.i32
                            (BitVec.ofNat 32 0))))
                          (.seq (.vgrowSet "vis"
                            (.var "u")
                            (.lit (.i32
                              (BitVec.ofNat 32 1))))
                            dfsGrowPush)
                          .skip)
                        .fail)
                      .skip)
                    .fail) ρ =
                  evalProgStmt vecGrowProg F .skip ρ := by
                rw [evalProgStmt_if_true _ _ _ _ _ _ hgIdx,
                  evalProgStmt_if_false _ _ _ _ _ _ hgNeF]
              have hL1ev : evalProgStmt vecGrowProg F
                  (.if_ (.ult dfsGrowRowIdx (.vgrowLen "m"))
                    (.if_ (.une
                      (.vgrowAt "m" dfsGrowRowIdx)
                      (.lit (.i32 (BitVec.ofNat 32 0))))
                      (.if_ (.ult (.var "u")
                        (.vgrowLen "vis"))
                        (.if_ (.ueq
                          (.vgrowAt "vis" (.var "u"))
                          (.lit (.i32
                            (BitVec.ofNat 32 0))))
                          (.seq (.vgrowSet "vis"
                            (.var "u")
                            (.lit (.i32
                              (BitVec.ofNat 32 1))))
                            dfsGrowPush)
                          .skip)
                        .fail)
                      .skip)
                    .fail) ρ =
                  .ok (ρ, .fellThrough) :=
                hL1.trans hskip
              obtain ⟨ρU, hupU⟩ := envUpdate_some_of_lookup ρ
                "u" (.u64 u) (.u64 (u + 1)) hu
              obtain ⟨huA, huU⟩ := evalProgUAdv F ρ u hu ρU hupU
              have hBody : evalProgStmt vecGrowProg F
                  dfsGrowInnerBody ρ =
                  .ok (ρU, .fellThrough) := by
                simp only [dfsGrowInnerBody]
                exact (evalProgStmt_seq_fallthrough vecGrowProg F _ _
                  _ _ hL1ev).trans huA
              -- Lookups after the `u` advance.
              have hmU : envLookup ρU "m" =
                  some (.stdVecOwned ⟨mL, false⟩
                    mL.length mL.length) :=
                (envLookup_update_miss ρ "m" "u"
                  (.u64 (u + 1)) ρU (by decide)
                  hupU).trans hm
              have hnU : envLookup ρU "n" = some (.u64 n) :=
                (envLookup_update_miss ρ "n" "u"
                  (.u64 (u + 1)) ρU (by decide)
                  hupU).trans hn
              have hvU : envLookup ρU "v" = some (.u64 v) :=
                (envLookup_update_miss ρ "v" "u"
                  (.u64 (u + 1)) ρU (by decide)
                  hupU).trans hv
              have htopU : envLookup ρU "top" =
                  some (.u64 top) :=
                (envLookup_update_miss ρ "top" "u"
                  (.u64 (u + 1)) ρU (by decide)
                  hupU).trans htop
              have hcountU : envLookup ρU "count" =
                  some (.u64 count) :=
                (envLookup_update_miss ρ "count" "u"
                  (.u64 (u + 1)) ρU (by decide)
                  hupU).trans hcount
              have hvisU : envLookup ρU "vis" =
                  some (.stdVecOwned ⟨visL, false⟩
                    visL.length visL.length) :=
                (envLookup_update_miss ρ "vis" "u"
                  (.u64 (u + 1)) ρU (by decide)
                  hupU).trans hvis
              have hstU : envLookup ρU "st" =
                  some (.stdVecOwned b len cap) :=
                (envLookup_update_miss ρ "st" "u"
                  (.u64 (u + 1)) ρU (by decide)
                  hupU).trans hst
              -- Budget premises after the advance (state unchanged but
              -- `u`; the `(n - u)` slack absorbs the step).
              have hPgU : L0 + visL.length + 8 +
                  (n.toNat - (u + 1).toNat) ≤ F := by
                rw [hwrapU]
                omega
              have hmaxU : len + (n.toNat - (u + 1).toNat) ≤
                  stdVecMaxDiffBV.toNat - 1 := by
                rw [hwrapU]
                have h1o := ones_le_length visL
                omega
              have hev : evalProgStmt vecGrowProg F dfsGrowInner ρU =
                  .error e :=
                ih visL b len cap top count (u + 1) ρU
                  hmU hvisU hvislen hstU hlive hlen hbuflen
                  hlen64 hcap64 hPgU hcnt hmaxL0 hnU hvU
                  htopU hcountU huU herr
              simp only [dfsGrowInner]
              rw [evalProgStmt_while_true _ _ _ _ _ hguardU, hBody]
              exact hev
          · -- Vacuous: contradicts the `ult` guard fact.
            exact absurd (hltM_of hidxB) hltM
      · have hidxBF : (v * n + u).ult
            (BitVec.ofNat 64 mL.length) = false :=
          Bool.eq_false_of_ne_true hidxB
        rw [hidxBF] at hgIdx
        simp only [hidxB] at herr
        cases herr
        -- Matrix-bound miss: the `if_` chain fails at the top
        -- guard, then `.fail`.
        have hIf : evalProgStmt vecGrowProg F
            (.if_ (.ult dfsGrowRowIdx (.vgrowLen "m"))
              (.if_ (.une
                (.vgrowAt "m" dfsGrowRowIdx)
                (.lit (.i32 (BitVec.ofNat 32 0))))
                (.if_ (.ult (.var "u")
                  (.vgrowLen "vis"))
                  (.if_ (.ueq
                    (.vgrowAt "vis" (.var "u"))
                    (.lit (.i32
                      (BitVec.ofNat 32 0))))
                    (.seq (.vgrowSet "vis"
                      (.var "u")
                      (.lit (.i32
                        (BitVec.ofNat 32 1))))
                      dfsGrowPush)
                    .skip)
                  .fail)
                .skip)
              .fail) ρ =
            evalProgStmt vecGrowProg F .fail ρ :=
          evalProgStmt_if_false _ _ _ _ _ _ hgIdx
        have hfail : evalProgStmt vecGrowProg F .fail ρ =
            .error .AssertFail := by
          have hfb : evalProgStmt vecGrowProg F .fail ρ =
              evalStmtFuel F .fail ρ := by
            simp only [evalProgStmt]
          rw [hfb]
          exact evalStmtFuel_fail _ _
        have hBody : evalProgStmt vecGrowProg F
            dfsGrowInnerBody ρ = .error .AssertFail := by
          simp only [dfsGrowInnerBody]
          exact evalProgStmt_seq_err _ _ _ _ _ _
            (hIf.trans hfail)
        have hev : evalProgStmt vecGrowProg (F + 1) dfsGrowInner
            ρ = .error .AssertFail := by
          simp only [dfsGrowInner]
          rw [evalProgStmt_while_true _ _ _ _ _ hguardU, hBody]
        exact hev

/-- The row forward preserves the visited-list length (marks are
    `set`s, skips pass through). Needed wherever a row result feeds
    another scan (the drain, the entry). -/
theorem dfsGrowRowFwd_length (F : Nat) (mL visL : List (BitVec 32))
    (b : Vec32) (len cap : Nat) (n v top count u : BitVec 64)
    (vis' : List (BitVec 32)) (b' : Vec32) (l' c' : Nat)
    (top' count' u' : BitVec 64)
    (hrow : dfsGrowRowFwd F mL visL b len cap n v top count u =
      .ok (vis', b', l', c', top', count', u')) :
    vis'.length = visL.length := by
  induction F generalizing visL b len cap u top count with
  | zero =>
    simp only [dfsGrowRowFwd] at hrow
    cases huLT : u.ult n with
    | false =>
      simp only [huLT] at hrow
      cases hrow
      rfl
    | true =>
      simp only [huLT, ↓reduceIte] at hrow
      cases hrow
  | succ F ih =>
    simp only [dfsGrowRowFwd, ↓reduceIte] at hrow
    cases huLT : u.ult n with
    | false =>
      simp only [huLT, ↓reduceIte] at hrow
      cases hrow
      rfl
    | true =>
      simp only [huLT, ↓reduceIte] at hrow
      by_cases hidxB :
          (v * n + u).ult (BitVec.ofNat 64 mL.length) = true
      · simp only [hidxB, ↓reduceIte] at hrow
        cases hgetM : mL[(v * n + u).toNat]? with
        | none =>
          simp only [hgetM, ↓reduceIte] at hrow
          cases hrow
        | some g =>
          simp only [hgetM, ↓reduceIte] at hrow
          by_cases hltM : (v * n + u).toNat < mL.length
          · simp only [hltM, ↓reduceIte] at hrow
            by_cases hg0 : (g != (BitVec.ofNat 32 0)) = true
            · simp only [hg0, ↓reduceIte] at hrow
              by_cases huVlen :
                  u.ult (BitVec.ofNat 64 visL.length) = true
              · simp only [huVlen, ↓reduceIte] at hrow
                cases hgetV : visL[u.toNat]? with
                | none =>
                  simp only [hgetV, ↓reduceIte] at hrow
                  cases hrow
                | some w =>
                  simp only [hgetV, ↓reduceIte] at hrow
                  by_cases hltV : u.toNat < visL.length
                  · simp only [hltV, ↓reduceIte] at hrow
                    by_cases hw0 :
                        (w == (BitVec.ofNat 32 0)) = true
                    · simp only [hw0, ↓reduceIte] at hrow
                      by_cases hmaxC :
                          len ≤ stdVecMaxDiffBV.toNat - 1
                      · simp only [hmaxC, ↓reduceIte] at hrow
                        by_cases htl :
                            top.ult (BitVec.ofNat 64 len) = true
                        · simp only [htl, ↓reduceIte] at hrow
                          cases hsetB : vecSet b top.toNat
                              (BitVec.ofNat 32 u.toNat) with
                          | error e =>
                            simp only [hsetB] at hrow
                            cases hrow
                          | ok b2 =>
                            simp only [hsetB] at hrow
                            have hrec := ih (visL.set u.toNat 1)
                              b2 len cap (top + 1) (count + 1)
                              (u + 1) hrow
                            have hL : (visL.set u.toNat 1).length =
                                visL.length := by
                              simp
                            omega
                        · have htlF : top.ult
                              (BitVec.ofNat 64 len) = false :=
                            Bool.eq_false_of_ne_true htl
                          simp only [htlF, ↓reduceIte] at hrow
                          cases hpush :
                              stdVecPushBackFwd b len cap
                                (BitVec.ofNat 32 u.toNat) with
                          | error e =>
                            simp only [hpush, vecGrow_bind_err, ↓reduceIte] at hrow
                            cases hrow
                          | ok pv =>
                            simp only [hpush, vecGrow_bind_ok, ↓reduceIte] at hrow
                            cases hown : vecGrowOwned pv with
                            | error e =>
                              simp only [hown, vecGrow_bind_err, ↓reduceIte] at hrow
                              cases hrow
                            | ok pt =>
                              simp only [hown, vecGrow_bind_ok, ↓reduceIte] at hrow
                              have hrec := ih (visL.set u.toNat 1)
                                pt.1 pt.2.1 pt.2.2 (top + 1) (count + 1)
                                (u + 1) hrow
                              have hL : (visL.set u.toNat 1).length =
                                  visL.length := by
                                simp
                              omega
                      · by_cases htl :
                            top.ult (BitVec.ofNat 64 len) = true
                        · simp only [htl, ↓reduceIte] at hrow
                          cases hsetB : vecSet b top.toNat
                              (BitVec.ofNat 32 u.toNat) with
                          | error e =>
                            simp only [hsetB] at hrow
                            cases hrow
                          | ok b2 =>
                            simp only [hsetB] at hrow
                            have hrec := ih (visL.set u.toNat 1)
                              b2 len cap (top + 1) (count + 1)
                              (u + 1) hrow
                            have hL : (visL.set u.toNat 1).length =
                                visL.length := by
                              simp
                            omega
                        · have htlF : top.ult
                              (BitVec.ofNat 64 len) = false :=
                            Bool.eq_false_of_ne_true htl
                          simp only [hmaxC, htlF, ↓reduceIte] at hrow
                          cases hrow
                    · simp only [hw0, ↓reduceIte] at hrow
                      exact ih visL b len cap top count (u + 1) hrow
                  · simp only [hltV, ↓reduceIte] at hrow
                    cases hrow
              · simp only [huVlen, ↓reduceIte] at hrow
                cases hrow
            · simp only [hg0, ↓reduceIte] at hrow
              exact ih visL b len cap top count (u + 1) hrow
          · simp only [hltM, ↓reduceIte] at hrow
            cases hrow
      · simp only [hidxB, ↓reduceIte] at hrow
        cases hrow

/-! ## Drain agreement -/

/-- Drain agreement (ok leg): the `top != 0` loop evaluates exactly
    as the outer forward says. Induction on fuel; each taken pop
    mirrors its evaluator steps, the row scan runs through
    `dfsGrowRow_ok` at predecessor fuel, and the drain recurses
    through the IH at predecessor fuel. -/
theorem dfsGrowOuter_ok (F : Nat) (mL visL : List (BitVec 32))
    (b : Vec32) (len cap : Nat) (n top count v u : BitVec 64) (ρ : Env)
    (L0 : Nat)
    (hm : envLookup ρ "m" =
      some (.stdVecOwned ⟨mL, false⟩ mL.length mL.length))
    (hmen : mL.length < 2 ^ 64)
    (hvis : envLookup ρ "vis" =
      some (.stdVecOwned ⟨visL, false⟩ visL.length visL.length))
    (hvislen : visL.length < 2 ^ 64)
    (hst : envLookup ρ "st" = some (.stdVecOwned b len cap))
    (hlive : b.freed = false)
    (hlen : len ≤ b.val.length)
    (hbuflen : b.val.length < 2 ^ 64)
    (hlen64 : len < 2 ^ 64)
    (hcap64 : cap < 2 ^ 64)
    (hP : L0 + visL.length + 8 + n.toNat +
      8 * (top.toNat + (visL.length - ones visL)) ≤ F)
    (hLV : L0 + visL.length + 1 < 2 ^ 64)
    (hcnt : len ≤ L0 + ones visL)
    (htopLe : top.toNat ≤ len)
    (hn : envLookup ρ "n" = some (.u64 n))
    (hv : envLookup ρ "v" = some (.u64 v))
    (htop : envLookup ρ "top" = some (.u64 top))
    (hcount : envLookup ρ "count" = some (.u64 count))
    (hu : envLookup ρ "u" = some (.u64 u))
    (vis' : List (BitVec 32)) (b' : Vec32) (l' c' : Nat)
    (top' count' v' u' : BitVec 64)
    (houter : dfsGrowOuterFwd F mL visL b len cap n top count v u =
      .ok (vis', b', l', c', top', count', v', u')) :
    ∃ ρ', evalProgStmt vecGrowProg F dfsGrowOuter ρ =
        .ok (ρ', .fellThrough) ∧
      envLookup ρ' "m" =
        some (.stdVecOwned ⟨mL, false⟩ mL.length mL.length) ∧
      envLookup ρ' "vis" =
        some (.stdVecOwned ⟨vis', false⟩ visL.length visL.length) ∧
      envLookup ρ' "st" = some (.stdVecOwned b' l' c') ∧
      envLookup ρ' "n" = some (.u64 n) ∧
      envLookup ρ' "v" = some (.u64 v') ∧
      envLookup ρ' "top" = some (.u64 top') ∧
      envLookup ρ' "count" = some (.u64 count') ∧
      envLookup ρ' "u" = some (.u64 u') ∧
      b'.freed = false ∧ l' ≤ b'.val.length ∧
      b'.val.length < 2 ^ 64 ∧ l' < 2 ^ 64 ∧ c' < 2 ^ 64 ∧
      l' ≤ L0 + ones vis' ∧ ones visL ≤ ones vis' ∧
      top'.toNat ≤ l' := by
  induction F generalizing visL b len cap top count v u ρ with
  | zero =>
    simp only [dfsGrowOuterFwd] at houter
    cases htop0 : top != (BitVec.ofNat 64 0) with
    | false =>
      simp only [htop0] at houter
      cases houter
      have hguard : evalExpr (.une (.var "top")
          (.lit (.u64 (BitVec.ofNat 64 0)))) ρ =
          .ok (.b false) := by
        have h1 := evalExpr_var_hit ρ "top" (.u64 top') htop
        have h2 : evalExpr (.lit (.u64 (BitVec.ofNat 64 0))) ρ =
            .ok (.u64 (BitVec.ofNat 64 0)) := evalExpr_lit _ _
        have h3 := evalExpr_une_u64 _ _ _ _ _ h1 h2
        rw [htop0] at h3
        exact h3
      have hwhile := evalProgStmt_while_false vecGrowProg 0
        (.une (.var "top") (.lit (.u64 (BitVec.ofNat 64 0))))
        dfsGrowOuterBody ρ hguard
      simp only [dfsGrowOuter] at hwhile ⊢
      -- Post-subst everything is primed; the lockstep conjuncts are
      -- exactly the substituted `hcnt`/`htopLe` plus reflexivities.
      refine ⟨ρ, hwhile, hm, hvis, hst, hn, hv, htop, hcount, hu,
        hlive, hlen, hbuflen, hlen64, hcap64, hcnt, Nat.le_refl _, htopLe⟩
    | true =>
      simp only [htop0] at houter
      cases houter
  | succ F ih =>
    simp only [dfsGrowOuterFwd] at houter
    cases htop0 : top != (BitVec.ofNat 64 0) with
    | false =>
      simp only [htop0] at houter
      cases houter
      have hguard : evalExpr (.une (.var "top")
          (.lit (.u64 (BitVec.ofNat 64 0)))) ρ =
          .ok (.b false) := by
        have h1 := evalExpr_var_hit ρ "top" (.u64 top') htop
        have h2 : evalExpr (.lit (.u64 (BitVec.ofNat 64 0))) ρ =
            .ok (.u64 (BitVec.ofNat 64 0)) := evalExpr_lit _ _
        have h3 := evalExpr_une_u64 _ _ _ _ _ h1 h2
        rw [htop0] at h3
        exact h3
      have hwhile := evalProgStmt_while_false vecGrowProg (F + 1)
        (.une (.var "top") (.lit (.u64 (BitVec.ofNat 64 0))))
        dfsGrowOuterBody ρ hguard
      simp only [dfsGrowOuter] at hwhile ⊢
      -- Post-subst everything is primed; the lockstep conjuncts are
      -- exactly the substituted `hcnt`/`htopLe` plus a reflexivity.
      refine ⟨ρ, hwhile, hm, hvis, hst, hn, hv, htop, hcount, hu,
        hlive, hlen, hbuflen, hlen64, hcap64, hcnt, Nat.le_refl _, htopLe⟩
    | true =>
      simp only [htop0] at houter
      -- Shared: the `top != 0` guard at `F + 1`.
      have hguardU : evalExpr (.une (.var "top")
          (.lit (.u64 (BitVec.ofNat 64 0)))) ρ =
          .ok (.b true) := by
        have h1 := evalExpr_var_hit ρ "top" (.u64 top) htop
        have h2 : evalExpr (.lit (.u64 (BitVec.ofNat 64 0))) ρ =
            .ok (.u64 (BitVec.ofNat 64 0)) := evalExpr_lit _ _
        have h3 := evalExpr_une_u64 _ _ _ _ _ h1 h2
        rw [htop0] at h3
        exact h3
      -- Decrement `top`.
      have htopDecE : evalExpr (.usub (.var "top")
          (.lit (.u64 (BitVec.ofNat 64 1)))) ρ =
          .ok (.u64 (top - 1)) :=
        evalExpr_usub_u64_rr _ _ _ _ _
          (evalExpr_var_hit ρ "top" (.u64 top) htop)
          (evalExpr_lit _ _)
      obtain ⟨ρT1, hupT1⟩ := envUpdate_some_of_lookup ρ "top"
        (.u64 top) (.u64 (top - 1)) htop
      have htopDecA : evalProgStmt vecGrowProg F
          (.assign "top" (.usub (.var "top")
            (.lit (.u64 (BitVec.ofNat 64 1))))) ρ =
          .ok (ρT1, .fellThrough) := by
        have hfb : evalProgStmt vecGrowProg F
            (.assign "top" (.usub (.var "top")
              (.lit (.u64 (BitVec.ofNat 64 1))))) ρ =
            evalStmtFuel F
              (.assign "top" (.usub (.var "top")
                (.lit (.u64 (BitVec.ofNat 64 1))))) ρ := by
          simp only [evalProgStmt]
        rw [hfb]
        exact evalStmtFuel_assign _ _ _ _ _ _ htopDecE hupT1
      have htopT1 : envLookup ρT1 "top" = some (.u64 (top - 1)) :=
        envLookup_update_hit ρ "top" _ ρT1 hupT1
      -- Guard facts in `ρT1`.
      have hmT1 : envLookup ρT1 "m" =
          some (.stdVecOwned ⟨mL, false⟩ mL.length mL.length) :=
        (envLookup_update_miss ρ "m" "top" (.u64 (top - 1)) ρT1
          (by decide) hupT1).trans hm
      have hnT1 : envLookup ρT1 "n" = some (.u64 n) :=
        (envLookup_update_miss ρ "n" "top" (.u64 (top - 1)) ρT1
          (by decide) hupT1).trans hn
      have hvT1 : envLookup ρT1 "v" = some (.u64 v) :=
        (envLookup_update_miss ρ "v" "top" (.u64 (top - 1)) ρT1
          (by decide) hupT1).trans hv
      have huT1 : envLookup ρT1 "u" = some (.u64 u) :=
        (envLookup_update_miss ρ "u" "top" (.u64 (top - 1)) ρT1
          (by decide) hupT1).trans hu
      have hvisT1 : envLookup ρT1 "vis" =
          some (.stdVecOwned ⟨visL, false⟩
            visL.length visL.length) :=
        (envLookup_update_miss ρ "vis" "top" (.u64 (top - 1)) ρT1
          (by decide) hupT1).trans hvis
      have hcountT1 : envLookup ρT1 "count" = some (.u64 count) :=
        (envLookup_update_miss ρ "count" "top" (.u64 (top - 1)) ρT1
          (by decide) hupT1).trans hcount
      have hstT1 : envLookup ρT1 "st" =
          some (.stdVecOwned b len cap) :=
        (envLookup_update_miss ρ "st" "top" (.u64 (top - 1)) ρT1
          (by decide) hupT1).trans hst
      have hstLen : evalExpr (.vgrowLen "st") ρT1 =
          .ok (.u64 (BitVec.ofNat 64 len)) :=
        evalExpr_vgrowLen_some "st" ρT1 b len cap hstT1
      have hgTop : evalExpr (.ult (.var "top")
          (.vgrowLen "st")) ρT1 =
          .ok (.b ((top - 1).ult (BitVec.ofNat 64 len))) :=
        evalExpr_ult_u64 _ _ _ _ _
          (evalExpr_var_hit ρT1 "top" (.u64 (top - 1)) htopT1)
          hstLen
      by_cases hB : (top - 1).ult (BitVec.ofNat 64 len) = true
      · rw [hB] at hgTop
        simp only [hB, ↓reduceIte] at houter
        cases hgetS : b.val[(top - 1).toNat]? with
        | none =>
          simp only [hgetS, ↓reduceIte] at houter
          cases houter
        | some w =>
          simp only [hgetS, ↓reduceIte] at houter
          by_cases hltS : (top - 1).toNat < len
          · simp only [hltS, ↓reduceIte] at houter
            -- Pop read plus widening.
            have hrd : evalExpr (.vgrowAt "st" (.var "top")) ρT1 =
                .ok (.i32 w) :=
              evalExpr_vgrowAt_some "st" _ ρT1 b len cap (top - 1) w
                hstT1
                (evalExpr_var_hit ρT1 "top" (.u64 (top - 1)) htopT1)
                hlive hgetS hltS
            have hwide : evalExpr
                (.u64ofI32 (.vgrowAt "st" (.var "top"))) ρT1 =
                .ok (.u64 (w.signExtend 64)) :=
              evalExpr_u64ofI32_ok _ _ _ hrd
            obtain ⟨ρV2, hupV2⟩ := envUpdate_some_of_lookup ρT1 "v"
              (.u64 v) (.u64 (w.signExtend 64)) hvT1
            have hVA : evalProgStmt vecGrowProg F
                (.assign "v"
                  (.u64ofI32 (.vgrowAt "st" (.var "top")))) ρT1 =
                .ok (ρV2, .fellThrough) := by
              have hfb : evalProgStmt vecGrowProg F
                  (.assign "v"
                    (.u64ofI32 (.vgrowAt "st" (.var "top")))) ρT1 =
                  evalStmtFuel F
                    (.assign "v"
                      (.u64ofI32
                        (.vgrowAt "st" (.var "top")))) ρT1 := by
                simp only [evalProgStmt]
              rw [hfb]
              exact evalStmtFuel_assign _ _ _ _ _ _ hwide hupV2
            have hvV2 : envLookup ρV2 "v" =
                some (.u64 (w.signExtend 64)) :=
              envLookup_update_hit ρT1 "v" _ ρV2 hupV2
            -- `u := 0`.
            have huV2 : envLookup ρV2 "u" = some (.u64 u) :=
              (envLookup_update_miss ρT1 "u" "v"
                (.u64 (w.signExtend 64)) ρV2 (by decide)
                hupV2).trans
                ((envLookup_update_miss ρ "u" "top"
                  (.u64 (top - 1)) ρT1 (by decide) hupT1).trans hu)
            have hu0E : evalExpr
                (.lit (.u64 (BitVec.ofNat 64 0))) ρV2 =
                .ok (.u64 (BitVec.ofNat 64 0)) := evalExpr_lit _ _
            obtain ⟨ρU0, hupU0⟩ := envUpdate_some_of_lookup ρV2 "u"
              (.u64 u) (.u64 (BitVec.ofNat 64 0)) huV2
            have hUA0 : evalProgStmt vecGrowProg F
                (.assign "u"
                  (.lit (.u64 (BitVec.ofNat 64 0)))) ρV2 =
                .ok (ρU0, .fellThrough) := by
              have hfb : evalProgStmt vecGrowProg F
                  (.assign "u"
                    (.lit (.u64 (BitVec.ofNat 64 0)))) ρV2 =
                  evalStmtFuel F
                    (.assign "u"
                      (.lit (.u64 (BitVec.ofNat 64 0)))) ρV2 := by
                simp only [evalProgStmt]
              rw [hfb]
              exact evalStmtFuel_assign _ _ _ _ _ _ hu0E hupU0
            have huU0 : envLookup ρU0 "u" =
                some (.u64 (BitVec.ofNat 64 0)) :=
              envLookup_update_hit ρV2 "u" _ ρU0 hupU0
            -- Row scan at predecessor fuel.
            cases hrowC : dfsGrowRowFwd F mL visL b len cap n
                (w.signExtend 64) (top - 1) count 0 with
            | error e =>
              simp only [hrowC, ↓reduceIte] at houter
              cases houter
            | ok t =>
              simp only [hrowC, ↓reduceIte] at houter
              obtain ⟨vr, b2r, l2r, c2r, top2r, count2r, u2r⟩ := t
              have hmV2 : envLookup ρV2 "m" =
                  some (.stdVecOwned ⟨mL, false⟩
                    mL.length mL.length) :=
                (envLookup_update_miss ρT1 "m" "v"
                  (.u64 (w.signExtend 64)) ρV2 (by decide)
                  hupV2).trans hmT1
              have hmU0 : envLookup ρU0 "m" =
                  some (.stdVecOwned ⟨mL, false⟩
                    mL.length mL.length) :=
                (envLookup_update_miss ρV2 "m" "u"
                  (.u64 (BitVec.ofNat 64 0)) ρU0 (by decide)
                  hupU0).trans hmV2
              have hnV2 : envLookup ρV2 "n" = some (.u64 n) :=
                (envLookup_update_miss ρT1 "n" "v"
                  (.u64 (w.signExtend 64)) ρV2 (by decide)
                  hupV2).trans hnT1
              have hnU0 : envLookup ρU0 "n" = some (.u64 n) :=
                (envLookup_update_miss ρV2 "n" "u"
                  (.u64 (BitVec.ofNat 64 0)) ρU0 (by decide)
                  hupU0).trans hnV2
              have hvisV2 : envLookup ρV2 "vis" =
                  some (.stdVecOwned ⟨visL, false⟩
                    visL.length visL.length) :=
                (envLookup_update_miss ρT1 "vis" "v"
                  (.u64 (w.signExtend 64)) ρV2 (by decide)
                  hupV2).trans hvisT1
              have hvisU0 : envLookup ρU0 "vis" =
                  some (.stdVecOwned ⟨visL, false⟩
                    visL.length visL.length) :=
                (envLookup_update_miss ρV2 "vis" "u"
                  (.u64 (BitVec.ofNat 64 0)) ρU0 (by decide)
                  hupU0).trans hvisV2
              have hstV2 : envLookup ρV2 "st" =
                  some (.stdVecOwned b len cap) :=
                (envLookup_update_miss ρT1 "st" "v"
                  (.u64 (w.signExtend 64)) ρV2 (by decide)
                  hupV2).trans hstT1
              have hstU0 : envLookup ρU0 "st" =
                  some (.stdVecOwned b len cap) :=
                (envLookup_update_miss ρV2 "st" "u"
                  (.u64 (BitVec.ofNat 64 0)) ρU0 (by decide)
                  hupU0).trans hstV2
              have htopV2 : envLookup ρV2 "top" =
                  some (.u64 (top - 1)) :=
                (envLookup_update_miss ρT1 "top" "v"
                  (.u64 (w.signExtend 64)) ρV2 (by decide)
                  hupV2).trans htopT1
              have htopU0 : envLookup ρU0 "top" =
                  some (.u64 (top - 1)) :=
                (envLookup_update_miss ρV2 "top" "u"
                  (.u64 (BitVec.ofNat 64 0)) ρU0 (by decide)
                  hupU0).trans htopV2
              have hcountV2 : envLookup ρV2 "count" =
                  some (.u64 count) :=
                (envLookup_update_miss ρT1 "count" "v"
                  (.u64 (w.signExtend 64)) ρV2 (by decide)
                  hupV2).trans hcountT1
              have hcountU0 : envLookup ρU0 "count" =
                  some (.u64 count) :=
                (envLookup_update_miss ρV2 "count" "u"
                  (.u64 (BitVec.ofNat 64 0)) ρU0 (by decide)
                  hupU0).trans hcountV2
              have hvU0 : envLookup ρU0 "v" =
                  some (.u64 (w.signExtend 64)) :=
                (envLookup_update_miss ρV2 "v" "u"
                  (.u64 (BitVec.ofNat 64 0)) ρU0 (by decide)
                  hupU0).trans hvV2
              -- `top != 0` as naturals: `1 ≤ top.toNat`, so `top - 1`
              -- does not wrap.
              have htopge1 : 1 ≤ top.toNat := by
                have htopne : top ≠ BitVec.ofNat 64 0 := by
                  intro hcon
                  rw [hcon, bne_self_eq_false] at htop0
                  exact Bool.false_ne_true htop0
                have h0 : (BitVec.ofNat 64 0).toNat = 0 := rfl
                have hz : top.toNat ≠ 0 := by
                  intro h
                  apply htopne
                  apply BitVec.toNat_inj.mp
                  rw [h, h0]
                omega
              have hsub1 : (top - 1).toNat = top.toNat - 1 := by
                have h1 : ((1 : BitVec 64)).toNat = 1 := rfl
                have hlt : top.toNat < 2 ^ 64 := BitVec.isLt top
                have hsub : (top - 1).toNat =
                    (2 ^ 64 - (1 : BitVec 64).toNat + top.toNat) %
                      2 ^ 64 :=
                  BitVec.toNat_sub _ _
                rw [h1] at hsub
                omega
              -- Row fuel: the row starts at `u = 0` and `8 * P ≥ 8`.
              have h0u : ((0 : BitVec 64)).toNat = 0 := rfl
              have hProw : L0 + visL.length + 8 +
                  (n.toNat - (0 : BitVec 64).toNat) ≤ F := by
                omega
              have htopLeU0 : (top - 1).toNat ≤ len :=
                Nat.le_of_lt hltS
              obtain ⟨ρR, hRowEval, hmR, hvisR, hstR, hnR, hvR,
                  htopR, hcountR, huR, hfrR, hlenR, hbuflenR, h64R,
                  hcapR, hcntR, hmonoR, htopEqR, htopLeR⟩ :=
                dfsGrowRow_ok F mL visL b len cap n
                  (w.signExtend 64) (top - 1) count 0 ρU0 L0
                  hmU0 hmen hvisU0 hvislen hstU0 hlive hlen hbuflen
                  hlen64 hcap64 hProw hLV hcnt htopLeU0 hnU0 hvU0
                  htopU0 hcountU0 huU0
                  vr b2r l2r c2r top2r count2r u2r hrowC
              have hvrlen : vr.length = visL.length :=
                dfsGrowRowFwd_length F mL visL b len cap n
                  (w.signExtend 64) (top - 1) count 0 vr b2r
                  l2r c2r top2r count2r u2r hrowC
              have hvislenR : vr.length < 2 ^ 64 := hvrlen ▸ hvislen
              rw [← hvrlen] at hvisR
              -- Outer fuel for the recursive call: the potential
              -- `top + (length - ones)` drops by exactly one across
              -- the row (`hvrlen` + row top equation + `top ≥ 1`).
              -- `ones_le_length` excludes the vacuous `ones > length`
              -- case split.
              have hLVih : L0 + vr.length + 1 < 2 ^ 64 :=
                hvrlen ▸ hLV
              have honesvr : ones vr ≤ vr.length := ones_le_length vr
              have hPih : L0 + vr.length + 8 + n.toNat +
                  8 * (top2r.toNat + (vr.length - ones vr)) ≤ F := by
                omega
              obtain ⟨ρ', ihEval, ihM, ihVis, ihSt, ihN, ihV, ihTop,
                  ihCount, ihU, ihFr, ihLe, ihBuflen, ih64,
                  ihCap, ihCnt, ihMono, ihTopLe⟩ :=
                ih vr b2r l2r c2r top2r count2r (w.signExtend 64)
                  u2r ρR hmR hvisR hvislenR hstR hfrR hlenR
                  hbuflenR h64R hcapR hPih hLVih hcntR htopLeR hnR
                  hvR htopR hcountR huR
                  houter
              rw [hvrlen] at ihVis
              -- Body assembly.
              have hGuardIf : evalProgStmt vecGrowProg F
                  (.if_ (.ult (.var "top") (.vgrowLen "st"))
                    (.assign "v"
                      (.u64ofI32 (.vgrowAt "st" (.var "top"))))
                    .fail) ρT1 =
                  evalProgStmt vecGrowProg F
                    (.assign "v"
                      (.u64ofI32
                        (.vgrowAt "st" (.var "top")))) ρT1 := by
                rw [evalProgStmt_if_true _ _ _ _ _ _ hgTop]
              have hGuardEv : evalProgStmt vecGrowProg F
                  (.if_ (.ult (.var "top") (.vgrowLen "st"))
                    (.assign "v"
                      (.u64ofI32 (.vgrowAt "st" (.var "top"))))
                    .fail) ρT1 =
                  .ok (ρV2, .fellThrough) :=
                hGuardIf.trans hVA
              have hRowSeq : evalProgStmt vecGrowProg F
                  (.seq (.assign "u"
                    (.lit (.u64 (BitVec.ofNat 64 0))))
                    dfsGrowInner) ρV2 =
                  .ok (ρR, .fellThrough) :=
                (evalProgStmt_seq_fallthrough vecGrowProg F _ _ _ _
                  hUA0).trans hRowEval
              have hBodyTl : evalProgStmt vecGrowProg F
                  (.seq (.if_ (.ult (.var "top") (.vgrowLen "st"))
                    (.assign "v"
                      (.u64ofI32 (.vgrowAt "st" (.var "top"))))
                    .fail)
                  (.seq (.assign "u"
                    (.lit (.u64 (BitVec.ofNat 64 0))))
                    dfsGrowInner)) ρT1 =
                  .ok (ρR, .fellThrough) :=
                (evalProgStmt_seq_fallthrough vecGrowProg F _ _ _ _
                  hGuardEv).trans hRowSeq
              have hBody : evalProgStmt vecGrowProg F
                  (.seq (.assign "top" (.usub (.var "top")
                    (.lit (.u64 (BitVec.ofNat 64 1)))))
                  (.seq (.if_ (.ult (.var "top") (.vgrowLen "st"))
                    (.assign "v"
                      (.u64ofI32 (.vgrowAt "st" (.var "top"))))
                    .fail)
                  (.seq (.assign "u"
                    (.lit (.u64 (BitVec.ofNat 64 0))))
                    dfsGrowInner))) ρ =
                  .ok (ρR, .fellThrough) :=
                (evalProgStmt_seq_fallthrough vecGrowProg F _ _ _ _
                  htopDecA).trans hBodyTl
              simp only [dfsGrowOuter, dfsGrowOuterBody] at ⊢ ihEval
              -- Lockstep: `l'`/`top' ≤ l'` come straight from the IH
              -- and mono chains row then IH. (No top equation: the
              -- per-iteration pop makes `top + ones` level-dependent.)
              have hmono : ones visL ≤ ones vis' :=
                Nat.le_trans hmonoR ihMono
              refine ⟨ρ', ?_, ihM, ihVis, ihSt, ihN, ihV, ihTop,
                ihCount, ihU, ihFr, ihLe, ihBuflen, ih64, ihCap,
                ihCnt, hmono, ihTopLe⟩
              rw [evalProgStmt_while_true _ _ _ _ _ hguardU, hBody]
              exact ihEval
          · simp only [hltS, ↓reduceIte] at houter
            cases houter
      · simp only [hB, ↓reduceIte] at houter
        cases houter

/-- Drain error agreement: the `top != 0` loop evaluates exactly as
    the outer forward says on the error legs. Fuel induction. Besides
    the ok-leg lookups it takes the fuel premise `hP`, the length cap
    `hLV`, the count invariant `hcnt`, the top bound `htopLe`, and a
    maxdiff budget `hmaxL0` (same shape as the row's, threaded
    unchanged through the row via length preservation; it excludes the
    over-strict gate case, exactly as in the row). Miss arms with
    contradictory case facts close by `getElem?_eq_getElem`; the row
    either errors (row err leg, threaded through the body) or succeeds
    (row ok leg, then the IH). -/
theorem dfsGrowOuter_err (F : Nat) (mL visL : List (BitVec 32))
    (b : Vec32) (len cap : Nat) (n top count v u : BitVec 64) (ρ : Env)
    (L0 : Nat)
    (hm : envLookup ρ "m" =
      some (.stdVecOwned ⟨mL, false⟩ mL.length mL.length))
    (hmen : mL.length < 2 ^ 64)
    (hvis : envLookup ρ "vis" =
      some (.stdVecOwned ⟨visL, false⟩ visL.length visL.length))
    (hvislen : visL.length < 2 ^ 64)
    (hst : envLookup ρ "st" = some (.stdVecOwned b len cap))
    (hlive : b.freed = false)
    (hlen : len ≤ b.val.length)
    (hbuflen : b.val.length < 2 ^ 64)
    (hlen64 : len < 2 ^ 64)
    (hcap64 : cap < 2 ^ 64)
    (hP : L0 + visL.length + 8 + n.toNat +
      8 * (top.toNat + (visL.length - ones visL)) ≤ F)
    (hLV : L0 + visL.length + 1 < 2 ^ 64)
    (hcnt : len ≤ L0 + ones visL)
    (htopLe : top.toNat ≤ len)
    (hmaxL0 : L0 + visL.length + n.toNat ≤ stdVecMaxDiffBV.toNat - 1)
    (hn : envLookup ρ "n" = some (.u64 n))
    (hv : envLookup ρ "v" = some (.u64 v))
    (htop : envLookup ρ "top" = some (.u64 top))
    (hcount : envLookup ρ "count" = some (.u64 count))
    (hu : envLookup ρ "u" = some (.u64 u))
    (e : Panic)
    (herr : dfsGrowOuterFwd F mL visL b len cap n top count v u =
      .error e) :
    evalProgStmt vecGrowProg F dfsGrowOuter ρ = .error e := by
  induction F generalizing visL b len cap top count v u ρ with
  | zero =>
    simp only [dfsGrowOuterFwd] at herr
    cases htop0 : top != (BitVec.ofNat 64 0) with
    | false =>
      simp only [htop0] at herr
      cases herr
    | true =>
      simp only [htop0] at herr
      cases herr
      have hguardU : evalExpr (.une (.var "top")
          (.lit (.u64 (BitVec.ofNat 64 0)))) ρ =
          .ok (.b true) := by
        have h1 := evalExpr_var_hit ρ "top" (.u64 top) htop
        have h2 : evalExpr (.lit (.u64 (BitVec.ofNat 64 0))) ρ =
            .ok (.u64 (BitVec.ofNat 64 0)) := evalExpr_lit _ _
        have h3 := evalExpr_une_u64 _ _ _ _ _ h1 h2
        rw [htop0] at h3
        exact h3
      have hfb : evalProgStmt vecGrowProg 0 dfsGrowOuter ρ =
          evalStmtFuel 0 dfsGrowOuter ρ := by
        simp only [dfsGrowOuter, evalProgStmt]
      rw [hfb]
      simp only [dfsGrowOuter]
      exact evalStmtFuel_zero_while_enter _ _ _ hguardU
  | succ F ih =>
    simp only [dfsGrowOuterFwd] at herr
    cases htop0 : top != (BitVec.ofNat 64 0) with
    | false =>
      simp only [htop0] at herr
      cases herr
    | true =>
      simp only [htop0] at herr
      -- Shared: the `top != 0` guard at `F + 1`.
      have hguardU : evalExpr (.une (.var "top")
          (.lit (.u64 (BitVec.ofNat 64 0)))) ρ =
          .ok (.b true) := by
        have h1 := evalExpr_var_hit ρ "top" (.u64 top) htop
        have h2 : evalExpr (.lit (.u64 (BitVec.ofNat 64 0))) ρ =
            .ok (.u64 (BitVec.ofNat 64 0)) := evalExpr_lit _ _
        have h3 := evalExpr_une_u64 _ _ _ _ _ h1 h2
        rw [htop0] at h3
        exact h3
      -- Decrement `top`.
      have htopDecE : evalExpr (.usub (.var "top")
          (.lit (.u64 (BitVec.ofNat 64 1)))) ρ =
          .ok (.u64 (top - 1)) :=
        evalExpr_usub_u64_rr _ _ _ _ _
          (evalExpr_var_hit ρ "top" (.u64 top) htop)
          (evalExpr_lit _ _)
      obtain ⟨ρT1, hupT1⟩ := envUpdate_some_of_lookup ρ "top"
        (.u64 top) (.u64 (top - 1)) htop
      have htopDecA : evalProgStmt vecGrowProg F
          (.assign "top" (.usub (.var "top")
            (.lit (.u64 (BitVec.ofNat 64 1))))) ρ =
          .ok (ρT1, .fellThrough) := by
        have hfb : evalProgStmt vecGrowProg F
            (.assign "top" (.usub (.var "top")
              (.lit (.u64 (BitVec.ofNat 64 1))))) ρ =
            evalStmtFuel F
              (.assign "top" (.usub (.var "top")
                (.lit (.u64 (BitVec.ofNat 64 1))))) ρ := by
          simp only [evalProgStmt]
        rw [hfb]
        exact evalStmtFuel_assign _ _ _ _ _ _ htopDecE hupT1
      have htopT1 : envLookup ρT1 "top" = some (.u64 (top - 1)) :=
        envLookup_update_hit ρ "top" _ ρT1 hupT1
      -- Guard facts in `ρT1`.
      have hmT1 : envLookup ρT1 "m" =
          some (.stdVecOwned ⟨mL, false⟩ mL.length mL.length) :=
        (envLookup_update_miss ρ "m" "top" (.u64 (top - 1)) ρT1
          (by decide) hupT1).trans hm
      have hnT1 : envLookup ρT1 "n" = some (.u64 n) :=
        (envLookup_update_miss ρ "n" "top" (.u64 (top - 1)) ρT1
          (by decide) hupT1).trans hn
      have hvT1 : envLookup ρT1 "v" = some (.u64 v) :=
        (envLookup_update_miss ρ "v" "top" (.u64 (top - 1)) ρT1
          (by decide) hupT1).trans hv
      have huT1 : envLookup ρT1 "u" = some (.u64 u) :=
        (envLookup_update_miss ρ "u" "top" (.u64 (top - 1)) ρT1
          (by decide) hupT1).trans hu
      have hvisT1 : envLookup ρT1 "vis" =
          some (.stdVecOwned ⟨visL, false⟩
            visL.length visL.length) :=
        (envLookup_update_miss ρ "vis" "top" (.u64 (top - 1)) ρT1
          (by decide) hupT1).trans hvis
      have hcountT1 : envLookup ρT1 "count" = some (.u64 count) :=
        (envLookup_update_miss ρ "count" "top" (.u64 (top - 1)) ρT1
          (by decide) hupT1).trans hcount
      have hstT1 : envLookup ρT1 "st" =
          some (.stdVecOwned b len cap) :=
        (envLookup_update_miss ρ "st" "top" (.u64 (top - 1)) ρT1
          (by decide) hupT1).trans hst
      have hstLen : evalExpr (.vgrowLen "st") ρT1 =
          .ok (.u64 (BitVec.ofNat 64 len)) :=
        evalExpr_vgrowLen_some "st" ρT1 b len cap hstT1
      have hgTop : evalExpr (.ult (.var "top")
          (.vgrowLen "st")) ρT1 =
          .ok (.b ((top - 1).ult (BitVec.ofNat 64 len))) :=
        evalExpr_ult_u64 _ _ _ _ _
          (evalExpr_var_hit ρT1 "top" (.u64 (top - 1)) htopT1)
          hstLen
      have hult_of : (top - 1).ult (BitVec.ofNat 64 len) = true →
          (top - 1).toNat < len := by
        intro h
        have hml : (BitVec.ofNat 64 len).toNat = len := by
          rw [BitVec.toNat_ofNat]
          exact Nat.mod_eq_of_lt hlen64
        rw [BitVec.ult_eq_decide, decide_eq_true_eq, hml] at h
        exact h
      by_cases hB : (top - 1).ult (BitVec.ofNat 64 len) = true
      · rw [hB] at hgTop
        simp only [hB, ↓reduceIte] at herr
        cases hgetS : b.val[(top - 1).toNat]? with
        | none =>
          simp only [hgetS, ↓reduceIte] at herr
          -- Vacuous: the `ult` guard gives `(top - 1).toNat < len ≤
          -- words`, so `get?` must hit.
          have hsome := List.getElem?_eq_getElem
            (Nat.lt_of_lt_of_le (hult_of hB) hlen)
          rw [hsome] at hgetS
          cases hgetS
        | some w =>
          simp only [hgetS, ↓reduceIte] at herr
          by_cases hltS : (top - 1).toNat < len
          · simp only [hltS, ↓reduceIte] at herr
            -- Pop read plus widening.
            have hrd : evalExpr (.vgrowAt "st" (.var "top")) ρT1 =
                .ok (.i32 w) :=
              evalExpr_vgrowAt_some "st" _ ρT1 b len cap (top - 1) w
                hstT1
                (evalExpr_var_hit ρT1 "top" (.u64 (top - 1)) htopT1)
                hlive hgetS hltS
            have hwide : evalExpr
                (.u64ofI32 (.vgrowAt "st" (.var "top"))) ρT1 =
                .ok (.u64 (w.signExtend 64)) :=
              evalExpr_u64ofI32_ok _ _ _ hrd
            obtain ⟨ρV2, hupV2⟩ := envUpdate_some_of_lookup ρT1 "v"
              (.u64 v) (.u64 (w.signExtend 64)) hvT1
            have hVA : evalProgStmt vecGrowProg F
                (.assign "v"
                  (.u64ofI32 (.vgrowAt "st" (.var "top")))) ρT1 =
                .ok (ρV2, .fellThrough) := by
              have hfb : evalProgStmt vecGrowProg F
                  (.assign "v"
                    (.u64ofI32 (.vgrowAt "st" (.var "top")))) ρT1 =
                  evalStmtFuel F
                    (.assign "v"
                      (.u64ofI32
                        (.vgrowAt "st" (.var "top")))) ρT1 := by
                simp only [evalProgStmt]
              rw [hfb]
              exact evalStmtFuel_assign _ _ _ _ _ _ hwide hupV2
            have hvV2 : envLookup ρV2 "v" =
                some (.u64 (w.signExtend 64)) :=
              envLookup_update_hit ρT1 "v" _ ρV2 hupV2
            -- `u := 0`.
            have huV2 : envLookup ρV2 "u" = some (.u64 u) :=
              (envLookup_update_miss ρT1 "u" "v"
                (.u64 (w.signExtend 64)) ρV2 (by decide)
                hupV2).trans
                ((envLookup_update_miss ρ "u" "top"
                  (.u64 (top - 1)) ρT1 (by decide) hupT1).trans hu)
            have hu0E : evalExpr
                (.lit (.u64 (BitVec.ofNat 64 0))) ρV2 =
                .ok (.u64 (BitVec.ofNat 64 0)) := evalExpr_lit _ _
            obtain ⟨ρU0, hupU0⟩ := envUpdate_some_of_lookup ρV2 "u"
              (.u64 u) (.u64 (BitVec.ofNat 64 0)) huV2
            have hUA0 : evalProgStmt vecGrowProg F
                (.assign "u"
                  (.lit (.u64 (BitVec.ofNat 64 0)))) ρV2 =
                .ok (ρU0, .fellThrough) := by
              have hfb : evalProgStmt vecGrowProg F
                  (.assign "u"
                    (.lit (.u64 (BitVec.ofNat 64 0)))) ρV2 =
                  evalStmtFuel F
                    (.assign "u"
                      (.lit (.u64 (BitVec.ofNat 64 0)))) ρV2 := by
                simp only [evalProgStmt]
              rw [hfb]
              exact evalStmtFuel_assign _ _ _ _ _ _ hu0E hupU0
            have huU0 : envLookup ρU0 "u" =
                some (.u64 (BitVec.ofNat 64 0)) :=
              envLookup_update_hit ρV2 "u" _ ρU0 hupU0
            -- Row fuel facts (as in the ok leg).
            have htopge1 : 1 ≤ top.toNat := by
              have htopne : top ≠ BitVec.ofNat 64 0 := by
                intro hcon
                rw [hcon, bne_self_eq_false] at htop0
                exact Bool.false_ne_true htop0
              have h0 : (BitVec.ofNat 64 0).toNat = 0 := rfl
              have hz : top.toNat ≠ 0 := by
                intro h
                apply htopne
                apply BitVec.toNat_inj.mp
                rw [h, h0]
              omega
            have hsub1 : (top - 1).toNat = top.toNat - 1 := by
              have h1 : ((1 : BitVec 64)).toNat = 1 := rfl
              have hlt : top.toNat < 2 ^ 64 := BitVec.isLt top
              have hsub : (top - 1).toNat =
                  (2 ^ 64 - (1 : BitVec 64).toNat + top.toNat) %
                    2 ^ 64 :=
                BitVec.toNat_sub _ _
              rw [h1] at hsub
              omega
            have h0u : ((0 : BitVec 64)).toNat = 0 := rfl
            have hProw : L0 + visL.length + 8 +
                (n.toNat - (0 : BitVec 64).toNat) ≤ F := by
              omega
            have htopLeU0 : (top - 1).toNat ≤ len :=
              Nat.le_of_lt hltS
            -- Lookups after the `v`/`u` updates.
            have hmV2 : envLookup ρV2 "m" =
                some (.stdVecOwned ⟨mL, false⟩
                  mL.length mL.length) :=
              (envLookup_update_miss ρT1 "m" "v"
                (.u64 (w.signExtend 64)) ρV2 (by decide)
                hupV2).trans hmT1
            have hmU0 : envLookup ρU0 "m" =
                some (.stdVecOwned ⟨mL, false⟩
                  mL.length mL.length) :=
              (envLookup_update_miss ρV2 "m" "u"
                (.u64 (BitVec.ofNat 64 0)) ρU0 (by decide)
                hupU0).trans hmV2
            have hnV2 : envLookup ρV2 "n" = some (.u64 n) :=
              (envLookup_update_miss ρT1 "n" "v"
                (.u64 (w.signExtend 64)) ρV2 (by decide)
                hupV2).trans hnT1
            have hnU0 : envLookup ρU0 "n" = some (.u64 n) :=
              (envLookup_update_miss ρV2 "n" "u"
                (.u64 (BitVec.ofNat 64 0)) ρU0 (by decide)
                hupU0).trans hnV2
            have hvisV2 : envLookup ρV2 "vis" =
                some (.stdVecOwned ⟨visL, false⟩
                  visL.length visL.length) :=
              (envLookup_update_miss ρT1 "vis" "v"
                (.u64 (w.signExtend 64)) ρV2 (by decide)
                hupV2).trans hvisT1
            have hvisU0 : envLookup ρU0 "vis" =
                some (.stdVecOwned ⟨visL, false⟩
                  visL.length visL.length) :=
              (envLookup_update_miss ρV2 "vis" "u"
                (.u64 (BitVec.ofNat 64 0)) ρU0 (by decide)
                hupU0).trans hvisV2
            have hstV2 : envLookup ρV2 "st" =
                some (.stdVecOwned b len cap) :=
              (envLookup_update_miss ρT1 "st" "v"
                (.u64 (w.signExtend 64)) ρV2 (by decide)
                hupV2).trans hstT1
            have hstU0 : envLookup ρU0 "st" =
                some (.stdVecOwned b len cap) :=
              (envLookup_update_miss ρV2 "st" "u"
                (.u64 (BitVec.ofNat 64 0)) ρU0 (by decide)
                hupU0).trans hstV2
            have htopV2 : envLookup ρV2 "top" =
                some (.u64 (top - 1)) :=
              (envLookup_update_miss ρT1 "top" "v"
                (.u64 (w.signExtend 64)) ρV2 (by decide)
                hupV2).trans htopT1
            have htopU0 : envLookup ρU0 "top" =
                some (.u64 (top - 1)) :=
              (envLookup_update_miss ρV2 "top" "u"
                (.u64 (BitVec.ofNat 64 0)) ρU0 (by decide)
                hupU0).trans htopV2
            have hcountV2 : envLookup ρV2 "count" =
                some (.u64 count) :=
              (envLookup_update_miss ρT1 "count" "v"
                (.u64 (w.signExtend 64)) ρV2 (by decide)
                hupV2).trans hcountT1
            have hcountU0 : envLookup ρU0 "count" =
                some (.u64 count) :=
              (envLookup_update_miss ρV2 "count" "u"
                (.u64 (BitVec.ofNat 64 0)) ρU0 (by decide)
                hupU0).trans hcountV2
            have hvU0 : envLookup ρU0 "v" =
                some (.u64 (w.signExtend 64)) :=
              (envLookup_update_miss ρV2 "v" "u"
                (.u64 (BitVec.ofNat 64 0)) ρU0 (by decide)
                hupU0).trans hvV2
            -- Row scan at predecessor fuel.
            cases hrowC : dfsGrowRowFwd F mL visL b len cap n
                (w.signExtend 64) (top - 1) count 0 with
            | error e1 =>
              simp only [hrowC, ↓reduceIte] at herr
              cases herr
              -- The row errors: thread through the body.
              have hRowErr : evalProgStmt vecGrowProg F
                  dfsGrowInner ρU0 = .error e :=
                dfsGrowRow_err F mL visL b len cap n
                  (w.signExtend 64) (top - 1) count 0 ρU0
                  hmU0 hmen hvisU0 hvislen hstU0 hlive hlen
                  hbuflen hlen64 hcap64 hProw hcnt hmaxL0
                  hnU0 hvU0 htopU0 hcountU0 huU0 e hrowC
              have hRowSeq : evalProgStmt vecGrowProg F
                  (.seq (.assign "u"
                    (.lit (.u64 (BitVec.ofNat 64 0))))
                    dfsGrowInner) ρV2 =
                  .error e :=
                (evalProgStmt_seq_fallthrough vecGrowProg F _ _ _ _
                  hUA0).trans hRowErr
              have hGuardIf : evalProgStmt vecGrowProg F
                  (.if_ (.ult (.var "top") (.vgrowLen "st"))
                    (.assign "v"
                      (.u64ofI32 (.vgrowAt "st" (.var "top"))))
                    .fail) ρT1 =
                  evalProgStmt vecGrowProg F
                    (.assign "v"
                      (.u64ofI32
                        (.vgrowAt "st" (.var "top")))) ρT1 := by
                rw [evalProgStmt_if_true _ _ _ _ _ _ hgTop]
              have hGuardEv : evalProgStmt vecGrowProg F
                  (.if_ (.ult (.var "top") (.vgrowLen "st"))
                    (.assign "v"
                      (.u64ofI32 (.vgrowAt "st" (.var "top"))))
                    .fail) ρT1 =
                  .ok (ρV2, .fellThrough) :=
                hGuardIf.trans hVA
              have hBodyTl : evalProgStmt vecGrowProg F
                  (.seq (.if_ (.ult (.var "top") (.vgrowLen "st"))
                    (.assign "v"
                      (.u64ofI32 (.vgrowAt "st" (.var "top"))))
                    .fail)
                  (.seq (.assign "u"
                    (.lit (.u64 (BitVec.ofNat 64 0))))
                    dfsGrowInner)) ρT1 =
                  .error e :=
                (evalProgStmt_seq_fallthrough vecGrowProg F _ _ _ _
                  hGuardEv).trans hRowSeq
              have hBody : evalProgStmt vecGrowProg F
                  (.seq (.assign "top" (.usub (.var "top")
                    (.lit (.u64 (BitVec.ofNat 64 1)))))
                  (.seq (.if_ (.ult (.var "top") (.vgrowLen "st"))
                    (.assign "v"
                      (.u64ofI32 (.vgrowAt "st" (.var "top"))))
                    .fail)
                  (.seq (.assign "u"
                    (.lit (.u64 (BitVec.ofNat 64 0))))
                    dfsGrowInner))) ρ =
                  .error e :=
                (evalProgStmt_seq_fallthrough vecGrowProg F _ _ _ _
                  htopDecA).trans hBodyTl
              have hev : evalProgStmt vecGrowProg (F + 1)
                  dfsGrowOuter ρ = .error e := by
                simp only [dfsGrowOuter, dfsGrowOuterBody]
                rw [evalProgStmt_while_true _ _ _ _ _ hguardU, hBody]
              exact hev
            | ok t =>
              simp only [hrowC, ↓reduceIte] at herr
              obtain ⟨vr, b2r, l2r, c2r, top2r, count2r, u2r⟩ := t
              have hvrlen : vr.length = visL.length :=
                dfsGrowRowFwd_length F mL visL b len cap n
                  (w.signExtend 64) (top - 1) count 0 vr b2r
                  l2r c2r top2r count2r u2r hrowC
              have hvislenR : vr.length < 2 ^ 64 := hvrlen ▸ hvislen
              have hmaxL0R : L0 + vr.length + n.toNat ≤
                  stdVecMaxDiffBV.toNat - 1 := by
                rw [hvrlen]
                exact hmaxL0
              obtain ⟨ρR, hRowEval, hmR, hvisR, hstR, hnR, hvR,
                  htopR, hcountR, huR, hfrR, hlenR, hbuflenR, h64R,
                  hcapR, hcntR, hmonoR, htopEqR, htopLeR⟩ :=
                dfsGrowRow_ok F mL visL b len cap n
                  (w.signExtend 64) (top - 1) count 0 ρU0 L0
                  hmU0 hmen hvisU0 hvislen hstU0 hlive hlen hbuflen
                  hlen64 hcap64 hProw hLV hcnt htopLeU0 hnU0 hvU0
                  htopU0 hcountU0 huU0
                  vr b2r l2r c2r top2r count2r u2r hrowC
              have hPih : L0 + vr.length + 8 + n.toNat +
                  8 * (top2r.toNat + (vr.length - ones vr)) ≤ F := by
                have honesvr := ones_le_length vr
                omega
              have hLVih : L0 + vr.length + 1 < 2 ^ 64 :=
                hvrlen ▸ hLV
              rw [← hvrlen] at hvisR
              have ihEval :=
                ih vr b2r l2r c2r top2r count2r (w.signExtend 64)
                  u2r ρR hmR hvisR hvislenR hstR hfrR hlenR
                  hbuflenR h64R hcapR hPih hLVih hcntR htopLeR
                  hmaxL0R hnR hvR htopR hcountR huR herr
              -- Body assembly.
              have hGuardIf : evalProgStmt vecGrowProg F
                  (.if_ (.ult (.var "top") (.vgrowLen "st"))
                    (.assign "v"
                      (.u64ofI32 (.vgrowAt "st" (.var "top"))))
                    .fail) ρT1 =
                  evalProgStmt vecGrowProg F
                    (.assign "v"
                      (.u64ofI32
                        (.vgrowAt "st" (.var "top")))) ρT1 := by
                rw [evalProgStmt_if_true _ _ _ _ _ _ hgTop]
              have hGuardEv : evalProgStmt vecGrowProg F
                  (.if_ (.ult (.var "top") (.vgrowLen "st"))
                    (.assign "v"
                      (.u64ofI32 (.vgrowAt "st" (.var "top"))))
                    .fail) ρT1 =
                  .ok (ρV2, .fellThrough) :=
                hGuardIf.trans hVA
              have hRowSeq : evalProgStmt vecGrowProg F
                  (.seq (.assign "u"
                    (.lit (.u64 (BitVec.ofNat 64 0))))
                    dfsGrowInner) ρV2 =
                  .ok (ρR, .fellThrough) :=
                (evalProgStmt_seq_fallthrough vecGrowProg F _ _ _ _
                  hUA0).trans hRowEval
              have hBodyTl : evalProgStmt vecGrowProg F
                  (.seq (.if_ (.ult (.var "top") (.vgrowLen "st"))
                    (.assign "v"
                      (.u64ofI32 (.vgrowAt "st" (.var "top"))))
                    .fail)
                  (.seq (.assign "u"
                    (.lit (.u64 (BitVec.ofNat 64 0))))
                    dfsGrowInner)) ρT1 =
                  .ok (ρR, .fellThrough) :=
                (evalProgStmt_seq_fallthrough vecGrowProg F _ _ _ _
                  hGuardEv).trans hRowSeq
              have hBody : evalProgStmt vecGrowProg F
                  (.seq (.assign "top" (.usub (.var "top")
                    (.lit (.u64 (BitVec.ofNat 64 1)))))
                  (.seq (.if_ (.ult (.var "top") (.vgrowLen "st"))
                    (.assign "v"
                      (.u64ofI32 (.vgrowAt "st" (.var "top"))))
                    .fail)
                  (.seq (.assign "u"
                    (.lit (.u64 (BitVec.ofNat 64 0))))
                    dfsGrowInner))) ρ =
                  .ok (ρR, .fellThrough) :=
                (evalProgStmt_seq_fallthrough vecGrowProg F _ _ _ _
                  htopDecA).trans hBodyTl
              have hev : evalProgStmt vecGrowProg (F + 1)
                  dfsGrowOuter ρ = .error e := by
                simp only [dfsGrowOuter, dfsGrowOuterBody]
                rw [evalProgStmt_while_true _ _ _ _ _ hguardU, hBody]
                exact ihEval
              exact hev
          · -- Vacuous: contradicts the `ult` guard fact.
            exact absurd (hult_of hB) hltS
      · simp only [hB] at herr
        cases herr
        -- Pop guard miss: the `if_` chain fails, then `.fail`.
        have hgTopF : evalExpr (.ult (.var "top")
            (.vgrowLen "st")) ρT1 = .ok (.b false) := by
          have hBF : (top - 1).ult (BitVec.ofNat 64 len) = false :=
            Bool.eq_false_of_ne_true hB
          rw [hBF] at hgTop
          exact hgTop
        have hIf : evalProgStmt vecGrowProg F
            (.if_ (.ult (.var "top") (.vgrowLen "st"))
              (.assign "v"
                (.u64ofI32 (.vgrowAt "st" (.var "top"))))
              .fail) ρT1 =
            evalProgStmt vecGrowProg F .fail ρT1 :=
          evalProgStmt_if_false _ _ _ _ _ _ hgTopF
        have hfail : evalProgStmt vecGrowProg F .fail ρT1 =
            .error .AssertFail := by
          have hfb : evalProgStmt vecGrowProg F .fail ρT1 =
              evalStmtFuel F .fail ρT1 := by
            simp only [evalProgStmt]
          rw [hfb]
          exact evalStmtFuel_fail _ _
        have hBodyTl : evalProgStmt vecGrowProg F
            (.seq (.if_ (.ult (.var "top") (.vgrowLen "st"))
              (.assign "v"
                (.u64ofI32 (.vgrowAt "st" (.var "top"))))
              .fail)
            (.seq (.assign "u"
              (.lit (.u64 (BitVec.ofNat 64 0))))
              dfsGrowInner)) ρT1 = .error .AssertFail :=
          evalProgStmt_seq_err _ _ _ _ _ _
            (hIf.trans hfail)
        have hBody : evalProgStmt vecGrowProg F
            (.seq (.assign "top" (.usub (.var "top")
              (.lit (.u64 (BitVec.ofNat 64 1)))))
            (.seq (.if_ (.ult (.var "top") (.vgrowLen "st"))
              (.assign "v"
                (.u64ofI32 (.vgrowAt "st" (.var "top"))))
              .fail)
            (.seq (.assign "u"
              (.lit (.u64 (BitVec.ofNat 64 0))))
              dfsGrowInner))) ρ =
            .error .AssertFail :=
          (evalProgStmt_seq_fallthrough vecGrowProg F _ _ _ _
            htopDecA).trans hBodyTl
        have hev : evalProgStmt vecGrowProg (F + 1) dfsGrowOuter ρ =
            .error .AssertFail := by
          simp only [dfsGrowOuter, dfsGrowOuterBody]
          rw [evalProgStmt_while_true _ _ _ _ _ hguardU, hBody]
        exact hev

/-- Seed error agreement: the fused entry seed evaluates exactly as
    the seed forward says on the error legs. Straight-line (no loop):
    the guard miss fails before any state change; the push error legs
    step the mark and the `x0` let, then the failing `push_back` call.
    The `hmax` premise (plain `len ≤ maxdiff - 1`, no loop to thread
    through) excludes the over-strict gate case, exactly as in the
    row; `hF` is the same push-fuel premise as the ok leg. Miss arms
    with contradictory case facts close by `getElem?_eq_getElem`; a
    fully-successful push contradicts `herr`, and an owned-shape
    mismatch against a successful push is vacuous. -/
theorem dfsGrowSeed_err (F : Nat) (mL visL : List (BitVec 32))
    (b : Vec32) (len cap : Nat) (n src : BitVec 64) (ρ : Env)
    (hm : envLookup ρ "m" =
      some (.stdVecOwned ⟨mL, false⟩ mL.length mL.length))
    (hmen : mL.length < 2 ^ 64)
    (hvis : envLookup ρ "vis" =
      some (.stdVecOwned ⟨visL, false⟩ visL.length visL.length))
    (hvislen : visL.length < 2 ^ 64)
    (hst : envLookup ρ "st" = some (.stdVecOwned b len cap))
    (hlive : b.freed = false)
    (hlen : len ≤ b.val.length)
    (hbuflen : b.val.length < 2 ^ 64)
    (hlen64 : len < 2 ^ 64)
    (hcap64 : cap < 2 ^ 64)
    (hF : len + 4 ≤ F)
    (hmax : len ≤ stdVecMaxDiffBV.toNat - 1)
    (hn : envLookup ρ "n" = some (.u64 n))
    (hsrc : envLookup ρ "src" = some (.u64 src))
    (e : Panic)
    (herr : dfsGrowSeedFwd F visL b len cap src = .error e) :
    evalProgStmt vecGrowProg F dfsGrowSeed ρ = .error e := by
  simp only [dfsGrowSeed]
  unfold dfsGrowSeedFwd at herr
  have hvl : (BitVec.ofNat 64 visL.length).toNat = visL.length := by
    rw [BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hvislen
  have hguardE : evalExpr (.ult (.var "src") (.vgrowLen "vis")) ρ =
      .ok (.b (src.ult (BitVec.ofNat 64 visL.length))) := by
    have h1 := evalExpr_var_hit ρ "src" (.u64 src) hsrc
    have h2 := evalExpr_vgrowLen_some "vis" ρ ⟨visL, false⟩
      visL.length visL.length hvis
    have h3 := evalExpr_ult_u64 _ _ _ _ _ h1 h2
    exact h3
  have hlt_of : src.ult (BitVec.ofNat 64 visL.length) = true →
      src.toNat < visL.length := by
    intro h
    rw [BitVec.ult_eq_decide, decide_eq_true_eq, hvl] at h
    exact h
  by_cases hg : src.ult (BitVec.ofNat 64 visL.length) = true
  · rw [hg] at hguardE
    simp only [hg] at herr
    cases hget : visL[src.toNat]? with
    | none =>
      simp only [hget, ↓reduceIte] at herr
      -- Vacuous: the `ult` guard gives `src < length`.
      have hsome := List.getElem?_eq_getElem (hlt_of hg)
      rw [hsome] at hget
      cases hget
    | some w =>
      simp only [hget, ↓reduceIte] at herr
      by_cases hltN : src.toNat < visL.length
      · simp only [hltN, ↓reduceIte] at herr
        by_cases hmaxC : len ≤ stdVecMaxDiffBV.toNat - 1
        · simp only [hmaxC, ↓reduceIte] at herr
          -- Push adequacy (as in the ok leg).
          obtain ⟨F', rfl, hF'⟩ : ∃ F', F = F' + 1 ∧
              len + 3 ≤ F' := ⟨F - 1, by omega, by omega⟩
          have hmax' : len ≤ stdVecMaxDiffBV.toNat := by omega
          have hcall := evalProgFunc_stdVecPushBack F' b len
            cap (BitVec.ofNat 32 src.toNat) hlive hmax'
            hlen hbuflen hcap64 hF'
          -- The visited mark.
          have hset : vecSet ⟨visL, false⟩ src.toNat 1 =
              .ok ⟨visL.set src.toNat 1, false⟩ := by
            unfold vecSet
            simp [hltN]
          obtain ⟨ρ1, hu⟩ := envUpdate_some_of_lookup ρ "vis"
            (.stdVecOwned ⟨visL, false⟩ visL.length visL.length)
            (.stdVecOwned ⟨visL.set src.toNat 1, false⟩
              visL.length visL.length) hvis
          have hmark := evalStmtFuel_vgrowSet (F' + 1)
            "vis" (.var "src") (.lit (.i32 1)) ρ src
            (BitVec.ofNat 32 1) ⟨visL, false⟩
            ⟨visL.set src.toNat 1, false⟩
            visL.length visL.length ρ1
            (evalExpr_var_hit ρ "src" (.u64 src) hsrc) rfl
            hvis hset hu
          have hfbMark : evalProgStmt vecGrowProg (F' + 1)
              (.vgrowSet "vis" (.var "src")
                (.lit (.i32 1))) ρ =
              evalStmtFuel (F' + 1)
                (.vgrowSet "vis" (.var "src")
                  (.lit (.i32 1))) ρ := by
            simp only [evalProgStmt]
          have hstepMark : evalProgStmt vecGrowProg (F' + 1)
              (.vgrowSet "vis" (.var "src")
                (.lit (.i32 1))) ρ =
              .ok (ρ1, .fellThrough) := by
            rw [hfbMark]
            exact hmark
          have hsrc1 : envLookup ρ1 "src" = some (.u64 src) := by
            have hmiss := envLookup_update_miss ρ "src" "vis"
              (.stdVecOwned ⟨visL.set src.toNat 1, false⟩
                visL.length visL.length) ρ1 (by decide) hu
            rwa [hsrc] at hmiss
          have hx0eval : evalExpr (.i32ofU64 (.var "src")) ρ1 =
              .ok (.i32 (BitVec.ofNat 32 src.toNat)) :=
            evalExpr_i32ofU64_ok _ _ _
              (evalExpr_var_hit ρ1 "src" (.u64 src) hsrc1)
          have hstepX0 := evalProgStmt_let_fb vecGrowProg (F' + 1)
            "x0" (.i 32) (.i32ofU64 (.var "src")) ρ1
          have hletX0 : evalStmtFuel (F' + 1)
              (.let_ "x0" (.i 32) (.i32ofU64 (.var "src")))
              ρ1 =
              .ok (envExtend ρ1 "x0"
                (.i32 (BitVec.ofNat 32 src.toNat)),
                .fellThrough) :=
            evalStmtFuel_let_ _ "x0" (.i 32)
              (.i32ofU64 (.var "src")) ρ1 _ hx0eval
          have hstepX0' : evalProgStmt vecGrowProg (F' + 1)
              (.let_ "x0" (.i 32) (.i32ofU64 (.var "src")))
              ρ1 =
              .ok (envExtend ρ1 "x0"
                (.i32 (BitVec.ofNat 32 src.toNat)),
                .fellThrough) := by
            rw [evalProgStmt_let_fb]
            exact hletX0
          have hargs : lookupArgs
              (envExtend ρ1 "x0"
                (.i32 (BitVec.ofNat 32 src.toNat)))
              ["st", "x0"] = some [.stdVecOwned b len cap,
                .i32 (BitVec.ofNat 32 src.toNat)] := by
            have hst2 : envLookup
                (envExtend ρ1 "x0"
                  (.i32 (BitVec.ofNat 32 src.toNat))) "st" =
                some (.stdVecOwned b len cap) := by
              simp only [envLookup, envExtend,
                show ("st" : String) ≠ "x0" by decide]
              have hmiss := envLookup_update_miss ρ "st" "vis"
                (.stdVecOwned ⟨visL.set src.toNat 1, false⟩
                  visL.length visL.length) ρ1 (by decide) hu
              rwa [hst] at hmiss
            have hx02 : envLookup
                (envExtend ρ1 "x0"
                  (.i32 (BitVec.ofNat 32 src.toNat))) "x0" =
                some (.i32 (BitVec.ofNat 32 src.toNat)) := by
              simp [envLookup, envExtend]
            exact lookupArgs_cons_hit _ "st"
              (.stdVecOwned b len cap) ["x0"]
              [.i32 (BitVec.ofNat 32 src.toNat)] hst2
              (lookupArgs_cons_hit _ "x0"
                (.i32 (BitVec.ofNat 32 src.toNat)) [] [] hx02
                (lookupArgs_nil _))
          cases hpush : stdVecPushBackFwd b len cap
              (BitVec.ofNat 32 src.toNat) with
          | error e1 =>
            simp only [hpush, vecGrow_bind_err] at herr
            cases herr
            rw [hpush] at hcall
            -- The failing `push_back` call.
            have hstepPushE : evalProgStmt vecGrowProg (F' + 1)
                (.callProg "st" stdVecPushBackName
                  ["st", "x0"])
                (envExtend ρ1 "x0"
                  (.i32 (BitVec.ofNat 32 src.toNat))) =
                .error e :=
              evalProgStmt_callProg_err vecGrowProg F'
                "st" stdVecPushBackName ["st", "x0"]
                (envExtend ρ1 "x0"
                  (.i32 (BitVec.ofNat 32 src.toNat)))
                [.stdVecOwned b len cap,
                  .i32 (BitVec.ofNat 32 src.toNat)]
                stdVecPushBackFunc e hargs
                findFunc_stdVecPushBack hcall
            have hIf : evalProgStmt vecGrowProg (F' + 1)
                (.if_ (.ult (.var "src") (.vgrowLen "vis"))
                  (.vgrowSet "vis" (.var "src")
                    (.lit (.i32 1)))
                  .fail) ρ =
                evalProgStmt vecGrowProg (F' + 1)
                  (.vgrowSet "vis" (.var "src")
                    (.lit (.i32 1))) ρ :=
              evalProgStmt_if_true _ _ _ _ _ _ hguardE
            have hFirst : evalProgStmt vecGrowProg (F' + 1)
                dfsGrowSeed ρ =
                .error e := by
              simp only [dfsGrowSeed]
              exact (evalProgStmt_seq_fallthrough vecGrowProg
                _ _ _ _ _ (hIf.trans hstepMark)).trans
                ((evalProgStmt_seq_fallthrough vecGrowProg
                  _ _ _ _ _ hstepX0').trans
                  (evalProgStmt_seq_err _ _ _ _ _ _ hstepPushE))
            exact hFirst
          | ok pv =>
            simp only [hpush, vecGrow_bind_ok] at herr
            cases hown : vecGrowOwned pv with
            | error e2 =>
              simp only [hown, vecGrow_bind_err] at herr
              -- Vacuous: a successful push always yields an owned
              -- triple, so `vecGrowOwned` on it cannot fail.
              have hshape := stdVecPushBackFwd_ok b len
                cap (BitVec.ofNat 32 src.toNat) pv hlive
                hlen hbuflen hlen64 hcap64 hmaxC hpush
              obtain ⟨b2, l2, c2, hv2, -, -, -, -, -, -⟩ := hshape
              rw [hv2] at hown
              simp only [vecGrowOwned] at hown
              cases hown
            | ok t =>
              simp only [hown, vecGrow_bind_ok] at herr
              cases herr
        · -- Excluded by the maxdiff budget.
          exact absurd hmax hmaxC
      · -- Vacuous: contradicts the `ult` guard fact.
        exact absurd (hlt_of hg) hltN
  · have hgF : src.ult (BitVec.ofNat 64 visL.length) = false :=
      Bool.eq_false_of_ne_true hg
    rw [hgF] at hguardE
    simp only [hg] at herr
    cases herr
    -- Guard miss: the `if_` fails, then `.fail`.
    have hIf : evalProgStmt vecGrowProg F
        (.if_ (.ult (.var "src") (.vgrowLen "vis"))
          (.vgrowSet "vis" (.var "src")
            (.lit (.i32 1)))
          .fail) ρ =
        evalProgStmt vecGrowProg F .fail ρ :=
      evalProgStmt_if_false _ _ _ _ _ _ hguardE
    have hfail : evalProgStmt vecGrowProg F .fail ρ =
        .error .AssertFail := by
      have hfb : evalProgStmt vecGrowProg F .fail ρ =
          evalStmtFuel F .fail ρ := by
        simp only [evalProgStmt]
      rw [hfb]
      exact evalStmtFuel_fail _ _
    have hBody : evalProgStmt vecGrowProg F
        dfsGrowSeed ρ = .error .AssertFail := by
      simp only [dfsGrowSeed]
      exact evalProgStmt_seq_err _ _ _ _ _ _
        (hIf.trans hfail)
    exact hBody

/-- Entry agreement: the fused `dfs_grow` program evaluates exactly as
    the entry forward says. Seed then drain, threading the row/drain
    lockstep. `L0` is the initial `len`; the fuel premise `hPout` and
    the length/maxdiff budgets are stated on the initial state and
    transported across the seed (which only marks one bit). The
    maxdiff budget excludes the over-strict gate case, exactly as in
    the row/outer legs; executions past `2^61` pushes are outside the
    proven scope (the fuzzer pins the native side). -/
theorem evalProgFunc_dfsGrow (F : Nat) (mL visL : List (BitVec 32))
    (b : Vec32) (len cap : Nat) (n src : BitVec 64)
    (hmen : mL.length < 2 ^ 64)
    (hvislen : visL.length < 2 ^ 64)
    (hlive : b.freed = false)
    (hlen : len ≤ b.val.length)
    (hbuflen : b.val.length < 2 ^ 64)
    (hlen64 : len < 2 ^ 64)
    (hcap64 : cap < 2 ^ 64)
    (hvis0 : visL[src.toNat]? = some (0 : BitVec 32))
    (hFseed : len + 4 ≤ F)
    (hPout : len + visL.length + 8 + n.toNat +
      8 * (1 + (visL.length - ones visL)) ≤ F)
    (hLV : len + visL.length + 1 < 2 ^ 64)
    (hmaxL0 : len + visL.length + n.toNat ≤
      stdVecMaxDiffBV.toNat - 1) :
    evalProgFunc vecGrowProg F dfsGrowFunc
      [.stdVecOwned ⟨mL, false⟩ mL.length mL.length,
       .stdVecOwned ⟨visL, false⟩ visL.length visL.length,
       .stdVecOwned b len cap, .u64 n, .u64 src] =
      dfsGrowFwd F mL visL b len cap n src := by
  have hbind : bindArgs dfsGrowFunc.args
      [.stdVecOwned ⟨mL, false⟩ mL.length mL.length,
       .stdVecOwned ⟨visL, false⟩ visL.length visL.length,
       .stdVecOwned b len cap, .u64 n, .u64 src] =
      some [("m", .stdVecOwned ⟨mL, false⟩ mL.length mL.length),
        ("vis", .stdVecOwned ⟨visL, false⟩
          visL.length visL.length),
        ("st", .stdVecOwned b len cap), ("n", .u64 n),
        ("src", .u64 src)] := rfl
  have hbody : dfsGrowFunc.body =
      (.seq dfsGrowSeed
        (.seq dfsGrowOuter (.return_ (.var "count")))) := rfl
  -- Seed-env lookups.
  have hmS0 : envLookup
        [("m", .stdVecOwned ⟨mL, false⟩ mL.length mL.length),
        ("vis", .stdVecOwned ⟨visL, false⟩
          visL.length visL.length),
        ("st", .stdVecOwned b len cap), ("n", .u64 n),
        ("src", .u64 src)] "m" =
      some (.stdVecOwned ⟨mL, false⟩ mL.length mL.length) := by
    simp [envLookup]
  have hvisS0 : envLookup
        [("m", .stdVecOwned ⟨mL, false⟩ mL.length mL.length),
        ("vis", .stdVecOwned ⟨visL, false⟩
          visL.length visL.length),
        ("st", .stdVecOwned b len cap), ("n", .u64 n),
        ("src", .u64 src)] "vis" =
      some (.stdVecOwned ⟨visL, false⟩
        visL.length visL.length) := by
    simp [envLookup]
  have hstS0 : envLookup
        [("m", .stdVecOwned ⟨mL, false⟩ mL.length mL.length),
        ("vis", .stdVecOwned ⟨visL, false⟩
          visL.length visL.length),
        ("st", .stdVecOwned b len cap), ("n", .u64 n),
        ("src", .u64 src)] "st" =
      some (.stdVecOwned b len cap) := by
    simp [envLookup]
  have hnS0 : envLookup
        [("m", .stdVecOwned ⟨mL, false⟩ mL.length mL.length),
        ("vis", .stdVecOwned ⟨visL, false⟩
          visL.length visL.length),
        ("st", .stdVecOwned b len cap), ("n", .u64 n),
        ("src", .u64 src)] "n" =
      some (.u64 n) := by
    simp [envLookup]
  have hsrcS0 : envLookup
        [("m", .stdVecOwned ⟨mL, false⟩ mL.length mL.length),
        ("vis", .stdVecOwned ⟨visL, false⟩
          visL.length visL.length),
        ("st", .stdVecOwned b len cap), ("n", .u64 n),
        ("src", .u64 src)] "src" =
      some (.u64 src) := by
    simp [envLookup]
  have hmax : len ≤ stdVecMaxDiffBV.toNat - 1 := by omega
  match hseed : dfsGrowSeedFwd F visL b len cap src with
  | .error e =>
    have hseedE := dfsGrowSeed_err F mL visL b len cap n src _
      hmS0 hmen hvisS0 hvislen hstS0 hlive hlen hbuflen hlen64
      hcap64 hFseed hmax hnS0 hsrcS0 _ hseed
    have hstmt : evalProgStmt vecGrowProg F dfsGrowFunc.body
        [("m", .stdVecOwned ⟨mL, false⟩ mL.length mL.length),
        ("vis", .stdVecOwned ⟨visL, false⟩
          visL.length visL.length),
        ("st", .stdVecOwned b len cap), ("n", .u64 n),
        ("src", .u64 src)] =
        .error e := by
      rw [hbody]
      exact evalProgStmt_seq_err _ _ _ _ _ _ hseedE
    simp only [evalProgFunc, hbind, hstmt, dfsGrowFwd, hseed]
  | .ok (vis1, b1, l1, c1) =>
    have hseedO := dfsGrowSeed_ok F mL visL b len cap n src _
      hmS0 hmen hvisS0 hvislen hstS0 hlive hlen hbuflen hlen64
      hcap64 hFseed hnS0 hsrcS0 hvis0 vis1 b1 l1 c1 hseed
    obtain ⟨ρS, hSeedEval, hmS, hvisS, hstS, hnS, hsrcS, htopS,
        hcountS, hvS, huS, hfrS, hlenS, hbuflenS, h64S, hcapS,
        hl1, hones1, hcnt1, h1l1⟩ := hseedO
    -- The seed marks exactly one bit: length preserved.
    have hltN : src.toNat < visL.length := by
      cases h : Nat.lt_or_ge src.toNat visL.length with
      | inl hlt => exact hlt
      | inr hge =>
        have hnone := List.getElem?_eq_none hge (l := visL)
        rw [hnone] at hvis0
        cases hvis0
    have hvl : (BitVec.ofNat 64 visL.length).toNat = visL.length := by
      rw [BitVec.toNat_ofNat]
      exact Nat.mod_eq_of_lt hvislen
    have hgS : src.ult (BitVec.ofNat 64 visL.length) = true := by
      rw [BitVec.ult_eq_decide, decide_eq_true_eq, hvl]
      exact hltN
    have hmaxC' : len ≤ stdVecMaxDiffBV.toNat - 1 := by omega
    have hvis1len : vis1.length = visL.length := by
      simp only [dfsGrowSeedFwd, hgS, hvis0, hltN, hmaxC',
        ↓reduceIte] at hseed
      cases hpushS : stdVecPushBackFwd b len cap
          (BitVec.ofNat 32 src.toNat) with
      | error e1 =>
        simp only [hpushS, vecGrow_bind_err] at hseed
        cases hseed
      | ok pv =>
        simp only [hpushS, vecGrow_bind_ok] at hseed
        cases hownS : vecGrowOwned pv with
        | error e2 =>
          simp only [hownS, vecGrow_bind_err] at hseed
          have hshape := stdVecPushBackFwd_ok b len cap
            (BitVec.ofNat 32 src.toNat) pv hlive hlen hbuflen
            hlen64 hcap64 hmaxC' hpushS
          obtain ⟨b2, l2, c2, hv2, -, -, -, -, -, -⟩ := hshape
          rw [hv2] at hownS
          simp only [vecGrowOwned] at hownS
          cases hownS
        | ok t =>
          simp only [hownS, vecGrow_bind_ok, Except.ok.injEq,
            Prod.mk.injEq] at hseed
          have hvis1set : vis1 = visL.set src.toNat 1 :=
            hseed.1.symm
          rw [hvis1set]
          simp
    have hvislen1 : vis1.length < 2 ^ 64 := by
      rw [hvis1len]
      exact hvislen
    -- Budget transport across the seed (length preserved; the
    -- potential can only shrink as `ones` grows).
    have honesLe := ones_le_length vis1
    have hPout' : len + vis1.length + 8 + n.toNat +
        8 * (1 + (vis1.length - ones vis1)) ≤ F := by
      rw [hvis1len]
      have h1o := ones_le_length visL
      omega
    have hLV' : len + vis1.length + 1 < 2 ^ 64 := by
      rw [hvis1len]
      exact hLV
    have hmaxL0' : len + vis1.length + n.toNat ≤
        stdVecMaxDiffBV.toNat - 1 := by
      rw [hvis1len]
      exact hmaxL0
    have hvisS' : envLookup ρS "vis" =
        some (.stdVecOwned ⟨vis1, false⟩
          vis1.length vis1.length) := by
      rw [hvis1len]
      exact hvisS
    have h1 : ((1 : BitVec 64)).toNat = 1 := rfl
    have htopLe : (1 : BitVec 64).toNat ≤ l1 := by
      rw [h1]
      exact h1l1
    cases houter : dfsGrowOuterFwd F mL vis1 b1 l1 c1 n 1 1 0 0 with
    | error e =>
      have houterE := dfsGrowOuter_err F mL vis1 b1 l1 c1 n 1 1 0 0
        ρS len hmS hmen hvisS' hvislen1 hstS hfrS hlenS hbuflenS
        h64S hcapS hPout' hLV' hcnt1 htopLe hmaxL0' hnS hvS htopS
        hcountS huS _ houter
      have hstmt : evalProgStmt vecGrowProg F dfsGrowFunc.body
        [("m", .stdVecOwned ⟨mL, false⟩ mL.length mL.length),
        ("vis", .stdVecOwned ⟨visL, false⟩
          visL.length visL.length),
        ("st", .stdVecOwned b len cap), ("n", .u64 n),
        ("src", .u64 src)] =
          .error e := by
        rw [hbody]
        exact (evalProgStmt_seq_fallthrough vecGrowProg F _ _ _ _
          hSeedEval).trans
          (evalProgStmt_seq_err _ _ _ _ _ _ houterE)
      simp only [evalProgFunc, hbind, hstmt, dfsGrowFwd, hseed,
        houter]
    | ok t =>
      obtain ⟨vis2, b2, l2, c2, top2, count2, v2, u2⟩ := t
      have houterO := dfsGrowOuter_ok F mL vis1 b1 l1 c1 n 1 1 0 0
        ρS len hmS hmen hvisS' hvislen1 hstS hfrS hlenS hbuflenS
        h64S hcapS hPout' hLV' hcnt1 htopLe hnS hvS htopS
        hcountS huS _ _ _ _ _ _ _ _ houter
      obtain ⟨ρ', hOuterEval, ihM, ihVis, ihSt, ihN, ihV, ihTop,
          ihCount, ihU, ihFr, ihLe, ihBuflen, ih64, ihCap,
          ihCnt, ihMono, ihTopLe⟩ := houterO
      have hcountR : evalExpr (.var "count") ρ' =
          .ok (.u64 count2) :=
        evalExpr_var_hit _ _ _ ihCount
      have hret := evalProgStmt_return vecGrowProg F _ ρ' _ hcountR
      have hstmt : evalProgStmt vecGrowProg F dfsGrowFunc.body
        [("m", .stdVecOwned ⟨mL, false⟩ mL.length mL.length),
        ("vis", .stdVecOwned ⟨visL, false⟩
          visL.length visL.length),
        ("st", .stdVecOwned b len cap), ("n", .u64 n),
        ("src", .u64 src)] =
          .ok (ρ', .returned (.u64 count2)) := by
        rw [hbody]
        exact (evalProgStmt_seq_fallthrough vecGrowProg F _ _ _ _
          hSeedEval).trans
          ((evalProgStmt_seq_fallthrough vecGrowProg F _ _ _ _
            hOuterEval).trans hret)
      simp only [evalProgFunc, hbind, hstmt, dfsGrowFwd, hseed,
        houter]
