-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

def _Z8dfs_growRKSt6vectorIiSaIiEERS1_S4_mm_spec_seed (vis st : List (BitVec 32)) (src : BitVec 64) :
    Result (List (BitVec 32) × List (BitVec 32)) :=
  match vis[src.toNat]? with
  | none => .error .AssertFail
  | some _ =>
    .ok (vis.set src.toNat 1,
      st ++ [BitVec.ofNat 32 src.toNat])

def _Z8dfs_growRKSt6vectorIiSaIiEERS1_S4_mm_spec_row (F : Nat) (m vis st : List (BitVec 32))
    (n v top count u : BitVec 64) :
    Result (List (BitVec 32) × List (BitVec 32) × BitVec 64 × BitVec 64 × BitVec 64) :=
  match F with
  | 0 =>
    if u.ult n then .error .AssertFail
    else .ok (vis, st, top, count, u)
  | F + 1 =>
    if u.ult n then
      match m[(v * n + u).toNat]? with
      | none => .error .AssertFail
      | some g =>
        if g != (BitVec.ofNat 32 0) then
          match vis[u.toNat]? with
          | none => .error .AssertFail
          | some w =>
            if w == (BitVec.ofNat 32 0) then
              let st' := if top.toNat < st.length then st.set top.toNat (BitVec.ofNat 32 u.toNat) else st ++ [BitVec.ofNat 32 u.toNat]
              _Z8dfs_growRKSt6vectorIiSaIiEERS1_S4_mm_spec_row F m (vis.set u.toNat 1) st'
                  n v (top + 1) (count + 1) (u + 1)
            else _Z8dfs_growRKSt6vectorIiSaIiEERS1_S4_mm_spec_row F m vis st n v top count (u + 1)
        else _Z8dfs_growRKSt6vectorIiSaIiEERS1_S4_mm_spec_row F m vis st n v top count (u + 1)
    else .ok (vis, st, top, count, u)

def _Z8dfs_growRKSt6vectorIiSaIiEERS1_S4_mm_spec_drain (F : Nat) (m vis st : List (BitVec 32))
    (n top count v u : BitVec 64) :
    Result (List (BitVec 32) × List (BitVec 32) × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) :=
  match F with
  | 0 =>
    if top != (BitVec.ofNat 64 0) then .error .AssertFail
    else .ok (vis, st, top, count, v, u)
  | F + 1 =>
    if top != (BitVec.ofNat 64 0) then
      let top1 := top - 1
      match st[top1.toNat]? with
      | none => .error .AssertFail
      | some w =>
        match _Z8dfs_growRKSt6vectorIiSaIiEERS1_S4_mm_spec_row F m vis st n (w.signExtend 64) top1 count 0 with
        | .error e => .error e
        | .ok (vis', st', top', count', u') =>
          _Z8dfs_growRKSt6vectorIiSaIiEERS1_S4_mm_spec_drain F m vis' st' n top' count' (w.signExtend 64) u'
    else .ok (vis, st, top, count, v, u)
/-- C++ signature: `_Z8dfs_growRKSt6vectorIiSaIiEERS1_S4_mm(m, vis, st, n, src)` returns the reachable count from `src` (iterative DFS over the flat row-major matrix, caller-grown stack).
    Base body reference: the seed plus the stack drain and the row scan over the reified words (cf. emitted `_Z8dfs_growRKSt6vectorIiSaIiEERS1_S4_mm_fwd`,
    `dfsGrowFwd` for the entry leg). Seed, stack, and matrix misses abort like `at()`-throw. -/
def _Z8dfs_growRKSt6vectorIiSaIiEERS1_S4_mm_spec_fwd (F : Nat) (m vis st : List (BitVec 32)) (n src : BitVec 64) : Result (BitVec 64) :=
  match _Z8dfs_growRKSt6vectorIiSaIiEERS1_S4_mm_spec_seed vis st src with
  | .error e => .error e
  | .ok (vis1, st1) =>
    match _Z8dfs_growRKSt6vectorIiSaIiEERS1_S4_mm_spec_drain F m vis1 st1 n 1 1 0 0 with
    | .error e => .error e
    | .ok (_, _, _, count, _, _) => .ok count

/-- Edge cases: line-2 reaches both, source out of range, disconnected, self-loop, line-3, chain. -/
def _Z8dfs_growRKSt6vectorIiSaIiEERS1_S4_mm_spec_edges : List (((Nat × List (BitVec 32) × List (BitVec 32) × List (BitVec 32) × BitVec 64 × BitVec 64)) × Result (BitVec 64)) :=
  [((100, [0, 1, 1, 0], [0, 0], [], 2, 0), .ok 2),
   ((100, [0, 1, 1, 0], [0, 0], [], 2, 5), .error .AssertFail),
   ((100, [0, 0, 0, 0], [0, 0], [], 2, 0), .ok 1),
   ((100, [1], [0], [], 1, 0), .ok 1),
   ((100, [0, 1, 1, 1, 0, 0, 0, 0, 0], [0, 0, 0], [], 3, 0), .ok 3),
   ((100, [0, 1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0], [], 3, 0), .ok 3)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z8dfs_growRKSt6vectorIiSaIiEERS1_S4_mm_spec_check : Bool :=
  _Z8dfs_growRKSt6vectorIiSaIiEERS1_S4_mm_spec_edges.all fun t =>
    (repr (_Z8dfs_growRKSt6vectorIiSaIiEERS1_S4_mm_spec_fwd t.1.1 t.1.2.1 t.1.2.2.1 t.1.2.2.2.1 t.1.2.2.2.2.1 t.1.2.2.2.2.2)).pretty == (repr t.2).pretty
