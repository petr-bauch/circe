-- Generated spec stub by the Circe emitter (S4) from validated CoreIR.
-- Unverified scaffolding: copy into `Circe.Specs` (or a per-project spec
-- file) and fill the equation. The `_fwd` mirror below is body-identical
-- to the emitted forward (same library op); specs proved against it
-- transfer verbatim by body identity (see docs/VERIFYING.md).

import Circe.Base

def _Z9bfs_orderRKSt6vectorIiSaIiEERS1_S4_S4_mm_spec_seed (vis q : List (BitVec 32)) (src : BitVec 64) :
    Result (List (BitVec 32) × List (BitVec 32)) :=
  match vis[src.toNat]? with
  | none => .error .AssertFail
  | some _ =>
    match q[(BitVec.ofNat 64 0).toNat]? with
    | none => .error .AssertFail
    | some _ =>
      .ok (vis.set src.toNat 1,
        q.set 0 (BitVec.ofNat 32 src.toNat))

def _Z9bfs_orderRKSt6vectorIiSaIiEERS1_S4_S4_mm_spec_row (F : Nat) (m vis q : List (BitVec 32))
    (n v tail count u : BitVec 64) :
    Result (List (BitVec 32) × List (BitVec 32) × BitVec 64 × BitVec 64 × BitVec 64) :=
  match F with
  | 0 =>
    if u.ult n then .error .AssertFail
    else .ok (vis, q, tail, count, u)
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
              match q[tail.toNat]? with
              | none => .error .AssertFail
              | some _ =>
                _Z9bfs_orderRKSt6vectorIiSaIiEERS1_S4_S4_mm_spec_row F m (vis.set u.toNat 1)
                  (q.set tail.toNat (BitVec.ofNat 32 u.toNat))
                  n v (tail + 1) (count + 1) (u + 1)
            else _Z9bfs_orderRKSt6vectorIiSaIiEERS1_S4_S4_mm_spec_row F m vis q n v tail count (u + 1)
        else _Z9bfs_orderRKSt6vectorIiSaIiEERS1_S4_S4_mm_spec_row F m vis q n v tail count (u + 1)
    else .ok (vis, q, tail, count, u)

def _Z9bfs_orderRKSt6vectorIiSaIiEERS1_S4_S4_mm_spec_drain (F : Nat) (m vis q order : List (BitVec 32))
    (n head tail count v u : BitVec 64) :
    Result (List (BitVec 32) × List (BitVec 32) × List (BitVec 32) × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64 × BitVec 64) :=
  match F with
  | 0 =>
    if head != tail then .error .AssertFail
    else .ok (vis, q, order, head, tail, count, v, u)



  | F + 1 =>
    if head != tail then
      match q[head.toNat]? with
      | none => .error .AssertFail
      | some w =>
        match order[head.toNat]? with
        | none => .error .AssertFail
        | some _ =>
          match _Z9bfs_orderRKSt6vectorIiSaIiEERS1_S4_S4_mm_spec_row F m vis q n (w.signExtend 64) tail count 0 with
        | .error e => .error e
        | .ok (vis', q', tail', count', u') =>
          _Z9bfs_orderRKSt6vectorIiSaIiEERS1_S4_S4_mm_spec_drain F m vis' q' (order.set head.toNat w)
            n (head + 1) tail' count' (w.signExtend 64) u'
    else .ok (vis, q, order, head, tail, count, v, u)
/-- C++ signature: `{name}(m, vis, q, order, n, src)` returns the reachable count from `src` and records the visit order in `order` (iterative BFS over the flat row-major matrix).
    Base body reference: the seed plus the queue drain and the row scan over the reified words (cf. emitted `_Z9bfs_orderRKSt6vectorIiSaIiEERS1_S4_S4_mm_fwd`,
    `bfsFwd` for the entry leg). Seed, queue, order, and matrix misses abort like `at()`-throw. -/
def _Z9bfs_orderRKSt6vectorIiSaIiEERS1_S4_S4_mm_spec_fwd (F : Nat) (m vis q order : List (BitVec 32)) (n src : BitVec 64) : Result (List (BitVec 32) × BitVec 64) :=
  match _Z9bfs_orderRKSt6vectorIiSaIiEERS1_S4_S4_mm_spec_seed vis q src with
  | .error e => .error e
  | .ok (vis1, q1) =>
    match _Z9bfs_orderRKSt6vectorIiSaIiEERS1_S4_S4_mm_spec_drain F m vis1 q1 order n 0 1 1 0 0 with
    | .error e => .error e
    | .ok (_, _, order', _, _, count, _, _) => .ok (order', count)

/-- Edge cases: diamond visits 0,1,2,3 with count 4; line-3 visits 0,1,2; disconnected-from-1 visits just 1; self-loop visits 0; source out of range; empty queue. -/
def _Z9bfs_orderRKSt6vectorIiSaIiEERS1_S4_S4_mm_spec_edges : List (((Nat × List (BitVec 32) × List (BitVec 32) × List (BitVec 32) × List (BitVec 32) × BitVec 64 × BitVec 64)) × Result (List (BitVec 32) × BitVec 64)) :=
  [((100, [0, 1, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], 4, 0), .ok ([0, 1, 2, 3], 4)),
   ((100, [0, 1, 0, 0, 0, 1, 0, 0, 0], [0, 0, 0], [0, 0, 0], [0, 0, 0], 3, 0), .ok ([0, 1, 2], 3)),
   ((100, [0, 0, 0, 0], [0, 0], [0, 0], [0, 0], 2, 1), .ok ([1, 0], 1)),
   ((100, [1], [0], [0], [0], 1, 0), .ok ([0], 1)),
   ((100, [0, 1, 1, 0], [0, 0], [0, 0], [0, 0], 2, 5), .error .AssertFail),
   ((100, [0, 1, 1, 0], [0, 0], [], [0, 0], 2, 0), .error .AssertFail)]

/-- Prop-test entry: the mirror agrees with ground truth on every edge. -/
def _Z9bfs_orderRKSt6vectorIiSaIiEERS1_S4_S4_mm_spec_check : Bool :=
  _Z9bfs_orderRKSt6vectorIiSaIiEERS1_S4_S4_mm_spec_edges.all fun t =>
    (repr (_Z9bfs_orderRKSt6vectorIiSaIiEERS1_S4_S4_mm_spec_fwd t.1.1 t.1.2.1 t.1.2.2.1 t.1.2.2.2.1 t.1.2.2.2.2.1 t.1.2.2.2.2.2.1 t.1.2.2.2.2.2.2)).pretty == (repr t.2).pretty
