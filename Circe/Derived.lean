/-
Circe.Derived — M3b value-level footprints (C only).

`Validator.derivedNoalias` is the text-level claim (which `RawFunc`s
carry their own noalias evidence); this module is the value-level
counterpart: for every admitted C `Func`, entry binding pins at most
one block, so `oracleNoalias` (pairwise-disjoint footprints) holds by
construction:

- all-scalar `Func`s (`add`, `incr`, `choose` — borrows functionalized
  to values — `add_caller`, `translate`, flow, widths, heap-internal
  `vec_*` whose `malloc`s happen after entry): empty layout;
- single-array `Func`s (`sum`, `sum_caller`, `find_eq`): singleton
  layout (the length-paired stride discipline keeps it to one block).

`add` / `sum` / `vec` already have their `oracleNoalias` witnesses
(`Mem` / `Transfer`); the remaining M3a-fragment shapes land here.
The full `RawFunc → Func` bridge (validate mapping) is M3c work; M3b
stops at both sides independently + the verdict-cache agreement check
(`tests/lean/DerivedNoalias.lean`).
-/
import Circe.Mem
import Circe.Validator
import Circe.Emit.Add
import Circe.Emit.Choose
import Circe.Emit.Calls
import Circe.Emit.Struct
import Circe.Emit.Flow
import Circe.Emit.Vec2
import Circe.Emit.VecRealloc
import Circe.Emit.Vec64
import Circe.Emit.Method
import Circe.Emit.Acc
import Circe.Emit.Move
import Circe.Emit.Box

/-! ## All-scalar shapes: empty footprint -/

/-- `incr` binding pins nothing (borrow functionalized to a value). -/
theorem oracleNoalias_incr (p : BitVec 32) :
    oracleNoalias
      ⟨"incr", [{ name := "p", ty := .i 32, role := .mutBorrow 0 }], .i 32,
       .return_ (.add (.var "p") (.lit (.i32 1)))⟩ [.i32 p] := by
  exact ⟨_, _, _, bindMemArgs_incr p, layoutNoAlias_nil⟩

/-- `choose` binding pins nothing (both borrows functionalized to
    values; selection is pure). -/
theorem bindMemArgs_choose (b : Bool) (x y : BitVec 32) :
    bindMemArgs
      [{ name := "b", ty := .bool, role := .owned },
       { name := "x", ty := .i 32, role := .mutBorrow 0 },
       { name := "y", ty := .i 32, role := .mutBorrow 0 }]
      [.b b, .i32 x, .i32 y] emptyMem =
      some ([("b", .b b), ("x", .i32 x), ("y", .i32 y)], emptyMem, []) := by
  rfl

/-- `choose` entry footprints are trivially disjoint. -/
theorem oracleNoalias_choose (b : Bool) (x y : BitVec 32) :
    oracleNoalias chooseFunc [.b b, .i32 x, .i32 y] := by
  have hb : bindMemArgs chooseFunc.args [.b b, .i32 x, .i32 y] emptyMem =
      some ([("b", .b b), ("x", .i32 x), ("y", .i32 y)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "b", ty := .bool, role := .owned },
       { name := "x", ty := .i 32, role := .mutBorrow 0 },
       { name := "y", ty := .i 32, role := .mutBorrow 0 }]
      [.b b, .i32 x, .i32 y] emptyMem = _
    exact bindMemArgs_choose b x y
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- `add_caller` binding pins nothing (three owned scalars). -/
theorem bindMemArgs_addCaller (x y z : BitVec 32) :
    bindMemArgs
      [{ name := "x", ty := .i 32, role := .owned },
       { name := "y", ty := .i 32, role := .owned },
       { name := "z", ty := .i 32, role := .owned }]
      [.i32 x, .i32 y, .i32 z] emptyMem =
      some ([("x", .i32 x), ("y", .i32 y), ("z", .i32 z)], emptyMem, []) := by
  rfl

/-- `add_caller` entry footprints are trivially disjoint. -/
theorem oracleNoalias_addCaller (x y z : BitVec 32) :
    oracleNoalias addCallerFunc [.i32 x, .i32 y, .i32 z] := by
  have hb : bindMemArgs addCallerFunc.args [.i32 x, .i32 y, .i32 z]
      emptyMem =
      some ([("x", .i32 x), ("y", .i32 y), ("z", .i32 z)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "x", ty := .i 32, role := .owned },
       { name := "y", ty := .i 32, role := .owned },
       { name := "z", ty := .i 32, role := .owned }]
      [.i32 x, .i32 y, .i32 z] emptyMem = _
    exact bindMemArgs_addCaller x y z
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-! ## N4a: overload / namespace footprints (empty: owned scalars) -/

/-- `add3` binding pins nothing (three owned scalars). -/
theorem bindMemArgs_add3 (x y z : BitVec 32) :
    bindMemArgs
      [{ name := "a", ty := .i 32, role := .owned },
       { name := "b", ty := .i 32, role := .owned },
       { name := "c", ty := .i 32, role := .owned }]
      [.i32 x, .i32 y, .i32 z] emptyMem =
      some ([("a", .i32 x), ("b", .i32 y), ("c", .i32 z)], emptyMem, []) := by
  rfl

/-- `add3` entry footprints are trivially disjoint. -/
theorem oracleNoalias_add3 (x y z : BitVec 32) :
    oracleNoalias add3Func [.i32 x, .i32 y, .i32 z] := by
  have hb : bindMemArgs add3Func.args [.i32 x, .i32 y, .i32 z]
      emptyMem =
      some ([("a", .i32 x), ("b", .i32 y), ("c", .i32 z)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "a", ty := .i 32, role := .owned },
       { name := "b", ty := .i 32, role := .owned },
       { name := "c", ty := .i 32, role := .owned }]
      [.i32 x, .i32 y, .i32 z] emptyMem = _
    exact bindMemArgs_add3 x y z
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- Overload-caller binding pins nothing (two owned scalars; shared by
    both entries). -/
theorem bindMemArgs_useAdd (x y : BitVec 32) :
    bindMemArgs
      [{ name := "x", ty := .i 32, role := .owned },
       { name := "y", ty := .i 32, role := .owned }]
      [.i32 x, .i32 y] emptyMem =
      some ([("x", .i32 x), ("y", .i32 y)], emptyMem, []) := by
  rfl

/-- `use_add` entry footprints are trivially disjoint. -/
theorem oracleNoalias_useAdd (x y : BitVec 32) :
    oracleNoalias useAddFunc [.i32 x, .i32 y] := by
  have hb : bindMemArgs useAddFunc.args [.i32 x, .i32 y]
      emptyMem =
      some ([("x", .i32 x), ("y", .i32 y)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "x", ty := .i 32, role := .owned },
       { name := "y", ty := .i 32, role := .owned }]
      [.i32 x, .i32 y] emptyMem = _
    exact bindMemArgs_useAdd x y
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- `use_ns_add` entry footprints are trivially disjoint. -/
theorem oracleNoalias_useNsAdd (x y : BitVec 32) :
    oracleNoalias useNsAddFunc [.i32 x, .i32 y] := by
  have hb : bindMemArgs useNsAddFunc.args [.i32 x, .i32 y]
      emptyMem =
      some ([("x", .i32 x), ("y", .i32 y)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "x", ty := .i 32, role := .owned },
       { name := "y", ty := .i 32, role := .owned }]
      [.i32 x, .i32 y] emptyMem = _
    exact bindMemArgs_useAdd x y
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-! ## Loop-free scalar shapes: empty footprint (M3c) -/

/-- `add64` binding pins nothing (two owned 64-bit scalars). -/
theorem bindMemArgs_add64 (a b : BitVec 64) :
    bindMemArgs
      [{ name := "a", ty := .i 64, role := .owned },
       { name := "b", ty := .i 64, role := .owned }]
      [.i64 a, .i64 b] emptyMem =
      some ([("a", .i64 a), ("b", .i64 b)], emptyMem, []) := by
  rfl

/-- `add64` entry footprints are trivially disjoint. -/
theorem oracleNoalias_add64 (a b : BitVec 64) :
    oracleNoalias add64Func [.i64 a, .i64 b] := by
  have hb : bindMemArgs add64Func.args [.i64 a, .i64 b] emptyMem =
      some ([("a", .i64 a), ("b", .i64 b)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "a", ty := .i 64, role := .owned },
       { name := "b", ty := .i 64, role := .owned }]
      [.i64 a, .i64 b] emptyMem = _
    exact bindMemArgs_add64 a b
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- `addu64` binding pins nothing (two owned 64-bit scalars). -/
theorem bindMemArgs_addu64 (a b : BitVec 64) :
    bindMemArgs
      [{ name := "a", ty := .u 64, role := .owned },
       { name := "b", ty := .u 64, role := .owned }]
      [.u64 a, .u64 b] emptyMem =
      some ([("a", .u64 a), ("b", .u64 b)], emptyMem, []) := by
  rfl

/-- `addu64` entry footprints are trivially disjoint. -/
theorem oracleNoalias_addu64 (a b : BitVec 64) :
    oracleNoalias addu64Func [.u64 a, .u64 b] := by
  have hb : bindMemArgs addu64Func.args [.u64 a, .u64 b] emptyMem =
      some ([("a", .u64 a), ("b", .u64 b)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "a", ty := .u 64, role := .owned },
       { name := "b", ty := .u 64, role := .owned }]
      [.u64 a, .u64 b] emptyMem = _
    exact bindMemArgs_addu64 a b
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- `cls` binding pins nothing (one owned scalar; the switch is an
    if-chain over pure comparisons). -/
theorem bindMemArgs_cls (x : BitVec 32) :
    bindMemArgs [{ name := "x", ty := .u 32, role := .owned }]
      [.u32 x] emptyMem =
      some ([("x", .u32 x)], emptyMem, []) := by
  rfl

/-- `cls` entry footprints are trivially disjoint. -/
theorem oracleNoalias_cls (x : BitVec 32) :
    oracleNoalias clsFunc [.u32 x] := by
  have hb : bindMemArgs clsFunc.args [.u32 x] emptyMem =
      some ([("x", .u32 x)], emptyMem, []) := by
    show bindMemArgs [{ name := "x", ty := .u 32, role := .owned }]
      [.u32 x] emptyMem = _
    exact bindMemArgs_cls x
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- `translate` binding pins nothing (the struct crosses by value —
    copy semantics — plus two owned scalars). -/
theorem bindMemArgs_translate (px py dx dy : BitVec 32) :
    bindMemArgs
      [{ name := "p", ty := .struct "Point" [.i 32, .i 32], role := .owned },
       { name := "dx", ty := .i 32, role := .owned },
       { name := "dy", ty := .i 32, role := .owned }]
      [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy]
      emptyMem =
      some ([("p", .structVal "Point" [("x", px), ("y", py)]),
        ("dx", .i32 dx), ("dy", .i32 dy)], emptyMem, []) := by
  rfl

/-- `translate` entry footprints are trivially disjoint. -/
theorem oracleNoalias_translate (px py dx dy : BitVec 32) :
    oracleNoalias translateFunc
      [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy] := by
  have hb : bindMemArgs translateFunc.args
      [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy]
      emptyMem =
      some ([("p", .structVal "Point" [("x", px), ("y", py)]),
        ("dx", .i32 dx), ("dy", .i32 dy)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "p", ty := .struct "Point" [.i 32, .i 32], role := .owned },
       { name := "dx", ty := .i 32, role := .owned },
       { name := "dy", ty := .i 32, role := .owned }]
      [.structVal "Point" [("x", px), ("y", py)], .i32 dx, .i32 dy]
      emptyMem = _
    exact bindMemArgs_translate px py dx dy
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- `methodSum` binding pins nothing: `this` carries a `Point` *value*
    (copy semantics — CoreIR has no field-store, so struct values are
    immutable and need no footprint). The CIR `nonnull +
    dereferenceable + noundef` triple is the uniqueness evidence that
    justifies treating the borrow as a copy. -/
theorem bindMemArgs_methodSum (px py : BitVec 32) :
    bindMemArgs
      [{ name := "this", ty := .struct "Point" [.i 32, .i 32],
         role := .owned }]
      [.structVal "Point" [("x", px), ("y", py)]] emptyMem =
      some ([("this", .structVal "Point" [("x", px), ("y", py)])],
        emptyMem, []) := by
  rfl

/-- `methodSum` entry footprints are trivially disjoint. -/
theorem oracleNoalias_methodSum (px py : BitVec 32) :
    oracleNoalias methodSumFunc
      [.structVal "Point" [("x", px), ("y", py)]] := by
  have hb : bindMemArgs methodSumFunc.args
      [.structVal "Point" [("x", px), ("y", py)]] emptyMem =
      some ([("this", .structVal "Point" [("x", px), ("y", py)])],
        emptyMem, []) := by
    show bindMemArgs
      [{ name := "this", ty := .struct "Point" [.i 32, .i 32],
         role := .owned }]
      [.structVal "Point" [("x", px), ("y", py)]] emptyMem = _
    exact bindMemArgs_methodSum px py
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- `pointSumRef` binding pins nothing (single `const&` value + the
    `callRet` delegation happens after entry). -/
theorem bindMemArgs_pointSumRef (px py : BitVec 32) :
    bindMemArgs
      [{ name := "p", ty := .struct "Point" [.i 32, .i 32], role := .owned }]
      [.structVal "Point" [("x", px), ("y", py)]] emptyMem =
      some ([("p", .structVal "Point" [("x", px), ("y", py)])],
        emptyMem, []) := by
  rfl

/-- `pointSumRef` entry footprints are trivially disjoint. -/
theorem oracleNoalias_pointSumRef (px py : BitVec 32) :
    oracleNoalias pointSumRefFunc
      [.structVal "Point" [("x", px), ("y", py)]] := by
  have hb : bindMemArgs pointSumRefFunc.args
      [.structVal "Point" [("x", px), ("y", py)]] emptyMem =
      some ([("p", .structVal "Point" [("x", px), ("y", py)])],
        emptyMem, []) := by
    show bindMemArgs
      [{ name := "p", ty := .struct "Point" [.i 32, .i 32], role := .owned }]
      [.structVal "Point" [("x", px), ("y", py)]] emptyMem = _
    exact bindMemArgs_pointSumRef px py
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- `nested_sum` binding pins nothing (two owned scalars; nested loops
    are pure accumulator updates). -/
theorem bindMemArgs_nested (nv mv : BitVec 32) :
    bindMemArgs
      [{ name := "n", ty := .u 32, role := .owned },
       { name := "m", ty := .u 32, role := .owned }]
      [.u32 nv, .u32 mv] emptyMem =
      some ([("n", .u32 nv), ("m", .u32 mv)], emptyMem, []) := by
  rfl

/-- `nested_sum` entry footprints are trivially disjoint. -/
theorem oracleNoalias_nested (nv mv : BitVec 32) :
    oracleNoalias nestedFunc [.u32 nv, .u32 mv] := by
  have hb : bindMemArgs nestedFunc.args [.u32 nv, .u32 mv] emptyMem =
      some ([("n", .u32 nv), ("m", .u32 mv)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "n", ty := .u 32, role := .owned },
       { name := "m", ty := .u 32, role := .owned }]
      [.u32 nv, .u32 mv] emptyMem = _
    exact bindMemArgs_nested nv mv
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- `skip_sum` binding pins nothing (one owned scalar; break/continue
    only steer the pure accumulation loop). -/
theorem bindMemArgs_skip (nv : BitVec 32) :
    bindMemArgs [{ name := "n", ty := .u 32, role := .owned }]
      [.u32 nv] emptyMem =
      some ([("n", .u32 nv)], emptyMem, []) := by
  rfl

/-- `skip_sum` entry footprints are trivially disjoint. -/
theorem oracleNoalias_skip (nv : BitVec 32) :
    oracleNoalias skipFunc [.u32 nv] := by
  have hb : bindMemArgs skipFunc.args [.u32 nv] emptyMem =
      some ([("n", .u32 nv)], emptyMem, []) := by
    show bindMemArgs [{ name := "n", ty := .u 32, role := .owned }]
      [.u32 nv] emptyMem = _
    exact bindMemArgs_skip nv
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- `vec_copy_sum` binding pins nothing (the length is an owned scalar;
    both blocks are allocated after entry, so the entry footprint is
    empty — disjointness of the two blocks is internal, by fresh
    allocation). -/
theorem bindMemArgs_vec2 (nv : BitVec 32) :
    bindMemArgs [{ name := "n", ty := .u 32, role := .owned }]
      [.u32 nv] emptyMem =
      some ([("n", .u32 nv)], emptyMem, []) := by
  rfl

/-- `vec_copy_sum` entry footprints are trivially disjoint. -/
theorem oracleNoalias_vec2 (nv : BitVec 32) :
    oracleNoalias vec2Func [.u32 nv] := by
  have hb : bindMemArgs vec2Func.args [.u32 nv] emptyMem =
      some ([("n", .u32 nv)], emptyMem, []) := by
    show bindMemArgs [{ name := "n", ty := .u 32, role := .owned }]
      [.u32 nv] emptyMem = _
    exact bindMemArgs_vec2 nv
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- `vec_realloc` binding pins nothing (the length is an owned scalar;
    the single block is allocated after entry and resized in place, so
    the entry footprint is empty). -/
theorem bindMemArgs_vecRealloc (nv : BitVec 32) :
    bindMemArgs [{ name := "n", ty := .u 32, role := .owned }]
      [.u32 nv] emptyMem =
      some ([("n", .u32 nv)], emptyMem, []) := by
  rfl

/-- `vec_realloc` entry footprints are trivially disjoint. -/
theorem oracleNoalias_vecRealloc (nv : BitVec 32) :
    oracleNoalias vecReallocFunc [.u32 nv] := by
  have hb : bindMemArgs vecReallocFunc.args [.u32 nv] emptyMem =
      some ([("n", .u32 nv)], emptyMem, []) := by
    show bindMemArgs [{ name := "n", ty := .u 32, role := .owned }]
      [.u32 nv] emptyMem = _
    exact bindMemArgs_vecRealloc nv
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- `vec_alloc_u64` binding pins nothing (the length is an owned 64-bit
    scalar; the single block is allocated after entry, so the entry
    footprint is empty). -/
theorem bindMemArgs_vec64 (nv : BitVec 64) :
    bindMemArgs [{ name := "n", ty := .u 64, role := .owned }]
      [.u64 nv] emptyMem =
      some ([("n", .u64 nv)], emptyMem, []) := by
  rfl

/-- `vec_alloc_u64` entry footprints are trivially disjoint. -/
theorem oracleNoalias_vec64 (nv : BitVec 64) :
    oracleNoalias vec64Func [.u64 nv] := by
  have hb : bindMemArgs vec64Func.args [.u64 nv] emptyMem =
      some ([("n", .u64 nv)], emptyMem, []) := by
    show bindMemArgs [{ name := "n", ty := .u 64, role := .owned }]
      [.u64 nv] emptyMem = _
    exact bindMemArgs_vec64 nv
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-! ## Single-array shapes: singleton footprint -/
/-- `sum_caller` binding pins exactly the array block (mirrors
    `bindMemArgs_sum`; the call itself happens after entry). -/
theorem bindMemArgs_sumCaller (l : List (BitVec 32)) (nv : BitVec 32) :
    bindMemArgs
      [{ name := "a", ty := .array (.u 32) 4096, role := .sharedBorrow },
       { name := "n", ty := .u 32, role := .owned }]
      [.arr32 l, .u32 nv] emptyMem =
      some ([("a", .arr32 l), ("n", .u32 nv)],
        ⟨1, [(0, ⟨0, true, l⟩)], []⟩, [("a", 0, 0)]) := by
  rfl

/-- `sum_caller` entry footprints are a singleton. -/
theorem oracleNoalias_sumCaller (l : List (BitVec 32)) (nv : BitVec 32) :
    oracleNoalias sumCallerFunc [.arr32 l, .u32 nv] := by
  have hb : bindMemArgs sumCallerFunc.args [.arr32 l, .u32 nv] emptyMem =
      some ([("a", .arr32 l), ("n", .u32 nv)],
        ⟨1, [(0, ⟨0, true, l⟩)], []⟩, [("a", 0, 0)]) := by
    show bindMemArgs
      [{ name := "a", ty := .array (.u 32) 4096, role := .sharedBorrow },
       { name := "n", ty := .u 32, role := .owned }]
      [.arr32 l, .u32 nv] emptyMem = _
    exact bindMemArgs_sumCaller l nv
  have hn : LayoutNoAlias [("a", 0, 0)] := by
    simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-- `find_eq` binding pins exactly the array block (needle + bound are
    scalars; the stride loop stays inside the single block). -/
theorem bindMemArgs_findEq (l : List (BitVec 32)) (nv kv : BitVec 32) :
    bindMemArgs
      [{ name := "a", ty := .array (.u 32) 4096, role := .sharedBorrow },
       { name := "n", ty := .u 32, role := .owned },
       { name := "k", ty := .u 32, role := .owned }]
      [.arr32 l, .u32 nv, .u32 kv] emptyMem =
      some ([("a", .arr32 l), ("n", .u32 nv), ("k", .u32 kv)],
        ⟨1, [(0, ⟨0, true, l⟩)], []⟩, [("a", 0, 0)]) := by
  rfl

/-- `find_eq` entry footprints are a singleton. -/
theorem oracleNoalias_findEq (l : List (BitVec 32)) (nv kv : BitVec 32) :
    oracleNoalias findEqFunc [.arr32 l, .u32 nv, .u32 kv] := by
  have hb : bindMemArgs findEqFunc.args [.arr32 l, .u32 nv, .u32 kv]
      emptyMem =
      some ([("a", .arr32 l), ("n", .u32 nv), ("k", .u32 kv)],
        ⟨1, [(0, ⟨0, true, l⟩)], []⟩, [("a", 0, 0)]) := by
    show bindMemArgs
      [{ name := "a", ty := .array (.u 32) 4096, role := .sharedBorrow },
       { name := "n", ty := .u 32, role := .owned },
       { name := "k", ty := .u 32, role := .owned }]
      [.arr32 l, .u32 nv, .u32 kv] emptyMem = _
    exact bindMemArgs_findEq l nv kv
  have hn : LayoutNoAlias [("a", 0, 0)] := by
    simp [LayoutNoAlias, layoutAddrs]
  exact ⟨_, _, _, hb, hn⟩

/-! ## M3d C++ shapes: empty footprints (N1b `Acc`, N1b `Box`) -/

/-- The `Acc` leaves are int-only (the accumulator never crosses the
    boundary — field loads/stores are fused into scalar params at
    validation), so entry binding pins nothing. -/
theorem oracleNoalias_accCtor :
    oracleNoalias accCtorFunc [] := by
  exact ⟨_, _, _, rfl, layoutNoAlias_nil⟩

theorem oracleNoalias_accAdd (s v : BitVec 32) :
    oracleNoalias accAddFunc [.i32 s, .i32 v] := by
  exact ⟨_, _, _, rfl, layoutNoAlias_nil⟩

theorem oracleNoalias_accGet (s : BitVec 32) :
    oracleNoalias accGetFunc [.i32 s] := by
  exact ⟨_, _, _, rfl, layoutNoAlias_nil⟩

theorem oracleNoalias_accDtor (t : BitVec 32) :
    oracleNoalias accDtorFunc [.i32 t] := by
  exact ⟨_, _, _, rfl, layoutNoAlias_nil⟩

/-- `acc_two` entry footprints are trivially disjoint (two owned
    scalars; the ctor/dtor calls happen after entry inside the
    `cleanup` scope). -/
theorem oracleNoalias_accTwo (a b : BitVec 32) :
    oracleNoalias accTwoFunc [.i32 a, .i32 b] := by
  have hb : bindMemArgs accTwoFunc.args [.i32 a, .i32 b] emptyMem =
      some ([("a", .i32 a), ("b", .i32 b)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "a", ty := .i 32, role := .owned },
       { name := "b", ty := .i 32, role := .owned }]
      [.i32 a, .i32 b] emptyMem = _
    rfl
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- Move-ctor leaf footprints are trivially disjoint (two owned
    scalars; the destination storage is modeled, not aliased). -/
theorem oracleNoalias_accMoveCtor (d s : BitVec 32) :
    oracleNoalias accMoveCtorFunc [.i32 d, .i32 s] := by
  exact ⟨_, _, _, rfl, layoutNoAlias_nil⟩

/-- `move_acc` entry footprints are trivially disjoint (two owned
    scalars; both `Acc` states are threaded as scalars after entry,
    exactly like `acc_two`). -/
theorem oracleNoalias_moveAcc (a b : BitVec 32) :
    oracleNoalias moveAccFunc [.i32 a, .i32 b] := by
  have hb : bindMemArgs moveAccFunc.args [.i32 a, .i32 b] emptyMem =
      some ([("a", .i32 a), ("b", .i32 b)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "a", ty := .i 32, role := .owned },
       { name := "b", ty := .i 32, role := .owned }]
      [.i32 a, .i32 b] emptyMem = _
    rfl
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- `scope_early` entry footprints are trivially disjoint (two owned
    scalars; the single `Acc` state is threaded as a scalar after
    entry, on both the early and fallthrough paths). -/
theorem oracleNoalias_scopeEarly (a b : BitVec 32) :
    oracleNoalias scopeEarlyFunc [.i32 a, .i32 b] := by
  have hb : bindMemArgs scopeEarlyFunc.args [.i32 a, .i32 b] emptyMem =
      some ([("a", .i32 a), ("b", .i32 b)], emptyMem, []) := by
    show bindMemArgs
      [{ name := "a", ty := .i 32, role := .owned },
       { name := "b", ty := .i 32, role := .owned }]
      [.i32 a, .i32 b] emptyMem = _
    rfl
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-- `box_through` entry footprints are trivially disjoint (one owned
    scalar; the box is allocated after entry, so the entry footprint
    is empty — the single-word block's disjointness is internal, by
    fresh allocation). -/
theorem oracleNoalias_boxThrough (x : BitVec 32) :
    oracleNoalias boxThroughFunc [.i32 x] := by
  have hb : bindMemArgs boxThroughFunc.args [.i32 x] emptyMem =
      some ([("x", .i32 x)], emptyMem, []) := by
    show bindMemArgs [{ name := "x", ty := .i 32, role := .owned }]
      [.i32 x] emptyMem = _
    rfl
  exact ⟨_, _, _, hb, layoutNoAlias_nil⟩

/-! ## Cache bridge (discharged by the executable check) -/

/-- Bridge: on a `noalias` verdict the gate admits. The premise
    (`o.verdict = .noalias` for every M3b `derivedNoalias` claim with
    live params) is discharged by the executable cache-agreement check
    (`tests/lean/DerivedNoalias.lean`, run in `tools/check.sh`), not by
    proof — the checked-in `verdicts.txt` stays a cache, and the check
    fails on any drift. -/
theorem derived_bridge_noalias (o : OracleFact) (h : o.verdict = .noalias) :
    verdictAdmits o.verdict = true := by
  simp [verdictAdmits, h]
